module

public import CFSG.Quasithin.EmptyFaithful.ModDSetup

public section

namespace CFSG.Quasithin

namespace SBc10

open CFSG.CosetTable CFSG.Quasithin.ModD
open scoped Pointwise

private def invSub {Γ M : Type} [Group Γ] [Group M] [Finite M] (φ : Γ →* MulAut M) (E : Subgroup M) :
    Subgroup Γ where
  carrier := {g | ∀ e ∈ E, φ g e ∈ E}
  mul_mem' := by
    intro a b ha hb e he
    show φ (a * b) e ∈ E
    rw [map_mul, MulAut.mul_apply]
    exact ha _ (hb e he)
  one_mem' := by
    intro e he
    show φ 1 e ∈ E
    rw [map_one, MulAut.one_apply]
    exact he
  inv_mem' := by
    intro g hg e he
    let f : E → E := fun e => ⟨φ g e, hg e e.2⟩
    have hinj : Function.Injective f := fun a b hab =>
      Subtype.ext ((φ g).injective (congrArg Subtype.val hab))
    obtain ⟨e', he'⟩ := Finite.injective_iff_surjective.1 hinj ⟨e, he⟩
    have h1 : φ g e' = e := congrArg Subtype.val he'
    have h2 : φ g⁻¹ e = e' := by
      rw [← h1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    show φ g⁻¹ e ∈ E
    rw [h2]
    exact e'.2

private theorem exists_fixed_of_isPGroup {Γ M : Type} [Group Γ] [Group M] [Finite M]
    (φ : Γ →* MulAut M) {X : Subgroup Γ} (hX : IsPGroup 2 X) (E : Subgroup M)
    (hXE : ∀ x ∈ X, ∀ e ∈ E, φ x e ∈ E) (hcard : 2 ∣ Nat.card E) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ x ∈ X, φ x e = e := by
  let _ : MulAction X E :=
    { smul := fun x e => ⟨φ x e, hXE x x.2 e e.2⟩
      one_smul := fun e => Subtype.ext (by
        show φ ((1 : X) : Γ) e = e
        simp)
      mul_smul := fun x y e => Subtype.ext (by
        show φ ((x * y : X) : Γ) e = φ x (φ y e)
        simp) }
  have h0 : (1 : E) ∈ MulAction.fixedPoints X E := by
    rw [MulAction.mem_fixedPoints]
    intro x
    exact Subtype.ext (by
      show φ x (1 : M) = 1
      exact map_one _)
  obtain ⟨b, hb, hb1⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hcard h0
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun x hx => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hb ⟨x, hx⟩)

private theorem mem_of_odd_pow_of_mem_sup {G : Type} [Group G] {T Y : Subgroup G}
    (hT : IsPGroup 2 T) (hN : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) {g : G} (hg : g ∈ T ⊔ Y) {n : ℕ}
    (hn : Odd n) (hgn : g ^ n = 1) : g ∈ Y := by
  have hLE : T ≤ Subgroup.normalizer Y := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hN t ht h hh, fun hh => ?_⟩
    have h2 := hN t⁻¹ (T.inv_mem ht) _ hh
    have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have hmul : g ∈ (T : Set G) * (Y : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T Y hLE]
    exact hg
  obtain ⟨t, ht, y, hy, rfl⟩ := Set.mem_mul.1 hmul
  have hpow : ∀ k : ℕ, ∃ w ∈ Y, (t * y) ^ k = t ^ k * w := by
    intro k
    induction k with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw, hk⟩ := ih
      refine ⟨t⁻¹ * w * t * y, Y.mul_mem (by simpa using hN t⁻¹ (T.inv_mem ht) w hw) hy, ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  obtain ⟨w, hw, hwn⟩ := hpow n
  rw [hgn] at hwn
  have htn : t ^ n ∈ Y := by
    have : t ^ n = w⁻¹ := eq_inv_of_mul_eq_one_left hwn.symm
    rw [this]
    exact Y.inv_mem hw
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hcop : Nat.Coprime n (2 ^ k) :=
    Nat.Coprime.pow_right k hn.coprime_two_right
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have htY : t ∈ Y := by
    have h1 : t ^ (a * (n : ℤ) + b * ((2 ^ k : ℕ) : ℤ)) = t := by rw [hab, zpow_one]
    have h2 : t = (t ^ n) ^ a := by
      conv_lhs => rw [← h1]
      rw [zpow_add, mul_comm a, zpow_mul, zpow_natCast, mul_comm b, zpow_mul, zpow_natCast, htk,
        one_zpow, mul_one]
    rw [h2]
    exact Y.zpow_mem htn a
  exact Y.mul_mem htY hy

private theorem vImg_four_ne : ∀ p : Fin 63, vImg 4 p ≠ p := by decide +kernel

theorem g2_module_facts
    {M : Type} [Group M] [Finite M]
    (hcard : Nat.card M = 2 ^ 6) (hsq : ∀ a : M, a * a = 1) (φ : U33G →* MulAut M)
    (hirr : ∀ N : Subgroup M, (∀ g : U33G, ∀ n ∈ N, φ g n ∈ N) → N = ⊥ ∨ N = ⊤)
    {Y : Subgroup U33G} (hTY : ∀ t ∈ u33Data.T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    {E : Subgroup M} (hE4 : Nat.card E = 4)
    (hET : ∀ t ∈ u33Data.T, ∀ e ∈ E, φ t e ∈ E)
    (hEY : ∀ y ∈ Y, ∀ e ∈ E, φ y e ∈ E)
    (hCE : ∀ e ∈ E, (∀ y ∈ Y, φ y e = e) → e = 1) :
    (∀ m : M, (∀ y ∈ Y, φ y m = m) → m = 1) ∧
      ∀ H : Subgroup M, (∀ y ∈ Y, ∀ m : M, φ y m * m⁻¹ ∈ H) → H = ⊤ := by
  classical
  have hT2 : IsPGroup 2 u33Data.T := u33_syl.1
  have hinv : ∀ a : M, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hcomm : ∀ a b : M, a * b = b * a := fun a b =>
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  obtain ⟨z, hzE, hz1, hzT⟩ := exists_fixed_of_isPGroup φ hT2 E hET (by rw [hE4]; decide)
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hsq z
  obtain ⟨Y₁, hY₁⟩ : ∃ Y₁ : Subgroup U33G, Y₁ = u33Data.T ⊔ Y := ⟨_, rfl⟩
  have hY1T : u33Data.T ≤ Y₁ := hY₁ ▸ le_sup_left
  have hY1Y : Y ≤ Y₁ := hY₁ ▸ le_sup_right
  have hinvE : Y₁ ≤ invSub φ E := hY₁ ▸ sup_le (fun t ht => hET t ht) (fun y hy => hEY y hy)
  have hV : ∀ g ∈ Y₁, ∀ v ∈ E, φ g v ∈ E := fun g hg => hinvE hg
  have hY1ne : Y₁ ≠ u33Data.T := by
    intro h
    have hYT : Y ≤ u33Data.T := h ▸ hY1Y
    obtain ⟨e, heE, he1, heY⟩ :=
      exists_fixed_of_isPGroup φ (hT2.to_le hYT) E hEY (by rw [hE4]; decide)
    exact he1 (hCE e heE heY)
  have hY1top : Y₁ ≠ ⊤ := by
    intro h
    have hall : ∀ g : U33G, ∀ e ∈ E, φ g e ∈ E := fun g => hinvE (by rw [h]; exact Subgroup.mem_top g)
    rcases hirr E (fun g n hn => hall g n hn) with hE | hE
    · have h1 : Nat.card E = 1 := by rw [hE]; exact Subgroup.card_bot
      omega
    · have h1 : Nat.card E = 2 ^ 6 := by rw [hE, Subgroup.card_top, hcard]
      omega
  have hAB : u33Data.A ≠ u33Data.B := fun h => A_not_le_B h.le
  have hAtop : u33Data.A ≠ ⊤ := fun h => B_not_le_A (by rw [h]; exact le_top)
  have hBtop : u33Data.B ≠ ⊤ := fun h => A_not_le_B (by rw [h]; exact le_top)
  obtain ⟨hY1B, ε, hε3, horb⟩ : Y₁ = u33Data.B ∧ ∃ ε : M → Fin 63,
      (∀ g m, (∃ h, φ h z = m) → ε (φ g m) = vHom g (ε m)) ∧
        (∀ m, m ≠ 1 → ∃ g, φ g z = m) := by
    rcases u33Data.lattice Y₁ hY1T with h | h | h | h
    · exact absurd h hY1ne
    · exfalso
      have hY1B := (pencil_setup hcard φ hirr hz1 hz2 hzT hzE hE4 hY1T u33Data.T_le_B hY1ne hY1top
        u33Data.T_ne_B.symm hBtop (fun h' => hAB (h.symm.trans h')) hV).1
      exact hAB (h.symm.trans hY1B)
    · obtain ⟨-, -, ε, -, -, -, -, hε3, horb, -⟩ := pencil_setup hcard φ hirr hz1 hz2 hzT hzE hE4
        hY1T u33Data.T_le_A hY1ne hY1top u33Data.T_ne_A.symm hAtop
        (fun h' => hAB (h'.symm.trans h)) hV
      exact ⟨h, ε, hε3, horb⟩
    · exact absurd h hY1top
  have hyY : u33Data.y ∈ Y := by
    have hyB : u33Data.y ∈ u33Data.T ⊔ Y := by
      rw [← hY₁, hY1B]
      exact u33Data.y_mem_B
    exact mem_of_odd_pow_of_mem_sup hT2 hTY hyB (by decide : Odd 3) u33Data.hy
  have hfixy : ∀ m : M, φ u33Data.y m = m → m = 1 := by
    intro m hm
    by_contra hm1
    have h1 := hε3 u33Data.y m (horb m hm1)
    rw [hm, show vHom u33Data.y = vImg 4 from vHom_gen 4] at h1
    exact vImg_four_ne (ε m) h1.symm
  refine ⟨fun m hm => hfixy m (hm _ hyY), fun H hH => ?_⟩
  have h3 : ∀ x : M, φ u33Data.y (φ u33Data.y (φ u33Data.y x)) = x := by
    intro x
    have h := congrArg (fun g => φ g x) u33Data.hy
    simpa [pow_succ, MulAut.mul_apply] using h
  rw [eq_top_iff]
  intro x _
  have hn : x * φ u33Data.y x * φ u33Data.y (φ u33Data.y x) = 1 := by
    apply hfixy
    calc φ u33Data.y (x * φ u33Data.y x * φ u33Data.y (φ u33Data.y x))
        = φ u33Data.y x * φ u33Data.y (φ u33Data.y x) * x := by rw [map_mul, map_mul, h3]
      _ = x * (φ u33Data.y x * φ u33Data.y (φ u33Data.y x)) := hcomm _ _
      _ = x * φ u33Data.y x * φ u33Data.y (φ u33Data.y x) := (mul_assoc _ _ _).symm
  have hx : x = φ u33Data.y x * (φ u33Data.y (φ u33Data.y x))⁻¹ :=
    calc x = (φ u33Data.y x * φ u33Data.y (φ u33Data.y x))⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rwa [← mul_assoc])
      _ = (φ u33Data.y (φ u33Data.y x))⁻¹ * (φ u33Data.y x)⁻¹ := mul_inv_rev _ _
      _ = (φ u33Data.y x)⁻¹ * (φ u33Data.y (φ u33Data.y x))⁻¹ := hcomm _ _
      _ = φ u33Data.y x * (φ u33Data.y (φ u33Data.y x))⁻¹ := by rw [hinv (φ u33Data.y x)]
  have hmem := H.mul_mem (hH _ hyY x) (hH _ hyY (φ u33Data.y (φ u33Data.y x)))
  rw [h3] at hmem
  have hval : φ u33Data.y x * x⁻¹ * (x * (φ u33Data.y (φ u33Data.y x))⁻¹) = x :=
    calc φ u33Data.y x * x⁻¹ * (x * (φ u33Data.y (φ u33Data.y x))⁻¹)
        = φ u33Data.y x * (φ u33Data.y (φ u33Data.y x))⁻¹ := by group
      _ = x := hx.symm
  rwa [hval] at hmem

end SBc10

end CFSG.Quasithin
