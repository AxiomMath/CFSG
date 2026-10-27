module

public import CFSG.Quasithin.H13.NQS13410K
public import CFSG.Quasithin.H13.U3S1344A
public import CFSG.Quasithin.H13.NQS13410E

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem l3_stab_two : ∀ p : L3.Vec, p ≠ 0 → ∀ x : L3.Γ, L3.act x p = p → x ^ 8 = 1 →
    ∀ g : L3.Γ, g ^ 3 = 1 → g ≠ 1 → L3.act g p = p → (x * (g * x * g⁻¹)) ^ 8 = 1 →
      (x * (g⁻¹ * x * g)) ^ 8 = 1 → x ∈ L3.AS {0, p} := by decide +kernel

theorem l3_AS_comm : ∀ p : L3.Vec, p ≠ 0 → ∀ g : L3.Γ, g ^ 3 = 1 → g ≠ 1 → L3.act g p = p →
    ∀ σ ∈ L3.AS {0, p}, σ * g = g * σ → σ = 1 := by decide +kernel

theorem l3_AS_fix_card : ∀ p : L3.Vec, p ≠ 0 → ∀ σ ∈ L3.AS {0, p}, σ ≠ 1 →
    (Finset.univ.filter fun v : L3.Vec => L3.act σ v = v).card = 4 := by decide +kernel

theorem l3_AS_fix2 : ∀ p : L3.Vec, p ≠ 0 → ∀ σ ∈ L3.AS {0, p}, ∀ τ ∈ L3.AS {0, p}, σ ≠ 1 →
    τ ≠ 1 → σ ≠ τ →
      (Finset.univ.filter fun v : L3.Vec => L3.act σ v = v ∧ L3.act τ v = v).card = 2 := by
  decide +kernel

theorem l3_sq_mem : ∀ p : L3.Vec, p ≠ 0 → ∀ x : L3.Γ, L3.act x p = p → x ^ 8 = 1 →
    x * x ≠ 1 → x * x ∈ L3.AS {0, p} := by decide +kernel

theorem l3_prod_mem : ∀ p : L3.Vec, p ≠ 0 → ∀ x : L3.Γ, L3.act x p = p → ∀ y : L3.Γ,
    L3.act y p = p → x * x = 1 → y * y = 1 → x ∉ L3.AS {0, p} → y ∉ L3.AS {0, p} → x ≠ y →
      (x * y) ^ 8 = 1 → x * y ∈ L3.AS {0, p} := by decide +kernel

theorem l3_comm_ne : ∀ p : L3.Vec, p ≠ 0 → ∀ g : L3.Γ, g ^ 3 = 1 → g ≠ 1 → L3.act g p = p →
    ∀ s ∈ L3.AS {0, p}, s ≠ 1 → s * (g * s * g⁻¹) ∈ L3.AS {0, p} ∧ s * (g * s * g⁻¹) ≠ 1 := by
  decide +kernel

theorem l3_pow_eight {x : L3.Γ} {k : ℕ} (h : x ^ 2 ^ k = 1) : x ^ 8 = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ 168 := by
    have := orderOf_dvd_natCard x
    rwa [HSType.card_SL_three_two] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hj3
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (by omega)).trans h2
    norm_num at this
  exact orderOf_dvd_iff_pow_eq_one.1 (hj ▸ (pow_dvd_pow 2 hj3).trans (by norm_num))

variable {G : Type} [Group G]

structure L3Coords (K X : Subgroup G) where
  ρ : ↥(normalizer (X : Set G)) →* L3.Γ
  c : ↥X → L3.Vec
  c_inj : Function.Injective c
  c_one : c 1 = 0
  equiv : ∀ (g : ↥(normalizer (X : Set G))) (x : ↥X), c (conjAct X g x) = L3.act (ρ g) (c x)
  ker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (X : Set G)
  image_K : ∀ γ, ∃ g : ↥(normalizer (X : Set G)), (g : G) ∈ K ∧ ρ g = γ

theorem exists_l3Coords [Finite G] {K X : Subgroup G} [IsMulCommutative ↥X]
    (hnat : BinaryNaturalSL (V := ↥X) (autOn K X) ⊤ ⊥ 3 1) : Nonempty (L3Coords K X) := by
  classical
  obtain ⟨D⟩ := hnat.toL3Coord
  have htop := autOn_eq_top_of_l32 hnat
  let e : L3.Γ ≃* ↥(autOn K X) := MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩
  have hmem : ∀ g, conjAct X g ∈ autOn K X := fun g => by rw [htop]; exact mem_top _
  let ρ : ↥(normalizer (X : Set G)) →* L3.Γ :=
    e.symm.toMonoidHom.comp ((conjAct X).codRestrict (autOn K X) hmem)
  have hρ : ∀ g, ((e (ρ g) : ↥(autOn K X)) : MulAut ↥X) = conjAct X g := fun g => by
    show ((e (e.symm ⟨conjAct X g, hmem g⟩)) : MulAut ↥X) = conjAct X g
    rw [MulEquiv.apply_symm_apply]
  refine ⟨⟨ρ, l3coord D, l3coord_injective D, ?_, fun g x => ?_, fun g => ?_, fun γ => ?_⟩⟩
  · show Multiplicative.toAdd (D.β ⟨1, mem_top 1⟩) = 0
    rw [show (⟨1, mem_top 1⟩ : ↥(⊤ : Subgroup ↥X)) = 1 from rfl, map_one]
    rfl
  · rw [← hρ g]
    exact l3coord_rho D (ρ g) x
  · constructor
    · intro h
      have : conjAct X g = 1 := by
        rw [← hρ g, h, map_one]
        rfl
      exact A4.conjAct_eq_one_iff.1 this
    · intro h
      apply e.injective
      apply Subtype.ext
      rw [map_one, hρ g]
      exact A4.conjAct_eq_one_iff.2 h
  · obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.1 (e γ).2
    refine ⟨g, mem_subgroupOf.1 hg, ?_⟩
    apply e.injective
    apply Subtype.ext
    rw [hρ g]
    exact hge

namespace L3Coords

variable {K X : Subgroup G} (C : L3Coords K X)

theorem fix_iff (g : ↥(normalizer (X : Set G))) (x : ↥X) :
    (g : G) * x * (g : G)⁻¹ = x ↔ L3.act (C.ρ g) (C.c x) = C.c x := by
  rw [← C.equiv]
  constructor
  · intro h
    congr 1
    apply Subtype.ext
    rw [A5.conjAct_val]
    exact h
  · intro h
    have := congrArg Subtype.val (C.c_inj h)
    rw [A5.conjAct_val] at this
    exact this

theorem conjAct_eq_one_iff (g : ↥(normalizer (X : Set G))) : conjAct X g = 1 ↔ C.ρ g = 1 := by
  rw [A4.conjAct_eq_one_iff, C.ker]

theorem c_ne_zero {x : ↥X} (hx : x ≠ 1) : C.c x ≠ 0 := fun h =>
  hx (C.c_inj (h.trans C.c_one.symm))

theorem rho_mem_AS [Finite G] {R : Subgroup G} (hR : IsPGroup 2 ↥R) {x₀ : ↥X} (hx₀ : x₀ ≠ 1)
    (hRx : ∀ r ∈ R, r * (x₀ : G) * r⁻¹ = x₀) (y : ↥(normalizer (X : Set G)))
    (hy3 : C.ρ y ^ 3 = 1) (hy1 : C.ρ y ≠ 1) (hyp : L3.act (C.ρ y) (C.c x₀) = C.c x₀)
    (hyR : (y : G) ∈ normalizer (R : Set G)) (r : ↥(normalizer (X : Set G)))
    (hr : (r : G) ∈ R) : C.ρ r ∈ L3.AS {0, C.c x₀} := by
  have h2 : ∀ g : ↥(normalizer (X : Set G)), (g : G) ∈ R → C.ρ g ^ 8 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hR ⟨g, hg⟩
    refine l3_pow_eight (k := k) ?_
    rw [← map_pow]
    have : g ^ 2 ^ k = 1 := Subtype.ext (by
      have h3 := congrArg Subtype.val hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3 ⊢
      exact h3)
    rw [this, map_one]
  have hfix : L3.act (C.ρ r) (C.c x₀) = C.c x₀ := (C.fix_iff r x₀).1 (hRx r hr)
  have hyr : (y : G) * r * (y : G)⁻¹ ∈ R := (mem_normalizer_iff.mp hyR r).mp hr
  have hyr' : (y : G)⁻¹ * r * (y : G)⁻¹⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (inv_mem hyR) r).mp hr
  have h3 := h2 (r * (y * r * y⁻¹)) (mul_mem hr hyr)
  have h4 := h2 (r * (y⁻¹ * r * y⁻¹⁻¹)) (mul_mem hr hyr')
  simp only [map_mul, map_inv, inv_inv] at h3 h4
  exact l3_stab_two _ (C.c_ne_zero hx₀) _ hfix (h2 r hr) _ hy3 hy1 hyp h3 h4

theorem relIndex_mul_card_le [Finite G] {A : Subgroup G} (hAN : A ≤ normalizer (X : Set G))
    {p : L3.Vec} (hp : p ≠ 0) (hAE : ∀ a : ↥(normalizer (X : Set G)), (a : G) ∈ A →
      C.ρ a ∈ L3.AS {0, p}) (hA : ¬ A ≤ centralizer (X : Set G)) :
    (A ⊓ centralizer (X : Set G)).relIndex A * Nat.card ↥(X ⊓ centralizer (A : Set G)) ≤ 8 := by
  classical
  set Y := (A.subgroupOf (normalizer (X : Set G))).map C.ρ with hY
  have h1 : (A ⊓ centralizer (X : Set G)).relIndex A = Nat.card ↥Y := by
    rw [← card_autOn_eq_relIndex hAN]
    exact Nat.card_congr (U3.mapMulEquivOfKer (conjAct X) C.ρ C.conjAct_eq_one_iff
      (A.subgroupOf (normalizer (X : Set G)))).toEquiv
  have hYE : ∀ σ ∈ Y, σ ∈ L3.AS {0, p} := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAE a (mem_subgroupOf.1 ha)
  obtain ⟨a₀, ha₀A, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hA
  set σ₀ := C.ρ ⟨a₀, hAN ha₀A⟩ with hσ₀
  have hσ₀Y : σ₀ ∈ Y := ⟨⟨a₀, hAN ha₀A⟩, mem_subgroupOf.2 ha₀A, rfl⟩
  have hσ₀1 : σ₀ ≠ 1 := fun h => ha₀C ((C.ker _).1 h)
  have hfix : ∀ w : ↥(X ⊓ centralizer (A : Set G)), ∀ τ ∈ Y,
      L3.act τ (C.c ⟨w, (mem_inf.1 w.2).1⟩) = C.c ⟨w, (mem_inf.1 w.2).1⟩ := by
    rintro w _ ⟨a, ha, rfl⟩
    refine (C.fix_iff a _).1 ?_
    show (a : G) * w * (a : G)⁻¹ = w
    rw [mem_centralizer_iff.mp (mem_inf.1 w.2).2 (a : G) (mem_subgroupOf.1 ha),
      mul_inv_cancel_right]
  let f : ↥(X ⊓ centralizer (A : Set G)) → L3.Vec := fun w => C.c ⟨w, (mem_inf.1 w.2).1⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext
    (congrArg (fun y : ↥X => (y : G)) (C.c_inj hab))
  have hYc : Nat.card ↥Y ≤ (L3.AS {0, p}).card :=
    card_le_of_maps_to (fun σ : ↥Y => (σ : L3.Γ)) Subtype.val_injective _ fun σ => hYE σ σ.2
  rw [L3.AS_card p hp] at hYc
  by_cases htwo : ∃ τ ∈ Y, τ ≠ 1 ∧ τ ≠ σ₀
  · obtain ⟨τ, hτY, hτ1, hτσ⟩ := htwo
    have hC : Nat.card ↥(X ⊓ centralizer (A : Set G)) ≤ 2 := by
      refine (card_le_of_maps_to f hf (Finset.univ.filter fun v : L3.Vec =>
        L3.act σ₀ v = v ∧ L3.act τ v = v) fun w => ?_).trans
          (l3_AS_fix2 p hp σ₀ (hYE σ₀ hσ₀Y) τ (hYE τ hτY) hσ₀1 hτ1 (Ne.symm hτσ)).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hfix w σ₀ hσ₀Y, hfix w τ hτY⟩
    rw [h1]
    nlinarith
  · push Not at htwo
    have hC : Nat.card ↥(X ⊓ centralizer (A : Set G)) ≤ 4 := by
      refine (card_le_of_maps_to f hf (Finset.univ.filter fun v : L3.Vec => L3.act σ₀ v = v)
        fun w => ?_).trans (l3_AS_fix_card p hp σ₀ (hYE σ₀ hσ₀Y) hσ₀1).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfix w σ₀ hσ₀Y
    have hYc2 : Nat.card ↥Y ≤ 2 := by
      refine (card_le_of_maps_to (fun σ : ↥Y => (σ : L3.Γ)) Subtype.val_injective
        {1, σ₀} fun σ => ?_).trans (Finset.card_le_two)
      by_cases h : (σ : L3.Γ) = 1
      · simp [h]
      · simp [htwo σ σ.2 h]
    rw [h1]
    nlinarith

theorem exists_mem_AS [Finite G] {T : Subgroup G} (hKX : K ≤ normalizer (X : Set G))
    (hsyl : IsSylowTwoOf (T ⊓ K) K) {x₀ : ↥X} (hx₀ : x₀ ≠ 1)
    (hx₀T : (x₀ : G) ∈ centralizer (T : Set G)) :
    ∃ s : ↥(normalizer (X : Set G)), (s : G) ∈ T ⊓ K ∧ C.ρ s ∈ L3.AS {0, C.c x₀} ∧
      C.ρ s ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set p := C.c x₀ with hp
  have hp0 : p ≠ 0 := C.c_ne_zero hx₀
  set f : ↥K →* L3.Γ := C.ρ.comp (Subgroup.inclusion hKX) with hf
  have hfs : Function.Surjective f := by
    intro γ
    obtain ⟨g, hgK, hg⟩ := C.image_K γ
    exact ⟨⟨g, hgK⟩, hg⟩
  set P := ((T ⊓ K).subgroupOf K).map f with hP
  have hidx : ¬ 2 ∣ P.index := fun h => hsyl.2.2 (h.trans (Subgroup.index_map_dvd _ hfs))
  have h8 : 8 ∣ Nat.card ↥P := by
    have h1 := P.index_mul_card
    rw [HSType.card_SL_three_two] at h1
    have hcop : Nat.Coprime 8 P.index :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hidx)))
    exact hcop.dvd_of_dvd_mul_left ⟨21, by omega⟩
  have hPpos : 0 < Nat.card ↥P := Nat.card_pos
  have hPfix : ∀ σ ∈ P, L3.act σ p = p := by
    rintro _ ⟨k, hk, rfl⟩
    have hkT : (k : G) ∈ T := (mem_inf.1 (mem_subgroupOf.1 hk)).1
    refine (C.fix_iff (Subgroup.inclusion hKX k) x₀).1 ?_
    show (k : G) * x₀ * (k : G)⁻¹ = x₀
    rw [mem_centralizer_iff.mp hx₀T (k : G) hkT, mul_inv_cancel_right]
  have hT2 : IsPGroup 2 ↥((T ⊓ K).subgroupOf K) := by
    have h1 : IsPGroup 2 ↥(T ⊓ K) := hsyl.2.1
    exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP2 : ∀ σ ∈ P, σ ^ 8 = 1 := by
    intro σ hσ
    obtain ⟨k, hk⟩ := (hT2.map f) ⟨σ, hσ⟩
    exact l3_pow_eight (k := k) (by simpa using congrArg Subtype.val hk)
  have key : ∃ σ ∈ P, σ ∈ L3.AS {0, p} ∧ σ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hinv : ∀ σ ∈ P, σ * σ = 1 := by
      intro σ hσ
      by_contra h
      exact h (hno _ (mul_mem hσ hσ) (l3_sq_mem p hp0 σ (hPfix σ hσ) (hP2 σ hσ) h))
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at h8
      norm_num at h8
    obtain ⟨⟨σ, hσP⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
    by_cases hτ : ∃ τ ∈ P, τ ≠ 1 ∧ τ ≠ σ
    · obtain ⟨τ, hτP, hτ1, hτσ⟩ := hτ
      have hσE : σ ∉ L3.AS {0, p} := fun h => hσ1' (hno σ hσP h)
      have hτE : τ ∉ L3.AS {0, p} := fun h => hτ1 (hno τ hτP h)
      have hστP : σ * τ ∈ P := mul_mem hσP hτP
      have hm := l3_prod_mem p hp0 σ (hPfix σ hσP) τ (hPfix τ hτP) (hinv σ hσP) (hinv τ hτP)
        hσE hτE (Ne.symm hτσ) (hP2 _ hστP)
      have h1 : σ * τ ≠ 1 := by
        intro h
        apply hτσ
        calc τ = (σ * σ) * τ := by rw [hinv σ hσP, one_mul]
          _ = σ * (σ * τ) := by group
          _ = σ := by rw [h, mul_one]
      exact h1 (hno _ hστP hm)
    · push Not at hτ
      have hP2' : Nat.card ↥P ≤ 2 := by
        refine (card_le_of_maps_to (fun τ : ↥P => (τ : L3.Γ)) Subtype.val_injective {1, σ}
          fun τ => ?_).trans Finset.card_le_two
        by_cases h : (τ : L3.Γ) = 1
        · simp [h]
        · simp [hτ τ τ.2 h]
      obtain ⟨c, hc⟩ := h8
      omega
  obtain ⟨σ, ⟨k, hk, rfl⟩, hσE, hσ1⟩ := key
  exact ⟨Subgroup.inclusion hKX k, mem_subgroupOf.1 hk, hσE, hσ1⟩

end L3Coords

end CFSG.Quasithin.H13.NQS134
