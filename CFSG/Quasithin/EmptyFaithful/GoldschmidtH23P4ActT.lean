module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Act
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Cen
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Quasithin.H23Out CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

@[instance_reducible] def conjAction {Γ : Type*} [Group Γ] (P E : Subgroup Γ)
    (h : ∀ s ∈ P, ∀ e ∈ E, s * e * s⁻¹ ∈ E) : MulAction P E where
  smul s e := ⟨s * e * s⁻¹, h s s.2 e e.2⟩
  one_smul e := by
    apply Subtype.ext
    show (1 : Γ) * (e : Γ) * (1 : Γ)⁻¹ = e
    simp
  mul_smul a b e := by
    apply Subtype.ext
    show ((a : Γ) * b) * (e : Γ) * ((a : Γ) * b)⁻¹ =
      (a : Γ) * ((b : Γ) * e * (b : Γ)⁻¹) * (a : Γ)⁻¹
    group

theorem card_modEq_conj {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    {P E : Subgroup Γ} (hP : IsPGroup p P) (h : ∀ s ∈ P, ∀ e ∈ E, s * e * s⁻¹ ∈ E) :
    Nat.card E ≡ Nat.card {e : E | ∀ s ∈ P, s * (e : Γ) * s⁻¹ = e} [MOD p] := by
  let _ : MulAction P E := conjAction P E h
  have h1 := IsPGroup.card_modEq_card_fixedPoints (α := E) hP
  have hset : {e : E | ∀ s ∈ P, s * (e : Γ) * s⁻¹ = e} = MulAction.fixedPoints P E := by
    ext e
    simp only [Set.mem_ofPred_eq, MulAction.mem_fixedPoints]
    constructor
    · intro he s
      apply Subtype.ext
      exact he s s.2
    · intro he s hs
      exact congrArg Subtype.val (he ⟨s, hs⟩)
  rw [hset]
  exact h1

theorem exists_central_of_normalized {Γ : Type*} [Group Γ] [Finite Γ] {S₀ E : Subgroup Γ}
    (hS : IsPGroup 2 S₀) (hE : E ≠ ⊥) (hn : ∀ s ∈ S₀, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    (hES : E ≤ S₀) : ∃ z ∈ E, z ≠ 1 ∧ ∀ s ∈ S₀, s * z = z * s := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_conj (p := 2) hS hn
  have hEP : IsPGroup 2 E := hS.to_le hES
  obtain ⟨n, hn2⟩ := hEP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hE
    rw [pow_zero] at hn2
    exact Subgroup.eq_bot_of_card_eq E hn2
  have heven : 2 ∣ Nat.card E := by
    rw [hn2]
    exact dvd_pow_self 2 hn0
  have hfix_even : 2 ∣ Nat.card {e : E | ∀ s ∈ S₀, s * (e : Γ) * s⁻¹ = e} :=
    (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 heven)))
  have hone : (1 : E) ∈ {e : E | ∀ s ∈ S₀, s * (e : Γ) * s⁻¹ = e} := by
    intro s _
    simp
  by_contra hcon
  push Not at hcon
  have hsub : {e : E | ∀ s ∈ S₀, s * (e : Γ) * s⁻¹ = e} ⊆ {1} := by
    intro e he
    by_contra hne
    have he1 : (e : Γ) ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨s, hs, hsne⟩ := hcon e e.2 he1
    exact hsne (by have := he s hs; calc s * e = (s * e * s⁻¹) * s := by group
                                         _ = e * s := by rw [this])
  have hcard : Nat.card {e : E | ∀ s ∈ S₀, s * (e : Γ) * s⁻¹ = e} = 1 := by
    have hsubs : Subsingleton {e : E | ∀ s ∈ S₀, s * (e : Γ) * s⁻¹ = e} :=
      (Set.subsingleton_coe _).2 (Set.subsingleton_singleton.anti hsub)
    exact Nat.card_eq_one_iff_unique.2 ⟨hsubs, ⟨⟨1, hone⟩⟩⟩
  rw [hcard] at hfix_even
  omega

theorem eq_one_of_commutator_eq {Γ : Type*} [Group Γ] [Finite Γ] {P E : Subgroup Γ}
    (hP : IsPGroup 5 P) (hE2 : IsPGroup 2 E) (hEc : Nat.card E ≤ 16)
    (hEn : ∀ s ∈ P, ∀ e ∈ E, s * e * s⁻¹ ∈ E) (hEP : ⁅E, P⁆ = E) (hE : E ≠ ⊥) :
    ∀ e ∈ E, (∀ s ∈ P, s * e = e * s) → e = 1 := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := card_modEq_conj (p := 5) hP hEn
  set F : Subgroup Γ := E ⊓ Subgroup.centralizer (P : Set Γ) with hF
  have hFE : F ≤ E := inf_le_left
  have hFcard : Nat.card {e : E | ∀ s ∈ P, s * (e : Γ) * s⁻¹ = e} = Nat.card F := by
    apply Nat.card_congr
    refine
      { toFun := fun e => ⟨e.1.1, e.1.2, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
        invFun := fun f => ⟨⟨f.1, f.2.1⟩, fun s hs => ?_⟩
        left_inv := fun e => rfl
        right_inv := fun f => rfl }
    · have := e.2 s hs
      calc s * (e.1 : Γ) = (s * e.1 * s⁻¹) * s := by group
        _ = e.1 * s := by rw [this]
    · have := Subgroup.mem_centralizer_iff.1 f.2.2 s hs
      calc s * f.1 * s⁻¹ = (s * f.1) * s⁻¹ := rfl
        _ = (f.1 * s) * s⁻¹ := by rw [this]
        _ = f.1 := by group
  rw [hFcard] at hmod
  obtain ⟨m, hm⟩ := hE2.exists_card_eq
  obtain ⟨j, hj⟩ := (hE2.to_le hFE).exists_card_eq
  have hm4 : m ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hjm : j ≤ m := by
    have hd : Nat.card F ∣ Nat.card E := Subgroup.card_dvd_of_le hFE
    rw [hj, hm] at hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  rw [hj, hm] at hmod
  have hcases : j = m ∨ (m = 4 ∧ j = 0) := by
    interval_cases m <;> interval_cases j <;> simp_all [Nat.ModEq]
  rcases hcases with rfl | ⟨-, rfl⟩
  ·
    exfalso
    apply hE
    have hFeq : F = E := Subgroup.eq_of_le_of_card_ge hFE (by rw [hj, hm])
    rw [← hEP]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.2
    intro e he
    have : e ∈ F := hFeq ▸ he
    exact this.2
  · intro e he hc
    have hFbot : F = ⊥ := Subgroup.eq_bot_of_card_eq F (by rw [hj, pow_zero])
    have : e ∈ F := ⟨he, Subgroup.mem_centralizer_iff.2 fun s hs => hc s hs⟩
    rw [hFbot, Subgroup.mem_bot] at this
    exact this

theorem false_of_overgroup_cen {Γ : Type*} [Group Γ] [Finite Γ] (hZ : Subgroup.center Γ = ⊥)
    (hOut : Out5Pow Γ) (hCen : CenOvergroup Γ) {A : Type*} [Group A] [Finite A]
    (ρ : A →* MulAut Γ) {X Y W : Subgroup A} (hX : IsPGroup 2 X) (hY : IsPGroup 5 Y)
    (hXY : (X : Set A) * Y = Y * X) {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hsub : ∀ s ∈ S₀, (MulAut.conj s : MulAut Γ) ∈ X.map ρ)
    (hWX : W ≤ X) (hWXn : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hWYn : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W)
    (hWc : Nat.card W ≤ 16) (hWY : ⁅W, Y⁆ = W) (hWne : ¬ W ≤ ρ.ker) : False := by
  classical
  obtain ⟨U, b, hS₀U, hb, hYU, hb0, hSg⟩ := key_overgroup hZ hOut ρ hX hY hXY hS₀ hsub
  have hinj := conj_injective_of_center_eq_bot hZ
  set c : Γ →* MulAut Γ := MulAut.conj with hc
  set E : Subgroup (MulAut Γ) := W.map ρ with hE
  set P₅ : Subgroup (MulAut Γ) := Y.map ρ with hP₅
  have hEcomm : E = ⁅E, P₅⁆ := by rw [hE, hP₅, ← Subgroup.map_commutator, hWY]
  have hE_ne : E ≠ ⊥ := by
    intro h
    apply hWne
    intro w hw
    have : ρ w ∈ E := ⟨w, hw, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hb_pos : 0 < b := by
    by_contra h0
    have hker := hb0 (Nat.eq_zero_of_not_pos h0)
    have hP₅bot : P₅ = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hker hy
    apply hE_ne
    rw [hEcomm, hP₅bot, Subgroup.commutator_bot_right]
  have hP₅I : P₅ ≤ inner Γ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, -, hg⟩ := hYU y hy
    exact ⟨g, hg.symm⟩
  have hEI : E ≤ inner Γ := by
    calc E = ⁅E, P₅⁆ := hEcomm
      _ ≤ ⁅E, inner Γ⁆ := Subgroup.commutator_mono le_rfl hP₅I
      _ ≤ inner Γ := Subgroup.commutator_le_right E (inner Γ)
  set Et : Subgroup Γ := E.comap c with hEt
  have hEtS : Et ≤ S₀ := by
    intro g hg
    obtain ⟨w, hw, hwg⟩ := hg
    exact hSg w (hWX hw) g hwg
  have hEtne : Et ≠ ⊥ := by
    intro h
    apply hE_ne
    refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
    obtain ⟨g, hg⟩ := hEI he
    have : g ∈ Et := by
      show c g ∈ E
      rw [hg]
      exact he
    rw [h, Subgroup.mem_bot] at this
    rw [← hg, this, map_one]
  have hEtn : ∀ s ∈ S₀, ∀ e ∈ Et, s * e * s⁻¹ ∈ Et := by
    intro s hs g hg
    obtain ⟨x, hx, hxs⟩ := hsub s hs
    obtain ⟨w, hw, hwg⟩ := hg
    have h1 := hWXn x hx w hw
    show c (s * g * s⁻¹) ∈ E
    rw [map_mul, map_mul, map_inv]
    refine ⟨x * w * x⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv, hxs, hwg]
  obtain ⟨z, hzE, hz1, hzc⟩ := exists_central_of_normalized (isSylowTwoOf_top_iff.1 hS₀).1
    hEtne hEtn hEtS
  have hUz := hCen S₀ U hS₀ hS₀U b hb_pos hb z (hEtS hzE) hzc
  have hEn : ∀ s ∈ P₅, ∀ e ∈ E, s * e * s⁻¹ ∈ E := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    exact ⟨y * w * y⁻¹, hWYn y hy w hw, by simp⟩
  have hEcard : Nat.card E ≤ 16 :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (H := W) ρ)).trans hWc
  have hfix := eq_one_of_commutator_eq (hY.map ρ) ((hX.to_le hWX).map ρ) hEcard hEn
    hEcomm.symm hE_ne
  have hcz : c z = 1 := by
    refine hfix (c z) hzE ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, hgU, hg⟩ := hYU y hy
    rw [hg, ← map_mul, ← map_mul, hUz g hgU]
  exact hz1 (hinj (hcz.trans (map_one c).symm))

end CFSG.Quasithin.H23P4
