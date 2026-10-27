module

public import CFSG.Quasithin.Vol2.Ch3zXLev
public import CFSG.Milestones.ASVolI.C61.HypSL2
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Fix

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Quasithin

private theorem s66nat_sl2_eq_one {K : Type} [Field K] (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : ∀ v : Fin 2 → K, Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v) : γ = 1 := by
  have hM : (γ : Matrix (Fin 2) (Fin 2) K) = 1 :=
    Matrix.ext_of_mulVec_single (fun i => by rw [Matrix.one_mulVec]; exact h _)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun hM i) j

private theorem s66nat_eq_one_of_fix {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {K : Type} [Field K] (π : Matrix.SpecialLinearGroup (Fin 2) K →* ↥H)
    (β : ↥U →* Multiplicative (Fin 2 → K)) (hβ : Function.Bijective β)
    (hβeq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) K) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ =
        Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β u))))
    (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (hfix : ∀ w : ↥U, ((π γ : ↥H) : MulAut V) (w : V) = (w : V)) : γ = 1 := by
  apply s66nat_sl2_eq_one
  intro v
  obtain ⟨w, hw⟩ := hβ.2 (Multiplicative.ofAdd v)
  have hu : ((π γ : ↥H) : MulAut V) (w : V) ∈ U := by
    rw [hfix w]
    exact w.2
  have h1 := hβeq γ w hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) (w : V), hu⟩ : ↥U) = w := Subtype.ext (hfix w)
  rw [h2, hw] at h1
  have h3 := congrArg Multiplicative.toAdd h1
  simpa using h3.symm

private theorem s66nat_ncard_fix_eq_natCard {V : Type} [CommGroup V] {U : Subgroup V} {K : Type} [Field K]
    (β : ↥U →* Multiplicative (Fin 2 → K)) (hβ : Function.Bijective β) (k : MulAut V)
    (hkU : ∀ u ∈ U, k u ∈ U) (γ : Matrix.SpecialLinearGroup (Fin 2) K)
    (hβeq : ∀ w : ↥U, β ⟨k (w : V), hkU _ w.2⟩ =
      Multiplicative.ofAdd ((γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (β w)))) :
    Set.ncard {u : V | u ∈ U ∧ k u = u} =
      Nat.card {v : Fin 2 → K // Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v} := by
  have himg : Subtype.val '' {w : ↥U | k (w : V) = (w : V)} = {u : V | u ∈ U ∧ k u = u} := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hu, hk⟩
      exact ⟨⟨u, hu⟩, hk, rfl⟩
  have hbij : Function.Bijective (fun w : ↥U => Multiplicative.toAdd (β w)) :=
    Multiplicative.toAdd.bijective.comp hβ
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) ?_)
  intro w
  show k (w : V) = (w : V) ↔
    Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w)
  constructor
  · intro hw
    have h1 : (⟨k (w : V), hkU _ w.2⟩ : ↥U) = w := Subtype.ext hw
    have h2 := hβeq w
    rw [h1] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    simpa using h3.symm
  · intro hv
    have h2 : β ⟨k (w : V), hkU _ w.2⟩ = β w := by
      rw [hβeq w, hv, ofAdd_toAdd]
    exact congrArg Subtype.val (hβ.1 h2)

theorem natBlock_fix_ncard_le_four {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    (hN : Ch3z.NatBlockData H U 2) {k : MulAut V} (hk : k ∈ H)
    (hkU : ∀ u ∈ U, k u ∈ U) (hsq : ∀ u ∈ U, k (k u) = u) (hne : ∃ u ∈ U, k u ≠ u) :
    Set.ncard {u : V | u ∈ U ∧ k u = u} ≤ 4 := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  obtain ⟨γ, hγ⟩ := hπs ⟨k, hk⟩
  have hg : ((π γ : ↥H) : MulAut V) = k := congrArg Subtype.val hγ
  subst hg
  have hK4 : Nat.card K = 4 := hK.trans (by norm_num)
  have hsq' : ∀ w : ↥U, ((π (γ ^ 2) : ↥H) : MulAut V) (w : V) = (w : V) := by
    intro w
    rw [map_pow, Subgroup.coe_pow, sq, MulAut.mul_apply]
    exact hsq _ w.2
  have h2 : γ ^ 2 = 1 := s66nat_eq_one_of_fix π β hβ hβeq (γ ^ 2) hsq'
  have h1 : γ ≠ 1 := by
    intro h
    obtain ⟨u, hu, hne'⟩ := hne
    apply hne'
    simp [h]
  rw [s66nat_ncard_fix_eq_natCard β hβ _ hkU γ (fun w => hβeq γ w (hkU _ w.2))]
  exact (card_fixed_of_involution_four hK4 γ h2 h1).le

theorem natBlock_isSimpleGroup {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (he : 2 ≤ e) (hN : Ch3z.NatBlockData H U e) : IsSimpleGroup ↥H := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have hinj : Function.Injective π := (injective_iff_map_eq_one π).mpr fun γ hγ =>
    s66nat_eq_one_of_fix π β hβ hβeq γ (fun w => by simp [hγ])
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ASVolI.burnsideC56_sl2_isSimple he hcard
  exact (MulEquiv.ofBijective π ⟨hinj, hπs⟩).symm.isSimpleGroup

theorem natBlock_not_isMulCommutative {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {e : ℕ} (he : 2 ≤ e) (hN : Ch3z.NatBlockData H U e) : ¬ IsMulCommutative ↥H := by
  intro hcomm
  haveI := natBlock_isSimpleGroup he hN
  haveI : Group.IsPerfect ↥H := Ch3z.NatBlockData.isPerfect he hN
  exact Group.IsPerfect.not_isMulCommutative ↥H hcomm

theorem natBlock_card {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (hN : Ch3z.NatBlockData H U e) : Nat.card ↥H = 2 ^ e * ((2 ^ e) ^ 2 - 1) := by
  obtain ⟨K, instK, instF, hK, π, β, hπs, hβ, hβeq⟩ := hN
  have hinj : Function.Injective π := (injective_iff_map_eq_one π).mpr fun γ hγ =>
    s66nat_eq_one_of_fix π β hβ hβeq γ (fun w => by simp [hγ])
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  rw [← Nat.card_congr (Equiv.ofBijective (⇑π) ⟨hinj, hπs⟩), card_specialLinear_two K, hcard]

theorem natBlock_eq_two_of_card {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V} {e : ℕ}
    (hN : Ch3z.NatBlockData H U e) (hc : Nat.card ↥H = 60) : e = 2 := by
  have h := natBlock_card hN
  rw [hc] at h
  exact exp_eq_two_of_card_specialLinear h.symm

end CFSG.Quasithin.H13.L319.S66

end
