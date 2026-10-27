module

public import CFSG.Adapters.WholeGroupLayer
public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Quasithin.A1b

section Aut

variable {S : Type} [Group S] [Finite S]

theorem center_eq_bot_of_simple_nonabelian [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : x ∈ Subgroup.center S := by
      rw [h]
      exact Subgroup.mem_top x
    exact hxy (Subgroup.mem_center_iff.mp hx y).symm

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : a ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : a * g * a⁻¹ = g := by
      have := congrArg (fun φ : MulAut S => φ g) ha
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

noncomputable def innerEquiv (hZ : Subgroup.center S = ⊥) : S ≃* ↥(inner S) :=
  MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)

theorem centralizer_inner_eq_bot (hZ : Subgroup.center S = ⊥) :
    Subgroup.centralizer ((inner S : Subgroup (MulAut S)) : Set (MulAut S)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_centralizer_iff] at hα
  have hconj : ∀ g : S, MulAut.conj (α g) = MulAut.conj g := by
    intro g
    have hmem : MulAut.conj g ∈ inner S := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    have hcomm := hα (MulAut.conj g) hmem
    apply MulEquiv.ext
    intro x
    have hx := congrArg (fun φ : MulAut S => φ (α.symm x)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply, map_mul,
      map_inv] at hx
    simp only [MulAut.conj_apply]
    exact hx.symm
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro g
  show α g = g
  exact conj_injective_of_center_eq_bot hZ (hconj g)

theorem generalizedFitting_mulAut_eq_inner [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x) :
    CFSG.generalizedFitting (MulAut S) = inner S := by
  have hZ := center_eq_bot_of_simple_nonabelian hnc
  have hsimple : IsSimpleGroup ↥(inner S) := (innerEquiv hZ).symm.isSimpleGroup
  have hnc' : ∃ x y : ↥(inner S), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨innerEquiv hZ x, innerEquiv hZ y, fun h => hxy ?_⟩
    apply (innerEquiv hZ).injective
    rw [map_mul, map_mul]
    exact h
  exact CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot (inner S)
    hnc' (centralizer_inner_eq_bot hZ)

private theorem sup_eq_top_of_index_two {G : Type*} [Group G] (I T : Subgroup G)
    (hI : I.index = 2) (hT : IsSylowIn 2 T ⊤) : I ⊔ T = ⊤ := by
  have hle : I ≤ I ⊔ T := le_sup_left
  have hdvd : (I ⊔ T).index ∣ 2 := by
    have := Subgroup.index_dvd_of_le hle
    rwa [hI] at this
  have hmul : I.relIndex (I ⊔ T) * (I ⊔ T).index = 2 := by
    rw [Subgroup.relIndex_mul_index hle, hI]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hrel : I.relIndex (I ⊔ T) = 1 := by
      rw [h2] at hmul
      omega
    have hJ : I ⊔ T ≤ I := Subgroup.relIndex_eq_one.mp hrel
    have hTle : T ≤ I := le_trans le_sup_right hJ
    have hdvd2 : I.index ∣ T.index := Subgroup.index_dvd_of_le hTle
    rw [hI] at hdvd2
    apply hT.not_dvd_relIndex
    rw [Subgroup.relIndex_top_right]
    exact hdvd2

theorem exists_sylow_sup_inner_eq_top (hout : Nat.card (Outer S) = 2) :
    ∃ T' : Subgroup (MulAut S), IsSylowIn 2 T' ⊤ ∧ inner S ⊔ T' = ⊤ := by
  obtain ⟨T', hT'⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup (MulAut S))
  refine ⟨T', hT', ?_⟩
  have hidx : (inner S : Subgroup (MulAut S)).index = 2 := hout
  exact sup_eq_top_of_index_two _ T' hidx hT'

theorem exists_data_mulAut [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x)
    (hout : Nat.card (Outer S) = 2) :
    ∃ T' : Subgroup (MulAut S), IsSylowIn 2 T' ⊤ ∧
      CFSG.generalizedFitting (MulAut S) ⊔ T' = ⊤ ∧
      IsSimpleGroup ↥(CFSG.generalizedFitting (MulAut S)) ∧
      Nonempty (S ≃* ↥(CFSG.generalizedFitting (MulAut S))) := by
  obtain ⟨T', hT', hsup⟩ := exists_sylow_sup_inner_eq_top hout
  have hZ := center_eq_bot_of_simple_nonabelian hnc
  have hF := generalizedFitting_mulAut_eq_inner hnc
  refine ⟨T', hT', ?_, ?_, ?_⟩
  · rw [hF]
    exact hsup
  · rw [hF]
    exact (innerEquiv hZ).symm.isSimpleGroup
  · rw [hF]
    exact ⟨innerEquiv hZ⟩

end Aut

end CFSG.Quasithin.RonanE114
