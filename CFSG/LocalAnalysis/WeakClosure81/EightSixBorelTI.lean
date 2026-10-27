module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

theorem inf_normalizer_eq_bot_or_commute_or_le_kGenIn (h : Hyp83 V H T)
    (hKT : H = kGenIn V H ⊔ T) {g a : G} (hUH : conjSubgroup V g ≤ H) (ha : a ∈ H) :
    conjSubgroup V g ⊓ Subgroup.normalizer (conjSubgroup V a : Set G) = ⊥ ∨
      (∀ u ∈ conjSubgroup V g, ∀ x ∈ conjSubgroup V a, u * x = x * u) ∨
      conjSubgroup V g ≤ kGenIn V H := by
  by_cases hN : conjSubgroup V g ⊓ Subgroup.normalizer (conjSubgroup V a : Set G) = ⊥
  · exact Or.inl hN
  · rcases two_conj_eq_or_comm h.elemAbelian h.isTI ⟨g, rfl⟩ ⟨a, rfl⟩ hN with
      hcomm | ⟨y, hy, hXy⟩
    · exact Or.inr (Or.inl hcomm)
    · refine Or.inr (Or.inr ?_)
      have hXH : conjSubgroup V a ≤ H := by
        intro x hx
        have h1 : a * x * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
        have h2 : a * x * a⁻¹ ∈ H := h.le_H h1
        have hx' : x = a⁻¹ * (a * x * a⁻¹) * a := by group
        rw [hx']
        exact H.mul_mem (H.mul_mem (H.inv_mem ha) h2) ha
      have hyH : y ∈ H := sup_le hUH hXH hy
      have hXK : conjSubgroup V a ≤ kGenIn V H := by
        intro x hx
        have h1 : a * x * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
        have h2 : a⁻¹ * (a * x * a⁻¹) * a ∈ conjClosure V H := by
          simpa using mem_conjClosure (H.inv_mem ha) h1
        have h3 : a⁻¹ * (a * x * a⁻¹) * a = x := by group
        rw [← h.conjClosure_eq_kGenIn hKT]
        simpa [h3] using h2
      have hU : conjSubgroup V g = conjSubgroup (conjSubgroup V a) y⁻¹ := by
        rw [hXy, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      intro u hu
      have huy : y⁻¹ * u * y ∈ conjSubgroup V a := by
        rw [hU] at hu
        have h1 := mem_conjSubgroup_iff.mp hu
        simpa using h1
      have huyK : y⁻¹ * u * y ∈ kGenIn V H := hXK huy
      have hyN : y ∈ Subgroup.normalizer (kGenIn V H : Set G) :=
        h.le_normalizer_kGenIn_of_eq_sup hKT hyH
      have hmem : y * (y⁻¹ * u * y) * y⁻¹ ∈ kGenIn V H :=
        (Subgroup.mem_normalizer_iff.mp hyN (y⁻¹ * u * y)).mp huyK
      have hconj : y * (y⁻¹ * u * y) * y⁻¹ = u := by group
      rwa [hconj] at hmem

end CFSG.LocalAnalysis.WeakClosure81

end
