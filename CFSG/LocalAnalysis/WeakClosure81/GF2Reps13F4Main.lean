module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4C
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4E
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4G
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourClausesB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w16f_case_two (hW : ∀ w : W, w ^ 2 = 1) {Y K : Subgroup (MulAut W)}
    (hY : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥)
    (hK : IsComponentOf K Y) {t : MulAut W} (ht : t ∈ Y) (ht2 : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hrk3 : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K) (hL3 : UC22.IsL3 ↥K 1)
    (hnt : ¬ ∀ a ∈ K, ∀ u ∈ commSub ⊤ (Subgroup.zpowers t), (a * (t * a * t⁻¹)) u = u) :
    Conc4_134 Y K t := by
  have F : S134Frame Y K t := ⟨hW, hY, hK, ht, ht2, hrk, hrk3, hmove, hL3, hnt⟩
  by_cases ha : ∃ I ∈ irrSet K, commSub I (S134Conj t K) = ⊥
  · obtain ⟨I, hI, hKI⟩ := ha
    exact s134b_case_a F hI hKI
  · have hno : ∀ I ∈ irrSet K, commSub I (S134Conj t K) ≠ ⊥ := fun I hI h => ha ⟨I, hI, h⟩
    obtain ⟨x, hx, u, hu, hx7, hux, hw⟩ := s134b_caseB_data F hno
    obtain ⟨-, hirr, hcard, hKnt, hK'nt⟩ := s134b_caseB_irr F hx hu hx7 hux hw
    refine Or.inl ⟨Or.inl ⟨hL3, s134b_tensor_of_irr hW F.comm hL3 F.l3' hcard hirr hKnt hK'nt⟩, ?_⟩
    intro g hg hgL
    exact s134_clause_one (fun w => by rw [← sq]; exact hW w) hK ht hmove hirr hg hgL

end CFSG.LocalAnalysis.WeakClosure81
