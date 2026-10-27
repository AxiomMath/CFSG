module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

variable {G : Type} [Group G] [Finite G]

theorem qTwoFront_q_eq_one
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hG : QTwoJoinGuard p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] {f m : ℕ}
    (hlabel : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.rank + 1 = m ∧ lab.n = f) p Bs L)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hm : 4 ≤ m)
    (hperf : commutator L = ⊤) (hdvd : p ∣ 2 ^ f + 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ f))) :
    f = 1 := by
  by_contra hf1
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    simp at h1
  have hf2 : 2 ≤ f := by omega
  obtain ⟨-, -, -, ι, M, eM, -, -, r, -, -, h6⟩ := hG
  obtain ⟨lab, K', hKf, hKfin, hKchar, f', n, ψ, hP, hn, hf', hcard, h4, hker, hrange, -, hacts, -⟩ :=
    ggNSLie_cover_of_esu_pred
      (P := fun p lab => ggRowP_ESU p lab ∧ lab.rank + 1 = m ∧ lab.n = f)
      (fun p lab h => ⟨h.1, by rintro ⟨h1, -⟩; have := h.2.2; omega⟩) hlabel
  letI : Field K' := hKf
  letI : Finite K' := hKfin
  letI : CharP K' 2 := hKchar
  have hf'2 : 2 ≤ f' := by rw [hf', hP.2.2]; exact hf2
  exact qTwoFrontQ_core hcard hf'2 h4 hker hrange hacts (H := ggHyperplane Bs r)
    (Subgroup.map_subtype_le _) h6

end CFSG.StandardType.QTwo

end
