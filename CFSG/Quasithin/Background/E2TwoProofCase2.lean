module

public import CFSG.Quasithin.Background.E2TwoProofN
public import CFSG.Quasithin.Background.E2TwoProofAS
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ} (S : Setting H T M L K)
include S

theorem a23List_L (hA21 : AsA21SQTKSection) (hList : A23SQTKListFact) : A23List ↥L := by
  have : Finite (E2.StarQuot M H) := finite_starQuot M H
  have hsq := sqtkGroup_star hA21 S.minPar S.sqtk S.ns
  have hL := S.factor.simple
  have hne := S.factor.exists_ne_comm
  have hbot : (⊥ : Subgroup ↥L).Normal := Subgroup.normal_bot
  have e : ↥L ⧸ (⊥ : Subgroup ↥L) ≃* ↥L := QuotientGroup.quotientBot
  have hs : IsSimpleGroup (↥L ⧸ (⊥ : Subgroup ↥L)) := (MulEquiv.isSimpleGroup_congr e).mpr hL
  have hne' : ∃ a b : ↥L ⧸ (⊥ : Subgroup ↥L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact A36A.a23List_of_mulEquiv e.symm (hList _ hsq L ⊥ hs hne')

theorem cases_of_normal (hF : E22Families) (h36 : A36CoreForSQTKCat) (hA21 : AsA21SQTKSection)
    (hList : A23SQTKListFact) (hLn : L.Normal) : E2.E22CasesNoN H T M K := by
  have : Finite (E2.StarQuot M H) := finite_starQuot M H
  have hX : ASHyp L (E2.star M H T) (E2.star M H M) := S.factor.asHyp
  have hcases := asCases_of_families hF hX (S.a23List_L hA21 hList)
  have hK0 := S.normal_kZero hLn
  have hTN : T ≤ Subgroup.normalizer (K : Set Γ) := by
    intro t ht
    have htH : t ∈ H := S.minPar.isSylow.1 ht
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have hkH : k ∈ H := S.le hk
      have := hK0.conj_mem (⟨k, hkH⟩ : ↥H) hk ⟨t, htH⟩
      exact this
    · intro hk
      have hkH : k ∈ H := by
        have h1 : t⁻¹ * (t * k * t⁻¹) * t ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem htH) (S.le hk)) htH
        simpa [mul_assoc] using h1
      have h2 := hK0.conj_mem (⟨t * k * t⁻¹, S.le hk⟩ : ↥H) hk ⟨t, htH⟩⁻¹
      rw [Subgroup.mem_subgroupOf] at h2
      simpa [mul_assoc] using h2
  have hMK : E2.star M H (M ⊓ K) = E2.star M H M ⊓ L := by
    rw [star_inf_M, S.star_eq]
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ L := by
    rw [star_inf_T S.minPar.isSylow (subnormal_of_mem_cComp S.cComp) S.le, S.star_eq]
  unfold E2.E22CasesNoN
  simp only []
  rw [S.star_eq, hMK, hTK]
  refine Or.inr ⟨hTN, S.mem_kerIn_iff h36 hLn, ?_⟩
  rw [inf_comm (E2.star M H M) L] at *
  rcases hcases with ⟨n, hB, hBor⟩ | ⟨n, hn, hty, hD, hBor⟩ |
      ⟨p, e, hp, hp3, he, hcong, hty, hC, hA⟩ | ⟨p, hp, hp2, hty, hC⟩
  · exact Or.inl ⟨n, hB, by rwa [inf_comm]⟩
  · exact Or.inr (Or.inl ⟨n, hn, hty, hD, by rwa [inf_comm]⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hcong, hty, ?_, hA⟩))
    rw [inf_comm L (E2.star M H M), hC]
    rfl
  · refine Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hty, ?_⟩))
    rw [inf_comm L (E2.star M H M), hC]
    rfl

end Setting

end E2P

end CFSG.Quasithin
