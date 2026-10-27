module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace Ctx812

theorem false_of_le_normalizer_Lf (c : Ctx812 G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) : False := by
  haveI : Fact p.Prime := ⟨(c.sig_prime p hp).1⟩
  have hle : ∀ i, CFSG.Open.pRank p (d.Lf i) ≤ 1 :=
    c.pRank_Lf_le_one hp h76 d hdM hdL hP hdS hPn
  obtain ⟨T, hTp, hT1, hTle, hsum⟩ :=
    c.exists_isPGroup_le_centralizer_AA hp d hdM hdL hinj hperm hle
  obtain ⟨k, k', hkk', hk, hk'⟩ : ∃ k k' : Fin 3, k ≠ k' ∧
      CFSG.Open.pRank p (d.Lf k) = 1 ∧ CFSG.Open.pRank p (d.Lf k') = 1 := by
    have h := hsum (c.pRank_inf_centralizer_AA_le_one hp h76 d hdM hdL hP hdS hPn)
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := c.three_le_k
    by_cases ha : CFSG.Open.pRank p (d.Lf 0) = 1
    · by_cases hb : CFSG.Open.pRank p (d.Lf 1) = 1
      · exact ⟨0, 1, by decide, ha, hb⟩
      · exact ⟨0, 2, by decide, ha, by omega⟩
    · exact ⟨1, 2, by decide, by omega, by omega⟩
  obtain ⟨⟨e, heT⟩, he⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
  have he1 : e ≠ 1 := fun h => he (Subtype.ext h)
  have hep : IsPGroup p (Subgroup.zpowers e) :=
    hTp.to_le ((Subgroup.zpowers_le (H := T)).mpr heT)
  have heM : e ∈ c.S.M := (hTle heT).1
  have heN : ∀ i, e ∈ Subgroup.normalizer (d.Lf i : Set G) :=
    d.le_normalizer_Lf_of_isPGroup (c.five_le_of_mem_sigma hp) hinj (hdM ▸ hperm)
      (hdM ▸ heM) hep
  exact c.false_of_pElement_centralizer_AA_of_ne hp h76 d hdM hdL hP hdS hPn hkk' hk hk'.ge
    he1 hep heM (hTle heT).2 heN

end Ctx812

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
