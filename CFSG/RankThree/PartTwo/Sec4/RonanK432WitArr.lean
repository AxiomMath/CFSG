module

public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem getElem!_map_arr {α β : Type*} [Inhabited α] [Inhabited β] (A : Array α) (f : α → β)
    {k : ℕ} (hk : k < A.size) : (A.map f)[k]! = f A[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos A k hk]

theorem wordA_rep_mem {n : ℕ} {S : Array (Array ℕ)} {K : Subgroup (Equiv.Perm (Fin n))} {j : ℕ}
    (hj : j ≤ S.size) (hv : ∀ k < S.size, validA n S[k]! = true)
    (hK : ∀ k < j, permOfArr n S[k]! ∈ K) :
    ∀ w : List ℤ, lettersOK j w = true →
      ∃ g ∈ K, Rep n (wordA n S (S.map (invCand n)) w) g
  | [], _ => ⟨1, K.one_mem, rep_idA⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g, hgK, hg⟩ := wordA_rep_mem hj hv hK w hw'
    have hlet : ∃ h ∈ K, Rep n (letterA S (S.map (invCand n)) l) h := by
      unfold letterA
      by_cases hpos : 0 < l
      · rw [if_pos hpos]
        have hk : l.toNat - 1 < j := by omega
        exact ⟨permOfArr n S[l.toNat - 1]!, hK _ hk, rep_of_validA (hv _ (by omega))⟩
      · rw [if_neg hpos]
        have hk : (-l).toNat - 1 < j := by omega
        refine ⟨(permOfArr n S[(-l).toNat - 1]!)⁻¹, K.inv_mem (hK _ hk), ?_⟩
        rw [getElem!_map_arr S _ (by omega)]
        exact rep_inv_of_validA (hv _ (by omega))
    obtain ⟨h, hhK, hh⟩ := hlet
    exact ⟨h * g, K.mul_mem hhK hgK, rep_compA hh hg⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
