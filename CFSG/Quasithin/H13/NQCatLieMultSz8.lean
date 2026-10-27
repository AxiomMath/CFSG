module

public import CFSG.Quasithin.H13.NQCatLieMult

public section

namespace CFSG.Quasithin.H13.NQCat.LieMult

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.PFAppendixIII CFSG.ShultStronglyClosedTI

theorem isSylowTwoOf_suzukiCoverRoot {m : ℕ} (hm : 0 < m) :
    IsSylowTwoOf (suzukiCoverRoot m) ⊤ := by
  refine ⟨le_top, (suzukiCoverRoot_structure m hm).1, ?_⟩
  rw [show ((suzukiCoverRoot m).subgroupOf ⊤).index = (suzukiCoverRoot m).index from
    Subgroup.relIndex_top_right _]
  exact (suzukiCoverRoot_index_odd m hm).not_two_dvd_nat

theorem card_le_of_le_centralizer_suzukiCoverRoot {m : ℕ} (hm : 0 < m)
    {E : Subgroup (SuzukiMatrixGroup m)} (hEU : E ≤ suzukiCoverRoot m)
    (hEC : E ≤ Subgroup.centralizer (suzukiCoverRoot m : Set (SuzukiMatrixGroup m))) :
    Nat.card E ≤ 2 ^ (2 * m + 1) := by
  obtain ⟨-, -, hcomm, hmem⟩ := suzukiCoverRoot_structure m hm
  have hb : ∀ x : E, ∃ b : BinaryGaloisField (2 * m + 1),
      (x : SuzukiMatrixGroup m) = ((suzukiCoverRootElement m 0 b : suzukiCoverRoot m) :
        SuzukiMatrixGroup m) := by
    intro x
    have hz : (⟨x, hEU x.2⟩ : suzukiCoverRoot m) ∈ Subgroup.center (suzukiCoverRoot m) := by
      rw [Subgroup.mem_center_iff]
      intro u
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEC x.2) u u.2)
    rw [← hcomm] at hz
    obtain ⟨b, hb⟩ := (hmem _).1 hz
    exact ⟨b, congrArg Subtype.val hb⟩
  choose β hβ using hb
  have hinj : Function.Injective β := fun x y hxy => by
    apply Subtype.ext
    rw [hβ x, hβ y, hxy]
  calc Nat.card E ≤ Nat.card (BinaryGaloisField (2 * m + 1)) := Nat.card_le_card_of_injective β hinj
    _ = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)

theorem sz8NoCentralE16_holds : Sz8NoCentralE16 := by
  intro S _ _ hS
  obtain ⟨-, a, ha, K, _, _, h3, hK, ⟨e⟩⟩ := hS
  obtain rfl : a = 1 := by omega
  refine NoCentralE16.of_mulEquiv (e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 1 K)).trans
    ((glaSzEquivNative 1 ha hK).trans (suzukiCoverNativeEquiv 1))))
    (noCentralE16_of_sylow (isSylowTwoOf_suzukiCoverRoot one_pos) fun E hEU hEC => ?_)
  have h1 := card_le_of_le_centralizer_suzukiCoverRoot one_pos hEU hEC
  norm_num at h1
  omega

end CFSG.Quasithin.H13.NQCat.LieMult
