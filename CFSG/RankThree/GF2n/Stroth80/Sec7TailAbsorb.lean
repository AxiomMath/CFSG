module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B B' : Subgroup G}

theorem CN_eq_of_rt_vt (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') {t s : G}
    (hR : Rt M (LB M Q B') s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B') B' Z s = Vt M (LB M Q B) B Z t) : hc'.CN s = hc.CN t := by
  ext x
  show x ∈ CNt M (LB M Q B') B' Z s ↔ x ∈ CNt M (LB M Q B) B Z t
  unfold CNt
  rw [hR, hV]

theorem omegaPlusNat_iff_of_rt_vt (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') {t s : G}
    (hR : Rt M (LB M Q B') s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B') B' Z s = Vt M (LB M Q B) B Z t) (k : ℕ) :
    OmegaPlusNat hc' s k ↔ OmegaPlusNat hc t k := by
  unfold OmegaPlusNat
  rw [hR, hV, CN_eq_of_rt_vt hc hc' hR hV]

theorem omegaMinusNat_iff_of_rt_vt (hc : Ctx M Q Z B) (hc' : Ctx M Q Z B') {t s : G}
    (hR : Rt M (LB M Q B') s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B') B' Z s = Vt M (LB M Q B) B Z t) (k : ℕ) :
    OmegaMinusNat hc' s k ↔ OmegaMinusNat hc t k := by
  unfold OmegaMinusNat
  rw [hR, hV, CN_eq_of_rt_vt hc hc' hR hV]

theorem sec7Hyp_conj_centre (hZt : Sec7ZtStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {m s : G} (hm : m ∈ M) (hsZ : s ∈ Z0) (hsQ : s ∉ Q)
    (hsL : s ∈ conjSubgroup m (LB M Q B)) :
    Sec7Hyp (hc.conj_of_mem hm) n s := by
  obtain ⟨hRs, hVs⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  obtain ⟨hRc, hVc⟩ := rt_vt_conj hc hm s
  have hR : Rt M (LB M Q (conjSubgroup m B)) s = Rt M (LB M Q B) t := hRc.trans hRs
  have hV : Vt M (LB M Q (conjSubgroup m B)) (conjSubgroup m B) Z s = Vt M (LB M Q B) B Z t :=
    hVc.trans hVs
  have hc' := hc.conj_of_mem hm
  refine
    { toSec5 :=
        { width := hs.toSec5.width
          n_gt := hs.toSec5.n_gt
          noA2 := hc.noA2_conj hs.toSec5.noA2 hm
          gen := hs.toSec5.gen.conj_of_mem hm
          mem := by rw [hc.LB_conj hm]; exact hsL
          notQ := hsQ }
      notPlus4 := ?_
      orth := ?_
      large := ?_ }
  · rw [omegaPlusNat_iff_of_rt_vt hc (hc.conj_of_mem hm) hR hV]; exact hs.notPlus4
  · obtain ⟨k, hk, h⟩ := hs.orth
    exact ⟨k, hk, by
      rw [omegaPlusNat_iff_of_rt_vt hc (hc.conj_of_mem hm) hR hV,
        omegaMinusNat_iff_of_rt_vt hc (hc.conj_of_mem hm) hR hV]; exact h⟩
  · rw [CN_eq_of_rt_vt hc (hc.conj_of_mem hm) hR hV]; exact hs.large

theorem centre_le_conj_LB (hZc : Sec7CentreMpStatement) (hZt : Sec7ZtStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {m s : G} (hm : m ∈ M) (hsZ : s ∈ Z0)
    (hsQ : s ∉ Q) (hsL : s ∈ conjSubgroup m (LB M Q B)) :
    Z0 ≤ conjSubgroup m (LB M Q B) := by
  have hs' := sec7Hyp_conj_centre hZt hc hs hZ0 hm hsZ hsQ hsL
  obtain ⟨hRs, -⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ hsQ
  have hR : Rt M (LB M Q (conjSubgroup m B)) s = Rt M (LB M Q B) t :=
    (rt_vt_conj hc hm s).1.trans hRs
  have hZ0' : IsCentrePre Z0 (Rt M (LB M Q (conjSubgroup m B)) s) Q := by rw [hR]; exact hZ0
  intro x hx
  have := (hZc G M Q Z (conjSubgroup m B) (hc.conj_of_mem hm) n s hs' Z0 hZ0' x hx).1
  rwa [hc.LB_conj hm] at this

end CFSG.RankThree.GF2n.Stroth80
