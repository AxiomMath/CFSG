module

public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_exists_Z0_not_Q (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ s ∈ Z0, s ∉ Q := by
  by_contra h
  push Not at h
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  have hcard := hZcard G M Q Z B hc n t hs Z0 hZ0
  have heq : Z0 = Q := le_antisymm h hQZ0
  rw [heq] at hcard
  have hq : 4 ≤ Nat.card Z := hc.hyp.q4
  have hpos : 0 < Nat.card Q := Nat.card_pos
  nlinarith

theorem sec7_normalizes_of_zt (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ NormH0 M Z Z0) :
    conjSubgroup g (Rt M (LB M Q B) t) = Rt M (LB M Q B) t ∧
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hgM : g ∈ M := hg.1.1
  have hgN : g ∈ Subgroup.normalizer (Z0 : Set G) := hg.2
  have hs' : g * s * g⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hgN s).mp hsZ0
  have hs'Q : g * s * g⁻¹ ∉ Q := by
    intro h
    apply hsQ
    have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hgM)) _).mp h
    simpa [mul_assoc] using h2
  obtain ⟨hR1, hV1⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ
  obtain ⟨hR2, hV2⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 (g * s * g⁻¹) hs' hs'Q
  refine ⟨?_, ?_⟩
  · calc conjSubgroup g (Rt M (LB M Q B) t) = conjSubgroup g (Rt M (LB M Q B) s) := by rw [hR1]
      _ = Rt M (LB M Q B) (g * s * g⁻¹) := conjSubgroup_Rt_eq hgM s
      _ = Rt M (LB M Q B) t := hR2
  · calc conjSubgroup g (Vt M (LB M Q B) B Z t) = conjSubgroup g (Vt M (LB M Q B) B Z s) := by
          rw [hV1]
      _ = Vt M (LB M Q B) B Z (g * s * g⁻¹) :=
          conjSubgroup_Vt_eq hgM (hc.conj_Z_eq hgM) s
      _ = Vt M (LB M Q B) B Z t := hV2

theorem sec7_conj_CN_eq (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : G} (hg : g ∈ NormH0 M Z Z0) :
    conjSubgroup g (hc.CN t) = hc.CN t := by
  obtain ⟨hR, hV⟩ := sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hg
  exact conjSubgroup_CN_eq hc hg.1.1 hR hV

end CFSG.RankThree.GF2n.Stroth80
