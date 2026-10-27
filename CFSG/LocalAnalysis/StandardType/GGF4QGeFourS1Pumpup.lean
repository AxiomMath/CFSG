module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourS1Plane
public import CFSG.LocalAnalysis.StandardType.GGPumpupConj
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPumpup
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProper
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LieType.BorelTits.LeviOrder
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

section Pumpup

theorem exists_s1OppPumpup {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hPU : GGPumpupInput) (hc : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    (hLA : ggAutomizer L Bs ≤ A) {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    {ψ : (ggU .PSp 3 f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .PSp 3 f).K)
    (hrange : ψ.range = L) (hpos : GGTableBPos p Bs L .PSp 3 f ψ)
    (htor : ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .PSp 3 f).D, ∀ z, b * ψ z * b⁻¹ = ψ (t * z * t⁻¹))
    (w : CoxeterMatrix.F₄.Group) {r u r' : MulAut ↥Bs}
    (hr : r = ((e (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hr' : r' = ((e (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hrL : r ∈ ggAutomizer L Bs) (huL : u ∈ ggAutomizer L Bs) {xB d : ↥Bs} (hxB : (xB : G) = x)
    (hrx : r xB = xB) (hux : u xB = xB) (hrd : r d = d) (hud : u d = d) (hr'd : r' d = d)
    (hpl : ∀ z : ↥Bs, r z = z → u z = z → ∃ i j : ℕ, z = xB ^ i * d ^ j)
    (hr'x : r (r' xB) ≠ r' xB) (hmv : ∃ φ ∈ ggAutomizer L Bs, φ d ≠ d) {n : G}
    (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) (hn : ∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹)
    (hnc : n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G)) :
    ∃ J' : Subgroup G,
      ggHyperplane Bs r ⊓ ggHyperplane Bs u = Subgroup.closure {x, (d : G)} ∧
      LargeEvenStdSub p B x L (ggHyperplane Bs r ⊓ ggHyperplane Bs u) J' ∧
      Nonempty (↥J' ≃* StatedSp 2 (GaloisField 2 f)) ∧
      GGNbr p B x (ggHyperplane Bs r ⊓ ggHyperplane Bs u) J' d
        (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J') ∧
      (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J').map
          (MulAut.conj n).toMonoidHom =
        ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' ∧
      J' ≤ ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' ∧
      LargeEvenPComponent p (Subgroup.centralizer ({(d : G)} : Set G))
        (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J') ∧
      r ∈ ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J') Bs ∧
      u ∈ ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J') Bs ∧
      r' ∈ ggAutomizer (ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J') Bs := by
  have hI : GGThmIHyp p B x L := hc.1
  obtain ⟨hpp, hEl, -, -, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hf0 : f ≠ 0 := by omega
  have huR : GGIsReflection p u := ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩
  have hdD : (d : G) ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs u := ⟨⟨d, hrd, rfl⟩, ⟨d, hud, rfl⟩⟩
  have hDX : ¬ ggHyperplane Bs r ⊓ ggHyperplane Bs u ≤ Subgroup.centralizer (L : Set G) := by
    intro hle
    obtain ⟨φ, hφ, hφd⟩ := hmv
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply hφd
    apply Subtype.ext
    rw [hg d]
    have hgd : g * d = d * g := Subgroup.mem_centralizer_iff.mp (hle hdD) g hgL
    rw [hgd]
    group
  obtain ⟨J', hJlay, hJcomp, hJcent, hSrJ, hSuJ, ⟨hJiso⟩⟩ :=
    exists_sp4Plane_of_tableBPos_PSp hpp hp2 hEl hNT hAind hpres hLA hf hker hrange hpos htor w
      hr hu hrL huL hDX
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hJcard : Nat.card J' = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
    rw [Nat.card_congr hJiso.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hq]
  have hq1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 2 - 1 := by
    exact Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2
  have hpJ : p ∣ Nat.card J' := by
    rw [hJcard]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (hpf.trans hq1) _) _
  have hsmall : ¬ LargeEvenSmall J' := by
    refine not_largeEvenSmall_of_map_big (MonoidHom.id G) J' (Or.inr ?_)
    rw [Subgroup.map_id, hJcard]
    have h1 : 256 ≤ (2 ^ f) ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ (2 ^ f) ^ 4 := Nat.pow_le_pow_left hq4 4
    have h2 : 15 ≤ (2 ^ f) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ f) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have h3 : 255 ≤ (2 ^ f) ^ 4 - 1 := by omega
    calc 25920 < 256 * (15 * 255) := by norm_num
      _ ≤ (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have hLpos : GGTableBPosImage p Bs .PSp 3 f L := ⟨ψ, hker, hrange, hpos⟩
  have hPq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs u) :=
    isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT hf hLpos huL huR
  obtain ⟨F, _, _, θ, -, hθinj, hθ, hFcard⟩ :=
    exists_sl2_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT (by omega) hLpos huL huR
  have hPcard : p ∣ Nat.card (ggRankOneIn L Bs u) := by
    rw [← hθ, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv,
      CFSG.LieType.BorelTits.card_specialLinearGroup_fin_two hFcard]
    exact Dvd.dvd.mul_left (hpf.trans hq1) _
  obtain ⟨hD', hStd, hNbr, hAn, hJA, hpc, hrA, huA, hr'A⟩ :=
    exists_oppPumpup_of_plane hPU hc hB hpres w hr hu hr' hrL huL hxB hrx hux hrd hud hr'd hpl
      hr'x hmv hnN hn hnc hJlay hJcomp hJcent hSrJ hSuJ hpJ hsmall hPq hPcard
  exact ⟨J', hD', hStd, ⟨hJiso⟩, hNbr, hAn, hJA, hpc, hrA, huA, hr'A⟩

end Pumpup

end CFSG.StandardType

end
