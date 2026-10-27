module

public import CFSG.LocalAnalysis.StandardType.GGPumpupConj
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourTwins
import CFSG.LocalAnalysis.StandardType.GGRankOneShared
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProper
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem exists_oppPumpup_of_plane {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hPU : GGPumpupInput) (hc : GGConfig p B Bs x L D J)
    (hB : B = Bs) {A : Subgroup (MulAut ↥Bs)} {e : CoxeterMatrix.F₄.Group ≃* ↥A}
    (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e) (w : CoxeterMatrix.F₄.Group)
    {r u r' : MulAut ↥Bs}
    (hr : r = ((e (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hu : u = ((e (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hr' : r' = ((e (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) : ↥A) : MulAut ↥Bs))
    (hrL : r ∈ ggAutomizer L Bs) (huL : u ∈ ggAutomizer L Bs) {xB d : ↥Bs} (hxB : (xB : G) = x)
    (hrx : r xB = xB) (hux : u xB = xB) (hrd : r d = d) (hud : u d = d) (hr'd : r' d = d)
    (hpl : ∀ z : ↥Bs, r z = z → u z = z → ∃ i j : ℕ, z = xB ^ i * d ^ j)
    (hr'x : r (r' xB) ≠ r' xB) (hmv : ∃ φ ∈ ggAutomizer L Bs, φ d ≠ d) {n : G}
    (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) (hn : ∀ b : ↥Bs, ((r' b : ↥Bs) : G) = n * b * n⁻¹)
    (hnc : n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G)) {J' : Subgroup G}
    (hJlay : LargeEvenLayer (L ⊓ Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)) = J')
    (hJcomp : CFSG.Assembly.IsComponentOf J' (L ⊓ Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs u : Subgroup G) : Set G)))
    (hJcent : Bs ⊓ Subgroup.centralizer (J' : Set G) = ggHyperplane Bs r ⊓ ggHyperplane Bs u)
    (hSrJ : ggRankOneIn L Bs r ≤ J') (hSuJ : ggRankOneIn L Bs u ≤ J')
    (hpJ : p ∣ Nat.card J') (hsmall : ¬ LargeEvenSmall J')
    (hPq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs u))
    (hPcard : p ∣ Nat.card (ggRankOneIn L Bs u)) :
    ggHyperplane Bs r ⊓ ggHyperplane Bs u = Subgroup.closure {x, (d : G)} ∧
      LargeEvenStdSub p B x L (ggHyperplane Bs r ⊓ ggHyperplane Bs u) J' ∧
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
  obtain ⟨hpp, hEl, hxBs, hLx, -⟩ := hc.tableB_facts
  have : Fact p.Prime := ⟨hpp⟩
  have hx1 : x ≠ 1 := hI.2.2.2.2.2.2.1.2.2.1
  have hr2 : r ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 2, hr⟩).1
  have hu2 : u ^ 2 = 1 := (ggCoxRefl_isReflection hpres.2 ⟨w, 1, hu⟩).1
  have hxL : ∀ φ ∈ ggAutomizer L Bs, φ xB = xB := by
    intro φ hφ
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hg xB, hxB]
    have hgx : g * x = x * g := (Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL))
    rw [hgx]
    group
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'def
  have hD'Bs : D' ≤ Bs := inf_le_left.trans (Subgroup.map_subtype_le _)
  have hdD : (d : G) ∈ D' := ⟨⟨d, hrd, rfl⟩, ⟨d, hud, rfl⟩⟩
  have hxD : x ∈ D' := ⟨⟨xB, hrx, hxB⟩, ⟨xB, hux, hxB⟩⟩
  have hD' : D' = Subgroup.closure {x, (d : G)} := by
    apply le_antisymm
    · rintro z ⟨⟨z₁, hz₁, rfl⟩, ⟨z₂, hz₂, hz₁₂⟩⟩
      have h12 : z₂ = z₁ := Subtype.ext hz₁₂
      subst h12
      obtain ⟨i, j, hij⟩ := hpl z₂ hz₁ hz₂
      have hz : ((z₂ : ↥Bs) : G) = x ^ i * (d : G) ^ j := by
        rw [hij, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hxB]
      rw [show Bs.subtype z₂ = ((z₂ : ↥Bs) : G) from rfl, hz]
      exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) i)
        (pow_mem (Subgroup.subset_closure (by simp)) j)
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact hxD
      · exact hdD
  have hdx : (d : G) ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    obtain ⟨φ, hφ, hφd⟩ := hmv
    apply hφd
    have hdk : d = xB ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hxB, hk])
    rw [hdk, map_zpow, hxL φ hφ]
  have hcardD : Nat.card D' = p ^ 2 := by
    rw [hD', Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
    exact card_zpowers_sup_zpowers hpp hEl hxBs d.2 hx1 hdx
  have hStd : LargeEvenStdSub p B x L D' J' := by
    refine ⟨⟨?_, ?_, hcardD, hxD, hJlay.symm, hJcomp, ?_⟩, fun _ => hsmall⟩
    · rw [hB]
      exact hD'Bs
    · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => hEl.2 z (hD'Bs hz)⟩
      have hab := hEl.1.is_comm.comm (⟨a, hD'Bs a.2⟩ : ↥Bs) ⟨b, hD'Bs b.2⟩
      exact (congrArg (Subtype.val : ↥Bs → G) hab :)
    · rw [hB, hJcent]
  have hperf : ggRankOneIn L Bs u ≤ ⁅ggRankOneIn L Bs u, ggRankOneIn L Bs u⁆ := by
    rw [← Subgroup.map_subtype_commutator, hPq.1, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ggRankOneIn L Bs u)) p hPcard
  have hgp : ((g : G)) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    exact hpp.one_lt.ne hg
  have hPn : ggRankOneIn L Bs u ≤ J'.map (MulAut.conj n).toMonoidHom := by
    intro z hz
    refine ⟨z, hSuJ hz, ?_⟩
    have hzn : z * n = n * z := Subgroup.mem_centralizer_iff.mp hnc z hz
    change n * z * n⁻¹ = z
    rw [← hzn]
    group
  have hnd : n * (d : G) * n⁻¹ = d := by
    rw [← hn d, hr'd]
  have hxnB : n * x * n⁻¹ ∈ B := by
    rw [← hxB, ← hn xB, hB]
    exact (r' xB).2
  have hxnD : n * x * n⁻¹ ∉ D' := by
    rintro ⟨⟨z, hz, hzx⟩, -⟩
    apply hr'x
    have hzr : z = r' xB := Subtype.ext (by rw [show ((z : ↥Bs) : G) = Bs.subtype z from rfl, hzx,
      ← hxB, ← hn xB])
    rw [← hzr]
    exact hz
  obtain ⟨hNbr, hAn, hJA, hpc⟩ := ggNbr_of_pumpup_conj hPU hI hStd hpJ hD' hnd hxnB hxnD hSuJ hPn
    hperf g.2 hg1 hgp
  set A' := ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' with hA'
  have hrA : r ∈ ggAutomizer A' Bs :=
    ggAutomizer_mono Bs (hSrJ.trans hJA) (mem_ggAutomizer_ggRankOneIn hrL hr2)
  have huA : u ∈ ggAutomizer A' Bs :=
    ggAutomizer_mono Bs (hSuJ.trans hJA) (mem_ggAutomizer_ggRankOneIn huL hu2)
  obtain ⟨m, hmS, hmN, hm⟩ := mem_ggAutomizer_iff.mp (mem_ggAutomizer_ggRankOneIn hrL hr2)
  have hconj : r' * r * r'⁻¹ ∈ ggAutomizer A' Bs := by
    rw [mem_ggAutomizer_iff]
    refine ⟨n * m * n⁻¹, ?_, mul_mem (mul_mem hnN hmN) (inv_mem hnN), fun b => ?_⟩
    · rw [← hAn]
      exact ⟨m, hJA (hSrJ hmS), rfl⟩
    · have h1 : ((r'⁻¹ b : ↥Bs) : G) = n⁻¹ * b * n := by
        have := hn (r'⁻¹ b)
        rw [MulAut.apply_inv_self] at this
        rw [this]
        group
      rw [MulAut.mul_apply, MulAut.mul_apply, hn, hm, h1]
      group
  have hW : w * CoxeterMatrix.F₄.simple 3 * w⁻¹ = w * CoxeterMatrix.F₄.simple 2 * w⁻¹ *
      (w * CoxeterMatrix.F₄.simple 3 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) *
        (w * CoxeterMatrix.F₄.simple 3 * w⁻¹)⁻¹) * (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) := by
    have h23 := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow 2 3
    have h33 := CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_self 3
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h23 h33
    have hM : CoxeterMatrix.F₄.M 2 3 = 3 := rfl
    rw [hM, pow_three] at h23
    have hinv : (CoxeterMatrix.F₄.simple 3)⁻¹ = CoxeterMatrix.F₄.simple 3 :=
      inv_eq_of_mul_eq_one_right h33
    have key : CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 *
        CoxeterMatrix.F₄.simple 2 * (CoxeterMatrix.F₄.simple 3)⁻¹ * CoxeterMatrix.F₄.simple 2 =
        CoxeterMatrix.F₄.simple 3 := by
      rw [hinv]
      calc CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2 *
            CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2
          = CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 *
              (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 *
                (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3)) *
              (CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 3)⁻¹ *
              CoxeterMatrix.F₄.simple 3 := by group
        _ = CoxeterMatrix.F₄.simple 3 := by rw [h23, h33]; group
    rw [show w * CoxeterMatrix.F₄.simple 2 * w⁻¹ *
        (w * CoxeterMatrix.F₄.simple 3 * w⁻¹ * (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) *
          (w * CoxeterMatrix.F₄.simple 3 * w⁻¹)⁻¹) * (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) =
        w * (CoxeterMatrix.F₄.simple 2 * CoxeterMatrix.F₄.simple 3 * CoxeterMatrix.F₄.simple 2 *
          (CoxeterMatrix.F₄.simple 3)⁻¹ * CoxeterMatrix.F₄.simple 2) * w⁻¹ by group, key]
  have hr'eq : r' = r * (r' * r * r'⁻¹) * r := by
    let ι : CoxeterMatrix.F₄.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
    have hι : ∀ v, ι v = ((e v : ↥A) : MulAut ↥Bs) := fun v => rfl
    rw [hr, hr', ← hι, ← hι, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← hW]
  refine ⟨hD', hStd, hNbr, hAn, hJA, hpc, hrA, huA, ?_⟩
  rw [hr'eq]
  exact mul_mem (mul_mem hrA hconj) hrA

end CFSG.StandardType

end
