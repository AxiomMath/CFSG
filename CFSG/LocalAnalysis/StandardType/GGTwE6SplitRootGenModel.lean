module

public import CFSG.LocalAnalysis.StandardType.GGTorusModelTwoBase
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenDist
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenReal
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private noncomputable def twE6SplitWbarPerm (p : ℕ) [NeZero p] :
    (Fin Tag.F4.rank → ZMod p) ≃ (Fin Tag.F4.rank → ZMod p) :=
  { toFun := TableBExc.torusAct .F4 p twE6SplitWbar
    invFun := TableBExc.torusAct .F4 p twE6SplitWbar⁻¹
    left_inv := fun t => by
      rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
    right_inv := fun t => by
      rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one] }

private lemma torusAct_twE6SplitWbarPerm_conj (p : ℕ) [NeZero p] (b : Fin Tag.F4.rank)
    (t : Fin Tag.F4.rank → ZMod p) :
    twE6SplitWbarPerm p (TableBExc.torusAct .F4 p (simple Tag.F4 b)
      ((twE6SplitWbarPerm p).symm t)) =
    TableBExc.torusAct .F4 p
      (twE6SplitWbar * simple Tag.F4 b * twE6SplitWbar⁻¹) t := by
  show TableBExc.torusAct .F4 p twE6SplitWbar
      (TableBExc.torusAct .F4 p (simple Tag.F4 b)
        (TableBExc.torusAct .F4 p twE6SplitWbar⁻¹ t)) = _
  rw [← TableBExc.torusAct_mul, ← TableBExc.torusAct_mul]

private lemma torusAct_simple_mul_twE6SplitWbar (p : ℕ) [NeZero p]
    (t : Fin Tag.F4.rank → ZMod p) :
    TableBExc.torusAct .F4 p (simple Tag.F4 ⟨1, by decide⟩)
        (TableBExc.torusAct .F4 p (simple Tag.F4 ⟨2, by decide⟩) t) =
      TableBExc.torusAct .F4 p twE6SplitWbar t := by
  rw [twE6SplitWbar, ← TableBExc.torusAct_mul]

theorem ggTorusModelAt_range_twE6SplitFrameHom
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    GGTorusModelAt p (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  choose w hwmem hwconj using fun a =>
    exists_mem_orbitRankOneGroup_conj_twE6SplitFrameHom σ hζ hζσ a
  let T := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
  let S : Fin Tag.F4.rank → Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    fun a => (orbitRankOneGroup TwistTag.E6 K σ a).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)
  let u := twE6SplitWbarPerm p
  have hn : ∀ t, (w ⟨1, by decide⟩ * w ⟨2, by decide⟩) * T (Multiplicative.ofAdd t) *
      (w ⟨1, by decide⟩ * w ⟨2, by decide⟩)⁻¹ = T (Multiplicative.ofAdd (u t)) := by
    intro t
    have h2 := hwconj ⟨2, by decide⟩ t
    have h1 := hwconj ⟨1, by decide⟩
      (TableBExc.torusAct .F4 p (simple Tag.F4 ⟨2, by decide⟩) t)
    calc
      (w ⟨1, by decide⟩ * w ⟨2, by decide⟩) * T (Multiplicative.ofAdd t) *
          (w ⟨1, by decide⟩ * w ⟨2, by decide⟩)⁻¹
          = w ⟨1, by decide⟩ * (w ⟨2, by decide⟩ * T (Multiplicative.ofAdd t) *
              (w ⟨2, by decide⟩)⁻¹) * (w ⟨1, by decide⟩)⁻¹ := by group
      _ = w ⟨1, by decide⟩ *
            T (Multiplicative.ofAdd (TableBExc.torusAct .F4 p
              (simple Tag.F4 ⟨2, by decide⟩) t)) *
            (w ⟨1, by decide⟩)⁻¹ := by rw [h2]
      _ = T (Multiplicative.ofAdd (TableBExc.torusAct .F4 p
            (simple Tag.F4 ⟨1, by decide⟩)
            (TableBExc.torusAct .F4 p (simple Tag.F4 ⟨2, by decide⟩) t))) := h1
      _ = T (Multiplicative.ofAdd (u t)) :=
        congrArg (fun s => T (Multiplicative.ofAdd s))
          (torusAct_simple_mul_twE6SplitWbar p t)
  have hf : Function.Injective
      (fun a : Fin Tag.F4.rank => TableBExc.torusAct .F4 p (simple Tag.F4 a)) := by
    intro a b hab
    by_contra hne
    exact torusAct_simple_ne_F4 hp2 hne hab
  have hfu : ∀ i j, (fun a : Fin Tag.F4.rank =>
        TableBExc.torusAct .F4 p (simple Tag.F4 a)) i ≠
      fun t => u ((fun a : Fin Tag.F4.rank =>
        TableBExc.torusAct .F4 p (simple Tag.F4 a)) j (u.symm t)) := by
    intro i j h
    exact torusAct_simple_ne_conj_F4 hp2 i j
      (funext fun t => (congrFun h t).trans (torusAct_twE6SplitWbarPerm_conj p j t))
  refine ggTorusModelAt_of_twoBase (p := p) (k := Tag.F4.rank)
    (G := ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (E := (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range) T ?_ rfl w
    (fun a => TableBExc.torusAct .F4 p (simple Tag.F4 a)) S ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (w ⟨1, by decide⟩ * w ⟨2, by decide⟩) u hn hf hfu
  · exact twE6SplitFrameHom_injective_of_orderOf σ hζo hζ hζσ
  · exact fun i t => hwconj i t
  · exact fun i t => torusAct_simple_involutive .F4 i t
  · exact fun i => card_fix_torusAct_simple .F4 hp2 i
  · exact fun i => (Subgroup.mem_subgroupOf).mpr (hwmem i)
  · exact fun i => isComponentOf_orbitRankOneGroup_twE6Split σ hp2 hζo hζ hζσ i
  · exact fun i => dvd_card_orbitRankOneGroup_subgroupOf_twE6Split σ hζo hζσ i
  · exact iSup_orbitRankOneGroup_subgroupOf_twE6 σ

end CFSG.StandardType.TwE6SplitRootGen

end
