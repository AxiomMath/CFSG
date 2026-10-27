module

public import CFSG.RankThree.Lattice.SteinbergBIGenCells
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularCentralizer
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section
namespace CFSG.RankThree.Lattice.GenFixedRootDatum
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise


theorem mem_orbitGroupC_of_charElem
    {τ : Tag} {r : ℕ} [Fact r.Prime] {L : Type} [Field L] [CharP L r] [IsAlgClosed L]
    {M : Type} [CommGroup M] (D : GenFixedRootDatum τ r L M)
    {g : adjointGroup τ L} (hg : g ∈ D.fixedGroup) {n : ℕ} (hn : g ^ r ^ n = 1) :
    g ∈ D.orbitGroupC := by
  have hdec : g ∈ (D.fixedTorus : Set (adjointGroup τ L)) *
      (D.orbitGroupC : Set (adjointGroup τ L)) := by
    rwa [← D.coe_fixedGroup_eq_mul]
  obtain ⟨t, ht, x, hx, htx⟩ := hdec
  have htx' : t * x = g := htx
  have htN : t ∈ Subgroup.normalizer (D.orbitGroupC : Set (adjointGroup τ L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => D.conj_mem_orbitGroupC_of_mem_fixedTorus ht hy, fun hy => ?_⟩
    have h := D.conj_mem_orbitGroupC_of_mem_fixedTorus (inv_mem ht) hy
    have heq : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [heq] at h
  haveI : Finite D.fixedGroup := D.finite_fixedGroup
  have htFix : t ∈ D.fixedGroup := D.fixedTorus_le_fixedGroup ht
  have horder : orderOf (t : ModGL τ L) ≠ 0 := by
    rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk t htFix]
    exact (isOfFinOrder_of_finite (⟨t, htFix⟩ : D.fixedGroup)).orderOf_pos.ne'
  have htT : (t : ModGL τ L) ∈ torusGroup τ L :=
    unionTorus_le_torusGroup (D.mem_fixedTorus.1 ht).1
  have hN : Nat.Coprime (orderOf (t : ModGL τ L)) r := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).2 ?_)
    intro hdvd
    have hs := orderOf_pow_orderOf_div horder hdvd
    have hsT := Subgroup.pow_mem (torusGroup τ L) htT (orderOf (t : ModGL τ L) / r)
    have hs1 : ((t : ModGL τ L) ^ (orderOf (t : ModGL τ L) / r)) ^ (r ^ 1) = 1 := by
      simpa only [pow_one, hs] using pow_orderOf_eq_one ((t : ModGL τ L) ^ (orderOf (t : ModGL τ L) / r))
    rw [eq_one_of_torus_pow_eq_one hsT hs1, orderOf_one] at hs
    exact (Fact.out : r.Prime).one_lt.ne hs
  have htN1 : t ^ orderOf (t : ModGL τ L) = 1 := Subtype.ext (pow_orderOf_eq_one _)
  have hgn : (t * x) ^ r ^ n = 1 := by rw [htx']; exact hn
  have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.mem_of_charElem_of_mul
    htN htN1 hN hx hgn
  rwa [htx'] at h

end CFSG.RankThree.Lattice.GenFixedRootDatum
