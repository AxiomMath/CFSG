module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdxC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalShapeL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T N : Subgroup (MulAut W)}

theorem ThreeNat.exists_mul_kBar_of_card_eq_168 (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hc : Nat.card ↥L = 168)
    {a : MulAut W} (ha : a ∈ A) :
    ∃ l ∈ L, ∃ k ∈ s1t3KBar A L, a = l * k := by
  obtain ⟨J₀, g, hJ₀, hker, hg⟩ := s16t3_exists_section_hom h h7
  have hnat : BinaryNaturalSL L J₀ (J₀ ⊓ fixV L) 3 1 :=
    s16t3_sumOfNat_one
      (SumOfNatShape.sl3_of_card_eq_168 h.quasi hc (h.natural_of_mem_irrSet hJ₀))
  have hfull : autSec L J₀ (J₀ ⊓ fixV L) = ⊤ := s16h_binarySL3_autSec_eq_top hnat
  have hLJ : L ≤ stabSub J₀ := le_stabSub_of_forall_mem hJ₀.2.2.1
  have hLZ : L ≤ stabSub (J₀ ⊓ fixV L) := by
    apply le_stabSub_of_forall_mem
    intro l hl u hu
    rw [Subgroup.mem_inf] at hu ⊢
    have hlu : (l : MulAut W) u = u := (mem_fixV.mp hu.2) l hl
    rw [hlu]
    exact hu
  have hgL : g.comp (Subgroup.inclusion h.le) =
      CFSG.Quasithin.B5.secHom L hLJ hLZ := by
    refine MonoidHom.ext fun l => MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [MonoidHom.comp_apply,
        hg (Subgroup.inclusion h.le l) l.2 u ((hLJ l.2 u).2 u.2)]
      exact (CFSG.Quasithin.B5.secHom_mk L hLJ hLZ l u).symm
  have hrange : (CFSG.Quasithin.B5.secHom L hLJ hLZ).range = ⊤ := by
    rw [CFSG.Quasithin.B5.range_secHom L hLJ hLZ, hfull]
  let aA : ↥A := ⟨a, ha⟩
  have hmem : g aA ∈ (CFSG.Quasithin.B5.secHom L hLJ hLZ).range := by
    rw [hrange]
    trivial
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hmem
  let lA : ↥A := Subgroup.inclusion h.le l
  have hgl : g lA = g aA := by
    change (g.comp (Subgroup.inclusion h.le)) l = g aA
    rw [hgL]
    exact hl
  let kA : ↥A := lA⁻¹ * aA
  have hkker : kA ∈ g.ker := by
    rw [MonoidHom.mem_ker]
    change g (lA⁻¹ * aA) = 1
    rw [map_mul, map_inv, hgl, inv_mul_cancel]
  have hkbar : (kA : MulAut W) ∈ s1t3KBar A L := by
    have hsub : kA ∈ (s1t3KBar A L).subgroupOf A := by
      rw [← hker]
      exact hkker
    exact Subgroup.mem_subgroupOf.mp hsub
  refine ⟨(l : MulAut W), l.2, (kA : MulAut W), hkbar, ?_⟩
  have hkval : (kA : MulAut W) = (l : MulAut W)⁻¹ * a := rfl
  rw [hkval]
  group

theorem ThreeNat.sup_kBar_eq_of_isL3 (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hL : IsL3 ↥L 1) :
    L ⊔ s1t3KBar A L = A := by
  have hc : Nat.card ↥L = 168 := card_eq_of_isL3 hL
  apply le_antisymm
  · exact sup_le h.le inf_le_left
  · intro a ha
    obtain ⟨l, hl, k, hk, rfl⟩ := h.exists_mul_kBar_of_card_eq_168 h7 hc ha
    exact Subgroup.mul_mem_sup hl hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
