module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
public import CFSG.LieType.SeitzGeneration.ExtSeitzBridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem planeGen_outer_A3_three {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) (hv : (TauCeti.LieTypeIndex.A 3 q).Valid)
    {E : Subgroup (MulAut (Cat ⟨.A 3 q, hv⟩))} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2)
    (hout : ¬ InnerPlane ⟨.A 3 q, hv⟩ 3 E) : PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let e : Cat ⟨.A 3 q, hv⟩ ≃* projectiveSL 4 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (3 + 1) _)
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcop : Nat.Coprime 3 (Nat.gcd 4 (Nat.card (GaloisField q.p q.exponent) - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 4 _) (by norm_num)
  have hpℓ : 3 ≠ q.p := by rw [hq2]; norm_num
  have hd := CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.fieldAutData_projectiveSL_of_cop
    (n := 4) (by norm_num) Nat.prime_three (by norm_num) q.prime_p hpℓ q.exponent_pos hKq hcop
  have hsimple : IsSimpleGroup (projectiveSL 4 (GaloisField q.p q.exponent)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  have hnab : ∃ a b : projectiveSL 4 (GaloisField q.p q.exponent), a * b ≠ b * a :=
    exists_noncommuting_of_isElementaryAbelian_aut hEi hc'
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab Nat.prime_three hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem seitzA3NoninnerTwo :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ (∃ q : TauCeti.PrimePower, d.1 = .A 3 q) ∧
      d.1.characteristic = 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, rfl, ⟨q, hd⟩, hch⟩
  subst hd
  have hq2 : q.p = 2 := by
    simpa [TauCeti.LieTypeIndex.characteristic_A] using hch
  exact planeGen_outer_A3_three hq2 hv hE hc hout

end CFSG.RankThree.PartTwo.Sec19
