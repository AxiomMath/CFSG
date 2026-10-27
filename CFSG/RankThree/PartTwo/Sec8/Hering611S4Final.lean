module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Norm
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Transport
public import Certificates.Certificate799350
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Pair

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

theorem j3TwoLocalInput_of_reg
    {Rg : ℕ → Gp} (hR : Reg Rg) : J3TwoLocalInput := by
  intro J _ _ ⟨e⟩ kb ab hk3 ha3 hcomm ⟨Pb, hPerf, hPbC, hab, h360⟩
  set φ : J ≃* ↥j3P := e.trans j3PermEquiv with hφ
  refine J3TwoLocalFacts.of_mulEquiv φ ?_
  set kb' : ↥j3P := φ kb with hkb'
  set ab' : ↥j3P := φ ab with hab'
  have hk3' : orderOf (kb' : Gp) = 3 := by
    rw [Subgroup.orderOf_coe, hkb', MulEquiv.orderOf_eq]; exact hk3
  have ha3' : orderOf (ab' : Gp) = 3 := by
    rw [Subgroup.orderOf_coe, hab', MulEquiv.orderOf_eq]; exact ha3
  set f : J →* Gp := j3P.subtype.comp φ.toMonoidHom with hf
  have hfinj : Function.Injective f := j3P.subtype_injective.comp φ.injective
  set Pb' : Subgroup Gp := Pb.map f with hPb'
  haveI : Group.IsPerfect Pb' := Group.IsPerfect.map _
  have hPb'C : Pb' ≤ centralizer {(kb' : Gp)} ⊓ j3P := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_inf.2 ⟨?_, (φ q).2⟩
    have := mem_centralizer_singleton_iff.1 (hPbC hq)
    rw [mem_centralizer_singleton_iff]
    have h2 := congrArg f this
    simpa [hf, hkb', map_mul] using h2
  have hab'' : (ab' : Gp) ∈ Pb' := ⟨ab, hab, rfl⟩
  have h360' : 360 ∣ Nat.card Pb' := by
    rw [hPb', card_map_of_injective hfinj]; exact h360
  obtain ⟨c, hcP, hckb, hcab⟩ := normal_form hR kb'.2 hk3' ha3' Pb' hPb'C hab'' h360'
  set c' : ↥j3P := ⟨c, hcP⟩ with hc'
  refine J3TwoLocalFacts.of_mulEquiv (MulAut.conj c') ?_
  have hab_eq : (MulAut.conj c') ab' = ⟨Rg r_uu, uu_mem hR⟩ :=
    Subtype.ext (by simpa [hc', MulAut.conj_apply] using hcab)
  have hcomm' : Commute (Rg r_x0) (Rg r_uu) := commute_of_prod hR.comm_x0_uu
  rcases hckb with h | h
  · have hkb_eq : (MulAut.conj c') kb' = ⟨Rg r_x0, x0_mem hR⟩ :=
      Subtype.ext (by simpa [hc', MulAut.conj_apply] using h)
    rw [hkb_eq, hab_eq]
    exact pair_facts hR
  · have hkb_eq : (MulAut.conj c') kb' = (⟨Rg r_x0, x0_mem hR⟩ : ↥j3P)⁻¹ :=
      Subtype.ext (by simpa [hc', MulAut.conj_apply] using h)
    rw [hkb_eq, hab_eq]
    refine J3TwoLocalFacts.inv_left ?_ ?_ ?_
    · exact Subtype.ext (by simpa using hcomm'.inv_left.eq)
    · exact Subtype.ext (by simpa using pow_of_ord hR.ord_uu)
    · rw [inv_inv]
      exact pair_facts hR

theorem j3TwoLocalInput :
    J3TwoLocalInput := by
  obtain ⟨Rg, hR⟩ := Certificates.certificate799350
  exact j3TwoLocalInput_of_reg hR

end CFSG.RankThree.PartTwo.Sec8.Hering611
