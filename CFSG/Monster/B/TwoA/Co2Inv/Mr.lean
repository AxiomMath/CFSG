
module

public import CFSG.Monster.B.TwoA.Co2Inv.MrBase

public import CFSG.Monster.B.TwoA.Co2Inv.Rows

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

theorem mk_monomial_mul_rK (a : C) (p : AutPerm) :
    (QuotientGroup.mk (gO a * PO p) : OLq) * alpha 12 =
      QuotientGroup.mk (gO (a + (permC p).symm dC) * PO p) := by
  rw [alpha12_eq, ← QuotientGroup.mk_mul, mul_assoc, PO_mul_gO, ← mul_assoc, ← gO_add]

theorem rK_mul_mk_monomial (a : C) (p : AutPerm) :
    alpha 12 * (QuotientGroup.mk (gO a * PO p) : OLq) =
      QuotientGroup.mk (gO (a + dC) * PO p) := by
  rw [alpha12_eq, ← QuotientGroup.mk_mul, ← mul_assoc, ← gO_add, add_comm]

theorem commute_rK_iff (a : C) (p : AutPerm) :
    (QuotientGroup.mk (gO a * PO p) : OLq) * alpha 12 =
        alpha 12 * QuotientGroup.mk (gO a * PO p) ↔ PresJ (p : Equiv.Perm (Fin 24)) := by
  rw [mk_monomial_mul_rK, rK_mul_mk_monomial, mk_eq_mk_monomial_iff, ← permC_dC_iff]
  constructor
  · rintro (h | h)
    · have h' : (permC p).symm dC = dC := add_left_cancel h.symm
      calc permC p dC = permC p ((permC p).symm dC) := by rw [h']
        _ = dC := LinearEquiv.apply_symm_apply _ _
    · exfalso
      have h1 : dC = (permC p).symm dC + VisQuot.ΩC := by
        rw [add_assoc] at h
        exact add_left_cancel h
      have h2 : (permC p).symm dC = dC + VisQuot.ΩC :=
        calc (permC p).symm dC = (permC p).symm dC + VisQuot.ΩC + VisQuot.ΩC := by
              rw [add_assoc, ZModModule.add_self, add_zero]
          _ = dC + VisQuot.ΩC := by rw [← h1]
      have hw := congrArg (fun x : C => hammingNorm (x : Fin 24 → ZMod 2)) h2
      simp only [hammingNorm_dC_add_Ω] at hw
      rw [permC_symm_apply, coe_permC, hammingNorm_permWord, hammingNorm_dC] at hw
      omega
  · intro h
    left
    have h' : (permC p).symm dC = dC := (LinearEquiv.symm_apply_eq _).2 h.symm
    rw [h']

@[expose] def Mr :
    Subgroup (Kstab v0) := Mfr ⊓ Subgroup.centralizer {rK}

theorem mem_Mr_iff
    (k : Kstab v0) : k ∈ Mr ↔ (k : OLq) ∈ monoSub foctHyp := by
  rw [Mr, Subgroup.mem_inf, mem_Mfr_iff, mem_monoSub_iff, mem_monoSub_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨a, ha, p, hp, e⟩, hc⟩
    refine ⟨a, ha, p, ⟨hp, ?_⟩, e⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    rw [e] at hc'
    exact (commute_rK_iff a p).1 hc'
  · rintro ⟨a, ha, p, hp, e⟩
    refine ⟨⟨a, ha, p, hp.1, e⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul]
    rw [e]
    exact (commute_rK_iff a p).2 hp.2

theorem map_Mr :
    Mr.map (Kstab v0).subtype = monoSub foctHyp := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_Mr_iff k).1 hk
  · intro hx
    have hK : x ∈ Kstab v0 :=
      monoSub_ceq_le_Kstab (monoSub_mono foctHyp ceqHyp le_rfl Foct_le_Ppair hx)
    exact ⟨⟨x, hK⟩, (mem_Mr_iff _).2 hx, rfl⟩

@[expose] def mrEquivMono :
    Mr ≃* monoSub foctHyp :=
  (Mr.equivMapOfInjective (Kstab v0).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_Mr)

@[expose] def MrEquiv :
    SDD foctHyp ≃* Mr := (monoSubEquiv foctHyp).trans mrEquivMono.symm

theorem natCard_Mr :
    Nat.card Mr = 2 ^ 10 * Nat.card Foct := by
  rw [Nat.card_congr mrEquivMono.toEquiv, natCard_monoSub, natCard_quot_ΩIn foctHyp, finrank_Ceq]

end CFSG.Monster.B.TwoA.Co2Inv
