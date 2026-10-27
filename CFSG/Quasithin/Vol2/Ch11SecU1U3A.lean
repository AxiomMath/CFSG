module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Cen

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Quasithin.A312U3 (uniData su3OddIrr_holds)

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem zcU_eq (hF : Nat.card F = p ^ 2) :
    zcU hF = unitaryPSUEquiv (uniData hF) (n := 3) (by norm_num)
      (unitaryProj (uniData hF) 3 (unitaryInvT (uniData hF))) := by
  rw [unitaryPSUEquiv_unitaryProj]
  rfl

theorem orderOf_zcU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : orderOf (zcU hF) = 2 := by
  rw [zcU_eq hF, MulEquiv.orderOf_eq]
  exact orderOf_unitaryProj_unitaryInvT (uniData hF) hp2

theorem isConj_zcU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {x : PSU3F p F}
    (hx : orderOf x = 2) : IsConj x (zcU hF) := by
  set e := unitaryPSUEquiv (uniData hF) (n := 3) (by norm_num) with he
  have h1 := isConj_unitaryProj_unitaryInvT (uniData hF) hp2 (s := e.symm x)
    (by rw [MulEquiv.orderOf_eq]; exact hx)
  have h2 := MonoidHom.map_isConj e.toMonoidHom h1
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
  rw [zcU_eq hF]
  exact h2

variable [Finite F]

theorem centralizer_zcU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    Subgroup.centralizer ({zcU hF} : Set (PSU3F p F)) = leviCU hF := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact mem_leviCU_of_commute_z hp2 hF h
  · intro h
    exact (zcU_comm_leviCU hF h).symm


theorem isCoatom_leviCU (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hF : Nat.card F = p ^ 2) :
    IsCoatom (leviCU hF) := by
  refine ⟨leviCU_ne_top hp2 hF, fun Y hY => ?_⟩
  by_contra hne
  exact (not_le_of_gt hY) (le_leviCU_of_ne_top su3OddIrr_holds hp2 hF
    (fun h => absurd h hp3) hY.le hne)

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
