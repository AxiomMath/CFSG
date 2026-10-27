module

public import CFSG.Quasithin.MS93.S38ESecMod
public import CFSG.Quasithin.MS93.S38EFFHyp
public import CFSG.Quasithin.MS93.S38Base

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem ofA_mem_stab_baseA (hTM : T ≤ M) (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ stab (puAmalgam hTM) (baseA _) := by
  rw [puAmalgam.stab_baseA hTM]
  exact ⟨m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩

@[expose] noncomputable def phiM (hTM : T ≤ M) : ↥M →* ↥(stab (puAmalgam hTM) (baseA _)) :=
  ((puAmalgam hTM).ofA).codRestrict _ (ofA_mem_stab_baseA hTM)

omit [Finite G] in
theorem phiM_coe (hTM : T ≤ M) (m : ↥M) :
    ((phiM hTM m : ↥(stab _ _)) : _) = (puAmalgam hTM).ofA m :=
  rfl

omit [Finite G] in
theorem phiM_surjective (hTM : T ≤ M) : Function.Surjective (phiM hTM) := by
  rintro ⟨g, hg⟩
  rw [puAmalgam.stab_baseA hTM] at hg
  obtain ⟨m, -, rfl⟩ := hg
  exact ⟨m, rfl⟩

namespace EndSetup

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {e : ℕ}
  (hS : EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
    (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') e)
  (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
    (c : (puAmalgam h.le).Universal) ∈
      ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
      lam c = 1)

noncomputable abbrev rhoM : ↥M →* MulAut (hS.SM lam hlam1) :=
  (hS.secRho lam hlam1).comp (phiM h.le)

theorem range_rhoM : (hS.rhoM h lam hlam1).range = (hS.secRho lam hlam1).range :=
  hS.range_secRho_comp lam hlam1 (phiM h.le) (phiM_surjective h.le)

theorem map_phiM_L : (L.subgroupOf M).map (phiM h.le) =
    (puTrans h.le L (baseA _)).subgroupOf (stab (puAmalgam h.le) (baseA _)) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, puTrans_baseA h.le h.L_subgroupOf_normal]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, hmg⟩
    exact ⟨m, hm, Subtype.ext hmg⟩

theorem imL_rhoM : IsIrrRep.imL L (hS.rhoM h lam hlam1) = hS.kS lam hlam1 := by
  rw [IsIrrRep.imL, ← Subgroup.map_map, map_phiM_L h]

variable (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
    (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
include hirr

theorem isIrrRep_rhoM : IsIrrRep L (hS.rhoM h lam hlam1) where
  sq := hS.sq_SM lam hlam1
  pCore m hm := by
    have hmQ : ((phiM h.le m : ↥(stab _ _)) : (puAmalgam h.le).Universal) ∈
        Qv (puAmalgam h.le) (baseA _) := by
      rw [phiM_coe, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    exact hS.secRho_comp_eq_one lam hlam1 hirr (phiM h.le) hS.qa_le hS.nQa hS.qa2 hmQ
  irr := hS.irr_secRho_comp lam hlam1 hirr (phiM h.le) (phiM_surjective h.le)
  ne := by
    obtain ⟨x, hxL, hx1⟩ :=
      hS.exists_secRho_comp_ne_one lam hlam1 hirr (phiM h.le) (phiM_surjective h.le)
    refine ⟨x, ?_, hx1⟩
    rw [phiM_coe, puTrans_baseA h.le h.L_subgroupOf_normal] at hxL
    obtain ⟨y, hy, hyx⟩ := hxL
    rw [← (puAmalgam h.le).ofA_injective hyx]
    exact Subgroup.mem_subgroupOf.mp hy

theorem isFFModule_rhoM (he2 : 2 ≤ e) : IsFFModule (hS.rhoM h lam hlam1).range := by
  rw [range_rhoM]
  refine ⟨hS.eS lam hlam1, Subgroup.map_le_range _ _, hS.eS_ne_bot lam hlam1 hirr he2,
    hS.isElemAbelian2_eS lam hlam1, ?_⟩
  exact hS.card_le_card_eS_mul lam hlam1 hirr

theorem ffHyp_rhoM (he2 : 2 ≤ e) (hSQ : SQTKQuot) :
    FFHyp (hS.rhoM h lam hlam1).range (IsIrrRep.imL L (hS.rhoM h lam hlam1)) := by
  exact (hS.isIrrRep_rhoM h lam hlam1 hirr).ffHyp h hSQ (hS.isFFModule_rhoM h lam hlam1 hirr he2)

end EndSetup

end CFSG.Quasithin.MS93.S38E
