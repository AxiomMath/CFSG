
module

public import CFSG.Sporadic.HNOddCore.Stab
public import CFSG.Sporadic.HNOddCore.CCheckBase
public import CFSG.Sporadic.HNSchreier.ThreeSpec
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.F5.Native Equiv

@[irreducible] def dTab : Array ℕ :=
  pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) LocalData.innerWord

theorem dTab_eq :
    dTab = pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) LocalData.innerWord := by
  unfold dTab; rfl

@[irreducible] def uTab : Array ℕ :=
  seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)
    LocalData.outerWord

theorem uTab_eq : uTab = seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) LocalData.outerWord := by
  unfold uTab; rfl

@[irreducible] def kTab : Array ℕ := pcomp hnsData.n dTab (pinvCand hnsData.n uTab)

theorem kTab_eq : kTab = pcomp hnsData.n dTab (pinvCand hnsData.n uTab) := by unfold kTab; rfl

@[irreducible] def wTab : Array ℕ :=
  ppow hnsData.n (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha)
    (pcomp hnsData.n (natTab (hnsData.orbit ()).beta) (natTab (hnsData.orbit ()).beta))) 8

theorem wTab_eq : wTab = ppow hnsData.n (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha)
    (pcomp hnsData.n (natTab (hnsData.orbit ()).beta) (natTab (hnsData.orbit ()).beta))) 8 := by
  unfold wTab; rfl

@[irreducible] def cABTab : Array ℕ × Array ℕ :=
  conjTabs hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) kTab
    (pinvCand hnsData.n kTab) wTab (pinvCand hnsData.n wTab)

theorem cABTab_eq : cABTab = conjTabs hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) kTab (pinvCand hnsData.n kTab) wTab
      (pinvCand hnsData.n wTab) := by
  unfold cABTab; rfl

@[irreducible] def parTab : Array ℕ :=
  bfsPar hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)

theorem parTab_eq :
    parTab = bfsPar hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) :=
  by unfold parTab; rfl

@[irreducible] def cRec : Array ℕ := cRecArr hnsData.n parTab cABTab.1 cABTab.2

theorem cRec_eq : cRec = cRecArr hnsData.n parTab cABTab.1 cABTab.2 := by unfold cRec; rfl

theorem prep_aTab :
    PRep hnsData.n (natTab (hnsData.orbit ()).alpha) (permJ aJ) := prep_a0

theorem prep_bTab :
    PRep hnsData.n (natTab (hnsData.orbit ()).beta) (permJ bJ) := prep_a1

theorem prep_uTab :
    PRep hnsData.n uTab (permJ (seedWordJ LocalData.outerWord)) := by
  rw [uTab_eq]
  exact prep_seedWordArr _ local_parts_data.2.1

theorem prep_wTab : PRep hnsData.n wTab (permJ wJ) := by
  rw [wTab_eq, map_pow, map_mul, map_pow, pow_two]
  exact prep_ppow (prep_pcomp prep_aTab (prep_pcomp prep_bTab prep_bTab)) 8

theorem conj_aux {G : Type*} [Group G] (d s a : G) :
    d * s * a * (s⁻¹ * d⁻¹) = d * (s * a * s⁻¹) * d⁻¹ := by group

theorem conjC_aJ :
    conjC aJ = dJ * aJ * dJ⁻¹ := by
  apply Subtype.ext
  rw [conjC_val, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, cU_eq, _root_.mul_inv_rev,
    conj_aux, sU_conj_aJ]

theorem conjC_bJ :
    conjC bJ = dJ * (wJ⁻¹ * bJ * wJ) * dJ⁻¹ := by
  apply Subtype.ext
  rw [conjC_val, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, cU_eq, _root_.mul_inv_rev, conj_aux, sU_conj_bJ]

theorem cATab_eq : cABTab.1 = pcomp hnsData.n kTab
    (pcomp hnsData.n (natTab (hnsData.orbit ()).alpha) (pinvCand hnsData.n kTab)) := by
  rw [cABTab_eq]
  simp only [conjTabs]

theorem cBTab_eq : cABTab.2 = pcomp hnsData.n kTab (pcomp hnsData.n (pinvCand hnsData.n wTab)
    (pcomp hnsData.n (natTab (hnsData.orbit ()).beta)
      (pcomp hnsData.n wTab (pinvCand hnsData.n kTab)))) := by
  rw [cABTab_eq]
  simp only [conjTabs]

theorem cR_smul_conj
    (g : JH) (y : X) : cR • (g • y) = conjC g • (cR • y) := by
  rw [← jR_smul, ← mul_smul, cR_mul_jR, mul_smul, jR_smul]

end CFSG.Sporadic.HNOddCore
