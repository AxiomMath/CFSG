
module

public import CFSG.Monster.B.TwoA.Amalgam.CoFiberBase
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocalBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0 wAct_mul wAct_one wAct_inv_apply wAct_apply_inv)

theorem jhatS_mul (k k' : Jhat) : jhatS (k * k') = jhatS k * jhatS k' := rfl

theorem jhatS_one : jhatS 1 = 1 := rfl

theorem cvOf_jhatS_one :
    cvOf (jhatS 1) = cv0 := rfl

theorem mem_cPi0
    {v : CVert} : v ∈ cPi0 ↔ ∃ k : Jhat, v = cvOf (jhatS k) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, by rw [mul_one]; rfl⟩
  · rintro ⟨k, rfl⟩
    exact jhatS_mem_cPi0 k

@[expose] def labE (k : Jhat) : Ehat := ⟨(k : Dfull)⁻¹ * cQ * k, conj_mem_Ehat k.2 cQ_mem_Ehat⟩

theorem clabel_jhatS
    (k : Jhat) : clabel (cvOf (jhatS k)) = labE k := rfl

theorem psiW_labE
    (k : Jhat) : psiW (labE k) = wAct v0 (jhatToKv0 k) Unitary.sigmaW :=
  (psiW_conj k.2 cQ_mem_Ehat).trans (congrArg (wAct v0 (jhatToKv0 k)) psiW_cE)

theorem coe_piPt
    (k : Jhat) : (piPt k : Wv v0) = wAct v0 (jhatToKv0 k) Unitary.sigmaW := rfl

theorem piPt_eq_psiW
    (k : Jhat) : (piPt k : Wv v0) = psiW (labE k) := (psiW_labE k).symm

theorem coe_piPt_mul
    (k p : Jhat) :
    (piPt (k * p) : Wv v0) = wAct v0 (jhatToKv0 p) (piPt k) := by
  rw [coe_piPt, coe_piPt, map_mul, wAct_mul, Module.End.mul_apply]

theorem coe_piPt_one :
    (piPt 1 : Wv v0) = Unitary.sigmaW := by
  rw [coe_piPt, map_one, wAct_one, Module.End.one_apply]

@[expose] def p1Orb
    (v : CVert) : Set CVert := {w | ∃ p : Shat, (p : Dfull) ∈ P1 ∧ w = cvMul v p}

@[expose] def p1J {p : Dfull} (hp : p ∈ P1) : Jhat := ⟨p, P1_le_Jhat hp⟩

theorem jhatS_p1J {p : Shat} (hp : (p : Dfull) ∈ P1) : jhatS (p1J hp) = p := rfl

theorem jhatToKv0_mem_Usig
    {p : Jhat} (hp : (p : Dfull) ∈ P1) : jhatToKv0 p ∈ Unitary.Usig := by
  rw [← map_P1]
  exact ⟨p, hp, rfl⟩

theorem exists_P1_of_mem_Usig
    {u : Kstab v0} (hu : u ∈ Unitary.Usig) :
    ∃ p : Jhat, (p : Dfull) ∈ P1 ∧ jhatToKv0 p = u := by
  rw [← map_P1] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  exact ⟨p, hp, rfl⟩

theorem p1Orb_cv0 :
    p1Orb cv0 = {cv0} := by
  ext w
  simp only [p1Orb, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (cvMul_cv0_iff p).2 (Pc_le_Eam 0 hp)
  · rintro rfl
    exact ⟨1, P1.one_mem, (cvMul_one _).symm⟩

theorem p1Orb_elS
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    p1Orb (cvOf (elS ha)) = {cvOf (elS ha)} := by
  ext w
  simp only [p1Orb, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [cvMul_cvOf, cvOf_eq_iff]
    have e : ((elS ha * (elS ha * p)⁻¹ : Shat) : Dfull) = a * (p : Dfull)⁻¹ * a⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_elS]
      group
    rw [e]
    exact Pc_le_Eam 0 (conj_mem_Pc_zero ha hn ((Pc 0).inv_mem hp))
  · rintro rfl
    exact ⟨1, P1.one_mem, (cvMul_one _).symm⟩

theorem cvMul_jhatS
    (k p : Jhat) : cvMul (cvOf (jhatS k)) (jhatS p) = cvOf (jhatS (k * p)) :=
  rfl

end CFSG.Monster.B.TwoA.Amalgam
