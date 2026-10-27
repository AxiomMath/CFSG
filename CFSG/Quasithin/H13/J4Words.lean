
module

public import CFSG.Quasithin.H13.J4WordsBase

public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.J4.Cert
public import CFSG.Quasithin.H13.J4WordsInputs
public import Certificates.Certificate7018

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

theorem matChecks_eq : CFSG.Sporadic.J4.Native.matChecks = true :=
  Certificates.certificate7018.1

theorem famRep_base : FamRep baseGL basePairs := by
  have hM := CFSG.Sporadic.J4.matFacts_of matChecks_eq
  intro i
  rcases i with _ | _ | i
  · exact ⟨baseMats_spec hM 0, baseInvs_spec hM 0⟩
  · exact ⟨baseMats_spec hM 1, baseInvs_spec hM 1⟩
  · have hb : baseGL (i + 2) = 1 := by unfold baseGL; simp
    rw [hb]
    exact PrRep.one

theorem famRep_uv : FamRep uvGen (uvPairsOf basePairs) := by
  intro i
  rcases i with _ | _ | i
  · show PrRep u (prWord basePairs uLetters)
    rw [u_eq_wordProd]
    exact famRep_base.word _
  · show PrRep v (prWord basePairs vLetters)
    rw [v_eq_wordProd]
    exact famRep_base.word _
  · have hb : uvGen (i + 2) = 1 := by unfold uvGen; simp
    rw [hb]
    exact PrRep.one

theorem prRep_u :
    PrRep u ((uvPairsOf basePairs)[0]?.getD prOne) := famRep_uv 0

theorem prRep_v :
    PrRep v ((uvPairsOf basePairs)[1]?.getD prOne) := famRep_uv 1

theorem prRep_d : PrRep d (dOf (uvPairsOf basePairs)) :=
  ((prRep_v.inv.mul prRep_u).mul prRep_v).mul prRep_u

theorem prRep_t :
    PrRep t (tOf (uvPairsOf basePairs)) := prRep_d.pow 22

theorem prRep_r :
    PrRep r (rOf (uvPairsOf basePairs)) := prRep_d.pow 11

theorem prRep_conjugator (i : Fin 12) :
    PrRep (conjugator i) (prWord (uvPairsOf basePairs) (coreBasisConjugators.getD i [])) :=
  famRep_uv.word _

theorem prRep_rConj (i : Fin 12) :
    PrRep (rConj i) (rConjOf (uvPairsOf basePairs) (coreBasisConjugators.getD i [])) :=
  ((prRep_conjugator i).mul prRep_r).mul (prRep_conjugator i).inv

theorem tChecks_eq : tChecks = true :=
  Certificates.certificate7018.2

theorem tChecks_spec :
    t * u = u * t ∧ t * v = v * t ∧ t * t = 1 ∧ t ≠ 1 := by
  have h := tChecks_eq
  simp only [tChecks, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine eq_of_eqRows ?_ ?_ h1
    · rw [rowsMatrix_mulRows, prRep_t.1, prRep_u.1, Units.val_mul]
    · rw [rowsMatrix_mulRows, prRep_t.1, prRep_u.1, Units.val_mul]
  · refine eq_of_eqRows ?_ ?_ h2
    · rw [rowsMatrix_mulRows, prRep_t.1, prRep_v.1, Units.val_mul]
    · rw [rowsMatrix_mulRows, prRep_t.1, prRep_v.1, Units.val_mul]
  · refine eq_of_eqRows ?_ ?_ h3
    · rw [rowsMatrix_mulRows, prRep_t.1, Units.val_mul]
    · rw [rowsMatrix_idRows, Units.val_one]
  · intro ht
    apply rowsMatrix_ne_of_rowsNe h4
    rw [prRep_t.1, rowsMatrix_idRows, ht, Units.val_one]

theorem W_le_centralizer :
    W ≤ Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2))) := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
    rintro _ rfl
  · exact tChecks_spec.1
  · exact tChecks_spec.2.1

theorem t_ne_one : t ≠ 1 := tChecks_spec.2.2.2

theorem t_mul_t : t * t = 1 := tChecks_spec.2.2.1

end CFSG.Quasithin.H13.J4
