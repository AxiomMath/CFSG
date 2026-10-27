module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qFacts45
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qGen
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.Hex CFSG.Quasithin.H13.F431.F48Rig CFSG.Quasithin.H13.F48Rig
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex CFSG.QuasithinUnique


set_option linter.unusedSectionVars false

theorem cartanFPF_d4 (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .trialityD4 0 f) (D : Type)
    [Group D] (hD : LieModel D .trialityD4 0 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .trialityD4)
      (three_le_polyNumber .trialityD4)).CartanFPF := by
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := d4q_model_data hD
  have hq4 : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq : 2 ≤ 2 ^ f := by omega
  obtain ⟨eC⟩ := exists_d4Model_equiv σ (by omega) hK hσ
  have hU := d4ModelSystem_isSylow σ (by omega) hK hσ hq
  have := isSimpleGroup_d4Model σ.toRingHom hq hK hσ
  have := finite_d4Model σ.toRingHom
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (d4ModelSystem σ.toRingHom hq hK hσ) hU (hm D hD).1
    (by norm_num) (eC.trans e.symm) A
  exact cartanFPF_d4Model hq hK hσ hU (hm D hD).1 A hq4 b XD

theorem faithfulOnType_d4 (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .trialityD4 0 f) (D : Type)
    [Group D] (hD : LieModel D .trialityD4 0 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .trialityD4)
      (three_le_polyNumber .trialityD4)).FaithfulOnType s := by
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := d4q_model_data hD
  have hq : 2 ≤ 2 ^ f := calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨eC⟩ := exists_d4Model_equiv σ (by omega) hK hσ
  have hU := d4ModelSystem_isSylow σ (by omega) hK hσ hq
  have := isSimpleGroup_d4Model σ.toRingHom hq hK hσ
  have := finite_d4Model σ.toRingHom
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (d4ModelSystem σ.toRingHom hq hK hσ) hU (hm D hD).1
    (by norm_num) (eC.trans e.symm) A
  exact faithfulOnType_d4Model hq hK hσ hU (hm D hD).1 A b XD
    (fun k hk =>
      centralizer_inn_trivial A (hm D hD).1 6 (by norm_num) (hm D hD).2 hgen e'.symm k hk) s

theorem f431F48_d4q (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .trialityD4 0 f) :
    F431F48 .trialityD4 0 f hm :=
  f431F48_of_model hm (f431Facts45_d4 f hm) (f431Generation_d4 f)
    (fun D _ hD A => cartanFPF_d4 f hf hm D hD A)
    (fun D _ hD A => faithfulOnType_d4 f hf hm D hD A _)

end CFSG.Quasithin.H13.F431.D4q.F48
