module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnF48Tor
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qF48Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnSystem

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.Open CFSG.LieType.Universal.Unitary

theorem f431ModelFacts_un (f : ℕ) : F431ModelFacts .PSU 4 f := by
  intro D _ hD
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  exact ⟨Finite.of_equiv _ e.toEquiv, center_eq_bot_of_rankTwo (unSystem hF ζ) e⟩

theorem f431Generation_un (f : ℕ) : F431Generation .PSU 4 f := by
  intro D _ hD A
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  exact range_conj_le_of_rankTwo (unSystem hF ζ) (isSylowTwoOf_unU hF) e A

theorem f431Facts45_un (f : ℕ) (hm : F431ModelFacts .PSU 4 f) : F431Facts45 .PSU 4 f hm := by
  intro D _ hD A
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  exact facts45L_of_rankTwo (unSystem hF ζ) (isSylowTwoOf_unU hF) (hm D hD).1 (by norm_num) e A

theorem cartanFPF_un (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSU 4 f) (D : Type)
    [Group D] (hD : LieModel D .PSU 4 2 f) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .PSU) (three_le_polyNumber .PSU)).CartanFPF := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (unSystem hF ζ) (isSylowTwoOf_unU hF) (hm D hD).1
    (by norm_num) e A
  obtain ⟨h, hh, hc⟩ := exists_cartan_un hF ζ hf
  exact cartanFPF_of_rankTwo (unSystem hF ζ) (isSylowTwoOf_unU hF) (hm D hD).1 (by norm_num) A b
    XD hh hc

theorem faithfulOnType_un (f : ℕ) (hm : F431ModelFacts .PSU 4 f) (D : Type) [Group D]
    (hD : LieModel D .PSU 4 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .PSU) (three_le_polyNumber .PSU)).FaithfulOnType s := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_unSU hF
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (unSystem hF ζ) (isSylowTwoOf_unU hF) (hm D hD).1
    (by norm_num) e A
  exact faithfulOnType_of_rankTwo (unSystem hF ζ) (isSylowTwoOf_unU hF) (hm D hD).1
    (by norm_num) A b XD
    (fun k hk =>
      centralizer_inn_trivial A (hm D hD).1 4 (by norm_num) (hm D hD).2 hgen e'.symm k hk) s

theorem f431F48_un (f : ℕ) (hf : 2 ≤ f) (hm : F431ModelFacts .PSU 4 f) : F431F48 .PSU 4 f hm :=
  f431F48_of_model hm (f431Facts45_un f hm) (f431Generation_un f)
    (fun D _ hD A => cartanFPF_un f hf hm D hD A)
    (fun D _ hD A => faithfulOnType_un f hm D hD A _)

theorem f431Recognition_un (f : ℕ) (hf : 2 ≤ f) : F431Recognition .PSU 4 f :=
  recognition_of_facts (f431ModelFacts_un f) (f431Generation_un f) (polyNumber .PSU)
    (three_le_polyNumber _) (f431Facts45_un f (f431ModelFacts_un f))
    (f431F48_un f hf (f431ModelFacts_un f))

end CFSG.Quasithin.H13.F431.Un
