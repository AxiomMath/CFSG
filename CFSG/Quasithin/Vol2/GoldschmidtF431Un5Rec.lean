module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Glue
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigCent
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigConc

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Blueprint CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN
  CFSG.Quasithin.H13.F431.D4q.F48 CFSG.Quasithin.H13.F48Rig CFSG.Quasithin.H13.F431.F48Rig
  CFSG.QuasithinUnique CFSG.Open CFSG.LieType.Universal.Unitary

theorem f431ModelFacts_un5 (f : ℕ) : F431ModelFacts .PSU 5 f := by
  intro D _ hD
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  exact ⟨Finite.of_equiv _ e.toEquiv, center_eq_bot_of_rankTwo (un5System hF ζ) e⟩

theorem f431Generation_un5 (f : ℕ) : F431Generation .PSU 5 f := by
  intro D _ hD A
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  exact range_conj_le_of_rankTwo (un5System hF ζ) hU e A

theorem f431Facts45_un5 (f : ℕ) (hm : F431ModelFacts .PSU 5 f) : F431Facts45 .PSU 5 f hm := by
  intro D _ hD A
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  exact facts45L_of_rankTwo (un5System hF ζ) hU (hm D hD).1 (by norm_num) e A

theorem cartanFPF_un5 (hm : F431ModelFacts .PSU 5 2) (D : Type)
    [Group D] (hD : LieModel D .PSU 5 2 2) (A : LieAmalgamExt D) :
    (A.setting (hm D hD).1 (polyNumber .PSU) (three_le_polyNumber .PSU)).CartanFPF := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (un5System hF ζ) hU (hm D hD).1
    (by norm_num) e A
  obtain ⟨h, hh, hc⟩ := exists_cartan_un5_quot hF ζ
  exact cartanFPF_of_rankTwo (un5System hF ζ) hU (hm D hD).1 (by norm_num) A b
    XD hh hc

theorem faithfulOnType_un5 (f : ℕ) (hm : F431ModelFacts .PSU 5 f) (D : Type) [Group D]
    (hD : LieModel D .PSU 5 2 f) (A : LieAmalgamExt D) (s : Bool) :
    (A.setting (hm D hD).1 (polyNumber .PSU) (three_le_polyNumber .PSU)).FaithfulOnType s := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := un5_model_equiv hD
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Fact ((ζ : F) ≠ 0) := ⟨hζ⟩
  have := isSimpleGroup_un5 hF
  have hU := isSylowTwoOf_un5System hF ζ
  obtain ⟨b, e', hgen, XD⟩ := exists_xdatum (un5System hF ζ) hU (hm D hD).1
    (by norm_num) e A
  exact faithfulOnType_of_rankTwo (un5System hF ζ) hU (hm D hD).1
    (by norm_num) A b XD
    (fun k hk =>
      centralizer_inn_trivial A (hm D hD).1 4 (by norm_num) (hm D hD).2 hgen e'.symm k hk) s

theorem f431F48_un5 (hm : F431ModelFacts .PSU 5 2) : F431F48 .PSU 5 2 hm :=
  f431F48_of_model hm (f431Facts45_un5 2 hm) (f431Generation_un5 2)
    (fun D _ hD A => cartanFPF_un5 hm D hD A)
    (fun D _ hD A => faithfulOnType_un5 2 hm D hD A _)

theorem f431Recognition_un5 : F431Recognition .PSU 5 2 :=
  recognition_of_facts (f431ModelFacts_un5 2) (f431Generation_un5 2) (polyNumber .PSU)
    (three_le_polyNumber _) (f431Facts45_un5 2 (f431ModelFacts_un5 2))
    (f431F48_un5 (f431ModelFacts_un5 2))

end CFSG.Quasithin.H13.F431.Un
