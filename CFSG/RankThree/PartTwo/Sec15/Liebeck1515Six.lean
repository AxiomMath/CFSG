module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Orders
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

@[expose] def IsType1483 (X : Type*) [Group X] : Prop :=
  Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON ∨ IsCentralProductA6Covers X ∨
    IsA6CoverTimesA5 X ∨
    Nonempty (X ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
    Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    (∃ _ : Fact (Nat.Prime 7),
      Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))

private theorem noNormal3_of_isA6CoverTimesA5 {W : Type*} [Group W] [Finite W]
    (h : IsA6CoverTimesA5 W) : Ronan148W.NoNormal3 W := by
  obtain ⟨U, V, hUn, hVn, hint, hsup, hU, ⟨ψ⟩⟩ := h
  have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have h1 : ⁅u, v⁆ ∈ U ⊓ V :=
      (Subgroup.commutator_le_inf U V) (Subgroup.commutator_mem_commutator hu hv)
    rw [hint, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [Ronan148W.card_alternatingGroup_six]
    norm_num
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have hV : Ronan148W.NoNormal3 V :=
    Ronan148W.noNormal3_congr ψ.symm
      (Ronan148W.noNormal3_of_isSimpleGroup (by rw [h60]; norm_num))
  have hcen : Subgroup.center V = ⊥ := by
    have hmap := Subgroup.map_center_eq ψ
    rw [Ronan148J.center_alternatingGroup_five_eq_bot] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).mp hmap
  refine Ronan148W.noNormal3_of_commute_sup hUn hVn hsup hcomm
    (Ronan148W.noNormal3_of_isTripleCover h3 hU) hV
    (fun z hz => Ronan148W.pow_three_eq_one_of_mem_center hU.1 hz) fun z hz => ?_
  rw [hcen, Subgroup.mem_bot] at hz
  rw [hz, one_pow]

theorem noNormal3_of_isType1483 {X : Type*} [Group X] [Finite X]
    (h : IsType1483 X) : Ronan148W.NoNormal3 X := by
  rcases h with hON | hcp | ha5 | h55 | h7 | ⟨hp7, hL37⟩
  · exact Ronan148W.noNormal3_of_isTripleCover_ON hON
  · exact Ronan148W.noNormal3_of_isCentralProductA6Covers hcp
  · exact noNormal3_of_isA6CoverTimesA5 ha5
  · obtain ⟨e⟩ := h55
    exact Ronan148W.noNormal3_congr e.symm Ronan148W.noNormal3_alternating_five_sq
  · obtain ⟨e⟩ := h7
    exact Ronan148W.noNormal3_congr e.symm Ronan148W.noNormal3_alternatingGroup_seven
  · haveI := hp7
    obtain ⟨e⟩ := hL37
    exact Ronan148W.noNormal3_congr e.symm Ronan148W.noNormal3_projSL_three_seven

theorem card_eq_of_isTripleCover_ON {X : Type*} [Group X]
    (h : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) :
    Nat.card X = 3 * 460815505920 := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, hc, CFSG.Sporadic.ON.card_ON]

private theorem card_of_isA6CoverTimesA5 {W : Type*} [Group W] [Finite W]
    (h : IsA6CoverTimesA5 W) : Nat.card W = 64800 := by
  obtain ⟨U, V, -, hVn, hint, hsup, hU, ⟨φ⟩⟩ := h
  have hN : U ≤ Subgroup.normalizer (V : Set W) := by
    rw [@Subgroup.normalizer_eq_top _ _ V hVn]
    exact le_top
  have key := Ronan148V.card_sup_mul_card_inf hN
  rw [hsup, hint, Subgroup.card_top, Subgroup.card_bot, HJRes2.card_of_isTripleCover_six hU,
    Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at key
  omega

theorem twentyFive_dvd_card {X : Type*} [Group X] [Finite X]
    (h : IsCentralProductA6Covers X ∨ IsA6CoverTimesA5 X ∨
      Nonempty (X ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    25 ∣ Nat.card X := by
  rcases h with hcp | ha5 | h55
  · rw [Ronan148V.card_of_isCentralProductA6Covers hcp]
    norm_num
  · rw [card_of_isA6CoverTimesA5 ha5]
    norm_num
  · obtain ⟨e⟩ := h55
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num

theorem card_ge_of_isType1483 {X : Type*} [Group X] [Finite X]
    (h : IsType1483 X) : 2520 ≤ Nat.card X := by
  rcases h with hON | hcp | ha5 | h55 | h7 | ⟨hp7, hL37⟩
  · rw [card_eq_of_isTripleCover_ON hON]
    norm_num
  · rw [Ronan148V.card_of_isCentralProductA6Covers hcp]
    norm_num
  · rw [card_of_isA6CoverTimesA5 ha5]
    norm_num
  · obtain ⟨e⟩ := h55
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    norm_num
  · obtain ⟨e⟩ := h7
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  · haveI := hp7
    obtain ⟨e⟩ := hL37
    rw [Nat.card_congr e.toEquiv, Sec15.card_projSL_three_seven]
    norm_num

private theorem cubeComm_of_isType1483 {X : Type*} [Group X]
    (h : IsType1483 X) : Read148Perf.CubeComm X := by
  have hA6 : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Read148Perf.isPerfect_alternatingGroup_six
  have hA5 : Read148Perf.CubeComm (alternatingGroup (Fin 5)) :=
    Read148Perf.cubeComm_alternatingGroup 5 le_rfl
  rcases h with hON | hcp | ha5 | h55 | h7 | ⟨hp7, hL37⟩
  · have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.Sporadic.ON.isSimpleGroup_ON
    have hONp : Group.IsPerfect CFSG.Blueprint.NativeSporadic.ON :=
      Read148Perf.isPerfect_of_isSimpleGroup_of_not_prime
        (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
    exact Read148Perf.CubeComm.of_isTripleCover hON hONp
  · obtain ⟨U, V, -, -, hsup, hcomm, -, hU, hV⟩ := hcp
    exact Read148Perf.CubeComm.of_sup hsup hcomm
      (Read148Perf.CubeComm.of_isTripleCover hU hA6)
      (Read148Perf.CubeComm.of_isTripleCover hV hA6)
  · obtain ⟨U, V, hUn, hVn, hint, hsup, hU, ⟨eV⟩⟩ := ha5
    have hcomm : ⁅U, V⁆ = ⊥ := le_bot_iff.mp (hint ▸ Subgroup.commutator_le_inf U V)
    exact Read148Perf.CubeComm.of_sup hsup hcomm
      (Read148Perf.CubeComm.of_isTripleCover hU hA6) (hA5.of_mulEquiv eV)
  · obtain ⟨e⟩ := h55
    exact (hA5.prod hA5).of_mulEquiv e
  · obtain ⟨e⟩ := h7
    exact (Read148Perf.cubeComm_alternatingGroup 7 (by norm_num)).of_mulEquiv e
  · haveI := hp7
    obtain ⟨e⟩ := hL37
    have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
    have : IsSimpleGroup X := e.isSimpleGroup
    exact Read148Perf.CubeComm.of_isSimpleGroup (KFacts.three_dvd_card_of_mulEquiv_projSL e)

theorem isPerfect_of_isType1483 {X : Type*} [Group X]
    (h : IsType1483 X)
    (h3 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 3 (X ⧸ N) → N = ⊤) : Group.IsPerfect X := by
  have hcube := cubeComm_of_isType1483 h
  refine ⟨h3 (commutator X) fun q => ?_⟩
  induction q using QuotientGroup.induction_on with | H x => ?_
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hcube x

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
