module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Vol2.F134L2
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.F134.LieF4

open CFSG.ABGLocalTools CFSG.LieType.BorelTits
open scoped MatrixGroups Pointwise

section Sylow

variable {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]

theorem exists_mem_eq_map_conj_of_isSylowOf {S U Q : Subgroup Y} (hS : IsSylowOf p S Q)
    (hU : IsSylowOf p U Q) : ∃ g ∈ Q, U = S.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨S', rfl⟩ := hS
  obtain ⟨U', rfl⟩ := hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q S' U'
  refine ⟨g, g.2, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hz
    exact ⟨s, ⟨s, hs, rfl⟩, by simp [MulAut.smul_def]⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨MulAut.conj g • s, Subgroup.smul_mem_pointwise_smul _ _ _ hs,
      by simp [MulAut.smul_def]⟩

theorem normalizer_le_of_isSylowOf {S U Q : Subgroup Y} (hS : IsSylowOf p S Q)
    (hU : IsSylowOf p U Q) (hSQ : Subgroup.normalizer (S : Set Y) ≤ Q) :
    Subgroup.normalizer (U : Set Y) ≤ Q := by
  obtain ⟨g, hg, rfl⟩ := exists_mem_eq_map_conj_of_isSylowOf hS hU
  rw [← Subgroup.map_equiv_normalizer_eq]
  rintro _ ⟨x, hx, rfl⟩
  have hxQ := hSQ hx
  change g * x * g⁻¹ ∈ Q
  exact Q.mul_mem (Q.mul_mem hg hxQ) (Q.inv_mem hg)

theorem isSylowOf_of_sylow (S : Sylow p Y) {Q : Subgroup Y} (hSQ : (S : Subgroup Y) ≤ Q) :
    IsSylowOf p (S : Subgroup Y) Q := by
  have hS : IsSylowOf p (S : Subgroup Y) ⊤ := isSylowOf_iff.2 ⟨le_top, S.isPGroup', by
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index⟩
  exact hS.of_le hSQ le_top

end Sylow

theorem exists_proper_overgroup_of_holds {Y : Type*} [Group Y] [Finite Y] (hBT : Holds Y 2)
    {U H : Subgroup Y} (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H)
    (hcard : (U.subgroupOf H).index.factorial < Nat.card H) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (U.subgroupOf H).normalCore with hC
  have hCne : C ≠ ⊥ := by
    intro hbot
    have h := (U.subgroupOf H).index_normalCore_dvd_factorial_index
    rw [← hC, hbot, Subgroup.index_bot] at h
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos _) h) (not_le.2 hcard)
  set V := C.map H.subtype with hV
  have hVU : V ≤ U := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hc)
  have hVne : V ≠ ⊥ := by
    intro h
    apply hCne
    rwa [hV, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  have hVsub : V.subgroupOf H = C := by
    rw [hV, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hHV : H ≤ Subgroup.normalizer (V : Set Y) := by
    have hn : (V.subgroupOf H).Normal := by
      rw [hVsub]
      exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C)).1 hn
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hVne (hU.isPGroup.to_le hVU)
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, normalizer_le_of_isSylowOf
    (isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

section SL2

variable {K : Type*} [Field K] [Finite K]

theorem nonempty_mulEquiv_sl2_psl2_eight (hK : Nat.card K = 8) :
    Nonempty (SL(2, K) ≃* PSL(2, GaloisField 2 3)) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hc : Subgroup.center SL(2, GaloisField 2 3) = ⊥ := CFSG.Walter.sl2_center_eq_bot_of_charTwo
  let e₂ : SL(2, GaloisField 2 3) ≃* PSL(2, GaloisField 2 3) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center _))
      ⟨(injective_iff_map_eq_one _).2 fun t ht => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hc] at ht
        exact Subgroup.mem_bot.1 ht,
      QuotientGroup.mk'_surjective _⟩
  exact ⟨(CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
    (FiniteField.ringEquivOfCardEq hcard)).trans e₂⟩

theorem card_sl2_eight (hK : Nat.card K = 8) : Nat.card SL(2, K) = 504 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_psl2_eight hK
  rw [Nat.card_congr e.toEquiv, card_psl2_two (by norm_num)]
  norm_num

theorem noElemNine_sl2_eight (hK : Nat.card K = 8) :
    NoElemNine SL(2, K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_psl2_eight hK
  exact NoElemNine.of_mulEquiv e (noElemNine_psl2 (by norm_num) (by norm_num))

end SL2

end CFSG.Quasithin.F134.LieF4
