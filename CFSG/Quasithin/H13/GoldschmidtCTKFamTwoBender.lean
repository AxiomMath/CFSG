module

public import CFSG.Quasithin.Vol2.GoldschmidtCor332Bender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.H13.GoldschmidtCTKFamImg

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Quasithin.H13.Cor332 (TwoLocalsSolvable twoLocalsSolvable_of_fusionIsBenderGroup)

theorem not_isSolvable_alt5 : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro h
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).2 h
  let a : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have h1 : a * b ≠ b * a := by
    intro h2
    have := congrArg Subtype.val h2
    revert this
    decide +kernel
  exact h1 (hc a b)

theorem IsDelta5Ext.not_isSolvable {K : Type*} [Group K] {V : Subgroup K}
    (h : IsDelta5Ext K V) : ¬ Group.IsSolvable K := by
  obtain ⟨α, hα, -⟩ := h
  intro hK
  exact not_isSolvable_alt5 (Group.isSolvable_of_surjective hα)

theorem IsDelta5Ext.le_normalizer {S : Type*} [Group S] {K V : Subgroup S} (hVK : V ≤ K)
    (h : IsDelta5Ext ↥K (V.subgroupOf K)) : K ≤ Subgroup.normalizer (V : Set S) := by
  obtain ⟨α, -, hαk, -⟩ := h
  have hnorm : (V.subgroupOf K).Normal := hαk ▸ α.normal_ker
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).1 hnorm

theorem A5Config.false_of_twoLocalsSolvable {S : Type} [Group S] (hS : TwoLocalsSolvable S)
    (h : A5Config S) : False := by
  obtain ⟨K, V, T₁, T₂, hVK, hV16, hel, hΔ, -⟩ := h
  have hV0 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV16
    omega
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num)
  exact hΔ.not_isSolvable (hS V K hV0 hV2 (hΔ.le_normalizer hVK))

theorem exclA5BlockFor_bender :
    ExclA5BlockFor fun S _ =>
      (∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 2 f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel S 2 f) := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  have hB : fusionIsBenderGroup S := by
    rcases hS with ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, -, -, h⟩
    · exact K1.fusionIsBenderGroup_of_stated_psl_two hf h
    · exact K1.fusionIsBenderGroup_of_stated_psu_three hf h
    · exact K1.fusionIsBenderGroup_of_suzukiModel h
  exact hc.false_of_twoLocalsSolvable (twoLocalsSolvable_of_fusionIsBenderGroup hB)

end CFSG.Quasithin.H13.CTK
