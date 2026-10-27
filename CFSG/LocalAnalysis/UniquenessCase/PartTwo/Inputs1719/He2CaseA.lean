module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.He2LatticeAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicModelGlue
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1 CFSG.Quasithin.RonanE114.HeOver
  CFSG.Quasithin.ModH.He2
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

open CFSG.Quasithin.E2P in
theorem he2_map_S_of_mem {Y J : Type} [Group Y] [Group J] {K S : Subgroup Y} [K.Normal]
    (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S) :
    ∀ t ∈ S, hl.S.map (autK e t).toMonoidHom = hl.S := by
  intro t ht
  rw [← he]
  exact map_autK_of_mem_normalizer' e inf_le_right (le_normalizer_inf ‹K.Normal› ht)

theorem he_map_Y7_of_normalizes {J : Type} [Group J] [Finite J] (hl : HeLat J)
    {α : MulAut J} (hα : hl.S.map α.toMonoidHom = hl.S) :
    (hl.Y 7).map α.toMonoidHom = hl.Y 7 := by
  refine map_eq_of_unique_card (hl.S_le_Y 7) ?_ α hα
  intro Z hZ hc
  rcases hl.complete Z hZ with ⟨j, hj, rfl⟩ | rfl
  · rw [card_Y_idx hl hj, card_Y_idx hl (by norm_num)] at hc
    have hidx : heIdx j = heIdx 7 := by omega
    have key : ∀ j < 11, heIdx j = heIdx 7 → j = 7 := by decide
    rw [key j hj hidx]
  · exfalso
    rw [card_top hl, card_Y7 hl] at hc
    omega

theorem he_map_Y8_Y10_of_fixes_Y3 {J : Type} [Group J] [Finite J] (hl : HeLat J)
    {α : MulAut J}
    (hα : hl.S.map α.toMonoidHom = hl.S) (h3 : (hl.Y 3).map α.toMonoidHom = hl.Y 3) :
    (hl.Y 8).map α.toMonoidHom = hl.Y 8 ∧ (hl.Y 10).map α.toMonoidHom = hl.Y 10 := by
  have h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 4 := by
    rcases aut_Y34 hl hα with ⟨-, h4⟩ | ⟨h3', -⟩
    · exact h4
    · exact absurd (h3'.symm.trans h3) (fun h => Y3_ne_Y4 hl h.symm)
  have h7 : (hl.Y 7).map α.toMonoidHom = hl.Y 7 := he_map_Y7_of_normalizes hl hα
  refine ⟨?_, ?_⟩
  · exact map_of_below hl hα (a := 8) (b := 3) (c := 7) (a' := 8) (b' := 3) (c' := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide)) h3 h7 (by decide)
  · exact map_of_below hl hα (a := 10) (b := 4) (c := 7) (a' := 10) (b' := 4) (c' := 7)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Y_le hl (by norm_num) (by norm_num) (by decide))
      (Y_le hl (by norm_num) (by norm_num) (by decide)) h4 h7 (by decide)

theorem _root_.CFSG.Quasithin.E2P.SporB.autK_mul {H C : Type} [Group H] [Group C]
    {K : Subgroup H} [K.Normal]
    (e : ↥K ≃* C) (t₁ t₂ : H) :
    autK e (t₁ * t₂) = autK e t₁ * autK e t₂ := by
  ext c
  rw [MulAut.mul_apply, autK_apply, autK_apply, autK_apply]
  congr 1
  ext
  simp only [Subtype.coe_mk, MulEquiv.symm_apply_apply]
  group

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem exists_overgroup_of_invariant_data {Y Γ : Type} [Group Y] [Finite Y]
    [Group Γ] [Finite Γ] {K S : Subgroup Y} [K.Normal] (e : ↥K ≃* Γ) {U P : Subgroup Γ}
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U) (hUP : U ≤ P) (m : ℕ)
    (hP : Nat.card P = m * Nat.card U)
    (hinv : ∀ t ∈ S, P.map (autK e t).toMonoidHom = P) :
    ∃ H₀ : Subgroup Y, H₀ ≤ K ∧ S ⊓ K ≤ H₀ ∧ S ≤ Subgroup.normalizer (H₀ : Set Y) ∧
      Nat.card H₀ = Nat.card P ∧ H₀ = (P.map e.symm.toMonoidHom).map K.subtype ∧
      Nat.card ↥(S ⊔ H₀) = m * Nat.card S := by
  set H₀ : Subgroup Y := (P.map e.symm.toMonoidHom).map K.subtype with hH₀
  have hSH₀ : S ⊓ K ≤ H₀ := (le_pull_iff e inf_le_right).mpr (he ▸ hUP)
  have hnorm : S ≤ Subgroup.normalizer (H₀ : Set Y) := fun t ht =>
    mem_normalizer_pull e (hinv t ht)
  have hH₀K : H₀ ≤ K := pull_le e P
  have hinf : S ⊓ H₀ = S ⊓ K :=
    le_antisymm (inf_le_inf_left _ hH₀K) (le_inf inf_le_left hSH₀)
  have hcardH₀ : Nat.card H₀ = Nat.card P := by
    rw [hH₀, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card U := by
    rw [← he, Subgroup.card_map_of_injective e.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    hnorm
  rw [hinf, hcardSK, hcardH₀, hP] at h
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hQc : Nat.card ↥(S ⊔ H₀) = m * Nat.card S := by
    have h2 : Nat.card ↥(S ⊔ H₀) * Nat.card U = (m * Nat.card S) * Nat.card U := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hU0 h2
  exact ⟨H₀, hH₀K, hSH₀, hnorm, hcardH₀, rfl, hQc⟩

open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB in
theorem he2_caseA {Y J : Type} [Group Y] [Finite Y] [Group J] [Finite J]
    {K S : Subgroup Y} [K.Normal] (hl : HeLat J) (e : ↥K ≃* J)
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = hl.S)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    (hSKtop : S ⊔ K = ⊤)
    (hfix : ∀ t ∈ S, (hl.Y 3).map (autK e t).toMonoidHom = hl.Y 3) :
    ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
            H₁ ⊔ H₂ ⊔ H₃ = ⊤ := by
  classical
  have hα := he2_map_S_of_mem hl e he
  have hSc : Nat.card ↥hl.S = 1024 := by
    rw [← Y0_eq_S hl, card_Y_idx hl (by norm_num)]; norm_num [heIdx]
  have hF : ∀ H : Subgroup Y, S ≤ H → Nat.card H = 3 * Nat.card S →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H := by
    intro H hSH hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨A, -, -, hAc, -, hAS, hAP⟩ := exists_permutes_of_overgroup Subgroup.normal_top
      ⟨0, by rw [Subgroup.index_top]; rfl⟩ hS.2.1 hSH (p := 3) (n := 1) (by norm_num)
      (by rw [hc, pow_one])
    rw [← hAS]
    exact inFSq_one_of_prime_mul_two_group A S 3 Nat.prime_three (by decide)
      (by rw [hAc, pow_one]) hS.2.1 hAP
  obtain ⟨H₀₁, -, -, -, -, hH₀₁eq, hQc₁⟩ :=
    exists_overgroup_of_invariant_data e he (hl.S_le_Y 1) 3
      (by rw [card_Y_idx hl (by norm_num), hSc]; norm_num [heIdx])
      fun t ht => map_Y1_of_fixes_Y3 hl (hα t ht) (hfix t ht)
  obtain ⟨H₀₈, -, -, -, -, hH₀₈eq, hQc₈⟩ :=
    exists_overgroup_of_invariant_data e he (hl.S_le_Y 8) 3
      (by rw [card_Y_idx hl (by norm_num), hSc]; norm_num [heIdx])
      fun t ht => (he_map_Y8_Y10_of_fixes_Y3 hl (hα t ht) (hfix t ht)).1
  obtain ⟨H₀₁₀, -, -, -, -, hH₀₁₀eq, hQc₁₀⟩ :=
    exists_overgroup_of_invariant_data e he (hl.S_le_Y 10) 3
      (by rw [card_Y_idx hl (by norm_num), hSc]; norm_num [heIdx])
      fun t ht => (he_map_Y8_Y10_of_fixes_Y3 hl (hα t ht) (hfix t ht)).2
  have hgenY : hl.Y 1 ⊔ hl.Y 8 ⊔ hl.Y 10 = ⊤ := by
    have hSle : hl.S ≤ hl.Y 1 ⊔ hl.Y 8 ⊔ hl.Y 10 :=
      (hl.S_le_Y 1).trans (le_sup_left.trans le_sup_left)
    rcases hl.complete _ hSle with ⟨j, hj, hjeq⟩ | htop
    · exfalso
      have h1 : hl.Y 1 ≤ hl.Y j := by rw [← hjeq]; exact le_sup_left.trans le_sup_left
      have h8 : hl.Y 8 ≤ hl.Y j := by rw [← hjeq]; exact le_sup_right.trans le_sup_left
      have h10 : hl.Y 10 ≤ hl.Y j := by rw [← hjeq]; exact le_sup_right
      have m1 := (hl.le_iff (by norm_num) hj).1 h1
      have m8 := (hl.le_iff (by norm_num) hj).1 h8
      have m10 := (hl.le_iff (by norm_num) hj).1 h10
      revert m1 m8 m10
      interval_cases j <;> decide
    · exact htop
  have hgen : H₀₁ ⊔ H₀₈ ⊔ H₀₁₀ = K := by
    rw [hH₀₁eq, hH₀₈eq, hH₀₁₀eq, ← pull_sup, ← pull_sup, hgenY, pull_top]
  refine ⟨S ⊔ H₀₁, S ⊔ H₀₈, S ⊔ H₀₁₀, le_sup_left, le_sup_left, le_sup_left,
    hF _ le_sup_left hQc₁, hF _ le_sup_left hQc₈, hF _ le_sup_left hQc₁₀, ?_⟩
  calc (S ⊔ H₀₁) ⊔ (S ⊔ H₀₈) ⊔ (S ⊔ H₀₁₀) = S ⊔ (H₀₁ ⊔ H₀₈ ⊔ H₀₁₀) := by ac_rfl
    _ = S ⊔ K := by rw [hgen]
    _ = ⊤ := hSKtop

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
