module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofStar
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofL3Aut
import CFSG.LieType.Simplicity.TrialityD4

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Census228ExcTwoEvenAut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (∃ f : ℕ, Even f ∧ (Blueprint.ChevalleyExceptionalModel Y .G2 2 f ∨
      Blueprint.ChevalleyExceptionalModel Y .trialityD4 2 f)) →
    ∀ (B : Subgroup Y) (y : Y) (N Kb : Subgroup Y) (m : ℕ),
      IsElemAbelian 3 B → Nat.card B = 9 → y ∈ B → y ≠ 1 →
      (∀ k ∈ N, y * k = k * y) → (∀ g : Y, g * y = y * g → ∀ k ∈ N, g * k * g⁻¹ ∈ N) →
      Kb ≤ N → Nonempty (Kb ≃* projSL 2 (GaloisField 2 m)) → 0 < m → Even m →
      (Kb = N ∨ StatedClassicalModel N .PSU 3 2 2) →
      ∃ g : Y, (∀ b ∈ B, g * b * g⁻¹ ∈ B) ∧ (∀ b ∈ B, g ^ 3 * b = b * g ^ 3) ∧
        ∃ b ∈ B, g * b ≠ b * g

namespace Item228Census4Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_imgInf {X A : Subgroup G} (hAe : IsElemAbelian 3 A) :
    IsElemAbelian 3 (Item22Res4Proof.imgInf X A) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have ha'' := (Subgroup.mem_subgroupOf.mp ha').1
    have hb'' := (Subgroup.mem_subgroupOf.mp hb').1
    have hab0 : (a' : G) * b' = b' * a' :=
      congrArg Subtype.val (hAe.1.is_comm.comm (⟨a', ha''⟩ : A) ⟨b', hb''⟩)
    have hab : a' * b' = b' * a' := Subtype.ext hab0
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul, hab]
  · rintro _ ⟨a', ha', rfl⟩
    have ha'' := (Subgroup.mem_subgroupOf.mp ha').1
    have h3 : a' ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ ha'')
    rw [← map_pow, h3, map_one]

end Item228Census4Proof

open Item228Census4Proof

theorem census228ExcTwoEven_of
    (hK : Census228ExcTwoEvenAut) : Census228ExcTwoEven := by
  intro G _ _ X A K K₀ m hP hAmax hA27 hAN hAC hin hmono _ ρ hρ hρr hKK hK0X hK0C hnorm hU hKm
    hm0 hme
  set Y := X ⧸ aschbacherSolvableCore 3 X with hY
  have hS : IsSimpleGroup Y := by
    obtain ⟨f, -, hG | hD⟩ := hP
    · exact (CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 f hG).2
    · exact (CFSG.LieType.Simplicity.fam_3d4_simplicity _ 2 f hD).2
  have hAe : IsElemAbelian 3 A := hAmax.prop
  obtain ⟨b, hbA, hbN, hβ1, N, Kb, hcfg⟩ := Item228Census2Proof.config228Aut_of hAmax hA27 hAN
    hAC hρ hρr hKK hK0X hK0C hnorm hU hKm hm0 hme
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hb | ht
    · exact hb
    · exfalso
      apply hβ1
      have hinn : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) ∈
          (MulAut.conj : Y →* MulAut Y).range := by
        by_contra h
        exact hin b hbA ⟨hbN, h⟩
      obtain ⟨z, hz⟩ := hinn
      rw [← hz]
      ext w
      rw [MulAut.conj_apply, MulAut.one_apply,
        (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top z) w).symm, mul_inv_cancel_right]
  obtain ⟨d, hdA, hd⟩ := Item22Res4Proof.exists_mem_conj_eq_thetaAct hAmax hAN hin hZ ⟨b, hbA⟩
  rw [Sec4.thetaAct_apply] at hd
  set yb : Y := (d : Y) with hyb
  have hyB : yb ∈ Item22Res4Proof.imgInf X A :=
    ⟨d, Subgroup.mem_subgroupOf.mpr ⟨hdA, d.2⟩, rfl⟩
  have hy1 : yb ≠ 1 := fun h => hβ1 (by rw [← hd, h, map_one])
  have hconj : ∀ k : Y, Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨b, hbN⟩) k = yb * k * yb⁻¹ :=
    fun k => by rw [← hd, MulAut.conj_apply]
  have hcomm : ∀ k ∈ N, yb * k = k * yb := fun k hk => by
    have h1 := hcfg.fix k hk
    rw [hconj] at h1
    calc yb * k = yb * k * yb⁻¹ * yb := by group
      _ = k * yb := by rw [h1]
  have hnorm' : ∀ g : Y, g * yb = yb * g → ∀ k ∈ N, g * k * g⁻¹ ∈ N := by
    intro g hg k hk
    refine hcfg.normalizes g ?_ k hk
    rw [hconj, ← hg, mul_inv_cancel_right]
  obtain ⟨g, hgN, h3, h1⟩ := hK Y hP (Item22Res4Proof.imgInf X A) yb N Kb m
    (isElemAbelian_imgInf hAe) (Item22Res4Proof.card_imgInf hAmax hA27 hAN hAC hin hZ) hyB hy1
    hcomm hnorm' hcfg.le hcfg.equiv hcfg.pos hcfg.even hcfg.eq_or
  exact Item22Res4Proof.false_of_order_three hAmax hAN hAC hin hZ hmono hgN h3 h1

end CFSG.RankThree.PartTwo.Sec21
