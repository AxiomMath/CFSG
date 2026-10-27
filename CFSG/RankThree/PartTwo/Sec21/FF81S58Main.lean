module

public import CFSG.RankThree.PartTwo.Sec21.FF81S58Sym

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem op_two_inf_eq_bot_of_model {K : Subgroup G} {t₀ : G} (hKt : K ≤ Cen t₀)
    (hm : StatedClassicalModel K .PSp 3 2 1) : Op 2 (Cen t₀) ⊓ K = ⊥ := by
  have hTp : IsPGroup 2 (Op 2 (Cen t₀)) := S59.op_two_isPGroup' t₀
  haveI : IsSimpleGroup K :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp K 3 2 1 hm
  haveI hn : ((Op 2 (Cen t₀) ⊓ K).subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨S59.op_two_conj' (hKt g.2) hn.1, K.mul_mem (K.mul_mem g.2 hn.2) (K.inv_mem g.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Op 2 (Cen t₀) ⊓ K).subgroupOf K) with h | h
  · refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, hx.2⟩ : K) ∈ (Op 2 (Cen t₀) ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hKT : K ≤ Op 2 (Cen t₀) := fun x hx => by
      have : (⟨x, hx⟩ : K) ∈ (Op 2 (Cen t₀) ⊓ K).subgroupOf K := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    obtain ⟨n, hn⟩ := (hTp.to_le hKT).exists_card_eq
    rw [card_of_model hm] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem cen_le_nor_op_two (t₀ : G) : Cen t₀ ≤ Nor (Op 2 (Cen t₀)) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => S59.op_two_conj' hg hs, fun hs => by
    have := S59.op_two_conj' ((Cen t₀).inv_mem hg) hs
    rwa [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at this⟩

theorem setMul_eq_coe_sup {H K : Subgroup G} (h : K ≤ Nor H) : setMul H K = ↑(H ⊔ K) := by
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H K h]
  ext x
  simp only [setMul, Set.mem_setOf_eq, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, k, hk, rfl⟩; exact ⟨a, ha, k, hk, rfl⟩
  · rintro ⟨a, ha, k, hk, rfl⟩; exact ⟨a, ha, k, hk, rfl⟩

theorem setMul_op_two_eq {t₀ : G} {K M' : Subgroup G} (hKt : K ≤ Cen t₀)
    (hK : StatedClassicalModel K .PSp 3 2 1) (hM' : StatedClassicalModel M' .PSp 3 2 1)
    (hM'S : setMul (Op 2 (Cen t₀)) M' = Cen t₀) : setMul (Op 2 (Cen t₀)) K = Cen t₀ := by
  set T := Op 2 (Cen t₀) with hT
  have hM't : M' ≤ Cen t₀ := fun m hm => by
    have : m ∈ setMul T M' := ⟨1, (Op 2 (Cen t₀)).one_mem, m, hm, (one_mul m).symm⟩
    rw [hM'S] at this
    exact this
  have hsupM : T ⊔ M' = Cen t₀ := by
    apply SetLike.coe_injective
    rw [← setMul_eq_coe_sup ((hM't.trans (cen_le_nor_op_two t₀)))]
    exact hM'S
  have hTM : T ⊓ M' = ⊥ := op_two_inf_eq_bot_of_model hM't hM'
  have hTK : T ⊓ K = ⊥ := op_two_inf_eq_bot_of_model hKt hK
  have c1 := card_sup_mul_card_inf M' T (hM't.trans (cen_le_nor_op_two t₀))
  have c2 := card_sup_mul_card_inf K T (hKt.trans (cen_le_nor_op_two t₀))
  rw [sup_comm, hsupM, inf_comm, hTM, Subgroup.card_bot, mul_one] at c1
  rw [sup_comm, inf_comm, hTK, Subgroup.card_bot, mul_one] at c2
  have hKM : Nat.card K = Nat.card M' := by rw [card_of_model hK, card_of_model hM']
  have hle : T ⊔ K ≤ Cen t₀ := sup_le (S59.op_two_le' t₀) hKt
  have hsup : T ⊔ K = Cen t₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [c1, c2, hKM]
  rw [setMul_eq_coe_sup (hKt.trans (cen_le_nor_op_two t₀)), hsup]


theorem ff81_5_8 :
    KF_McLaughlin6 → KF_HoltThm1 → KF_FF81aProp1 → FF81_3_2 → FF81_5_2_6 → FF81_5_7 →
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
      FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
      ∀ M : Subgroup G, FF81Conc5_7 b b₁ b₂ b₃ s₀ M → FF81Conc5_8 L t₀ := by
  intro hMcl hHolt hP1 h32 h526p h57 G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 h526 M hM7
  obtain ⟨M', h526', hM7'⟩ := rerun hMcl hHolt hP1 h32 h526p h57 h5 h526 hM7
  obtain ⟨-, -, -, hS, -⟩ := h526'
  exact ⟨setMul_op_two_eq (S59.le_cen_of_mem_cenS h5.ht₀L) h5.basis.hyp.model hM7'.2.1
    hM7'.2.2.1, hS⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
