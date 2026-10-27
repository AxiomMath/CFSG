module

public import CFSG.RankThree.GF2n.Tim78P210

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Setup210

variable {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁)
include S

theorem nrm_eq_omega (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hne : B₀ ≠ B₁) (h0 : ∀ x ∈ nrm B₀ B₁, x * x = 1) (h1 : ∀ x ∈ nrm B₁ B₀, x * x = 1) :
    nrm B₀ B₁ = PartTwo.omegaOneSub B₀ := by
  by_contra hFL
  have P := S.prop24Setup h0 h1 hFL
  obtain ⟨y, hyB, hyy, hyF⟩ := S.exists_sq_mem h0 h1 hFL
  have hFle : nrm B₀ B₁ ≤ PartTwo.omegaOneSub B₀ := fun x hx =>
    S.mem_L₀.mpr ⟨(mem_nrm.mp hx).1, h0 x hx⟩
  obtain ⟨t, htL, htF⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hFle hFL)
  obtain ⟨z, hzL, hzF⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne P.Lb_le P.Lb_ne)
  have D : QData B₀ B₁ (sqPre B₀ (nrm B₀ B₁) S.comm) (sqPre B₁ (nrm B₁ B₀) S.comm₁) :=
    { setup := S
      ne := hne
      invol₀ := h0
      invol₁ := h1
      memA₀ := fun _ => Iff.rfl
      memA₁ := fun _ => Iff.rfl
      neA₀ := ⟨y, ⟨hyB, hyF⟩, fun h => hyy (h0 y h)⟩
      neA₁ := ⟨z, ⟨(S.mem_L₁.mp hzL).1, by rw [(S.mem_L₁.mp hzL).2]; exact (nrm B₁ B₀).one_mem⟩,
        hzF⟩ }
  have hN := D.normal_Q
  have QP := D.quotPair
  set R := sqPre B₀ (nrm B₀ B₁) S.comm ⊔ sqPre B₁ (nrm B₁ B₀) S.comm₁ with hR
  have htA : t ∈ sqPre B₀ (nrm B₀ B₁) S.comm :=
    ⟨(S.mem_L₀.mp htL).1, by rw [(S.mem_L₀.mp htL).2]; exact (nrm B₀ B₁).one_mem⟩
  have hyA : y ∈ sqPre B₀ (nrm B₀ B₁) S.comm := ⟨hyB, hyF⟩
  have htR : t ∈ R := Subgroup.mem_sup_left htA
  have hyR : y ∈ R := Subgroup.mem_sup_left hyA
  have htQ : t ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ := fun h => htF (D.mem_F₀_of_mem_Q (S.mem_L₀.mp htL).1 h)
  have hyQ : y ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ := fun h => hyy (h0 y (D.mem_F₀_of_mem_Q hyB h))
  have hmem : ∀ (x : G) (hx : x ∈ sqPre B₀ (nrm B₀ B₁) S.comm),
      QuotientGroup.mk' ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf R) ⟨x, Subgroup.mem_sup_left hx⟩ ∈
        ((sqPre B₀ (nrm B₀ B₁) S.comm).subgroupOf R).map
          (QuotientGroup.mk' ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf R)) :=
    fun x hx => ⟨⟨x, _⟩, hx, rfl⟩
  have hne1 : ∀ (x : G) (hx : x ∈ R), x ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ →
      QuotientGroup.mk' ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf R) ⟨x, hx⟩ ≠ 1 :=
    fun x hx hxQ h => hxQ ((QData.mk_eq_one_iff _).mp h)
  obtain ⟨c', hc'⟩ := isConj_iff.mp (QP.isConj_of_involution hCen hU
    (QP.sq_eq_one QuotPair.mem_pairConj_left (hmem t htA)) (hne1 t htR htQ)
    (QP.sq_eq_one QuotPair.mem_pairConj_left (hmem y hyA)) (hne1 y hyR hyQ))
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ c'
  set v : ↥R := c * ⟨t, htR⟩ * c⁻¹ with hv
  have hvA : (v : G) ∈ conjSubgroup (c : G) (sqPre B₀ (nrm B₀ B₁) S.comm) := by
    rw [mem_conjSubgroup, hv]
    simpa [mul_assoc] using htA
  have hvQ : (v : G) ∉ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    intro h
    apply htQ
    have hcN := D.R_le_normalizer_Q c.2
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) _).mp h
    simpa [hv, mul_assoc] using this
  have hvy : QuotientGroup.mk' ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf R) v =
      QuotientGroup.mk' ((nrm B₀ B₁ ⊔ nrm B₁ B₀).subgroupOf R) ⟨y, hyR⟩ := by
    rw [hv, map_mul, map_mul, map_inv]
    exact hc'
  have hcomm := D.commute_mod (v := v) (w := ⟨y, hyR⟩) (by rw [hvy])
  have he := D.eq_of_commute_mod_side QData.isSide_left QData.isSide_left c.2 R.one_mem hvA hvQ
    (by rw [conjSubgroup_one]; exact hyA) hyQ hcomm
  rw [conjSubgroup_one] at he
  have hvB : (v : G) ∈ B₀ := he ▸ (D.side_memA QData.isSide_left c.2).mp hvA |>.1
  have hvv : (v : G) * v = 1 := by
    rw [hv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (c : G) * t * (c : G)⁻¹ * ((c : G) * t * (c : G)⁻¹) = (c : G) * (t * t) * (c : G)⁻¹ by
      group, (S.mem_L₀.mp htL).2, mul_one, mul_inv_cancel]
  have hq : ((v : G))⁻¹ * y ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
    have := QuotientGroup.eq.mp hvy
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have hqF := D.mem_F₀_of_mem_Q (B₀.mul_mem (B₀.inv_mem hvB) hyB) hq
  have hyL : y ∈ PartTwo.omegaOneSub B₀ := by
    rw [show y = (v : G) * ((v : G)⁻¹ * y) by group]
    exact (PartTwo.omegaOneSub B₀).mul_mem (S.mem_L₀.mpr ⟨hvB, hvv⟩) (hFle hqF)
  exact hyy (S.mem_L₀.mp hyL).2

omit [Finite G] in
theorem exp₁ (hexp : ∀ x ∈ B₀, x ^ 4 = 1) : ∀ x ∈ B₁, x ^ 4 = 1 := by
  obtain ⟨g, rfl⟩ := S.conj
  intro x hx
  have h := hexp _ (mem_conjSubgroup.mp hx)
  rw [show (g⁻¹ * x * g) ^ 4 = g⁻¹ * x ^ 4 * g by
    simpa using conj_pow (a := g⁻¹) (b := x) (i := 4)] at h
  calc x ^ 4 = g * (g⁻¹ * x ^ 4 * g) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem qdata_full (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hexp : ∀ x ∈ B₀, x ^ 4 = 1) (hne : B₀ ≠ B₁) (h0 : ∀ x ∈ nrm B₀ B₁, x * x = 1)
    (h1 : ∀ x ∈ nrm B₁ B₀, x * x = 1) : QData B₀ B₁ B₀ B₁ := by
  have hF0 := S.nrm_eq_omega hCen hU hne h0 h1
  have hF1 := S.symm.nrm_eq_omega hCen hU (Ne.symm hne) h1 h0
  refine
    { setup := S
      ne := hne
      invol₀ := h0
      invol₁ := h1
      memA₀ := fun z => ⟨fun hz => ⟨hz, by rw [hF0]; exact S.sq_mem_L₀ hz (hexp z hz)⟩,
        fun h => h.1⟩
      memA₁ := fun z => ⟨fun hz => ⟨hz, by rw [hF1]; exact S.symm.sq_mem_L₀ hz (S.exp₁ hexp z hz)⟩,
        fun h => h.1⟩
      neA₀ := ?_
      neA₁ := ?_ }
  · obtain ⟨x, hx, hx2⟩ := S.exp_ne
    exact ⟨x, hx, fun h => hx2 (by rw [sq]; exact h0 x h)⟩
  · obtain ⟨x, hx, hx2⟩ := S.exp_ne₁
    exact ⟨x, hx, fun h => hx2 (by rw [sq]; exact h1 x h)⟩

theorem quot_models (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hexp : ∀ x ∈ B₀, x ^ 4 = 1) (hne : B₀ ≠ B₁) (h0 : ∀ x ∈ nrm B₀ B₁, x * x = 1)
    (h1 : ∀ x ∈ nrm B₁ B₀, x * x = 1) :
    ∃ _ : ((PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁)).Normal,
      ((∃ f : ℕ, 2 ≤ f ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ^ f ∧
          Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
            (B₀ ⊔ B₁) ≃* PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ^ (2 * a + 1) ∧
          Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
            (B₀ ⊔ B₁) ≃* Sz a)) ∨
        (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ∧
          Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
            (B₀ ⊔ B₁) ≃* DihedralGroup m))) := by
  have D := S.qdata_full hCen hU hexp hne h0 h1
  have hF0 := S.nrm_eq_omega hCen hU hne h0 h1
  have hF1 := S.symm.nrm_eq_omega hCen hU (Ne.symm hne) h1 h0
  rw [← hF0, ← hF1]
  have hN := D.normal_Q
  refine ⟨hN, ?_⟩
  obtain ⟨-, hmod⟩ := D.quotPair.models hCen hU
  rw [D.relIndex_eq_card_image]
  exact hmod

end Setup210

theorem mem_normalizer_omega_iff {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBti : IsTI B) (hL1 : PartTwo.omegaOneSub B ≠ ⊥) (x : G) :
    x ∈ Subgroup.normalizer (PartTwo.omegaOneSub B : Set G) ↔
      x ∈ Subgroup.normalizer (B : Set G) := by
  rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_eq_self_iff, ← omegaOneSub_conj hBc]
  constructor
  · intro h
    refine conjSubgroup_eq_of_isTI hBti fun hbot => hL1 ?_
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ PartTwo.omegaOneSub (conjSubgroup x B) := h ▸ hy
    have : y ∈ B ⊓ conjSubgroup x B :=
      Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le B hy, PartTwo.omegaOneSub_le _ hy'⟩
    rwa [hbot] at this
  · intro h
    rw [h]

theorem tim78_2_10_b (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁) (hexp : ∀ x ∈ B₀, x ^ 4 = 1) :
    (∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a) ∨
      ∃ _ : ((PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf (B₀ ⊔ B₁)).Normal,
        ((∃ f : ℕ, 2 ≤ f ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ^ f ∧
            Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
              (B₀ ⊔ B₁) ≃* PSL(2, GaloisField 2 f))) ∨
          (∃ a : ℕ, 1 ≤ a ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ^ (2 * a + 1) ∧
            Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
              (B₀ ⊔ B₁) ≃* Sz a)) ∨
          (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ (PartTwo.omegaOneSub B₀).relIndex B₀ = 2 ∧
            Nonempty (↥(B₀ ⊔ B₁) ⧸ (PartTwo.omegaOneSub B₀ ⊔ PartTwo.omegaOneSub B₁).subgroupOf
              (B₀ ⊔ B₁) ≃* DihedralGroup m))) := by
  by_cases hne : B₀ = B₁
  · subst hne
    exact Or.inl S.comm
  by_cases h0 : ∃ x ∈ nrm B₀ B₁, x * x ≠ 1
  · obtain ⟨x, hx, hx2⟩ := h0
    exact Or.inl (S.commutes_of_sq_ne_one hx hx2)
  by_cases h1 : ∃ x ∈ nrm B₁ B₀, x * x ≠ 1
  · obtain ⟨x, hx, hx2⟩ := h1
    have h := S.symm.commutes_of_sq_ne_one hx hx2
    exact Or.inl fun a ha b hb => (h b hb a ha).symm
  simp only [not_exists, not_and, not_not] at h0 h1
  exact Or.inr (S.quot_models hCen hU hexp hne h0 h1)

theorem tim78_2_10_a (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁) :
    (∀ a ∈ PartTwo.omegaOneSub B₀, ∀ b ∈ PartTwo.omegaOneSub B₁, a * b = b * a) ∧
      IsRootTypeTI (PartTwo.omegaOneSub B₀) := by
  have key : ∀ {C₀ C₁ : Subgroup G}, Setup210 C₀ C₁ →
      ∀ a ∈ PartTwo.omegaOneSub C₀, ∀ b ∈ PartTwo.omegaOneSub C₁, a * b = b * a := by
    intro C₀ C₁ T a ha b hb
    have haC := PartTwo.omegaOneSub_le C₀ ha
    have hbC := PartTwo.omegaOneSub_le C₁ hb
    by_cases hne : C₀ = C₁
    · subst hne
      exact T.comm a haC b hbC
    by_cases h0 : ∃ x ∈ nrm C₀ C₁, x * x ≠ 1
    · obtain ⟨x, hx, hx2⟩ := h0
      exact T.commutes_of_sq_ne_one hx hx2 a haC b hbC
    by_cases h1 : ∃ x ∈ nrm C₁ C₀, x * x ≠ 1
    · obtain ⟨x, hx, hx2⟩ := h1
      exact (T.symm.commutes_of_sq_ne_one hx hx2 b hbC a haC).symm
    simp only [not_exists, not_and, not_not] at h0 h1
    have hF0 := T.nrm_eq_omega hCen hU hne h0 h1
    have hF1 := T.symm.nrm_eq_omega hCen hU (Ne.symm hne) h1 h0
    rw [← hF0] at ha
    rw [← hF1] at hb
    exact T.comm_nrm hne ha hb
  refine ⟨key S, ?_, ?_⟩
  ·
    intro k
    by_cases hk : PartTwo.omegaOneSub B₀ ⊓ conjSubgroup k (PartTwo.omegaOneSub B₀) = ⊥
    · exact Or.inl hk
    · right
      have hB : conjSubgroup k B₀ = B₀ := by
        refine conjSubgroup_eq_of_isTI S.ti fun hbot => hk ?_
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        have hy2' : k⁻¹ * y * k ∈ PartTwo.omegaOneSub B₀ := mem_conjSubgroup.mp hy2
        have : y ∈ B₀ ⊓ conjSubgroup k B₀ := Subgroup.mem_inf.mpr
          ⟨PartTwo.omegaOneSub_le B₀ hy1, mem_conjSubgroup.mpr (PartTwo.omegaOneSub_le B₀ hy2')⟩
        rwa [hbot] at this
      rw [← omegaOneSub_conj S.comm, hB, inf_idem]
  ·
    intro g hg a ha b hb
    have hL1 : PartTwo.omegaOneSub (conjSubgroup g B₀) ≠ ⊥ := by
      rw [omegaOneSub_conj S.comm]
      intro h
      apply hg
      have h0 : PartTwo.omegaOneSub B₀ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : g * x * g⁻¹ ∈ conjSubgroup g (PartTwo.omegaOneSub B₀) := by
          rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
          exact hx
        rw [h, Subgroup.mem_bot] at hx'
        rw [Subgroup.mem_bot]
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [hx']; group
      rw [h0, bot_inf_eq]
    have T : Setup210 B₀ (conjSubgroup g B₀) :=
      { comm := S.comm
        two := S.two
        exp_ne := S.exp_ne
        ti := S.ti
        conj := ⟨g, rfl⟩
        ne_bot := by
          intro hbot
          apply hg
          rw [eq_bot_iff]
          intro x hx
          obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
          rw [← omegaOneSub_conj S.comm] at hxN
          have hxN' := (mem_normalizer_omega_iff (fun x hx y hy => by
            have h := S.comm _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
            calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
              _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
              _ = y * x := by group) (isTI_conjSubgroup S.ti g) hL1 x).mp hxN
          have : x ∈ B₀ ⊓ Subgroup.normalizer (conjSubgroup g B₀ : Set G) :=
            Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le B₀ hxL, hxN'⟩
          rwa [hbot] at this }
    rw [← omegaOneSub_conj S.comm] at hb
    exact key T a ha b hb

end CFSG.RankThree.GF2n.Tim78
