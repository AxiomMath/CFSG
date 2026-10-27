module

public import CFSG.Milestones.ASVolI.F4N.CIota
public import CFSG.Milestones.ASVolI.F4N.CPset
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F4N.L23b

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Pre

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

theorem burnsideF4nC_N1set_le (c : α.Completion Y) (cc y : c.Γ) :
    N1set c GLKind.Tits cc y ⊆ stv c c.xv := by
  intro s hs
  unfold N1set at hs
  rw [if_pos rfl] at hs
  exact hs.1

theorem burnsideF4nC_N2set_le (c : α.Completion Y) (cc y y' : c.Γ) :
    N2set c GLKind.Tits cc y y' ⊆ stv c c.lv := by
  intro s hs
  unfold N2set at hs
  rw [if_pos rfl] at hs
  exact hs.1

theorem burnsideF4nC_ncard_N1_pre (c : α.Completion Y) (hc : c.IsFaithful) (cc y : c.Γ) :
    (N1set c GLKind.Tits cc y).ncard =
      {a : α.G1 | f1 (c := c) a ∈ N1set c GLKind.Tits cc y}.ncard := by
  have h : N1set c GLKind.Tits cc y =
      (f1 (c := c)) '' {a : α.G1 | f1 (c := c) a ∈ N1set c GLKind.Tits cc y} := by
    ext s
    constructor
    · intro hs
      obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 c (burnsideF4nC_N1set_le c cc y hs)
      exact ⟨a, hs, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  conv_lhs => rw [h]
  exact Set.ncard_image_of_injective _ (f1_injective c hc)

theorem burnsideF4nC_ncard_N2_pre (c : α.Completion Y) (hc : c.IsFaithful) (cc y y' : c.Γ) :
    (N2set c GLKind.Tits cc y y').ncard =
      {b : α.G2 | f2 (c := c) b ∈ N2set c GLKind.Tits cc y y'}.ncard := by
  have h : N2set c GLKind.Tits cc y y' =
      (f2 (c := c)) '' {b : α.G2 | f2 (c := c) b ∈ N2set c GLKind.Tits cc y y'} := by
    ext s
    constructor
    · intro hs
      obtain ⟨b, rfl⟩ := stv_lv_le_range_f2 c (burnsideF4nC_N2set_le c cc y y' hs)
      exact ⟨b, hs, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb
  conv_lhs => rw [h]
  exact Set.ncard_image_of_injective _ (f2_injective c hc)

end Pre

section Main


theorem burnsideF4nC_F420_tits (h45 : F_4_5) (h46 : F_4_6) :
    ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → κ = .Tits →
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
        ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
        ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
          Set.ncard (N1set β κ cc y) = 2 ^ 4 ∧ Set.ncard (N2set β κ cc y y') = 2 ^ 6 ∧
          Set.ncard (Pset β κ cc y y') = 2 ^ 9 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.xv ⊓ Qu p Gp β β.lv, g * s * g⁻¹ = s' := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ Y _ β hβ hs cc hcc hccl y hy hyx y' hy' hy'x
  subst hκ
  have hP := burnsideF4nC_ncard_Pset h45 h46 hyp hGp β hβ hs hcc hccl hy hyx hy' hy'x
  subst hGp
  obtain ⟨hp2, hf1, -⟩ := hyp.model
  subst hp2
  subst hf1
  obtain ⟨Md⟩ := burnsideF4nC_model hyp
  have hι := incl_faithful M₁ M₂
  have hιs : (incl M₁ M₂).IsSmall GLKind.Tits.m :=
    burnsideF4b_IotaSmall_of (burnsideF4n_facts46All h46) h45 .Tits 2 1 E ⊤ M₁ M₂ hyp
  have Fβ := burnsideF4n_facts46_at h46 hyp β hβ
  have Fι := burnsideF4n_facts46_at h46 hyp (incl M₁ M₂) hι
  obtain ⟨a₀, rfl⟩ := burnsideF4n_exists_a0 β hcc
  obtain ⟨b₀, rfl⟩ := burnsideF4n_exists_b0 β hy
  obtain ⟨-, -, -, ha₀β, hb₀β, -⟩ := burnsideF4n_corr_props β hβ a₀ b₀ b₀
  obtain ⟨hcι, hyι, -, ha₀ι, hb₀ι, -⟩ := burnsideF4n_corr_props (incl M₁ M₂) hι a₀ b₀ b₀
  have hcclι := ha₀ι.mpr (ha₀β.mp hccl)
  have hyxι := hb₀ι.mpr (hb₀β.mp hyx)
  have hN1 := fun a => burnsideF4n_N1set_tits_iff β (incl M₁ M₂) hβ hι Fβ Fι a₀ a
    (f2 (c := β) b₀ • β.xv) (incl M₁ M₂).xv
  have hN2 := fun b => burnsideF4n_N2set_tits_iff β (incl M₁ M₂) hβ hι b₀ b
    (f1 (c := β) a₀ • β.lv) y' (incl M₁ M₂).lv (incl M₁ M₂).xv
  refine ⟨?_, ?_, hP, ?_⟩
  ·
    rw [burnsideF4nC_ncard_N1_pre β hβ]
    simp only [hN1]
    rw [← burnsideF4nC_ncard_N1_pre _ hι]
    exact burnsideF4nC_md_card_N1 h45 h46 hyp (incl M₁ M₂) hι hιs Md hcι hcclι _
  ·
    rw [burnsideF4nC_ncard_N2_pre β hβ]
    simp only [hN2]
    rw [← burnsideF4nC_ncard_N2_pre _ hι]
    exact burnsideF4nC_md_card_N2 Md hyι hyxι _ _
  ·
    intro s hs s' hs'
    obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 β (burnsideF4nC_N1set_le β _ _ hs)
    obtain ⟨a', rfl⟩ := stv_xv_le_range_f1 β (burnsideF4nC_N1set_le β _ _ hs')
    obtain ⟨g, ⟨hgx, hgl⟩, hg⟩ := burnsideF4nC_md_trans h45 h46 hyp (incl M₁ M₂) hι hιs Md hcι
      hcclι _ _ ((hN1 a).1 hs) _ ((hN1 a').1 hs')
    have hQι := burnsideF4b_QNormalized 2 (inferInstance : (⊤ : Subgroup E).Normal) (incl M₁ M₂)
    have hQβ := burnsideF4b_QNormalized 2 (inferInstance : (⊤ : Subgroup E).Normal) β
    have hQxι : Qu 2 ⊤ (incl M₁ M₂) (incl M₁ M₂).xv = Qx 2 ⊤ (incl M₁ M₂) :=
      Qvert_baseVert hQι false
    have hQlι : Qu 2 ⊤ (incl M₁ M₂) (incl M₁ M₂).lv = Ql 2 ⊤ (incl M₁ M₂) :=
      Qvert_baseVert hQι true
    have hQxβ : Qu 2 ⊤ β β.xv = Qx 2 ⊤ β := Qvert_baseVert hQβ false
    have hQlβ : Qu 2 ⊤ β β.lv = Ql 2 ⊤ β := Qvert_baseVert hQβ true
    rw [← burnsideF4nC_iota_Qu hyp, hQxι] at hgx
    rw [← burnsideF4nC_iota_Qu hyp, hQlι] at hgl
    obtain ⟨d₁, hd₁, rfl⟩ := hgx
    obtain ⟨d₂, hd₂, hd₁₂⟩ := hgl
    have hY : (incl M₁ M₂).φ1 d₁ = (incl M₁ M₂).φ2 d₂ := congrArg Subtype.val hd₁₂.symm
    have hint : (incl M₁ M₂).φ1 d₁ ∈ (incl M₁ M₂).φ1.range ⊓ (incl M₁ M₂).φ2.range :=
      ⟨⟨d₁, rfl⟩, ⟨d₂, hY.symm⟩⟩
    rw [(incl M₁ M₂).inter] at hint
    obtain ⟨d, hd⟩ := hint
    have hd1 : (RankTwoAmalgam.ofSubgroups M₁ M₂).α1 d = d₁ :=
      hι.1 (by rw [(incl M₁ M₂).comm1]; exact hd)
    have hd2 : (RankTwoAmalgam.ofSubgroups M₁ M₂).α2 d = d₂ :=
      hι.2.2 (by rw [(incl M₁ M₂).comm2]; exact hd.trans hY)
    refine ⟨f1 (c := β) d₁, ⟨?_, ?_⟩, ?_⟩
    · rw [hQxβ]
      exact ⟨d₁, hd₁, rfl⟩
    · rw [hQlβ]
      refine ⟨d₂, hd₂, ?_⟩
      rw [← hd1, ← hd2, burnsideF4n_f1_alpha1]
    · have hconj : d₁ * a * d₁⁻¹ = a' := by
        apply f1_injective (incl M₁ M₂) hι
        rw [map_mul, map_mul, map_inv]
        exact hg
      rw [← hconj, map_mul, map_mul, map_inv]

theorem burnsideF4nC_F420_of_g2d (h45 : F_4_5) (h46 : F_4_6)
    (hG : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → Gp = ⊤ → κ = .G2d →
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        ∀ cc ∈ CosetGeom.nbrs β.xv, cc ≠ β.lv →
        ∀ y ∈ CosetGeom.nbrs β.lv, y ≠ β.xv →
        ∀ y' ∈ CosetGeom.nbrs cc, y' ≠ β.xv →
          Set.ncard (N1set β κ cc y) = 4 ∧ Set.ncard (N2set β κ cc y y') = 4 ∧
          Set.ncard (Pset β κ cc y y') = 8 ∧
          ∀ s ∈ N1set β κ cc y, ∀ s' ∈ N1set β κ cc y,
            ∃ g ∈ Qu p Gp β β.lv ⊓ Qu p Gp β cc, g * s * g⁻¹ = s') :
    F_4_20 := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp _ Y _ β hβ hs cc hcc hccl y hy hyx y' hy' hy'x
  exact ⟨fun hκ => burnsideF4nC_F420_tits h45 h46 κ p f E Gp M₁ M₂ hyp hGp hκ Y β hβ hs cc hcc
      hccl y hy hyx y' hy' hy'x,
    fun hκ => hG κ p f E Gp M₁ M₂ hyp hGp hκ Y β hβ hs cc hcc hccl y hy hyx y' hy' hy'x⟩

end Main

end CFSG.ASVolI
