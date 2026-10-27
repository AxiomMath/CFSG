module

public import CFSG.Sporadic.MI301.LayerQuot
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301LayerQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

namespace CFSG.Sporadic.MI301Five

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.EvenSporadicStandard.HNRecog Subgroup

private def wrInl : alternatingGroup (Fin 5) →* A5WrTwo :=
  A5WrTwo.baseEmb.comp (MonoidHom.inl _ _)

private def wrInr : alternatingGroup (Fin 5) →* A5WrTwo :=
  A5WrTwo.baseEmb.comp (MonoidHom.inr _ _)

private theorem wrInl_mul_wrInr (a b : alternatingGroup (Fin 5)) :
    wrInl a * wrInr b = A5WrTwo.baseEmb (a, b) := by
  simp only [wrInl, wrInr, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

private theorem wrInr_mul_wrInl (a b : alternatingGroup (Fin 5)) :
    wrInr b * wrInl a = A5WrTwo.baseEmb (a, b) := by
  simp only [wrInl, wrInr, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

private theorem wrInl_injective : Function.Injective wrInl := fun a b h => by
  have h1 : A5WrTwo.baseEmb (a, 1) = A5WrTwo.baseEmb (b, 1) := h
  exact congrArg Prod.fst (A5WrTwo.baseEmb_injective h1)

private theorem wrInr_injective : Function.Injective wrInr := fun a b h => by
  have h1 : A5WrTwo.baseEmb (1, a) = A5WrTwo.baseEmb (1, b) := h
  exact congrArg Prod.snd (A5WrTwo.baseEmb_injective h1)

private theorem wr_commute : ∀ x ∈ wrInl.range, ∀ y ∈ wrInr.range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [wrInl_mul_wrInr, wrInr_mul_wrInl]

private theorem wr_inf_eq_bot : wrInl.range ⊓ wrInr.range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨a, rfl⟩, b, hb⟩
  have h1 : A5WrTwo.baseEmb (1, b) = A5WrTwo.baseEmb (a, 1) := hb
  have ha : a = 1 := (congrArg Prod.fst (A5WrTwo.baseEmb_injective h1)).symm
  rw [ha, map_one]
  exact one_mem _

private theorem wr_sup_eq : wrInl.range ⊔ wrInr.range = commutator A5WrTwo := by
  rw [← A5WrTwo.range_baseEmb]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨(a, 1), rfl⟩
    · rintro _ ⟨b, rfl⟩
      exact ⟨(1, b), rfl⟩
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [← wrInl_mul_wrInr]
    exact mul_mem (mem_sup_left ⟨a, rfl⟩) (mem_sup_right ⟨b, rfl⟩)

private theorem wr_normal_left : (wrInl.range.subgroupOf (wrInl.range ⊔ wrInr.range)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_left]
  have hc : wrInr.range ≤ centralizer (wrInl.range : Set A5WrTwo) := fun y hy =>
    mem_centralizer_iff.2 fun x hx => wr_commute x hx y hy
  exact sup_le le_normalizer (hc.trans (centralizer_le_normalizer _))

private theorem wr_normal_right :
    (wrInr.range.subgroupOf (wrInl.range ⊔ wrInr.range)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  have hc : wrInl.range ≤ centralizer (wrInr.range : Set A5WrTwo) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => (wr_commute x hx y hy).symm
  exact sup_le (hc.trans (centralizer_le_normalizer _)) le_normalizer

private theorem a5_nonabelian : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩, by decide +kernel⟩

variable {f : alternatingGroup (Fin 5) →* A5WrTwo}

private theorem range_isSimple (hf : Function.Injective f) : IsSimpleGroup ↥f.range :=
  (MonoidHom.ofInjective hf).symm.isSimpleGroup

private theorem range_nonabelian (hf : Function.Injective f) :
    ∃ a b : ↥f.range, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := a5_nonabelian
  refine ⟨MonoidHom.ofInjective hf a, MonoidHom.ofInjective hf b, fun h => hab ?_⟩
  apply (MonoidHom.ofInjective hf).injective
  rw [map_mul, map_mul, h]

private theorem five_dvd_card_range (hf : Function.Injective f) : 5 ∣ Nat.card ↥f.range := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

theorem nonempty_pQuot_glaPLayer_a5WrTwo :
    Nonempty (PQuot 5 (GLAPLayer 5 (⊤ : Subgroup A5WrTwo)) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  have hL := CFSG.Sporadic.MI301.glaPLayer_eq_sup_of_isSimple Nat.prime_five
    (H := ⊤) (by rw [wr_sup_eq]; exact .step le_top (Normal.subgroupOf inferInstance ⊤) (.refl ⊤))
    wr_normal_left wr_normal_right (range_isSimple wrInl_injective)
    (range_isSimple wrInr_injective) (range_nonabelian wrInl_injective)
    (range_nonabelian wrInr_injective) (five_dvd_card_range wrInl_injective)
    (five_dvd_card_range wrInr_injective) (by rw [wr_sup_eq]; exact (commutator_def A5WrTwo).ge)
  rw [hL]
  obtain ⟨e⟩ := CFSG.Sporadic.MI301.nonempty_pQuot_sup_equiv_prod Nat.prime_five
    (range_isSimple wrInl_injective) (range_isSimple wrInr_injective)
    (range_nonabelian wrInl_injective) (range_nonabelian wrInr_injective)
    (five_dvd_card_range wrInl_injective) (five_dvd_card_range wrInr_injective) wr_commute
    wr_inf_eq_bot
  exact ⟨e.trans (MulEquiv.prodCongr (MonoidHom.ofInjective wrInl_injective).symm
    (MonoidHom.ofInjective wrInr_injective).symm)⟩

theorem nonempty_pQuot_glaPLayer_of_shape {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : IsExtraspecialPlusByA5WrTwo ↥X) :
    Nonempty (PQuot 5 (GLAPLayer 5 X) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) := by
  obtain ⟨Q, _, hw⟩ := h
  obtain ⟨q⟩ := hw.quotient
  set π : ↥X →* A5WrTwo := q.toMonoidHom.comp (QuotientGroup.mk' Q) with hπ
  have hsurj : Function.Surjective π := q.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hker : π.ker = Q := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ q.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hN : ¬ 5 ∣ Nat.card π.ker := by
    rw [hker, hw.plus.2.1]
    decide
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.H301.nonempty_pQuot_glaPLayer_subtype
    Nat.prime_five X
  obtain ⟨e₂⟩ := CFSG.Sporadic.MI301.nonempty_pQuot_glaPLayer_top_of_surjective Nat.prime_five π
    hsurj hN
  obtain ⟨e₃⟩ := nonempty_pQuot_glaPLayer_a5WrTwo
  exact ⟨e₁.trans (e₂.trans e₃)⟩

end CFSG.Sporadic.MI301Five
