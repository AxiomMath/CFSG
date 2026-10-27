module

public import CFSG.Milestones.ASVolI.F4N.L11
public import CFSG.Milestones.ASVolI.F4N.Rig

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF411_Ident {E : Type} [Group E] (p : ℕ) (M₁ M₂ : Subgroup E) : Prop :=
  ∀ T : Subgroup E, IsPGroup p T → ¬ p ∣ T.index → T ≤ M₁ ⊓ M₂ →
    ∀ X₁ X₂ : Subgroup E, Nonempty (↥X₁ ≃* ↥M₁) → Nonempty (↥X₂ ≃* ↥M₂) → T ≤ X₁ → T ≤ X₂ →
      X₁ ⊔ X₂ = ⊤ → (X₁ = M₁ ∧ X₂ = M₂) ∨ (X₁ = M₂ ∧ X₂ = M₁)

@[expose] def burnsideF411_Swap {E : Type} [Group E] (M₁ M₂ : Subgroup E) : Prop :=
  ∀ (χ₁ : ↥M₁ →* E) (χ₂ : ↥M₂ →* E), Function.Injective χ₁ → Function.Injective χ₂ →
    χ₁.range = M₂ → χ₂.range = M₁ →
    (∀ x : ↥(M₁ ⊓ M₂), χ₁ (Subgroup.inclusion inf_le_left x) =
      χ₂ (Subgroup.inclusion inf_le_right x)) →
    ∃ θ : E ≃* E, M₁.map θ.toMonoidHom = M₂ ∧ M₂.map θ.toMonoidHom = M₁

theorem burnsideF411_quasiEquiv_of_equiv {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (hgen : M₁ ⊔ M₂ = ⊤) {Y : Type} [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful)
    (e : E ≃* Y) (h1 : μ.φ1.range.comap e.toMonoidHom = M₁)
    (h2 : μ.φ2.range.comap e.toMonoidHom = M₂) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion (incl M₁ M₂).toCompletion := by
  let φ : Y ≃* ↥(M₁ ⊔ M₂) :=
    e.symm.trans ((Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr hgen.symm))
  have hφsymm : ∀ z : ↥(M₁ ⊔ M₂), φ.symm z = e (z : E) := fun z => rfl
  have hm1 : ∀ x : E, e x ∈ μ.φ1.range ↔ x ∈ M₁ := fun x => SetLike.ext_iff.mp h1 x
  have hm2 : ∀ x : E, e x ∈ μ.φ2.range ↔ x ∈ M₂ := fun x => SetLike.ext_iff.mp h2 x
  refine burnsideF4n_quasiEquiv_of_map μ (incl M₁ M₂) hμ (incl_faithful M₁ M₂) φ ?_ ?_
  · ext z
    rw [Subgroup.mem_map_equiv, hφsymm, burnsideF4n_mem_range_incl1]
    exact hm1 _
  · ext z
    rw [Subgroup.mem_map_equiv, hφsymm, burnsideF4n_mem_range_incl2]
    exact hm2 _

theorem burnsideF411_comap_range1_equiv {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful) (e : E ≃* Y) :
    Nonempty (↥(μ.φ1.range.comap e.toMonoidHom) ≃* ↥M₁) :=
  ⟨((μ.φ1.range.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _)).trans
      (MonoidHom.ofInjective hμ.1).symm)⟩

theorem burnsideF411_comap_range2_equiv {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful) (e : E ≃* Y) :
    Nonempty (↥(μ.φ2.range.comap e.toMonoidHom) ≃* ↥M₂) :=
  ⟨((μ.φ2.range.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _)).trans
      (MonoidHom.ofInjective hμ.2.2).symm)⟩

theorem burnsideF411_comap_range_sup {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] (μ : Cpl M₁ M₂ Y) (e : E ≃* Y) :
    μ.φ1.range.comap e.toMonoidHom ⊔ μ.φ2.range.comap e.toMonoidHom = ⊤ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective e.surjective,
    Subgroup.map_comap_eq_self_of_surjective e.surjective, μ.gen,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem burnsideF411_exists_equiv_sylow {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    {M₁ M₂ : Subgroup E} {T : Subgroup E} (hTp : IsPGroup p T) (hTi : ¬ p ∣ T.index)
    (hT : T ≤ M₁ ⊓ M₂) {Y : Type} [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful)
    (e : E ≃* Y) :
    ∃ e' : E ≃* Y, T ≤ μ.φ1.range.comap e'.toMonoidHom ∧
      T ≤ μ.φ2.range.comap e'.toMonoidHom := by
  classical
  haveI : Finite Y := Finite.of_equiv E e.toEquiv
  let Sa : Subgroup Y := T.map e.toMonoidHom
  let T₀ : Subgroup (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := T.comap (M₁ ⊓ M₂).subtype
  let Sb : Subgroup Y := T₀.map μ.φ12
  have hcardT₀ : Nat.card T₀ = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
  have hcardSa : Nat.card Sa = Nat.card T := Subgroup.card_map_of_injective e.injective
  have hcardSb : Nat.card Sb = Nat.card T := by
    rw [Subgroup.card_map_of_injective hμ.2.1, hcardT₀]
  obtain ⟨n, hn⟩ := hTp.exists_card_eq
  have hSap : IsPGroup p Sa := IsPGroup.of_card (n := n) (by rw [hcardSa, hn])
  have hSbp : IsPGroup p Sb := IsPGroup.of_card (n := n) (by rw [hcardSb, hn])
  have hcardY : Nat.card Y = Nat.card E := (Nat.card_congr e.toEquiv).symm
  have hidx : ∀ S : Subgroup Y, Nat.card S = Nat.card T → S.index = T.index := by
    intro S hS
    have h1 := Subgroup.card_mul_index S
    have h2 := Subgroup.card_mul_index T
    rw [hS, hcardY] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hSai : ¬ p ∣ Sa.index := hidx Sa hcardSa ▸ hTi
  have hSbi : ¬ p ∣ Sb.index := hidx Sb hcardSb ▸ hTi
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y (hSbp.toSylow hSbi) (hSap.toSylow hSai)
  have hconj : ∀ x, x ∈ Sa ↔ ∃ s ∈ Sb, y * s * y⁻¹ = x := by
    intro x
    have hSaeq : Sa = ((y • hSbp.toSylow hSbi : Sylow p Y) : Subgroup Y) := by
      rw [hy, IsPGroup.toSylow_coe]
    rw [hSaeq, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, Subgroup.mem_smul_pointwise_iff_exists]
    simp only [MulAut.smul_def, MulAut.conj_apply]
  let e' : E ≃* Y := e.trans (MulAut.conj y⁻¹)
  have he' : ∀ x, e' x = y⁻¹ * e x * y⁻¹⁻¹ := fun x => rfl
  have hmem : ∀ t ∈ T, e' t ∈ μ.φ12.range := by
    intro t ht
    obtain ⟨s, hs, hseq⟩ := (hconj (e t)).mp ⟨t, ht, rfl⟩
    obtain ⟨b, -, rfl⟩ := hs
    refine ⟨b, ?_⟩
    rw [he', ← hseq, inv_inv]
    group
  have h12le1 : μ.φ12.range ≤ μ.φ1.range := μ.inter ▸ inf_le_left
  have h12le2 : μ.φ12.range ≤ μ.φ2.range := μ.inter ▸ inf_le_right
  exact ⟨e', fun t ht => h12le1 (hmem t ht), fun t ht => h12le2 (hmem t ht)⟩

theorem burnsideF411_rigid_of_ident_swap {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E]
    {M₁ M₂ : Subgroup E} (hgen : M₁ ⊔ M₂ = ⊤) {T : Subgroup E} (hTp : IsPGroup p T)
    (hTi : ¬ p ∣ T.index) (hT : T ≤ M₁ ⊓ M₂) (hId : burnsideF411_Ident p M₁ M₂)
    (hSw : burnsideF411_Swap M₁ M₂) {Y : Type} [Group Y] (μ : Cpl M₁ M₂ Y) (hμ : μ.IsFaithful)
    (e : E ≃* Y) :
    Amalgam.Completion.IsQuasiEquivalent μ.toCompletion (incl M₁ M₂).toCompletion := by
  classical
  obtain ⟨e', hT1, hT2⟩ := burnsideF411_exists_equiv_sylow hTp hTi hT μ hμ e
  rcases hId T hTp hTi hT _ _ (burnsideF411_comap_range1_equiv μ hμ e')
      (burnsideF411_comap_range2_equiv μ hμ e') hT1 hT2 (burnsideF411_comap_range_sup μ e') with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact burnsideF411_quasiEquiv_of_equiv hgen μ hμ e' h1 h2
  ·
    let χ₁ : ↥M₁ →* E := e'.symm.toMonoidHom.comp μ.φ1
    let χ₂ : ↥M₂ →* E := e'.symm.toMonoidHom.comp μ.φ2
    have hχ1 : Function.Injective χ₁ := e'.symm.injective.comp hμ.1
    have hχ2 : Function.Injective χ₂ := e'.symm.injective.comp hμ.2.2
    have hr : ∀ (H : Type) [Group H] (f : H →* Y),
        (e'.symm.toMonoidHom.comp f).range = f.range.comap e'.toMonoidHom := by
      intro H _ f
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        show e' (e'.symm (f a)) ∈ f.range
        rw [MulEquiv.apply_symm_apply]
        exact ⟨a, rfl⟩
      · rintro ⟨a, ha⟩
        refine ⟨a, ?_⟩
        show e'.symm (f a) = x
        rw [ha]
        exact e'.symm_apply_apply x
    have hr1 : χ₁.range = M₂ := (hr _ μ.φ1).trans h1
    have hr2 : χ₂.range = M₁ := (hr _ μ.φ2).trans h2
    have hagree : ∀ x : ↥(M₁ ⊓ M₂), χ₁ (Subgroup.inclusion inf_le_left x) =
        χ₂ (Subgroup.inclusion inf_le_right x) := by
      intro x
      exact congrArg e'.symm ((μ.comm1 x).trans (μ.comm2 x).symm)
    obtain ⟨θ, hθ1, hθ2⟩ := hSw χ₁ χ₂ hχ1 hχ2 hr1 hr2 hagree
    refine burnsideF411_quasiEquiv_of_equiv hgen μ hμ (θ.trans e') ?_ ?_
    · have : μ.φ1.range.comap (θ.trans e').toMonoidHom =
          (μ.φ1.range.comap e'.toMonoidHom).comap θ.toMonoidHom := rfl
      rw [this, h1, ← hθ1, Subgroup.comap_map_eq_self_of_injective θ.injective]
    · have : μ.φ2.range.comap (θ.trans e').toMonoidHom =
          (μ.φ2.range.comap e'.toMonoidHom).comap θ.toMonoidHom := rfl
      rw [this, h2, ← hθ2, Subgroup.comap_map_eq_self_of_injective θ.injective]

theorem burnsideF411_rigidExt_of_local
    (h : ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
      HypF_4_4 κ p f Gp M₁ M₂ → Gp ≠ ⊤ →
        (∃ T : Subgroup E, IsPGroup p T ∧ ¬ p ∣ T.index ∧ T ≤ M₁ ⊓ M₂) ∧
          burnsideF411_Ident p M₁ M₂ ∧ burnsideF411_Swap M₁ M₂) :
    burnsideF4n_F411RigidExt := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp ι hι Y _ μ hμ he
  subst hι
  obtain ⟨e⟩ := he
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨burnsideF4a_prime_of_isGenLie hyp.model⟩
  obtain ⟨⟨T, hTp, hTi, hT⟩, hId, hSw⟩ := h κ p f E Gp M₁ M₂ hyp hGp
  let eY : E ≃* Y := e.trans ((MulEquiv.subgroupCongr μ.gen).trans Subgroup.topEquiv)
  exact burnsideF411_rigid_of_ident_swap hyp.gen hTp hTi hT hId hSw μ hμ eY

end CFSG.ASVolI
