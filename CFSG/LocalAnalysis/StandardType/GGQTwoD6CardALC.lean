module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2d6l_card_fix_conj {G : Type} [Group G] {Bs : Subgroup G}
    (s φ : MulAut ↥Bs) :
    Nat.card {b : ↥Bs // (s * φ * s⁻¹) b = b} = Nat.card {b : ↥Bs // φ b = b} := by
  have key : ∀ y : ↥Bs, (s * φ * s⁻¹) (s y) = s (φ y) := by
    intro y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  apply Nat.card_congr
  refine
  { toFun := fun b => ⟨s⁻¹ b, ?_⟩
    invFun := fun b => ⟨s b, ?_⟩
    left_inv := fun b => ?_
    right_inv := fun b => ?_ }
  · have h1 := congrArg (fun x => s⁻¹ x) b.2
    show φ (s⁻¹ (b : ↥Bs)) = s⁻¹ (b : ↥Bs)
    simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] using h1
  · show (s * φ * s⁻¹) (s (b : ↥Bs)) = s (b : ↥Bs)
    rw [key (b : ↥Bs), b.2]
  · ext; simp
  · ext; simp

private lemma ggQ2d6l_isRefl_conj {G : Type} [Group G] {Bs : Subgroup G} (p : ℕ)
    (s φ : MulAut ↥Bs) (h : GGIsReflection p φ) :
    GGIsReflection p (s * φ * s⁻¹) := by
  obtain ⟨h2, hfix⟩ := h
  refine ⟨?_, ?_⟩
  · have hc : s * φ * s⁻¹ = (MulAut.conj s) φ := by rw [MulAut.conj_apply]
    rw [hc, ← map_pow, h2, map_one]
  · rw [ggQ2d6l_card_fix_conj s φ, hfix]

private lemma ggQ2d6l_transp_eq_isSwap (k : ℕ) :
    ggTransp k = {t : Equiv.Perm (Fin k) | t.IsSwap} := by
  ext t
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨a, b, hab, rfl⟩

private lemma ggQ2d6l_closure_transp_top : Subgroup.closure (ggTransp 6) = ⊤ := by
  rw [ggQ2d6l_transp_eq_isSwap 6]
  exact Equiv.Perm.closure_isSwap

theorem ggQ2d6l_inner_of_index_two {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (AJ AL : Subgroup (MulAut ↥Bs)) (hle : AJ ≤ AL) (hnot : ¬ AL ≤ AJ)
    (Φ : Equiv.Perm (Fin 6) ≃* ↥AJ)
    (hΦ1 : ∀ t ∈ ggTransp 6, GGIsReflection 3 (Φ t : MulAut ↥Bs))
    (hΦ2 : ∀ r ∈ AJ, GGIsReflection 3 r → ∃ t ∈ ggTransp 6, r = (Φ t : MulAut ↥Bs))
    (hcard : Nat.card ↥AL ≤ 1440) :
    ∀ s ∈ AL, ∃ g ∈ AJ, ∀ r ∈ AJ, s * r * s⁻¹ = g * r * g⁻¹ := by
  have hcardAJ : Nat.card ↥AJ = 720 := by
    rw [← Nat.card_congr Φ.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hcard_le : Nat.card ↥AJ ≤ Nat.card ↥AL :=
    Nat.card_le_card_of_injective (fun x : ↥AJ => (⟨(x : MulAut ↥Bs), hle x.2⟩ : ↥AL))
      (by
        intro a b hab
        exact Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hsubAJ : Nat.card ↥(AJ.subgroupOf AL) = 720 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardAJ]
  have hindex : (AJ.subgroupOf AL).index = 2 := by
    have hci := Subgroup.card_mul_index (AJ.subgroupOf AL)
    rw [hsubAJ] at hci
    have hge : 720 ≤ Nat.card ↥AL := hcardAJ ▸ hcard_le
    have h1 : 1 ≤ (AJ.subgroupOf AL).index := by omega
    have h2 : (AJ.subgroupOf AL).index ≤ 2 := by omega
    have h12 : (AJ.subgroupOf AL).index = 1 ∨ (AJ.subgroupOf AL).index = 2 := by omega
    rcases h12 with h1' | h2'
    · exact absurd ((Subgroup.subgroupOf_eq_top).1 ((Subgroup.index_eq_one).1 h1')) hnot
    · exact h2'
  have hnorm : (AJ.subgroupOf AL).Normal := Subgroup.normal_of_index_eq_two hindex
  intro s hs
  have hmem : ∀ σ : Equiv.Perm (Fin 6), s * (Φ σ : MulAut ↥Bs) * s⁻¹ ∈ AJ := by
    intro σ
    have h1 : (⟨s, hs⟩ : ↥AL) * (⟨(Φ σ : MulAut ↥Bs), hle (Φ σ).2⟩ : ↥AL) *
        (⟨s, hs⟩ : ↥AL)⁻¹ ∈ AJ.subgroupOf AL :=
      hnorm.conj_mem (⟨(Φ σ : MulAut ↥Bs), hle (Φ σ).2⟩ : ↥AL)
        ((Subgroup.mem_subgroupOf).2 (Φ σ).2) (⟨s, hs⟩ : ↥AL)
    show s * (Φ σ : MulAut ↥Bs) * s⁻¹ ∈ AJ
    exact (Subgroup.mem_subgroupOf).1 h1
  let π : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) :=
    { toFun := fun σ => Φ.symm ⟨s * (Φ σ : MulAut ↥Bs) * s⁻¹, hmem σ⟩
      map_one' := by
        apply Φ.injective
        rw [MulEquiv.apply_symm_apply]
        exact Subtype.ext (by
          show s * (Φ 1 : MulAut ↥Bs) * s⁻¹ = ((Φ 1 : ↥AJ) : MulAut ↥Bs)
          rw [map_one]
          simp)
      map_mul' := by
        intro a b
        apply Φ.injective
        rw [MulEquiv.apply_symm_apply]
        conv_rhs => rw [map_mul]
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact Subtype.ext (by
          show s * (Φ (a * b) : MulAut ↥Bs) * s⁻¹ =
            (s * (Φ a : MulAut ↥Bs) * s⁻¹) * (s * (Φ b : MulAut ↥Bs) * s⁻¹)
          rw [map_mul]
          simp only [Subgroup.coe_mul]
          group) }
  have hπdef : ∀ σ, (Φ (π σ) : MulAut ↥Bs) = s * (Φ σ : MulAut ↥Bs) * s⁻¹ := by
    intro σ
    rw [show π σ = Φ.symm ⟨s * (Φ σ : MulAut ↥Bs) * s⁻¹, hmem σ⟩ from rfl]
    rw [MulEquiv.apply_symm_apply]
  have hπT : ∀ t ∈ ggTransp 6, π t ∈ ggTransp 6 := by
    intro t ht
    have hrefl : GGIsReflection 3 (s * (Φ t : MulAut ↥Bs) * s⁻¹) :=
      ggQ2d6l_isRefl_conj 3 s (Φ t) (hΦ1 t ht)
    have hrefl' : GGIsReflection 3 ((Φ (π t)) : MulAut ↥Bs) := by
      rw [hπdef t]; exact hrefl
    obtain ⟨t', ht', hEq⟩ := hΦ2 (Φ (π t)) (Φ (π t)).2 hrefl'
    have hEq' : π t = t' := Φ.injective (Subtype.ext hEq)
    rw [hEq']
    exact ht'
  have hinj : Set.InjOn π (ggTransp 6) := by
    intro a _ b _ hab
    apply Φ.injective
    have h1 : (Φ (π a) : MulAut ↥Bs) = (Φ (π b) : MulAut ↥Bs) := by rw [hab]
    rw [hπdef a, hπdef b] at h1
    apply Subtype.ext
    have h2 : (Φ a : MulAut ↥Bs) * s⁻¹ = (Φ b : MulAut ↥Bs) * s⁻¹ :=
      mul_left_cancel (by simpa only [mul_assoc] using h1)
    exact mul_right_cancel h2
  have hπ : ∀ a ∈ ggTransp 6, ∀ b ∈ ggTransp 6,
      π (a * b * a⁻¹) = π a * π b * (π a)⁻¹ := by
    intro a _ b _
    rw [map_mul, map_mul, map_inv]
  obtain ⟨g', hg'⟩ := ggQ2_quandle_aut_sym 6 (by norm_num) π hπT hinj hπ
  have hπeq : π = (MulAut.conj g').toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense ggQ2d6l_closure_transp_top (by
      intro t ht
      rw [hg' t ht]
      exact (MulAut.conj_apply g' t).symm)
  have hpoint : ∀ σ, π σ = g' * σ * g'⁻¹ := by
    intro σ
    have hcong := DFunLike.congr_fun hπeq σ
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcong
  refine ⟨(Φ g' : ↥AJ), (Φ g').2, ?_⟩
  intro r hr
  obtain ⟨σ, hσ⟩ : ∃ σ, (Φ σ : ↥AJ) = ⟨r, hr⟩ := ⟨Φ.symm ⟨r, hr⟩, by simp⟩
  have hσval : (Φ σ : MulAut ↥Bs) = r := congrArg Subtype.val hσ
  rw [← hσval]
  rw [← hπdef σ, hpoint σ]
  rw [map_mul, map_mul, map_inv]
  rfl

end CFSG.StandardType

end
