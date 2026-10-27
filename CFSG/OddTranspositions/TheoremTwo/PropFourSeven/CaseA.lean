module

public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.Labelling
public import CFSG.OddTranspositions.O4FibresMOrbit
public import CFSG.OddTranspositions.FiveThreeQZ

public section

namespace CFSG.OddTranspositions.PropFourSeven

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ CFSG.GroupTheory Equiv

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

omit [Finite G] in
theorem image_conj_eq_of_forall {k : G} {S : Set G} (h₁ : ∀ t ∈ S, k * t * k⁻¹ ∈ S)
    (h₂ : ∀ t ∈ S, k⁻¹ * t * k ∈ S) : (fun y => k * y * k⁻¹) '' S = S := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact h₁ t ht
  · intro hy
    exact ⟨k⁻¹ * y * k, h₂ y hy, by group⟩

omit [Finite G] in
theorem image_conj_eq_of_commute {k : G} {S : Set G} (h : ∀ t ∈ S, Commute k t) :
    (fun y => k * y * k⁻¹) '' S = S :=
  image_conj_eq_of_forall (fun t ht => by rw [(h t ht).eq, mul_inv_cancel_right]; exact ht)
    (fun t ht => by rw [(h t ht).inv_left.eq, inv_mul_cancel_right]; exact ht)

omit [Finite G] in
theorem image_conj_eq_of_mem_normalizer {k : G} {S : Set G}
    (hk : k ∈ Subgroup.normalizer S) : (fun y => k * y * k⁻¹) '' S = S :=
  image_conj_eq_of_forall (fun t ht => (Subgroup.mem_set_normalizer_iff.mp hk t).mp ht)
    (fun t ht => by
      have := (Subgroup.mem_set_normalizer_iff.mp (Subgroup.inv_mem _ hk) t).mp ht
      rwa [inv_inv] at this)

omit [Finite G] in
theorem image_conj_conj (k y : G) (S : Set G) :
    (fun t => k * y * k⁻¹ * t * (k * y * k⁻¹)⁻¹) '' S =
      (fun t => k * t * k⁻¹) '' ((fun t => y * t * y⁻¹) '' ((fun t => k⁻¹ * t * k⁻¹⁻¹) '' S)) := by
  simp only [Set.image_image]
  congr 1
  funext t
  group

theorem fixesPerpBlocks_conj (hN : IsNormalSet D) {y : G} {β : Set G}
    (h : FixesPerpBlocks D y β) (k : G) :
    FixesPerpBlocks D (k * y * k⁻¹) ((fun t => k * t * k⁻¹) '' β) := by
  intro γ hγ
  have hγ' : (fun t => k⁻¹ * t * k⁻¹⁻¹) '' γ ∈ perp D β := by
    have := perp.conj hN hγ k⁻¹
    rwa [image_conj_inv_image_conj] at this
  rw [image_conj_conj, h _ hγ', image_conj_image_conj_inv]

theorem exists_radical_conj_of_label_eq (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hε : ε '' imageClass hC = transpositions) {p q : G}
    (hp : p ∈ DalphaStar D hC.alpha) (hq : q ∈ DalphaStar D hC.alpha)
    (hpq : labelOf ε p = labelOf ε q) :
    ∃ m ∈ CFSG.solvableRadical (Halpha D hC.alpha), q = (m : G) * p * (m : G)⁻¹ := by
  have hpH : p ∈ Halpha D hC.alpha := Subgroup.subset_closure hp
  have hqH : q ∈ Halpha D hC.alpha := Subgroup.subset_closure hq
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨p, hpH⟩ =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨q, hqH⟩ := by
    apply ε.injective
    simpa [labelOf, piG_mem hpH, piG_mem hqH] using hpq
  obtain ⟨m, hm, hmq⟩ := (mk_eq_iff_m_conj_of_config hC hQ hε
    (d := ⟨⟨p, hpH⟩, hp⟩) (d' := ⟨⟨q, hqH⟩, hq⟩)).mp hmk
  exact ⟨m, hm, by simpa using (congrArg Subtype.val hmq).symm⟩

theorem mem_of_radical_conj (hC : HypothesisC D)
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ)
    {θ : Set G} (hθ : θ ∈ Dalpha D hC.alpha) {p : G} (hp : p ∈ θ) {m : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    (m : G) * p * (m : G)⁻¹ ∈ θ := by
  have hpS := subset_DalphaStar hθ hp
  have hpH : p ∈ Halpha D hC.alpha := Subgroup.subset_closure hpS
  refine hA θ hθ p hp _
    ((Subgroup.mem_set_normalizer_iff.mp (Halpha_le_normalizer hC.setup.normal m.2) p).mp hpS) ?_
  have h1 : labelOf ε (m : G) = 1 := by
    simp [labelOf, piG_coe, (QuotientGroup.eq_one_iff m).mpr hm]
  simp only [labelOf] at h1 ⊢
  rw [piG_conj m.2 hpH, h1, one_mul, inv_one, mul_one]

theorem mem_block_iff_radical_conj (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hε : ε '' imageClass hC = transpositions)
    (hblock : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ θ, labelOf ε x = labelOf ε y)
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ)
    {θ : Set G} (hθ : θ ∈ Dalpha D hC.alpha) {p : G} (hp : p ∈ θ) (y : G) :
    y ∈ θ ↔ ∃ m ∈ CFSG.solvableRadical (Halpha D hC.alpha), y = (m : G) * p * (m : G)⁻¹ := by
  constructor
  · intro hy
    exact exists_radical_conj_of_label_eq hC hQ hε (subset_DalphaStar hθ hp)
      (subset_DalphaStar hθ hy) (hblock θ hθ p hp y hy)
  · rintro ⟨m, hm, rfl⟩
    exact mem_of_radical_conj hC hA hθ hp hm

theorem image_conj_radical (hC : HypothesisC D)
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ)
    {θ : Set G} (hθ : θ ∈ Dalpha D hC.alpha) {m : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    (fun y => (m : G) * y * (m : G)⁻¹) '' θ = θ :=
  image_conj_eq_of_forall (fun _ ht => mem_of_radical_conj hC hA hθ ht hm)
    (fun _ ht => by simpa using mem_of_radical_conj hC hA hθ ht (Subgroup.inv_mem _ hm))

theorem fixesPerpBlocks_alpha (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hε : ε '' imageClass hC = transpositions)
    (hblock : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ θ, labelOf ε x = labelOf ε y)
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {p q : G} (hp : p ∈ β) (hq : q ∈ β) :
    FixesPerpBlocks D (p * q) hC.alpha := by
  intro γ hγ
  rcases mem_perp_iff.mp hγ with hγ | rfl
  · obtain ⟨m, hm, rfl⟩ := exists_radical_conj_of_label_eq hC hQ hε (subset_DalphaStar hβ hp)
      (subset_DalphaStar hβ hq) (hblock β hβ p hp q hq)
    have hpH : p ∈ Halpha D hC.alpha := Subgroup.subset_closure (subset_DalphaStar hβ hp)
    have hpp : p⁻¹ = p := hC.setup.oddT.inv_eq (hβ.2.1 hp)
    have hn : (⟨p, hpH⟩ * m * ⟨p, hpH⟩⁻¹ * m⁻¹ : Halpha D hC.alpha) ∈
        CFSG.solvableRadical (Halpha D hC.alpha) :=
      Subgroup.mul_mem _ (Subgroup.Normal.conj_mem inferInstance m hm _) (Subgroup.inv_mem _ hm)
    have heq : ((⟨p, hpH⟩ * m * ⟨p, hpH⟩⁻¹ * m⁻¹ : Halpha D hC.alpha) : G) =
        p * ((m : G) * p * (m : G)⁻¹) := by
      simp [hpp, mul_assoc]
    rw [← heq]
    exact image_conj_radical hC hA hγ hn
  · exact image_conj_eq_of_commute fun t ht =>
      (hβ.2.2.2 t ht p hp).symm.mul_left (hβ.2.2.2 t ht q hq).symm

theorem fixesPerpBlocks_block (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5)}
    (hε : ε '' imageClass hC = transpositions)
    (hblock : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ θ, labelOf ε x = labelOf ε y)
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ)
    {θ : Set G} (hθ : θ ∈ Dalpha D hC.alpha) {g : G}
    (hg : (hC.conj g).alpha = θ) {p q : G} (hp : p ∈ θ) (hq : q ∈ θ) :
    ∀ γ ∈ perp D θ, FixesPerpBlocks D (p * q) γ := by
  have hN := hC.setup.normal
  have hθb : IsBlock D θ := isBlock_of_mem_blockClass hN hC.isBlock_alpha hθ.1
  intro γ hγ
  rcases mem_perp_iff.mp hγ with hγ | rfl
  · have htrans := (hC.conj g).normalizer_transitive
    rw [hg] at htrans
    obtain ⟨k, hk, hkγ⟩ := htrans _ (Dalpha_symm hθ hC.isBlock_alpha.1) _ hγ
    have hk' : k⁻¹ ∈ Subgroup.normalizer θ := Subgroup.inv_mem _ hk
    have hp' := (Subgroup.mem_set_normalizer_iff.mp hk' p).mp hp
    have hq' := (Subgroup.mem_set_normalizer_iff.mp hk' q).mp hq
    have h2 := fixesPerpBlocks_conj hN (fixesPerpBlocks_alpha hC hQ hε hblock hA hθ hp' hq') k
    rw [hkγ] at h2
    have hpq : p * q = k * (k⁻¹ * p * k⁻¹⁻¹ * (k⁻¹ * q * k⁻¹⁻¹)) * k⁻¹ := by group
    rw [hpq]
    exact h2
  · intro δ hδ
    rcases mem_perp_iff.mp hδ with hδ | rfl
    · exact image_conj_eq_of_commute fun t ht =>
        (hδ.2.2.2 p hp t ht).mul_left (hδ.2.2.2 q hq t ht)
    · exact image_conj_eq_of_mem_normalizer (Subgroup.mul_mem _
        (mem_normalizer_of_mem_block hθb hp) (mem_normalizer_of_mem_block hθb hq))

theorem caseA_singleton (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S')
    (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* Perm (Fin 5))
    (hε : ε '' imageClass hC = transpositions)
    (hblock : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ θ, labelOf ε x = labelOf ε y)
    (hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ) :
    ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ θ, x = y := by
  intro θ hθ p hp q hq
  have hN := hC.setup.normal
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hθ.1
  have hcα : (hC.conj g).alpha = θ := (HypothesisC.conj_alpha hC g).trans hg.symm
  have hS := isS5Model_of_quotient (CFSG.solvableRadical (Halpha D hC.alpha)) ε
    (fun _ hθ' _ hp' y => mem_block_iff_radical_conj hC hQ hε hblock hA hθ' hp' y)
  have hpet : PetersenAt D hC.alpha := petersenAt_of_S5 hC hS
  have hpet' : ∀ δ ∈ blockClass (hC.conj g).alpha, PetersenAt D δ := by
    intro δ hδ
    rw [hcα] at hδ
    obtain ⟨h, rfl⟩ := mem_blockClass_iff.mp (mem_blockClass_trans hθ.1 hδ)
    exact hpet.conj hN h
  have hbase : ∀ β ∈ perp D (hC.conj g).alpha, FixesPerpBlocks D (p * q) β := by
    rw [hcα]
    exact fixesPerpBlocks_block hC hQ hε hblock hA hθ hcα hp hq
  have h1 : p * q = 1 := faithfulOnBlocks_of_localSecond (hC.conj g) hQ.rad hQ.local2 _
    (sixTen_of_petersen (hC.conj g) hpet' hbase)
  rw [eq_inv_of_mul_eq_one_right h1, hC.setup.oddT.inv_eq (hθ.2.1 hp)]

end CFSG.OddTranspositions.PropFourSeven

