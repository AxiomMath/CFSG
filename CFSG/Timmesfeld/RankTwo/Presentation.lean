module

public import CFSG.LieType.Steinberg.G2.Perfect
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.CurtisTits.ExceptionalModel

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Steinberg CFSG.Blueprint CFSG.Assembly.LowTwoRank

universe u v w

section RankTwo

theorem presentationA_SL3 (F : Type) [Field F] :
    PresentationA.{0, 0, w}
      (Steinberg.RootSystem.ofCartan (Universal.SpecialLinear.rootDatum 2 F).isFiniteType
        (Universal.SpecialLinear.rootDatum 2 F).divisible)
      (Universal.SpecialLinear.rootDatum 2 F).rootGroup :=
  presentationA_of (Universal.SpecialLinear.isCTGroupDatum 2 F)
    (Universal.SpecialLinear.steinbergExtras 2 F)

theorem presentationA_G2 (F : Type) [Field F] :
    PresentationA.{0, 0, w}
      (Steinberg.RootSystem.ofCartan (Adjoint.g2Datum F).isFiniteType (Adjoint.g2Datum F).divisible)
      (Adjoint.g2Datum F).rootGroup :=
  presentationA_of (Adjoint.g2_isCTGroupDatum F) (Adjoint.g2_steinbergExtras F)

theorem presentationA_twistedD4 {F : Type} [Field F] (σ : F →+* F)
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    PresentationA.{0, 0, w}
      (Steinberg.RootSystem.ofCartan (TwistedD4.twistedDatum σ).isFiniteType
        (TwistedD4.twistedDatum σ).divisible)
      (TwistedD4.twistedDatum σ).rootGroup :=
  presentationA_of (TwistedD4.twistedDatum_isCTGroupDatum σ hσ)
    (TwistedD4.twistedDatum_steinbergExtras σ hσ)

end RankTwo

section Extends

variable {ι : Type u} {K : Type v} [Group K]

@[expose] def ExtendsToHom {G : Type*} [Group G] (X : (ι → ℤ) → Subgroup K)
    (Ψ : Set (ι → ℤ)) (φ : ∀ γ, X γ → G) : Prop :=
  ∃ (S : Subgroup K) (θ : S →* G), ∀ γ ∈ Ψ, ∀ x : X γ, ∃ hx : (x : K) ∈ S, θ ⟨x, hx⟩ = φ γ x

variable {X : (ι → ℤ) → Subgroup K} {G : Type*} [Group G] {Ψ : Set (ι → ℤ)}
  {φ : ∀ γ, X γ → G}

theorem ExtendsToHom.mono {Ψ' : Set (ι → ℤ)} (h : ExtendsToHom X Ψ φ) (hΨ : Ψ' ⊆ Ψ) :
    ExtendsToHom X Ψ' φ := by
  obtain ⟨S, θ, hθ⟩ := h
  exact ⟨S, θ, fun γ hγ => hθ γ (hΨ hγ)⟩

theorem ExtendsToHom.relationsHold (h : ExtendsToHom X Ψ φ) :
    CurtisTits.RelationsHold X Ψ φ := by
  obtain ⟨S, θ, hθ⟩ := h
  have key : ∀ l : List (Σ γ : ι → ℤ, X γ), (∀ p ∈ l, p.1 ∈ Ψ) →
      ∃ hl : (l.map fun p => (p.2 : K)).prod ∈ S,
        θ ⟨_, hl⟩ = (l.map fun p => φ p.1 p.2).prod := by
    intro l hl
    induction l with
    | nil => exact ⟨by simp [S.one_mem], θ.map_one⟩
    | cons p l ih =>
      obtain ⟨hp, hpθ⟩ := hθ p.1 (hl p (by simp)) p.2
      obtain ⟨hl', hlθ⟩ := ih fun q hq => hl q (by simp [hq])
      refine ⟨by simpa using S.mul_mem hp hl', ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [← hpθ, ← hlθ, ← map_mul]
      rfl
  intro l hl h1
  obtain ⟨hmem, heq⟩ := key l hl
  rw [← heq]
  have : (⟨_, hmem⟩ : S) = 1 := Subtype.ext h1
  rw [this, map_one]

end Extends

section Cones

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {K : Type v} [Group K]

structure ConeCompatible (Φ : Steinberg.RootSystem ι) (X : (ι → ℤ) → Subgroup K) {G : Type*}
    [Group G] (φ : ∀ γ, X γ → G) : Prop where
  cone : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, ¬ Steinberg.IsNegMultiple α β →
    ExtendsToHom X (Steinberg.cone Φ.roots α β) φ
  rankOne : ∀ i, ExtendsToHom X {Pi.single i 1, -Pi.single i 1} φ

variable {Φ : Steinberg.RootSystem ι} {X : (ι → ℤ) → Subgroup K} {G : Type*} [Group G]
  {φ : ∀ γ, X γ → G}

theorem ConeCompatible.lift_eq_one (h : ConeCompatible Φ X φ) :
    ∀ w ∈ rel1 Φ X ∪ rel2 Φ X, FreeGroup.lift (symbolMap Φ φ) w = 1 := by
  rintro w (⟨α, hα, β, hβ, hneg, hw, h1⟩ | ⟨i, hw, h1⟩)
  · exact (relationsHold_iff fun γ hγ => hγ.1).mp (h.cone α hα β hβ hneg).relationsHold w hw h1
  · refine (relationsHold_iff ?_).mp (h.rankOne i).relationsHold w hw h1
    rintro γ (rfl | rfl)
    exacts [Φ.single_mem i, Φ.neg_mem _ (Φ.single_mem i)]

theorem existsUnique_hom_of_coneCompatible (hP : PresentationA.{u, v, w} Φ X) {G : Type w}
    [Group G] {φ : ∀ γ, X γ → G} (h : ConeCompatible Φ X φ) :
    ∃! ψ : K →* G, ∀ γ ∈ Φ.roots, ∀ x : X γ, ψ x = φ γ x := by
  obtain ⟨ψ, hψ, huniq⟩ := hP.2.2 G (symbolMap Φ φ) h.lift_eq_one
  exact ⟨ψ, fun γ hγ x => hψ ⟨(γ, x), hγ, x.2⟩,
    fun ψ' hψ' => huniq ψ' fun s => hψ' s.1.1 s.2.1 ⟨s.1.2, s.2.2⟩⟩

theorem exists_surjective_of_coneCompatible (hP : PresentationA.{u, v, w} Φ X)
    (hK : IsQuasisimple K) {G : Type w} [Group G] {φ : ∀ γ, X γ → G} (h : ConeCompatible Φ X φ)
    (hgen : Subgroup.closure (⋃ γ ∈ Φ.roots, Set.range (φ γ)) = ⊤)
    (hnt : ∃ γ ∈ Φ.roots, ∃ x : X γ, φ γ x ≠ 1) :
    ∃ ψ : K →* G, (∀ γ ∈ Φ.roots, ∀ x : X γ, ψ x = φ γ x) ∧ Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple G ∧
      Subgroup.center G = (Subgroup.center K).map ψ ∧ Nonempty (K ⧸ ψ.ker ≃* G) ∧
      Nonempty (K ⧸ Subgroup.center K ≃* G ⧸ Subgroup.center G) := by
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_coneCompatible hP h
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_range] at hg
    obtain ⟨γ, hγ, x, rfl⟩ := hg
    exact ⟨x, hψ γ hγ x⟩
  have hnt' : ∃ k, ψ k ≠ 1 := by
    obtain ⟨γ, hγ, x, hx⟩ := hnt
    exact ⟨x, by rw [hψ γ hγ x]; exact hx⟩
  have hker := CurtisTits.ker_le_center_of_isQuasisimple hK hnt'
  exact ⟨ψ, hψ, hsurj, hker, CurtisTits.isQuasisimple_of_surjective hK hsurj hnt',
    CurtisTits.center_eq_map_center_of_isQuasisimple hK hsurj hker,
    ⟨QuotientGroup.quotientKerEquivOfSurjective ψ hsurj⟩,
    ⟨CurtisTits.centralQuotientEquivOfIsQuasisimple hK hsurj hker⟩⟩

end Cones

section Models

theorem lieModel_quotient_of_surjective {K G : Type} [Group K] [Group G] (hK : IsQuasisimple K)
    {t : StatedLieTag} {n p f : ℕ} (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f)
    {ψ : K →* G} (hsurj : Function.Surjective ψ) (hnt : ∃ k, ψ k ≠ 1) :
    LieModel (G ⧸ Subgroup.center G) t n p f :=
  CurtisTits.lieModel_of_mulEquiv (CurtisTits.centralQuotientEquivOfIsQuasisimple hK hsurj
    (CurtisTits.ker_le_center_of_isQuasisimple hK hnt)) hmodel

theorem lieModel_of_center_eq_bot {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (G ⧸ Subgroup.center G) t n p f) :
    LieModel G t n p f :=
  CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) h

theorem lieModel_SL3_quotient {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) :
    LieModel (Matrix.SpecialLinearGroup (Fin (2 + 1)) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (2 + 1)) F)) .PSL 3 p f :=
  Or.inl ⟨by simp [classicalTags], Universal.SpecialLinear.statedClassicalModel_center_quotient
    2 F ⟨hp, hf, by norm_num, by simp, by simp⟩ hF⟩

theorem lieModel_G2_quotient {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hq : 3 ≤ p ^ f) (hF : Nat.card F = p ^ f) :
    LieModel (AdjointQuotient .G2 F) .G2 0 p f :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, hf, rfl, hq⟩, F, inferInstance, inferInstance, hF,
    ⟨MulEquiv.refl _⟩⟩)

theorem lieModel_twistedD4_quotient {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hF : Nat.card F = (p ^ f) ^ 3) (σ : F →+* F) (hσ : ∀ c, σ c = c ^ p ^ f) :
    LieModel (TwistedD4.twistedGroup σ ⧸ Subgroup.center (TwistedD4.twistedGroup σ))
      .trialityD4 0 p f := by
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hK := TwistedD4.twistedGroup_isQuasisimple_of_card hq hF hσ
  have := TwistedD4.twistedGroup_nontrivial (TwistedD4.sigma_three_of_card hF hσ)
  obtain ⟨x, hx⟩ := exists_ne (1 : TwistedD4.twistedGroup σ)
  let e := TwistedD4.twistedGroupEquivDerived σ hq hF hσ
  refine Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, hf, rfl⟩, ?_⟩)
  exact CurtisTits.twistedChevalleyModel_of_surjective hK (t := .D4) hF σ hσ e.toMonoidHom
    e.surjective ⟨x, fun h => hx (e.injective (h.trans (map_one e).symm))⟩ (MulEquiv.refl _)

end Models

section Recognition

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {K : Type} [Group K]
  {Φ : Steinberg.RootSystem ι} {X : (ι → ℤ) → Subgroup K}

theorem exists_lieModel_of_coneCompatible (hP : PresentationA.{u, 0, 0} Φ X)
    (hK : IsQuasisimple K) {t : StatedLieTag} {n p f : ℕ}
    (hmodel : LieModel (K ⧸ Subgroup.center K) t n p f) {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) {φ : ∀ γ, X γ → G} (h : ConeCompatible Φ X φ)
    (hgen : Subgroup.closure (⋃ γ ∈ Φ.roots, Set.range (φ γ)) = ⊤)
    (hnt : ∃ γ ∈ Φ.roots, ∃ x : X γ, φ γ x ≠ 1) :
    ∃ ψ : K →* G, (∀ γ ∈ Φ.roots, ∀ x : X γ, ψ x = φ γ x) ∧ Function.Surjective ψ ∧
      ψ.ker = Subgroup.center K ∧ LieModel G t n p f := by
  obtain ⟨ψ, hψ, hsurj, hker, -, hZK, -, ⟨e⟩⟩ :=
    exists_surjective_of_coneCompatible hP hK h hgen hnt
  refine ⟨ψ, hψ, hsurj, le_antisymm hker fun z hz => ?_,
    lieModel_of_center_eq_bot hZ (CurtisTits.lieModel_of_mulEquiv e hmodel)⟩
  have : ψ z ∈ Subgroup.center G := hZK ▸ Subgroup.mem_map_of_mem ψ hz
  rw [hZ, Subgroup.mem_bot] at this
  exact this

end Recognition

section RankTwoRecognition

variable {F : Type} [Field F] [Finite F] {p f : ℕ} {G : Type} [Group G]

theorem exists_lieModel_of_coneCompatible_SL3 (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hZ : Subgroup.center G = ⊥)
    {φ : ∀ γ, (Universal.SpecialLinear.rootDatum 2 F).rootGroup γ → G}
    (h : ConeCompatible (Steinberg.RootSystem.ofCartan
      (Universal.SpecialLinear.rootDatum 2 F).isFiniteType
      (Universal.SpecialLinear.rootDatum 2 F).divisible)
      (Universal.SpecialLinear.rootDatum 2 F).rootGroup φ)
    (hgen : Subgroup.closure
      (⋃ γ ∈ (Universal.SpecialLinear.rootDatum 2 F).roots, Set.range (φ γ)) = ⊤)
    (hnt : ∃ γ ∈ (Universal.SpecialLinear.rootDatum 2 F).roots, ∃ x, φ γ x ≠ 1) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (2 + 1)) F →* G,
      (∀ γ ∈ (Universal.SpecialLinear.rootDatum 2 F).roots,
        ∀ x : (Universal.SpecialLinear.rootDatum 2 F).rootGroup γ, ψ x = φ γ x) ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center _ ∧ LieModel G .PSL 3 p f :=
  exists_lieModel_of_coneCompatible (presentationA_SL3 F)
    (Universal.SpecialLinear.isQuasisimple 2 F le_rfl) (lieModel_SL3_quotient hp hf hF) hZ h
    hgen hnt

theorem exists_lieModel_of_coneCompatible_G2 (hp : p.Prime) (hf : 1 ≤ f) (hq : 3 ≤ p ^ f)
    (hF : Nat.card F = p ^ f) (hZ : Subgroup.center G = ⊥)
    {φ : ∀ γ, (Adjoint.g2Datum F).rootGroup γ → G}
    (h : ConeCompatible (Steinberg.RootSystem.ofCartan (Adjoint.g2Datum F).isFiniteType
      (Adjoint.g2Datum F).divisible) (Adjoint.g2Datum F).rootGroup φ)
    (hgen : Subgroup.closure (⋃ γ ∈ (Adjoint.g2Datum F).roots, Set.range (φ γ)) = ⊤)
    (hnt : ∃ γ ∈ (Adjoint.g2Datum F).roots, ∃ x, φ γ x ≠ 1) :
    ∃ ψ : ↥(Chevalley.adjointGroup .G2 F) →* G,
      (∀ γ ∈ (Adjoint.g2Datum F).roots, ∀ x : (Adjoint.g2Datum F).rootGroup γ, ψ x = φ γ x) ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center _ ∧ LieModel G .G2 0 p f :=
  exists_lieModel_of_coneCompatible (presentationA_G2 F)
    (Adjoint.isQuasisimple_g2_of_three_le_card F (hF ▸ hq)) (lieModel_G2_quotient hp hf hq hF) hZ
    h hgen hnt

theorem exists_lieModel_of_coneCompatible_twistedD4 (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = (p ^ f) ^ 3) (σ : F →+* F) (hσ : ∀ c, σ c = c ^ p ^ f)
    (hZ : Subgroup.center G = ⊥) {φ : ∀ γ, (TwistedD4.twistedDatum σ).rootGroup γ → G}
    (h : ConeCompatible (Steinberg.RootSystem.ofCartan (TwistedD4.twistedDatum σ).isFiniteType
      (TwistedD4.twistedDatum σ).divisible) (TwistedD4.twistedDatum σ).rootGroup φ)
    (hgen : Subgroup.closure (⋃ γ ∈ (TwistedD4.twistedDatum σ).roots, Set.range (φ γ)) = ⊤)
    (hnt : ∃ γ ∈ (TwistedD4.twistedDatum σ).roots, ∃ x, φ γ x ≠ 1) :
    ∃ ψ : TwistedD4.twistedGroup σ →* G,
      (∀ γ ∈ (TwistedD4.twistedDatum σ).roots,
        ∀ x : (TwistedD4.twistedDatum σ).rootGroup γ, ψ x = φ γ x) ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center _ ∧ LieModel G .trialityD4 0 p f :=
  exists_lieModel_of_coneCompatible
    (presentationA_twistedD4 σ (TwistedD4.sigma_three_of_card hF hσ))
    (TwistedD4.twistedGroup_isQuasisimple_of_card
      (le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hF hσ)
    (lieModel_twistedD4_quotient hp hf hF σ hσ) hZ h hgen hnt

end RankTwoRecognition

section Pairs

variable {I : Type*} [DecidableEq I] {K : Type*} [Group K] {X : (I → ℤ) → Subgroup K}
  {G : Type*} [Group G]

theorem levi_hom_ext {J : Finset I} {θ θ' : CurtisTits.levi X J →* G}
    (h : ∀ j ∈ J, ∀ (x : K) (hx : x ∈ CurtisTits.levi X J), x ∈ CurtisTits.rankOne X j →
      θ ⟨x, hx⟩ = θ' ⟨x, hx⟩) : θ = θ' := by
  ext ⟨y, hy⟩
  have hle : CurtisTits.levi X J ≤ (MonoidHom.eqLocus θ θ').map (CurtisTits.levi X J).subtype := by
    refine iSup₂_le fun j hj x hx => ?_
    have hxJ : x ∈ CurtisTits.levi X J := CurtisTits.rankOne_le_levi X hj hx
    exact ⟨⟨x, hxJ⟩, h j hj x hxJ hx, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hle hy
  obtain rfl : z = ⟨y, hy⟩ := Subtype.ext hzy
  exact hz

@[expose] def PairCompatible (φ₁ : ∀ i, CurtisTits.rankOne X i →* G)
    (φ₂ : ∀ i j : I, CurtisTits.levi X {i, j} →* G) : Prop :=
  ∀ i j k, k = i ∨ k = j → ∀ (x : K) (hx : x ∈ CurtisTits.rankOne X k)
    (hx' : x ∈ CurtisTits.levi X {i, j}), φ₂ i j ⟨x, hx'⟩ = φ₁ k ⟨x, hx⟩

theorem exists_eq_pair_of_card_le_two {J : Finset I} (hJ : J.card ≤ 2) (hne : J.Nonempty) :
    ∃ i j, J = {i, j} := by
  rcases Nat.lt_or_ge J.card 2 with h1 | h1
  · have h1' : J.card = 1 := by have := hne.card_pos; omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1'
    exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (le_antisymm hJ h1)
    exact ⟨a, b, rfl⟩

open Classical in
noncomputable def pairFamily (φ₂ : ∀ i j : I, CurtisTits.levi X {i, j} →* G)
    (J : {J : Finset I // J.card ≤ 2}) : CurtisTits.leviAmalgam X J →* G :=
  if h : ∃ i j, J.1 = {i, j} then
    (φ₂ h.choose h.choose_spec.choose).comp
      (Subgroup.inclusion (CurtisTits.levi_mono X h.choose_spec.choose_spec.le))
  else 1

variable {φ₁ : ∀ i, CurtisTits.rankOne X i →* G} {φ₂ : ∀ i j : I, CurtisTits.levi X {i, j} →* G}

theorem PairCompatible.apply_eq (h : PairCompatible φ₁ φ₂) {i j k l : I}
    (hsub : ({i, j} : Finset I) ⊆ {k, l}) (x : K) (hx : x ∈ CurtisTits.levi X {i, j})
    (hx' : x ∈ CurtisTits.levi X {k, l}) : φ₂ i j ⟨x, hx⟩ = φ₂ k l ⟨x, hx'⟩ := by
  have key : φ₂ i j = (φ₂ k l).comp (Subgroup.inclusion (CurtisTits.levi_mono X hsub)) := by
    refine levi_hom_ext fun m hm y hy hym => ?_
    have hmkl : m = k ∨ m = l := by simpa using hsub hm
    rw [h i j m (by simpa using hm) y hym hy, MonoidHom.comp_apply]
    exact (h k l m hmkl y hym _).symm
  rw [key]
  rfl

theorem PairCompatible.pairFamily_apply (h : PairCompatible φ₁ φ₂) (i j : I)
    (hJ : ({i, j} : Finset I).card ≤ 2) (x : K) (hx : x ∈ CurtisTits.levi X {i, j}) :
    pairFamily φ₂ ⟨{i, j}, hJ⟩ ⟨x, hx⟩ = φ₂ i j ⟨x, hx⟩ := by
  have hex : ∃ a b, ({i, j} : Finset I) = {a, b} := ⟨i, j, rfl⟩
  rw [pairFamily, dite_eq_left hex, MonoidHom.comp_apply]
  exact (h.apply_eq (hex.choose_spec.choose_spec ▸ subset_refl _) x hx _).symm

theorem PairCompatible.pairFamily_singleton (h : PairCompatible φ₁ φ₂) (k : I)
    (hJ : ({k} : Finset I).card ≤ 2) (x : K) (hx : x ∈ CurtisTits.levi X {k})
    (hx' : x ∈ CurtisTits.rankOne X k) : pairFamily φ₂ ⟨{k}, hJ⟩ ⟨x, hx⟩ = φ₁ k ⟨x, hx'⟩ := by
  have hex : ∃ a b, ({k} : Finset I) = {a, b} := ⟨k, k, by simp⟩
  rw [pairFamily, dite_eq_left hex, MonoidHom.comp_apply]
  have hk : k = hex.choose ∨ k = hex.choose_spec.choose := by
    have := hex.choose_spec.choose_spec ▸ Finset.mem_singleton_self k
    simpa using this
  exact h _ _ k hk x hx' _

theorem PairCompatible.isCompatible (h : PairCompatible φ₁ φ₂) :
    CurtisTits.IsCompatible (CurtisTits.leviAmalgam X) (pairFamily φ₂) := by
  intro A B hAB x y hxy
  by_cases hA : A.1.Nonempty
  · obtain ⟨i, j, hij⟩ := exists_eq_pair_of_card_le_two A.2 hA
    obtain ⟨k, l, hkl⟩ := exists_eq_pair_of_card_le_two B.2 (hA.mono hAB)
    obtain ⟨A, hA2⟩ := A
    obtain ⟨B, hB2⟩ := B
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only at hij hkl hxy
    subst hij hkl hxy
    rw [h.pairFamily_apply i j hA2 x hx, h.pairFamily_apply k l hB2 x hy]
    exact h.apply_eq hAB x hx hy
  · obtain ⟨x, hx⟩ := x
    have hA0 : A.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hx1 : x = 1 := by
      have : CurtisTits.levi X A.1 = ⊥ := by simp [hA0, CurtisTits.levi]
      change x ∈ CurtisTits.levi X A.1 at hx
      rw [this] at hx
      exact hx
    have hy1 : y = 1 := Subtype.ext (by simp only at hxy; rw [← hxy, hx1]; rfl)
    have hx1' : (⟨x, hx⟩ : CurtisTits.leviAmalgam X A) = 1 := Subtype.ext hx1
    rw [hx1', hy1, map_one, map_one]

end Pairs

section CurtisTits

variable {K : Type} [Group K] {D : Universal.UniversalRootDatum K} {t : StatedLieTag}
  {n p f : ℕ}

theorem lieModel_of_curtisTitsConclusion (hCT : CurtisTits.CurtisTitsConclusion.{w} D t n p f)
    {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) (φ : ∀ J, D.leviAmalgam J →* G)
    (hφ : CurtisTits.IsCompatible D.leviAmalgam φ) (hgen : ⨆ J, (φ J).range = ⊤)
    (hnt : ∃ J, ∃ x, φ J x ≠ 1) :
    ∃ ψ : K →* G, (∀ J (x : D.leviAmalgam J), ψ x = φ J x) ∧ Function.Surjective ψ ∧
      ψ.ker = Subgroup.center K ∧ LieModel G t n p f := by
  obtain ⟨ψ, hψ, hsurj, hker, -, hZK, -, hmodel⟩ := hCT.2.2.1 G φ hφ hgen hnt
  refine ⟨ψ, hψ, hsurj, le_antisymm hker fun z hz => ?_, lieModel_of_center_eq_bot hZ hmodel⟩
  have : ψ z ∈ Subgroup.center G := hZK ▸ Subgroup.mem_map_of_mem ψ hz
  rw [hZ, Subgroup.mem_bot] at this
  exact this

theorem lieModel_of_curtisTitsConclusion_of_pairs
    (hCT : CurtisTits.CurtisTitsConclusion.{w} D t n p f) {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) {φ₁ : ∀ i, CurtisTits.rankOne D.rootGroup i →* G}
    {φ₂ : ∀ i j, CurtisTits.levi D.rootGroup {i, j} →* G} (h : PairCompatible φ₁ φ₂)
    (hgen : ⨆ i, (φ₁ i).range = ⊤) (hnt : ∃ i, ∃ x, φ₁ i x ≠ 1) :
    ∃ ψ : K →* G, (∀ i j (x : CurtisTits.levi D.rootGroup {i, j}), ψ x = φ₂ i j x) ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center K ∧ LieModel G t n p f := by
  have hsingle : ∀ k, ({k} : Finset (Fin D.rank)).card ≤ 2 := fun k => by simp
  have hmem : ∀ k, ∀ x ∈ CurtisTits.rankOne D.rootGroup k, x ∈ CurtisTits.levi D.rootGroup {k} :=
    fun k x hx => by rw [CurtisTits.levi_singleton]; exact hx
  have hrank : ∀ k (x : CurtisTits.rankOne D.rootGroup k),
      pairFamily φ₂ ⟨{k}, hsingle k⟩ ⟨x.1, hmem k x.1 x.2⟩ = φ₁ k x :=
    fun k x => h.pairFamily_singleton k (hsingle k) x.1 (hmem k x.1 x.2) x.2
  have hgen' : ⨆ J, (pairFamily φ₂ J).range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨{k}, hsingle k⟩ : {J : Finset (Fin D.rank) // J.card ≤ 2})
      ⟨_, hrank k x⟩
  have hnt' : ∃ J, ∃ x, pairFamily φ₂ J x ≠ 1 := by
    obtain ⟨k, x, hx⟩ := hnt
    exact ⟨⟨{k}, hsingle k⟩, _, (hrank k x).trans_ne hx⟩
  obtain ⟨ψ, hψ, hsurj, hker, hmodel⟩ :=
    lieModel_of_curtisTitsConclusion hCT hZ (pairFamily φ₂) h.isCompatible hgen' hnt'
  refine ⟨ψ, fun i j x => ?_, hsurj, hker, hmodel⟩
  have hJ : ({i, j} : Finset (Fin D.rank)).card ≤ 2 := Finset.card_le_two
  exact (hψ ⟨{i, j}, hJ⟩ x).trans (h.pairFamily_apply i j hJ x.1 x.2)

theorem exists_surjective_of_curtisTitsConclusion
    (hCT : CurtisTits.CurtisTitsConclusion.{w} D t n p f) {G : Type} [Group G]
    (M : {J : Finset (Fin D.rank) // J.card ≤ 2} → Subgroup G) (hMgen : ⨆ J, M J = ⊤)
    (ψ : ∀ J, D.leviAmalgam J →* M J) (hψ : ∀ J, Function.Surjective (ψ J))
    (hcomp : ∀ I J, I ≤ J → ∀ (x : D.leviAmalgam I) (y : D.leviAmalgam J), (x : K) = y →
      (ψ I x : G) = ψ J y)
    (hnt : ∃ J, M J ≠ ⊥) :
    ∃ θ : K →* G, (∀ J (x : D.leviAmalgam J), θ x = ψ J x) ∧ Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center K ∧ IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) t n p f := by
  let φ : ∀ J, D.leviAmalgam J →* G := fun J => (M J).subtype.comp (ψ J)
  have hrange : ∀ J, (φ J).range = M J := by
    intro J
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (ψ J x).2
    · intro hg
      obtain ⟨x, hx⟩ := hψ J ⟨g, hg⟩
      exact ⟨x, by simp [φ, hx]⟩
  have hnt' : ∃ J, ∃ x, φ J x ≠ 1 := by
    obtain ⟨J, hJ⟩ := hnt
    obtain ⟨g, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ
    obtain ⟨x, hx⟩ := hψ J g
    refine ⟨J, x, fun h => hg1 (Subtype.ext ?_)⟩
    rw [← hx]
    exact h
  obtain ⟨θ, hθ, hsurj, hker, hGq, -, -, hmodel⟩ :=
    hCT.2.2.1 G φ (fun I J hIJ x y hxy => hcomp I J hIJ x y hxy)
      (by simpa only [hrange] using hMgen) hnt'
  exact ⟨θ, hθ, hsurj, hker, hGq, hmodel⟩

end CurtisTits

end CFSG.Timmesfeld
