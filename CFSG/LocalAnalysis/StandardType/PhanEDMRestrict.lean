module

public import CFSG.LocalAnalysis.StandardType.PhanEDMRel

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C K : Type*}

@[expose] def restrictBy (X : ChamberSystem I C) (e : K → I) (A : Set C) : ChamberSystem K A where
  adj k a b := X.adj (e k) a b
  equivalence k := (X.equivalence (e k)).comap (fun a : A => (a : C))

@[expose] def coeGallery (e : K → I) (A : Set C) (γ : List (K × A)) : List (I × C) :=
  γ.map fun p => (e p.1, (p.2 : C))

variable (X : ChamberSystem I C) {e : K → I} {A : Set C}

theorem restrictBy_adj (k : K) (a b : A) :
    (restrictBy X e A).adj k a b ↔ X.adj (e k) a b := Iff.rfl

theorem coeGallery_nil : coeGallery e A ([] : List (K × A)) = [] := rfl

theorem coeGallery_cons (p : K × A) (γ : List (K × A)) :
    coeGallery e A (p :: γ) = (e p.1, (p.2 : C)) :: coeGallery e A γ := rfl

theorem coeGallery_append (γ η : List (K × A)) :
    coeGallery e A (γ ++ η) = coeGallery e A γ ++ coeGallery e A η := by
  simp only [coeGallery, List.map_append]

theorem coeGallery_injective (he : Function.Injective e) :
    Function.Injective (coeGallery (K := K) e A) := by
  have hf : Function.Injective (fun p : K × A => (e p.1, (p.2 : C))) := by
    intro p q h
    exact Prod.ext (he (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  change Function.Injective (List.map fun p : K × A => (e p.1, (p.2 : C)))
  exact List.map_injective_iff.mpr hf

theorem galleryEnd_coeGallery (a : A) (γ : List (K × A)) :
    galleryEnd (a : C) (coeGallery e A γ) = ((galleryEnd a γ : A) : C) := by
  induction γ generalizing a with
  | nil => rfl
  | cons p γ ih =>
    simp only [coeGallery_cons, galleryEnd_cons]
    exact ih p.2

theorem galleryIn_coeGallery {a : A} {γ : List (K × A)}
    (h : (restrictBy X e A).IsGallery a γ) :
    GalleryIn X (Set.range e) A a (coeGallery e A γ) := by
  induction γ generalizing a with
  | nil => exact ⟨a.2, trivial, by simp [coeGallery]⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := h
    have ih' := ih h2
    refine ⟨a.2, ?_, ?_⟩
    · rw [coeGallery_cons, isGallery_cons]
      exact ⟨(restrictBy_adj X p.1 a p.2).mp h1, ih'.2.1⟩
    · intro q hq
      rw [coeGallery_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨⟨p.1, rfl⟩, p.2.2⟩
      · exact ih'.2.2 q hq

theorem exists_coeGallery (he : Function.Injective e) {a : A} {γ' : List (I × C)}
    (h : GalleryIn X (Set.range e) A a γ') :
    ∃ γ : List (K × A), coeGallery e A γ = γ' ∧ (restrictBy X e A).IsGallery a γ := by
  induction γ' generalizing a with
  | nil => exact ⟨[], rfl, trivial⟩
  | cons p γ'' ih =>
    obtain ⟨ha, hgal, hmem⟩ := h
    obtain ⟨hpJ, hpA⟩ := hmem p (by simp)
    obtain ⟨k, hk⟩ := hpJ
    obtain ⟨hadj, hgal'⟩ := hgal
    let b : A := ⟨p.2, hpA⟩
    have hmem' : ∀ q ∈ γ'', q.1 ∈ Set.range e ∧ q.2 ∈ A :=
      fun q hq => hmem q (List.mem_cons_of_mem p hq)
    have hgal'' : GalleryIn X (Set.range e) A b γ'' := ⟨hpA, hgal', hmem'⟩
    obtain ⟨γ, hγcoe, hγgal⟩ := ih hgal''
    refine ⟨(k, b) :: γ, ?_, ?_⟩
    · rw [coeGallery_cons, hγcoe]
      exact congrArg (fun q => q :: γ'') (Prod.ext hk rfl)
    · rw [isGallery_cons]
      exact ⟨by rw [restrictBy_adj, hk]; exact hadj, hγgal⟩

private theorem q2cDMr_isGallery_iff (a : A) (γ : List (K × A)) :
    (restrictBy X e A).IsGallery a γ ↔ X.IsGallery (a : C) (coeGallery e A γ) := by
  induction γ generalizing a with
  | nil => exact Iff.rfl
  | cons p γ ih =>
    simp only [coeGallery_cons, isGallery_cons, restrictBy_adj, ih p.2]

private theorem q2cDMr_isGallery_of_coe (he : Function.Injective e) {a : A} {γ : List (I × C)}
    (h : GalleryIn X (Set.range e) A (a : C) γ) {ũ : List (K × A)}
    (hũ : coeGallery e A ũ = γ) : (restrictBy X e A).IsGallery a ũ := by
  obtain ⟨w, hw, hwgal⟩ := exists_coeGallery X he h
  rw [← hũ] at hw
  rw [coeGallery_injective he hw] at hwgal
  exact hwgal

private theorem q2cDMr_isGallery_of_homIn (he : Function.Injective e) {a : A}
    {u v : List (I × C)} (h : HomIn X (Set.range e) A 2 (a : C) u v)
    {ũ : List (K × A)} (hũ : coeGallery e A ũ = u)
    (hgal : (restrictBy X e A).IsGallery a ũ) {w : List (K × A)}
    (hw : coeGallery e A w = v) : (restrictBy X e A).IsGallery a w := by
  have hg : GalleryIn X (Set.range e) A (a : C) u := by
    rw [← hũ]
    exact galleryIn_coeGallery X hgal
  exact q2cDMr_isGallery_of_coe X he ((HomIn.galleryIn_iff h).mp hg) hw

private theorem q2cDMr_types_mem_image {η : List (K × A)} {J : Set K}
    (h : ∀ i ∈ galleryType η, i ∈ J) :
    ∀ p ∈ coeGallery e A η, p.1 ∈ e '' J := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (by simpa only [coeGallery] using hp)
  exact ⟨q.1, h q.1 (by rw [galleryType]; exact List.mem_map.mpr ⟨q, hq, rfl⟩), rfl⟩

private theorem q2cDMr_coe_eq_append_iff {l : List (K × A)} {s₁ s₂ : List (I × C)} :
    coeGallery e A l = s₁ ++ s₂ ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ coeGallery e A l₁ = s₁ ∧ coeGallery e A l₂ = s₂ := by
  constructor
  · intro h
    obtain ⟨l₁, l₂, hl, h1, h2⟩ := List.map_eq_append_iff.mp
      (show List.map (fun p : K × A => (e p.1, (p.2 : C))) l = s₁ ++ s₂ from h)
    exact ⟨l₁, l₂, hl, h1, h2⟩
  · rintro ⟨l₁, l₂, hl, h1, h2⟩
    subst hl
    rw [coeGallery_append, h1, h2]

private theorem q2cDMr_elemMove_coe (he : Function.Injective e) {a : A}
    {γ γ' : List (K × A)} (hγ : (restrictBy X e A).IsGallery a γ)
    (h : (restrictBy X e A).ElemMove a γ γ') :
    HomIn X (Set.range e) A 2 (a : C) (coeGallery e A γ) (coeGallery e A γ') := by
  cases h with
  | mk γ₁ η η' γ₂ J hJ hη hη' hηJ hη'J hend =>
    have hγ₁η : (restrictBy X e A).IsGallery a (γ₁ ++ η) :=
      ((isGallery_append a (γ₁ ++ η) γ₂).mp hγ).1
    have hγ₁ : (restrictBy X e A).IsGallery a γ₁ := ((isGallery_append a γ₁ η).mp hγ₁η).1
    have hγ₂ : (restrictBy X e A).IsGallery (galleryEnd (galleryEnd a γ₁) η') γ₂ := by
      have h2 : (restrictBy X e A).IsGallery (galleryEnd a (γ₁ ++ η)) γ₂ :=
        ((isGallery_append a (γ₁ ++ η) γ₂).mp hγ).2
      rw [galleryEnd_append, hend] at h2
      exact h2
    have hγ' : (restrictBy X e A).IsGallery a (γ₁ ++ η' ++ γ₂) := by
      rw [isGallery_append, isGallery_append, galleryEnd_append]
      exact ⟨⟨hγ₁, hη'⟩, hγ₂⟩
    have hE : ElemIn X (Set.range e) A 2 (a : C)
        (coeGallery e A γ₁ ++ coeGallery e A η ++ coeGallery e A γ₂)
        (coeGallery e A γ₁ ++ coeGallery e A η' ++ coeGallery e A γ₂) :=
      ElemIn.mk (coeGallery e A γ₁) (coeGallery e A η) (coeGallery e A η')
        (coeGallery e A γ₂) (e '' J) ((Set.encard_image_le e J).trans hJ)
        (by simpa only [coeGallery_append] using galleryIn_coeGallery X hγ)
        (by simpa only [coeGallery_append] using galleryIn_coeGallery X hγ')
        (q2cDMr_types_mem_image hηJ) (q2cDMr_types_mem_image hη'J)
        (by
          rw [galleryEnd_coeGallery (a := a) (γ := γ₁),
            galleryEnd_coeGallery (a := galleryEnd a γ₁) (γ := η),
            galleryEnd_coeGallery (a := galleryEnd a γ₁) (γ := η'), hend])
    simpa only [coeGallery_append] using HomIn.of_elemIn hE

private theorem q2cDMr_elemIn_coe (he : Function.Injective e) {a : A}
    {u v : List (I × C)} (hE : ElemIn X (Set.range e) A 2 (a : C) u v)
    {ũ : List (K × A)} (hũ : coeGallery e A ũ = u)
    {w : List (K × A)} (hw : coeGallery e A w = v) :
    (restrictBy X e A).TwoHomotopic a ũ w := by
  cases hE with
  | mk γ₁ η η' γ₂ K hK hγ hγ' hηK hη'K hend =>
    obtain ⟨ũ₁, ũrest, hũsplit, hcoe1, hcoerest⟩ :=
      q2cDMr_coe_eq_append_iff.mp (show coeGallery e A ũ = γ₁ ++ (η ++ γ₂) from by
        rw [hũ, List.append_assoc])
    obtain ⟨ũη, ũ₂, hurest, hcoeη, hcoe2⟩ := q2cDMr_coe_eq_append_iff.mp hcoerest
    obtain ⟨w₁, wrest, hwsplit, hcoe1', hcoerest'⟩ :=
      q2cDMr_coe_eq_append_iff.mp (show coeGallery e A w = γ₁ ++ (η' ++ γ₂) from by
        rw [hw, List.append_assoc])
    obtain ⟨wη', w₂, hwrest, hcoeη', hcoe2'⟩ := q2cDMr_coe_eq_append_iff.mp hcoerest'
    have h₁eq : ũ₁ = w₁ := by
      apply coeGallery_injective he
      rw [hcoe1, hcoe1']
    have h₂eq : ũ₂ = w₂ := by
      apply coeGallery_injective he
      rw [hcoe2, hcoe2']
    have hη : X.IsGallery (galleryEnd (a : C) γ₁) η :=
      (hγ.2.1.of_append_left).of_append_right
    have hη' : X.IsGallery (galleryEnd (a : C) γ₁) η' :=
      (hγ'.2.1.of_append_left).of_append_right
    have hgalη : (restrictBy X e A).IsGallery (galleryEnd a ũ₁) ũη :=
      (q2cDMr_isGallery_iff X (galleryEnd a ũ₁) ũη).mpr (by
        rw [← galleryEnd_coeGallery (a := a) (γ := ũ₁), hcoe1, hcoeη]
        exact hη)
    have hgalη' : (restrictBy X e A).IsGallery (galleryEnd a ũ₁) wη' :=
      (q2cDMr_isGallery_iff X (galleryEnd a ũ₁) wη').mpr (by
        rw [← galleryEnd_coeGallery (a := a) (γ := ũ₁), hcoe1, hcoeη']
        exact hη')
    have hηJ' : ∀ i ∈ galleryType ũη, i ∈ e ⁻¹' K := by
      intro i hi
      rw [galleryType] at hi
      obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hi
      show e i ∈ K
      rw [← hqi]
      have hmem : (e q.1, (q.2 : C)) ∈ coeGallery e A ũη :=
        List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hcoeη] at hmem
      exact hηK _ hmem
    have hη'J' : ∀ i ∈ galleryType wη', i ∈ e ⁻¹' K := by
      intro i hi
      rw [galleryType] at hi
      obtain ⟨q, hq, hqi⟩ := List.mem_map.mp hi
      show e i ∈ K
      rw [← hqi]
      have hmem : (e q.1, (q.2 : C)) ∈ coeGallery e A wη' :=
        List.mem_map.mpr ⟨q, hq, rfl⟩
      rw [hcoeη'] at hmem
      exact hη'K _ hmem
    have hJ' : (e ⁻¹' K).encard ≤ 2 :=
      (Set.encard_le_encard_of_injOn (f := e) (s := e ⁻¹' K) (t := K)
        (fun x hx => hx) he.injOn).trans hK
    have hend' : galleryEnd (galleryEnd a ũ₁) ũη = galleryEnd (galleryEnd a ũ₁) wη' := by
      apply Subtype.ext
      rw [← galleryEnd_coeGallery (a := galleryEnd a ũ₁) (γ := ũη),
        ← galleryEnd_coeGallery (a := galleryEnd a ũ₁) (γ := wη'),
        ← galleryEnd_coeGallery (a := a) (γ := ũ₁), hcoe1, hcoeη, hcoeη', hend]
    have hmove : (restrictBy X e A).ElemMove a (ũ₁ ++ ũη ++ ũ₂) (ũ₁ ++ wη' ++ ũ₂) :=
      ElemMove.mk ũ₁ ũη wη' ũ₂ (e ⁻¹' K) hJ' hgalη hgalη' hηJ' hη'J' hend'
    have hthis : (restrictBy X e A).TwoHomotopic a (ũ₁ ++ ũη ++ ũ₂)
        (ũ₁ ++ wη' ++ ũ₂) := TwoHomotopic.of_elemMove hmove
    rw [hũsplit, hurest, hwsplit, hwrest, ← h₁eq, ← h₂eq]
    simpa only [List.append_assoc] using hthis

private theorem q2cDMr_twoHomotopic_forward (he : Function.Injective e) {a : A}
    {γ γ' : List (K × A)} (hγ : (restrictBy X e A).IsGallery a γ)
    (h : (restrictBy X e A).TwoHomotopic a γ γ') :
    HomIn X (Set.range e) A 2 (a : C) (coeGallery e A γ) (coeGallery e A γ') := by
  rw [TwoHomotopic.iff_reflTransGen] at h
  induction h with
  | refl => exact HomIn.refl _
  | @tail b c hab hbc ih =>
    have hb : (restrictBy X e A).IsGallery a b :=
      (TwoHomotopic.iff_reflTransGen.mpr hab).isGallery_iff.mp hγ
    exact ih.trans (q2cDMr_elemMove_coe X he hb hbc)

private theorem q2cDMr_twoHomotopic_backward (he : Function.Injective e) {a : A}
    {u v : List (I × C)} (h : HomIn X (Set.range e) A 2 (a : C) u v) :
    ∀ ũ : List (K × A), coeGallery e A ũ = u → (restrictBy X e A).IsGallery a ũ →
      ∀ w : List (K × A), coeGallery e A w = v →
        (restrictBy X e A).TwoHomotopic a ũ w := by
  change Relation.EqvGen (ElemIn X (Set.range e) A 2 (a : C)) u v at h
  induction h with
  | rel x y hxy =>
    intro ũ hũ _ w hw
    exact q2cDMr_elemIn_coe X he hxy hũ hw
  | refl x =>
    intro ũ hũ _ w hw
    have hx : ũ = w := by
      apply coeGallery_injective he
      rw [hũ, hw]
    rw [hx]
  | symm x y hxy ih =>
    intro ũ hũ hgal w hw
    have hgal' : (restrictBy X e A).IsGallery a w :=
      q2cDMr_isGallery_of_homIn X he (HomIn.symm hxy) hũ hgal hw
    exact (ih w hw hgal' ũ hũ).symm
  | trans x y z hxy hyz ih1 ih2 =>
    intro ũ hũ hgal w hw
    have hg : GalleryIn X (Set.range e) A (a : C) x := by
      rw [← hũ]
      exact galleryIn_coeGallery X hgal
    have hgy : GalleryIn X (Set.range e) A (a : C) y := (HomIn.galleryIn_iff hxy).mp hg
    obtain ⟨m, hm, hmgal⟩ := exists_coeGallery X he hgy
    exact (ih1 ũ hũ hgal m hm).trans (ih2 m hm hmgal w hw)

theorem twoHomotopic_restrictBy_iff (he : Function.Injective e) {a : A} {γ γ' : List (K × A)}
    (hγ : (restrictBy X e A).IsGallery a γ) :
    (restrictBy X e A).TwoHomotopic a γ γ' ↔
      HomIn X (Set.range e) A 2 a (coeGallery e A γ) (coeGallery e A γ') := by
  refine ⟨q2cDMr_twoHomotopic_forward X he hγ, fun h => ?_⟩
  exact q2cDMr_twoHomotopic_backward X he h γ rfl hγ γ' rfl

theorem connected_restrictBy_iff (he : Function.Injective e) :
    (restrictBy X e A).Connected ↔ ConnectedIn X (Set.range e) A := by
  constructor
  · intro hc a ha b hb
    obtain ⟨γ, hgal, hend⟩ := hc ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨coeGallery e A γ, galleryIn_coeGallery X hgal, by
      change galleryEnd (↑(⟨a, ha⟩ : A)) (coeGallery e A γ) = b
      rw [galleryEnd_coeGallery (⟨a, ha⟩ : A) γ]
      exact congrArg Subtype.val hend⟩
  · intro hc x y
    obtain ⟨γ, hgal, hend⟩ := hc (x : C) x.2 (y : C) y.2
    obtain ⟨γ', hcoe, hgal'⟩ := exists_coeGallery X he hgal
    refine ⟨γ', hgal', ?_⟩
    apply Subtype.ext
    rw [← galleryEnd_coeGallery (a := x) (γ := γ'), hcoe, hend]

theorem simplyTwoConnected_restrictBy_iff (he : Function.Injective e) :
    (restrictBy X e A).SimplyTwoConnected ↔ SimplyConnectedIn X (Set.range e) A 2 := by
  constructor
  · intro hs x γ hgal hend
    let x' : A := ⟨x, hgal.1⟩
    obtain ⟨γ', hcoe, hgal'⟩ := exists_coeGallery X he (a := x') hgal
    have hend' : galleryEnd x' γ' = x' := by
      apply Subtype.ext
      rw [← galleryEnd_coeGallery (a := x') (γ := γ'), hcoe, hend]
    have h := hs x' γ' hgal' hend'
    have h' := (twoHomotopic_restrictBy_iff X he hgal').mp h
    simpa only [hcoe, coeGallery_nil] using h'
  · intro hs x γ hgal hend
    have hgalX : GalleryIn X (Set.range e) A (x : C) (coeGallery e A γ) :=
      galleryIn_coeGallery X hgal
    have hendX : galleryEnd (x : C) (coeGallery e A γ) = (x : C) := by
      rw [galleryEnd_coeGallery]
      exact congrArg Subtype.val hend
    have h := hs (x : C) (coeGallery e A γ) hgalX hendX
    exact (twoHomotopic_restrictBy_iff X he hgal).mpr (by simpa only [coeGallery_nil] using h)

end CFSG.ClassicalInvolution.Phan.PhanE.DM
