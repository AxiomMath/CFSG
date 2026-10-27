module

public import CFSG.Monster.B.Geometry.StrictGallery
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.GroupActions.Exchange

section Map

variable {B B' B'' : Type*}

theorem BraidMove.map_extend (g : B → B') (α β : List B) (e : BraidMove B) :
    (e.extend α β).map g = (e.map g).extend (α.map g) (β.map g) := by
  simp [BraidMove.map, BraidMove.extend]

theorem BraidMove.map_map (f : B → B') (g : B' → B'') (e : BraidMove B) :
    (e.map f).map g = e.map (g ∘ f) := by
  simp [BraidMove.map, List.map_map]

theorem BraidMove.map_id (e : BraidMove B) : e.map id = e := by
  simp [BraidMove.map]

theorem IsBraidPath.eq_of_isBraidPath {m : B → B → ℕ} {x y y' : List B} {p : List (BraidMove B)}
    (h : IsBraidPath m x p y) (h' : IsBraidPath m x p y') : y = y' := by
  induction p generalizing x with
  | nil => exact (isBraidPath_nil.mp h).symm.trans (isBraidPath_nil.mp h')
  | cons e p ih => exact ih h.2.2 h'.2.2

variable {m : B → B → ℕ} {m' : B' → B' → ℕ} {g : B → B'} (hg : Function.Injective g)
  (hm : ∀ a b, m' (g a) (g b) = m a b)
include hg hm

theorem BraidMove.IsValid.map {e : BraidMove B} (he : e.IsValid m) : (e.map g).IsValid m' :=
  ⟨fun h => he.1 (hg h), he.2.1.trans (hm _ _).symm, he.2.2⟩

theorem Elementary.map {a b : List (BraidMove B)} (h : Elementary m a b) :
    Elementary m' (a.map (BraidMove.map g)) (b.map (BraidMove.map g)) := by
  classical
  cases h with
  | backtrack e => exact .backtrack (e.map g)
  | square A C D s t k s' t' k' =>
    have h := Elementary.square (m := m') (A.map g) (C.map g) (D.map g) (g s) (g t) k (g s')
      (g t') k'
    simpa [BraidMove.map, map_altWord] using h
  | loop α β μ c T hT hc hcT =>
    have h := Elementary.loop (m := m') (α.map g) (β.map g) (μ.map g) (c.map (BraidMove.map g))
      (T.image g) (Finset.card_image_le.trans hT) (hc.map fun e he => he.map hg hm) ?_
    · have e1 : (c.map (BraidMove.extend α β)).map (BraidMove.map g) =
          (c.map (BraidMove.map g)).map (BraidMove.extend (α.map g) (β.map g)) := by
        simp only [List.map_map]
        exact List.map_congr_left fun e _ => BraidMove.map_extend g α β e
      rw [e1, List.map_nil]
      exact h
    · intro e he b hb
      obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
      rw [BraidMove.source_map] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.mp hb
      exact Finset.mem_image_of_mem g (hcT e₀ he₀ b₀ hb₀)

theorem Homotopic.map {x y : List B} {p q : List (BraidMove B)} (h : Homotopic m x y p q) :
    Homotopic m' (x.map g) (y.map g) (p.map (BraidMove.map g)) (q.map (BraidMove.map g)) := by
  induction h with
  | rel p q h =>
    obtain ⟨h1, h2, p₀, a, b, q₀, hab, rfl, rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨h1.map fun e he => he.map hg hm,
      h2.map fun e he => he.map hg hm, p₀.map (BraidMove.map g), a.map (BraidMove.map g),
      b.map (BraidMove.map g), q₀.map (BraidMove.map g), hab.map hg hm, by simp, by simp⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end Map

namespace ChamberSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {X : ChamberSystem ι C}

theorem isStrictMoveAt_iff {x : C} {e : BraidMove ι} {γ₁ η γ₂ γ' : List (ι × C)}
    (h1 : galleryType γ₁ = e.pre) (h2 : galleryType η = altWord e.s e.t e.len)
    (h3 : galleryType γ₂ = e.suf) :
    X.IsStrictMoveAt x e (γ₁ ++ η ++ γ₂) γ' ↔ ∃ η', γ' = γ₁ ++ η' ++ γ₂ ∧
      galleryType η' = altWord e.t e.s e.len ∧ X.IsOrdinary (galleryEnd x γ₁) η ∧
      X.IsOrdinary (galleryEnd x γ₁) η' ∧
      galleryEnd (galleryEnd x γ₁) η = galleryEnd (galleryEnd x γ₁) η' := by
  constructor
  · rintro ⟨ζ₁, ζ, ζ', ζ₂, hγ, rfl, k1, k2, k3, -, k5, k6, k7⟩
    have l1 : γ₁.length = ζ₁.length := by
      rw [← length_galleryType, ← length_galleryType, h1, k1]
    have l2 : η.length = ζ.length := by
      rw [← length_galleryType, ← length_galleryType, h2, k2]
    obtain ⟨e12, rfl⟩ := List.append_inj hγ (by simp [l1, l2])
    obtain ⟨rfl, rfl⟩ := List.append_inj e12 l1
    exact ⟨ζ', rfl, k3, k5, k6, k7⟩
  · rintro ⟨η', rfl, k3, k5, k6, k7⟩
    exact ⟨γ₁, η, η', γ₂, rfl, rfl, h1, h2, k3, h3, k5, k6, k7⟩

theorem IsStrictMoveAt.of_extend {x : C} {e : BraidMove ι} {α β : List ι}
    {gα gμ gβ γ' : List (ι × C)} (hα : galleryType gα = α) (hβ : galleryType gβ = β)
    (h : X.IsStrictMoveAt x (e.extend α β) (gα ++ gμ ++ gβ) γ') :
    ∃ gμ', γ' = gα ++ gμ' ++ gβ ∧ X.IsStrictMoveAt (galleryEnd x gα) e gμ gμ' := by
  obtain ⟨γ₁, η, η', γ₂, hγ, rfl, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [BraidMove.extend] at h1 h2 h3 h4
  obtain ⟨γ₁a, γ₁b, rfl, ha, hb⟩ := exists_split_of_galleryType_eq_append h1
  obtain ⟨γ₂a, γ₂b, rfl, hc, hd⟩ := exists_split_of_galleryType_eq_append h4
  have l1 : gα.length = γ₁a.length := by
    rw [← length_galleryType, ← length_galleryType, hα, ha]
  have l2 : gβ.length = γ₂b.length := by
    rw [← length_galleryType, ← length_galleryType, hβ, hd]
  have hγ' : gα ++ gμ ++ gβ = γ₁a ++ (γ₁b ++ η ++ γ₂a) ++ γ₂b := by
    rw [hγ]
    simp
  obtain ⟨e1, rfl⟩ := List.append_inj' hγ' l2
  obtain ⟨rfl, rfl⟩ := List.append_inj e1 l1
  rw [galleryEnd_append] at h5 h6 h7
  exact ⟨γ₁b ++ η' ++ γ₂a, by simp, γ₁b, η, η', γ₂a, rfl, rfl, hb, h2, h3, hc, h5, h6, h7⟩

theorem IsStrictLift.of_extend {x : C} {c : List (BraidMove ι)} {α β : List ι}
    {gα gμ gβ γ' : List (ι × C)} (hα : galleryType gα = α) (hβ : galleryType gβ = β)
    (h : X.IsStrictLift x (c.map (BraidMove.extend α β)) (gα ++ gμ ++ gβ) γ') :
    ∃ gμ', γ' = gα ++ gμ' ++ gβ ∧ X.IsStrictLift (galleryEnd x gα) c gμ gμ' := by
  induction c generalizing gμ with
  | nil => exact ⟨gμ, (isStrictLift_nil.mp h).symm, rfl⟩
  | cons e c ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    obtain ⟨gμ₁, rfl, h3⟩ := h1.of_extend hα hβ
    obtain ⟨gμ', rfl, h4⟩ := ih h2
    exact ⟨gμ', rfl, gμ₁, h3, h4⟩

theorem IsStrictLift.galleryType_eq {m : ι → ι → ℕ} {x : C} {p : List (BraidMove ι)}
    {ω ω' : List ι} (hp : IsBraidPath m ω p ω') {γ γ' : List (ι × C)}
    (h : X.IsStrictLift x p γ γ') (hγ : galleryType γ = ω) : galleryType γ' = ω' := by
  induction p generalizing γ ω with
  | nil => rw [← isStrictLift_nil.mp h, hγ, isBraidPath_nil.mp hp]
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    exact ih hp.2.2 h2 h1.galleryType_eq.2

theorem IsStrictLift.isBraidPath {x : C} {p : List (BraidMove ι)}
    (hp : ∀ e ∈ p, e.IsValid (braidExponent cs)) {γ γ' : List (ι × C)}
    (h : X.IsStrictLift x p γ γ') :
    IsBraidPath (braidExponent cs) (galleryType γ) p (galleryType γ') := by
  induction p generalizing γ with
  | nil => rw [isStrictLift_nil.mp h]; rfl
  | cons e p ih =>
    obtain ⟨γ₁, h1, h2⟩ := h
    refine ⟨hp e (by simp), h1.galleryType_eq.1.symm, ?_⟩
    rw [← h1.galleryType_eq.2]
    exact ih (fun e' he' => hp e' (by simp [he'])) h2

theorem exists_isStrictLift_of_reflTransGen {x : C} {γ γ' : List (ι × C)}
    (h : Relation.ReflTransGen (X.StrictMove cs x) γ γ') :
    ∃ p : List (BraidMove ι), (∀ e ∈ p, e.IsValid (braidExponent cs)) ∧
      X.IsStrictLift x p γ γ' := by
  induction h with
  | refl => exact ⟨[], by simp, rfl⟩
  | tail _ h ih =>
    obtain ⟨p, hp, hl⟩ := ih
    obtain ⟨e, he, hm⟩ := h
    refine ⟨p ++ [e], fun e' he' => ?_, isStrictLift_append.mpr ⟨_, hl, _, hm, rfl⟩⟩
    rcases List.mem_append.mp he' with he' | he'
    · exact hp e' he'
    · rw [List.mem_singleton.mp he']
      exact he

section Rigidity

variable (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)
include hres

theorem eq_of_isOrdinary_altWord {a b : ι} (hab : a ≠ b) {k : ℕ} (hk : k = braidExponent cs a b)
    (hk0 : k ≠ 0) {y : C} {η η' : List (ι × C)} (hη : X.IsOrdinary y η) (hη' : X.IsOrdinary y η')
    (ht : galleryType η = altWord a b k) (ht' : galleryType η' = altWord a b k)
    (hend : galleryEnd y η = galleryEnd y η') : η = η' := by
  rw [braidExponent_eq] at hk
  obtain ⟨δ, hB, hadj⟩ := hres a b hab y
  have hJ : ∀ i ∈ galleryType η, i ∈ ({a, b} : Set ι) := fun i hi => by
    rw [ht] at hi
    rcases mem_altWord hi with rfl | rfl <;> simp
  have hred : cs.IsReduced (galleryType η) := by
    rw [ht, hk]
    exact isReduced_altWord hab (hk ▸ hk0)
  exact eq_of_isOrdinary_of_isBuildingOn hB hadj (X.self_mem_residue _ y) hη hη' hJ
    (ht.trans ht'.symm) hred hend

variable (h3 : ∀ T : Finset ι, T.card ≤ 3 → ∀ y : C,
  ∃ T' : Set ι, (T : Set ι) ⊆ T' ∧ X.IsResidueBuilding cs T' y)
include h3

theorem lift_eq_of_elementary {a b : List (BraidMove ι)}
    (hab : Elementary (braidExponent cs) a b) {u v v' : List ι}
    (ha : IsBraidPath (braidExponent cs) u a v) (hb : IsBraidPath (braidExponent cs) u b v')
    {x : C} {γ₀ γa γb : List (ι × C)} (hγ₀ : X.IsReducedOrdinary cs x γ₀)
    (htype : galleryType γ₀ = u) (hla : X.IsStrictLift x a γ₀ γa)
    (hlb : X.IsStrictLift x b γ₀ γb) : γa = γb := by
  cases hab with
  | backtrack e =>
    obtain ⟨γ₁, h1, γ₂, h2, rfl⟩ := hla
    rw [← isStrictLift_nil.mp hlb]
    exact h2.unique hres ha.2.2.1 h1.reverse
  | square A C' D s t k s' t' k' =>
    obtain ⟨⟨hst, hk, hk0⟩, hsrc, ⟨hst', hk', hk0'⟩, -, -⟩ := ha
    obtain ⟨γ₁, h1, γ₂, h2, rfl⟩ := hla
    obtain ⟨γ₁', h1', γ₂', h2', rfl⟩ := hlb
    have hu : galleryType γ₀ = A ++ altWord s t k ++ (C' ++ altWord s' t' k' ++ D) := by
      rw [htype, ← hsrc]
      rfl
    obtain ⟨gAη, rest, rfl, hAη, hrest⟩ := exists_split_of_galleryType_eq_append hu
    obtain ⟨gA, η, rfl, hA, hη⟩ := exists_split_of_galleryType_eq_append hAη
    obtain ⟨gCζ, gD, rfl, hCζ, hD⟩ := exists_split_of_galleryType_eq_append hrest
    obtain ⟨gC, ζ, rfl, hC, hζ⟩ := exists_split_of_galleryType_eq_append hCζ
    obtain ⟨η₁, rfl, hη₁, -, hη₁o, hη₁e⟩ := (isStrictMoveAt_iff (e := ⟨A, s, t, k,
      C' ++ altWord s' t' k' ++ D⟩) hA hη (by rw [galleryType_append, galleryType_append, hC,
        hζ, hD])).mp h1
    have e2 : gA ++ η₁ ++ (gC ++ ζ ++ gD) = gA ++ η₁ ++ gC ++ ζ ++ gD := by simp
    rw [e2] at h2
    obtain ⟨ζ₁, rfl, hζ₁, -, hζ₁o, hζ₁e⟩ := (isStrictMoveAt_iff (e := ⟨A ++ altWord t s k ++ C',
      s', t', k', D⟩) (by rw [galleryType_append, galleryType_append, hA, hη₁, hC]) hζ hD).mp h2
    have e3 : gA ++ η ++ (gC ++ ζ ++ gD) = gA ++ η ++ gC ++ ζ ++ gD := by simp
    rw [e3] at h1'
    obtain ⟨ζ₂, rfl, hζ₂, -, hζ₂o, hζ₂e⟩ := (isStrictMoveAt_iff (e := ⟨A ++ altWord s t k ++ C',
      s', t', k', D⟩) (by rw [galleryType_append, galleryType_append, hA, hη, hC]) hζ hD).mp h1'
    have e4 : gA ++ η ++ gC ++ ζ₂ ++ gD = gA ++ η ++ (gC ++ ζ₂ ++ gD) := by simp
    rw [e4] at h2'
    obtain ⟨η₂, rfl, hη₂, -, hη₂o, hη₂e⟩ := (isStrictMoveAt_iff (e := ⟨A, s, t, k,
      C' ++ altWord t' s' k' ++ D⟩) hA hη (by rw [galleryType_append, galleryType_append, hC,
        hζ₂, hD])).mp h2'
    have hηη : η₁ = η₂ := eq_of_isOrdinary_altWord hres hst.symm
      (hk.trans (braidExponent_comm _ _)) hk0 hη₁o hη₂o hη₁ hη₂ (hη₁e.symm.trans hη₂e)
    subst hηη
    have hend : galleryEnd x (gA ++ η₁ ++ gC) = galleryEnd x (gA ++ η ++ gC) := by
      simp only [galleryEnd_append] at hη₁e ⊢
      rw [hη₁e]
    rw [hend] at hζ₁o hζ₁e
    have hζζ : ζ₁ = ζ₂ := eq_of_isOrdinary_altWord hres hst'.symm
      (hk'.trans (braidExponent_comm _ _)) hk0' hζ₁o hζ₂o hζ₁ hζ₂ (hζ₁e.symm.trans hζ₂e)
    subst hζζ
    simp
  | loop α β μ c T hT hc hcT =>
    rw [← isStrictLift_nil.mp hlb]
    rcases c with _ | ⟨e₀, c'⟩
    · exact (isStrictLift_nil.mp hla).symm
    obtain ⟨-, hsrc, -⟩ := ha
    have hμ : e₀.source = μ := hc.2.1
    have hu : galleryType γ₀ = α ++ μ ++ β := by
      rw [htype, ← hsrc, BraidMove.source_extend, hμ]
    obtain ⟨gαμ, gβ, rfl, hαμ, hβ⟩ := exists_split_of_galleryType_eq_append hu
    obtain ⟨gα, gμ, rfl, hα, hgμ⟩ := exists_split_of_galleryType_eq_append hαμ
    obtain ⟨gμ', rfl, hl⟩ := hla.of_extend hα hβ
    obtain ⟨⟨-, hgμo⟩, -⟩ := (isOrdinary_append x _ _).mp ((isOrdinary_append x _ _).mp hγ₀.1).1
      |> fun h => (⟨h, trivial⟩ : _ ∧ True)
    have hgμ'o : X.IsOrdinary (galleryEnd x gα) gμ' := hl.isOrdinary_iff.mp hgμo
    have hgμ't : galleryType gμ' = μ := hl.galleryType_eq hc hgμ
    have hred : cs.IsReduced (galleryType gμ) := by
      have h1 := hγ₀.2
      rw [hu] at h1
      have h2 := (h1.drop α.length).take μ.length
      rwa [List.append_assoc, List.drop_left, List.take_left, ← hgμ] at h2
    have hT' : ∀ i ∈ galleryType gμ, i ∈ (T : Set ι) := by
      rw [hgμ, ← hμ]
      exact fun i hi => hcT e₀ (by simp) i hi
    obtain ⟨T', hTT', hRB⟩ := h3 T hT (galleryEnd x gα)
    have := hRB.eq_of_isReducedOrdinary ⟨hgμo, hred⟩ hgμ'o (fun i hi => hTT' (hT' i hi))
      (hgμ.trans hgμ't.symm) hl.galleryEnd_eq
    rw [← this]

theorem IsStrictLift.eq_of_homotopic {x : C} {γ : List (ι × C)}
    (hγ : X.IsReducedOrdinary cs x γ) {ω' : List ι} {p q : List (BraidMove ι)}
    (hpp : IsBraidPath (braidExponent cs) (galleryType γ) p ω')
    (h : Homotopic (braidExponent cs) (galleryType γ) ω' p q) {γp γq : List (ι × C)}
    (hp : X.IsStrictLift x p γ γp) (hq : X.IsStrictLift x q γ γq) : γp = γq := by
  have key : ∀ (p₀ a b q₀ : List (BraidMove ι)), Elementary (braidExponent cs) a b →
      IsBraidPath (braidExponent cs) (galleryType γ) (p₀ ++ a ++ q₀) ω' →
      IsBraidPath (braidExponent cs) (galleryType γ) (p₀ ++ b ++ q₀) ω' →
      ∀ γ', X.IsStrictLift x (p₀ ++ a ++ q₀) γ γ' → X.IsStrictLift x (p₀ ++ b ++ q₀) γ γ' := by
    intro p₀ a b q₀ hab ha hb γ' hl
    obtain ⟨w₁, ha1, ha2⟩ := ha.of_append
    obtain ⟨u, hu1, hu2⟩ := ha1.of_append
    obtain ⟨w₁', hb1, hb2⟩ := hb.of_append
    obtain ⟨u', hu1', hu2'⟩ := hb1.of_append
    obtain rfl := hu1.eq_of_isBraidPath hu1'
    obtain ⟨γ₂, hl1, hl2⟩ := isStrictLift_append.mp hl
    obtain ⟨γ₁, hl11, hl12⟩ := isStrictLift_append.mp hl1
    have hγ₁ : X.IsReducedOrdinary cs x γ₁ :=
      ((hl11.strictHomotopic fun e he => hu1.isValid_of_mem he).isReducedOrdinary_iff).mp hγ
    have hγ₁t : galleryType γ₁ = u := hl11.galleryType_eq hu1 rfl
    obtain ⟨γ₂', hb', hγ₂'o, -, -⟩ := exists_isStrictLift hres hu2' hγ₁.1 hγ₁t
    have hγ₂ : γ₂ = γ₂' := lift_eq_of_elementary hres h3 hab hu2 hu2' hγ₁ hγ₁t hl12 hb'
    subst hγ₂
    exact isStrictLift_append.mpr ⟨_, isStrictLift_append.mpr ⟨_, hl11, hb'⟩, hl2⟩
  have hset := h.apply_eq (fun r => {γ' | X.IsStrictLift x r γ γ'}) fun p₀ a b q₀ hab ha hb => by
    ext γ'
    constructor
    · exact key p₀ a b q₀ hab ha hb γ'
    · intro hl
      obtain ⟨w₁, ha1, ha2⟩ := ha.of_append
      obtain ⟨u, hu1, hu2⟩ := ha1.of_append
      obtain ⟨w₁', hb1, hb2⟩ := hb.of_append
      obtain ⟨u', hu1', hu2'⟩ := hb1.of_append
      obtain rfl := hu1.eq_of_isBraidPath hu1'
      obtain ⟨γ₂, hl1, hl2⟩ := isStrictLift_append.mp hl
      obtain ⟨γ₁, hl11, hl12⟩ := isStrictLift_append.mp hl1
      have hγ₁ : X.IsReducedOrdinary cs x γ₁ :=
        ((hl11.strictHomotopic fun e he => hu1.isValid_of_mem he).isReducedOrdinary_iff).mp hγ
      have hγ₁t : galleryType γ₁ = u := hl11.galleryType_eq hu1 rfl
      obtain ⟨γ₂', ha', -, -, -⟩ := exists_isStrictLift hres hu2 hγ₁.1 hγ₁t
      have hγ₂ : γ₂' = γ₂ := lift_eq_of_elementary hres h3 hab hu2 hu2' hγ₁ hγ₁t ha' hl12
      subst hγ₂
      exact isStrictLift_append.mpr ⟨_, isStrictLift_append.mpr ⟨_, hl11, ha'⟩, hl2⟩
  have hmem : γp ∈ {γ' | X.IsStrictLift x q γ γ'} := by
    rw [← hset]
    exact hp
  have hqq : IsBraidPath (braidExponent cs) (galleryType γ) q ω' := h.isBraidPath_iff.mp hpp
  exact hmem.unique hres (fun e he => hqq.isValid_of_mem he) hq

theorem eq_of_strictHomotopic [Finite W] {x : C} {γ γ' : List (ι × C)}
    (hγ : X.IsReducedOrdinary cs x γ) (h : X.StrictHomotopic cs x γ γ')
    (htype : galleryType γ = galleryType γ') : γ = γ' := by
  obtain ⟨p, hpv, hl⟩ := exists_isStrictLift_of_reflTransGen (StrictHomotopic.iff_reflTransGen.mp h)
  have hpath : IsBraidPath (braidExponent cs) (galleryType γ) p (galleryType γ) := by
    have := hl.isBraidPath hpv
    rwa [← htype] at this
  let f : ι → simpleSet cs := fun i => ⟨cs.simple i, i, rfl⟩
  have hf : Function.Injective f := fun a b h => cs.simple_injective (congrArg Subtype.val h)
  have hS : IsBraidPath (pairOrder (simpleSet cs)) (toSWord cs (galleryType γ))
      (p.map (BraidMove.map f)) (toSWord cs (galleryType γ)) :=
    hpath.map fun e he => he.map hf fun a b => rfl
  have hH := homotopic_of_isReduced orderOf_simpleSet exchangeCondition_simpleSet
    triplePrefix_simpleSet (isReduced_toSWord_iff.mpr hγ.2) hS (IsBraidPath.nil _)
  have hg : Function.Injective (simpleIndex (cs := cs)) := fun s t h => Subtype.ext (by
    rw [← simple_simpleIndex s, ← simple_simpleIndex t, h])
  have hH' := hH.map (m' := braidExponent cs) hg fun s t => by
    change orderOf (cs.simple (simpleIndex s) * cs.simple (simpleIndex t)) = orderOf ((s : W) * t)
    rw [simple_simpleIndex, simple_simpleIndex]
  have hpp : (p.map (BraidMove.map f)).map (BraidMove.map simpleIndex) = p := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id p]
    refine List.map_congr_left fun e _ => ?_
    rw [Function.comp_apply, BraidMove.map_map]
    have : (simpleIndex ∘ f) = id := funext fun i => simpleIndex_mk i
    rw [this, BraidMove.map_id]
    rfl
  rw [hpp, List.map_nil, map_simpleIndex_toSWord] at hH'
  exact (IsStrictLift.eq_of_homotopic hres h3 hγ hpath hH' hl rfl).symm

end Rigidity

end ChamberSystem

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ChamberSystem

theorem F4_local_three_strict_gallery_rigidity
    {C : Type*} (X : ChamberSystem (Fin Tag.F4.rank) C)
    (hres2 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 2 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x)
    (hres3 : ∀ J : Set (Fin Tag.F4.rank), J.ncard = 3 → ∀ x,
      X.IsResidueBuilding (coxeterSystem .F4) J x)
    {x : C} {γ γ' : List (Fin Tag.F4.rank × C)}
    (hγ : X.IsReducedOrdinary (coxeterSystem .F4) x γ)
    (h : X.StrictHomotopic (coxeterSystem .F4) x γ γ') (htype : galleryType γ = galleryType γ') :
    γ = γ' := by
  refine eq_of_strictHomotopic (fun s t hst y => hres2 {s, t} (Set.ncard_pair hst) y)
    (fun T hT y => ?_) hγ h htype
  have huniv : (Set.univ : Set (Fin Tag.F4.rank)).encard = 4 := by
    rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    rfl
  have hTc : (T : Set (Fin Tag.F4.rank)).encard ≤ 3 := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hT
  obtain ⟨T', hTT', -, hT'⟩ := Set.exists_superset_subset_encard_eq (k := 3)
    (Set.subset_univ (T : Set (Fin Tag.F4.rank))) hTc (by rw [huniv]; norm_num)
  refine ⟨T', hTT', hres3 T' ?_ y⟩
  rw [Set.ncard, hT']
  rfl

end CFSG.Monster.B.Geometry
