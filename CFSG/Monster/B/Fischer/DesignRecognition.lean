module

public import CFSG.Monster.B.Classical.Derived22Coordinates
public import CFSG.Monster.B.Classical.HyperovalOrbits
public import CFSG.Monster.B.TwoA.Base.M22

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Plane CFSG.Monster.B.Classical.Mog22
  CFSG.Monster.B.TwoA
open scoped MatrixGroups

section Design

variable {X : Type*}

theorem map_perm_mul (σ τ : Equiv.Perm X) (B : Finset X) :
    B.map (σ * τ).toEmbedding = (B.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]; rfl

theorem map_perm_one (B : Finset X) : B.map (1 : Equiv.Perm X).toEmbedding = B :=
  Finset.map_refl

@[expose] def IsSteiner3Design [Fintype X] (ℬ : Finset (Finset X)) : Prop :=
  Fintype.card X = 22 ∧ (∀ B ∈ ℬ, B.card = 6) ∧
    ∀ T : Finset X, T.card = 3 → ∃! B, B ∈ ℬ ∧ T ⊆ B

@[expose] def designAut (ℬ : Finset (Finset X)) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ B : Finset X, B.map σ.toEmbedding ∈ ℬ ↔ B ∈ ℬ}
  mul_mem' {σ τ} hσ hτ B := by
    change B.map (σ * τ).toEmbedding ∈ ℬ ↔ B ∈ ℬ
    rw [map_perm_mul, hσ, hτ]
  one_mem' B := by
    change B.map (1 : Equiv.Perm X).toEmbedding ∈ ℬ ↔ B ∈ ℬ
    rw [map_perm_one]
  inv_mem' {σ} hσ B := by
    change B.map σ⁻¹.toEmbedding ∈ ℬ ↔ B ∈ ℬ
    rw [← hσ, ← map_perm_mul, mul_inv_cancel, map_perm_one]

theorem mem_designAut {ℬ : Finset (Finset X)} {σ : Equiv.Perm X} :
    σ ∈ designAut ℬ ↔ ∀ B : Finset X, B.map σ.toEmbedding ∈ ℬ ↔ B ∈ ℬ := Iff.rfl

variable [DecidableEq X]

theorem card_inter_le_two {ℬ : Finset (Finset X)}
    (hu : ∀ T : Finset X, T.card = 3 → ∃! B, B ∈ ℬ ∧ T ⊆ B) {B B' : Finset X} (hB : B ∈ ℬ)
    (hB' : B' ∈ ℬ) (hne : B ≠ B') : (B ∩ B').card ≤ 2 := by
  by_contra h
  obtain ⟨T, hT, hT3⟩ := Finset.exists_subset_card_eq (s := B ∩ B') (n := 3) (by omega)
  obtain ⟨B₀, -, hB₀⟩ := hu T hT3
  exact hne ((hB₀ B ⟨hB, hT.trans Finset.inter_subset_left⟩).trans
    (hB₀ B' ⟨hB', hT.trans Finset.inter_subset_right⟩).symm)

variable {x : X}

@[expose] def planeImg (ι : {y // y ≠ x} ≃ Fin 21) (B : Finset X) : Finset (Fin 21) :=
  Finset.univ.filter fun p => ((ι.symm p : {y // y ≠ x}) : X) ∈ B

theorem mem_planeImg {ι : {y // y ≠ x} ≃ Fin 21} {B : Finset X} {p : Fin 21} :
    p ∈ planeImg ι B ↔ ((ι.symm p : {y // y ≠ x}) : X) ∈ B := by
  simp [planeImg]

theorem planeImg_inter (ι : {y // y ≠ x} ≃ Fin 21) (B B' : Finset X) :
    planeImg ι (B ∩ B') = planeImg ι B ∩ planeImg ι B' := by
  ext p; simp [mem_planeImg]

theorem card_planeImg_le (ι : {y // y ≠ x} ≃ Fin 21) (B : Finset X) :
    (planeImg ι B).card ≤ B.card :=
  Finset.card_le_card_of_injOn (fun p => ((ι.symm p : {y // y ≠ x}) : X))
    (fun _ hp => mem_planeImg.1 hp) (fun _ _ _ _ h => ι.symm.injective (Subtype.ext h))

theorem card_planeImg_of_not_mem (ι : {y // y ≠ x} ≃ Fin 21) {B : Finset X} (hx : x ∉ B) :
    (planeImg ι B).card = B.card := by
  refine le_antisymm (card_planeImg_le ι B) ?_
  refine Finset.card_le_card_of_injOn (fun y => if h : y = x then 0 else ι ⟨y, h⟩) ?_ ?_
  · intro y hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    rw [Finset.mem_coe, mem_planeImg]
    simp only [hyx, ↓reduceDIte, Equiv.symm_apply_apply]
    exact hy
  · intro y hy z hz h
    have hyx : y ≠ x := fun e => hx (e ▸ hy)
    have hzx : z ≠ x := fun e => hx (e ▸ hz)
    simp only [hyx, hzx, ↓reduceDIte] at h
    exact congrArg Subtype.val (ι.injective h)

@[expose] def preTriple (ι : {y // y ≠ x} ≃ Fin 21) (p q r : Fin 21) : Finset X :=
  {(ι.symm p : X), (ι.symm q : X), (ι.symm r : X)}

theorem card_preTriple (ι : {y // y ≠ x} ≃ Fin 21) {p q r : Fin 21} (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) : (preTriple ι p q r).card = 3 := by
  have hinj : ∀ a b : Fin 21, a ≠ b → ((ι.symm a : {y // y ≠ x}) : X) ≠ ι.symm b := by
    intro a b hab h
    exact hab (ι.symm.injective (Subtype.ext h))
  rw [preTriple, Finset.card_insert_of_notMem, Finset.card_pair (hinj q r hqr)]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hinj p q hpq, hinj p r hpr⟩

theorem preTriple_subset (ι : {y // y ≠ x} ≃ Fin 21) {B : Finset X} {p q r : Fin 21}
    (hp : p ∈ planeImg ι B) (hq : q ∈ planeImg ι B) (hr : r ∈ planeImg ι B) :
    preTriple ι p q r ⊆ B := by
  intro y hy
  simp only [preTriple, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact mem_planeImg.1 hp
  · exact mem_planeImg.1 hq
  · exact mem_planeImg.1 hr

theorem planeImg_map (ι : {y // y ≠ x} ≃ Fin 21) {σ : Equiv.Perm X} {π : Equiv.Perm (Fin 21)}
    (hσ : ∀ p, σ (ι.symm p : X) = ι.symm (π p)) (B : Finset X) :
    planeImg ι (B.map σ.toEmbedding) = (planeImg ι B).map π.toEmbedding := by
  ext q
  rw [Finset.mem_map_equiv, mem_planeImg, mem_planeImg, Finset.mem_map_equiv]
  have h := hσ (π.symm q)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]

end Design

section Recognition

variable {X : Type*} [Fintype X] [DecidableEq X] {ℬ : Finset (Finset X)} {x : X}
  {ι : {y // y ≠ x} ≃ Fin 21}

omit [Fintype X] in
theorem exists_block_of_line
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine) (a : Fin 21) :
    ∃ B ∈ ℬ, x ∈ B ∧ planeImg ι B = projLine a := by
  have : projLine a ∈ (ℬ.filter (x ∈ ·)).image (planeImg ι) :=
    hL ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
  obtain ⟨B, hB, e⟩ := Finset.mem_image.1 this
  exact ⟨B, (Finset.mem_filter.1 hB).1, (Finset.mem_filter.1 hB).2, e⟩

omit [Fintype X] in
theorem exists_line_of_block
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine) {B : Finset X}
    (hB : B ∈ ℬ) (hx : x ∈ B) : ∃ a, planeImg ι B = projLine a := by
  have : planeImg ι B ∈ Finset.univ.image projLine :=
    hL ▸ Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB, hx⟩)
  obtain ⟨a, -, e⟩ := Finset.mem_image.1 this
  exact ⟨a, e.symm⟩

theorem planeImg_isHyperoval (hD : IsSteiner3Design ℬ)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine) {B : Finset X}
    (hB : B ∈ ℬ) (hx : x ∉ B) : IsHyperoval (planeImg ι B) := by
  refine ⟨by rw [card_planeImg_of_not_mem ι hx, hD.2.1 B hB], ?_⟩
  rintro p hp q hq r hr hpq hpr hqr ⟨a, hpa, hqa, hra⟩
  obtain ⟨B', hB', hxB', hB'a⟩ := exists_block_of_line hL a
  rw [← hB'a] at hpa hqa hra
  obtain ⟨B₀, -, hu⟩ := hD.2.2 _ (card_preTriple ι hpq hpr hqr)
  have h1 := hu B ⟨hB, preTriple_subset ι hp hq hr⟩
  have h2 := hu B' ⟨hB', preTriple_subset ι hpa hqa hra⟩
  exact hx (h1.trans h2.symm ▸ hxB')

@[expose] def offImg (ι : {y // y ≠ x} ≃ Fin 21) (ℬ : Finset (Finset X)) :
    Finset (Finset (Fin 21)) :=
  (ℬ.filter (x ∉ ·)).image (planeImg ι)

omit [Fintype X] in
theorem mem_offImg {A : Finset (Fin 21)} :
    A ∈ offImg ι ℬ ↔ ∃ B ∈ ℬ, x ∉ B ∧ planeImg ι B = A := by
  simp only [offImg, Finset.mem_image, Finset.mem_filter, and_assoc]

omit [Fintype X] in
theorem map_mem_offImg {σ : Equiv.Perm X} (hσ : σ ∈ designAut ℬ) (hσx : σ x = x)
    {π : Equiv.Perm (Fin 21)} (hπ : ∀ p, σ (ι.symm p : X) = ι.symm (π p)) {A : Finset (Fin 21)}
    (hA : A ∈ offImg ι ℬ) : A.map π.toEmbedding ∈ offImg ι ℬ := by
  obtain ⟨B, hB, hx, rfl⟩ := mem_offImg.1 hA
  refine mem_offImg.2 ⟨B.map σ.toEmbedding, (hσ B).2 hB, ?_, planeImg_map ι hπ B⟩
  rw [Finset.mem_map_equiv]
  intro h
  apply hx
  have : σ.symm x = x := by rw [Equiv.symm_apply_eq, hσx]
  rwa [this] at h

theorem card_inter_offImg_le (hD : IsSteiner3Design ℬ) {A A' : Finset (Fin 21)}
    (hA : A ∈ offImg ι ℬ) (hA' : A' ∈ offImg ι ℬ) (hne : A ≠ A') : (A ∩ A').card ≤ 2 := by
  obtain ⟨B, hB, -, rfl⟩ := mem_offImg.1 hA
  obtain ⟨B', hB', -, rfl⟩ := mem_offImg.1 hA'
  rw [← planeImg_inter]
  exact (card_planeImg_le ι _).trans
    (card_inter_le_two hD.2.2 hB hB' fun h => hne (h ▸ rfl))

theorem not_collinear3_five_one_zero : ¬Collinear3 5 1 0 := isFrame_base.1

theorem offImg_nonempty (hD : IsSteiner3Design ℬ)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine) :
    (offImg ι ℬ).Nonempty := by
  obtain ⟨B, ⟨hB, hT⟩, -⟩ := hD.2.2 _ (card_preTriple ι (p := 5) (q := 1) (r := 0) (by decide)
    (by decide) (by decide))
  have hmem : ∀ p ∈ ({5, 1, 0} : Finset (Fin 21)), p ∈ planeImg ι B := by
    intro p hp
    rw [mem_planeImg]
    apply hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> simp [preTriple]
  by_cases hx : x ∈ B
  · obtain ⟨a, ha⟩ := exists_line_of_block hL hB hx
    exact absurd ⟨a, ha ▸ hmem 5 (by simp), ha ▸ hmem 1 (by simp), ha ▸ hmem 0 (by simp)⟩
      not_collinear3_five_one_zero
  · exact ⟨_, mem_offImg.2 ⟨B, hB, hx, rfl⟩⟩

theorem exists_card_inter_three : ∀ i k : Fin 3, i ≠ k →
    3 ≤ ((ofMask (leastMask i) : Finset (Fin 21)) ∩ ofMask (leastMask k)).card := by
  decide

theorem ofMask_leastMask_mem
    (i : Fin 3) : (ofMask (leastMask i) : Finset (Fin 21)) ∈ O i := by
  obtain ⟨A, hA, e⟩ := (leastMask_spec i).2
  rwa [← e, ofMask_mask]

theorem offImg_eq_O (hD : IsSteiner3Design ℬ)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine)
    (hG : ∀ g : PSL(3, CFSG.Fischer.F4), ∃ σ ∈ designAut ℬ, σ x = x ∧
      ∀ p, σ (ι.symm p : X) = ι.symm (pslPerm g p)) :
    ∃ i, offImg ι ℬ = O i := by
  have hhyp : ∀ A ∈ offImg ι ℬ, A ∈ O 0 ∪ O 1 ∪ O 2 := by
    intro A hA
    obtain ⟨B, hB, hx, rfl⟩ := mem_offImg.1 hA
    rw [← hyperovals_eq, mem_hyperovals]
    exact planeImg_isHyperoval hD hL hB hx
  have hO3 : ∀ A ∈ offImg ι ℬ, ∃ k, A ∈ O k := by
    intro A hA
    have := hhyp A hA
    simp only [Finset.mem_union] at this
    rcases this with (h | h) | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hsub : ∀ k, ∀ A ∈ offImg ι ℬ, A ∈ O k → O k ⊆ offImg ι ℬ := by
    intro k A hA hk A' hA'
    have : A' ∈ pslOrbit A := by
      rw [show pslOrbit A = (O k : Set (Finset (Fin 21))) from orbit_O hk]
      exact hA'
    obtain ⟨g, rfl⟩ := this
    obtain ⟨σ, hσ, hσx, hπ⟩ := hG g
    exact map_mem_offImg hσ hσx hπ hA
  obtain ⟨A₀, hA₀⟩ := offImg_nonempty hD hL
  obtain ⟨i, hi⟩ := hO3 A₀ hA₀
  refine ⟨i, Finset.Subset.antisymm (fun A hA => ?_) (hsub i A₀ hA₀ hi)⟩
  obtain ⟨k, hk⟩ := hO3 A hA
  by_cases hik : i = k
  · exact hik ▸ hk
  · exfalso
    have h1 := hsub i A₀ hA₀ hi (ofMask_leastMask_mem i)
    have h2 := hsub k A hA hk (ofMask_leastMask_mem k)
    have hne : (ofMask (leastMask i) : Finset (Fin 21)) ≠ ofMask (leastMask k) := fun h =>
      Finset.disjoint_left.1 (disjoint_O hik) (ofMask_leastMask_mem i)
        (h ▸ ofMask_leastMask_mem k)
    have := card_inter_offImg_le hD h1 h2 hne
    have := exists_card_inter_three i k hik
    omega

@[expose] noncomputable def etaMap (ι : {y // y ≠ x} ≃ Fin 21) (j : Fin 3) (y : X) : Fin 24 :=
  if h : y = x then 2 else φ ((dPerm ^ (j : ℕ)) (ι ⟨y, h⟩))

theorem φ_mem_erase : ∀ p : Fin 21, φ p ∈ X₀.erase 2 := by decide

theorem φ_ne_two (p : Fin 21) : φ p ≠ 2 := (Finset.mem_erase.1 (φ_mem_erase p)).1

theorem φ_mem_X₀ (p : Fin 21) : φ p ∈ X₀ := (Finset.mem_erase.1 (φ_mem_erase p)).2

theorem two_mem_X₀ : (2 : Fin 24) ∈ X₀ := by decide

omit [Fintype X] in
theorem etaMap_mem (j : Fin 3) (y : X) : etaMap ι j y ∈ X₀ := by
  unfold etaMap
  split_ifs
  · exact two_mem_X₀
  · exact φ_mem_X₀ _

omit [Fintype X] in
theorem etaMap_injective (j : Fin 3) : Function.Injective (etaMap ι j) := by
  intro y z h
  unfold etaMap at h
  by_cases hy : y = x <;> by_cases hz : z = x
  · rw [hy, hz]
  · simp only [hy, hz, ↓reduceDIte] at h
    exact absurd h.symm (φ_ne_two _)
  · simp only [hy, hz, ↓reduceDIte] at h
    exact absurd h (φ_ne_two _)
  · simp only [hy, hz, ↓reduceDIte] at h
    exact congrArg Subtype.val (ι.injective ((dPerm ^ (j : ℕ)).injective (φ_injective h)))

omit [Fintype X] in
theorem image_erase_etaMap (j : Fin 3) (B : Finset X) :
    (B.erase x).image (etaMap ι j) =
      ((planeImg ι B).map (dPerm ^ (j : ℕ)).toEmbedding).image φ := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_map_equiv, mem_planeImg]
  constructor
  · rintro ⟨y, ⟨hyx, hy⟩, rfl⟩
    refine ⟨(dPerm ^ (j : ℕ)) (ι ⟨y, hyx⟩), ?_, ?_⟩
    · rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hy
    · simp [etaMap, hyx]
  · rintro ⟨q, hq, rfl⟩
    set p := (dPerm ^ (j : ℕ)).symm q
    have hpq : q = (dPerm ^ (j : ℕ)) p := by simp [p]
    refine ⟨(ι.symm p : X), ⟨(ι.symm p).2, hq⟩, ?_⟩
    simp [etaMap, (ι.symm p).2, hpq]

omit [Fintype X] in
theorem image_etaMap_of_mem (j : Fin 3) {B : Finset X} (hx : x ∈ B) :
    B.image (etaMap ι j) =
      insert 2 (((planeImg ι B).map (dPerm ^ (j : ℕ)).toEmbedding).image φ) := by
  rw [← image_erase_etaMap]
  conv_lhs => rw [← Finset.insert_erase hx]
  rw [Finset.image_insert]
  simp [etaMap]

omit [Fintype X] in
theorem image_etaMap_of_not_mem (j : Fin 3) {B : Finset X} (hx : x ∉ B) :
    B.image (etaMap ι j) = ((planeImg ι B).map (dPerm ^ (j : ℕ)).toEmbedding).image φ := by
  rw [← image_erase_etaMap, Finset.erase_eq_of_notMem hx]

theorem image_φ_filter {B₀ : Finset (Fin 24)} (hB₀ : B₀ ∈ ℬ₀) (h2 : 2 ∉ B₀) :
    (Finset.univ.filter fun p => φ p ∈ B₀).image φ = B₀ := by
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    have hz' : z ∈ X₀.erase 2 :=
      Finset.mem_erase.2 ⟨fun h => h2 (h ▸ hz), (block_spec hB₀).1 hz⟩
    rw [← image_φ] at hz'
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz'
    exact ⟨p, hz, rfl⟩

theorem dPerm_pow_mem_lineAut (j : ℕ) : dPerm ^ j ∈ lineAut := pow_mem dPerm_mem_lineAut j

omit [Fintype X] in
theorem image_etaMap_mem
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine) {i : Fin 3}
    (hi : offImg ι ℬ = O i) {B : Finset X} (hB : B ∈ ℬ) :
    B.image (etaMap ι (2 - i)) ∈ ℬ₀ := by
  have hcoord := mog_derived_design_coordinates
  by_cases hx : x ∈ B
  · rw [image_etaMap_of_mem _ hx]
    obtain ⟨a, ha⟩ := exists_line_of_block hL hB hx
    obtain ⟨b, hb⟩ := dPerm_pow_mem_lineAut ((2 - i : Fin 3) : ℕ) a
    rw [ha, hb]
    have : (projLine b).image φ ∈ Finset.univ.image (fun a => (projLine a).image φ) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ b)
    rw [hcoord.2.2.2.1] at this
    obtain ⟨B₀, hB₀, e⟩ := Finset.mem_image.1 this
    rw [← e, Finset.insert_erase (Finset.mem_filter.1 hB₀).2]
    exact (Finset.mem_filter.1 hB₀).1
  · rw [image_etaMap_of_not_mem _ hx]
    have hA : planeImg ι B ∈ O i := hi ▸ mem_offImg.2 ⟨B, hB, hx, rfl⟩
    have h2 : (planeImg ι B).map (dPerm ^ ((2 - i : Fin 3) : ℕ)).toEmbedding ∈ O 2 := by
      have := setImage_dPerm_pow_O i (2 - i)
      rw [add_sub_cancel] at this
      rw [← this]
      exact Finset.mem_image_of_mem _ hA
    rw [← hcoord.2.2.2.2.1] at h2
    obtain ⟨B₀, hB₀, e⟩ := Finset.mem_image.1 h2
    rw [← e, image_φ_filter (Finset.mem_filter.1 hB₀).1 (Finset.mem_filter.1 hB₀).2]
    exact (Finset.mem_filter.1 hB₀).1

theorem image_univ_etaMap (hD : IsSteiner3Design ℬ) (j : Fin 3) :
    Finset.univ.image (etaMap ι j) = X₀ := by
  refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact etaMap_mem j y
  · rw [Finset.card_image_of_injective _ (etaMap_injective j), Finset.card_univ, hD.1, card_X₀]

theorem derived_plane_design_recognition (hD : IsSteiner3Design ℬ)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine)
    (hG : ∀ g : PSL(3, CFSG.Fischer.F4), ∃ σ ∈ designAut ℬ, σ x = x ∧
      ∀ p, σ (ι.symm p : X) = ι.symm (pslPerm g p)) :
    ∃ j : Fin 3, Function.Injective (etaMap ι j) ∧ Finset.univ.image (etaMap ι j) = X₀ ∧
      ℬ.image (Finset.image (etaMap ι j)) = ℬ₀ ∧
      ∀ B : Finset X, B ∈ ℬ ↔ B.image (etaMap ι j) ∈ ℬ₀ := by
  obtain ⟨i, hi⟩ := offImg_eq_O hD hL hG
  set η := etaMap ι (2 - i)
  have hinj : Function.Injective η := etaMap_injective _
  have hsub : ℬ.image (Finset.image η) ⊆ ℬ₀ := by
    intro B₀ hB₀
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hB₀
    exact image_etaMap_mem hL hi hB
  have heq : ℬ.image (Finset.image η) = ℬ₀ := by
    refine Finset.Subset.antisymm hsub fun B₀ hB₀ => ?_
    obtain ⟨hB₀X, hB₀6⟩ := block_spec hB₀
    obtain ⟨T₀, hT₀, hT₀3⟩ := Finset.exists_subset_card_eq (s := B₀) (n := 3) (by omega)
    set T := Finset.univ.filter fun y => η y ∈ T₀
    have hTT₀ : T.image η = T₀ := by
      ext z
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hz => ?_⟩
      have : z ∈ Finset.univ.image η := by
        rw [image_univ_etaMap hD]
        exact hB₀X (hT₀ hz)
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 this
      exact ⟨y, hz, rfl⟩
    have hT3 : T.card = 3 := by
      rw [← Finset.card_image_of_injective T hinj, hTT₀, hT₀3]
    obtain ⟨B, ⟨hB, hTB⟩, -⟩ := hD.2.2 T hT3
    have hBη := image_etaMap_mem hL hi hB
    obtain ⟨B₁, -, hu⟩ := existsUnique_block (hT₀.trans hB₀X) hT₀3
    have e1 := hu B₀ ⟨hB₀, hT₀⟩
    have e2 := hu _ ⟨hBη, hTT₀ ▸ Finset.image_subset_image hTB⟩
    exact Finset.mem_image.2 ⟨B, hB, e2.trans e1.symm⟩
  refine ⟨2 - i, hinj, image_univ_etaMap hD _, heq, fun B => ⟨fun hB => hsub
    (Finset.mem_image_of_mem _ hB), fun hB => ?_⟩⟩
  rw [← heq] at hB
  obtain ⟨B', hB', e⟩ := Finset.mem_image.1 hB
  rwa [← Finset.image_injective hinj e]

end Recognition

section Bound

variable {X : Type*} [DecidableEq X] {ℬ : Finset (Finset X)} {x : X}

omit [DecidableEq X] in
theorem stab_apply_ne_iff (τ : MulAction.stabilizer (designAut ℬ) x) (y : X) :
    ((τ : designAut ℬ) : Equiv.Perm X) y ≠ x ↔ y ≠ x := by
  have hτ : ((τ : designAut ℬ) : Equiv.Perm X) x = x := MulAction.mem_stabilizer_iff.1 τ.2
  refine not_congr ⟨fun h => ((τ : designAut ℬ) : Equiv.Perm X).injective (h.trans hτ.symm),
    fun h => ?_⟩
  rw [h]
  exact hτ

@[expose] def inducedPerm (ι : {y // y ≠ x} ≃ Fin 21) (τ : MulAction.stabilizer (designAut ℬ) x) :
    Equiv.Perm (Fin 21) :=
  ι.permCongr (((τ : designAut ℬ) : Equiv.Perm X).subtypePerm (stab_apply_ne_iff τ))

omit [DecidableEq X] in
theorem inducedPerm_spec (ι : {y // y ≠ x} ≃ Fin 21)
    (τ : MulAction.stabilizer (designAut ℬ) x) (p : Fin 21) :
    ((τ : designAut ℬ) : Equiv.Perm X) (ι.symm p : X) = ι.symm (inducedPerm ι τ p) := by
  rw [inducedPerm, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rfl

theorem card_stabilizer_le (ι : {y // y ≠ x} ≃ Fin 21)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine)
    (hO : (ℬ.filter (x ∉ ·)).image (planeImg ι) = O 2) :
    Nat.card (MulAction.stabilizer (designAut ℬ) x) ≤ 40320 := by
  have hmapB : ∀ τ : MulAction.stabilizer (designAut ℬ) x, ∀ B : Finset X,
      planeImg ι (B.map ((τ : designAut ℬ) : Equiv.Perm X).toEmbedding) =
        (planeImg ι B).map (inducedPerm ι τ).toEmbedding :=
    fun τ B => planeImg_map ι (inducedPerm_spec ι τ) B
  have hfix : ∀ τ : MulAction.stabilizer (designAut ℬ) x,
      ((τ : designAut ℬ) : Equiv.Perm X) x = x := fun τ => MulAction.mem_stabilizer_iff.1 τ.2
  have hxmap : ∀ τ : MulAction.stabilizer (designAut ℬ) x, ∀ B : Finset X,
      x ∈ B.map ((τ : designAut ℬ) : Equiv.Perm X).toEmbedding ↔ x ∈ B := by
    intro τ B
    rw [Finset.mem_map_equiv]
    have : ((τ : designAut ℬ) : Equiv.Perm X).symm x = x := by
      rw [Equiv.symm_apply_eq, hfix τ]
    rw [this]
  have hline : ∀ τ : MulAction.stabilizer (designAut ℬ) x, inducedPerm ι τ ∈ lineAut := by
    intro τ a
    obtain ⟨B, hB, hx, hBa⟩ := exists_block_of_line hL a
    have hmem : planeImg ι (B.map ((τ : designAut ℬ) : Equiv.Perm X).toEmbedding) ∈
        Finset.univ.image projLine :=
      hL ▸ Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨((τ : designAut ℬ).2 B).2 hB,
        (hxmap τ B).2 hx⟩)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hmem
    exact ⟨b, by rw [← hBa, ← hmapB, hb]⟩
  have hset : ∀ τ : MulAction.stabilizer (designAut ℬ) x,
      setImage (inducedPerm ι τ) (O 2) = O 2 := by
    intro τ
    refine Finset.eq_of_subset_of_card_le (fun A hA => ?_) (by rw [card_setImage])
    obtain ⟨A₀, hA₀, rfl⟩ := Finset.mem_image.1 hA
    rw [← hO] at hA₀ ⊢
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA₀
    rw [← hmapB]
    have hB' := Finset.mem_filter.1 hB
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨((τ : designAut ℬ).2 B).2 hB'.1,
      fun h => hB'.2 ((hxmap τ B).1 h)⟩)
  let F : MulAction.stabilizer (designAut ℬ) x → {σ : lineAut // setImage σ (O 2) = O 2} :=
    fun τ => ⟨⟨inducedPerm ι τ, hline τ⟩, hset τ⟩
  have hF : Function.Injective F := by
    intro τ τ' h
    have h' : inducedPerm ι τ = inducedPerm ι τ' :=
      congrArg (fun z => (z.1 : Equiv.Perm (Fin 21))) h
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext
    intro y
    by_cases hy : y = x
    · rw [hy, hfix τ, hfix τ']
    · have e1 := inducedPerm_spec ι τ (ι ⟨y, hy⟩)
      have e2 := inducedPerm_spec ι τ' (ι ⟨y, hy⟩)
      rw [Equiv.symm_apply_apply] at e1 e2
      rw [e1, e2, h']
  exact (Nat.card_le_card_of_injective F hF).trans (card_stab_O_le 2)

theorem card_designAut_le [Fintype X] (ι : {y // y ≠ x} ≃ Fin 21)
    (hL : (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine)
    (hO : (ℬ.filter (x ∉ ·)).image (planeImg ι) = O 2) :
    Nat.card (designAut ℬ) ≤ Fintype.card X * 40320 := by
  have h := (MulAction.stabilizer (designAut ℬ) x).card_mul_index
  rw [MulAction.index_stabilizer] at h
  rw [← h, mul_comm]
  refine Nat.mul_le_mul ?_ (card_stabilizer_le ι hL hO)
  calc (MulAction.orbit (designAut ℬ) x).ncard ≤ (Set.univ : Set X).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = Fintype.card X := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

end Bound

section Mog

theorem mem_X₀_iff : ∀ i : Fin 24, i ∈ X₀ ↔ i ≠ 0 ∧ i ≠ 1 := by decide

@[expose] noncomputable def ℬ₀X : Finset (Finset X₀) := ℬ₀.image (Finset.subtype (· ∈ X₀))

theorem subtype_map_subtype (C : Finset X₀) :
    (C.map (Function.Embedding.subtype (· ∈ X₀))).subtype (· ∈ X₀) = C := by
  ext a; simp

theorem mem_ℬ₀X {C : Finset X₀} :
    C ∈ ℬ₀X ↔ C.map (Function.Embedding.subtype (· ∈ X₀)) ∈ ℬ₀ := by
  constructor
  · intro h
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 h
    rwa [Finset.subtype_map_of_mem fun i hi => (block_spec hB).1 hi]
  · intro h
    exact Finset.mem_image.2 ⟨_, h, subtype_map_subtype C⟩

theorem map_mem_octads {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm) {O : Finset (Fin 24)}
    (hO : O ∈ octads) : O.map p.toEmbedding ∈ octads := by
  obtain ⟨w, hw, h8, rfl⟩ := mem_octads.1 hO
  refine mem_octads.2 ⟨permWord p w, permWord_mem_of_mem_AutPerm hp hw, ?_, ?_⟩
  · rw [permWord, hammingNorm_comp_perm, h8]
  · ext i
    rw [mem_suppFin, Finset.mem_map_equiv, mem_suppFin]
    rfl

theorem map_mem_octads_iff {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm) {O : Finset (Fin 24)} :
    O.map p.toEmbedding ∈ octads ↔ O ∈ octads := by
  refine ⟨fun h => ?_, map_mem_octads hp⟩
  have := map_mem_octads (inv_mem hp) h
  rwa [← map_perm_mul, inv_mul_cancel, map_perm_one] at this

theorem mem_ℬ₀_iff_insert {B : Finset (Fin 24)} (h0 : (0 : Fin 24) ∉ B) (h1 : (1 : Fin 24) ∉ B) :
    B ∈ ℬ₀ ↔ insert 0 (insert 1 B) ∈ octads := by
  rw [mem_ℬ₀]
  constructor
  · rintro ⟨O, hO, h0O, h1O, rfl⟩
    convert hO using 1
    ext i
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | ⟨h, -⟩)
      · exact h0O
      · exact h1O
      · exact h
    · intro hi
      by_cases e0 : i = 0
      · exact Or.inl e0
      by_cases e1 : i = 1
      · exact Or.inr (Or.inl e1)
      exact Or.inr (Or.inr ⟨hi, fun h => h.elim e0 e1⟩)
  · intro h
    refine ⟨_, h, by simp, by simp, ?_⟩
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h | h, hn⟩
      · exact absurd (Or.inl h) hn
      · exact absurd (Or.inr h) hn
      · exact h
    · intro hi
      refine ⟨Or.inr (Or.inr hi), ?_⟩
      rintro (rfl | rfl)
      · exact h0 hi
      · exact h1 hi

abbrev pPerm (p : Ppair) : Equiv.Perm (Fin 24) := ((p : AutPerm) : Equiv.Perm (Fin 24))

theorem pPerm_mem_X₀ (p : Ppair) (i : Fin 24) : pPerm p i ∈ X₀ ↔ i ∈ X₀ := by
  rw [mem_X₀_iff, mem_X₀_iff]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · rcases Ppair_apply_mem p.2 (Or.inl h0) with e | e
      · exact h.1 e
      · exact h.2 e
    · rcases Ppair_apply_mem p.2 (Or.inr h1) with e | e
      · exact h.1 e
      · exact h.2 e
  · rintro ⟨h0, h1⟩
    exact Ppair_apply_ne p.2 h0 h1

theorem Ppair_map_insert (p : Ppair) (B : Finset (Fin 24)) :
    (insert 0 (insert 1 B)).map (pPerm p).toEmbedding =
      insert 0 (insert 1 (B.map (pPerm p).toEmbedding)) := by
  rw [Finset.map_insert, Finset.map_insert]
  change insert (pPerm p 0) (insert (pPerm p 1) _) = _
  rcases (mem_Ppair_iff (p : AutPerm)).1 p.2 with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [e0, e1]
  · rw [e0, e1, Finset.insert_comm]

theorem subset_X₀_iff {S : Finset (Fin 24)} : S ⊆ X₀ ↔ (0 : Fin 24) ∉ S ∧ (1 : Fin 24) ∉ S := by
  constructor
  · intro h
    exact ⟨fun h0 => ((mem_X₀_iff 0).1 (h h0)).1 rfl, fun h1 => ((mem_X₀_iff 1).1 (h h1)).2 rfl⟩
  · rintro ⟨h0, h1⟩ i hi
    exact (mem_X₀_iff i).2 ⟨fun e => h0 (e ▸ hi), fun e => h1 (e ▸ hi)⟩

theorem map_mem_ℬ₀_iff (p : Ppair) {B : Finset (Fin 24)} (hB : B ⊆ X₀) :
    B.map (pPerm p).toEmbedding ∈ ℬ₀ ↔ B ∈ ℬ₀ := by
  have hB' : B.map (pPerm p).toEmbedding ⊆ X₀ := by
    intro i hi
    rw [Finset.mem_map_equiv] at hi
    have := hB hi
    rwa [← pPerm_mem_X₀ p, Equiv.apply_symm_apply] at this
  rw [mem_ℬ₀_iff_insert (subset_X₀_iff.1 hB').1 (subset_X₀_iff.1 hB').2,
    mem_ℬ₀_iff_insert (subset_X₀_iff.1 hB).1 (subset_X₀_iff.1 hB).2, ← Ppair_map_insert]
  exact map_mem_octads_iff (p : AutPerm).2

@[expose] def resHom : Ppair →* Equiv.Perm X₀ where
  toFun p := (pPerm p).subtypePerm (pPerm_mem_X₀ p)
  map_one' := Equiv.ext fun _ => rfl
  map_mul' _ _ := Equiv.ext fun _ => rfl

theorem resHom_apply (p : Ppair) (i : X₀) : (resHom p i : Fin 24) = pPerm p i := rfl

theorem map_resHom (p : Ppair) (C : Finset X₀) :
    (C.map (resHom p).toEmbedding).map (Function.Embedding.subtype (· ∈ X₀)) =
      (C.map (Function.Embedding.subtype (· ∈ X₀))).map (pPerm p).toEmbedding := by
  rw [Finset.map_map, Finset.map_map]
  rfl

theorem map_subtype_subset_X₀ (C : Finset X₀) :
    C.map (Function.Embedding.subtype (· ∈ X₀)) ⊆ X₀ := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
  exact j.2

theorem resHom_mem (p : Ppair) : resHom p ∈ designAut ℬ₀X := by
  intro C
  rw [mem_ℬ₀X, mem_ℬ₀X, map_resHom]
  exact map_mem_ℬ₀_iff p (map_subtype_subset_X₀ C)

theorem resHom_injective : Function.Injective resHom := by
  rw [injective_iff_map_eq_one]
  intro p hp
  refine native_pair_stabilizer_two_core_trivial.2.2.2.1 p fun i h0 h1 => ?_
  have hi : i ∈ X₀ := (mem_X₀_iff i).2 ⟨h0, h1⟩
  exact congrArg (fun σ : Equiv.Perm X₀ => (σ ⟨i, hi⟩ : Fin 24)) hp

@[expose] noncomputable def resAut : Ppair →* designAut ℬ₀X := resHom.codRestrict _ resHom_mem

theorem resAut_injective : Function.Injective resAut := fun _ _ h =>
  resHom_injective (congrArg Subtype.val h)

@[expose] def φX (p : Fin 21) : {y : X₀ // y ≠ pt 2} :=
  ⟨⟨φ p, φ_mem_X₀ p⟩, fun h => φ_ne_two p (congrArg Subtype.val h)⟩

theorem φX_bijective : Function.Bijective φX := by
  refine ⟨fun p q h => φ_injective (congrArg (fun y => ((y.1 : X₀) : Fin 24)) h), ?_⟩
  rintro ⟨⟨z, hz⟩, hz2⟩
  have : z ∈ X₀.erase 2 := Finset.mem_erase.2 ⟨fun h => hz2 (Subtype.ext h), hz⟩
  rw [← image_φ] at this
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 this
  exact ⟨p, rfl⟩

@[expose] noncomputable def ι₀ : {y : X₀ // y ≠ pt 2} ≃ Fin 21 :=
  (Equiv.ofBijective φX φX_bijective).symm

theorem ι₀_symm_apply (p : Fin 21) : ι₀.symm p = φX p := by
  rw [ι₀, Equiv.symm_symm]
  rfl

theorem planeImg_ι₀ (C : Finset X₀) :
    planeImg ι₀ C =
      Finset.univ.filter fun p => φ p ∈ C.map (Function.Embedding.subtype (· ∈ X₀)) := by
  ext p
  rw [mem_planeImg, ι₀_symm_apply]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coe_subtype]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    have : y = (φX p : X₀) := Subtype.ext e
    rwa [← this]

theorem image_ℬ₀X (P : Finset (Fin 24) → Prop) [DecidablePred P] :
    (ℬ₀X.filter fun C => P (C.map (Function.Embedding.subtype (· ∈ X₀)))).image (planeImg ι₀) =
      (ℬ₀.filter P).image fun B => Finset.univ.filter fun p => φ p ∈ B := by
  ext S
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨C, ⟨hC, hP⟩, rfl⟩
    exact ⟨_, ⟨mem_ℬ₀X.1 hC, hP⟩, (planeImg_ι₀ C).symm⟩
  · rintro ⟨B, ⟨hB, hP⟩, rfl⟩
    have hBX : ∀ i ∈ B, i ∈ X₀ := fun i hi => (block_spec hB).1 hi
    refine ⟨B.subtype (· ∈ X₀), ⟨Finset.mem_image_of_mem _ hB, ?_⟩, ?_⟩
    · rwa [Finset.subtype_map_of_mem hBX]
    · rw [planeImg_ι₀, Finset.subtype_map_of_mem hBX]

theorem mem_pt_two_iff (C : Finset X₀) :
    pt 2 ∈ C ↔ (2 : Fin 24) ∈ C.map (Function.Embedding.subtype (· ∈ X₀)) := by
  rw [Finset.mem_map]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    have : y = pt 2 := Subtype.ext e
    rwa [← this]

theorem filter_φ_image (A : Finset (Fin 21)) :
    (Finset.univ.filter fun p => φ p ∈ A.image φ) = A := by
  ext p
  simp [φ_injective.eq_iff]

theorem filter_φ_erase (B : Finset (Fin 24)) :
    (Finset.univ.filter fun p => φ p ∈ B.erase 2) = Finset.univ.filter fun p => φ p ∈ B := by
  ext p
  simp [φ_ne_two]

theorem lines_ℬ₀X :
    (ℬ₀X.filter (pt 2 ∈ ·)).image (planeImg ι₀) = Finset.univ.image projLine := by
  have h := congrArg (Finset.image fun B => Finset.univ.filter fun p => φ p ∈ B)
    mog_derived_design_coordinates.2.2.2.1
  simp only [Finset.image_image, Function.comp_def, filter_φ_image, filter_φ_erase] at h
  rw [h, ← image_ℬ₀X]
  congr 1
  exact Finset.filter_congr fun C _ => mem_pt_two_iff C

theorem hyperovals_ℬ₀X :
    (ℬ₀X.filter (pt 2 ∉ ·)).image (planeImg ι₀) = O 2 := by
  rw [← mog_derived_design_coordinates.2.2.2.2.1, ← image_ℬ₀X]
  congr 1
  exact Finset.filter_congr fun C _ => not_congr (mem_pt_two_iff C)

theorem card_designAut_ℬ₀X_le :
    Nat.card (designAut ℬ₀X) ≤ 887040 := by
  have h := card_designAut_le ι₀ lines_ℬ₀X hyperovals_ℬ₀X
  rwa [Fintype.card_coe, card_X₀] at h

theorem resAut_bijective :
    Function.Bijective resAut :=
  resAut_injective.bijective_of_nat_card_le (by rw [natCard_Ppair]; exact card_designAut_ℬ₀X_le)

theorem psiHom_mem_X₀ (g : Equiv.Perm (Fin 22)) (i : Fin 24) : psiHom g i ∈ X₀ ↔ i ∈ X₀ := by
  rw [mem_X₀_iff, mem_X₀_iff]
  have hinj := (psiHom g).injective
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun e => h0 (e ▸ psiHom_zero g), fun e => h1 (e ▸ psiHom_one g)⟩
  · rintro ⟨h0, h1⟩
    exact ⟨fun e => h0 (hinj (e.trans (psiHom_zero g).symm)),
      fun e => h1 (hinj (e.trans (psiHom_one g).symm))⟩

@[expose] def psiX : Equiv.Perm (Fin 22) →* Equiv.Perm X₀ where
  toFun g := (psiHom g).subtypePerm (psiHom_mem_X₀ g)
  map_one' := Equiv.ext fun i => Subtype.ext (by
    change psiHom 1 i = i
    rw [map_one]
    rfl)
  map_mul' g h := Equiv.ext fun i => Subtype.ext (by
    change psiHom (g * h) i = psiHom g (psiHom h i)
    rw [map_mul]
    rfl)

theorem psiX_apply (g : Equiv.Perm (Fin 22)) (i : X₀) : (psiX g i : Fin 24) = psiHom g i := rfl

theorem map_P0in_resHom :
    P0in.map resHom = (CFSG.Blueprint.NativeSporadic.M22).map psiX := by
  ext σ
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [SetLike.mem_coe, P0in, Subgroup.mem_subgroupOf, ← range_psiM] at hp
    obtain ⟨g, hg⟩ := hp
    refine ⟨g, g.2, Equiv.ext fun i => Subtype.ext ?_⟩
    rw [psiX_apply, resHom_apply, pPerm, ← hg, coe_psiM]
  · rintro ⟨g, hg, rfl⟩
    have hmem : psiM ⟨g, hg⟩ ∈ P0 := range_psiM ▸ ⟨_, rfl⟩
    refine ⟨⟨psiM ⟨g, hg⟩, P0_le_Ppair hmem⟩, ?_, Equiv.ext fun i => Subtype.ext ?_⟩
    · rw [SetLike.mem_coe, P0in, Subgroup.mem_subgroupOf]
      exact hmem
    · rw [psiX_apply, resHom_apply, pPerm, coe_psiM]

theorem derived_design_automorphism_group :
    (∀ p : Ppair, resHom p ∈ designAut ℬ₀X) ∧
    (∃ e : Ppair ≃* designAut ℬ₀X, ∀ p i, (((e p : designAut ℬ₀X) : Equiv.Perm X₀) i : Fin 24) =
      ((p : AutPerm) : Equiv.Perm (Fin 24)) i) ∧
    Nat.card (designAut ℬ₀X) = 887040 ∧
    P0in.map resHom = (CFSG.Blueprint.NativeSporadic.M22).map psiX ∧
    (∃ e : CFSG.Blueprint.NativeSporadic.M22 ≃* P0, ∀ g,
      (((e g : P0) : AutPerm) : Equiv.Perm (Fin 24)) = psiHom g) ∧
    P0in.index = 2 := by
  refine ⟨resHom_mem, ⟨MulEquiv.ofBijective resAut resAut_bijective, fun p i => rfl⟩, ?_,
    map_P0in_resHom, ⟨m22EquivP0, coe_m22EquivP0⟩, index_P0in⟩
  rw [← Nat.card_congr (MulEquiv.ofBijective resAut resAut_bijective).toEquiv, natCard_Ppair]

end Mog

universe u in
theorem twenty_two_derived_plane_design_recognition :
    (∀ (X : Type u) [Fintype X] [DecidableEq X] (ℬ : Finset (Finset X)) (x : X)
      (ι : {y // y ≠ x} ≃ Fin 21), IsSteiner3Design ℬ →
      (ℬ.filter (x ∈ ·)).image (planeImg ι) = Finset.univ.image projLine →
      (∀ g : PSL(3, CFSG.Fischer.F4), ∃ σ ∈ designAut ℬ, σ x = x ∧
        ∀ p, σ (ι.symm p : X) = ι.symm (pslPerm g p)) →
      ∃ j : Fin 3, Function.Injective (etaMap ι j) ∧ Finset.univ.image (etaMap ι j) = X₀ ∧
        ℬ.image (Finset.image (etaMap ι j)) = ℬ₀ ∧
        ∀ B : Finset X, B ∈ ℬ ↔ B.image (etaMap ι j) ∈ ℬ₀) ∧
    (∀ p : Ppair, resHom p ∈ designAut ℬ₀X) ∧
    (∃ e : Ppair ≃* designAut ℬ₀X, ∀ p i, (((e p : designAut ℬ₀X) : Equiv.Perm X₀) i : Fin 24) =
      ((p : AutPerm) : Equiv.Perm (Fin 24)) i) ∧
    Nat.card (designAut ℬ₀X) = 887040 ∧
    P0in.map resHom = (CFSG.Blueprint.NativeSporadic.M22).map psiX ∧
    (∃ e : CFSG.Blueprint.NativeSporadic.M22 ≃* P0, ∀ g,
      (((e g : P0) : AutPerm) : Equiv.Perm (Fin 24)) = psiHom g) ∧
    P0in.index = 2 :=
  ⟨fun _ _ _ _ _ _ hD hL hG => derived_plane_design_recognition hD hL hG,
    derived_design_automorphism_group⟩

end CFSG.Monster.B.Fischer
