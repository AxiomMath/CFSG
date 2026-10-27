module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagBuilding
public import CFSG.LocalAnalysis.StandardType.PhanEClassify
import CFSG.LocalAnalysis.StandardType.PhanEDMBuilding
import CFSG.LocalAnalysis.StandardType.PhanEGateDouble

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι ι' C D : Type}

@[expose] noncomputable def cdist (X : ChamberSystem ι C) (x y : C) : ℕ :=
  sInf {k | ∃ γ : List (ι × C), X.IsGallery x γ ∧ γ.length = k ∧ galleryEnd x γ = y}

@[expose] def IsGateAt (X : ChamberSystem ι C) (R₀ : Set C) (y g : C) : Prop :=
  g ∈ R₀ ∧ ∀ z ∈ R₀, cdist X y z = cdist X y g + cdist X g z

@[expose] def IntrSet (X : ChamberSystem ι C) (R₀ : Set C) (ψ : C → C) (D : ℕ) : Set C :=
  {y | ∃ g ∈ R₀, IsGateAt X R₀ y g ∧ cdist X y (ψ g) = D}

private theorem p9uFL_cdist_le {X : ChamberSystem ι C} {x y : C} {γ : List (ι × C)}
    (hγ : X.IsGallery x γ) (he : galleryEnd x γ = y) : cdist X x y ≤ γ.length :=
  Nat.sInf_le ⟨γ, hγ, rfl, he⟩

private theorem p9uFL_exists_min_gallery {X : ChamberSystem ι C} (hX : X.Connected) (x y : C) :
    ∃ γ : List (ι × C), X.IsGallery x γ ∧ γ.length = cdist X x y ∧ galleryEnd x γ = y := by
  obtain ⟨γ, hγ, hend⟩ := hX x y
  have hne : {k | ∃ γ : List (ι × C), X.IsGallery x γ ∧ γ.length = k ∧
      galleryEnd x γ = y}.Nonempty := ⟨γ.length, γ, hγ, rfl, hend⟩
  obtain ⟨η, hη, hlen, hendη⟩ := Nat.sInf_mem hne
  exact ⟨η, hη, hlen, hendη⟩

theorem cdist_self (X : ChamberSystem ι C) (x : C) : cdist X x x = 0 := by
  exact Nat.le_zero.mp (p9uFL_cdist_le (X := X) (x := x) (y := x)
    (ChamberSystem.isGallery_nil x) rfl)

theorem cdist_eq_zero_iff (X : ChamberSystem ι C) (hX : X.Connected) {x y : C} :
    cdist X x y = 0 ↔ x = y := by
  constructor
  · intro h
    obtain ⟨γ, hγ, hend⟩ := hX x y
    have hne : {k | ∃ γ : List (ι × C), X.IsGallery x γ ∧ γ.length = k ∧
        galleryEnd x γ = y}.Nonempty := ⟨γ.length, γ, hγ, rfl, hend⟩
    obtain ⟨η, hη, hlen, hendη⟩ := Nat.sInf_mem hne
    have hlen0 : η.length = 0 := by rw [hlen]; exact h
    have hnil : η = [] := List.eq_nil_of_length_eq_zero hlen0
    rw [hnil] at hendη
    simpa using hendη
  · rintro rfl
    exact cdist_self X x

theorem IsGateAt.unique {X : ChamberSystem ι C} (hX : X.Connected) {R₀ : Set C} {y g g' : C}
    (h : IsGateAt X R₀ y g) (h' : IsGateAt X R₀ y g') : g = g' := by
  have h1 := h.2 g' h'.1
  have h2 := h'.2 g h.1
  have hzero : cdist X g g' = 0 := by omega
  exact (cdist_eq_zero_iff X hX).mp hzero

private theorem p9uFL_length_le_gallery {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {E : Type} {δ : E → E → W}
    (hB : IsWeylDistanceBuilding cs δ)
    {E' : Type} {ι' : Type} {X : ChamberSystem ι' E'} (f : E' → E) {e : ι' → ι}
    (hadj : ∀ i x y, X.adj i x y ↔ δ (f x) (f y) = 1 ∨ δ (f x) (f y) = cs.simple (e i))
    {x : E'} {γ : List (ι' × E')} (hγ : X.IsGallery x γ) :
    cs.length (δ (f x) (f (galleryEnd x γ))) ≤ γ.length := by
  induction γ generalizing x with
  | nil => simp [hB.eq_one_self (f x)]
  | cons p γ ih =>
    obtain ⟨hadj1, hgal⟩ := hγ
    rcases (hadj p.1 x p.2).mp hadj1 with h1 | h1
    · have hx : f x = f p.2 := (hB.eq_one_iff (f x) (f p.2)).mp h1
      rw [hx]
      simpa only [galleryEnd_cons, List.length_cons] using
        Nat.le_trans (ih (x := p.2) hgal) (Nat.le_succ γ.length)
    · have hstep : cs.length (δ (f x) (f (galleryEnd p.2 γ))) ≤
          cs.length (δ (f p.2) (f (galleryEnd p.2 γ))) + 1 := by
        rcases CFSG.ClassicalInvolution.Phan.PhanE.Gate.dist_mul_simple_left hB h1 with h | h
        · rw [h]; omega
        · calc cs.length (δ (f x) (f (galleryEnd p.2 γ)))
              = cs.length ((cs.simple (e p.1))⁻¹ * δ (f p.2) (f (galleryEnd p.2 γ))) := by
                rw [h, inv_mul_cancel_left]
            _ ≤ cs.length ((cs.simple (e p.1))⁻¹) +
                  cs.length (δ (f p.2) (f (galleryEnd p.2 γ))) := cs.length_mul_le _ _
            _ = cs.length (δ (f p.2) (f (galleryEnd p.2 γ))) + 1 := by
                rw [cs.length_inv, cs.length_simple]; omega
      simpa only [galleryEnd_cons, List.length_cons] using
        Nat.le_trans hstep (Nat.succ_le_succ (ih (x := p.2) hgal))

private theorem p9uFL_exists_gallery_of_isStrictGallery {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {E : Type} {δ : E → E → W}
    (hB : IsWeylDistanceBuilding cs δ)
    {ι' : Type} {X : ChamberSystem ι' E} {e : ι' → ι}
    (hadj : ∀ i x y, X.adj i x y ↔ δ x y = 1 ∨ δ x y = cs.simple (e i))
    {x : E} {γ : List (ι × E)} (hγ : IsStrictGallery cs δ x γ)
    (hf : ∀ i ∈ galleryType γ, ∃ i' : ι', e i' = i) :
    ∃ γ' : List (ι' × E), X.IsGallery x γ' ∧ γ'.length = γ.length ∧
      galleryEnd x γ' = galleryEnd x γ := by
  induction γ generalizing x with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨i', hi'⟩ := hf p.1 (by simp)
    have hf' : ∀ i ∈ galleryType γ, ∃ i' : ι', e i' = i := fun i hi => hf i (by simp [hi])
    obtain ⟨γ', hγ'g, hγ'len, hγ'end⟩ := ih (x := p.2) h2 hf'
    refine ⟨(i', p.2) :: γ', ⟨?_, hγ'g⟩, by simp [hγ'len], by simpa using hγ'end⟩
    exact (hadj i' x p.2).mpr (Or.inr (by rw [hi']; exact h1))

private theorem p9uFL_length_eq_cdist {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {E : Type} {δ : E → E → W}
    (hB : IsWeylDistanceBuilding cs δ)
    {E' : Type} {ι' : Type} {X : ChamberSystem ι' E'} (f : E' → E) {e : ι' → ι}
    (hadj : ∀ i x y, X.adj i x y ↔ δ (f x) (f y) = 1 ∨ δ (f x) (f y) = cs.simple (e i))
    {x y : E'} {γ : List (ι' × E')} (hγ : X.IsGallery x γ)
    (hlen : γ.length = cs.length (δ (f x) (f y))) (hend : galleryEnd x γ = y) :
    cs.length (δ (f x) (f y)) = cdist X x y := by
  have hne : {k | ∃ γ : List (ι' × E'), X.IsGallery x γ ∧ γ.length = k ∧
      galleryEnd x γ = y}.Nonempty := ⟨γ.length, γ, hγ, rfl, hend⟩
  obtain ⟨η, hη, hlenη, hendη⟩ := Nat.sInf_mem hne
  have hle : cdist X x y ≤ cs.length (δ (f x) (f y)) := by
    have hmem : γ.length ∈ {k | ∃ γ : List (ι' × E'), X.IsGallery x γ ∧ γ.length = k ∧
        galleryEnd x γ = y} := ⟨γ, hγ, rfl, hend⟩
    have := Nat.sInf_le hmem
    rwa [hlen] at this
  have hge : cs.length (δ (f x) (f y)) ≤ cdist X x y := by
    have h := p9uFL_length_le_gallery hB f hadj hη
    rw [hendη] at h
    rwa [hlenη] at h
  exact le_antisymm hge hle

private theorem p9uFL_exists_gallery_restrict {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {E : Type} {δ : E → E → W} (hB : IsWeylDistanceBuilding cs δ)
    (J : Set ι) (a : E) {x : E} {γ : List (ι × E)}
    (hx : x ∈ residue cs δ J a) (hγ : IsStrictGallery cs δ x γ)
    (hR : ∀ p ∈ γ, p.2 ∈ residue cs δ J a)
    (hJ : ∀ i ∈ galleryType γ, i ∈ J) :
    ∃ γ' : List (↥J × ↥(residue cs δ J a)),
      ((buildingOver cs δ J).restrict (residue cs δ J a)).IsGallery ⟨x, hx⟩ γ' ∧
      γ'.length = γ.length ∧
      ((galleryEnd ⟨x, hx⟩ γ' : ↥(residue cs δ J a)) : E) = galleryEnd x γ := by
  induction γ generalizing x with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have hpJ : p.1 ∈ J := hJ p.1 (by simp)
    have hpR : p.2 ∈ residue cs δ J a := hR p (by simp)
    have hR' : ∀ q ∈ γ, q.2 ∈ residue cs δ J a := fun q hq => hR q (by simp [hq])
    have hJ' : ∀ i ∈ galleryType γ, i ∈ J := fun i hi => hJ i (by simp [hi])
    obtain ⟨γ', hγ'g, hγ'len, hγ'end⟩ := ih (x := p.2) hpR h2 hR' hJ'
    refine ⟨(⟨p.1, hpJ⟩, ⟨p.2, hpR⟩) :: γ', ⟨?_, hγ'g⟩,
      by simp [hγ'len], by simpa using hγ'end⟩
    change Relation.EqvGen (fun a b : E => δ a b = cs.simple p.1) x p.2
    exact Relation.EqvGen.rel x p.2 h1

theorem length_dist_eq_cdist {M : CoxeterMatrix ι} {W : Type} [Group W]
    {cs : CoxeterSystem M W} {δ : C → C → W} (hB : IsWeylDistanceBuilding cs δ)
    (J : Set ι) (a : C) {x y : C} (hx : x ∈ residue cs δ J a) (hy : y ∈ residue cs δ J a) :
    cs.length (δ x y) =
      cdist ((buildingOver cs δ J).restrict (residue cs δ J a)) ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced (δ x y)
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hB hω hprod.symm
  have hpar : δ x y ∈ cs.parabolic J := by
    have hxr : y ∈ residue cs δ J x := by rw [residue_eq_of_mem hB hx]; exact hy
    exact mem_parabolic_of_mem_residue hB (self_mem_residue J x) hxr
  have hJ : ∀ i ∈ galleryType γ, i ∈ J := by
    intro i hi
    rw [htype] at hi
    exact mem_of_isReduced_of_mem_parabolic cs hω (by rw [← hprod]; exact hpar) hi
  have hR : ∀ p ∈ γ, p.2 ∈ residue cs δ J a := by
    have hRx := IsStrictGallery.mem_residue hγ hJ
    intro p hp
    rw [← residue_eq_of_mem hB hx]
    exact hRx p hp
  obtain ⟨γ', hγ'g, hγ'len, hγ'end⟩ :=
    p9uFL_exists_gallery_restrict hB J a hx hγ hR hJ
  have hadj : ∀ (j : ↥J) (u v : ↥(residue cs δ J a)),
      ((buildingOver cs δ J).restrict (residue cs δ J a)).adj j u v ↔
        δ u.1 v.1 = 1 ∨ δ u.1 v.1 = cs.simple ((j : ι)) := by
    intro j u v
    change (buildingSystem cs δ).adj (j : ι) u.1 v.1 ↔
      δ u.1 v.1 = 1 ∨ δ u.1 v.1 = cs.simple (j : ι)
    exact buildingSystem_adj_iff hB
  have hlen : γ'.length = cs.length (δ x y) := by
    rw [hγ'len, ← length_galleryType γ, htype, ← hω, hprod]
  have hend' : galleryEnd ⟨x, hx⟩ γ' = ⟨y, hy⟩ := by
    apply Subtype.ext
    rw [hγ'end, hend]
  exact p9uFL_length_eq_cdist hB Subtype.val hadj hγ'g hlen hend'

theorem length_flagδ_eq_cdist {K : Type} [Field K] (m : ℕ) (E F : FlagK K (m + 1)) :
    (symCox m).length (flagδ m E F) = cdist (flagSys K m) E F := by
  have hB : IsWeylDistanceBuilding (symCox m) (flagδ (K := K) m) :=
    isWeylDistanceBuilding_flag (K := K) (m := m)
  have hadj : ∀ (i : Fin m) (x y : FlagK K (m + 1)),
      (flagSys K m).adj i x y ↔ flagδ m x y = 1 ∨
        flagδ m x y = (symCox m).simple ((id : Fin m → Fin m) i) := by
    intro i x y
    simpa using flagSys_adj_iff (K := K) (m := m) i x y
  obtain ⟨ω, hω, hprod⟩ := (symCox m).exists_isReduced (flagδ m E F)
  obtain ⟨γ, hγ, htype, hend⟩ := exists_strictGallery hB hω hprod.symm
  have hf : ∀ i ∈ galleryType γ, ∃ i' : Fin m, (id i' : Fin m) = i := fun i _ => ⟨i, rfl⟩
  obtain ⟨γ', hγ'g, hγ'len, hγ'end⟩ :=
    p9uFL_exists_gallery_of_isStrictGallery hB hadj hγ hf
  have hlen : γ'.length = (symCox m).length (flagδ m E F) := by
    rw [hγ'len, ← length_galleryType γ, htype, ← hω, hprod]
  have hend' : galleryEnd E γ' = F := by rw [hγ'end, hend]
  exact p9uFL_length_eq_cdist hB id hadj hγ'g hlen hend'

private def p9uFL_relabel {X : ChamberSystem ι C} {Y : ChamberSystem ι' D} (Θ : ChamberIso X Y)
    (γ : List (ι × C)) : List (ι' × D) :=
  γ.map fun p => (Θ.e p.1, Θ.Φ p.2)

private theorem p9uFL_length_relabel {X : ChamberSystem ι C} {Y : ChamberSystem ι' D}
    (Θ : ChamberIso X Y) (γ : List (ι × C)) :
    (p9uFL_relabel Θ γ).length = γ.length := List.length_map ..

private theorem p9uFL_galleryEnd_relabel {X : ChamberSystem ι C} {Y : ChamberSystem ι' D}
    (Θ : ChamberIso X Y) (x : C) (γ : List (ι × C)) :
    galleryEnd (Θ.Φ x) (p9uFL_relabel Θ γ) = Θ.Φ (galleryEnd x γ) := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => exact ih p.2

private theorem p9uFL_isGallery_relabel {X : ChamberSystem ι C} {Y : ChamberSystem ι' D}
    (Θ : ChamberIso X Y) {x : C} {γ : List (ι × C)} (hγ : X.IsGallery x γ) :
    Y.IsGallery (Θ.Φ x) (p9uFL_relabel Θ γ) := by
  induction γ generalizing x with
  | nil => trivial
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    exact ⟨(Θ.adj_iff p.1 x p.2).mp h1, ih h2⟩

private def p9uFL_symm {X : ChamberSystem ι C} {Y : ChamberSystem ι' D}
    (Θ : ChamberIso X Y) : ChamberIso Y X where
  e := Θ.e.symm
  Φ := Θ.Φ.symm
  adj_iff := by
    intro i x y
    have h := Θ.adj_iff (Θ.e.symm i) (Θ.Φ.symm x) (Θ.Φ.symm y)
    simpa using h.symm

theorem cdist_chamberIso {X : ChamberSystem ι C} {Y : ChamberSystem ι' D} (Θ : ChamberIso X Y)
    (x y : C) : cdist Y (Θ.Φ x) (Θ.Φ y) = cdist X x y := by
  have hset : {k : ℕ | ∃ γ : List (ι' × D), Y.IsGallery (Θ.Φ x) γ ∧ γ.length = k ∧
        galleryEnd (Θ.Φ x) γ = Θ.Φ y} =
      {k : ℕ | ∃ γ : List (ι × C), X.IsGallery x γ ∧ γ.length = k ∧
        galleryEnd x γ = y} := by
    ext k
    constructor
    · rintro ⟨γ, hγ, hlen, hend⟩
      refine ⟨p9uFL_relabel (p9uFL_symm Θ) γ, ?_, ?_, ?_⟩
      · have h' := p9uFL_isGallery_relabel (p9uFL_symm Θ) hγ
        rw [show (p9uFL_symm Θ).Φ = Θ.Φ.symm from rfl, Equiv.symm_apply_apply] at h'
        exact h'
      · rw [p9uFL_length_relabel, hlen]
      · have h' := p9uFL_galleryEnd_relabel (p9uFL_symm Θ) (Θ.Φ x) γ
        rw [show (p9uFL_symm Θ).Φ = Θ.Φ.symm from rfl, Equiv.symm_apply_apply, hend,
          Equiv.symm_apply_apply] at h'
        exact h'
    · rintro ⟨γ, hγ, hlen, hend⟩
      exact ⟨p9uFL_relabel Θ γ, p9uFL_isGallery_relabel Θ hγ,
        by rw [p9uFL_length_relabel, hlen], by rw [p9uFL_galleryEnd_relabel, hend]⟩
  unfold cdist
  rw [hset]

theorem IsGateAt.chamberIso {X : ChamberSystem ι C} {Y : ChamberSystem ι' D} (Θ : ChamberIso X Y)
    {R₀ : Set C} {y g : C} : IsGateAt Y (Θ.Φ '' R₀) (Θ.Φ y) (Θ.Φ g) ↔ IsGateAt X R₀ y g := by
  unfold IsGateAt
  constructor
  · rintro ⟨hgY, hY⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨g₀, hg₀, hg₀g⟩ := hgY
      exact Θ.Φ.injective hg₀g ▸ hg₀
    · intro z hz
      have hzY : Θ.Φ z ∈ Θ.Φ '' R₀ := ⟨z, hz, rfl⟩
      have h := hY (Θ.Φ z) hzY
      rw [cdist_chamberIso Θ y z, cdist_chamberIso Θ y g, cdist_chamberIso Θ g z] at h
      exact h
  · rintro ⟨hg, hX⟩
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    rintro z ⟨z₀, hz₀, rfl⟩
    have h := hX z₀ hz₀
    rwa [cdist_chamberIso Θ y z₀, cdist_chamberIso Θ y g, cdist_chamberIso Θ g z₀]

theorem IntrSet_chamberIso {X : ChamberSystem ι C} {Y : ChamberSystem ι' D} (Θ : ChamberIso X Y)
    {R₀ : Set C} {ψ : C → C} {ψ' : D → D} (hψ : ∀ g ∈ R₀, Θ.Φ (ψ g) = ψ' (Θ.Φ g)) (n : ℕ)
    (y : C) : Θ.Φ y ∈ IntrSet Y (Θ.Φ '' R₀) ψ' n ↔ y ∈ IntrSet X R₀ ψ n := by
  unfold IntrSet
  constructor
  · rintro ⟨g', hg'Y, hgateY, hdist⟩
    obtain ⟨g, hg, hg'g⟩ := hg'Y
    rw [← hg'g] at hgateY hdist
    refine ⟨g, hg, (IsGateAt.chamberIso Θ).mp hgateY, ?_⟩
    rw [← hψ g hg, cdist_chamberIso Θ y (ψ g)] at hdist
    exact hdist
  · rintro ⟨g, hg, hgateX, hdist⟩
    refine ⟨Θ.Φ g, ⟨g, hg, rfl⟩, (IsGateAt.chamberIso Θ).mpr hgateX, ?_⟩
    rw [← hψ g hg, cdist_chamberIso Θ y (ψ g)]
    exact hdist

section Prod

variable {I J : Type} {C₁ C₂ : Type}

private def p9uFL_leftSteps (γ : List ((I ⊕ J) × (C₁ × C₂))) : List (I × C₁) :=
  γ.filterMap fun p => match p.1 with
    | Sum.inl i => some (i, p.2.1)
    | Sum.inr _ => none

private def p9uFL_rightSteps (γ : List ((I ⊕ J) × (C₁ × C₂))) : List (J × C₂) :=
  γ.filterMap fun p => match p.1 with
    | Sum.inl _ => none
    | Sum.inr j => some (j, p.2.2)

private theorem p9uFL_prod_isGallery_inl {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂}
    {x : C₁ × C₂} {γ : List (I × C₁)} (hγ : X.IsGallery x.1 γ) :
    (X.prod Y).IsGallery x (γ.map fun p => ((Sum.inl p.1 : I ⊕ J), (p.2, x.2))) ∧
      galleryEnd x (γ.map fun p => ((Sum.inl p.1 : I ⊕ J), (p.2, x.2))) =
        (galleryEnd x.1 γ, x.2) := by
  induction γ generalizing x with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨ihg, ihe⟩ := ih (x := (p.2, x.2)) h2
    exact ⟨⟨⟨h1, rfl⟩, ihg⟩, by simpa using ihe⟩

private theorem p9uFL_prod_isGallery_inr {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂}
    {x : C₁ × C₂} {γ : List (J × C₂)} (hγ : Y.IsGallery x.2 γ) :
    (X.prod Y).IsGallery x (γ.map fun p => ((Sum.inr p.1 : I ⊕ J), (x.1, p.2))) ∧
      galleryEnd x (γ.map fun p => ((Sum.inr p.1 : I ⊕ J), (x.1, p.2))) =
        (x.1, galleryEnd x.2 γ) := by
  induction γ generalizing x with
  | nil => exact ⟨trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    obtain ⟨ihg, ihe⟩ := ih (x := (x.1, p.2)) h2
    exact ⟨⟨⟨rfl, h1⟩, ihg⟩, by simpa using ihe⟩

private theorem p9uFL_prod_project {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂}
    {x : C₁ × C₂} {γ : List ((I ⊕ J) × (C₁ × C₂))} (hγ : (X.prod Y).IsGallery x γ) :
    (X.IsGallery x.1 (p9uFL_leftSteps γ) ∧
        galleryEnd x.1 (p9uFL_leftSteps γ) = (galleryEnd x γ).1) ∧
      (Y.IsGallery x.2 (p9uFL_rightSteps γ) ∧
        galleryEnd x.2 (p9uFL_rightSteps γ) = (galleryEnd x γ).2) ∧
      (p9uFL_leftSteps γ).length + (p9uFL_rightSteps γ).length = γ.length := by
  induction γ generalizing x with
  | nil => exact ⟨⟨trivial, rfl⟩, ⟨trivial, rfl⟩, rfl⟩
  | cons p γ ih =>
    obtain ⟨hadj, hγ'⟩ := hγ
    obtain ⟨⟨ihL, ihLe⟩, ⟨ihR, ihRe⟩, ihLen⟩ := ih (x := p.2) hγ'
    rcases p with ⟨s, z⟩
    cases s with
    | inl i =>
      change X.adj i x.1 z.1 ∧ x.2 = z.2 at hadj
      obtain ⟨hXi, hz2⟩ := hadj
      have hLc : p9uFL_leftSteps ((Sum.inl i, z) :: γ) = (i, z.1) :: p9uFL_leftSteps γ := by
        simp [p9uFL_leftSteps]
      have hRc : p9uFL_rightSteps ((Sum.inl i, z) :: γ) = p9uFL_rightSteps γ := by
        simp [p9uFL_rightSteps]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [hLc]; exact ⟨hXi, ihL⟩
      · rw [hLc]; simpa only [galleryEnd_cons] using ihLe
      · rw [hRc, hz2]; exact ihR
      · rw [hRc, hz2]; simpa only [galleryEnd_cons] using ihRe
      · rw [hLc, hRc]; simp only [List.length_cons]; omega
    | inr j =>
      change x.1 = z.1 ∧ Y.adj j x.2 z.2 at hadj
      obtain ⟨hz1, hYj⟩ := hadj
      have hLc : p9uFL_leftSteps ((Sum.inr j, z) :: γ) = p9uFL_leftSteps γ := by
        simp [p9uFL_leftSteps]
      have hRc : p9uFL_rightSteps ((Sum.inr j, z) :: γ) = (j, z.2) :: p9uFL_rightSteps γ := by
        simp [p9uFL_rightSteps]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [hLc, hz1]; exact ihL
      · rw [hLc, hz1]; simpa only [galleryEnd_cons] using ihLe
      · rw [hRc]; exact ⟨hYj, ihR⟩
      · rw [hRc]; simpa only [galleryEnd_cons] using ihRe
      · rw [hLc, hRc]; simp only [List.length_cons]; omega

theorem cdist_prod {I J : Type} {C₁ C₂ : Type} {X : ChamberSystem I C₁} {Y : ChamberSystem J C₂}
    (hX : X.Connected) (hY : Y.Connected) (x y : C₁ × C₂) :
    cdist (X.prod Y) x y = cdist X x.1 y.1 + cdist Y x.2 y.2 := by
  have hconn : (X.prod Y).Connected := by
    intro a b
    obtain ⟨α, hα, heα⟩ := hX a.1 b.1
    obtain ⟨β, hβ, heβ⟩ := hY a.2 b.2
    refine ⟨α.map (fun p => (Sum.inl p.1, (p.2, a.2))) ++
        β.map (fun p => (Sum.inr p.1, (b.1, p.2))), ?_, ?_⟩
    · refine (ChamberSystem.isGallery_append (X := X.prod Y) a _ _).mpr
        ⟨(p9uFL_prod_isGallery_inl (X := X) (Y := Y) hα).1, ?_⟩
      rw [(p9uFL_prod_isGallery_inl (X := X) (Y := Y) hα).2, heα]
      exact (p9uFL_prod_isGallery_inr (X := X) (Y := Y) (x := (b.1, a.2)) hβ).1
    · rw [galleryEnd_append, (p9uFL_prod_isGallery_inl (X := X) (Y := Y) hα).2, heα,
        (p9uFL_prod_isGallery_inr (X := X) (Y := Y) (x := (b.1, a.2)) hβ).2, heβ]
  obtain ⟨γ, hγ, hlenγ, hendγ⟩ := p9uFL_exists_min_gallery hconn x y
  have hle : cdist (X.prod Y) x y ≤ cdist X x.1 y.1 + cdist Y x.2 y.2 := by
    obtain ⟨γ₁, hγ₁, hlen₁, hend₁⟩ := p9uFL_exists_min_gallery hX x.1 y.1
    obtain ⟨γ₂, hγ₂, hlen₂, hend₂⟩ := p9uFL_exists_min_gallery hY x.2 y.2
    have hg₁ := p9uFL_prod_isGallery_inl (X := X) (Y := Y) (x := x) hγ₁
    have hg₂ := p9uFL_prod_isGallery_inr (X := X) (Y := Y) (x := (y.1, x.2)) hγ₂
    have hprod : (X.prod Y).IsGallery x
        (γ₁.map (fun p => (Sum.inl p.1, (p.2, x.2))) ++
          γ₂.map (fun p => (Sum.inr p.1, (y.1, p.2)))) := by
      refine (ChamberSystem.isGallery_append (X := X.prod Y) x _ _).mpr ⟨hg₁.1, ?_⟩
      rw [hg₁.2, hend₁]
      exact hg₂.1
    have hprodEnd : galleryEnd x
        (γ₁.map (fun p => (Sum.inl p.1, (p.2, x.2))) ++
          γ₂.map (fun p => (Sum.inr p.1, (y.1, p.2)))) = y := by
      rw [galleryEnd_append, hg₁.2, hend₁, hg₂.2, hend₂]
    have h := p9uFL_cdist_le (X := X.prod Y) hprod hprodEnd
    rw [List.length_append, List.length_map, List.length_map, hlen₁, hlen₂] at h
    exact h
  have hge : cdist X x.1 y.1 + cdist Y x.2 y.2 ≤ cdist (X.prod Y) x y := by
    obtain ⟨⟨hL, hLe⟩, ⟨hR, hRe⟩, hLen⟩ := p9uFL_prod_project hγ
    have h1 : cdist X x.1 y.1 ≤ (p9uFL_leftSteps γ).length :=
      p9uFL_cdist_le hL (by rw [hLe, hendγ])
    have h2 : cdist Y x.2 y.2 ≤ (p9uFL_rightSteps γ).length :=
      p9uFL_cdist_le hR (by rw [hRe, hendγ])
    omega
  exact le_antisymm hle hge

end Prod

end CFSG.ClassicalInvolution.Phan.PhanE.Flag

end
