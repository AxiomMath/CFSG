module

public import CFSG.LocalAnalysis.StandardType.PhanEDMStep

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*} {X : ChamberSystem I C} {lev : C → ℕ} {x : C} {γ γ' : List (I × C)}

theorem residue_univ_eq_univ (hX : X.Connected) (c : C) : X.residue Set.univ c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨γ, hγ, rfl⟩ := hX c y
  exact galleryEnd_mem_residue hγ (fun i _ => Set.mem_univ i)

private theorem q2cDMt_mem_galleryType {p : I × C} {γ : List (I × C)} (hp : p ∈ γ) :
    p.1 ∈ galleryType γ :=
  List.mem_map_of_mem hp

private def q2cDMt_bound (lev : C → ℕ) (x : C) (γ : List (I × C)) : ℕ :=
  lev x + (γ.map fun p => lev p.2).sum

private theorem q2cDMt_lev_le_bound (lev : C → ℕ) (x : C) (γ : List (I × C)) :
    lev x ≤ q2cDMt_bound lev x γ := by
  show lev x ≤ lev x + _
  exact Nat.le_add_right _ _

private theorem q2cDMt_lev_mem_le_bound (lev : C → ℕ) (x : C) {p : I × C}
    {γ : List (I × C)} (hp : p ∈ γ) : lev p.2 ≤ q2cDMt_bound lev x γ := by
  have h1 : lev p.2 ≤ (γ.map fun q => lev q.2).sum := List.le_sum_of_mem (List.mem_map_of_mem hp)
  show lev p.2 ≤ lev x + (γ.map fun q => lev q.2).sum
  exact h1.trans (Nat.le_add_left _ _)

private theorem q2cDMt_elemMove_to_elemIn (lev : C → ℕ) {x : C} {b c : List (I × C)}
    (hb : X.IsGallery x b) (hbc : X.ElemMove x b c) :
    ∃ N : ℕ, ElemIn X Set.univ (levelSet lev N) 2 x b c := by
  have hc : X.IsGallery x c := hbc.isGallery hb
  cases hbc with
  | mk γ₁ η η' γ₂ K hK hη hη' hηJ hη'J hend =>
    refine ⟨q2cDMt_bound lev x ((γ₁ ++ η ++ γ₂) ++ (γ₁ ++ η' ++ γ₂)),
      ElemIn.mk γ₁ η η' γ₂ K hK ?_ ?_ ?_ ?_ hend⟩
    · exact ⟨q2cDMt_lev_le_bound lev x _,
        hb,
        fun p hp => ⟨Set.mem_univ _,
          q2cDMt_lev_mem_le_bound lev x (List.mem_append_left _ hp)⟩⟩
    · exact ⟨q2cDMt_lev_le_bound lev x _,
        hc,
        fun p hp => ⟨Set.mem_univ _,
          q2cDMt_lev_mem_le_bound lev x (List.mem_append_right _ hp)⟩⟩
    · intro p hp
      exact hηJ p.1 (q2cDMt_mem_galleryType hp)
    · intro p hp
      exact hη'J p.1 (q2cDMt_mem_galleryType hp)

private theorem q2cDMt_exists_levelSet_homIn_of_reflTransGen (lev : C → ℕ) {x : C}
    {γ γ' : List (I × C)} (hγ : X.IsGallery x γ)
    (h : Relation.ReflTransGen (X.ElemMove x) γ γ') :
    X.IsGallery x γ' ∧ ∃ N : ℕ, HomIn X Set.univ (levelSet lev N) 2 x γ γ' := by
  revert hγ
  induction h with
  | refl =>
    intro hγ
    exact ⟨hγ, 0, Relation.EqvGen.refl γ⟩
  | tail hab hbc ih =>
    intro hγ
    obtain ⟨ha, N, hhom⟩ := ih hγ
    obtain ⟨N', helem⟩ := q2cDMt_elemMove_to_elemIn lev ha hbc
    refine ⟨hbc.isGallery ha, max N N', ?_⟩
    exact (hhom.mono (subset_refl _) (levelSet_mono (le_max_left _ _)) le_rfl).trans
      ((HomIn.of_elemIn helem).mono (subset_refl _) (levelSet_mono (le_max_right _ _)) le_rfl)

theorem exists_levelSet_homIn_univ (lev : C → ℕ) (hγ : X.IsGallery x γ)
    (h : X.TwoHomotopic x γ γ') : ∃ N : ℕ, HomIn X Set.univ (levelSet lev N) 2 x γ γ' :=
  (q2cDMt_exists_levelSet_homIn_of_reflTransGen lev hγ
    (TwoHomotopic.iff_reflTransGen.mp h)).2

private theorem q2cDMt_eq_nil_of_isEmpty (hI : IsEmpty I) {x : C} {γ : List (I × C)}
    (hγ : X.IsGallery x γ) : γ = [] := by
  cases γ with
  | nil => rfl
  | cons p γ => exact (hI.false p.1).elim

private theorem q2cDMt_connectedIn_levelSet_of_gallery (hres : IsResidual X lev)
    (hlco : Lco X lev) (hX : X.Connected) [Nonempty I] :
    ∀ (N : ℕ) (a b : C) (γ : List (I × C)), a ∈ levelSet lev 0 → b ∈ levelSet lev 0 →
      GalleryIn X Set.univ (levelSet lev N) a γ → galleryEnd a γ = b →
      ∃ γ' : List (I × C), GalleryIn X Set.univ (levelSet lev 0) a γ' ∧ galleryEnd a γ' = b := by
  intro N
  induction N with
  | zero =>
    intro a b γ ha hb hgal hend
    exact ⟨γ, by simpa using hgal, hend⟩
  | succ N ih =>
    intro a b γ ha hb hgal hend
    obtain ⟨i, hi, π, ε, hD⟩ := exists_pushData hres hlco Set.univ_nonempty a
      (m := N) ⟨a, X.self_mem_residue Set.univ a, le_trans ha (Nat.zero_le N)⟩
    simp only [residue_univ_eq_univ hX a, Set.univ_inter] at hD
    have hπa : π a = a := hD.fix a (le_trans ha (Nat.zero_le N))
    have hπb : π b = b := hD.fix b (le_trans hb (Nat.zero_le N))
    obtain ⟨hgal', hend'⟩ := hD.galleryIn_push (Set.mem_univ i) hgal
    rw [hπa] at hgal'
    rw [hπa, hend, hπb] at hend'
    exact ih a b (push ε a γ) ha hb hgal' hend'

theorem connectedIn_levelSet_zero (hres : IsResidual X lev) (hlco : Lco X lev)
    (hX : X.Connected) :
    ConnectedIn X Set.univ (levelSet lev 0) := by
  intro a ha b hb
  rcases isEmpty_or_nonempty I with hI | hI
  · obtain ⟨γ, hγ, hend⟩ := hX a b
    exact ⟨γ, ⟨ha, hγ, fun p hp => (hI.false p.1).elim⟩, hend⟩
  · haveI : Nonempty I := hI
    obtain ⟨γ, hγ, hend⟩ := hX a b
    refine q2cDMt_connectedIn_levelSet_of_gallery hres hlco hX (q2cDMt_bound lev a γ)
      a b γ ha hb ?_ hend
    exact ⟨q2cDMt_lev_le_bound lev a γ, hγ,
      fun p hp => ⟨Set.mem_univ _, q2cDMt_lev_mem_le_bound lev a hp⟩⟩

private theorem q2cDMt_homIn_levelSet_zero (hres : IsResidual X lev) (hlco : Lco X lev)
    (hlsco : Lsco X lev) (hX : X.Connected) [Nonempty I] :
    ∀ (N : ℕ) (x : C) (γ γ' : List (I × C)),
      GalleryIn X Set.univ (levelSet lev 0) x γ →
      GalleryIn X Set.univ (levelSet lev 0) x γ' →
      HomIn X Set.univ (levelSet lev N) 2 x γ γ' →
      HomIn X Set.univ (levelSet lev 0) 2 x γ γ' := by
  intro N
  induction N with
  | zero =>
    intro x γ γ' hγ hγ' h
    exact h
  | succ N ih =>
    intro x γ γ' hγ hγ' h
    obtain ⟨i, hi, π, ε, hD⟩ := exists_pushData hres hlco Set.univ_nonempty x
      (m := N) ⟨x, X.self_mem_residue Set.univ x, le_trans hγ.mem_start (Nat.zero_le N)⟩
    simp only [residue_univ_eq_univ hX x, Set.univ_inter] at hD
    have h3 : ∀ K : Set I, K ⊆ Set.univ → K.encard = 3 → ∀ a ∈ levelSet lev N,
        SimplyConnectedIn X K (levelSet lev N ∩ X.residue K a) 2 := by
      intro K _ hK a _
      simpa [Set.inter_comm] using simplyConnectedIn_residue_levelSet hres hlco hlsco hK a N
    have hγN : GalleryIn X Set.univ (levelSet lev N) x γ :=
      hγ.mono (subset_refl _) (levelSet_mono (Nat.zero_le N))
    have hγ'N : GalleryIn X Set.univ (levelSet lev N) x γ' :=
      hγ'.mono (subset_refl _) (levelSet_mono (Nat.zero_le N))
    exact ih x γ γ' hγ hγ' (hD.homIn_two_of_homIn_two (Set.mem_univ i) h3 hγN hγ'N h)

theorem homIn_levelSet_zero (hres : IsResidual X lev) (hlco : Lco X lev) (hlsco : Lsco X lev)
    (hX : X.Connected) (N : ℕ)
    (hγ : GalleryIn X Set.univ (levelSet lev 0) x γ)
    (hγ' : GalleryIn X Set.univ (levelSet lev 0) x γ')
    (h : HomIn X Set.univ (levelSet lev N) 2 x γ γ') :
    HomIn X Set.univ (levelSet lev 0) 2 x γ γ' := by
  rcases isEmpty_or_nonempty I with hI | hI
  · have h1 : γ = [] := q2cDMt_eq_nil_of_isEmpty hI hγ.isGallery
    have h2 : γ' = [] := q2cDMt_eq_nil_of_isEmpty hI hγ'.isGallery
    subst h1
    subst h2
    exact Relation.EqvGen.refl []
  · haveI : Nonempty I := hI
    exact q2cDMt_homIn_levelSet_zero hres hlco hlsco hX N x γ γ' hγ hγ' h

theorem DM07_thm314 (hres : IsResidual X lev) (hlco : Lco X lev) (hlsco : Lsco X lev)
    (hX : X.Connected) (hsc : X.SimplyTwoConnected) :
    ConnectedIn X Set.univ (levelSet lev 0) ∧
      SimplyConnectedIn X Set.univ (levelSet lev 0) 2 := by
  refine ⟨connectedIn_levelSet_zero hres hlco hX, ?_⟩
  intro x γ hγ hend
  have hγ' : GalleryIn X Set.univ (levelSet lev 0) x [] := galleryIn_nil.mpr hγ.1
  obtain ⟨N, hN⟩ :=
    exists_levelSet_homIn_univ lev hγ.isGallery (hsc x γ hγ.isGallery hend)
  exact homIn_levelSet_zero hres hlco hlsco hX N hγ hγ' hN

end CFSG.ClassicalInvolution.Phan.PhanE.DM
