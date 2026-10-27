module

public import CFSG.LocalAnalysis.StandardType.PhanEDMDatum

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.DM

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*} {X : ChamberSystem I C} {lev : C → ℕ} {J : Set I} {Q P : Set C}
  {i : I} {π : C → C} {ε : I → C → C → List (I × C)} {x : C} {γ γ' : List (I × C)}

theorem simplyConnectedIn_empty (m : ℕ) : SimplyConnectedIn X J (∅ : Set C) m := by
  intro x γ hγ _
  exact absurd hγ.1 (Set.notMem_empty x)

private theorem q2cDMs_galleryIn_residue {A : Set C} {K : Set I} (h : GalleryIn X J A x γ)
    (hK : ∀ p ∈ γ, p.1 ∈ K) : GalleryIn X K (A ∩ X.residue K x) x γ := by
  refine ⟨⟨h.1, X.self_mem_residue K x⟩, h.2.1, fun p hp =>
    ⟨hK p hp, (h.2.2 p hp).2, ?_⟩⟩
  exact h.2.1.mem_residue (fun i hi => by
    have hi' : i ∈ γ.map Prod.fst := by simpa [galleryType] using hi
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi'
    exact hK q hq) p hp

theorem homIn_two_of_homIn_three
    (h3 : ∀ K : Set I, K ⊆ J → K.encard = 3 → ∀ a ∈ P,
      SimplyConnectedIn X K (P ∩ X.residue K a) 2)
    (h : HomIn X J P 3 x γ γ') : HomIn X J P 2 x γ γ' := by
  induction h with
  | rel a b hab =>
    obtain ⟨γ₁, η, η', γ₂, K, hK, hγ, hγ', hηK, hη'K, hend⟩ := hab
    set a0 := galleryEnd x γ₁ with ha0
    have hsplitγ := galleryIn_append.mp hγ
    have hsplitγ' := galleryIn_append.mp hγ'
    have hη : GalleryIn X J P a0 η := (galleryIn_append.mp hsplitγ.1).2
    have hη' : GalleryIn X J P a0 η' := (galleryIn_append.mp hsplitγ'.1).2
    have hγ₁ : GalleryIn X J P x γ₁ := (galleryIn_append.mp hsplitγ.1).1
    have hηK' : ∀ p ∈ η, p.1 ∈ K ∩ J := fun p hp => ⟨hηK p hp, (hη.2.2 p hp).1⟩
    have hη'K' : ∀ p ∈ η', p.1 ∈ K ∩ J := fun p hp => ⟨hη'K p hp, (hη'.2.2 p hp).1⟩
    by_cases hK'2 : (K ∩ J).encard ≤ 2
    · exact homIn_replace (X := X) (J := J) (A := P) (m := 2) (x := x) (K := K ∩ J)
        γ₁ η η' γ₂ hK'2 hγ hγ' hηK' hη'K' hend
    · have hK'3 : (K ∩ J).encard = 3 := by
        have hle : (K ∩ J).encard ≤ (3 : ℕ∞) :=
          le_trans (Set.encard_mono Set.inter_subset_left) hK
        have hlt : (2 : ℕ∞) < (K ∩ J).encard := not_le.mp hK'2
        have h3le : (3 : ℕ∞) ≤ (K ∩ J).encard := by
          have h := (ENat.natCast_add_one_le_iff (m := 2) (n := (K ∩ J).encard)).mpr hlt
          norm_num at h
          exact h
        exact le_antisymm hle h3le
      have hsc := h3 (K ∩ J) Set.inter_subset_right hK'3 a0 hη.1
      have hgalη : GalleryIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) a0 η :=
        q2cDMs_galleryIn_residue hη hηK'
      have hgalη' : GalleryIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) a0 η' :=
        q2cDMs_galleryIn_residue hη' hη'K'
      have hrev : GalleryIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) (galleryEnd a0 η)
          (galleryReverse a0 η') := by
        rw [hend]
        exact hgalη'.reverse
      have hclosed : GalleryIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) a0
          (η ++ galleryReverse a0 η') :=
        galleryIn_append.mpr ⟨hgalη, hrev⟩
      have hendclosed : galleryEnd a0 (η ++ galleryReverse a0 η') = a0 := by
        rw [galleryEnd_append, hend, galleryEnd_galleryReverse]
      have hnil : HomIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) 2 a0
          (η ++ galleryReverse a0 η') [] :=
        hsc a0 (η ++ galleryReverse a0 η') hclosed hendclosed
      have hhom : HomIn X (K ∩ J) (P ∩ X.residue (K ∩ J) a0) 2 a0 η η' :=
        (homIn_iff_append_reverse (X := X) (J := K ∩ J)
          (A := P ∩ X.residue (K ∩ J) a0) (m := 2) (x := a0) (γ := η) (η := η')
          (by norm_num : (1 : ℕ) ≤ 2) hgalη hgalη' hend).mpr hnil
      have hhomP : HomIn X J P 2 a0 η η' :=
        hhom.mono Set.inter_subset_right Set.inter_subset_left le_rfl
      have h1 : HomIn X J P 2 x (γ₁ ++ η) (γ₁ ++ η') :=
        HomIn.append_left hγ₁ hhomP
      have hγ₂ : GalleryIn X J P (galleryEnd x (γ₁ ++ η)) γ₂ := hsplitγ.2
      exact h1.append_right hγ₂
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem PushData.homIn_two_of_homIn_two (hD : PushData X J Q P i π ε) (hi : i ∈ J)
    (h3 : ∀ K : Set I, K ⊆ J → K.encard = 3 → ∀ a ∈ P,
      SimplyConnectedIn X K (P ∩ X.residue K a) 2)
    (hγ : GalleryIn X J P x γ) (hγ' : GalleryIn X J P x γ')
    (h : HomIn X J Q 2 x γ γ') : HomIn X J P 2 x γ γ' := by
  have hthree := hD.homIn_three_of_homIn_two hi h
  rw [hD.fix x hγ.1, hD.push_eq_self hγ, hD.push_eq_self hγ'] at hthree
  exact homIn_two_of_homIn_three h3 hthree

theorem PushData.simplyConnectedIn_of (hD : PushData X J Q P i π ε) (hi : i ∈ J) (hPQ : P ⊆ Q)
    (hP : SimplyConnectedIn X J P 2) : SimplyConnectedIn X J Q 2 := by
  intro x γ hγ hend
  have hpush := hD.homIn_push hi hPQ hγ
  have hgal := hD.galleryIn_push hi hγ
  have hendP : galleryEnd (π x) (push ε x γ) = π x := by
    rw [hgal.2, hend]
  have h0 : HomIn X J Q 2 (π x) (push ε x γ) [] :=
    (hP (π x) (push ε x γ) hgal.1 hendP).mono (subset_refl J) hPQ le_rfl
  have hxQ : x ∈ Q := hγ.1
  have hmem := hD.mem x hxQ
  have hα : GalleryIn X J Q x [(i, π x)] := by
    rw [galleryIn_cons, galleryIn_nil]
    exact ⟨hxQ, hmem.2, hi, hPQ hmem.1, hPQ hmem.1⟩
  have hβ : GalleryIn X J Q (galleryEnd x ([(i, π x)] ++ push ε x γ)) [(i, x)] := by
    rw [galleryEnd_append, galleryEnd_cons, galleryEnd_nil, hendP, galleryIn_cons,
      galleryIn_nil]
    exact ⟨hPQ hmem.1, adj_symm hmem.2, hi, hxQ, hxQ⟩
  have h1 : HomIn X J Q 2 x ([(i, π x)] ++ push ε x γ ++ [(i, x)])
      ([(i, π x)] ++ [(i, x)]) := by
    have := (HomIn.append_left hα h0).append_right hβ
    simpa only [List.nil_append, List.append_nil] using this
  have hback : HomIn X J Q 2 x ([(i, π x)] ++ [(i, x)]) [] := by
    have hb : GalleryIn X J Q x
        ([] ++ [(i, π x), (i, galleryEnd x ([] : List (I × C)))] ++ []) := by
      simp only [List.nil_append, galleryEnd_nil, List.append_nil]
      rw [galleryIn_cons, galleryIn_cons, galleryIn_nil]
      exact ⟨hxQ, hmem.2, hi, hPQ hmem.1, hPQ hmem.1, adj_symm hmem.2, hi, hxQ, hxQ⟩
    simpa using homIn_backtrack (X := X) (J := J) (A := Q) (x := x)
      (by norm_num : (1 : ℕ) ≤ 2) ([] : List (I × C)) ([] : List (I × C))
      (i := i) (y := π x) hb
  have hW : HomIn X J Q 2 x ([(i, π x)] ++ push ε x γ ++ [(i, galleryEnd x γ)]) [] := by
    rw [hend]
    exact h1.trans hback
  exact hpush.trans hW

theorem simplyConnectedIn_residue_levelSet (hres : IsResidual X lev) (hlco : Lco X lev)
    (hlsco : Lsco X lev) {K : Set I} (hK : K.encard = 3) (a : C) (m : ℕ) :
    SimplyConnectedIn X K (X.residue K a ∩ levelSet lev m) 2 := by
  have hKne : K.Nonempty := by
    rw [← Set.encard_pos, hK]
    norm_num
  have base : ∀ m : ℕ, (∀ x ∈ X.residue K a, m ≤ lev x) →
      SimplyConnectedIn X K (X.residue K a ∩ levelSet lev m) 2 := by
    intro m hm
    by_cases hne : (X.residue K a ∩ levelSet lev m).Nonempty
    · rw [inter_levelSet_eq_aff hm hne]
      exact hlsco K a hK
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact simplyConnectedIn_empty 2
  induction m with
  | zero => exact base 0 (fun x _ => Nat.zero_le _)
  | succ m ih =>
    by_cases hex : ∃ x ∈ X.residue K a, lev x ≤ m
    · obtain ⟨i, hiK, π, ε, hD⟩ := exists_pushData hres hlco hKne a hex
      exact PushData.simplyConnectedIn_of hD hiK
        (fun x hx => ⟨hx.1, levelSet_mono (Nat.le_succ m) hx.2⟩) ih
    · exact base (m + 1) (fun x hx => by
        have hx' : ¬ lev x ≤ m := fun h => hex ⟨x, hx, h⟩
        exact Nat.succ_le_of_lt (not_le.mp hx'))

end CFSG.ClassicalInvolution.Phan.PhanE.DM
