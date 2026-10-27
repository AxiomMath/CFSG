module

public import CFSG.Quasithin.Background.D2Z15
public import CFSG.Quasithin.Background.D2Z13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section Perm

variable {X : Subgroup (MulAut V)}

theorem Pfam_conj {g : MulAut V} (hg : g ∈ X) {Y : Subgroup (MulAut V)} (hY : Y ∈ Pfam X) :
    conjBy g Y ∈ Pfam X := by
  obtain ⟨hYP, hYc, hYr⟩ := hY
  refine ⟨?_, by rw [card_conjBy]; exact hYc, by rw [rk_commV_conjBy]; exact hYr⟩
  intro x hx
  have h1 : g⁻¹ * x * g ∈ Y := mem_conjBy_iff.mp hx
  have h2 : g⁻¹ * x * g ∈ pCoreOf 3 X := hYP h1
  have h3 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hg) (g⁻¹ * x * g)).mp h2
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h3

variable {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)}

omit [Finite V] in
theorem PDecomp.injective (d : PDecomp X Pi) : Function.Injective Pi := by
  intro i j hij
  by_contra hne
  have hd := d.indep.pairwiseDisjoint hne
  have hbot : Pi i = ⊥ := by
    have := disjoint_iff.mp hd
    rw [← hij, inf_idem] at this
    exact this
  have hc := d.card_eq i
  rw [hbot, Subgroup.card_bot] at hc
  omega

theorem PDecomp.card_pfam (hV : ∀ v : V, v ^ 2 = 1) (d : PDecomp X Pi)
    (hcomm : ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x) :
    Nat.card (Pfam X) = s := by
  rw [← d.range_eq hV hcomm, Nat.card_range_of_injective d.injective]
  simp

end Perm

section Main

variable {X : Subgroup (MulAut V)} {r : ℚ}

theorem fixV_pCoreOf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) : fixV (pCoreOf 3 X) = ⊥ :=
  (D2_20 hV h).2 _ fun B hB => commSub_eq_bot_iff.mp (D2_14_5 hV (hall B hB))

theorem iSup_commV_eq_top (hV : ∀ v : V, v ^ 2 = 1) {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)}
    (d : PDecomp X Pi) (hW : fixV (pCoreOf 3 X) = ⊥) : ⨆ i, commV (Pi i) = ⊤ := by
  have hdir := (isDirectSum_commV_fixV hV X).1
  rw [hW, sup_bot_eq] at hdir
  rw [d.vsup]
  exact hdir

theorem two_mul_le_of_dvd_of_ne {d n : ℕ} (hn : 0 < n) (hd : d ∣ n) (hne : d ≠ n) : 2 * d ≤ n := by
  obtain ⟨m, rfl⟩ := hd
  rcases m with _ | _ | m
  · omega
  · simp at hne
  · nlinarith

omit [Finite V] in
theorem K_le_stab {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)} :
    ∀ i, (X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V))) ≤ stabSub (commV (Pi i)) := by
  intro i g hg
  have hgn : g ∈ Subgroup.normalizer (Pi i : Set (MulAut V)) := by
    have := (Subgroup.mem_inf.mp hg).2
    exact (Subgroup.mem_iInf.mp this) i
  have hgn' : g⁻¹ ∈ Subgroup.normalizer (Pi i : Set (MulAut V)) := Subgroup.inv_mem _ hgn
  refine mem_stabSub_commV (fun p hp => ?_) (fun p hp => ?_)
  · exact (Subgroup.mem_normalizer_iff.mp hgn p).mp hp
  · have := (Subgroup.mem_normalizer_iff.mp hgn' p).mp hp
    simpa using this

theorem X_card_bound (hV : ∀ v : V, v ^ 2 = 1) {r : ℚ} (hq : qhatOf X = (r : WithTop ℚ))
    (hr : 1 < r) {s : ℕ} (hs : 0 < s) {Pi : Fin s → Subgroup (MulAut V)} (d : PDecomp X Pi)
    (hW : fixV (pCoreOf 3 X) = ⊥) :
    2 * Nat.card (X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V)) : Subgroup (MulAut V)) ≤
      6 ^ s := by
  set K : Subgroup (MulAut V) := X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V)) with hK
  have htop := iSup_commV_eq_top hV d hW
  have hdvd := card_dvd_of_stab hV d.rk_eq htop (K_le_stab (X := X) (Pi := Pi))
  have hne : Nat.card K ≠ 6 ^ s := by
    intro hcard
    obtain ⟨g, hgK, hg1, hg2, hgr⟩ := exists_transvection_of_card_eq hV hs d.vindep htop d.rk_eq
      (K_le_stab (X := X) (Pi := Pi)) hcard
    exact not_transvection hV hq hr (hgK.1) hg1 hg2 hgr
  exact two_mul_le_of_dvd_of_ne (by positivity) hdvd hne

theorem hcomm_of_hall (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) :
    ∀ x ∈ pCoreOf 3 X, ∀ y ∈ pCoreOf 3 X, x * y = y * x := by
  obtain ⟨A, hA⟩ := QhatStar_nonempty h.qhat h.le_two
  exact pCoreOf_comm hV (hall A hA)

theorem X_le_normalizers_of_three (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) {Pi : Fin 3 → Subgroup (MulAut V)}
    (d : PDecomp X Pi) : X ≤ ⨅ i, Subgroup.normalizer (Pi i : Set (MulAut V)) := by
  have hcomm := hcomm_of_hall hV h hall
  have hcard3 : Nat.card (Pfam X) = 3 := d.card_pfam hV hcomm
  have hrange : Set.range Pi = Pfam X := d.range_eq hV hcomm
  have hB : ∀ B ∈ QhatStar X, ∀ g ∈ B, ∀ i, conjBy g (Pi i) = Pi i := by
    intro B hB g hg i
    rcases D2_14_7 hV (hall B hB) with ⟨Pi', d', hr', -⟩ | ⟨Pi', d', hr', hc'⟩
    · exfalso
      have := d'.card_pfam hV hcomm
      omega
    · have hmem : Pi i ∈ Set.range Pi' := by rw [hr', ← hrange]; exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hmem
      rw [← hj]
      exact hc'.1 g hg j
  refine h.jhat.le.trans (iSup₂_le fun B hB' g hg => ?_)
  exact Subgroup.mem_iInf.mpr fun i => mem_normalizer_of_conjBy_eq (hB B hB' g hg i)

theorem card_le_two_mul_K {Pi : Fin 2 → Subgroup (MulAut V)} (hr : Set.range Pi = Pfam X)
    (hinj : Function.Injective Pi) {a₀ : MulAut V} (ha₀ : a₀ ∈ X)
    (hsw : conjBy a₀ (Pi 0) = Pi 1) :
    Nat.card X ≤ 2 * Nat.card (X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V)) :
      Subgroup (MulAut V)) := by
  set K : Subgroup (MulAut V) := X ⊓ ⨅ j, Subgroup.normalizer (Pi j : Set (MulAut V)) with hK
  have hPi : ∀ i, Pi i ∈ Pfam X := fun i => hr ▸ ⟨i, rfl⟩
  have hcase : ∀ g ∈ X, conjBy g (Pi 0) = Pi 0 ∨ conjBy g (Pi 0) = Pi 1 := by
    intro g hg
    have hmem : conjBy g (Pi 0) ∈ Set.range Pi := hr ▸ Pfam_conj hg (hPi 0)
    obtain ⟨j, hj⟩ := hmem
    fin_cases j
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  have hKmem : ∀ g ∈ X, conjBy g (Pi 0) = Pi 0 → g ∈ K := by
    intro g hg h0
    refine ⟨hg, Subgroup.mem_iInf.mpr fun i => ?_⟩
    fin_cases i
    · exact mem_normalizer_of_conjBy_eq h0
    · have hmem : conjBy g (Pi 1) ∈ Set.range Pi := hr ▸ Pfam_conj hg (hPi 1)
      obtain ⟨j, hj⟩ := hmem
      fin_cases j
      · exfalso
        have h1 : conjBy g (Pi 1) = conjBy g (Pi 0) := by rw [h0]; exact hj.symm
        have := conjBy_injective g h1
        exact absurd (hinj (show Pi 1 = Pi 0 from this)) (by decide)
      · exact mem_normalizer_of_conjBy_eq hj.symm
  have hsub : (X : Set (MulAut V)) ⊆ (K : Set (MulAut V)) ∪
      (fun y => a₀ * y) '' (K : Set (MulAut V)) := by
    intro g hg
    rcases hcase g hg with h0 | h1
    · exact Or.inl (hKmem g hg h0)
    · right
      refine ⟨a₀⁻¹ * g, hKmem _ (X.mul_mem (X.inv_mem ha₀) hg) ?_, by simp⟩
      have e : conjBy a₀⁻¹ (Pi 1) = Pi 0 := by
        rw [← hsw, conjBy_conjBy, inv_mul_cancel, conjBy_one]
      rw [← conjBy_conjBy, h1, e]
  have hfin : (K : Set (MulAut V)) ∪ (fun y => a₀ * y) '' (K : Set (MulAut V)) |>.Finite :=
    Set.toFinite _
  calc Nat.card X = (X : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
    _ ≤ ((K : Set (MulAut V)) ∪ (fun y => a₀ * y) '' (K : Set (MulAut V))).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ (K : Set (MulAut V)).ncard + ((fun y => a₀ * y) '' (K : Set (MulAut V))).ncard :=
        Set.ncard_union_le _ _
    _ = 2 * Nat.card K := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective a₀), ← Nat.card_coe_set_eq]
        simp [two_mul]

end Main

end CFSG.Quasithin
