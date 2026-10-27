module

public import CFSG.RankThree.PartOne.FIS.SymLocal
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.RankThree.PartOne.FIS.Reduction

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm
open CFSG.Permutation.SymmetricCoxeter

variable {X : Type} [Group X] {E : Set X} {d : X} {n : ℕ}

theorem isSwap_conj' {α : Type*} [DecidableEq α] {s : Perm α} (hs : s.IsSwap) (g : Perm α) :
    (g * s * g⁻¹).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  exact ⟨g a, g b, g.injective.ne hab, by rw [swap_apply_apply]⟩

theorem isSwap_conj_iff {α : Type*} [DecidableEq α] {s : Perm α} (g : Perm α) :
    (g * s * g⁻¹).IsSwap ↔ s.IsSwap := by
  refine ⟨fun h => ?_, fun h => isSwap_conj' h g⟩
  have := isSwap_conj' h g⁻¹
  simpa [mul_assoc] using this

@[expose] def LocalIso.conj (L : LocalIso E d n) (k : Perm (Fin n)) : LocalIso E d n where
  φ := L.φ.trans (MulAut.conj k)
  isSwap_iff t := by
    rw [L.isSwap_iff t]
    exact (isSwap_conj_iff k).symm

theorem adjSwap_last_ne {m i : ℕ} (hi : i < m) :
    adjSwap m i (Fin.last m) ≠ Fin.last m ↔ i + 1 = m := by
  rw [adjSwap_of_lt hi]
  constructor
  · intro h
    by_contra hne
    apply h
    rw [swap_apply_of_ne_of_ne]
    · simp [Fin.ext_iff]
      omega
    · simp [Fin.ext_iff]
      omega
  · intro h
    have : (⟨i + 1, by omega⟩ : Fin (m + 1)) = Fin.last m := by
      ext
      simp [h]
    rw [← this, swap_apply_right]
    simp [Fin.ext_iff]

theorem adjSwap_isSwap {m i : ℕ} (hi : i < m) : (adjSwap m i).IsSwap := by
  rw [adjSwap_of_lt hi]
  exact ⟨_, _, by simp [Fin.ext_iff], rfl⟩

theorem coxeter_build {m : ℕ} (hP : Pair X E) (hd : d ∈ E)
    (L : LocalIso E d (m + 1)) {c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c)
    (hstar : ∀ e (he : e ∈ LocalClass E d),
      (e * c ≠ c * e ↔ L.φ ⟨e, mem_localGroup he⟩ (Fin.last m) ≠ Fin.last m)) :
    ∃ Ψ : Perm (Fin (m + 2 + 1)) →* X,
      (∀ i < m, Ψ (adjSwap (m + 2) i) = ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X)) ∧
        Ψ (adjSwap (m + 2) m) = c ∧ Ψ (adjSwap (m + 2) (m + 1)) = d := by
  have hT := tt_of_pair hP
  have := Pair.finite hP
  let g : ℕ → X := fun i =>
    if h : i < m then ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X)
    else if i = m then c else d
  have hg_lt : ∀ i < m, g i = ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X) := by
    intro i hi
    simp [g, hi]
  have hg_m : g m = c := by simp [g]
  have hg_m1 : g (m + 1) = d := by simp [g]
  have hgT : ∀ i < m, g i ∈ LocalClass E d := by
    intro i hi
    rw [hg_lt i hi]
    exact L.mem_of_swap (adjSwap_isSwap hi)
  have hgE : ∀ i < m + 2, g i ∈ E := by
    intro i hi
    rcases (by omega : i < m ∨ i = m ∨ i = m + 1) with h | h | h
    · exact (hgT i h).1
    · rw [h, hg_m]; exact hc
    · rw [h, hg_m1]; exact hd
  have hgc : ∀ i < m, (g i * c ≠ c * g i ↔ i + 1 = m) := by
    intro i hi
    have hmem := hgT i hi
    have hH : (⟨g i, mem_localGroup hmem⟩ : ↥(LocalGroup E d)) = L.φ.symm (adjSwap m i) :=
      Subtype.ext (hg_lt i hi)
    rw [hstar (g i) hmem, hH, MulEquiv.apply_symm_apply, adjSwap_last_ne hi]
  have hgd : ∀ i < m, g i * d = d * g i := fun i hi => (hgT i hi).2.2
  have hcox : IsCoxeterA (m + 2) g := by
    refine ⟨fun i hi => Pair.mul_self hP (hgE i hi), fun i hi => ?_, fun i j hij hj => ?_⟩
    · rcases (by omega : i + 1 < m ∨ i + 1 = m ∨ i = m) with h | h | h
      · have h1 := (isCoxeterA_adjSwap m).braid i h
        have h2 := congrArg (fun σ => ((L.φ.symm σ : ↥(LocalGroup E d)) : X)) h1
        simpa [map_mul, hg_lt i (by omega), hg_lt (i + 1) h] using h2
      · have hi' : i < m := by omega
        have hnc : g i * c ≠ c * g i := (hgc i hi').2 h
        have := tt_braid hT (hgE i (by omega)) hc hnc
        rw [show g (i + 1) = c by rw [h, hg_m]]
        exact this
      · rw [h, hg_m, hg_m1]
        exact tt_braid hT hc hd hcd
    · rcases (by omega : j < m ∨ j = m ∨ j = m + 1) with h | h | h
      · have h1 := (isCoxeterA_adjSwap m).comm i j hij h
        have h2 := congrArg (fun σ => ((L.φ.symm σ : ↥(LocalGroup E d)) : X)) h1
        simpa [map_mul, hg_lt i (by omega), hg_lt j h] using h2
      · have hi' : i < m := by omega
        rw [h, hg_m]
        by_contra hne
        have := (hgc i hi').1 hne
        omega
      · have hi' : i < m := by omega
        rw [h, hg_m1]
        exact hgd i hi'
  obtain ⟨Ψ, hΨ⟩ := exists_hom_perm (m + 2) g hcox
  refine ⟨Ψ, fun i hi => ?_, ?_, ?_⟩
  · rw [hΨ i (by omega), hg_lt i hi]
  · rw [hΨ m (by omega), hg_m]
  · rw [hΨ (m + 1) (by omega), hg_m1]

theorem adjSwap_zero_ne_one {m : ℕ} (hm : 2 ≤ m) : adjSwap m 0 ≠ adjSwap m 1 := by
  intro h
  have := congrArg (fun σ : Perm (Fin (m + 1)) => σ ⟨0, by omega⟩) h
  simp only [adjSwap_of_lt (by omega : 0 < m), adjSwap_of_lt (by omega : 1 < m)] at this
  rw [swap_apply_left, swap_apply_of_ne_of_ne] at this
  · simp [Fin.ext_iff] at this
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

theorem injective_of_ne_one {m : ℕ} (hm : 2 ≤ m) (Ψ : Perm (Fin (m + 2 + 1)) →* X)
    (h : Ψ (adjSwap (m + 2) 0) * Ψ (adjSwap (m + 2) 1) ≠ 1) : Function.Injective Ψ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hnt : Nontrivial Ψ.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin (m + 2 + 1))
    (by simp; omega) (N := Ψ.ker) hnt
  have hmem : adjSwap (m + 2) 0 * adjSwap (m + 2) 1 ∈ alternatingGroup (Fin (m + 2 + 1)) := by
    rw [Equiv.Perm.mem_alternatingGroup, adjSwap_of_lt (by omega : 0 < m + 2),
      adjSwap_of_lt (by omega : 1 < m + 2), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by simp), Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
    norm_num
  exact h (by simpa using hle hmem)

theorem image_swap_mem (hP : Pair X E) {m : ℕ} (hd : d ∈ E) (Ψ : Perm (Fin (m + 2 + 1)) →* X)
    (hΨd : Ψ (adjSwap (m + 2) (m + 1)) = d) {s : Perm (Fin (m + 2 + 1))} (hs : s.IsSwap) :
    Ψ s ∈ E := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨a1, b1, hab1, h1⟩ := adjSwap_isSwap (m := m + 2) (i := m + 1) (by omega)
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_swap hab1 hab)
  have : Ψ (swap a b) = Ψ g * d * (Ψ g)⁻¹ := by
    rw [← hg, ← h1, map_mul, map_mul, map_inv, hΨd]
  rw [this]
  exact Pair.conj_mem hP hd _

theorem localClass_subset_image {m : ℕ} (hm : 0 < m) (L : LocalIso E d (m + 1))
    (Ψ : Perm (Fin (m + 2 + 1)) →* X)
    (hΨ : ∀ i < m, Ψ (adjSwap (m + 2) i) = ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X)) :
    LocalClass E d ⊆ Ψ '' {σ | σ.IsSwap} := by
  intro e he
  let Θ : Perm (Fin (m + 1)) →* X := (LocalGroup E d).subtype.comp L.φ.symm.toMonoidHom
  have hΘ : ∀ w, Θ w = ((L.φ.symm w : ↥(LocalGroup E d)) : X) := fun w => rfl
  have hrange : ∀ w, Θ w ∈ Ψ.range := by
    intro w
    have hw : w ∈ Subgroup.closure (adjSwap m '' Set.Iio m) := by
      rw [closure_adjSwap m]
      trivial
    induction hw using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact ⟨adjSwap (m + 2) i, by rw [hΨ i hi, hΘ]⟩
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  have hτ : (L.φ ⟨e, mem_localGroup he⟩).IsSwap := L.swap_of_mem he
  have he' : e = Θ (L.φ ⟨e, mem_localGroup he⟩) := by rw [hΘ]; simp
  obtain ⟨a, b, hab, hτab⟩ := hτ
  obtain ⟨a0, b0, hab0, h0⟩ := adjSwap_isSwap hm
  obtain ⟨w, hw⟩ := isConj_iff.1 (isConj_swap hab0 hab)
  obtain ⟨w', hw'⟩ := hrange w
  refine ⟨w' * adjSwap (m + 2) 0 * w'⁻¹, isSwap_conj' (adjSwap_isSwap (by omega)) w', ?_⟩
  have h3 : Θ (w * adjSwap m 0 * w⁻¹) = e := by
    rw [h0, hw, ← hτab]
    exact he'.symm
  rw [map_mul, map_mul, map_inv, hw', hΨ 0 hm, ← hΘ (adjSwap m 0), ← map_inv, ← map_mul, ← map_mul]
  exact h3

theorem star_subset_image (hP : Pair X E) {m : ℕ} (hm : 0 < m) (L : LocalIso E d (m + 1))
    (Ψ : Perm (Fin (m + 2 + 1)) →* X)
    (hΨ : ∀ i < m, Ψ (adjSwap (m + 2) i) = ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X))
    (hΨd : Ψ (adjSwap (m + 2) (m + 1)) = d) {t e : X} (ht : t ∈ Ψ '' {σ | σ.IsSwap})
    (he : e ∈ LocalClass E t) : e ∈ Ψ '' {σ | σ.IsSwap} := by
  obtain ⟨s, ⟨a, b, hab, hsab⟩, rfl⟩ := ht
  obtain ⟨a1, b1, hab1, h1⟩ := adjSwap_isSwap (m := m + 2) (i := m + 1) (by omega)
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_swap hab1 hab)
  have hs' : Ψ s = Ψ g * d * (Ψ g)⁻¹ := by
    rw [hsab, ← hg, ← h1, map_mul, map_mul, map_inv, hΨd]
  rw [hs'] at he
  have he' : (Ψ g)⁻¹ * e * Ψ g ∈ LocalClass E d := by
    have := (Pair.conj_mem_localClass_iff hP (Ψ g) (e := d) (f := (Ψ g)⁻¹ * e * Ψ g)).1
    refine this ?_
    rw [show Ψ g * ((Ψ g)⁻¹ * e * Ψ g) * (Ψ g)⁻¹ = e by group]
    exact he
  obtain ⟨s', hs'', hs'e⟩ := localClass_subset_image hm L Ψ hΨ he'
  refine ⟨g * s' * g⁻¹, isSwap_conj' hs'' g, ?_⟩
  rw [map_mul, map_mul, map_inv, hs'e]
  group

theorem image_swaps_eq (hP : Pair X E) (hconn : (commGraph E).Connected) {m : ℕ} (hm : 0 < m)
    (hd : d ∈ E) (L : LocalIso E d (m + 1)) (Ψ : Perm (Fin (m + 2 + 1)) →* X)
    (hΨ : ∀ i < m, Ψ (adjSwap (m + 2) i) = ((L.φ.symm (adjSwap m i) : ↥(LocalGroup E d)) : X))
    (hΨd : Ψ (adjSwap (m + 2) (m + 1)) = d) : Ψ '' {σ | σ.IsSwap} = E := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact image_swap_mem hP hd Ψ hΨd hs
  · intro hx
    have hdT : d ∈ Ψ '' {σ | σ.IsSwap} := ⟨adjSwap (m + 2) (m + 1), adjSwap_isSwap (by omega), hΨd⟩
    exact reachable_induction (G := commGraph E) (p := fun a : E => (a : X) ∈ Ψ '' {σ | σ.IsSwap})
      (fun a b hab ha => star_subset_image hP hm L Ψ hΨ hΨd ha
        ⟨b.2, fun h => hab.1 (Subtype.ext h.symm), hab.2.symm⟩)
      (hconn ⟨d, hd⟩ ⟨x, hx⟩) hdT

theorem symmetric_char {m : ℕ} (hI : PermInput (m + 1)) (hm : 2 ≤ m) (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
    (hna : ∃ a b : commutator X, a * b ≠ b * a) (hd : d ∈ E) (L : LocalIso E d (m + 1)) :
    ∃ Ψ : Perm (Fin (m + 2 + 1)) ≃* X, Ψ '' {σ | σ.IsSwap} = E := by
  have := Pair.finite hP
  obtain ⟨x₀, hx₀E, hx₀d⟩ : ∃ x ∈ E, x * d ≠ d * x := by
    by_contra! hall
    have hc : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 hall
    rw [hZ, Subgroup.mem_bot] at hc
    exact Pair.ne_one hP hd hc
  obtain ⟨p₀, hp₀⟩ := exists_star hI (by omega) hP hZ hS hna hd L ⟨hx₀E, hx₀d⟩
  obtain ⟨k, hk⟩ : ∃ k : Perm (Fin (m + 1)), k p₀ = Fin.last m :=
    ⟨swap p₀ (Fin.last m), swap_apply_left _ _⟩
  have hstar : ∀ e (he : e ∈ LocalClass E d),
      (e * x₀ ≠ x₀ * e ↔ (L.conj k).φ ⟨e, mem_localGroup he⟩ (Fin.last m) ≠ Fin.last m) := by
    intro e he
    rw [hp₀ e he]
    have h1 : (L.conj k).φ ⟨e, mem_localGroup he⟩ (Fin.last m) =
        k (L.φ ⟨e, mem_localGroup he⟩ p₀) := by
      show (k * L.φ ⟨e, mem_localGroup he⟩ * k⁻¹) (Fin.last m) = _
      rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_def, (Equiv.symm_apply_eq k).2 hk.symm]
    rw [h1, ← hk]
    exact (not_congr k.injective.eq_iff).symm
  obtain ⟨Ψ, hΨ, hΨc, hΨd⟩ := coxeter_build hP hd (L.conj k) hx₀E hx₀d hstar
  have h01 : Ψ (adjSwap (m + 2) 0) * Ψ (adjSwap (m + 2) 1) ≠ 1 := by
    rw [hΨ 0 (by omega), hΨ 1 (by omega)]
    intro h
    have h' : ((L.conj k).φ.symm (adjSwap m 0) * (L.conj k).φ.symm (adjSwap m 1) :
        ↥(LocalGroup E d)) = 1 := Subtype.ext h
    rw [← map_mul] at h'
    have h'' := (L.conj k).φ.symm.injective (h'.trans (map_one _).symm)
    apply adjSwap_zero_ne_one hm
    rw [eq_inv_of_mul_eq_one_left h'']
    exact inv_eq_of_mul_eq_one_right ((isCoxeterA_adjSwap m).sq 1 (by omega))
  have hinj : Function.Injective Ψ := injective_of_ne_one hm Ψ h01
  have himg := image_swaps_eq hP (Pair.connected_of_nonabelian hP hS hna) (by omega) hd (L.conj k)
    Ψ hΨ hΨd
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
    intro e he
    rw [← himg] at he
    obtain ⟨s, _, rfl⟩ := he
    exact ⟨s, rfl⟩
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, himg⟩

end CFSG.RankThree.PartOne.FIS
