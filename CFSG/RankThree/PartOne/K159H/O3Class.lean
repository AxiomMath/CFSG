module

public import CFSG.RankThree.PartOne.K159H.O3Basic

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  (S : Subgroup (Fin r → Kˣ))

abbrev TrivOn (j : Fin r ⊕ Fin r) : Prop := ∀ d ∈ S, wt d j = 1

abbrev SimOn (j j' : Fin r ⊕ Fin r) : Prop := ∀ d ∈ S, wt d j = wt d j'

theorem SimOn.refl (j : Fin r ⊕ Fin r) : SimOn S j j := fun _ _ => rfl

theorem SimOn.symm {j j' : Fin r ⊕ Fin r} (h : SimOn S j j') : SimOn S j' j := fun d hd => (h d hd).symm

theorem SimOn.trans {j j' j'' : Fin r ⊕ Fin r} (h : SimOn S j j') (h' : SimOn S j' j'') : SimOn S j j'' :=
  fun d hd => (h d hd).trans (h' d hd)

theorem TrivOn.swap {j : Fin r ⊕ Fin r} (h : TrivOn S j) : TrivOn S j.swap := fun d hd => by
  rw [wt_swap, h d hd, inv_one]

theorem trivOn_swap_iff (j : Fin r ⊕ Fin r) : TrivOn S j.swap ↔ TrivOn S j :=
  ⟨fun h => by simpa [Sum.swap_swap] using h.swap S, fun h => h.swap S⟩

theorem TrivOn.of_sim {j j' : Fin r ⊕ Fin r} (h : SimOn S j j') (hj : TrivOn S j) : TrivOn S j' :=
  fun d hd => (h d hd).symm.trans (hj d hd)

theorem unit_eq_one_of_sq_eq_one [CharP K 2] {u : Kˣ} (h : u ^ 2 = 1) : u = 1 := by
  have h2 : ((u : K) - 1) ^ 2 = 0 := by
    have h' : (u : K) ^ 2 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      simpa using this
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h' + (1 - (u : K)) * this
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h2
  exact Units.ext (by simpa [sub_eq_zero] using this)

theorem not_sim_swap [CharP K 2] {j : Fin r ⊕ Fin r} (hj : ¬ TrivOn S j) : ¬ SimOn S j j.swap := by
  intro h
  apply hj
  intro d hd
  have h1 := h d hd
  rw [wt_swap] at h1
  apply unit_eq_one_of_sq_eq_one
  rw [pow_two]
  calc wt d j * wt d j = wt d j * (wt d j)⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel _

theorem eq_swap_of_coordIdx_eq {j j' : Fin r ⊕ Fin r} (h : coordIdx j = coordIdx j') (hne : j ≠ j') :
    j' = j.swap := by
  rcases j with k | k <;> rcases j' with k' | k' <;> simp_all [coordIdx]

theorem coordIdx_ne_of_sim [CharP K 2] {j j' : Fin r ⊕ Fin r} (hj : ¬ TrivOn S j) (h : SimOn S j j')
    (hne : j ≠ j') : coordIdx j ≠ coordIdx j' := by
  intro h1
  have := eq_swap_of_coordIdx_eq h1 hne
  subst this
  exact not_sim_swap S hj h

theorem simOn_swap_iff (j j' : Fin r ⊕ Fin r) : SimOn S j' j.swap ↔ SimOn S j'.swap j := by
  constructor
  · intro h d hd
    have h1 := h d hd
    rw [wt_swap] at h1 ⊢
    rw [h1, inv_inv]
  · intro h d hd
    have h1 := h d hd
    rw [wt_swap] at h1 ⊢
    rw [← h1, inv_inv]

variable {S}

theorem comm_apply {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {d : Fin r → Kˣ}
    (hg : g * torH K A r d = torH K A r d * g) (v : (Fin r ⊕ Fin r → K) × A) :
    torH K A r d (g v) = g (torH K A r d v) := by
  have := congrArg (fun e : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) => e v) hg
  exact this.symm

theorem entry_eq_zero {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {d : Fin r → Kˣ}
    (hg : g * torH K A r d = torH K A r d * g) {j c : Fin r ⊕ Fin r} (hne : wt d c ≠ wt d j) :
    (g (hypVec K A j)).1 c = 0 := by
  have h1 := comm_apply hg (hypVec K A j)
  rw [torH_hypVec, map_smul] at h1
  have h2 := congrFun (congrArg Prod.fst h1) c
  rw [torH_fst, Prod.smul_fst, Pi.smul_apply, smul_eq_mul] at h2
  have : ((wt d c : K) - wt d j) * (g (hypVec K A j)).1 c = 0 := by linear_combination h2
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr fun h' => hne (Units.ext h'))

theorem entry_coord_eq_zero {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ d ∈ S, g * torH K A r d = torH K A r d * g) {j c : Fin r ⊕ Fin r} (h : ¬ SimOn S c j) :
    (g (hypVec K A j)).1 c = 0 := by
  unfold SimOn at h
  push Not at h
  obtain ⟨d, hd, hne⟩ := h
  exact entry_eq_zero (hg d hd) hne

theorem entry_snd_eq_zero {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hg : ∀ d ∈ S, g * torH K A r d = torH K A r d * g) {j : Fin r ⊕ Fin r} (h : ¬ TrivOn S j) :
    (g (hypVec K A j)).2 = 0 := by
  unfold TrivOn at h
  push Not at h
  obtain ⟨d, hd, hne⟩ := h
  have h1 := comm_apply (hg d hd) (hypVec K A j)
  rw [torH_hypVec, map_smul] at h1
  have h2 := congrArg Prod.snd h1
  rw [torH_snd, Prod.smul_snd] at h2
  have h3 : ((wt d j : K) - 1) • (g (hypVec K A j)).2 = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr fun h' => hne (Units.ext h'))

end CFSG.RankThree.PartOne.K159H
