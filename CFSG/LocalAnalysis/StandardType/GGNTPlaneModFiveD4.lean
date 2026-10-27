module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def d4CentralChar : X3 := ![0, 0, 0, 1, 2, 0]

theorem pairVec_d4CentralChar_eq_zero {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kerRoots (reps 4)) :
    pairVec d4CentralChar α = 0 := by
  obtain ⟨hroot, hx⟩ := hα
  have key : ∀ α ∈ e6RootList, pairVec (reps 4) α = 0 → pairVec d4CentralChar α = 0 := by
    decide +kernel
  exact key α ((isRoot_iff_mem_e6RootList α).1 hroot) hx

private def d4i (n : Fin 6) : Fin Tag.E6.rank := ⟨n.val, n.isLt⟩

private def d4v (a b c d e f : ℤ) : Fin Tag.E6.rank → ℤ := ![a, b, c, d, e, f]

private def d4Moved : X3 := ![0, 0, 1, 2, 0, 0]

private theorem d4_reps_apply_zero : (reps 4 : X3) (d4i 0) = 0 := by decide

private theorem d4_reps_apply_one : (reps 4 : X3) (d4i 1) = 0 := by decide

private theorem d4_reps_apply_two : (reps 4 : X3) (d4i 2) = 1 := by decide

private theorem d4_reps_apply_three : (reps 4 : X3) (d4i 3) = 1 := by decide

private theorem d4_reps_apply_four : (reps 4 : X3) (d4i 4) = 1 := by decide

private theorem d4_reps_apply_five : (reps 4 : X3) (d4i 5) = 0 := by decide

private theorem d4_char_apply_zero : d4CentralChar (d4i 0) = 0 := by decide

private theorem d4_char_apply_one : d4CentralChar (d4i 1) = 0 := by decide

private theorem d4_char_apply_two : d4CentralChar (d4i 2) = 0 := by decide

private theorem d4_char_apply_three : d4CentralChar (d4i 3) = 1 := by decide

private theorem d4_char_apply_four : d4CentralChar (d4i 4) = 2 := by decide

private theorem d4_char_apply_five : d4CentralChar (d4i 5) = 0 := by decide

private theorem d4_single_mem (i : Fin 6) (hi : (reps 4 : X3) (d4i i) = 0) :
    (Pi.single (d4i i) 1 : Fin Tag.E6.rank → ℤ) ∈ kerRoots (reps 4) :=
  ⟨IsRoot.basis (d4i i), by rw [pairVec_single]; exact hi⟩

private theorem d4_reps_mem : (d4v 0 0 1 1 1 0 : Fin Tag.E6.rank → ℤ) ∈ kerRoots (reps 4) := by
  refine ⟨(isRoot_iff_mem_e6RootList _).2 (by decide +kernel), ?_⟩
  decide +kernel

private theorem d4_pairVec_reps_root (y : X3) :
    pairVec y (d4v 0 0 1 1 1 0) = y (d4i 2) + y (d4i 3) + y (d4i 4) := by
  decide +kernel +revert

private theorem d4_eq_smul_add_of_forall {y : X3}
    (hy : ∀ α ∈ kerRoots (reps 4), pairVec y α = 0) :
    ∃ c d : ZMod 3, y = c • reps 4 + d • d4CentralChar := by
  have h0 : y (d4i 0) = 0 := by
    have h := hy _ (d4_single_mem 0 d4_reps_apply_zero)
    rwa [pairVec_single] at h
  have h1 : y (d4i 1) = 0 := by
    have h := hy _ (d4_single_mem 1 d4_reps_apply_one)
    rwa [pairVec_single] at h
  have h5 : y (d4i 5) = 0 := by
    have h := hy _ (d4_single_mem 5 d4_reps_apply_five)
    rwa [pairVec_single] at h
  have hsum : y (d4i 2) + y (d4i 3) + y (d4i 4) = 0 := by
    have h := hy _ d4_reps_mem
    rwa [d4_pairVec_reps_root] at h
  have hthree : (3 : ZMod 3) = 0 := by decide
  refine ⟨y (d4i 2), y (d4i 3) - y (d4i 2), ?_⟩
  funext i
  obtain ⟨k, hk⟩ : ∃ k : Fin 6, d4i k = i := ⟨⟨i.val, i.isLt⟩, rfl⟩
  subst hk
  fin_cases k
  · change y (d4i 0) = y (d4i 2) * (reps 4 : X3) (d4i 0) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 0)
    rw [d4_reps_apply_zero, d4_char_apply_zero, h0]
    ring
  · change y (d4i 1) = y (d4i 2) * (reps 4 : X3) (d4i 1) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 1)
    rw [d4_reps_apply_one, d4_char_apply_one, h1]
    ring
  · change y (d4i 2) = y (d4i 2) * (reps 4 : X3) (d4i 2) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 2)
    rw [d4_reps_apply_two, d4_char_apply_two]
    ring
  · change y (d4i 3) = y (d4i 2) * (reps 4 : X3) (d4i 3) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 3)
    rw [d4_reps_apply_three, d4_char_apply_three]
    ring
  · change y (d4i 4) = y (d4i 2) * (reps 4 : X3) (d4i 4) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 4)
    rw [d4_reps_apply_four, d4_char_apply_four]
    linear_combination hsum - (y (d4i 3)) * hthree
  · change y (d4i 5) = y (d4i 2) * (reps 4 : X3) (d4i 5) +
      (y (d4i 3) - y (d4i 2)) * d4CentralChar (d4i 5)
    rw [d4_reps_apply_five, d4_char_apply_five, h5]
    ring

private theorem d4_smul_eq_of_mem {g : WeylGroup Tag.E6} {x : X3} (hg : g ∈ stabVec x) :
    g • x = x := by
  simpa [stabVec, MulAction.mem_stabilizer_iff] using hg

private theorem d4_inv_smul_eq_of_mem {g : WeylGroup Tag.E6} {x : X3} (hg : g ∈ stabVec x) :
    g⁻¹ • x = x := by
  calc g⁻¹ • x = g⁻¹ • (g • x) := by rw [d4_smul_eq_of_mem hg]
    _ = (g⁻¹ * g) • x := (mul_smul g⁻¹ g x).symm
    _ = x := by rw [inv_mul_cancel, one_smul]

private theorem d4_zmod3_cases (c : ZMod 3) (hc : c ≠ 0) : c = 1 ∨ c = 2 := by
  decide +kernel +revert


private theorem d4_pairVec_add_char (x y : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (x + y) v = pairVec x v + pairVec y v := by
  simp only [pairVec, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem d4_pairVec_smul_char (c : ZMod 3) (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (c • x) v = c * pairVec x v := by
  simp only [pairVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem d4_kerReflVec_le_stabVec :
    kerReflVec (reps 4) ≤ stabVec d4CentralChar :=
  kerReflVec_le_stabVec_of_forall fun _ hα => pairVec_d4CentralChar_eq_zero hα

private def d4Word : List (Fin Tag.E6.rank) :=
  ([3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3] : List (Fin 6)).map d4i

private def d4W0 : WeylGroup Tag.E6 := (d4Word.map (simple Tag.E6)).prod

private theorem d4W0_smul_reps : d4W0 • reps 4 = reps 4 := by
  rw [d4W0, ← applyWord_eq_prod_smul]
  decide +kernel

private theorem d4W0_smul_char : d4W0 • d4CentralChar = d4Moved := by
  rw [d4W0, ← applyWord_eq_prod_smul]
  decide +kernel

private theorem d4W0_mem_stabVec : d4W0 ∈ stabVec (reps 4) := by
  rw [stabVec, MulAction.mem_stabilizer_iff]
  exact d4W0_smul_reps

private theorem d4W0_notMem_stabVec_char : d4W0 ∉ stabVec d4CentralChar := by
  intro h
  rw [stabVec, MulAction.mem_stabilizer_iff] at h
  have hc := d4W0_smul_char
  rw [h] at hc
  exact absurd hc (by decide)

private theorem d4W0_notMem_kerReflVec : d4W0 ∉ kerReflVec (reps 4) :=
  fun h => d4W0_notMem_stabVec_char (d4_kerReflVec_le_stabVec h)

private theorem d4_kerReflVec_ne_stabVec : kerReflVec (reps 4) ≠ stabVec (reps 4) := by
  intro h
  exact d4W0_notMem_kerReflVec (h ▸ d4W0_mem_stabVec)

private theorem d4_subgroupOf_index_eq_three :
    ((kerReflVec (reps 4)).subgroupOf (stabVec (reps 4))).index = 3 := by
  have hT : kerReflVec (reps 4) = stabVec (reps 4) ∨
      (((kerRoots (reps 4)).ncard = 18 ∨ (kerRoots (reps 4)).ncard = 24) ∧
        ((kerReflVec (reps 4)).subgroupOf (stabVec (reps 4))).index = 3) := tableVec_rep 4
  rcases hT with h | ⟨-, hidx⟩
  · exact absurd h d4_kerReflVec_ne_stabVec
  · exact hidx

private theorem d4_relIndex_eq_three :
    (kerReflVec (reps 4)).relIndex (stabVec (reps 4)) = 3 := by
  have h := Subgroup.relIndex_subgroupOf (H := kerReflVec (reps 4)) (K := stabVec (reps 4))
    (L := stabVec (reps 4)) (le_refl _)
  rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
  rw [← h, d4_subgroupOf_index_eq_three]

theorem stabVec_inf_stabVec_d4CentralChar :
    stabVec (reps 4) ⊓ stabVec d4CentralChar = kerReflVec (reps 4) := by
  have hKleH : kerReflVec (reps 4) ≤ stabVec (reps 4) ⊓ stabVec d4CentralChar :=
    le_inf (kerReflVec_le_stabVec (reps 4)) d4_kerReflVec_le_stabVec
  have hHleS : stabVec (reps 4) ⊓ stabVec d4CentralChar ≤ stabVec (reps 4) := inf_le_left
  have htower : (kerReflVec (reps 4)).relIndex (stabVec (reps 4) ⊓ stabVec d4CentralChar) *
      (stabVec (reps 4) ⊓ stabVec d4CentralChar).relIndex (stabVec (reps 4)) = 3 := by
    rw [Subgroup.relIndex_mul_relIndex (kerReflVec (reps 4))
      (stabVec (reps 4) ⊓ stabVec d4CentralChar) (stabVec (reps 4)) hKleH hHleS,
      d4_relIndex_eq_three]
  have hHne : (stabVec (reps 4) ⊓ stabVec d4CentralChar).relIndex (stabVec (reps 4)) ≠ 1 := by
    intro h1
    have hSH : stabVec (reps 4) ≤ stabVec (reps 4) ⊓ stabVec d4CentralChar :=
      (Subgroup.relIndex_eq_one).1 h1
    exact d4W0_notMem_stabVec_char (hSH d4W0_mem_stabVec).2
  have hKrel : (kerReflVec (reps 4)).relIndex (stabVec (reps 4) ⊓ stabVec d4CentralChar) = 1 := by
    have hdvd : (stabVec (reps 4) ⊓ stabVec d4CentralChar).relIndex (stabVec (reps 4)) ∣ 3 :=
      ⟨(kerReflVec (reps 4)).relIndex (stabVec (reps 4) ⊓ stabVec d4CentralChar),
        by rw [mul_comm]; exact htower.symm⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd (by decide : Nat.Prime 3)
      ((stabVec (reps 4) ⊓ stabVec d4CentralChar).relIndex (stabVec (reps 4))) hdvd with h1 | h3
    · exact absurd h1 hHne
    · have h2 : (kerReflVec (reps 4)).relIndex (stabVec (reps 4) ⊓ stabVec d4CentralChar) * 3 =
          1 * 3 := by rw [h3] at htower; simpa using htower
      exact Nat.eq_of_mul_eq_mul_right (by decide) h2
  exact le_antisymm ((Subgroup.relIndex_eq_one).1 hKrel) hKleH

private theorem d4_pow_three_mem_kerReflVec
    {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4)) :
    g ^ 3 ∈ kerReflVec (reps 4) := by
  have hnorm : stabVec (reps 4) ≤ Subgroup.normalizer ↑(kerReflVec (reps 4)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := kerReflVec_smul x (reps 4)
    have hx' : x • reps 4 = reps 4 := by
      simpa [stabVec, MulAction.mem_stabilizer_iff] using hx
    rw [hx'] at h
    exact h.symm
  haveI : ((kerReflVec (reps 4)).subgroupOf (stabVec (reps 4))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (kerReflVec_le_stabVec (reps 4))).2 hnorm
  have h3 : (⟨g, hg⟩ : ↥(stabVec (reps 4))) ^ 3 ∈
      (kerReflVec (reps 4)).subgroupOf (stabVec (reps 4)) := by
    have h := Subgroup.pow_index_mem ((kerReflVec (reps 4)).subgroupOf (stabVec (reps 4)))
      (⟨g, hg⟩ : ↥(stabVec (reps 4)))
    rwa [d4_subgroupOf_index_eq_three] at h
  simpa using Subgroup.mem_subgroupOf.1 h3

private def d4Class (j : ZMod 3) : Finset (Fin Tag.E6.rank → ℤ) :=
  if j = 0 then
    {d4v (-1) (-1) (-1) (-2) (-2) (-1), d4v 0 (-1) (-1) (-2) (-2) (-1),
      d4v 0 (-1) 0 (-1) (-1) (-1), d4v 0 (-1) 0 (-1) (-1) 0, d4v 0 0 0 (-1) (-1) (-1),
      d4v 0 0 0 (-1) (-1) 0, d4v 0 0 1 0 0 0, d4v 1 0 1 0 0 0}
  else if j = 1 then
    {d4v 0 0 0 1 0 0, d4v 0 1 0 1 0 0, d4v 0 1 1 2 1 0, d4v 0 1 1 2 1 1, d4v 1 1 1 2 1 0,
      d4v 1 1 1 2 1 1, d4v 1 1 2 3 2 1, d4v 1 2 2 3 2 1}
  else
    {d4v (-1) (-1) (-2) (-2) (-1) (-1), d4v (-1) (-1) (-2) (-2) (-1) 0,
      d4v (-1) (-1) (-1) (-1) 0 0, d4v (-1) 0 (-1) (-1) 0 0, d4v 0 (-1) (-1) (-1) 0 0,
      d4v 0 0 (-1) (-1) 0 0, d4v 0 0 0 0 1 0, d4v 0 0 0 0 1 1}

private theorem d4_d4Class_card (j : ZMod 3) : (d4Class j).card = 8 := by
  decide +kernel +revert

private theorem d4_mem_d4Class_iff_list (j : ZMod 3) :
    ∀ α ∈ e6RootList,
      (α ∈ d4Class j ↔ pairVec (reps 4) α = 1 ∧ pairVec d4CentralChar α = j) := by
  decide +kernel +revert

private theorem d4_d4Class_subset_list (j : ZMod 3) : ∀ α ∈ d4Class j, α ∈ e6RootList := by
  decide +kernel +revert

private theorem d4_mem_d4Class {j : ZMod 3} {α : Fin Tag.E6.rank → ℤ} :
    α ∈ d4Class j ↔ IsRoot Tag.E6 α ∧ pairVec (reps 4) α = 1 ∧ pairVec d4CentralChar α = j := by
  constructor
  · intro h
    have hlist := d4_d4Class_subset_list j α h
    exact ⟨(isRoot_iff_mem_e6RootList α).2 hlist,
      (d4_mem_d4Class_iff_list j α hlist).1 h⟩
  · rintro ⟨hroot, h1, h2⟩
    exact (d4_mem_d4Class_iff_list j α ((isRoot_iff_mem_e6RootList α).1 hroot)).2 ⟨h1, h2⟩

private theorem d4_mem_d4Class_smul {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar)
    {j : ZMod 3} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ d4Class j) :
    g • α ∈ d4Class (c + d * j) := by
  obtain ⟨hroot, hx, hf⟩ := d4_mem_d4Class.1 hα
  have hfix : g⁻¹ • reps 4 = reps 4 := d4_inv_smul_eq_of_mem hg
  have hx' : pairVec (reps 4) (g • α) = pairVec (reps 4) α := by
    have h := (pairVec_smul (g⁻¹) (reps 4) α).symm
    rw [inv_inv, hfix] at h
    exact h
  have hf' : pairVec d4CentralChar (g • α) = c + d * j := by
    have h := (pairVec_smul (g⁻¹) d4CentralChar α).symm
    rw [inv_inv, hdec, d4_pairVec_add_char, d4_pairVec_smul_char, d4_pairVec_smul_char,
      hx, hf] at h
    rw [h]
    ring
  rw [d4_mem_d4Class]
  exact ⟨IsRoot.smul hroot g, hx'.trans hx, hf'⟩

private theorem d4_class_image {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar) (j : ZMod 3) :
    (d4Class j).image (fun α => g • α) = d4Class (c + d * j) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro α hα
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hα
    exact d4_mem_d4Class_smul hg hdec hβ
  · exact Nat.le_of_eq (by
      rw [Finset.card_image_of_injective _ (MulAction.injective g), d4_d4Class_card,
        d4_d4Class_card])

private def d4PowSum (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) (k : ℕ) (j : ZMod 3) : ZMod 5 :=
  ∑ α ∈ d4Class j, (μ α) ^ k

private theorem d4_powSum_smul {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {κ : ZMod 5}
    (hμ : ∀ v, μ (g • v) = κ * μ v) (k : ℕ) (j : ZMod 3) :
    d4PowSum μ k (c + d * j) = κ ^ k * d4PowSum μ k j := by
  have himg := d4_class_image hg hdec j
  calc d4PowSum μ k (c + d * j) = ∑ α ∈ d4Class (c + d * j), (μ α) ^ k := rfl
    _ = ∑ α ∈ (d4Class j).image (fun α => g • α), (μ α) ^ k := by rw [himg]
    _ = ∑ α ∈ d4Class j, (μ (g • α)) ^ k :=
          Finset.sum_image (fun a _ b _ hab => MulAction.injective g hab)
    _ = ∑ α ∈ d4Class j, (κ * μ α) ^ k := Finset.sum_congr rfl fun α _ => by rw [hμ α]
    _ = ∑ α ∈ d4Class j, κ ^ k * (μ α) ^ k :=
          Finset.sum_congr rfl fun α _ => by rw [mul_pow]
    _ = κ ^ k * ∑ α ∈ d4Class j, (μ α) ^ k := by rw [Finset.mul_sum]
    _ = κ ^ k * d4PowSum μ k j := rfl

private theorem d4_affine_const {p : ZMod 3 → ZMod 5} {c : ZMod 3} (hc : c ≠ 0)
    (h : ∀ j, p (c + j) = p j) : p 0 = p 1 ∧ p 1 = p 2 := by
  rcases d4_zmod3_cases c hc with rfl | rfl
  · refine ⟨?_, ?_⟩
    · simpa using (h 0).symm
    · have h1 := h 1
      rw [show (1 : ZMod 3) + 1 = 2 from by decide] at h1
      exact h1.symm
  · refine ⟨?_, ?_⟩
    · have h1 := h 1
      rw [show (2 : ZMod 3) + 1 = 0 from by decide] at h1
      exact h1
    · have h0 := h 0
      rw [show (2 : ZMod 3) + 0 = 2 from by decide] at h0
      have h1 : p 0 = p 1 := by
        have h := h 1
        rw [show (2 : ZMod 3) + 1 = 0 from by decide] at h
        exact h
      rw [h0, h1]

private theorem d4_const_apply {p : ZMod 3 → ZMod 5} (h01 : p 0 = p 1) (h12 : p 1 = p 2)
    (c : ZMod 3) : p c = p 0 := by
  rcases eq_or_ne c 0 with h | h
  · rw [h]
  · rcases d4_zmod3_cases c h with rfl | rfl
    · exact h01.symm
    · exact h12.symm.trans h01.symm

private theorem d4_affine_zero {p : ZMod 3 → ZMod 5} {c : ZMod 3} {κ : ZMod 5}
    (h01 : p 0 = p 1) (h12 : p 1 = p 2) (h : ∀ j, p (c + j) = κ * p j) (hκ : κ = 4) :
    p 0 = 0 := by
  have h0 := h 0
  simp only [add_zero] at h0
  rw [d4_const_apply h01 h12 c, hκ] at h0
  have h3 : (3 : ZMod 5) * p 0 = 0 := by linear_combination -h0
  calc p 0 = (2 * 3 : ZMod 5) * p 0 := by
        rw [show (2 * 3 : ZMod 5) = 1 from by decide, one_mul]
    _ = 2 * ((3 : ZMod 5) * p 0) := by ring
    _ = 0 := by rw [h3, mul_zero]

private theorem d4_pairVec_char_smul {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar)
    {j : ZMod 3} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ d4Class j) :
    pairVec d4CentralChar (g • α) = c + d * j := by
  obtain ⟨-, hx, hf⟩ := d4_mem_d4Class.1 hα
  have hfix : g⁻¹ • reps 4 = reps 4 := d4_inv_smul_eq_of_mem hg
  have h := (pairVec_smul (g⁻¹) d4CentralChar α).symm
  rw [inv_inv, hdec, d4_pairVec_add_char, d4_pairVec_smul_char, d4_pairVec_smul_char,
    hx, hf] at h
  rw [h]
  ring

private theorem d4_pairVec_char_smul_three {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar)
    {j : ZMod 3} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ d4Class j) :
    pairVec d4CentralChar (g • (g • (g • α))) = c + d * (c + d * (c + d * j)) := by
  have h1 : g • α ∈ d4Class (c + d * j) := d4_mem_d4Class_smul hg hdec hα
  have h2 : g • (g • α) ∈ d4Class (c + d * (c + d * j)) := d4_mem_d4Class_smul hg hdec h1
  exact d4_pairVec_char_smul hg hdec h2

private theorem d4_d_cube_eq_one
    {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    {c d : ZMod 3} (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar) :
    d ^ 3 = 1 := by
  have hα0 : (d4v 0 0 1 0 0 0 : Fin Tag.E6.rank → ℤ) ∈ d4Class 0 := by
    rw [d4_mem_d4Class]
    exact ⟨(isRoot_iff_mem_e6RootList _).2 (by decide +kernel), by decide, by decide⟩
  have hα1 : (d4v 0 0 0 1 0 0 : Fin Tag.E6.rank → ℤ) ∈ d4Class 1 := by
    rw [d4_mem_d4Class]
    exact ⟨(isRoot_iff_mem_e6RootList _).2 (by decide +kernel), by decide, by decide⟩
  have hfix : ∀ α : Fin Tag.E6.rank → ℤ,
      pairVec d4CentralChar ((g ^ 3) • α) = pairVec d4CentralChar α := by
    intro α
    have h3 : g ^ 3 ∈ stabVec d4CentralChar :=
      d4_kerReflVec_le_stabVec (d4_pow_three_mem_kerReflVec hg)
    have h := (pairVec_smul ((g ^ 3)⁻¹) d4CentralChar α).symm
    rw [inv_inv, d4_inv_smul_eq_of_mem h3] at h
    exact h
  have h3 : g ^ 3 = g * (g * g) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, show (2 : ℕ) = 1 + 1 from rfl, pow_succ,
      pow_one, mul_assoc]
  have hpow : ∀ α : Fin Tag.E6.rank → ℤ, (g ^ 3) • α = g • (g • (g • α)) := by
    intro α
    rw [h3, mul_smul, mul_smul]
  have e0 : c + d * (c + d * (c + d * 0)) = 0 := by
    have h := hfix (d4v 0 0 1 0 0 0)
    rw [hpow, d4_pairVec_char_smul_three hg hdec hα0] at h
    rw [h, (d4_mem_d4Class.1 hα0).2.2]
  have e1 : c + d * (c + d * (c + d * 1)) = 1 := by
    have h := hfix (d4v 0 0 0 1 0 0)
    rw [hpow, d4_pairVec_char_smul_three hg hdec hα1] at h
    rw [h, (d4_mem_d4Class.1 hα1).2.2]
  linear_combination e1 - e0

private theorem d4_c_ne_zero
    {g : WeylGroup Tag.E6} (hg : g ∈ stabVec (reps 4))
    (hg' : g ∉ kerReflVec (reps 4)) {c : ZMod 3}
    (hdec : g⁻¹ • d4CentralChar = c • reps 4 + d4CentralChar) : c ≠ 0 := by
  intro hc
  apply hg'
  have hfix : g ∈ stabVec d4CentralChar := by
    rw [stabVec, MulAction.mem_stabilizer_iff]
    have h1 : g⁻¹ • d4CentralChar = d4CentralChar := by rw [hdec, hc]; simp
    calc g • d4CentralChar = g • (g⁻¹ • d4CentralChar) := by rw [h1]
      _ = d4CentralChar := by rw [smul_inv_smul]
  have hmem : g ∈ stabVec (reps 4) ⊓ stabVec d4CentralChar := ⟨hg, hfix⟩
  rwa [stabVec_inf_stabVec_d4CentralChar] at hmem

private theorem d4_d_eq_one {d : ZMod 3} (h : d ^ 3 = 1) : d = 1 := by
  rcases eq_or_ne d 0 with h0 | h0
  · subst h0
    exact absurd h (by decide)
  · rcases d4_zmod3_cases d h0 with rfl | rfl
    · rfl
    · exact absurd h (by decide)

private theorem d4_mu_apply (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) (α : Fin Tag.E6.rank → ℤ) :
    μ α = ∑ i, (α i : ZMod 5) * μ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum α]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_eq_mul]

private def d4Poly (m : Fin Tag.E6.rank → ZMod 5) (k : ℕ) (j : ZMod 3) : ZMod 5 :=
  ∑ α ∈ d4Class j, (∑ i, (α i : ZMod 5) * m i) ^ k

private theorem d4PowSum_eq_d4Poly (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) (k : ℕ) (j : ZMod 3) :
    d4PowSum μ k j = d4Poly (fun i => μ (Pi.single i 1)) k j :=
  Finset.sum_congr rfl fun α _ => by rw [d4_mu_apply]

private def d4vecOf (g : Fin 6 → ZMod 5) : Fin Tag.E6.rank → ZMod 5 :=
  fun i => g ⟨i.val, i.isLt⟩

private theorem d4_sum_vecOf (g : Fin 6 → ZMod 5) (m : Fin Tag.E6.rank → ZMod 5) :
    (∑ i, (d4vecOf g) i * m i) =
      g 0 * m (d4i 0) + g 1 * m (d4i 1) + g 2 * m (d4i 2) + g 3 * m (d4i 3) +
        g 4 * m (d4i 4) + g 5 * m (d4i 5) := by
  rw [← Equiv.sum_comp (finCongr (by decide : 6 = Tag.E6.rank))]
  rw [Fin.sum_univ_six]
  rfl

private theorem d4_coord_sum_zero (i : Fin Tag.E6.rank) :
    (∑ α ∈ d4Class 0, (α i : ZMod 5)) = (d4vecOf ![0, 1, 0, 2, 2, 1]) i := by
  decide +kernel +revert

private theorem d4_coord_sum_two (i : Fin Tag.E6.rank) :
    (∑ α ∈ d4Class 2, (α i : ZMod 5)) = (d4vecOf ![1, 1, 2, 2, 0, 0]) i := by
  decide +kernel +revert

private theorem d4Poly_one_zero (m : Fin Tag.E6.rank → ZMod 5) :
    d4Poly m 1 0 = m (d4i 1) + 2 * m (d4i 3) + 2 * m (d4i 4) + m (d4i 5) := by
  simp only [d4Poly, pow_one]
  rw [Finset.sum_comm]
  rw [show (∑ i, ∑ α ∈ d4Class 0, (α i : ZMod 5) * m i) =
      ∑ i, (∑ α ∈ d4Class 0, (α i : ZMod 5)) * m i from
    Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]]
  rw [show (∑ i, (∑ α ∈ d4Class 0, (α i : ZMod 5)) * m i) =
      ∑ i, (d4vecOf ![0, 1, 0, 2, 2, 1]) i * m i from
    Finset.sum_congr rfl fun i _ => by rw [d4_coord_sum_zero i]]
  rw [d4_sum_vecOf]
  rw [show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 0 = 0 from by decide,
    show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 1 = 1 from by decide,
    show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 2 = 0 from by decide,
    show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 3 = 2 from by decide,
    show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 4 = 2 from by decide,
    show (![0, 1, 0, 2, 2, 1] : Fin 6 → ZMod 5) 5 = 1 from by decide]
  ring

private theorem d4Poly_one_two (m : Fin Tag.E6.rank → ZMod 5) :
    d4Poly m 1 2 = m (d4i 0) + m (d4i 1) + 2 * m (d4i 2) + 2 * m (d4i 3) := by
  simp only [d4Poly, pow_one]
  rw [Finset.sum_comm]
  rw [show (∑ i, ∑ α ∈ d4Class 2, (α i : ZMod 5) * m i) =
      ∑ i, (∑ α ∈ d4Class 2, (α i : ZMod 5)) * m i from
    Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]]
  rw [show (∑ i, (∑ α ∈ d4Class 2, (α i : ZMod 5)) * m i) =
      ∑ i, (d4vecOf ![1, 1, 2, 2, 0, 0]) i * m i from
    Finset.sum_congr rfl fun i _ => by rw [d4_coord_sum_two i]]
  rw [d4_sum_vecOf]
  rw [show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 0 = 1 from by decide,
    show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 1 = 1 from by decide,
    show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 2 = 2 from by decide,
    show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 3 = 2 from by decide,
    show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 4 = 0 from by decide,
    show (![1, 1, 2, 2, 0, 0] : Fin 6 → ZMod 5) 5 = 0 from by decide]
  ring

private def d4mOf (n : Fin 4 → ZMod 5) : Fin Tag.E6.rank → ZMod 5 :=
  d4vecOf ![-(n 0 + 2 * n 1 + 2 * n 2), n 0, n 1, n 2, n 3, -(n 0 + 2 * n 2 + 2 * n 3)]

private theorem d4mOf_apply_zero (n : Fin 4 → ZMod 5) :
    d4mOf n (d4i 0) = -(n 0 + 2 * n 1 + 2 * n 2) := rfl

private theorem d4mOf_apply_one (n : Fin 4 → ZMod 5) : d4mOf n (d4i 1) = n 0 := rfl

private theorem d4mOf_apply_two (n : Fin 4 → ZMod 5) : d4mOf n (d4i 2) = n 1 := rfl

private theorem d4mOf_apply_three (n : Fin 4 → ZMod 5) : d4mOf n (d4i 3) = n 2 := rfl

private theorem d4mOf_apply_four (n : Fin 4 → ZMod 5) : d4mOf n (d4i 4) = n 3 := rfl

private theorem d4mOf_apply_five (n : Fin 4 → ZMod 5) :
    d4mOf n (d4i 5) = -(n 0 + 2 * n 2 + 2 * n 3) := rfl

private theorem d4mOf_eq_zero :
    ∀ n : Fin 4 → ZMod 5, (∀ j, d4Poly (d4mOf n) 2 j = 0) →
      d4Poly (d4mOf n) 4 0 = d4Poly (d4mOf n) 4 1 →
      d4Poly (d4mOf n) 4 1 = d4Poly (d4mOf n) 4 2 → d4mOf n = 0 := by
  decide +kernel

private theorem d4_mu_eq_zero {μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5}
    (hm : (fun i => μ (Pi.single i 1)) = 0) : μ = 0 := by
  refine AddMonoidHom.ext fun α => ?_
  rw [d4_mu_apply, show (0 : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) α = 0 from rfl]
  have h : ∀ i, μ (Pi.single i 1) = 0 := fun i => congrFun hm i
  simp [h]

theorem modFive_eq_zero_of_mem_stabVec_rep_four
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w u : WeylGroup Tag.E6}
    (hw : w ∈ stabVec (reps 4)) (hμw : ∀ v, μ (w • v) = 2 * μ v)
    (hu : u ∈ stabVec (reps 4)) (hu' : u ∉ kerReflVec (reps 4)) (hμu : ∀ v, μ (u • v) = μ v) :
    μ = 0 := by
  have hdecomp : ∀ {g : WeylGroup Tag.E6}, g ∈ stabVec (reps 4) →
      ∃ c d : ZMod 3, g⁻¹ • d4CentralChar = c • reps 4 + d • d4CentralChar := by
    intro g hg
    refine d4_eq_smul_add_of_forall fun α hα => ?_
    rw [pairVec_smul (g⁻¹) d4CentralChar α, inv_inv]
    refine pairVec_d4CentralChar_eq_zero ⟨IsRoot.smul hα.1 g, ?_⟩
    calc pairVec (reps 4) (g • α) = pairVec (g⁻¹ • reps 4) α := by
          simpa only [inv_inv] using (pairVec_smul (g⁻¹) (reps 4) α).symm
      _ = pairVec (reps 4) α := by rw [d4_inv_smul_eq_of_mem hg]
      _ = 0 := hα.2
  obtain ⟨cu, du, hdu⟩ := hdecomp hu
  obtain ⟨cw, dw, hdw⟩ := hdecomp hw
  have hdu1 : du = 1 := d4_d_eq_one (d4_d_cube_eq_one hu hdu)
  have hdw1 : dw = 1 := d4_d_eq_one (d4_d_cube_eq_one hw hdw)
  rw [hdu1] at hdu
  rw [hdw1] at hdw
  have hcu : cu ≠ 0 := d4_c_ne_zero hu hu' (by simpa using hdu)
  have hu_aff : ∀ k : ℕ, d4PowSum μ k 0 = d4PowSum μ k 1 ∧
      d4PowSum μ k 1 = d4PowSum μ k 2 := by
    intro k
    refine d4_affine_const hcu fun j => ?_
    have h := d4_powSum_smul hu hdu μ (κ := 1) (fun v => by simpa using hμu v) k j
    simpa using h
  have hone : ∀ j : ZMod 3, d4PowSum μ 1 j = 0 := by
    intro j
    obtain ⟨h01, h12⟩ := hu_aff 1
    have hrel := d4_powSum_smul hw hdw μ (κ := 2) hμw 1 j
    rw [show (2 : ZMod 5) ^ 1 = 2 from by decide, one_mul] at hrel
    rw [d4_const_apply h01 h12 (cw + j), d4_const_apply h01 h12 j] at hrel
    have hP : d4PowSum μ 1 0 = 0 := by linear_combination -hrel
    rw [d4_const_apply h01 h12 j]
    exact hP
  have htwo : ∀ j : ZMod 3, d4PowSum μ 2 j = 0 := by
    intro j
    obtain ⟨h01, h12⟩ := hu_aff 2
    have hrel : ∀ j' : ZMod 3, d4PowSum μ 2 (cw + j') = 4 * d4PowSum μ 2 j' := by
      intro j'
      have h := d4_powSum_smul hw hdw μ (κ := 2) hμw 2 j'
      rw [show (2 : ZMod 5) ^ 2 = 4 from by decide, one_mul] at h
      simpa using h
    have hP : d4PowSum μ 2 0 = 0 := d4_affine_zero h01 h12 hrel rfl
    rw [d4_const_apply h01 h12 j]
    exact hP
  obtain ⟨h4a, h4b⟩ := hu_aff 4
  have hm0 : (fun i => μ (Pi.single i 1)) (d4i 0) =
      -((fun i => μ (Pi.single i 1)) (d4i 1) + 2 * (fun i => μ (Pi.single i 1)) (d4i 2) +
        2 * (fun i => μ (Pi.single i 1)) (d4i 3)) := by
    have h0 : d4Poly (fun i => μ (Pi.single i 1)) 1 2 = 0 := by
      rw [← d4PowSum_eq_d4Poly]
      exact hone 2
    rw [d4Poly_one_two] at h0
    linear_combination h0
  have hm5 : (fun i => μ (Pi.single i 1)) (d4i 5) =
      -((fun i => μ (Pi.single i 1)) (d4i 1) + 2 * (fun i => μ (Pi.single i 1)) (d4i 3) +
        2 * (fun i => μ (Pi.single i 1)) (d4i 4)) := by
    have h0 : d4Poly (fun i => μ (Pi.single i 1)) 1 0 = 0 := by
      rw [← d4PowSum_eq_d4Poly]
      exact hone 0
    rw [d4Poly_one_zero] at h0
    linear_combination h0
  obtain ⟨n, hn⟩ : ∃ n : Fin 4 → ZMod 5, (fun i => μ (Pi.single i 1)) = d4mOf n := by
    refine ⟨![(fun i => μ (Pi.single i 1)) (d4i 1), (fun i => μ (Pi.single i 1)) (d4i 2),
      (fun i => μ (Pi.single i 1)) (d4i 3), (fun i => μ (Pi.single i 1)) (d4i 4)], ?_⟩
    funext i
    obtain ⟨k, hk⟩ : ∃ k : Fin 6, d4i k = i := ⟨⟨i.val, i.isLt⟩, rfl⟩
    subst hk
    fin_cases k
    · change (fun i => μ (Pi.single i 1)) (d4i 0) = d4mOf _ (d4i 0)
      rw [d4mOf_apply_zero, hm0]
      rfl
    · change (fun i => μ (Pi.single i 1)) (d4i 1) = d4mOf _ (d4i 1)
      rw [d4mOf_apply_one]
      rfl
    · change (fun i => μ (Pi.single i 1)) (d4i 2) = d4mOf _ (d4i 2)
      rw [d4mOf_apply_two]
      rfl
    · change (fun i => μ (Pi.single i 1)) (d4i 3) = d4mOf _ (d4i 3)
      rw [d4mOf_apply_three]
      rfl
    · change (fun i => μ (Pi.single i 1)) (d4i 4) = d4mOf _ (d4i 4)
      rw [d4mOf_apply_four]
      rfl
    · change (fun i => μ (Pi.single i 1)) (d4i 5) = d4mOf _ (d4i 5)
      rw [d4mOf_apply_five, hm5]
      rfl
  have h2poly : ∀ j, d4Poly (d4mOf n) 2 j = 0 := fun j => by
    rw [← hn, ← d4PowSum_eq_d4Poly]
    exact htwo j
  have h4poly : d4Poly (d4mOf n) 4 0 = d4Poly (d4mOf n) 4 1 := by
    rw [← hn, ← d4PowSum_eq_d4Poly, ← d4PowSum_eq_d4Poly]
    exact h4a
  have h4poly' : d4Poly (d4mOf n) 4 1 = d4Poly (d4mOf n) 4 2 := by
    rw [← hn, ← d4PowSum_eq_d4Poly, ← d4PowSum_eq_d4Poly]
    exact h4b
  exact d4_mu_eq_zero (hn.trans (d4mOf_eq_zero n h2poly h4poly h4poly'))

private theorem d4_ncard_isRoot :
    ({α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} : Set _).ncard = 72 := by
  have hnod : e6RootList.Nodup := by decide +kernel
  have hset : {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} = ↑e6RootList.toFinset := by
    ext α
    simp [isRoot_iff_mem_e6RootList]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnod,
    show e6RootList.length = 72 from by decide +kernel]

private theorem d4_kerRoots_zero :
    kerRoots (0 : X3) = {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} := by
  ext α
  simp [kerRoots, pairVec]

private theorem d4_repKerCard_eq_four {k : Fin 7} (h : repKerCard k = 24) : k = 4 := by
  decide +kernel +revert

private theorem d4_ne_zero_of_ncard {x : X3} (hx : (kerRoots x).ncard = 24) : x ≠ 0 := by
  intro h
  have h1 : (kerRoots x).ncard = 72 := by rw [h, d4_kerRoots_zero]; exact d4_ncard_isRoot
  omega

private theorem d4_mem_stabVec_conj {g w : WeylGroup Tag.E6} {x : X3} :
    g⁻¹ * w * g ∈ stabVec x ↔ w ∈ stabVec (g • x) := by
  rw [stabVec, MulAction.mem_stabilizer_iff, stabVec, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h2 : g • ((g⁻¹ * w * g) • x) = g • x := by rw [h]
    simpa [mul_smul] using h2
  · intro h
    rw [mul_smul, mul_smul, h, inv_smul_smul]

private theorem d4_mem_kerReflVec_conj {g u : WeylGroup Tag.E6} {x : X3} :
    u ∈ kerReflVec (g • x) ↔ g⁻¹ * u * g ∈ kerReflVec x := by
  rw [kerReflVec_smul g x, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyeq⟩
    have hyeq' : g * y * g⁻¹ = u := hyeq
    have h : g⁻¹ * u * g = y := by rw [← hyeq']; group
    rwa [h]
  · intro h
    refine ⟨g⁻¹ * u * g, h, ?_⟩
    show g * (g⁻¹ * u * g) * g⁻¹ = u
    group

private noncomputable def d4pull (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) (g : WeylGroup Tag.E6) :
    (Fin Tag.E6.rank → ℤ) →+ ZMod 5 where
  toFun v := μ (g • v)
  map_zero' := by simp
  map_add' a b := by simp [smul_add]

private theorem d4_transport
    {x : X3} {g : WeylGroup Tag.E6} (hxg : x = g • reps 4)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w u : WeylGroup Tag.E6}
    (hw : w ∈ stabVec x) (hμw : ∀ v, μ (w • v) = 2 * μ v)
    (hu : u ∈ stabVec x) (hu' : u ∉ kerReflVec x) (hμu : ∀ v, μ (u • v) = μ v) :
    μ = 0 := by
  subst hxg
  have hw' : g⁻¹ * w * g ∈ stabVec (reps 4) :=
    (d4_mem_stabVec_conj (g := g) (x := reps 4)).2 hw
  have hu'0 : g⁻¹ * u * g ∈ stabVec (reps 4) :=
    (d4_mem_stabVec_conj (g := g) (x := reps 4)).2 hu
  have huk : g⁻¹ * u * g ∉ kerReflVec (reps 4) := by
    rw [← d4_mem_kerReflVec_conj (g := g) (x := reps 4)]
    exact hu'
  have hμ'w : ∀ v, d4pull μ g ((g⁻¹ * w * g) • v) = 2 * d4pull μ g v := by
    intro v
    show μ (g • ((g⁻¹ * w * g) • v)) = 2 * μ (g • v)
    rw [show g • ((g⁻¹ * w * g) • v) = w • (g • v) by
      rw [← mul_smul, ← mul_smul, show g * (g⁻¹ * w * g) = w * g by group]]
    rw [hμw]
  have hμ'u : ∀ v, d4pull μ g ((g⁻¹ * u * g) • v) = d4pull μ g v := by
    intro v
    show μ (g • ((g⁻¹ * u * g) • v)) = μ (g • v)
    rw [show g • ((g⁻¹ * u * g) • v) = u • (g • v) by
      rw [← mul_smul, ← mul_smul, show g * (g⁻¹ * u * g) = u * g by group]]
    rw [hμu]
  have hzero := modFive_eq_zero_of_mem_stabVec_rep_four (d4pull μ g) hw' hμ'w hu'0 huk hμ'u
  refine AddMonoidHom.ext fun v => ?_
  have hv : d4pull μ g (g⁻¹ • v) = 0 := by rw [hzero]; rfl
  rwa [show d4pull μ g (g⁻¹ • v) = μ v from by simp [d4pull]] at hv

theorem modFive_eq_zero_of_ncard_kerRoots_eq_twentyFour
    {x : X3} (hx : (kerRoots x).ncard = 24)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w u : WeylGroup Tag.E6}
    (hw : w ∈ stabVec x) (hμw : ∀ v, μ (w • v) = 2 * μ v)
    (hu : u ∈ stabVec x) (hu' : u ∉ kerReflVec x) (hμu : ∀ v, μ (u • v) = μ v) :
    μ = 0 := by
  have hx0 : x ≠ 0 := d4_ne_zero_of_ncard hx
  obtain ⟨k, g, hxg⟩ := exists_smul_reps x hx0
  have hk : k = 4 := d4_repKerCard_eq_four (by
    have h1 := ncard_kerRoots_smul g (reps k)
    rw [← hxg, hx, ncard_kerRoots_reps] at h1
    exact h1.symm)
  subst hk
  exact d4_transport hxg μ hw hμw hu hu' hμu

theorem exists_central_of_ncard_kerRoots_eq_twentyFour
    {x : X3} (hx : (kerRoots x).ncard = 24) :
    ∃ f : X3, (∀ α ∈ kerRoots x, pairVec f α = 0) ∧ stabVec x ⊓ stabVec f ≤ kerReflVec x := by
  have hx0 : x ≠ 0 := d4_ne_zero_of_ncard hx
  obtain ⟨k, g, hxg⟩ := exists_smul_reps x hx0
  have hk : k = 4 := d4_repKerCard_eq_four (by
    have h1 := ncard_kerRoots_smul g (reps k)
    rw [← hxg, hx, ncard_kerRoots_reps] at h1
    exact h1.symm)
  subst hk
  refine ⟨g • d4CentralChar, ?_, ?_⟩
  · intro α hα
    rw [pairVec_smul]
    refine pairVec_d4CentralChar_eq_zero ⟨IsRoot.smul hα.1 g⁻¹, ?_⟩
    have h := hα.2
    rw [hxg, pairVec_smul] at h
    exact h
  · have hstab : stabVec (g • reps 4) ⊓ stabVec (g • d4CentralChar) =
        kerReflVec (g • reps 4) := by
      rw [stabVec_smul, stabVec_smul, ← Subgroup.map_inf (stabVec (reps 4))
        (stabVec d4CentralChar) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
        stabVec_inf_stabVec_d4CentralChar, kerReflVec_smul]
    rw [hxg]
    exact le_of_eq hstab

private theorem d4_rootCharKernel_one {L : Type} [Field L] :
    rootCharKernel (1 : Fin Tag.E6.rank → Lˣ) =
      {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} := by
  ext α
  simp [rootCharKernel, rootChar]

private theorem d4_a_ne_one {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (h24 : (rootCharKernel a).ncard = 24) : a ≠ 1 := by
  intro h
  have h1 : (rootCharKernel a).ncard = 72 := by
    rw [h, d4_rootCharKernel_one]
    exact d4_ncard_isRoot
  omega

private theorem d4_prod_zpow_eq {G : Type*} [CommGroup G] (y : G)
    (e : Fin Tag.E6.rank → ℤ) :
    ∏ k, y ^ e k = y ^ ∑ k, e k := by
  have h : ∀ n : ℤ, y ^ n = zpowersHom G y (Multiplicative.ofAdd n) := fun _ => rfl
  simp only [h, ofAdd_sum, map_prod]

private theorem d4_rootChar_z_iff {L : Type} [Field L] {a : Fin Tag.E6.rank → Lˣ}
    (ha3 : ∀ i, a i ^ 3 = 1) (i₀ : Fin Tag.E6.rank) (hi₀ : a i₀ ≠ 1) (f : X3) :
    ∀ v : Fin Tag.E6.rank → ℤ,
      rootChar (fun i => (a i₀) ^ (f i).val) v = 1 ↔ pairVec f v = 0 := by
  have hζo : orderOf (a i₀) = 3 := orderOf_eq_prime (ha3 i₀) hi₀
  have hNcast : ∀ v, ((∑ j, ((f j).val : ℤ) * v j : ℤ) : ZMod 3) = pairVec f v := fun v => by
    rw [pairVec]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [ZMod.natCast_zmod_val]
  have hprod : ∀ v, rootChar (fun i => (a i₀) ^ (f i).val) v =
      (a i₀) ^ (∑ j, ((f j).val : ℤ) * v j) := by
    intro v
    simp only [rootChar]
    rw [show (∏ j, ((a i₀) ^ (f j).val : Lˣ) ^ v j) =
        ∏ j, (a i₀) ^ (((f j).val : ℤ) * v j) from
      Finset.prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul]]
    exact d4_prod_zpow_eq (a i₀) fun j => ((f j).val : ℤ) * v j
  intro v
  rw [hprod v, ← hNcast v, ← orderOf_dvd_iff_zpow_eq_one, hζo]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm

theorem modFive_eq_zero_of_ncard_rootCharKernel_eq_twentyFour
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (h24 : (rootCharKernel a).ncard = 24)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w u : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) (hμw : ∀ v, μ (w • v) = 2 * μ v)
    (hu : u ∈ rootCharStabilizerSubgroup a) (hu' : u ∉ kernelReflectionGroup a)
    (hμu : ∀ v, μ (u • v) = μ v) : μ = 0 := by
  obtain ⟨x, -, hxchar⟩ := exists_vec_of_cube_roots a ha3 (d4_a_ne_one a ha3 h24)
  have hx24 : (kerRoots x).ncard = 24 := by
    rw [← rootCharKernel_eq_kerRoots hxchar]
    exact h24
  have hw' : w ∈ stabVec x := by
    rwa [rootCharStabilizerSubgroup_eq_stabVec hxchar] at hw
  have hu'0 : u ∈ stabVec x := by
    rwa [rootCharStabilizerSubgroup_eq_stabVec hxchar] at hu
  have huk : u ∉ kerReflVec x := by
    rwa [kernelReflectionGroup_eq_kerReflVec hxchar] at hu'
  exact modFive_eq_zero_of_ncard_kerRoots_eq_twentyFour hx24 μ hw' hμw hu'0 huk hμu

theorem exists_central_of_ncard_rootCharKernel_eq_twentyFour
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (h24 : (rootCharKernel a).ncard = 24) :
    ∃ z : Fin Tag.E6.rank → Lˣ, (∀ α ∈ rootCharKernel a, rootChar z α = 1) ∧
      rootCharStabilizerSubgroup a ⊓ rootCharStabilizerSubgroup z ≤ kernelReflectionGroup a := by
  have ha1 : a ≠ 1 := d4_a_ne_one a ha3 h24
  obtain ⟨x, -, hxchar⟩ := exists_vec_of_cube_roots a ha3 ha1
  have hx24 : (kerRoots x).ncard = 24 := by
    rw [← rootCharKernel_eq_kerRoots hxchar]
    exact h24
  obtain ⟨f, hf, hle⟩ := exists_central_of_ncard_kerRoots_eq_twentyFour hx24
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    exact ha1 (funext fun i => not_not.mp (h i))
  have hz := d4_rootChar_z_iff ha3 i₀ hi₀ f
  refine ⟨fun i => (a i₀) ^ (f i).val, ?_, ?_⟩
  · intro α hα
    have hαx : α ∈ kerRoots x := by
      rwa [rootCharKernel_eq_kerRoots hxchar] at hα
    exact (hz α).2 (hf α hαx)
  · rw [rootCharStabilizerSubgroup_eq_stabVec hz,
      rootCharStabilizerSubgroup_eq_stabVec hxchar, kernelReflectionGroup_eq_kerReflVec hxchar]
    exact hle

end CFSG.StandardType.NTPlane

end
