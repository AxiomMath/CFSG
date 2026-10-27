module

import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.Timmesfeld.Transvection.PresSUModel
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import CFSG.LieType.Universal.Unitary.Extras.Commutator

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement CharTwo

variable {m : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (hm : ¬Even m)

theorem crd_ne_midIdx (a : Fin (m / 2) ⊕ Fin (m / 2)) : crd a ≠ midIdx m hm := by
  rcases a with a | a
  · intro h
    have := congrArg Fin.val h
    simp only [crd_inl, val_lowIdx, midIdx] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [crd_inr, Fin.val_rev, val_lowIdx, midIdx] at this
    rw [Nat.not_even_iff_odd] at hm
    obtain ⟨r, hr⟩ := hm
    omega

theorem eq_midIdx_of_rev_eq {k : Fin m} (hk : Fin.rev k = k) : k = midIdx m hm := by
  have h := congrArg Fin.val hk
  simp only [Fin.val_rev, midIdx] at h ⊢
  rw [Nat.not_even_iff_odd] at hm
  obtain ⟨r, hr⟩ := hm
  apply Fin.ext
  change k.val = m / 2
  omega

variable (σ) in
open Classical in
noncomputable def suHeis (hσ : ∀ c, σ (σ c) = c) (hm : ¬Even m)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) : SU σ m :=
  if h : v + σ v + σ u * u = 0 then
    heisRootElt hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) u v h
  else 1

theorem mat_suHeis {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : v + σ v + σ u * u = 0) :
    mat σ m (suHeis σ hσ hm a u v) =
      heisenbergMatrix σ (crd a) (midIdx m hm) u v := by
  rw [suHeis, dite_eq_left h, mat_apply]
  rfl

theorem suHeis_of_not {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : ¬ v + σ v + σ u * u = 0) : suHeis σ hσ hm a u v = 1 := by
  rw [suHeis, dif_neg h]

private theorem suHeis_zero_zero (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    suHeis σ hσ hm a 0 0 = 1 := by
  have h0 : (0 : F) + σ 0 + σ (0 : F) * 0 = 0 := by simp
  apply mat_injective
  rw [mat_suHeis hσ hm h0, heisenbergMatrix_zero, map_one]

theorem heis_add_valid (hσ : ∀ c, σ (σ c) = c) {u v u' v' : F}
    (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    (v + v' - u * σ u') + σ (v + v' - u * σ u') + σ (u + u') * (u + u') = 0 := by
  rw [map_sub, map_add, map_add, map_mul, hσ]
  calc v + v' - u * σ u' + (σ v + σ v' - σ u * u') + (σ u + σ u') * (u + u')
      = (v + σ v + σ u * u) + (v' + σ v' + σ u' * u') := by ring
    _ = 0 := by rw [h, h', add_zero]

theorem heis_neg_valid (hσ : ∀ c, σ (σ c) = c) {u v : F} (h : v + σ v + σ u * u = 0) :
    (-v - u * σ u) + σ (-v - u * σ u) + σ (-u) * (-u) = 0 := by
  rw [map_sub, map_neg, map_neg, map_mul, hσ]
  calc -v - u * σ u + (-σ v - σ u * u) + (-σ u) * (-u)
      = -(v + σ v + σ u * u) := by ring
    _ = 0 := by rw [h, neg_zero]

theorem heis_zero_left_valid [CharP F 2] {c : F} (hc : σ c = c) :
    c + σ c + σ 0 * 0 = 0 := by
  rw [map_zero, zero_mul, add_zero, hc]
  exact CharTwo.add_self_eq_zero c

theorem heis_smul_valid (hσ : ∀ c, σ (σ c) = c) {u v κ s : F}
    (h : v + σ v + σ u * u = 0) (hκ : σ κ * κ = σ s * s) :
    σ s * s * v + σ (σ s * s * v) + σ (κ * u) * (κ * u) = 0 := by
  simp only [map_mul, hσ] at h ⊢
  linear_combination (σ s * s) * h + (σ u * u) * hκ

theorem suHeis_mul {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v u' v' : F}
    (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    suHeis σ hσ hm a u v * suHeis σ hσ hm a u' v' =
      suHeis σ hσ hm a (u + u') (v + v' - u * σ u') := by
  have h'' := heis_add_valid hσ h h'
  apply mat_injective
  rw [map_mul, mat_suHeis hσ hm h, mat_suHeis hσ hm h', mat_suHeis hσ hm h'',
    heisenbergMatrix_mul σ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm)]

theorem suHeis_inv {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : v + σ v + σ u * u = 0) :
    (suHeis σ hσ hm a u v)⁻¹ = suHeis σ hσ hm a (-u) (-v - u * σ u) := by
  have h' := heis_neg_valid hσ h
  refine inv_eq_of_mul_eq_one_right ?_
  rw [suHeis_mul hσ hm h h', show u + -u = 0 by ring,
    show v + (-v - u * σ u) - u * σ (-u) = 0 by rw [map_neg]; ring,
    suHeis_zero_zero hσ hm]

theorem suHeis_zero_left (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    suHeis σ hσ hm a 0 c = suLong σ a c := by
  by_cases h : c + σ c = 0
  · have h' : c + σ c + σ (0 : F) * 0 = 0 := by simpa using h
    apply mat_injective
    rw [mat_suHeis hσ hm h', mat_suLong a h, crd_swap a]
    simp [heisenbergMatrix]
  · have h' : ¬(c + σ c + σ (0 : F) * 0 = 0) := by simpa using h
    rw [suHeis, dite_eq_right h', suLong, dite_eq_right h]

theorem mat_suHeis_apply_mid {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : v + σ v + σ u * u = 0) :
    mat σ m (suHeis σ hσ hm a u v) (crd a) (midIdx m hm) = u := by
  rw [mat_suHeis hσ hm h,
    heisenbergMatrix_apply_ik (crd_ne_midIdx hm a) (rev_midIdx hm) u v]

theorem mat_suHeis_apply_swap {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v : F}
    (h : v + σ v + σ u * u = 0) :
    mat σ m (suHeis σ hσ hm a u v) (crd a) (crd (Sum.swap a)) = v := by
  have h1 : crd a ≠ midIdx m hm := crd_ne_midIdx hm a
  have h2 : Fin.rev (crd a) ≠ midIdx m hm := by
    rw [← crd_swap a]
    exact crd_ne_midIdx hm (Sum.swap a)
  rw [mat_suHeis hσ hm h, crd_swap, heisenbergMatrix]
  simp [single_apply, crd_ne_rev a, h1, h2, Ne.symm h1, Ne.symm h2]


private theorem dot_weight_self {i : Fin m} (hi : i ≠ Fin.rev i) :
    weight m i ⬝ᵥ weight m i = 1 := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · rw [weight_lowIdx]
    simp [single_dotProduct]
  · rw [weight_rev_lowIdx]
    simp [single_dotProduct]

private theorem dot_rt_self {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    rt a b ⬝ᵥ rt a b = 2 := by
  rw [rt_dot_rt, wt_dot_of_idx_ne hab]
  ring

private theorem dot_rt_self_self (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    rt a a ⬝ᵥ rt a a = 4 := by
  rw [rt, ← two_nsmul, smul_dotProduct, dotProduct_smul, Sp.dot_wt_self]
  norm_num

private theorem mem_heisenbergSubgroup_iff {a : Fin (m / 2) ⊕ Fin (m / 2)} (g : SU σ m) :
    g ∈ heisenbergSubgroup σ hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) ↔
      ∃ u v, v + σ v + σ u * u = 0 ∧ suHeis σ hσ hm a u v = g := by
  constructor
  · rintro ⟨u, v, hab, hg⟩
    refine ⟨u, v, hab, ?_⟩
    apply mat_injective
    rw [mat_suHeis hσ hm hab, mat_apply]
    exact hg.symm
  · rintro ⟨u, v, hab, rfl⟩
    rw [suHeis, dite_eq_left hab]
    exact heisRootElt_mem hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) u v hab

private theorem rootGroup_le_heisenberg_of_toStd_eq_wt {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = wt a) :
    rootGroup σ hσ m γ ≤
      heisenbergSubgroup σ hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun _ => iSup_le fun hi =>
      iSup_le fun hj => iSup_le fun _ => iSup_le fun hw => ?_
    have hw' : weight m i - weight m j = weight m (crd a) := by rw [hw, hγ, weight_crd]
    rcases eq_of_weight_sub_eq_weight (crd_ne_rev a) (rev_midIdx hm) hw' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (rev_midIdx hm).symm hj
    · exact absurd (rev_midIdx hm) (Ne.symm hi)
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    have h1 := congrArg (fun v => v ⬝ᵥ v) (by rw [hw, hγ] : 2 • weight m i = wt a)
    simp only [smul_dotProduct, dotProduct_smul, dot_weight_self hi, Sp.dot_wt_self] at h1
    norm_num at h1
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun _ => iSup_le fun _ => iSup_le fun hk =>
      iSup_le fun hw => ?_
    have hwi : weight m i = weight m (crd a) := by rw [hw, hγ, weight_crd]
    obtain rfl := weight_injective hwi
    obtain rfl := eq_midIdx_of_rev_eq hm hk
    exact le_rfl

private theorem heisenbergSubgroup_le_rootGroup {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = wt a) :
    heisenbergSubgroup σ hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) ≤
      rootGroup σ hσ m γ :=
  heisenberg_le hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) (by
    rw [weight_crd]
    exact hγ.symm)

theorem suHeis_mem {a : Fin (m / 2) ⊕ Fin (m / 2)} {γ : Fin (m / 2) → ℤ}
    (hγ : toStd m γ = wt a) (u v : F) :
    suHeis σ hσ hm a u v ∈ rootGroup σ hσ m γ := by
  refine heisenbergSubgroup_le_rootGroup hσ hm hγ ?_
  by_cases h : v + σ v + σ u * u = 0
  · rw [suHeis, dite_eq_left h]
    exact heisRootElt_mem hσ (crd_ne_rev a) (crd_ne_midIdx hm a) (rev_midIdx hm) u v h
  · rw [suHeis, dite_eq_right h]
    exact one_mem _

theorem mem_rootGroup_iff_suHeis {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = wt a) (g : SU σ m) :
    g ∈ rootGroup σ hσ m γ ↔ ∃ u v, v + σ v + σ u * u = 0 ∧ suHeis σ hσ hm a u v = g := by
  constructor
  · intro hg
    exact (mem_heisenbergSubgroup_iff hσ hm g).mp
      (rootGroup_le_heisenberg_of_toStd_eq_wt hσ hm hγ hg)
  · rintro ⟨u, v, _, rfl⟩
    exact suHeis_mem hσ hm hγ u v

private theorem rootGroup_le_rootHom_of_toStd_eq_rt {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) :
    rootGroup σ hσ m γ ≤ (rootHom σ hσ (crd_ne_crd_swap hab) (crd_ne_rev a)
      (crd_ne_rev (Sum.swap b))).range := by
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hji => iSup_le fun hw => ?_
    have hw' : weight m i - weight m j = weight m (crd a) - weight m (crd (Sum.swap b)) := by
      rw [hw, hγ, rt, weight_crd, weight_crd, Sp.wt_swap, sub_neg_eq_add]
    have hba : b ≠ a := ne_of_idx_ne hab
    have hji' : crd (Sum.swap b) ≠ Fin.rev (crd a) := by
      rw [← crd_swap a]
      intro e
      exact hba (by simpa using congrArg Sum.swap (crd_injective e))
    rcases eq_of_weight_sub_eq_sub (i := crd a) (j := crd (Sum.swap b))
      (crd_ne_crd_swap hab) (crd_ne_rev a) (crd_ne_rev (Sum.swap b)) hji' hw' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · rintro _ ⟨c, rfl⟩
      refine ⟨Multiplicative.ofAdd (-σ (Multiplicative.toAdd c)), ?_⟩
      apply mat_injective
      rw [mat_apply, mat_apply, coe_rootHom, coe_rootHom, toAdd_ofAdd]
      simp only [rootMatrix, Fin.rev_rev, map_neg, hσ]
      rw [← single_neg, ← single_neg]
      abel
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    have h1 := congrArg (fun v => v ⬝ᵥ v) (by rw [hw, hγ] : 2 • weight m i = rt a b)
    simp only [smul_dotProduct, dotProduct_smul, dot_weight_self hi, dot_rt_self hab] at h1
    norm_num at h1
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hw => ?_
    have h1 := congrArg (fun v => v ⬝ᵥ v) (by rw [hw, hγ] : weight m i = rt a b)
    rw [dot_weight_self hi, dot_rt_self hab] at h1
    norm_num at h1

private theorem mem_rootHom_range_iff_suElt {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) (g : SU σ m) :
    g ∈ (rootHom σ hσ (crd_ne_crd_swap hab) (crd_ne_rev a)
      (crd_ne_rev (Sum.swap b))).range ↔ ∃ c, suElt σ hσ a b c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c,
      by rw [suElt, dite_eq_left hab, ofAdd_toAdd]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, by rw [suElt, dite_eq_left hab]⟩

theorem mem_rootGroup_iff_suElt_odd {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (g : SU σ m) :
    g ∈ rootGroup σ hσ m γ ↔ ∃ c, suElt σ hσ a b c = g := by
  have hiff := mem_rootHom_range_iff_suElt hσ hab g
  constructor
  · intro hg
    exact hiff.mp (rootGroup_le_rootHom_of_toStd_eq_rt hσ hab hγ hg)
  · rintro ⟨c, hc⟩
    exact hc ▸ suElt_mem hσ hab hγ c

private theorem rootGroup_le_longRootHom_of_toStd_eq_rt_self {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) :
    rootGroup σ hσ m γ ≤ (longRootHom σ (crd_ne_rev a)).range := by
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hji => iSup_le fun hw => ?_
    have hw' : weight m i - weight m j = 2 • weight m (crd a) := by
      rw [hw, hγ, rt, two_nsmul, weight_crd]
    have hne : weight m (crd a) ≠ 0 := by
      intro h0
      have h1 := dot_weight_self (crd_ne_rev a)
      rw [h0, zero_dotProduct] at h1
      norm_num at h1
    obtain ⟨hb, -⟩ := eq_rev_of_weight_sub_eq_two_smul hw' hne
    exact absurd hb hji
  · refine iSup_le fun i => iSup_le fun _ => iSup_le fun hw => ?_
    have hw' : 2 • weight m i = 2 • weight m (crd a) := by
      rw [hw, hγ, rt, two_nsmul, weight_crd]
    have hwi : weight m i = weight m (crd a) := by
      funext c
      have := congrFun hw' c
      simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    obtain rfl := weight_injective hwi
    exact le_rfl
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hw => ?_
    have h1 := congrArg (fun v => v ⬝ᵥ v) (by rw [hw, hγ] : weight m i = rt a a)
    rw [dot_weight_self hi, dot_rt_self_self] at h1
    norm_num at h1

private theorem mem_longRootHom_range_iff_suLong {a : Fin (m / 2) ⊕ Fin (m / 2)}
    (g : SU σ m) :
    g ∈ (longRootHom σ (crd_ne_rev a)).range ↔
      ∃ c, c + σ c = 0 ∧ suLong σ a c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ((Multiplicative.toAdd c : traceZero σ) : F) +
        σ ((Multiplicative.toAdd c : traceZero σ) : F) = 0 := (Multiplicative.toAdd c).2
    refine ⟨((Multiplicative.toAdd c : traceZero σ) : F), hc, ?_⟩
    rw [suLong, dite_eq_left hc]
    rfl
  · rintro ⟨c, hc, rfl⟩
    rw [suLong, dite_eq_left hc]
    exact ⟨Multiplicative.ofAdd ⟨c, hc⟩, rfl⟩

theorem mem_rootGroup_iff_suLong_odd (a : Fin (m / 2) ⊕ Fin (m / 2))
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) (g : SU σ m) :
    g ∈ rootGroup σ hσ m γ ↔ ∃ c, c + σ c = 0 ∧ suLong σ a c = g := by
  have hiff := mem_longRootHom_range_iff_suLong (a := a) g
  constructor
  · intro hg
    exact hiff.mp (rootGroup_le_longRootHom_of_toStd_eq_rt_self hσ hγ hg)
  · rintro ⟨c, _, rfl⟩
    exact suLong_mem hσ a hγ c

private theorem weight_crd_sub_mid (c : Fin (m / 2) ⊕ Fin (m / 2)) :
    weight m (crd c) - weight m (midIdx m hm) = wt c := by
  rw [weight_crd, weight_eq_zero_of_rev_eq (rev_midIdx hm), sub_zero]

private theorem weight_crd_sub_crd_swap (c : Fin (m / 2) ⊕ Fin (m / 2)) :
    weight m (crd c) - weight m (crd (Sum.swap c)) = 2 • wt c := by
  rw [weight_crd, weight_crd, Sp.wt_swap, sub_neg_eq_add, ← two_nsmul]

private theorem wt_ne_rt {c a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    wt c ≠ rt a b := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [Sp.dot_wt_self, dot_rt_self hab] at h1
  norm_num at h1

private theorem wt_ne_two_rt {c a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    wt c ≠ 2 • rt a b := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [Sp.dot_wt_self, smul_dotProduct, dotProduct_smul, dot_rt_self hab] at h1
  norm_num at h1

private theorem two_wt_ne_rt {c a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    2 • wt c ≠ rt a b := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [smul_dotProduct, dotProduct_smul, Sp.dot_wt_self, dot_rt_self hab] at h1
  norm_num at h1

private theorem two_wt_ne_two_rt {c a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) :
    2 • wt c ≠ 2 • rt a b := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [smul_dotProduct, dotProduct_smul, Sp.dot_wt_self, smul_dotProduct, dotProduct_smul,
    dot_rt_self hab] at h1
  norm_num at h1

private theorem wt_ne_rt_self (c a : Fin (m / 2) ⊕ Fin (m / 2)) :
    wt c ≠ rt a a := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [Sp.dot_wt_self, dot_rt_self_self] at h1
  norm_num at h1

private theorem wt_ne_two_rt_self (c a : Fin (m / 2) ⊕ Fin (m / 2)) :
    wt c ≠ 2 • rt a a := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [Sp.dot_wt_self, smul_dotProduct, dotProduct_smul, dot_rt_self_self] at h1
  norm_num at h1

private theorem two_wt_ne_rt_self {c a : Fin (m / 2) ⊕ Fin (m / 2)} (hca : c ≠ a) :
    2 • wt c ≠ rt a a := by
  intro h
  rw [rt, ← two_nsmul] at h
  have h1 : wt c = wt a := by
    funext s
    have := congrFun h s
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
    omega
  exact hca (Sp.wt_injective h1)

private theorem two_wt_ne_two_rt_self (c a : Fin (m / 2) ⊕ Fin (m / 2)) :
    2 • wt c ≠ 2 • rt a a := by
  intro h
  have h1 := congrArg (fun v => v ⬝ᵥ v) h
  rw [smul_dotProduct, dotProduct_smul, Sp.dot_wt_self, smul_dotProduct, dotProduct_smul,
    dot_rt_self_self] at h1
  norm_num at h1

private theorem mat_apply_eq_zero_of_mem_rootGroup {γ : Fin (m / 2) → ℤ} {x : SU σ m}
    (hx : x ∈ rootGroup σ hσ m γ) {p q : Fin m} (hpq : p ≠ q)
    (h1 : weight m p - weight m q ≠ toStd m γ)
    (h2 : weight m p - weight m q ≠ 2 • toStd m γ) :
    mat σ m x p q = 0 := by
  rw [mat_apply_of_mem_rootGroup hσ hx h1 h2]
  exact one_apply_ne hpq

private theorem mat_suElt_apply_mid {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (t : F)
    (c : Fin (m / 2) ⊕ Fin (m / 2)) :
    mat σ m (suElt σ hσ a b t) (crd c) (midIdx m hm) = 0 := by
  refine mat_apply_eq_zero_of_mem_rootGroup hσ (suElt_mem hσ hab hγ t)
    (crd_ne_midIdx hm c) ?_ ?_
  · rw [weight_crd_sub_mid, hγ]
    exact wt_ne_rt hab
  · rw [weight_crd_sub_mid, hγ]
    exact wt_ne_two_rt hab

private theorem mat_suElt_apply_swap_self {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (t : F)
    (c : Fin (m / 2) ⊕ Fin (m / 2)) :
    mat σ m (suElt σ hσ a b t) (crd c) (crd (Sum.swap c)) = 0 := by
  refine mat_apply_eq_zero_of_mem_rootGroup hσ (suElt_mem hσ hab hγ t)
    (by rw [crd_swap c]; exact crd_ne_rev c) ?_ ?_
  · rw [weight_crd_sub_crd_swap, hγ]
    exact two_wt_ne_rt hab
  · rw [weight_crd_sub_crd_swap, hγ]
    exact two_wt_ne_two_rt hab

private theorem mat_suLong_apply_mid (hσ : ∀ c, σ (σ c) = c)
    {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) {t : F}
    (c : Fin (m / 2) ⊕ Fin (m / 2)) :
    mat σ m (suLong σ a t) (crd c) (midIdx m hm) = 0 := by
  refine mat_apply_eq_zero_of_mem_rootGroup hσ (suLong_mem hσ a hγ t)
    (crd_ne_midIdx hm c) ?_ ?_
  · rw [weight_crd_sub_mid, hγ]
    exact wt_ne_rt_self c a
  · rw [weight_crd_sub_mid, hγ]
    exact wt_ne_two_rt_self c a

private theorem mat_suLong_apply_swap_self (hσ : ∀ c, σ (σ c) = c)
    {a : Fin (m / 2) ⊕ Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) {t : F}
    (c : Fin (m / 2) ⊕ Fin (m / 2)) (hca : c ≠ a) :
    mat σ m (suLong σ a t) (crd c) (crd (Sum.swap c)) = 0 := by
  refine mat_apply_eq_zero_of_mem_rootGroup hσ (suLong_mem hσ a hγ t)
    (by rw [crd_swap c]; exact crd_ne_rev c) ?_ ?_
  · rw [weight_crd_sub_crd_swap, hγ]
    exact two_wt_ne_rt_self hca
  · rw [weight_crd_sub_crd_swap, hγ]
    exact two_wt_ne_two_rt_self c a

theorem rootGroup_inf_heis_eq_bot (hm : ¬Even m)
    {a b c : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {γ δ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (hδ : toStd m δ = wt c) :
    rootGroup σ hσ m γ ⊓ rootGroup σ hσ m δ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxγ, hxδ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨u, v, hP, rfl⟩ := (mem_rootGroup_iff_suHeis hσ hm hδ x).mp hxδ
  obtain ⟨t, ht⟩ := (mem_rootGroup_iff_suElt_odd hσ hab hγ
    (suHeis σ hσ hm c u v)).mp hxγ
  have hu : u = 0 := by
    have h1 := mat_suHeis_apply_mid (a := c) hσ hm hP
    rw [← ht, mat_suElt_apply_mid hσ hm hab hγ t c] at h1
    exact h1.symm
  have hv : v = 0 := by
    have h1 := mat_suHeis_apply_swap (a := c) hσ hm hP
    rw [← ht, mat_suElt_apply_swap_self hσ hab hγ t c] at h1
    exact h1.symm
  rw [hu, hv, suHeis_zero_zero hσ hm]

theorem rootGroup_long_inf_heis_eq_bot (hm : ¬Even m)
    {a c : Fin (m / 2) ⊕ Fin (m / 2)} (hca : c ≠ a)
    {γ δ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) (hδ : toStd m δ = wt c) :
    rootGroup σ hσ m γ ⊓ rootGroup σ hσ m δ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxγ, hxδ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨u, v, hP, rfl⟩ := (mem_rootGroup_iff_suHeis hσ hm hδ x).mp hxδ
  obtain ⟨t, ht, hst⟩ := (mem_rootGroup_iff_suLong_odd hσ a hγ
    (suHeis σ hσ hm c u v)).mp hxγ
  have hu : u = 0 := by
    have h1 := mat_suHeis_apply_mid (a := c) hσ hm hP
    rw [← hst, mat_suLong_apply_mid hm hσ hγ c] at h1
    exact h1.symm
  have hv : v = 0 := by
    have h1 := mat_suHeis_apply_swap (a := c) hσ hm hP
    rw [← hst, mat_suLong_apply_swap_self hσ hγ c hca] at h1
    exact h1.symm
  rw [hu, hv, suHeis_zero_zero hσ hm]

theorem suHeis_comm_suElt {a b c : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    (hca : c ≠ Sum.swap a) (hcb : c ≠ Sum.swap b) (u v t : F) :
    ⁅suHeis σ hσ hm c u v, suElt σ hσ a b t⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  by_cases h : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [map_mul, map_mul, mat_suHeis hσ hm h, mat_suElt hσ hab t]
    set A : Matrix (Fin m) (Fin m) F :=
      single (crd a) (crd (Sum.swap b)) t - single (crd b) (crd (Sum.swap a)) (σ t)
      with hA
    set B : Matrix (Fin m) (Fin m) F :=
      single (crd c) (midIdx m hm) u -
        single (midIdx m hm) (Fin.rev (crd c)) (σ u) +
          single (crd c) (Fin.rev (crd c)) v with hB
    have hH : heisenbergMatrix σ (crd c) (midIdx m hm) u v = 1 + B := by
      rw [heisenbergMatrix, hB]
      abel
    have hE : 1 + single (crd a) (crd (Sum.swap b)) t -
        single (crd b) (crd (Sum.swap a)) (σ t) = 1 + A := by
      rw [hA]
      abel
    rw [hH, hE]
    have hab' : a ≠ b := (ne_of_idx_ne hab).symm
    have hca' : Sum.swap c ≠ a := fun e => hca (by simpa using congrArg Sum.swap e)
    have hca'' : a ≠ Sum.swap c := hca'.symm
    have hcb' : Sum.swap c ≠ b := fun e => hcb (by simpa using congrArg Sum.swap e)
    have hcb'' : b ≠ Sum.swap c := hcb'.symm
    have hAB : A * B = 0 := by
      rw [hA, hB]
      simp only [sub_mul, mul_add, mul_sub, add_mul, single_mul_single', crd_injective.eq_iff,
        ← crd_swap, Fin.rev_inj]
      simp_all [hca, hca.symm, hcb, hcb.symm, hca', hca'', hcb', hcb'', hab', crd_ne_midIdx hm c,
        crd_ne_midIdx hm a, crd_ne_midIdx hm b, crd_ne_midIdx hm (Sum.swap a),
        crd_ne_midIdx hm (Sum.swap b), (crd_ne_midIdx hm a).symm,
        (crd_ne_midIdx hm b).symm, (crd_ne_midIdx hm (Sum.swap a)).symm,
        (crd_ne_midIdx hm (Sum.swap b)).symm]
    have hBA : B * A = 0 := by
      rw [hA, hB]
      simp only [sub_mul, mul_add, mul_sub, add_mul, single_mul_single', crd_injective.eq_iff,
        ← crd_swap, Fin.rev_inj]
      simp_all [hca, hca.symm, hcb, hcb.symm, hca', hca'', hcb', hcb'', hab', crd_ne_midIdx hm c,
        crd_ne_midIdx hm a, crd_ne_midIdx hm b, crd_ne_midIdx hm (Sum.swap a),
        crd_ne_midIdx hm (Sum.swap b), (crd_ne_midIdx hm a).symm,
        (crd_ne_midIdx hm b).symm, (crd_ne_midIdx hm (Sum.swap a)).symm,
        (crd_ne_midIdx hm (Sum.swap b)).symm]
    have hL : (1 + B) * (1 + A) = 1 + A + B := by
      rw [show (1 + B) * (1 + A) = 1 + B + A + B * A by noncomm_ring, hBA, add_zero]
      abel
    have hR : (1 + A) * (1 + B) = 1 + A + B := by
      rw [show (1 + A) * (1 + B) = 1 + A + B + A * B by noncomm_ring, hAB, add_zero]
    rw [hL, hR]
  · rw [suHeis, dite_eq_right h]
    simp

theorem suHeis_comm_suLong {a c : Fin (m / 2) ⊕ Fin (m / 2)} (hca : c ≠ Sum.swap a)
    (u v t : F) : ⁅suHeis σ hσ hm c u v, suLong σ a t⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  by_cases h : v + σ v + σ u * u = 0
  · by_cases ht : t + σ t = 0
    · apply mat_injective
      rw [map_mul, map_mul, mat_suHeis hσ hm h, mat_suLong a ht]
      set A : Matrix (Fin m) (Fin m) F := single (crd a) (crd (Sum.swap a)) t with hA
      set B : Matrix (Fin m) (Fin m) F :=
        single (crd c) (midIdx m hm) u -
          single (midIdx m hm) (Fin.rev (crd c)) (σ u) +
            single (crd c) (Fin.rev (crd c)) v with hB
      have hH : heisenbergMatrix σ (crd c) (midIdx m hm) u v = 1 + B := by
        rw [heisenbergMatrix, hB]
        abel
      have hE : 1 + single (crd a) (crd (Sum.swap a)) t = 1 + A := by
        rw [hA]
      rw [hH, hE]
      have hca' : Sum.swap c ≠ a := fun e => hca (by simpa using congrArg Sum.swap e)
      have hca'' : a ≠ Sum.swap c := hca'.symm
      have hAB : A * B = 0 := by
        rw [hA, hB]
        simp only [sub_mul, mul_add, mul_sub, add_mul, single_mul_single', crd_injective.eq_iff,
          ← crd_swap, Fin.rev_inj]
        simp_all [hca, hca.symm, hca', hca'', crd_ne_midIdx hm c, crd_ne_midIdx hm a,
          crd_ne_midIdx hm (Sum.swap a), (crd_ne_midIdx hm a).symm,
          (crd_ne_midIdx hm (Sum.swap a)).symm]
      have hBA : B * A = 0 := by
        rw [hA, hB]
        simp only [sub_mul, mul_add, mul_sub, add_mul, single_mul_single', crd_injective.eq_iff,
          ← crd_swap, Fin.rev_inj]
        simp_all [hca, hca.symm, hca', hca'', crd_ne_midIdx hm c, crd_ne_midIdx hm a,
          crd_ne_midIdx hm (Sum.swap a), (crd_ne_midIdx hm a).symm,
          (crd_ne_midIdx hm (Sum.swap a)).symm]
      have hL : (1 + B) * (1 + A) = 1 + A + B := by
        rw [show (1 + B) * (1 + A) = 1 + B + A + B * A by noncomm_ring, hBA, add_zero]
        abel
      have hR : (1 + A) * (1 + B) = 1 + A + B := by
        rw [show (1 + A) * (1 + B) = 1 + A + B + A * B by noncomm_ring, hAB, add_zero]
      rw [hL, hR]
    · rw [suLong, dite_eq_right ht]
      simp
  · rw [suHeis, dite_eq_right h]
    simp

theorem suHeis_comm_self [CharP F 2] {a : Fin (m / 2) ⊕ Fin (m / 2)} {u v u' v' : F}
    (h : v + σ v + σ u * u = 0) (h' : v' + σ v' + σ u' * u' = 0) :
    ⁅suHeis σ hσ hm a u v, suHeis σ hσ hm a u' v'⁆ =
      suLong σ a (u * σ u' + u' * σ u) := by
  have h1 := heis_add_valid hσ h h'
  have h2 := heis_neg_valid hσ h
  have h3 := heis_neg_valid hσ h'
  have h4 := heis_add_valid hσ h1 h2
  have h5 := heis_add_valid hσ h4 h3
  rw [commutatorElement_def, suHeis_inv hσ hm h, suHeis_inv hσ hm h',
    suHeis_mul hσ hm h h', suHeis_mul hσ hm h1 h2, suHeis_mul hσ hm h4 h3,
    show (u + u') + -u + -u' = 0 by
      simp only [CharTwo.neg_eq]
      calc u + u' + u + u' = (u + u) + (u' + u') := by ring
        _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero],
    suHeis_zero_left]
  exact congrArg (suLong σ a) (by
    simp only [map_neg, CharTwo.neg_eq, CharTwo.sub_eq_add]
    ring_nf
    simp [CharTwo.two_eq_zero, CharTwo.ofNat_eq_mod, Nat.reduceMod])

private theorem diagonal_ne_zero {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (s : Fin m) : d s ≠ 0 := by
  intro h
  have := hd s
  rw [h, map_zero, zero_mul] at this
  exact zero_ne_one this

private theorem diagonal_mul_diagonal_inv {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    diagonal d * diagonal (fun s => (d s)⁻¹) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
  funext s
  exact mul_inv_cancel₀ (diagonal_ne_zero hd s)

private theorem mat_inv_of_diagonal
    {g : SU σ m} {d : Fin m → F}
    (hg : mat σ m g = diagonal d) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) :
    mat σ m g⁻¹ = diagonal (fun s => (d s)⁻¹) := by
  have h1 : diagonal d * mat σ m g⁻¹ = 1 := by
    calc diagonal d * mat σ m g⁻¹ = mat σ m g * mat σ m g⁻¹ := by rw [hg]
      _ = mat σ m (g * g⁻¹) := (map_mul (mat σ m) g g⁻¹).symm
      _ = mat σ m 1 := congrArg (mat σ m) (mul_inv_cancel g)
      _ = 1 := map_one _
  ext i j
  have hij := congrFun (congrFun h1 i) j
  rw [Matrix.diagonal_mul, Matrix.one_apply] at hij
  by_cases h : i = j
  · subst h
    rw [if_pos rfl] at hij
    rw [Matrix.diagonal_apply_eq]
    exact eq_inv_of_mul_eq_one_right hij
  · rw [if_neg h] at hij
    have hzero : (mat σ m g⁻¹) i j = 0 :=
      (mul_eq_zero.mp hij).resolve_left (diagonal_ne_zero hd i)
    rw [hzero, Matrix.diagonal_apply_ne (fun s => (d s)⁻¹) h]

private theorem sigma_diagonal_conj_coeff {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (p q : Fin m) (c : F) :
    σ (d p * c * (d q)⁻¹) = d (Fin.rev q) * σ c * (d (Fin.rev p))⁻¹ := by
  have hp : σ (d p) = (d (Fin.rev p))⁻¹ := eq_inv_of_mul_eq_one_left (hd p)
  have hq : (σ (d q))⁻¹ = d (Fin.rev q) := inv_eq_of_mul_eq_one_right (hd q)
  rw [map_mul, map_mul, map_inv₀, hp, hq]
  ring

private theorem conj_add_sigma {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (a : Fin (m / 2) ⊕ Fin (m / 2)) (v : F) :
    d (crd a) * v * (d (crd (Sum.swap a)))⁻¹ +
      σ (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹) =
      d (crd a) * (d (crd (Sum.swap a)))⁻¹ * (v + σ v) := by
  have hA : σ (d (crd a)) = (d (crd (Sum.swap a)))⁻¹ := by
    have h := hd (crd a)
    rw [← crd_swap a] at h
    exact eq_inv_of_mul_eq_one_left h
  have hA' : σ (d (crd (Sum.swap a))) = (d (crd a))⁻¹ := by
    have h := hd (crd (Sum.swap a))
    have e : Fin.rev (crd (Sum.swap a)) = crd a := by
      rw [← crd_swap (Sum.swap a), Sum.swap_swap]
    rw [e] at h
    exact eq_inv_of_mul_eq_one_left h
  have hA0 : d (crd a) ≠ 0 := diagonal_ne_zero hd (crd a)
  have hA'0 : d (crd (Sum.swap a)) ≠ 0 := diagonal_ne_zero hd (crd (Sum.swap a))
  rw [map_mul, map_mul, map_inv₀, hA, hA']
  field_simp

private theorem conj_sigma_mul {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (a : Fin (m / 2) ⊕ Fin (m / 2)) (u : F) :
    σ (d (crd a) * u * (d (midIdx m hm))⁻¹) *
        (d (crd a) * u * (d (midIdx m hm))⁻¹) =
      d (crd a) * (d (crd (Sum.swap a)))⁻¹ * (σ u * u) := by
  have hA : σ (d (crd a)) = (d (crd (Sum.swap a)))⁻¹ := by
    have h := hd (crd a)
    rw [← crd_swap a] at h
    exact eq_inv_of_mul_eq_one_left h
  have hM : σ (d (midIdx m hm)) = (d (midIdx m hm))⁻¹ := by
    have h := hd (midIdx m hm)
    rw [rev_midIdx hm] at h
    exact eq_inv_of_mul_eq_one_left h
  have hA0 : d (crd a) ≠ 0 := diagonal_ne_zero hd (crd a)
  have hA'0 : d (crd (Sum.swap a)) ≠ 0 := diagonal_ne_zero hd (crd (Sum.swap a))
  have hM0 : d (midIdx m hm) ≠ 0 := diagonal_ne_zero hd (midIdx m hm)
  rw [map_mul, map_mul, map_inv₀, hA, hM]
  field_simp

private theorem heis_conj_valid {d : Fin m → F}
    (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1) (a : Fin (m / 2) ⊕ Fin (m / 2))
    {u v : F} (h : v + σ v + σ u * u = 0) :
    (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹) +
      σ (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹) +
      σ (d (crd a) * u * (d (midIdx m hm))⁻¹) *
        (d (crd a) * u * (d (midIdx m hm))⁻¹) = 0 := by
  rw [conj_add_sigma hd, conj_sigma_mul hm hd, ← mul_add, h, mul_zero]

theorem conj_suElt_of_mat_diagonal {g : SU σ m} {d : Fin m → F}
    (hg : mat σ m g = diagonal d) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b) (c : F) :
    g * suElt σ hσ a b c * g⁻¹ =
      suElt σ hσ a b (d (crd a) * c * (d (crd (Sum.swap b)))⁻¹) := by
  have hE := mat_inv_of_diagonal hg hd
  have hDE := diagonal_mul_diagonal_inv hd
  apply mat_injective
  rw [map_mul, map_mul, hg, hE, mat_suElt hσ hab c,
    mat_suElt hσ hab (d (crd a) * c * (d (crd (Sum.swap b)))⁻¹)]
  have hs1 : diagonal d * single (crd a) (crd (Sum.swap b)) c *
      diagonal (fun s => (d s)⁻¹) =
      single (crd a) (crd (Sum.swap b))
        (d (crd a) * c * (d (crd (Sum.swap b)))⁻¹) :=
    TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := fun s => (d s)⁻¹) c
  have hs2 : diagonal d * single (crd b) (crd (Sum.swap a)) (σ c) *
      diagonal (fun s => (d s)⁻¹) =
      single (crd b) (crd (Sum.swap a))
        (d (crd b) * σ c * (d (crd (Sum.swap a)))⁻¹) :=
    TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := fun s => (d s)⁻¹) (σ c)
  have hmain : diagonal d * (1 + single (crd a) (crd (Sum.swap b)) c -
      single (crd b) (crd (Sum.swap a)) (σ c)) * diagonal (fun s => (d s)⁻¹) =
      1 + single (crd a) (crd (Sum.swap b))
          (d (crd a) * c * (d (crd (Sum.swap b)))⁻¹) -
        single (crd b) (crd (Sum.swap a))
          (d (crd b) * σ c * (d (crd (Sum.swap a)))⁻¹) := by
    rw [show diagonal d * (1 + single (crd a) (crd (Sum.swap b)) c -
        single (crd b) (crd (Sum.swap a)) (σ c)) * diagonal (fun s => (d s)⁻¹) =
        diagonal d * diagonal (fun s => (d s)⁻¹) +
          (diagonal d * single (crd a) (crd (Sum.swap b)) c * diagonal (fun s => (d s)⁻¹) -
            diagonal d * single (crd b) (crd (Sum.swap a)) (σ c) *
              diagonal (fun s => (d s)⁻¹)) by
      noncomm_ring]
    rw [hDE, hs1, hs2]
    noncomm_ring
  rw [hmain]
  have hcoeff := sigma_diagonal_conj_coeff hd (crd a) (crd (Sum.swap b)) c
  rw [← crd_swap (Sum.swap b), Sum.swap_swap, ← crd_swap a] at hcoeff
  rw [hcoeff]

theorem heisenbergMatrix_eq_one_add (i k : Fin m) (u v : F) :
    heisenbergMatrix σ i k u v = 1 + (single i k u - single k (Fin.rev i) (σ u) +
      single i (Fin.rev i) v) := by
  rw [heisenbergMatrix]
  abel

theorem conj_suHeis_of_mat_diagonal {g : SU σ m} {d : Fin m → F}
    (hg : mat σ m g = diagonal d) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) {u v : F} (h : v + σ v + σ u * u = 0) :
    g * suHeis σ hσ hm a u v * g⁻¹ =
      suHeis σ hσ hm a (d (crd a) * u * (d (midIdx m hm))⁻¹)
        (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹) := by
  have h' := heis_conj_valid hm hd a h
  have hE := mat_inv_of_diagonal hg hd
  have hDE := diagonal_mul_diagonal_inv hd
  set i := crd a
  set e : Fin m → F := fun s => (d s)⁻¹ with he
  apply mat_injective
  rw [map_mul, map_mul, hg, hE, mat_suHeis hσ hm h, mat_suHeis hσ hm h',
    heisenbergMatrix_eq_one_add (i := crd a) (k := midIdx m hm) u v,
    heisenbergMatrix_eq_one_add (i := crd a) (k := midIdx m hm)
      (d (crd a) * u * (d (midIdx m hm))⁻¹) (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹)]
  have hs1 : diagonal d * single (crd a) (midIdx m hm) u * diagonal e =
      single (crd a) (midIdx m hm) (d (crd a) * u * e (midIdx m hm)) :=
    TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := e) u
  have hs2 : diagonal d * single (midIdx m hm) (Fin.rev (crd a)) (σ u) * diagonal e =
      single (midIdx m hm) (Fin.rev (crd a))
        (d (midIdx m hm) * σ u * e (Fin.rev (crd a))) :=
    TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := e) (σ u)
  have hs3 : diagonal d * single (crd a) (Fin.rev (crd a)) v * diagonal e =
      single (crd a) (Fin.rev (crd a)) (d (crd a) * v * e (Fin.rev (crd a))) :=
    TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := e) v
  have hcoeff := sigma_diagonal_conj_coeff hd (crd a) (midIdx m hm) u
  rw [rev_midIdx hm] at hcoeff
  rw [← hcoeff] at hs2
  have hmain : diagonal d * (1 + (single (crd a) (midIdx m hm) u -
        single (midIdx m hm) (Fin.rev (crd a)) (σ u) +
          single (crd a) (Fin.rev (crd a)) v)) * diagonal e =
      1 + (single (crd a) (midIdx m hm) (d (crd a) * u * (d (midIdx m hm))⁻¹) -
        single (midIdx m hm) (Fin.rev (crd a))
          (σ (d (crd a) * u * (d (midIdx m hm))⁻¹)) +
          single (crd a) (Fin.rev (crd a))
            (d (crd a) * v * (d (crd (Sum.swap a)))⁻¹)) := by
    rw [show diagonal d * (1 + (single (crd a) (midIdx m hm) u -
          single (midIdx m hm) (Fin.rev (crd a)) (σ u) +
            single (crd a) (Fin.rev (crd a)) v)) * diagonal e =
        diagonal d * diagonal e +
          (diagonal d * single (crd a) (midIdx m hm) u * diagonal e -
            diagonal d * single (midIdx m hm) (Fin.rev (crd a)) (σ u) * diagonal e +
              diagonal d * single (crd a) (Fin.rev (crd a)) v * diagonal e) by
      noncomm_ring]
    rw [hDE, hs1, hs2, hs3]
    simp only [he]
    rw [crd_swap a]
  rw [hmain]

theorem conj_suLong_of_mat_diagonal
    {g : SU σ m} {d : Fin m → F}
    (hg : mat σ m g = diagonal d) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    g * suLong σ a c * g⁻¹ =
      suLong σ a (d (crd a) * c * (d (crd (Sum.swap a)))⁻¹) := by
  have hE := mat_inv_of_diagonal hg hd
  have hDE := diagonal_mul_diagonal_inv hd
  by_cases hc : c + σ c = 0
  · have hc' : d (crd a) * c * (d (crd (Sum.swap a)))⁻¹ +
        σ (d (crd a) * c * (d (crd (Sum.swap a)))⁻¹) = 0 := by
      rw [conj_add_sigma hd, hc, mul_zero]
    apply mat_injective
    rw [map_mul, map_mul, hg, hE, mat_suLong a hc, mat_suLong a hc']
    have hs : diagonal d * single (crd a) (Fin.rev (crd a)) c *
        diagonal (fun s => (d s)⁻¹) =
        single (crd a) (Fin.rev (crd a)) (d (crd a) * c * (d (Fin.rev (crd a)))⁻¹) :=
      TauCeti.diagonal_mul_single_mul_diagonal (v := d) (w := fun s => (d s)⁻¹) c
    have hmain : diagonal d * (1 + single (crd a) (Fin.rev (crd a)) c) *
        diagonal (fun s => (d s)⁻¹) =
        1 + single (crd a) (Fin.rev (crd a)) (d (crd a) * c * (d (Fin.rev (crd a)))⁻¹) := by
      rw [show diagonal d * (1 + single (crd a) (Fin.rev (crd a)) c) *
          diagonal (fun s => (d s)⁻¹) =
          diagonal d * diagonal (fun s => (d s)⁻¹) +
            diagonal d * single (crd a) (Fin.rev (crd a)) c *
              diagonal (fun s => (d s)⁻¹) by noncomm_ring]
      rw [hDE, hs]
    rw [crd_swap a, hmain]
  · have hdi : d (crd a) * (d (crd (Sum.swap a)))⁻¹ ≠ 0 :=
      mul_ne_zero (diagonal_ne_zero hd (crd a))
        (inv_ne_zero (diagonal_ne_zero hd (crd (Sum.swap a))))
    have hc' : ¬(d (crd a) * c * (d (crd (Sum.swap a)))⁻¹ +
        σ (d (crd a) * c * (d (crd (Sum.swap a)))⁻¹) = 0) := by
      intro h0
      have h1 := conj_add_sigma hd a c
      rw [h0] at h1
      have : c + σ c = 0 := (mul_eq_zero.mp h1.symm).resolve_left hdi
      exact hc this
    rw [suLong, dite_eq_right hc, suLong, dite_eq_right hc']
    simp


end CFSG.Timmesfeld.Transvection.Pres
