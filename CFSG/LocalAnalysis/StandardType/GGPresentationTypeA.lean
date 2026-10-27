module

public import CFSG.LocalAnalysis.StandardType.GGPresentationReduce
public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear

variable (m : ℕ) (F : Type) [Field F]

theorem exists_weyl_toStd (π : Equiv.Perm (Fin (m + 1))) :
    ∃ w : (coxeterMatrix (isFiniteType_A m)).Group,
      ∀ γ, toStd m (weylAction (isFiniteType_A m) w γ) = fun a => toStd m γ (π.symm a) := by
  have hmem : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top π
  induction hmem using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨(coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k, fun γ => ?_⟩
    rw [weylAction_simple, toStd_reflection]
    funext a
    simp
  | one => exact ⟨1, fun γ => by rw [map_one, Module.End.one_apply]; rfl⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨w₁, h₁⟩ := ihx
    obtain ⟨w₂, h₂⟩ := ihy
    refine ⟨w₁ * w₂, fun γ => ?_⟩
    rw [weylAction_mul_apply, h₁, h₂]
    funext a
    simp [Equiv.Perm.mul_def]

@[expose] def typeAJ₁ : Finset (Fin m) := Finset.univ.filter fun k => k.val + 1 < m

theorem typeA_mem_lattice {v : Fin m → ℤ} (h : toStd m v (Fin.last m) = 0) :
    v ∈ ggSuppLattice (rootDatum m F) (typeAJ₁ m) := by
  rintro ⟨i, hi_lt⟩ hi
  change i < m at hi_lt
  have hi' : i + 1 = m := by
    have : ¬ (i + 1 < m) := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have e : toStd m v (Fin.last m) = - v ⟨i, hi_lt⟩ := by
    have hm0 : 0 < m := by omega
    simp only [toStd, Fin.val_last, lt_irrefl, dite_false, zero_sub, hm0, dite_true]
    congr 2
    ext
    simp only
    omega
  change v ⟨i, hi_lt⟩ = 0
  omega

theorem typeA_orbit (hm : 4 ≤ m) :
    GGOrbit (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m)) := by
  refine ggOrbit_of_pairs (fun _ => ggSuppLattice (rootDatum m F) (typeAJ₁ m))
    (fun _ γ hγ hγM => ⟨hγ, hγM⟩) ?_
  intro J hJ
  let J' : Finset (Fin m) := J
  have h4 : J'.card ≤ 2 := hJ
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin (m + 1)),
      E = J'.image Fin.castSucc ∪ J'.image Fin.succ := ⟨_, rfl⟩
  have hE : E.card < (Finset.univ : Finset (Fin (m + 1))).card := by
    have h1 := Finset.card_union_le (J'.image Fin.castSucc) (J'.image Fin.succ)
    have h2 := Finset.card_image_le (s := J') (f := Fin.castSucc)
    have h3 := Finset.card_image_le (s := J') (f := Fin.succ)
    rw [Finset.card_univ, Fintype.card_fin, hEdef]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hE
  obtain ⟨w, hw⟩ := exists_weyl_toStd m (Equiv.swap c (Fin.last m))
  refine ⟨w, (), fun j hj => typeA_mem_lattice m F ?_⟩
  let j' : Fin m := j
  have hj' : j' ∈ J' := hj
  have hc1 : c ≠ j'.castSucc := fun h =>
    hc (hEdef ▸ Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j', hj', h.symm⟩))
  have hc2 : c ≠ j'.succ := fun h =>
    hc (hEdef ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j', hj', h.symm⟩))
  change toStd m (weylAction (isFiniteType_A m) w (Pi.single j' 1)) (Fin.last m) = 0
  rw [hw]
  change toStd m (Pi.single j' 1) ((Equiv.swap c (Fin.last m)).symm (Fin.last m)) = 0
  rw [toStd_single]
  simp [Equiv.swap_apply_right, hc1, hc2]

@[expose] def TypeARealizes (w : (coxeterMatrix (isFiniteType_A m)).Group)
    (π : Equiv.Perm (Fin (m + 1))) : Prop :=
  ∀ γ, toStd m (weylAction (isFiniteType_A m) w γ) = fun a => toStd m γ (π.symm a)

theorem typeARealizes_one : TypeARealizes m 1 1 := fun γ => by
  rw [map_one, Module.End.one_apply]
  rfl

theorem typeARealizes_mul {w₁ w₂ : (coxeterMatrix (isFiniteType_A m)).Group}
    {π₁ π₂ : Equiv.Perm (Fin (m + 1))} (h₁ : TypeARealizes m w₁ π₁)
    (h₂ : TypeARealizes m w₂ π₂) : TypeARealizes m (w₁ * w₂) (π₁ * π₂) := fun γ => by
  rw [weylAction_mul_apply, h₁, h₂]
  funext a
  simp [Equiv.Perm.mul_def]

theorem typeARealizes_simple (k : Fin m) :
    TypeARealizes m ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k)
      (Equiv.swap k.castSucc k.succ) := fun γ => by
  rw [weylAction_simple, toStd_reflection]
  funext a
  simp

theorem exists_typeARealizes (w : (coxeterMatrix (isFiniteType_A m)).Group) :
    ∃ π, TypeARealizes m w π := by
  induction w using (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple_induction_left with
  | one => exact ⟨1, typeARealizes_one m⟩
  | mul_simple_left w k ih =>
    obtain ⟨π, hπ⟩ := ih
    exact ⟨_, typeARealizes_mul m (typeARealizes_simple m k) hπ⟩

theorem typeARealizes_inj {w w' : (coxeterMatrix (isFiniteType_A m)).Group}
    {π : Equiv.Perm (Fin (m + 1))} (h : TypeARealizes m w π) (h' : TypeARealizes m w' π) :
    w = w' :=
  weylAction_injective (isFiniteType_A m)
    (LinearMap.ext fun γ => toStd_injective m ((h γ).trans (h' γ).symm))

@[expose] def typeAW₁ : Subgroup (coxeterMatrix (isFiniteType_A m)).Group :=
  Subgroup.closure ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
    (typeAJ₁ m : Set (Fin m)))

theorem exists_typeAW₁_swap_adj (x y : Fin (m + 1)) (hxy : y.val = x.val + 1) (hy : y.val < m) :
    ∃ w ∈ typeAW₁ m, TypeARealizes m w (Equiv.swap x y) := by
  have hk : x.val < m := by omega
  let k : Fin m := ⟨x.val, hk⟩
  have hkJ : k ∈ typeAJ₁ m := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [k]; omega⟩
  refine ⟨(coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k,
    Subgroup.subset_closure ⟨k, hkJ, rfl⟩, ?_⟩
  have e1 : k.castSucc = x := Fin.ext (by simp [k])
  have e2 : k.succ = y := Fin.ext (by simp only [k, Fin.val_succ]; omega)
  rw [← e1, ← e2]
  exact typeARealizes_simple m k

theorem exists_typeAW₁_swap_of_lt : ∀ (d : ℕ) (x y : Fin (m + 1)), y.val = x.val + d + 1 →
    y.val < m → ∃ w ∈ typeAW₁ m, TypeARealizes m w (Equiv.swap x y) := by
  intro d
  induction d with
  | zero => exact fun x y hxy hy => exists_typeAW₁_swap_adj m x y (by omega) hy
  | succ d ih =>
    intro x y hxy hy
    let y' : Fin (m + 1) := ⟨x.val + d + 1, by omega⟩
    obtain ⟨w₁, hw₁, h₁⟩ := ih x y' rfl (by simp only [y']; omega)
    obtain ⟨w₂, hw₂, h₂⟩ := exists_typeAW₁_swap_adj m y' y (by simp only [y']; omega) hy
    have hx1 : x ≠ y' := fun h => by
      have := congrArg Fin.val h
      simp only [y'] at this
      omega
    have hx2 : x ≠ y := fun h => by
      have := congrArg Fin.val h
      omega
    have key : Equiv.swap x y = Equiv.swap y' y * Equiv.swap x y' * Equiv.swap y' y := by
      have := Equiv.swap_apply_apply (Equiv.swap y' y) x y'
      rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_left, Equiv.swap_inv] at this
      exact this
    refine ⟨w₂ * w₁ * w₂, mul_mem (mul_mem hw₂ hw₁) hw₂, ?_⟩
    rw [key]
    exact typeARealizes_mul m (typeARealizes_mul m h₂ h₁) h₂

theorem exists_typeAW₁_swap (x y : Fin (m + 1)) (hx : x.val < m) (hy : y.val < m) :
    ∃ w ∈ typeAW₁ m, TypeARealizes m w (Equiv.swap x y) := by
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact exists_typeAW₁_swap_of_lt m (y.val - x.val - 1) x y (by omega) hy
  · obtain rfl : x = y := Fin.ext h
    exact ⟨1, one_mem _, by rw [Equiv.swap_self]; exact typeARealizes_one m⟩
  · obtain ⟨w, hw, hw'⟩ := exists_typeAW₁_swap_of_lt m (x.val - y.val - 1) y x (by omega) hx
    exact ⟨w, hw, by rw [Equiv.swap_comm]; exact hw'⟩

theorem typeA_root_of_mem {γ : Fin m → ℤ}
    (hγ : γ ∈ ggSupp (rootDatum m F) (typeAJ₁ m)) :
    ∃ a b : Fin (m + 1), a ≠ b ∧ a.val < m ∧ b.val < m ∧
      toStd m γ = Pi.single a 1 - Pi.single b 1 := by
  have hroot : γ ∈ roots (isFiniteType_A m) ∅ := hγ.1
  rw [roots_eq] at hroot
  obtain ⟨a, b, hab, hγab⟩ := hroot
  have hlast : toStd m γ (Fin.last m) = 0 := by
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
      · exact hm
    have h0 : γ ⟨m - 1, by omega⟩ = 0 := hγ.2 ⟨m - 1, by change m - 1 < m; omega⟩ fun h => by
      have := (Finset.mem_filter.mp h).2
      simp only at this
      omega
    simp only [toStd, Fin.val_last, lt_irrefl, dite_false, zero_sub, hm, dite_true, h0, neg_zero]
  rw [hγab] at hlast
  have ha : a ≠ Fin.last m := fun h => by
    subst h
    simp [Ne.symm hab] at hlast
  have hb : b ≠ Fin.last m := fun h => by
    subst h
    simp [hab] at hlast
  exact ⟨a, b, hab, Fin.val_lt_last ha, Fin.val_lt_last hb, hγab⟩

theorem typeA_transitive {α β : Fin m → ℤ} (hα : α ∈ ggSupp (rootDatum m F) (typeAJ₁ m))
    (hβ : β ∈ ggSupp (rootDatum m F) (typeAJ₁ m)) :
    ∃ w ∈ typeAW₁ m, weylAction (isFiniteType_A m) w α = β := by
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeA_root_of_mem m F hα
  obtain ⟨a', b', hab', ha', hb', hβab⟩ := typeA_root_of_mem m F hβ
  let b'' := Equiv.swap a a' b
  have hb''m : b''.val < m := by
    simp only [b'', Equiv.swap_apply_def]
    split_ifs <;> assumption
  have hb''a' : b'' ≠ a' := fun h => hab (by
    have := congrArg (Equiv.swap a a') h
    simpa [b''] using this.symm)
  obtain ⟨w₁, hw₁, h₁⟩ := exists_typeAW₁_swap m a a' ha ha'
  obtain ⟨w₂, hw₂, h₂⟩ := exists_typeAW₁_swap m b'' b' hb''m hb'
  refine ⟨w₂ * w₁, mul_mem hw₂ hw₁, toStd_injective m ?_⟩
  rw [typeARealizes_mul m h₂ h₁ α, hαab, hβab]
  have hπa : (Equiv.swap b'' b' * Equiv.swap a a') a = a' := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hb''a') hab'
  have hπb : (Equiv.swap b'' b' * Equiv.swap a a') b = b' := by
    simp only [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
  funext x
  simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq, hπa, hπb]

theorem typeA_refl_mem (w : (coxeterMatrix (isFiniteType_A m)).Group) (j : Fin m)
    (hj : weylAction (isFiniteType_A m) w (Pi.single j 1) ∈
      ggSupp (rootDatum m F) (typeAJ₁ m)) :
    w * (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j * w⁻¹ ∈ typeAW₁ m := by
  obtain ⟨π, hπ⟩ := exists_typeARealizes m w
  obtain ⟨a, b, hab, ha, hb, hγab⟩ := typeA_root_of_mem m F hj
  rw [hπ, toStd_single] at hγab
  have hπa : π j.castSucc = a := by
    by_contra h
    have := congrFun hγab a
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq] at this
    split_ifs at this <;> simp_all
  have hπb : π j.succ = b := by
    by_contra h
    have := congrFun hγab b
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq] at this
    split_ifs at this <;> simp_all
  obtain ⟨w', hw', h'⟩ := exists_typeAW₁_swap m a b ha hb
  have hinv : TypeARealizes m w⁻¹ π⁻¹ := fun γ => by
    have := hπ (weylAction (isFiniteType_A m) w⁻¹ γ)
    rw [weylAction_apply_inv_apply] at this
    funext x
    have h2 := congrFun this (π x)
    simp only [Equiv.symm_apply_apply] at h2
    rw [← h2]
    rfl
  have hconj := typeARealizes_mul m (typeARealizes_mul m hπ (typeARealizes_simple m j)) hinv
  rw [← Equiv.swap_apply_apply, hπa, hπb] at hconj
  rw [typeARealizes_inj m hconj h']
  exact hw'

end CFSG.StandardType
