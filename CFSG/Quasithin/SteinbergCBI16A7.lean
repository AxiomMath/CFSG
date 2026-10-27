module

public import CFSG.Quasithin.SteinbergCBI16FourGroup
public import CFSG.Quasithin.SteinbergCBI16Central

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix
open scoped Pointwise

abbrev A7 : Type := ↥(alternatingGroup (Fin 7))

@[expose] def tP : Perm (Fin 7) := swap 4 5 * swap 5 6
@[expose] def v1P : Perm (Fin 7) := swap 0 1 * swap 2 3
@[expose] def v2P : Perm (Fin 7) := swap 0 2 * swap 1 3

theorem tP_mem : tP ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, tP]
  decide +kernel

theorem v1P_mem : v1P ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, v1P]
  decide +kernel

theorem v2P_mem : v2P ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, v2P]
  decide +kernel

@[expose] def tA : A7 := ⟨tP, tP_mem⟩
@[expose] def v1A : A7 := ⟨v1P, v1P_mem⟩
@[expose] def v2A : A7 := ⟨v2P, v2P_mem⟩

theorem relations_perm : tP ^ 3 = 1 ∧ tP ≠ 1 ∧ v1P * v1P = 1 ∧ v2P * v2P = 1 ∧
    tP * v1P = v1P * tP ∧ tP * v2P = v2P * tP ∧ v1P * v2P = v2P * v1P ∧ v1P ≠ 1 ∧ v2P ≠ 1 ∧
    v1P ≠ v2P := by
  decide +kernel

theorem relations_A7 : tA ^ 3 = 1 ∧ tA ≠ 1 ∧ v1A * v1A = 1 ∧ v2A * v2A = 1 ∧
    tA * v1A = v1A * tA ∧ tA * v2A = v2A * tA ∧ v1A * v2A = v2A * v1A ∧ v1A ≠ 1 ∧ v2A ≠ 1 ∧
    v1A ≠ v2A := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := relations_perm
  refine ⟨Subtype.ext h1, fun h => h2 (congrArg Subtype.val h), Subtype.ext h3, Subtype.ext h4,
    Subtype.ext h5, Subtype.ext h6, Subtype.ext h7, fun h => h8 (congrArg Subtype.val h),
    fun h => h9 (congrArg Subtype.val h), fun h => h10 (congrArg Subtype.val h)⟩

theorem tP_sign : Perm.sign tP = 1 := Perm.mem_alternatingGroup.1 tP_mem

@[expose] def tPinv : Perm (Fin 7) := swap 5 6 * swap 4 5

theorem tP_inv : tP⁻¹ = tPinv :=
  inv_eq_of_mul_eq_one_right (by rw [tP, tPinv]; decide +kernel)

@[expose] def swapProd : List (Fin 7 × Fin 7) → Perm (Fin 7)
  | [] => 1
  | q :: l => swap q.1 q.2 * swapProd l

theorem sign_swapProd : ∀ l : List (Fin 7 × Fin 7), (∀ q ∈ l, q.1 ≠ q.2) →
    Perm.sign (swapProd l) = (-1) ^ l.length
  | [], _ => by simp [swapProd]
  | q :: l, h => by
    rw [swapProd, Perm.sign_mul, Perm.sign_swap (h q (List.mem_cons_self ..)),
      sign_swapProd l fun q' hq' => h q' (List.mem_cons_of_mem _ hq'), List.length_cons,
      pow_succ, mul_comm]

@[expose] def S456 : Finset (Fin 7) := {4, 5, 6}

@[expose] noncomputable def L7 : Subgroup A7 := MulAction.stabilizer A7 S456

@[expose] def witA7 : List (List (Fin 7 × Fin 7)) := [
  [(0, 4), (0, 1), (0, 5), (0, 2), (0, 6), (0, 3)], [(3, 6), (1, 4), (0, 5), (0, 2)],
  [(0, 4), (0, 6), (0, 3), (0, 1), (0, 5), (0, 2)],
  [(0, 5), (0, 6), (0, 3), (0, 1), (0, 4), (0, 2)], [(1, 5), (1, 3), (0, 4), (0, 2)],
  [(3, 6), (2, 5), (0, 4), (0, 1)], [(0, 5), (0, 2), (0, 4), (0, 6), (0, 3), (0, 1)],
  [(0, 4), (0, 2), (0, 5), (0, 6), (0, 3), (0, 1)], [(2, 4), (0, 5), (0, 3), (0, 1)],
  [(0, 4), (0, 6), (0, 3), (0, 5), (0, 2), (0, 1)],
  [(0, 5), (0, 6), (0, 3), (0, 4), (0, 2), (0, 1)], [(3, 5), (0, 4), (0, 2), (0, 1)],
  [(0, 4), (0, 5), (0, 6), (0, 3), (0, 2), (0, 1)], [(0, 5), (0, 3), (0, 2), (0, 1)],
  [(0, 4), (0, 3), (0, 2), (0, 1)], [(3, 6), (1, 5), (1, 2), (1, 4)],
  [(2, 5), (1, 4), (1, 6), (1, 3)], [(2, 4), (1, 5), (1, 6), (1, 3)],
  [(1, 4), (1, 2), (1, 5), (1, 3)], [(3, 4), (3, 6), (1, 5), (1, 2)],
  [(3, 5), (3, 6), (1, 4), (1, 2)], [(1, 5), (1, 3), (1, 4), (1, 2)],
  [(1, 5), (1, 6), (1, 3), (1, 2)], [(1, 4), (1, 5), (1, 3), (1, 2)],
  [(1, 5), (1, 4), (1, 3), (1, 2)], [(2, 4), (2, 6), (2, 3), (2, 5)],
  [(2, 5), (2, 6), (2, 3), (2, 4)], [(2, 4), (3, 5)], [(2, 4), (2, 5), (2, 6), (2, 3)],
  [(2, 5), (2, 3)], [(2, 4), (2, 3)], [(3, 5), (3, 6)], [(3, 4), (3, 5)], [(3, 5), (3, 4)], []]

theorem witA7_even : ∀ l ∈ witA7, (∀ q ∈ l, q.1 ≠ q.2) ∧ Even l.length := by
  rw [witA7]
  decide +kernel

theorem witA7_sign : ∀ l ∈ witA7, Perm.sign (swapProd l) = 1 := by
  intro l hl
  obtain ⟨hne, hev⟩ := witA7_even l hl
  rw [sign_swapProd l hne, hev.neg_one_pow]

theorem witA7_spec : ∀ T ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 7)),
    ∃ l ∈ witA7, swapProd l • S456 = T := by
  rw [witA7, S456]
  decide +kernel

theorem orbit_S456 : MulAction.orbit A7 S456 =
    ↑(Finset.powersetCard 3 (Finset.univ : Finset (Fin 7))) := by
  ext T
  constructor
  · rintro ⟨σ, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    change ((σ : Perm (Fin 7)) • S456).card = 3
    rw [Finset.card_smul_finset]
    rfl
  · intro hT
    obtain ⟨l, hl, hlT⟩ := witA7_spec T hT
    exact ⟨⟨swapProd l, Perm.mem_alternatingGroup.2 (witA7_sign l hl)⟩, hlT⟩

theorem index_L7 : L7.index = 35 := by
  rw [L7, MulAction.index_stabilizer, orbit_S456, Set.ncard_coe_finset, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  rfl

theorem fix_low (π : Perm (Fin 7)) (hπ : π = 1 ∨ π = tP ∨ π = tPinv ∨ π = swap 4 5 ∨
    π = swap 4 6 ∨ π = swap 5 6) : ∀ i : Fin 7, i.val < 4 → π i = i := by
  rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
  · intro i _
    rfl
  all_goals
    first
    | (rw [tP]; decide +kernel)
    | (rw [tPinv]; decide +kernel)
    | decide +kernel

theorem perm_fix_cases (g : Perm (Fin 7)) (hfix : ∀ i : Fin 7, i.val < 4 → g i = i)
    (hg : Perm.sign g = 1) : g = 1 ∨ g = tP ∨ g = tPinv := by
  have key : ∀ i : Fin 7, 4 ≤ i.val → i = 4 ∨ i = 5 ∨ i = 6 := by decide
  have hout : ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (g i).val := by
    intro i hi
    by_contra h
    push Not at h
    have h2 := g.injective (hfix (g i) h)
    rw [h2] at h
    omega
  have hext : ∀ π : Perm (Fin 7), (∀ i : Fin 7, i.val < 4 → π i = i) → π 4 = g 4 →
      π 5 = g 5 → π 6 = g 6 → g = π := by
    intro π hπ h4 h5 h6
    apply Equiv.ext
    intro i
    by_cases hi : i.val < 4
    · rw [hfix i hi, hπ i hi]
    · rcases key i (by omega) with rfl | rfl | rfl
      · exact h4.symm
      · exact h5.symm
      · exact h6.symm
  have hodd : ∀ a b : Fin 7, a ≠ b → g = swap a b → False := by
    intro a b hab h
    rw [h, Perm.sign_swap hab] at hg
    exact absurd hg (by decide)
  have htP : tP 4 = 5 ∧ tP 5 = 6 ∧ tP 6 = 4 := by
    rw [tP]
    decide +kernel
  have htPinv : tPinv 4 = 6 ∧ tPinv 5 = 4 ∧ tPinv 6 = 5 := by
    rw [tPinv]
    decide +kernel
  have hsw : swap (4 : Fin 7) 5 4 = 5 ∧ swap (4 : Fin 7) 5 5 = 4 ∧ swap (4 : Fin 7) 5 6 = 6 ∧
      swap (4 : Fin 7) 6 4 = 6 ∧ swap (4 : Fin 7) 6 5 = 5 ∧ swap (4 : Fin 7) 6 6 = 4 ∧
      swap (5 : Fin 7) 6 4 = 4 ∧ swap (5 : Fin 7) 6 5 = 6 ∧ swap (5 : Fin 7) 6 6 = 5 := by
    decide +kernel
  obtain ⟨ht4, ht5, ht6⟩ := htP
  obtain ⟨hu4, hu5, hu6⟩ := htPinv
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hsw
  rcases key _ (hout 4 (by decide)) with h4 | h4 | h4 <;>
    rcases key _ (hout 5 (by decide)) with h5 | h5 | h5 <;>
    rcases key _ (hout 6 (by decide)) with h6 | h6 | h6 <;>
    first
    | exact absurd (g.injective (h4.trans h5.symm)) (by decide)
    | exact absurd (g.injective (h4.trans h6.symm)) (by decide)
    | exact absurd (g.injective (h5.trans h6.symm)) (by decide)
    | exact Or.inl (hext 1 (fix_low 1 (Or.inl rfl)) h4.symm h5.symm h6.symm)
    | exact Or.inr (Or.inl (hext tP (fix_low tP (Or.inr (Or.inl rfl))) (ht4.trans h4.symm)
        (ht5.trans h5.symm) (ht6.trans h6.symm)))
    | exact Or.inr (Or.inr (hext tPinv (fix_low tPinv (Or.inr (Or.inr (Or.inl rfl))))
        (hu4.trans h4.symm) (hu5.trans h5.symm) (hu6.trans h6.symm)))
    | exact (hodd 4 5 (by decide) (hext _ (fix_low _ (by simp)) (s1.trans h4.symm)
        (s2.trans h5.symm) (s3.trans h6.symm))).elim
    | exact (hodd 4 6 (by decide) (hext _ (fix_low _ (by simp)) (s4.trans h4.symm)
        (s5.trans h5.symm) (s6.trans h6.symm))).elim
    | exact (hodd 5 6 (by decide) (hext _ (fix_low _ (by simp)) (s7.trans h4.symm)
        (s8.trans h5.symm) (s9.trans h6.symm))).elim

theorem conj_tP {l : A7} (hl : l ∈ L7) :
    (l : Perm (Fin 7)) * tP * (l : Perm (Fin 7))⁻¹ = tP ∨
      (l : Perm (Fin 7)) * tP * (l : Perm (Fin 7))⁻¹ = tP⁻¹ := by
  set c := (l : Perm (Fin 7)) * tP * (l : Perm (Fin 7))⁻¹ with hc
  have hS : (l : Perm (Fin 7)) • S456 = S456 := hl
  have hout : ∀ i : Fin 7, i.val < 4 → i ∉ S456 := by
    rw [S456]
    decide +kernel
  have htfix : ∀ j : Fin 7, j ∉ S456 → tP j = j := by
    rw [S456, tP]
    decide +kernel
  have hfix : ∀ i : Fin 7, i.val < 4 → c i = i := by
    intro i hi
    have hl' : (l : Perm (Fin 7))⁻¹ i ∉ S456 := by
      intro h
      apply hout i hi
      rw [← hS]
      exact Finset.mem_smul_finset.2 ⟨_, h, by
        rw [Perm.smul_def, Perm.inv_def, Equiv.apply_symm_apply]⟩
    rw [hc, Perm.mul_apply, Perm.mul_apply, htfix _ hl', Perm.inv_def, Equiv.apply_symm_apply]
  have hsign : Perm.sign c = 1 := by
    have hl1 : Perm.sign (l : Perm (Fin 7)) = 1 := Perm.mem_alternatingGroup.1 l.2
    rw [hc, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hl1, tP_sign, mul_one, one_mul]
  rcases perm_fix_cases c hfix hsign with h | h | h
  · exfalso
    apply relations_perm.2.1
    rw [hc, mul_inv_eq_one] at h
    exact mul_eq_left.1 h
  · exact Or.inl h
  · exact Or.inr (h.trans tP_inv.symm)

@[expose] noncomputable def matAct {G : Type*} [Group G] (M : G →* GL (Fin 4) (ZMod 2)) :
    G →* AddMonoid.End Vec4 where
  toFun g := (Matrix.mulVecLin ((M g : GL (Fin 4) (ZMod 2)) : Mat4)).toAddMonoidHom
  map_one' := by
    refine AddMonoidHom.ext fun v => ?_
    change ((M 1 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v
    rw [map_one, Units.val_one, one_mulVec]
  map_mul' g h := by
    refine AddMonoidHom.ext fun v => ?_
    change ((M (g * h) : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v =
      ((M g : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ (((M h : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v)
    rw [map_mul, Units.val_mul, mulVec_mulVec]

theorem matAct_apply {G : Type*} [Group G] (M : G →* GL (Fin 4) (ZMod 2)) (g : G) (v : Vec4) :
    matAct M g v = ((M g : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v := rfl

theorem Z1A_inv_of_vanish {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    {μ : G →* AddMonoid.End M} {f : G → M} (hf : f ∈ Z1A μ) {g : G} (hg : f g = 0) :
    f g⁻¹ = 0 := by
  have h := hf g⁻¹ g
  rw [inv_mul_cancel, Z1A_one hf, hg, map_zero, add_zero] at h
  exact h.symm

theorem Z1A_fixed_of_conj {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    {μ : G →* AddMonoid.End M} {f : G → M} (hf : f ∈ Z1A μ) {c l t : G} (hc : c * l = l * t)
    (hfc : f c = 0) (hft : f t = 0) : μ c (f l) = f l := by
  have h1 := hf c l
  have h2 := hf l t
  rw [hc] at h1
  rw [h1, hfc, zero_add, hft, map_zero, add_zero] at h2
  exact h2

theorem Z1A_le_B1A_A7 (M : A7 →* GL (Fin 4) (ZMod 2)) (hM : Function.Injective M) :
    Z1A (matAct M) ≤ B1A (matAct M) := by
  obtain ⟨ht3, ht1, hv1, hv2, htv1, htv2, hvv, hv1n, hv2n, hv12⟩ := relations_A7
  have hmat : ∀ a b : A7, a * b = b * a →
      (M a : Mat4) * (M b : Mat4) = (M b : Mat4) * (M a : Mat4) := by
    intro a b hab
    rw [← Units.val_mul, ← map_mul, hab, map_mul, Units.val_mul]
  have hne : ∀ a b : A7, a ≠ b → (M a : Mat4) ≠ (M b : Mat4) := fun a b hab h =>
    hab (hM (Units.ext h))
  have hsq : ∀ a : A7, a * a = 1 → (M a : Mat4) * (M a : Mat4) = 1 := fun a ha => by
    rw [← Units.val_mul, ← map_mul, ha, map_one, Units.val_one]
  have hne1 : ∀ a : A7, a ≠ 1 → (M a : Mat4) ≠ 1 := fun a ha h =>
    hne a 1 ha (by rw [h, map_one, Units.val_one])
  set x : Mat4 := (M tA : Mat4) with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← Units.val_pow_eq_pow_val, ← map_pow, ht3, map_one, Units.val_one]
  have hfp : ∀ v, x *ᵥ v = v → v = 0 := fun v hv =>
    fixed_eq_zero_of_fourGroup hx3 (hne1 _ ht1) (hsq _ hv1) (hsq _ hv2) (hmat _ _ htv1)
      (hmat _ _ htv2) (hmat _ _ hvv) (hne1 _ hv1n) (hne1 _ hv2n) (hne _ _ hv12) hv
  have hinj : Function.Injective fun v : Vec4 => x *ᵥ v - v := by
    intro v w h
    have h' : x *ᵥ v - v = x *ᵥ w - w := h
    have hvw : x *ᵥ (v - w) = v - w := by
      rw [mulVec_sub]
      linear_combination (norm := abel_nf) h'
    exact sub_eq_zero.1 (hfp _ hvw)
  intro f hf
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.1 hinj (f tA)
  have hm' : x *ᵥ m - m = f tA := hm
  refine mem_B1A_of_restrict (H := L7) (fun v => vec4_add_self v) ?_ hf (m := m) ?_
  · rw [index_L7]
    decide
  · intro l hl
    set f' : A7 → Vec4 := fun g => f g - (matAct M g m - m) with hf'
    have hf'Z : f' ∈ Z1A (matAct M) := sub_mem hf (B1A_le_Z1A _ ⟨m, rfl⟩)
    have hf't : f' tA = 0 := by
      change f tA - (x *ᵥ m - m) = 0
      rw [hm', sub_self]
    have hf'ti : f' tA⁻¹ = 0 := Z1A_inv_of_vanish hf'Z hf't
    have hconj : l * tA * l⁻¹ = tA ∨ l * tA * l⁻¹ = tA⁻¹ := by
      rcases conj_tP hl with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hfix : ∀ c : A7, c * l = l * tA → f' c = 0 → matAct M c (f' l) = f' l :=
      fun c hc hfc => Z1A_fixed_of_conj hf'Z hc hfc hf't
    have hzero : f' l = 0 := by
      rcases hconj with h | h
      · have hc : tA * l = l * tA := by
          calc tA * l = l * tA * l⁻¹ * l := by rw [h]
            _ = l * tA := by group
        exact hfp _ (hfix tA hc hf't)
      · have hc : tA⁻¹ * l = l * tA := by
          calc tA⁻¹ * l = l * tA * l⁻¹ * l := by rw [h]
            _ = l * tA := by group
        have h1 := hfix tA⁻¹ hc hf'ti
        rw [matAct_apply] at h1
        apply hfp
        conv_lhs => rw [← h1]
        rw [hx, mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
          Units.val_one, one_mulVec]
    have hz : f l - (matAct M l m - m) = 0 := hzero
    exact sub_eq_zero.1 hz

@[expose] def transposeInvHom : GL (Fin 4) (ZMod 2) →* GL (Fin 4) (ZMod 2) where
  toFun g := ⟨((g⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ, (g : Mat4)ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩
  map_one' := Units.ext (by
    change ((1⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ = 1
    rw [inv_one, Units.val_one, transpose_one])
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ =
      ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ * ((h⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

theorem transposeInvHom_injective : Function.Injective transposeInvHom := by
  intro g h hgh
  have h1 : ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ = ((h⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4)ᵀ :=
    congrArg Units.val hgh
  have h2 : g⁻¹ = h⁻¹ := Units.ext (transpose_injective h1)
  exact inv_injective h2

theorem altLift7At_injective (p : Fin 8) : Function.Injective (altLift7At p) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext (Perm.viaEmbeddingHom_injective _ h)

@[expose] noncomputable def a7Hom (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    (p : Fin 8) : NatDual → A7 →* GL (Fin 4) (ZMod 2)
  | .natural => α.toMonoidHom.comp (altLift7At p)
  | .dual => transposeInvHom.comp (α.toMonoidHom.comp (altLift7At p))

theorem a7Hom_injective (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)) (p : Fin 8)
    (ε : NatDual) : Function.Injective (a7Hom α p ε) := by
  cases ε with
  | natural => exact α.injective.comp (altLift7At_injective p)
  | dual => exact transposeInvHom_injective.comp (α.injective.comp (altLift7At_injective p))

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem Z1_le_B1_of_transport {ρ : Representation (ZMod 2) Γ W} {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] {μ : G →* AddMonoid.End M} {θ : Γ ≃* G} {β : W ≃+ M}
    (hβ : ∀ γ w, β (ρ γ w) = μ (θ γ) (β w)) (h : Z1A μ ≤ B1A μ) : Z1 ρ ≤ B1 ρ := fun _ hf =>
  (transport_mem_B1A hβ).1 (h ((transport_mem_Z1A hβ).2 hf))

theorem finrank_H1_a7Four {ρ : Representation (ZMod 2) Γ W} {p : Fin 8} {ε : NatDual}
    (h : Explicit.A7Four ρ p ε) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨α, θ, β, hw⟩ := h
  have hamb := Witness.ambient (D := a7FourModel α p ε) rfl rfl hw
  set e := (β.trans (secEquivAmb (a7FourModel α p ε) rfl rfl).toAdditive).trans
    (AddEquiv.additiveMultiplicative Vec4) with he
  have hβ : ∀ γ w, e (ρ γ w) = matAct (a7Hom α p ε) (θ γ) (e w) := by
    intro γ w
    change AddEquiv.additiveMultiplicative Vec4
      ((β.trans (secEquivAmb (a7FourModel α p ε) rfl rfl).toAdditive) (ρ γ w)) = _
    rw [hamb γ w]
    cases ε <;> rfl
  exact finrank_H1_eq_zero_of_le (Z1_le_B1_of_transport hβ
    (Z1A_le_B1A_A7 _ (a7Hom_injective α p ε)))

end CFSG.Quasithin.SteinbergCB.I16
