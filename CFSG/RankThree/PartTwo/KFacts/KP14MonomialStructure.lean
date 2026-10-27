module

public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP14

open Matrix

@[expose] def diagVec : Fin 4 → Fin 3 → ZMod 3 :=
  ![![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]

@[expose] def diagIdx (v : Fin 3 → ZMod 3) : Fin 4 :=
  if v 0 * v 1 = 1 then (if v 0 * v 2 = 1 then 0 else 1) else (if v 0 * v 2 = 1 then 2 else 3)

@[expose] def diagMap (M : Mat3) (i : Fin 4) : Fin 4 := diagIdx (M *ᵥ diagVec i)

theorem diagIdx_smul : ∀ c : ZMod 3, c ≠ 0 → ∀ v : Fin 3 → ZMod 3,
    diagIdx (c • v) = diagIdx v := by
  decide +kernel

theorem mat_diag_spec : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) → ∀ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
      signedMat π s *ᵥ diagVec i = c • diagVec (diagMap (signedMat π s) i) := by
  decide +kernel

theorem diagMap_one (i : Fin 4) : diagMap 1 i = i := by
  revert i
  decide +kernel

theorem diagMap_mul {M N : GL (Fin 3) (ZMod 3)} (hM : M ∈ monomial) (hN : N ∈ monomial)
    (i : Fin 4) : diagMap ((M * N : GL (Fin 3) (ZMod 3)) : Mat3) i = diagMap M (diagMap N i) := by
  obtain ⟨c, hc, hNi⟩ := forall_mem_monomial (P := fun A => ∀ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
    A *ᵥ diagVec i = c • diagVec (diagMap A i)) (fun π hπ s hs => mat_diag_spec π hπ s hs) hN i
  have key : ((M * N : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ diagVec i =
      c • ((M : Mat3) *ᵥ diagVec (diagMap N i)) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hNi, Matrix.mulVec_smul]
  have hM' := hM
  change diagIdx (((M * N : GL (Fin 3) (ZMod 3)) : Mat3) *ᵥ diagVec i) =
    diagIdx ((M : Mat3) *ᵥ diagVec (diagMap N i))
  rw [key, diagIdx_smul c hc]

@[expose] def diagEquiv (g : monomial) : Equiv.Perm (Fin 4) where
  toFun := diagMap ((g : GL (Fin 3) (ZMod 3)) : Mat3)
  invFun := diagMap (((g⁻¹ : monomial) : GL (Fin 3) (ZMod 3)) : Mat3)
  left_inv i := by
    have h := diagMap_mul (g⁻¹).2 g.2 i
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, diagMap_one] at h
    exact h.symm
  right_inv i := by
    have h := diagMap_mul g.2 (g⁻¹).2 i
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, diagMap_one] at h
    exact h.symm

theorem diagEquiv_apply (g : monomial) (i : Fin 4) :
    diagEquiv g i = diagMap ((g : GL (Fin 3) (ZMod 3)) : Mat3) i := rfl

@[expose] def diagPerm : monomial →* Equiv.Perm (Fin 4) where
  toFun := diagEquiv
  map_one' := Equiv.ext fun i => by
    rw [diagEquiv_apply, Subgroup.coe_one, Units.val_one, diagMap_one]
    rfl
  map_mul' g h := Equiv.ext fun i => by
    rw [Equiv.Perm.mul_apply, diagEquiv_apply, diagEquiv_apply, diagEquiv_apply,
      Subgroup.coe_mul, diagMap_mul g.2 h.2]

theorem diagPerm_apply (g : monomial) (i : Fin 4) :
    diagPerm g i = diagMap ((g : GL (Fin 3) (ZMod 3)) : Mat3) i := rfl

theorem diagPerm_mk (x : GL (Fin 3) (ZMod 3)) (hx : x ∈ monomial) (i : Fin 4) :
    diagPerm ⟨x, hx⟩ i = diagMap (x : Mat3) i := rfl

@[expose] def signProd (M : Mat3) : ZMod 3 := ∏ j, ∑ i, M i j

theorem signProd_signedMat (π : Fin 3 → Fin 3) (s : Fin 3 → ZMod 3) :
    signProd (signedMat π s) = ∏ j, s j := by
  simp [signProd, signedMat]

theorem signProd_mul {M N : GL (Fin 3) (ZMod 3)} (hM : M ∈ monomial) (hN : N ∈ monomial) :
    signProd ((M * N : GL (Fin 3) (ZMod 3)) : Mat3) = signProd M * signProd N := by
  obtain ⟨π, hπ, s, hs, hMe⟩ := hM
  obtain ⟨τ, hτ, t, ht, hNe⟩ := hN
  rw [Units.val_mul, hMe, hNe, signedMat_mul, signProd_signedMat, signProd_signedMat,
    signProd_signedMat, Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_bijective τ hτ _ _ fun _ => rfl

theorem signProd_ne_zero {M : GL (Fin 3) (ZMod 3)} (hM : M ∈ monomial) : signProd M ≠ 0 := by
  obtain ⟨π, hπ, s, hs, hMe⟩ := hM
  rw [hMe, signProd_signedMat]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hs j

@[expose] def toSign (a : ZMod 3) : ℤˣ := if a = 1 then 1 else -1

theorem toSign_mul : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → toSign (a * b) = toSign a * toSign b := by
  decide +kernel

@[expose] def signChar : monomial →* ℤˣ where
  toFun g := toSign (signProd ((g : GL (Fin 3) (ZMod 3)) : Mat3))
  map_one' := by
    rw [Subgroup.coe_one, Units.val_one]
    decide +kernel
  map_mul' g h := by
    rw [Subgroup.coe_mul, signProd_mul g.2 h.2, toSign_mul _ _ (signProd_ne_zero g.2)
      (signProd_ne_zero h.2)]

theorem signChar_apply (g : monomial) :
    signChar g = toSign (signProd ((g : GL (Fin 3) (ZMod 3)) : Mat3)) := rfl

theorem signChar_mk (x : GL (Fin 3) (ZMod 3)) (hx : x ∈ monomial) :
    signChar ⟨x, hx⟩ = toSign (signProd (x : Mat3)) := rfl

@[expose] def negOne : monomial :=
  ⟨-1, mem_monomial_of id (fun _ => 2) Function.bijective_id (by decide) (by decide)⟩

theorem mat_diag_ker : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) → (∀ i, diagMap (signedMat π s) i = i) →
      signedMat π s = 1 ∨ signedMat π s = -1 := by
  decide +kernel

theorem eq_one_or_eq_negOne {g : monomial} (hg : diagPerm g = 1) : g = 1 ∨ g = negOne := by
  have h := forall_mem_monomial (P := fun A => (∀ i, diagMap A i = i) → A = 1 ∨ A = -1)
    mat_diag_ker g.2 (fun i => by rw [← diagPerm_apply, hg, Equiv.Perm.one_apply])
  rcases h with h | h
  · exact Or.inl (Subtype.ext (Units.ext h))
  · exact Or.inr (Subtype.ext (Units.ext h))

theorem signChar_negOne : signChar negOne = -1 := by decide +kernel

theorem diagPerm_negOne : diagPerm negOne = 1 := by
  ext i
  revert i
  decide +kernel

@[expose] def theta : monomial →* ℤˣ × Equiv.Perm (Fin 4) := signChar.prod diagPerm

theorem theta_injective : Function.Injective theta := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : signChar g = 1 := congrArg Prod.fst hg
  have h2 : diagPerm g = 1 := congrArg Prod.snd hg
  rcases eq_one_or_eq_negOne h2 with h | h
  · exact h
  · rw [h, signChar_negOne] at h1
    exact absurd h1 (by decide)

theorem swapRefl_le : Subgroup.closure swapRefl ≤ monomial :=
  (Subgroup.closure_le _).mpr fun _ hx => monoRefl_subset_monomial (Or.inr hx)

theorem closure_swapRefl_le_ker :
    Subgroup.closure swapRefl ≤ signChar.ker.map monomial.subtype := by
  rw [Subgroup.closure_le]
  intro x hx
  have hxm : x ∈ monomial := monoRefl_subset_monomial (Or.inr hx)
  rw [SetLike.mem_coe, Subgroup.mem_map]
  refine ⟨⟨x, hxm⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker, signChar_mk]
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem signChar_of_mem_closure {g : monomial}
    (hg : (g : GL (Fin 3) (ZMod 3)) ∈ Subgroup.closure swapRefl) : signChar g = 1 := by
  obtain ⟨y, hy, hyg⟩ := closure_swapRefl_le_ker hg
  rw [← MonoidHom.mem_ker, ← show y = g from Subtype.ext hyg]
  exact hy

theorem negOne_not_mem_closure :
    ((negOne : monomial) : GL (Fin 3) (ZMod 3)) ∉ Subgroup.closure swapRefl := by
  intro h
  have := signChar_of_mem_closure h
  rw [signChar_negOne] at this
  exact absurd this (by decide)

theorem not_mem_closure_swapRefl {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ diagRefl) :
    x ∉ Subgroup.closure swapRefl := by
  intro h
  have hxm : x ∈ monomial := monoRefl_subset_monomial (Or.inl hx)
  have := signChar_of_mem_closure (g := ⟨x, hxm⟩) h
  rw [signChar_mk] at this
  revert this
  simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> decide +kernel

@[expose] def swapReflPerm : Subgroup.closure swapRefl →* Equiv.Perm (Fin 4) :=
  diagPerm.comp (Subgroup.inclusion swapRefl_le)

theorem swapReflPerm_apply (k : Subgroup.closure swapRefl) (i : Fin 4) :
    swapReflPerm k i = diagMap ((k : GL (Fin 3) (ZMod 3)) : Mat3) i := rfl

theorem swapReflPerm_injective : Function.Injective swapReflPerm := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rcases eq_one_or_eq_negOne (g := Subgroup.inclusion swapRefl_le k) hk with h | h
  · exact Subgroup.inclusion_injective swapRefl_le (h.trans (map_one _).symm)
  · have h' : (k : GL (Fin 3) (ZMod 3)) = ((negOne : monomial) : GL (Fin 3) (ZMod 3)) := by
      rw [← h, Subgroup.coe_inclusion]
    exact absurd (h' ▸ k.2) negOne_not_mem_closure

theorem mem_closure_of_mem {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl) :
    x ∈ Subgroup.closure swapRefl :=
  Subgroup.subset_closure hx

theorem swapReflPerm_p01 :
    swapReflPerm ⟨p01, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 2 3 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swapReflPerm_m01 :
    swapReflPerm ⟨m01, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 0 1 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swapReflPerm_p12 :
    swapReflPerm ⟨p12, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 1 2 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swapReflPerm_m12 :
    swapReflPerm ⟨m12, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 0 3 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swapReflPerm_p02 :
    swapReflPerm ⟨p02, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 1 3 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swapReflPerm_m02 :
    swapReflPerm ⟨m02, mem_closure_of_mem (by simp [swapRefl])⟩ = Equiv.swap 0 2 := by
  ext i
  rw [swapReflPerm_apply]
  revert i
  decide +kernel

theorem swap_cases : ∀ a b : Fin 4, a ≠ b →
    Equiv.swap a b = Equiv.swap 2 3 ∨ Equiv.swap a b = Equiv.swap 0 1 ∨
      Equiv.swap a b = Equiv.swap 1 2 ∨ Equiv.swap a b = Equiv.swap 0 3 ∨
      Equiv.swap a b = Equiv.swap 1 3 ∨ Equiv.swap a b = Equiv.swap 0 2 := by
  decide +kernel

theorem isSwap_swapReflPerm {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl) :
    (swapReflPerm ⟨x, mem_closure_of_mem hx⟩).IsSwap := by
  simp only [swapRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 3, by decide, swapReflPerm_p01⟩
  · exact ⟨0, 1, by decide, swapReflPerm_m01⟩
  · exact ⟨1, 2, by decide, swapReflPerm_p12⟩
  · exact ⟨0, 3, by decide, swapReflPerm_m12⟩
  · exact ⟨1, 3, by decide, swapReflPerm_p02⟩
  · exact ⟨0, 2, by decide, swapReflPerm_m02⟩

theorem swapReflPerm_surjective : Function.Surjective swapReflPerm := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨a, b, hab, rfl⟩
  rcases swap_cases a b hab with h | h | h | h | h | h <;> rw [h]
  · exact ⟨_, swapReflPerm_p01⟩
  · exact ⟨_, swapReflPerm_m01⟩
  · exact ⟨_, swapReflPerm_p12⟩
  · exact ⟨_, swapReflPerm_m12⟩
  · exact ⟨_, swapReflPerm_p02⟩
  · exact ⟨_, swapReflPerm_m02⟩

@[expose] noncomputable def swapReflEquiv : Subgroup.closure swapRefl ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective swapReflPerm ⟨swapReflPerm_injective, swapReflPerm_surjective⟩

theorem swapReflEquiv_apply (k : Subgroup.closure swapRefl) :
    swapReflEquiv k = swapReflPerm k := rfl

theorem card_closure_swapRefl : Nat.card (Subgroup.closure swapRefl) = 24 := by
  rw [Nat.card_congr swapReflEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  rfl

theorem theta_surjective : Function.Surjective theta := by
  rintro ⟨u, σ⟩
  obtain ⟨k, hk⟩ := swapReflPerm_surjective σ
  have hk1 : signChar (Subgroup.inclusion swapRefl_le k) = 1 := signChar_of_mem_closure k.2
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨Subgroup.inclusion swapRefl_le k, Prod.ext hk1 hk⟩
  · refine ⟨negOne * Subgroup.inclusion swapRefl_le k, Prod.ext ?_ ?_⟩
    · show signChar (negOne * _) = -1
      rw [map_mul, signChar_negOne, hk1, mul_one]
    · show diagPerm (negOne * _) = σ
      rw [map_mul, diagPerm_negOne, one_mul]
      exact hk

@[expose] noncomputable def monomialEquiv : monomial ≃* ℤˣ × Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective theta ⟨theta_injective, theta_surjective⟩

theorem monomialEquiv_apply (g : monomial) : monomialEquiv g = (signChar g, diagPerm g) := rfl

theorem card_monomial : Nat.card monomial = 48 := by
  rw [Nat.card_congr monomialEquiv.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, Fintype.card_units_int]
  rfl

theorem negOne_eq : ((negOne : monomial) : GL (Fin 3) (ZMod 3)) = d0 * d1 * d2 := by
  decide +kernel

theorem closure_monoRefl : Subgroup.closure monoRefl = monomial := by
  apply le_antisymm ((Subgroup.closure_le _).mpr monoRefl_subset_monomial)
  intro g hg
  obtain ⟨k, hk⟩ := swapReflPerm_surjective (diagPerm ⟨g, hg⟩)
  have hkK : (k : GL (Fin 3) (ZMod 3)) ∈ Subgroup.closure monoRefl :=
    Subgroup.closure_mono Set.subset_union_right k.2
  have hker : diagPerm (⟨g, hg⟩ * (Subgroup.inclusion swapRefl_le k)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    exact mul_inv_eq_one.mpr hk.symm
  have hmem : ∀ x : monomial, (x : GL (Fin 3) (ZMod 3)) ∈ Subgroup.closure monoRefl →
      ⟨g, hg⟩ * (Subgroup.inclusion swapRefl_le k)⁻¹ = x → g ∈ Subgroup.closure monoRefl := by
    intro x hx h
    have h' := congrArg Subtype.val (eq_mul_of_mul_inv_eq h)
    rw [Subgroup.coe_mul, Subgroup.coe_inclusion] at h'
    rw [show g = (x : GL (Fin 3) (ZMod 3)) * k from h']
    exact mul_mem hx hkK
  rcases eq_one_or_eq_negOne hker with h | h
  · exact hmem 1 (one_mem _) h
  · refine hmem negOne ?_ h
    rw [negOne_eq]
    have hd : ∀ x ∈ diagRefl, x ∈ Subgroup.closure monoRefl := fun x hx =>
      Subgroup.subset_closure (Or.inl hx)
    exact mul_mem (mul_mem (hd _ (by simp [diagRefl])) (hd _ (by simp [diagRefl])))
      (hd _ (by simp [diagRefl]))

theorem perm_pow_twelve : ∀ σ : Equiv.Perm (Fin 4), σ ^ 12 = 1 := by decide +kernel

theorem units_int_pow_twelve (u : ℤˣ) : u ^ 12 = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem pow_twelve_eq_one {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) : g ^ 12 = 1 := by
  have h : (⟨g, hg⟩ : monomial) ^ 12 = 1 := theta_injective (by
    rw [map_pow, map_one]
    exact Prod.ext (by rw [Prod.pow_fst, Prod.fst_one]; exact units_int_pow_twelve _)
      (by rw [Prod.pow_snd, Prod.snd_one]; exact perm_pow_twelve _))
  have := congrArg Subtype.val h
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at this

theorem perm_no_quaternion : ∀ σ τ : Equiv.Perm (Fin 4), σ ^ 2 ≠ 1 → τ ^ 2 = σ ^ 2 →
    τ * σ ≠ σ⁻¹ * τ := by
  decide +kernel

theorem no_quaternion_pair {x y : GL (Fin 3) (ZMod 3)} (hx : x ∈ monomial) (hy : y ∈ monomial)
    (hx2 : x ^ 2 ≠ 1) (hyx : y ^ 2 = x ^ 2) (hconj : y * x * y⁻¹ = x⁻¹) : False := by
  set X : monomial := ⟨x, hx⟩
  set Y : monomial := ⟨y, hy⟩
  have hX2 : diagPerm X ^ 2 ≠ 1 := by
    intro h
    rw [← map_pow] at h
    rcases eq_one_or_eq_negOne h with h' | h'
    · exact hx2 (by simpa [X] using congrArg Subtype.val h')
    · have := congrArg signChar h'
      rw [map_pow, signChar_negOne, Int.units_sq] at this
      exact absurd this (by decide)
  have hYX2 : diagPerm Y ^ 2 = diagPerm X ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
    exact Subtype.ext (by simpa [X, Y] using hyx)
  apply perm_no_quaternion _ _ hX2 hYX2
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [X, Y, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hconj]
  group

theorem quaternion_facts : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 ∧
    (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 1 ^ 2 ∧
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
      (QuaternionGroup.a 1 : QuaternionGroup 2)⁻¹ := by
  decide +kernel

theorem not_quaternion_le (φ : QuaternionGroup 2 →* GL (Fin 3) (ZMod 3))
    (hφ : Function.Injective φ) : ¬ φ.range ≤ monomial := by
  intro h
  obtain ⟨h1, h2, h3⟩ := quaternion_facts
  refine no_quaternion_pair (x := φ (QuaternionGroup.a 1)) (y := φ (QuaternionGroup.xa 0))
    (h ⟨_, rfl⟩) (h ⟨_, rfl⟩) ?_ ?_ ?_
  · rw [← map_pow, ← map_one φ]
    exact fun h' => h1 (hφ h')
  · rw [← map_pow, ← map_pow, h2]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, h3]

theorem swap_mul_swap : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b ∨
      (Equiv.swap a b * Equiv.swap c d) ^ 3 = 1 := by
  decide +kernel

theorem swapRefl_commute_or_cube {x y : GL (Fin 3) (ZMod 3)} (hx : x ∈ swapRefl)
    (hy : y ∈ swapRefl) : x * y = y * x ∨ (x * y) ^ 3 = 1 := by
  obtain ⟨a, b, hab, hxab⟩ := isSwap_swapReflPerm hx
  obtain ⟨c, d, hcd, hycd⟩ := isSwap_swapReflPerm hy
  set X : Subgroup.closure swapRefl := ⟨x, mem_closure_of_mem hx⟩
  set Y : Subgroup.closure swapRefl := ⟨y, mem_closure_of_mem hy⟩
  rcases swap_mul_swap a b c d hab hcd with h | h
  · left
    have : X * Y = Y * X := swapReflPerm_injective (by rw [map_mul, map_mul, hxab, hycd, h])
    exact congrArg Subtype.val this
  · right
    have : (X * Y) ^ 3 = 1 := swapReflPerm_injective (by rw [map_pow, map_mul, hxab, hycd, h,
      map_one])
    simpa [X, Y] using congrArg Subtype.val this

@[expose] def thetaRefl : List (ℤˣ × Equiv.Perm (Fin 4)) :=
  [(-1, Equiv.swap 0 3 * Equiv.swap 1 2), (-1, Equiv.swap 0 2 * Equiv.swap 1 3),
   (-1, Equiv.swap 0 1 * Equiv.swap 2 3), (1, Equiv.swap 2 3), (1, Equiv.swap 0 1),
   (1, Equiv.swap 1 2), (1, Equiv.swap 0 3), (1, Equiv.swap 1 3), (1, Equiv.swap 0 2)]

theorem theta_eq_of (x : GL (Fin 3) (ZMod 3)) (hx : x ∈ monomial) (u : ℤˣ)
    (σ : Equiv.Perm (Fin 4)) (hu : toSign (signProd (x : Mat3)) = u)
    (hσ : ∀ i, diagMap (x : Mat3) i = σ i) : theta ⟨x, hx⟩ = (u, σ) :=
  Prod.ext hu (Equiv.ext hσ)

theorem theta_mem_thetaRefl {x : GL (Fin 3) (ZMod 3)} (hx : x ∈ monoRefl) :
    theta ⟨x, monoRefl_subset_monomial hx⟩ ∈ thetaRefl := by
  have h := monoRefl_subset_monomial hx
  revert h
  simp only [monoRefl, diagRefl, swapRefl, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl) <;> intro h
  · rw [theta_eq_of _ h (-1) (Equiv.swap 0 3 * Equiv.swap 1 2) (by decide +kernel)
      (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h (-1) (Equiv.swap 0 2 * Equiv.swap 1 3) (by decide +kernel)
      (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h (-1) (Equiv.swap 0 1 * Equiv.swap 2 3) (by decide +kernel)
      (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 2 3) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 0 1) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 1 2) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 0 3) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 1 3) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · rw [theta_eq_of _ h 1 (Equiv.swap 0 2) (by decide +kernel) (by decide +kernel)]
    decide +kernel

theorem thetaRefl_mul : ∀ a ∈ thetaRefl, ∀ b ∈ thetaRefl,
    a * b = b * a ∨ (a * b) ^ 3 = 1 ∨ (a * b) ^ 4 = 1 := by
  decide +kernel

theorem monoRefl_commute_or_cube_or_four {x y : GL (Fin 3) (ZMod 3)} (hx : x ∈ monoRefl)
    (hy : y ∈ monoRefl) : x * y = y * x ∨ (x * y) ^ 3 = 1 ∨ (x * y) ^ 4 = 1 := by
  set X : monomial := ⟨x, monoRefl_subset_monomial hx⟩
  set Y : monomial := ⟨y, monoRefl_subset_monomial hy⟩
  rcases thetaRefl_mul _ (theta_mem_thetaRefl hx) _ (theta_mem_thetaRefl hy) with h | h | h
  · left
    have : X * Y = Y * X := theta_injective (by rw [map_mul, map_mul, h])
    exact congrArg Subtype.val this
  · right; left
    have : (X * Y) ^ 3 = 1 := theta_injective (by rw [map_pow, map_mul, h, map_one])
    simpa [X, Y] using congrArg Subtype.val this
  · right; right
    have : (X * Y) ^ 4 = 1 := theta_injective (by rw [map_pow, map_mul, h, map_one])
    simpa [X, Y] using congrArg Subtype.val this

theorem exists_swapRefl_mul_order_four {s : GL (Fin 3) (ZMod 3)} (hs : s ∈ diagRefl) :
    ∃ r ∈ swapRefl, (s * r) ^ 2 ≠ 1 ∧ (s * r) ^ 4 = 1 := by
  simp only [diagRefl, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl
  · exact ⟨p01, by simp [swapRefl], by decide +kernel, by decide +kernel⟩
  · exact ⟨p01, by simp [swapRefl], by decide +kernel, by decide +kernel⟩
  · exact ⟨p12, by simp [swapRefl], by decide +kernel, by decide +kernel⟩

end CFSG.RankThree.PartTwo.KFacts.KP14
