module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Factor

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

@[expose] def relabelPerm (a b c d : Fin 5) : Perm (Fin 5) :=
  swap ((swap ((swap (swap a 0 b) 1 * swap a 0) c) 2 * (swap (swap a 0 b) 1 * swap a 0)) d) 3 *
    (swap ((swap (swap a 0 b) 1 * swap a 0) c) 2 * (swap (swap a 0 b) 1 * swap a 0))

theorem relabelPerm_spec : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    relabelPerm a b c d a = 0 ∧ relabelPerm a b c d b = 1 ∧ relabelPerm a b c d c = 2 ∧
      relabelPerm a b c d d = 3 := by
  decide +kernel

theorem disjoint_of_commute_swap : ∀ a b c d : Fin 5, a ≠ b → c ≠ d → swap a b ≠ swap c d →
    swap a b * swap c d = swap c d * swap a b → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  decide +kernel

@[expose] def vactEquiv (π : Perm (Fin 5)) : evenWeight 5 ≃+ evenWeight 5 where
  toFun := vact π
  invFun := vact π⁻¹
  left_inv x := by rw [← vact_mul, inv_mul_cancel, vact_one]
  right_inv x := by rw [← vact_mul, mul_inv_cancel, vact_one]
  map_add' := vact_add π

theorem coe_vactEquiv (π : Perm (Fin 5)) (x : evenWeight 5) :
    ((vactEquiv π x : evenWeight 5) : Fin 5 → ZMod 2) = pact π x := rfl

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}

theorem relabel_equivariant {θ : ↥K ≃* Perm (Fin 5)}
    {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    (π : Perm (Fin 5)) :
    ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd ((β.trans (vactEquiv π).toMultiplicative) ⟨(h : MulAut W) u, hu⟩) :
        evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd ((β.trans (vactEquiv π).toMultiplicative) u) : evenWeight 5) :
          Fin 5 → ZMod 2) (((θ.trans (MulAut.conj π)) h)⁻¹ i) := by
  intro h u hu i
  simp only [MulEquiv.trans_apply, AddEquiv.toMultiplicative_apply_apply, toAdd_ofAdd,
    coe_vactEquiv, pact, MulAut.conj_apply, mul_inv_rev, inv_inv, Perm.mul_apply]
  rw [show π⁻¹ (π ((θ h)⁻¹ (π⁻¹ i))) = (θ h)⁻¹ (π⁻¹ i) from π.symm_apply_apply _]
  exact hβ h u hu _

theorem exists_swap_pair [Finite W] (θ : ↥K ≃* Perm (Fin 5)) {P X : Subgroup (MulAut W)}
    (θ₀ : ↥K ≃* Perm (Fin 5)) (hP4 : Nat.card ↥P = 4)
    (hP : P = Subgroup.closure {x | ∃ hx : x ∈ K, x ∈ X ∧ (θ₀ ⟨x, hx⟩).IsSwap}) :
    ∃ (x₁ x₂ : MulAut W) (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K) (a b c d : Fin 5),
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      θ ⟨x₁, hx₁⟩ = swap a b ∧ θ ⟨x₂, hx₂⟩ = swap c d ∧
      ∀ g, g ∈ P ↔ g = 1 ∨ g = x₁ ∨ g = x₂ ∨ g = x₁ * x₂ := by
  classical
  set Sw := {x | ∃ hx : x ∈ K, x ∈ X ∧ (θ₀ ⟨x, hx⟩).IsSwap}
  have hSwP : Sw ⊆ P := fun x hx => hP ▸ Subgroup.subset_closure hx
  have hθswap : ∀ x ∈ Sw, ∃ hx : x ∈ K, (θ ⟨x, hx⟩).IsSwap := by
    rintro x ⟨hx, -, hs⟩
    refine ⟨hx, ?_⟩
    have h1 := isSwap_map_mulEquiv (θ₀.symm.trans θ) hs
    simpa using h1
  have hinv : ∀ x ∈ Sw, x ≠ 1 ∧ x * x = 1 := by
    intro x hxS
    obtain ⟨hx, a, b, hab, e⟩ := hθswap x hxS
    refine ⟨fun h1 => ?_, ?_⟩
    · have h2 : θ ⟨x, hx⟩ = 1 := by
        rw [show (⟨x, hx⟩ : ↥K) = 1 from Subtype.ext h1, map_one]
      rw [h2] at e
      exact hab (by simpa using congrArg (fun σ : Perm (Fin 5) => σ a) e)
    · have h2 : θ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by rw [map_mul, e, swap_mul_self]
      have h3 := θ.injective (h2.trans (map_one θ).symm)
      exact congrArg Subtype.val h3
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ : ∃ x₁ ∈ Sw, ∃ x₂ ∈ Sw, x₁ ≠ x₂ := by
    by_contra hcon
    push Not at hcon
    rcases Set.eq_empty_or_nonempty Sw with hSw | ⟨x, hx⟩
    · rw [hSw, Subgroup.closure_empty] at hP
      rw [hP, Subgroup.card_bot] at hP4
      omega
    · have hle : P ≤ Subgroup.zpowers x := by
        rw [hP, Subgroup.closure_le]
        intro y hy
        rw [hcon y hy x hx]
        exact Subgroup.mem_zpowers x
      have hc : Nat.card ↥(Subgroup.zpowers x) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact (hinv x hx).2)
      have := Subgroup.card_le_of_le hle
      omega
  obtain ⟨hx₁K, a, b, hab, e₁⟩ := hθswap x₁ hx₁
  obtain ⟨hx₂K, c, d, hcd, e₂⟩ := hθswap x₂ hx₂
  have hcommP : x₁ * x₂ = x₂ * x₁ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥P)
      (by rw [hP4]; norm_num)
    have h2 : (⟨x₁, hSwP hx₁⟩ : ↥P) * ⟨x₂, hSwP hx₂⟩ = ⟨x₂, hSwP hx₂⟩ * ⟨x₁, hSwP hx₁⟩ :=
      h1.is_comm.comm _ _
    exact congrArg Subtype.val h2
  have hne' : swap a b ≠ swap c d := by
    rw [← e₁, ← e₂]
    intro h
    exact hne (congrArg Subtype.val (θ.injective h))
  have hcomm' : swap a b * swap c d = swap c d * swap a b := by
    rw [← e₁, ← e₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcommP
  obtain ⟨hac, had, hbc, hbd⟩ := disjoint_of_commute_swap a b c d hab hcd hne' hcomm'
  refine ⟨x₁, x₂, hx₁K, hx₂K, a, b, c, d, hab, hac, had, hbc, hbd, hcd, e₁, e₂, fun g => ?_⟩
  have h1 := (hinv x₁ hx₁).1
  have h2 := (hinv x₂ hx₂).1
  have h12 : x₁ * x₂ ≠ 1 := fun h => hne (by
    calc x₁ = x₁ * (x₂ * x₂) := by rw [(hinv x₂ hx₂).2, mul_one]
      _ = (x₁ * x₂) * x₂ := by group
      _ = x₂ := by rw [h, one_mul])
  have h13 : x₁ * x₂ ≠ x₁ := fun h => h2 (by simpa using h)
  have h23 : x₁ * x₂ ≠ x₂ := fun h => h1 (by simpa using h)
  set F : Finset (MulAut W) := {1, x₁, x₂, x₁ * x₂}
  have hF : F.card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.symm, h2.symm, h12.symm]),
      Finset.card_insert_of_notMem (by simp [hne, h13.symm]),
      Finset.card_insert_of_notMem (by simp [h23.symm]), Finset.card_singleton]
  have hFP : (F : Set (MulAut W)) ⊆ P := by
    intro y hy
    simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact P.one_mem
    · exact hSwP hx₁
    · exact hSwP hx₂
    · exact P.mul_mem (hSwP hx₁) (hSwP hx₂)
  have heqF : (P : Set (MulAut W)) = F := by
    symm
    refine Set.eq_of_subset_of_ncard_le hFP ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hF, ← hP4, ← Nat.card_coe_set_eq]
    rfl
  rw [← SetLike.mem_coe, heqF]
  simp [F]

theorem exists_normalized [Finite W] {θ : ↥K ≃* Perm (Fin 5)}
    {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    {P X : Subgroup (MulAut W)} (θ₀ : ↥K ≃* Perm (Fin 5)) (hP4 : Nat.card ↥P = 4)
    (hP : P = Subgroup.closure {x | ∃ hx : x ∈ K, x ∈ X ∧ (θ₀ ⟨x, hx⟩).IsSwap}) :
    ∃ (θ' : ↥K ≃* Perm (Fin 5)) (β' : ↥(commV K) ≃* Multiplicative (evenWeight 5)),
      (∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
        ((Multiplicative.toAdd (β' ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
          ((Multiplicative.toAdd (β' u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ' h)⁻¹ i)) ∧
      ∀ g (hg : g ∈ K), g ∈ P ↔ θ' ⟨g, hg⟩ ∈ eFour := by
  obtain ⟨x₁, x₂, hx₁, hx₂, a, b, c, d, hab, hac, had, hbc, hbd, hcd, e₁, e₂, hmem⟩ :=
    exists_swap_pair θ θ₀ hP4 hP
  obtain ⟨hπa, hπb, hπc, hπd⟩ := relabelPerm_spec a b c d hab hac had hbc hbd hcd
  set π := relabelPerm a b c d
  set θ' := θ.trans (MulAut.conj π)
  refine ⟨θ', β.trans (vactEquiv π).toMultiplicative, relabel_equivariant hβ π, fun g hg => ?_⟩
  have k₁ : θ' ⟨x₁, hx₁⟩ = sA := by
    show π * θ ⟨x₁, hx₁⟩ * π⁻¹ = sA
    rw [e₁, ← swap_apply_apply, hπa, hπb]
    rfl
  have k₂ : θ' ⟨x₂, hx₂⟩ = sB := by
    show π * θ ⟨x₂, hx₂⟩ * π⁻¹ = sB
    rw [e₂, ← swap_apply_apply, hπc, hπd]
    rfl
  have k₃ : θ' ⟨x₁ * x₂, K.mul_mem hx₁ hx₂⟩ = sA * sB := by
    rw [← k₁, ← k₂, ← map_mul]
    rfl
  constructor
  · intro hgP
    rw [eFour_mem_iff]
    rcases (hmem g).mp hgP with rfl | rfl | rfl | rfl
    · left
      exact (congrArg θ' (Subtype.ext rfl : (⟨1, hg⟩ : ↥K) = 1)).trans (map_one θ')
    · right; left; exact k₁
    · right; right; left; exact k₂
    · right; right; right; exact k₃
  · intro hgE
    rw [hmem g]
    rcases (eFour_mem_iff _).mp hgE with h | h | h | h
    · left
      have := θ'.injective (h.trans (map_one θ').symm)
      exact congrArg Subtype.val this
    · right; left
      exact congrArg Subtype.val (θ'.injective (h.trans k₁.symm))
    · right; right; left
      exact congrArg Subtype.val (θ'.injective (h.trans k₂.symm))
    · right; right; right
      exact congrArg Subtype.val (θ'.injective (h.trans k₃.symm))

end CFSG.Quasithin.Vol2.Ch10.SecE
