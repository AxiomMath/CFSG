module

public import CFSG.Quasithin.H13.L32AL2w

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Quasithin.H.Om4 Matrix

variable {F : Type} [Field F]

structure L2Cfg (F : Type) [Field F] (Hs Ts Ls Rs O : Subgroup (MulAut (VM F)))
    (Vs : Subgroup (VM F)) (t : MulAut (VM F)) (a : VM F) : Prop where
  card : Nat.card F = 4
  hN : Hs ≤ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F)))
  hTH : Ts ≤ Hs
  hT2 : ∀ x ∈ Ts, ∃ k : ℕ, x ^ (2 ^ k) = 1
  hS0 : Ts ⊓ (rho (K := F)).range = sZero
  hTV : ∀ x ∈ Ts, ∀ v ∈ Vs, x v ∈ Vs
  hLK : Ls ≤ (rho (K := F)).range
  hLV : ∀ x ∈ Ls, ∀ v ∈ Vs, x v ∈ Vs
  hLT : Ts ≤ Subgroup.normalizer (Ls : Set (MulAut (VM F)))
  hL3 : ∃ y ∈ Ls, ∃ v ∈ Vs, y v ≠ v
  hOL : O ≤ Ls
  hO2 : ∀ x ∈ O, ∃ k : ℕ, x ^ (2 ^ k) = 1
  hLR : ∀ l ∈ Ls, ∀ r ∈ Rs, l * r * l⁻¹ * r⁻¹ ∈ O
  hNR : ∀ N : Subgroup (MulAut (VM F)), N ≤ Ls →
    Ls ≤ Subgroup.normalizer (N : Set (MulAut (VM F))) → (∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1) →
      N ≤ Rs
  hRT : Rs ≤ Ts
  hRidx0 : Rs.relIndex Ts ≠ 0
  hRidx : Rs.relIndex Ts ≤ 2
  hRn : Ls ⊔ Ts ≤ Subgroup.normalizer (Rs : Set (MulAut (VM F)))
  hRV : ∀ x ∈ Rs, ∀ v ∈ Vs, x v = v
  hVcard : Nat.card Vs = 4
  ht : t ∈ Rs
  ht2 : t * t = 1
  ht1 : t ≠ 1
  htc : Nat.card (commHom t).range ≤ 4
  ha : a ∈ (commHom t).range
  ha1 : a ≠ 1

theorem mul_mem_of_relIndex_le_two {G : Type*} [Group G] {R S : Subgroup G}
    (hR0 : R.relIndex S ≠ 0) (hR : R.relIndex S ≤ 2) {x y : G} (hx : x ∈ S) (hy : y ∈ S)
    (hxR : x ∉ R) (hyR : y ∉ R) : x * y ∈ R := by
  set K := R.subgroupOf S with hK
  have hK2 : K.index ≤ 2 := hR
  have h0 : K.index ≠ 0 := hR0
  have hxK : (⟨x, hx⟩ : S) ∉ K := fun h => hxR (Subgroup.mem_subgroupOf.mp h)
  have hyK : (⟨y, hy⟩ : S) ∉ K := fun h => hyR (Subgroup.mem_subgroupOf.mp h)
  have h2 : K.index = 2 := by
    rcases (by omega : K.index = 1 ∨ K.index = 2) with h | h
    · exact (hxK (by rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _)).elim
    · exact h
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    (iff_of_false hxK hyK)
  exact Subgroup.mem_subgroupOf.mp this

theorem sZero_sq [CharP F 2] {s : MulAut (VM F)} (hs : s ∈ sZero) : s * s = 1 := by
  obtain ⟨p, q, rfl⟩ := hs
  rw [← map_mul, Prod.mk_mul_mk, utS_mul, utS_mul, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, utS_zero, ← Prod.one_eq_mk, map_one]

theorem sZero_comm {s s' : MulAut (VM F)} (hs : s ∈ sZero) (hs' : s' ∈ sZero) :
    s * s' = s' * s := by
  obtain ⟨p, q, rfl⟩ := hs
  obtain ⟨p', q', rfl⟩ := hs'
  rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, utS_mul, utS_mul, utS_mul, utS_mul,
    add_comm p, add_comm q]

namespace L2Cfg

variable {Hs Ts Ls Rs O : Subgroup (MulAut (VM F))} {Vs : Subgroup (VM F)} {t : MulAut (VM F)}
  {a : VM F}

theorem sZero_le_ts (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : sZero ≤ Ts := by
  rw [← C.hS0]
  exact inf_le_left

theorem mem_gamma (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {x : MulAut (VM F)} (hx : x ∈ Ts) :
    x ∈ Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) :=
  C.hN (C.hTH hx)

variable [Finite F] [CharP F 2]

theorem exists_mem_left_right (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    (∃ p : F, p ≠ 0 ∧ rho (utS p, (1 : SpecialLinearGroup (Fin 2) F)) ∈ Rs) ∧
      ∃ q : F, q ≠ 0 ∧ rho ((1 : SpecialLinearGroup (Fin 2) F), utS q) ∈ Rs := by
  obtain ⟨ω, hω, -⟩ := exists_omega C.card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hω - h2)
  have hωω : ω * ω ≠ 0 := mul_ne_zero hω0 hω0
  have h1ω : (1 : F) + ω = ω * ω := by linear_combination -hω + (1 + ω) * h2
  have hRS : Rs.relIndex sZero ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right C.sZero_le_ts C.hRidx0).trans C.hRidx
  have hRS0 : Rs.relIndex sZero ≠ 0 :=
    mt (Subgroup.relIndex_eq_zero_of_le_right C.sZero_le_ts) C.hRidx0
  have hmem : ∀ p q : F, rho (utS p, utS q) ∈ sZero := fun p q => ⟨p, q, rfl⟩
  constructor
  · by_contra hall
    push Not at hall
    have h1 := hall 1 one_ne_zero
    have h2' := hall ω hω0
    have h3 := hall (ω * ω) hωω
    rw [← utS_zero] at h1 h2' h3
    apply h3
    have := mul_mem_of_relIndex_le_two hRS0 hRS (hmem 1 0) (hmem ω 0) h1 h2'
    rwa [← map_mul, Prod.mk_mul_mk, utS_mul, utS_mul, h1ω, add_zero] at this
  · by_contra hall
    push Not at hall
    have h1 := hall 1 one_ne_zero
    have h2' := hall ω hω0
    have h3 := hall (ω * ω) hωω
    rw [← utS_zero] at h1 h2' h3
    apply h3
    have := mul_mem_of_relIndex_le_two hRS0 hRS (hmem 0 1) (hmem 0 ω) h1 h2'
    rwa [← map_mul, Prod.mk_mul_mk, utS_mul, utS_mul, h1ω, add_zero] at this

theorem vs_iff (C : L2Cfg F Hs Ts Ls Rs O Vs t a) (v : VM F) :
    v ∈ Vs ↔ ∃ c : F, v = Multiplicative.ofAdd (c • matE) := by
  obtain ⟨⟨p, hp, hpR⟩, ⟨q, hq, hqR⟩⟩ := C.exists_mem_left_right
  have hsub : ∀ v ∈ Vs, ∃ c : F, v = Multiplicative.ofAdd (c • matE) := fun v hv => by
    have h1 := C.hRV _ hpR v hv
    have h2 := C.hRV _ hqR v hv
    rw [← ofAdd_toAdd v] at h1 h2
    exact ⟨_, by rw [← eq_smul_e11_of_fix hp hq h1 h2, ofAdd_toAdd]⟩
  constructor
  · exact hsub v
  · rintro ⟨c, rfl⟩
    set f : F → VM F := fun c => Multiplicative.ofAdd (c • matE) with hf
    have hfi : Function.Injective f := fun c c' h => by
      have h' : c • (matE : Matrix (Fin 2) (Fin 2) F) = c' • matE :=
        Multiplicative.ofAdd.injective h
      have := congrFun (congrFun h' 0) 0
      simpa [matE] using this
    have hS : (Vs : Set (VM F)) ⊆ Set.range f := fun v hv => by
      obtain ⟨c, rfl⟩ := hsub v hv
      exact ⟨c, rfl⟩
    have hcard : (Set.range f).ncard ≤ (Vs : Set (VM F)).ncard := by
      rw [Set.ncard_range_of_injective hfi, C.card, ← Nat.card_coe_set_eq]
      exact le_of_eq C.hVcard.symm
    have heq := Set.eq_of_subset_of_ncard_le hS hcard (Set.toFinite _)
    have : f c ∈ (Vs : Set (VM F)) := by
      rw [heq]
      exact ⟨c, rfl⟩
    exact this

theorem e11_mem (C : L2Cfg F Hs Ts Ls Rs O Vs t a) (c : F) :
    Multiplicative.ofAdd (c • matE) ∈ Vs := (C.vs_iff _).mpr ⟨c, rfl⟩

theorem exists_A (C : L2Cfg F Hs Ts Ls Rs O Vs t a) :
    ∃ A : GL (Fin 2) F, IsUT A ∧ t = lr A A⁻¹ * trM ∧
      ∃ c : F, c ≠ 0 ∧ a = Multiplicative.ofAdd (c • ((A : Matrix (Fin 2) (Fin 2) F) * matJ)) := by
  rcases inv_cases C.card (C.mem_gamma (C.hRT C.ht)) C.ht2 C.ht1 with h | ⟨A, hA⟩
  · have := C.htc
    omega
  · obtain ⟨μ, hμ⟩ := (C.vs_iff _).mp (C.hTV _ (C.hRT C.ht) _ (C.e11_mem 1))
    have hUT : IsUT A := by
      have e := congrArg Multiplicative.toAdd hμ
      rw [hA, MulAut.mul_apply, toAdd_lr, toAdd_trM, toAdd_ofAdd, toAdd_ofAdd, one_smul] at e
      have hEt : (matE : Matrix (Fin 2) (Fin 2) F)ᵀ = !![1, 0; 0, 0] := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      rw [hEt] at e
      exact (isUT_of_mul_e11 (B := A⁻¹) e).1
    obtain ⟨c, hc⟩ := (mem_range_commHom_iff A a).mp (hA ▸ C.ha)
    refine ⟨A, hUT, hA, c, ?_, hc⟩
    rintro rfl
    apply C.ha1
    rw [hc, zero_smul]
    rfl

omit [Finite F] in
theorem t_fix (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : t a = a := by
  have hV : ∀ w : VM F, w * w = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  exact mem_ker_commHom.mp (range_le_ker hV C.ht2 C.ha)

theorem isSemi_one_of_mem (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {r : MulAut (VM F)} (hr : r ∈ Rs) :
    IsSemi r 1 := by
  obtain ⟨τ, hτ⟩ := isSemi_of_mem_normalizer (by rw [C.card]) (C.mem_gamma (C.hRT hr))
  have hτ1 : τ = 1 := by
    refine RingEquiv.ext fun c => ?_
    have e1 := C.hRV r hr _ (C.e11_mem c)
    have e2 := C.hRV r hr _ (C.e11_mem 1)
    have e3 := hτ c matE
    rw [one_smul] at e2
    rw [e1, toAdd_ofAdd, e2, toAdd_ofAdd] at e3
    have := congrFun (congrFun e3 0) 0
    simpa [matE] using this.symm
  exact hτ1 ▸ hτ

theorem isSemi_t (C : L2Cfg F Hs Ts Ls Rs O Vs t a) : IsSemi t 1 := C.isSemi_one_of_mem C.ht

theorem lin_cases (C : L2Cfg F Hs Ts Ls Rs O Vs t a) {x : MulAut (VM F)} (hx : x ∈ Ts)
    (hlin : IsSemi x 1) : x ∈ sZero ∨ x * t ∈ sZero := by
  obtain ⟨A, -, hA, -⟩ := C.exists_A
  have hrange : ∀ y : MulAut (VM F), y ∈ Ts → IsNS y → IsSemi y 1 → y ∈ sZero := by
    intro y hy hNS hy1
    obtain ⟨P, Q, τ, h⟩ := hNS
    have hτ : τ = 1 := (show IsSemi y τ from h ▸ isSemi_lr_frM P Q τ).eq hy1
    subst hτ
    rw [frM_one, mul_one] at h
    obtain ⟨k, hk⟩ := C.hT2 y hy
    have hr : y ∈ (rho (K := F)).range := by
      rw [h] at hk ⊢
      exact mem_range_of_pow C.card hk
    rw [← C.hS0]
    exact ⟨hy, hr⟩
  obtain ⟨P, Q, τ, h | h⟩ := exists_eq_of_mem_normalizer (by rw [C.card]) (C.mem_gamma hx)
  · exact Or.inl (hrange x hx ⟨P, Q, τ, h⟩ hlin)
  · right
    refine hrange _ (Ts.mul_mem hx (C.hRT C.ht)) ?_ ?_
    · rw [h, hA]
      exact isNS_swap_mul A P Q τ
    · have := hlin.mul C.isSemi_t
      rwa [mul_one] at this

end L2Cfg

end CFSG.Quasithin.H13.L32A.L2
