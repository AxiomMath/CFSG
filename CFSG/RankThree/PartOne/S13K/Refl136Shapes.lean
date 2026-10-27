module

public import CFSG.RankThree.PartOne.S13K.Sp6Four

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def wvec (a b : Fin 3) (s : Bool) (z : (Qext K)ˣ) : Fin 3 → (Qext K)ˣ :=
  fun j => if j = a then z else if j = b then (if s then z else z⁻¹) else 1

theorem wvec_pow {z : (Qext K)ˣ} (hz : z ^ p = 1) (a b : Fin 3) (s : Bool) (j : Fin 3) :
    wvec a b s z j ^ p = 1 := by
  unfold wvec
  by_cases h1 : j = a
  · simp [h1, hz]
  · by_cases h2 : j = b
    · cases s <;> simp [h2, hz, inv_pow]
    · simp [h1, h2]

theorem sact_D_apply {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (s : Bool)
    (x : Fin 3 → (Qext K)ˣ) :
    sact (Equiv.swap a b) (fun j => if j = c then false else s) x =
      fun j => if j = a then (if s then (x b)⁻¹ else x b)
        else if j = b then (if s then (x a)⁻¹ else x a) else x c := by
  funext j
  by_cases h1 : j = a
  · subst h1
    simp [sact_apply, hcb.symm, Equiv.swap_apply_left]
  · by_cases h2 : j = b
    · subst h2
      simp [sact_apply, hca.symm, h1, Equiv.swap_apply_right]
    · have hjc : j = c := by
        have : ∀ j : Fin 3, ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → j ≠ a → j ≠ b → j = c := by
          decide +kernel
        exact this j a b c hab hca hcb h1 h2
      subst hjc
      simp [sact_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne hca hcb]

theorem sact_D_sact_D {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (s : Bool)
    (x : Fin 3 → (Qext K)ˣ) :
    sact (Equiv.swap a b) (fun j => if j = c then false else s)
      (sact (Equiv.swap a b) (fun j => if j = c then false else s) x) = x := by
  rw [sact_D_apply hab hca hcb s x]
  rw [sact_D_apply hab hca hcb s]
  funext j
  by_cases h1 : j = a
  · subst h1
    cases s <;> simp [hab.symm]
  · by_cases h2 : j = b
    · subst h2
      cases s <;> simp [hab.symm]
    · have hjc : j = c := by
        have : ∀ j : Fin 3, ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → j ≠ a → j ≠ b → j = c := by
          decide +kernel
        exact this j a b c hab hca hcb h1 h2
      subst hjc
      simp [h1, h2]

@[expose] noncomputable def zfun (a b : Fin 3) (s : Bool) (x : Fin 3 → (Qext K)ˣ) : (Qext K)ˣ :=
  if s then (x a * x b)⁻¹ else x b * (x a)⁻¹

theorem sact_D_mul_inv {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (s : Bool)
    (x : Fin 3 → (Qext K)ˣ) :
    sact (Equiv.swap a b) (fun j => if j = c then false else s) x * x⁻¹ =
      wvec a b s (zfun a b s x) := by
  rw [sact_D_apply hab hca hcb s x]
  funext j
  by_cases h1 : j = a
  · subst h1
    cases s <;> simp [wvec, zfun, mul_comm, mul_inv_rev]
  · by_cases h2 : j = b
    · subst h2
      cases s <;> simp [wvec, zfun, h1, mul_comm, mul_inv_rev]
    · have hjc : j = c := by
        have : ∀ j : Fin 3, ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → j ≠ a → j ≠ b → j = c := by
          decide +kernel
        exact this j a b c hab hca hcb h1 h2
      subst hjc
      simp [wvec, h1, h2]

theorem wvec_pow_eq {z : (Qext K)ˣ} (a b : Fin 3) (s : Bool) (n : ℕ) :
    wvec a b s (z ^ n) = (wvec a b s z) ^ n := by
  funext j
  unfold wvec
  by_cases h1 : j = a
  · simp [h1]
  · by_cases h2 : j = b
    · cases s <;> simp [h2, inv_pow]
    · simp [h1, h2]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

theorem autMoved_tSgn_D {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {a b c : Fin 3}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (s : Bool) :
    autMoved E (C.tSgn (Equiv.swap a b) (fun j => if j = c then false else s)) =
      Subgroup.zpowers (C.eT (wvec a b s ζ) (wvec_pow hζ.pow_eq_one a b s)) := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  set t := C.tSgn (Equiv.swap a b) (fun j => if j = c then false else s) with ht
  set m := C.eT (wvec a b s ζ) (wvec_pow hζp a b s) with hm
  have hz : ∀ x : Fin 3 → (Qext K)ˣ, (∀ j, x j ^ p = 1) → zfun a b s x ^ p = 1 := by
    intro x hx
    unfold zfun
    cases s <;> simp [mul_pow, inv_pow, hx a, hx b]
  have hgen : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ j, x j ^ p = 1) (k : ℤ),
      t (C.eT x hx * C.cE ^ k) * (C.eT x hx * C.cE ^ k)⁻¹ =
        C.eT (wvec a b s (zfun a b s x)) (wvec_pow (hz x hx) a b s) := by
    intro x hx k
    rw [ht, C.tSgn_apply_decomp]
    have h1 : C.eT (sact (Equiv.swap a b) (fun j => if j = c then false else s) x) (sact_pow hx) *
        C.cE ^ k * (C.eT x hx * C.cE ^ k)⁻¹ =
        C.eT (sact (Equiv.swap a b) (fun j => if j = c then false else s) x) (sact_pow hx) *
          (C.eT x hx)⁻¹ := by
      group
    rw [h1, C.eT_inv, C.eT_mul]
    exact C.eT_congr (sact_D_mul_inv hab hca hcb s x)
  apply le_antisymm
  · unfold autMoved
    rw [Subgroup.closure_le]
    rintro _ ⟨e, rfl⟩
    obtain ⟨x, hx, k, rfl⟩ := C.exists_decomp_eT e
    show t (C.eT x hx * C.cE ^ k) * (C.eT x hx * C.cE ^ k)⁻¹ ∈ Subgroup.zpowers m
    rw [hgen x hx k]
    obtain ⟨n, hn⟩ := exists_pow_eq hp hζ (hz x hx)
    have hmn : C.eT (wvec a b s (zfun a b s x)) (wvec_pow (hz x hx) a b s) = m ^ n := by
      rw [hm, C.eT_pow]
      refine C.eT_congr ?_
      rw [← hn]
      exact wvec_pow_eq a b s n
    rw [hmn]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers m) n
  · rw [Subgroup.zpowers_le]
    set x₀ : Fin 3 → (Qext K)ˣ := fun j => if j = b then (if s then ζ⁻¹ else ζ) else 1 with hx₀
    have hx₀p : ∀ j, x₀ j ^ p = 1 := by
      intro j
      by_cases hj : j = b
      · cases s <;> simp [hx₀, hj, hζp, inv_pow]
      · simp [hx₀, hj]
    have hzx : zfun a b s x₀ = ζ := by
      cases s <;> simp [zfun, hx₀, hab]
    have h1 := hgen x₀ hx₀p 0
    have hmem : t (C.eT x₀ hx₀p * C.cE ^ (0 : ℤ)) * (C.eT x₀ hx₀p * C.cE ^ (0 : ℤ))⁻¹ ∈
        autMoved E t := Subgroup.subset_closure ⟨_, rfl⟩
    rw [h1] at hmem
    have hfun : wvec a b s (zfun a b s x₀) = wvec a b s ζ := by rw [hzx]
    rw [C.eT_congr hfun] at hmem
    exact hmem

theorem isAutReflection_tSgn_D {a b c : Fin 3} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (s : Bool) :
    IsAutReflection p E (C.tSgn (Equiv.swap a b) (fun j => if j = c then false else s)) := by
  have hp : p.Prime := C.h.prime
  have h5 : 5 ≤ p := Sec12Three.five_le C.h
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp C.hp2 C.hpq'
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := zeta_ne_one hζ h5
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsq : C.tSgn (Equiv.swap a b) (fun j => if j = c then false else s) ^ 2 = 1 := by
      rw [sq]
      exact C.tSgn_sq_eq_one (fun x => sact_D_sact_D hab hca hcb s x)
    refine orderOf_eq_prime hsq (C.tSgn_ne_one ?_)
    set x₀ : Fin 3 → (Qext K)ˣ := fun j => if j = b then (if s then ζ⁻¹ else ζ) else 1 with hx₀
    have hx₀p : ∀ j, x₀ j ^ p = 1 := by
      intro j
      by_cases hj : j = b
      · cases s <;> simp [hx₀, hj, hζp, inv_pow]
      · simp [hx₀, hj]
    refine ⟨x₀, hx₀p, fun h => ?_⟩
    have h2 := sact_D_mul_inv hab hca hcb s x₀
    rw [h, mul_inv_cancel] at h2
    have h3 := congrFun h2 a
    have hzx : zfun a b s x₀ = ζ := by
      cases s <;> simp [zfun, hx₀, hab]
    simp only [wvec, hzx, ite_true, Pi.one_apply] at h3
    exact hζ1 h3.symm
  · rw [C.autMoved_tSgn_D hζ hp hab hca hcb s, Nat.card_zpowers]
    have hm1 : (C.eT (wvec a b s ζ) (wvec_pow hζp a b s)) ^ p = 1 := by
      rw [C.eT_pow]
      have h1 : (wvec a b s ζ) ^ p = 1 := by
        funext j
        exact wvec_pow hζp a b s j
      exact (C.eT_congr h1).trans C.eT_one
    have hm2 : C.eT (wvec a b s ζ) (wvec_pow hζp a b s) ≠ 1 := by
      intro h
      have h' : C.eT (wvec a b s ζ) (wvec_pow hζp a b s) =
          C.eT (1 : Fin 3 → (Qext K)ˣ) (fun _ => one_pow _) := h.trans C.eT_one.symm
      have h3 := congrFun (C.eT_injective h') a
      simp only [wvec, ite_true, Pi.one_apply] at h3
      exact hζ1 h3
    exact orderOf_eq_prime hm1 hm2

theorem tSgn_mem_reflectionSet_of_shape (hF13 : Sec13Facts G p A c L E) {π : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → Bool} (hs : ReflShape π ε) : C.tSgn π ε ∈ reflectionSet p E := by
  rcases hs with ⟨rfl, i, hi, hj⟩ | ⟨a, b, c', hab, hca, hcb, rfl, hεab, hεc⟩
  · have hε : ε = fun j => decide (j = i) := by
      funext j
      by_cases h : j = i
      · subst h; simp [hi]
      · simp [h, hj j h]
    subst hε
    exact C.S_mem_reflectionSet hF13 i
  · have hε : ε = fun j => if j = c' then false else ε a := by
      funext j
      by_cases h : j = c'
      · simp [h, hεc]
      · have hj : j = a ∨ j = b := by
          have : ∀ j : Fin 3, ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → j ≠ c → j = a ∨ j = b := by
            decide +kernel
          exact this j a b c' hab hca hcb h
        rcases hj with rfl | rfl
        · simp [h]
        · simp [h, hεab]
    rw [hε]
    exact ⟨C.isAutReflection_tSgn_D hab hca hcb (ε a), L, hF13.inZeroStar,
      C.tSgn_mem_torusImage _ _⟩

end Sp6Ctx

end CFSG.RankThree.PartOne.S13K
