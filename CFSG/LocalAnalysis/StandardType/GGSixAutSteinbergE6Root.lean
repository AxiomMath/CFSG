module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Steinberg.Adjoint.CertE6Valid

public section

namespace CFSG.StandardType

namespace AutSt

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open scoped commutatorElement


variable {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]

theorem xPar_single_eq_adjX (i : Fin τ.rank) (c : K) :
    xPar F (Pi.single i 1) c = adjX τ K i c :=
  endHom_injective (by rw [xPar_simple, endHom_xElt]; rfl)

theorem xPar_neg_single_eq_adjY (i : Fin τ.rank) (c : K) :
    xPar F (-Pi.single i 1) c = adjY τ K i c :=
  endHom_injective (by rw [xPar_neg_simple, endHom_yElt]; rfl)

theorem xPar_one_ne_one {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : xPar F γ (1 : K) ≠ 1 := by
  intro h
  rw [← xPar_zero (F := F) γ] at h
  exact one_ne_zero (xPar_injective hγ h)

theorem xPar_one_inv [CharP K 2] (γ : Fin τ.rank → ℤ) : (xPar F γ (1 : K))⁻¹ = xPar F γ 1 := by
  rw [xPar_neg, CharTwo.neg_eq]

theorem reflect_single_of_cartan {i j : Fin τ.rank} (h : τ.cartan i j = -1) :
    reflect τ i (Pi.single j 1) = Pi.single j 1 + Pi.single i 1 := by
  rw [reflect, sum_cartan_mul_single, h, neg_one_smul, sub_neg_eq_add]

theorem reflect_single_add_of_cartan {i j : Fin τ.rank} (h : τ.cartan j i = -1) :
    reflect τ j (Pi.single j 1 + Pi.single i 1) = Pi.single i 1 := by
  have hs : ∑ l, τ.cartan j l * (Pi.single j 1 + Pi.single i 1 : Fin τ.rank → ℤ) l = 1 := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_cartan_mul_single,
      Tag.cartan_self, h]
    norm_num
  rw [reflect, hs, one_smul, add_sub_cancel_left]

theorem exists_conj_xPar_single_of_edge [Finite K] [CharP K 2] {i j : Fin τ.rank}
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) :
    ∃ g : adjointGroup τ K, g * xPar F (Pi.single j 1) 1 * g⁻¹ = xPar F (Pi.single i 1) 1 := by
  have h1 := weylElement_conj_mem (F := F) i (isRoot_single τ j)
    (xPar_mem (F := F) (isRoot_single τ j) (1 : K))
  have hr : IsRoot τ (Pi.single j 1 + Pi.single i 1) := by
    rw [← reflect_single_of_cartan hij]
    exact IsRoot.reflect i (isRoot_single τ j)
  rw [reflect_single_of_cartan hij] at h1
  have h2 := weylElement_conj_mem (F := F) j hr h1
  rw [reflect_single_add_of_cartan hji] at h2
  obtain ⟨c, hc⟩ := (mem_rootGroup_iff (isRoot_single τ i) _).1 h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [xPar_zero, eq_comm, conj_eq_one_iff, conj_eq_one_iff] at hc
    exact xPar_one_ne_one (isRoot_single τ j) hc
  obtain ⟨g, hg⟩ := exists_conj_xPar_single_eq_one (F := F) i hc0
  refine ⟨g * (CFSG.LieType.Chevalley.weylElement τ K j *
    CFSG.LieType.Chevalley.weylElement τ K i), ?_⟩
  rw [← hg, hc]
  group

abbrev e6Node (i : Fin 6) : Fin Tag.E6.rank := i

theorem exists_conj_xPar_single_one_E6 [Finite K] [CharP K 2] {F : RootOperatorFamily .E6}
    (j : Fin Tag.E6.rank) :
    ∃ g : adjointGroup .E6 K, g * xPar F (Pi.single j 1) 1 * g⁻¹ =
      xPar F (Pi.single (e6Node 1) 1) 1 := by
  have e : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j = -1 → Tag.E6.cartan j i = -1 →
      ∃ g : adjointGroup .E6 K, g * xPar F (Pi.single j 1) 1 * g⁻¹ = xPar F (Pi.single i 1) 1 :=
    fun i j h1 h2 => exists_conj_xPar_single_of_edge h1 h2
  have tr : ∀ {x y z : adjointGroup .E6 K}, (∃ g, g * x * g⁻¹ = y) → (∃ g, g * y * g⁻¹ = z) →
      ∃ g, g * x * g⁻¹ = z := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨h * g, by group⟩
  have h31 := e (e6Node 1) (e6Node 3) (by decide) (by decide)
  have h23 := e (e6Node 3) (e6Node 2) (by decide) (by decide)
  have h43 := e (e6Node 3) (e6Node 4) (by decide) (by decide)
  have h02 := e (e6Node 2) (e6Node 0) (by decide) (by decide)
  have h54 := e (e6Node 4) (e6Node 5) (by decide) (by decide)
  fin_cases j
  · exact tr h02 (tr h23 h31)
  · exact ⟨1, by rw [one_mul, inv_one, mul_one]; rfl⟩
  · exact tr h23 h31
  · exact h31
  · exact tr h43 h31
  · exact tr h54 (tr h43 h31)

theorem exists_conj_one_E6 [Finite K] [CharP K 2] {F : RootOperatorFamily .E6}
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) {z : adjointGroup .E6 K}
    (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) :
    ∃ g : adjointGroup .E6 K, g * z * g⁻¹ = xPar F (Pi.single (e6Node 1) 1) 1 := by
  obtain ⟨g, j, hg⟩ := exists_conj_xPar_single hγ hz hz1
  obtain ⟨h, hh⟩ := exists_conj_xPar_single_one_E6 (K := K) (F := F) j
  exact ⟨h * g, by rw [← hh, ← hg]; group⟩

theorem commute_xPar_single_neg_single {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ)
    {j k : Fin τ.rank} (hjk : j ≠ k) (c d : K) :
    Commute (xPar F (Pi.single j 1) c) (xPar F (-Pi.single k 1) d) := by
  have hne : (Pi.single j 1 + -Pi.single k 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
    have := congrFun h j
    simp [Pi.single_eq_of_ne hjk] at this
  have hn : ¬IsRoot τ (Pi.single j 1 + -Pi.single k 1) := by
    rw [← sub_eq_add_neg]
    exact not_isRoot_single_sub_single hjk
  exact commute_xPar hD hτ (isRoot_single τ j) (isRoot_neg_single τ k) hne hn c d

theorem commute_xPar_single_single {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ)
    {j k : Fin τ.rank} (hjk : j ≠ k) (h0 : τ.cartan k j = 0) (c d : K) :
    Commute (xPar F (Pi.single j 1) c) (xPar F (Pi.single k 1) d) := by
  have hne : (Pi.single j 1 + Pi.single k 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
    have := congrFun h j
    simp [Pi.single_eq_of_ne hjk] at this
  have hn : ¬IsRoot τ (Pi.single j 1 + Pi.single k 1) := by
    rw [add_comm]
    exact not_isRoot_single_add_single_of_cartan_eq_zero hjk h0
  exact commute_xPar hD hτ (isRoot_single τ j) (isRoot_single τ k) hne hn c d

theorem commute_xPar_neg_single_neg_single {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ)
    {j k : Fin τ.rank} (hjk : j ≠ k) (h0 : τ.cartan k j = 0) (c d : K) :
    Commute (xPar F (-Pi.single j 1) c) (xPar F (-Pi.single k 1) d) := by
  have hne : (-Pi.single j 1 + -Pi.single k 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
    have := congrFun h j
    simp [Pi.single_eq_of_ne hjk] at this
  have hn : ¬IsRoot τ (-Pi.single j 1 + -Pi.single k 1) := by
    intro h
    have h' := IsRoot.neg h
    rw [neg_add, neg_neg, neg_neg, add_comm] at h'
    exact not_isRoot_single_add_single_of_cartan_eq_zero hjk h0 h'
  exact commute_xPar hD hτ (isRoot_neg_single τ j) (isRoot_neg_single τ k) hne hn c d

theorem commutatorElement_mul_mul_of_commute {G : Type*} [Group G] {x₁ y₁ x₂ y₂ : G}
    (h1 : Commute x₁ x₂) (h2 : Commute x₁ y₂) (h3 : Commute y₁ x₂) (h4 : Commute y₁ y₂) :
    ⁅x₁ * x₂, y₁ * y₂⁆ = ⁅x₁, y₁⁆ * ⁅x₂, y₂⁆ := by
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [h3.symm.left_comm, h1.symm.inv_inv.left_comm, h2.symm.inv_right.left_comm,
    h1.symm.inv_right.left_comm, h4.symm.inv_inv.eq, h3.symm.inv_inv.left_comm,
    h4.symm.inv_right.left_comm, h3.symm.inv_right.left_comm]

theorem not_commute_xPar_mul_xPar_neg [CharP K 2] {i k : Fin τ.rank} (hk : τ.cartan i k = -1) :
    ¬Commute (xPar F (Pi.single i 1) (1 : K) * xPar F (-Pi.single i 1) 1)
      (xPar F (Pi.single i 1) 1) := by
  obtain ⟨φ, hφ, hU, hL⟩ := exists_sl2_hom (K := K) F hk
  rw [xPar_simple, xPar_neg_simple, ← hU, ← hL, ← map_mul]
  intro h
  set U := CFSG.LieType.Steinberg.sl2Upper (1 : K)
  set L := CFSG.LieType.Steinberg.sl2Lower (1 : K)
  have h1 : φ (U * L * U) = φ (U * (U * L)) := by
    rw [map_mul φ (U * L) U, map_mul φ U (U * L)]
    exact h.eq
  have h' : U * L * U = U * (U * L) := hφ h1
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have e := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h'
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e
  change (!![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1] * !![(1 : K), 1; 0, 1]) 0 0 =
    (!![(1 : K), 1; 0, 1] * (!![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1])) 0 0 at e
  simp [Matrix.mul_apply, Fin.sum_univ_two, h2] at e

section E6


variable {F : RootOperatorFamily .E6}

theorem e6A_eq [CharP K 2] :
    ⁅xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K),
      xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)⁆ =
    (xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 0) 1) (1 : K)) ^ 2 *
      (xPar F (Pi.single (e6Node 5) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)) ^ 2 := by
  have h05 : e6Node 0 ≠ e6Node 5 := by decide
  have h50 : e6Node 5 ≠ e6Node 0 := by decide
  rw [commutatorElement_mul_mul_of_commute
    (commute_xPar_single_single e6AdjData_valid noG2_E6 h05 (by decide) 1 1)
    (commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h05 1 1)
    (commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h50 1 1).symm
    (commute_xPar_neg_single_neg_single e6AdjData_valid noG2_E6 h05 (by decide) 1 1),
    commutatorElement_def, commutatorElement_def, xPar_one_inv, xPar_one_inv, xPar_one_inv,
    xPar_one_inv, pow_two, pow_two]
  simp only [mul_assoc]

theorem commute_e6B :
    Commute (xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 0) 1) (1 : K))
      (xPar F (Pi.single (e6Node 5) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)) := by
  have h05 : e6Node 0 ≠ e6Node 5 := by decide
  have h50 : e6Node 5 ≠ e6Node 0 := by decide
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
  · exact commute_xPar_single_single e6AdjData_valid noG2_E6 h05 (by decide) 1 1
  · exact commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h05 1 1
  · exact (commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h50 1 1).symm
  · exact commute_xPar_neg_single_neg_single e6AdjData_valid noG2_E6 h05 (by decide) 1 1

theorem orderOf_e6B_mul [CharP K 2] :
    orderOf ((xPar F (Pi.single (e6Node 0) 1) (1 : K) *
      xPar F (-Pi.single (e6Node 0) 1) (1 : K)) * (xPar F (Pi.single (e6Node 5) 1) (1 : K) *
        xPar F (-Pi.single (e6Node 5) 1) (1 : K))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h05 : e6Node 0 ≠ e6Node 5 := by decide
  have h50 : e6Node 5 ≠ e6Node 0 := by decide
  have ho0 := orderOf_xPar_mul_xPar_neg (F := F) (K := K) (i := e6Node 0) (k := e6Node 2)
    (by decide)
  have ho5 := orderOf_xPar_mul_xPar_neg (F := F) (K := K) (i := e6Node 5) (k := e6Node 4)
    (by decide)
  have hb0 := pow_orderOf_eq_one
    (xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 0) 1) (1 : K))
  have hb5 := pow_orderOf_eq_one
    (xPar F (Pi.single (e6Node 5) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K))
  rw [ho0] at hb0
  rw [ho5] at hb5
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [(commute_e6B (F := F) (K := K)).mul_pow, hb0, hb5, one_mul]
  · have hb := eq_inv_of_mul_eq_one_left h
    apply not_commute_xPar_mul_xPar_neg (F := F) (K := K) (i := e6Node 0) (k := e6Node 2)
      (by decide)
    rw [hb]
    refine Commute.inv_left (Commute.mul_left ?_ ?_)
    · exact (commute_xPar_single_single e6AdjData_valid noG2_E6 h05 (by decide) 1 1).symm
    · exact commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h05 1 1 |>.symm

theorem orderOf_e6A [CharP K 2] :
    orderOf ⁅xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K),
      xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)⁆ = 3 := by
  rw [e6A_eq, ← (commute_e6B (F := F) (K := K)).mul_pow, orderOf_pow' _ two_ne_zero,
    orderOf_e6B_mul]
  norm_num

theorem commute_e6A :
    Commute ⁅xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K),
      xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)⁆
      (xPar F (Pi.single (e6Node 1) 1) (1 : K)) := by
  have h01 : e6Node 0 ≠ e6Node 1 := by decide
  have h51 : e6Node 5 ≠ e6Node 1 := by decide
  have h10 : e6Node 1 ≠ e6Node 0 := by decide
  have h15 : e6Node 1 ≠ e6Node 5 := by decide
  have hu : Commute (xPar F (Pi.single (e6Node 0) 1) (1 : K) *
      xPar F (Pi.single (e6Node 5) 1) (1 : K)) (xPar F (Pi.single (e6Node 1) 1) (1 : K)) :=
    (commute_xPar_single_single e6AdjData_valid noG2_E6 h01 (by decide) 1 1).mul_left
      (commute_xPar_single_single e6AdjData_valid noG2_E6 h51 (by decide) 1 1)
  have hv : Commute (xPar F (-Pi.single (e6Node 0) 1) (1 : K) *
      xPar F (-Pi.single (e6Node 5) 1) (1 : K)) (xPar F (Pi.single (e6Node 1) 1) (1 : K)) :=
    (commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h10 1 1).symm.mul_left
      (commute_xPar_single_neg_single e6AdjData_valid noG2_E6 h15 1 1).symm
  rw [commutatorElement_def]
  exact ((hu.mul_left hv).mul_left hu.inv_left).mul_left hv.inv_left

section Normal


theorem exactNormalAut_one_adjX_one {τ : Tag} (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank) :
    exactNormalAut τ K 1 σ ε (adjX τ K i 1) = adjX τ K (exactPerm τ ε i) 1 := by
  rw [exactNormalAut_adjX, map_one, Pi.one_apply, Units.val_one, one_mul]

theorem exactNormalAut_one_adjY_one {τ : Tag} (σ : K ≃+* K) (ε : ℕ) (i : Fin τ.rank) :
    exactNormalAut τ K 1 σ ε (adjY τ K i 1) = adjY τ K (exactPerm τ ε i) 1 := by
  rw [exactNormalAut_adjY, map_one, Pi.one_apply, inv_one, Units.val_one, one_mul]

theorem exactNormalAut_diag_adjX_one {τ : Tag} (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    exactNormalAut τ K a 1 0 (adjX τ K i 1) = adjX τ K i (a i) := by
  rw [exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply, map_one, mul_one]

theorem exactPerm_E6_cases (ε : ℕ) :
    exactPerm .E6 ε = 1 ∨
      exactPerm .E6 ε = Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4) := by
  have h2 : (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) ^ 2 = 1 := by
    decide
  change (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) ^ ε = 1 ∨
    (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) ^ ε =
      Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' ε
  · exact Or.inl (by rw [pow_mul, h2, one_pow])
  · exact Or.inr (by rw [pow_succ, pow_mul, h2, one_pow, one_mul])

theorem exactNormalAut_one_e6One (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K 1 σ ε (xPar F (Pi.single (e6Node 1) 1) 1) =
      xPar F (Pi.single (e6Node 1) 1) 1 := by
  rw [xPar_single_eq_adjX, exactNormalAut_one_adjX_one]
  rcases exactPerm_E6_cases ε with h | h
  · rw [h]
    rfl
  · rw [h, show (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) (e6Node 1) =
      e6Node 1 by decide]

theorem exactNormalAut_one_e6U (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K 1 σ ε
        (xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K)) =
      xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K) := by
  rw [map_mul, xPar_single_eq_adjX, xPar_single_eq_adjX, exactNormalAut_one_adjX_one,
    exactNormalAut_one_adjX_one]
  rcases exactPerm_E6_cases ε with h | h
  · rw [h]
    rfl
  · rw [h, show (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) (e6Node 0) =
      e6Node 5 by decide,
      show (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) (e6Node 5) =
      e6Node 0 by decide, ← xPar_single_eq_adjX (F := F),
      ← xPar_single_eq_adjX (F := F)]
    exact (commute_xPar_single_single e6AdjData_valid noG2_E6 (j := e6Node 5) (k := e6Node 0)
      (by decide) (by decide) 1 1).eq

theorem exactNormalAut_one_e6V (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K 1 σ ε
        (xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)) =
      xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K) := by
  rw [map_mul, xPar_neg_single_eq_adjY, xPar_neg_single_eq_adjY, exactNormalAut_one_adjY_one,
    exactNormalAut_one_adjY_one]
  rcases exactPerm_E6_cases ε with h | h
  · rw [h]
    rfl
  · rw [h, show (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) (e6Node 0) =
      e6Node 5 by decide,
      show (Equiv.swap (e6Node 0) (e6Node 5) * Equiv.swap (e6Node 2) (e6Node 4)) (e6Node 5) =
      e6Node 0 by decide, ← xPar_neg_single_eq_adjY (F := F),
      ← xPar_neg_single_eq_adjY (F := F)]
    exact (commute_xPar_neg_single_neg_single e6AdjData_valid noG2_E6 (j := e6Node 5)
      (k := e6Node 0) (by decide) (by decide) 1 1).eq

theorem exactNormalAut_one_e6A (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut .E6 K 1 σ ε
        ⁅xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K),
          xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)⁆ =
      ⁅xPar F (Pi.single (e6Node 0) 1) (1 : K) * xPar F (Pi.single (e6Node 5) 1) (1 : K),
        xPar F (-Pi.single (e6Node 0) 1) (1 : K) * xPar F (-Pi.single (e6Node 5) 1) (1 : K)⁆ := by
  rw [map_commutatorElement, exactNormalAut_one_e6U, exactNormalAut_one_e6V]

end Normal

end E6

end AutSt

end CFSG.StandardType
