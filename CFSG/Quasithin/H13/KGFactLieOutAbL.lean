module

public import CFSG.Quasithin.Vol2.KGFactInspOutDer
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin

public section

namespace CFSG.Quasithin.H13.KGLieOut

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
  (linear_perfect_cover_outer_derived_diagonal_bound
    unitary_perfect_cover_outer_derived_diagonal_bound)
open CFSG.Quasithin.H13.KGInsp4316 (center_eq_bot_of_simple quotCenterEquiv)
open scoped commutatorElement

theorem inner_of_outer_comm {X : Type*} [Group X] (h : ∀ a b : Outer X, a * b = b * a) :
    ∀ α β : MulAut X, ∃ g : X, α * β * α⁻¹ * β⁻¹ = MulAut.conj g := by
  intro α β
  have h1 : ((α * β * α⁻¹ * β⁻¹ : MulAut X) : Outer X) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h (α : Outer X) β]
    group
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨g, hg.symm⟩

theorem outer_comm_of_dvd_one {X : Type*} [Group X] (h : Nat.card (commutator (Outer X)) ∣ 1) :
    ∀ a b : Outer X, a * b = b * a := by
  have hb : commutator (Outer X) = ⊥ := Subgroup.card_eq_one.mp (Nat.dvd_one.mp h)
  intro a b
  have : ⁅a, b⁆ ∈ commutator (Outer X) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem exists_noncomm {X : Type*} [Group X] [Nontrivial X] [Group.IsPerfect X] :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative X ⟨⟨h⟩⟩

theorem outer_comm_psl {X : Type} [Group X] [Group.IsPerfect X] (hs : IsSimpleGroup X)
    {n p f : ℕ} (hm : StatedClassicalModel X .PSL n p f) (hg : Nat.gcd n (p ^ f - 1) = 1) :
    ∀ a b : Outer X, a * b = b * a := by
  have : Nontrivial X := hs.toNontrivial
  have hm' := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (quotCenterEquiv (center_eq_bot_of_simple hs exists_noncomm)).symm hm
  obtain ⟨-, hdvd, -⟩ := linear_perfect_cover_outer_derived_diagonal_bound X n p f hm'
  exact outer_comm_of_dvd_one (hg ▸ hdvd)

theorem outer_comm_psu {X : Type} [Group X] [Group.IsPerfect X] (hs : IsSimpleGroup X)
    {n p f : ℕ} (hm : StatedClassicalModel X .PSU n p f) (hg : Nat.gcd n (p ^ f + 1) = 1) :
    ∀ a b : Outer X, a * b = b * a := by
  have : Nontrivial X := hs.toNontrivial
  have hm' := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (quotCenterEquiv (center_eq_bot_of_simple hs exists_noncomm)).symm hm
  obtain ⟨-, hdvd, -⟩ := unitary_perfect_cover_outer_derived_diagonal_bound X n p f hm'
  exact outer_comm_of_dvd_one (hg ▸ hdvd)

theorem isPerfect_of_psl {X : Type} [Group X] {n p f : ℕ}
    (hm : StatedClassicalModel X .PSL n p f) (hn : 3 ≤ n ∨ (n = 2 ∧ 4 ≤ p ^ f)) :
    Group.IsPerfect X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) := by
    rcases hn with hn | ⟨rfl, h4⟩
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K
        (by rw [hK]; exact h4)
  have : Group.IsPerfect ↥(StatedSL n K) :=
    Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL n K).toMonoidHom)
      (specialLinearGroupEquivStatedSL n K).surjective
  have : Group.IsPerfect (StatedProj (StatedSL n K)) :=
    Group.IsPerfect.ofSurjective (CFSG.RankThree.CentralCover.statedProjMk_surjective _)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isPerfect_of_psu {X : Type} [Group X] {n p f : ℕ}
    (hm : StatedClassicalModel X .PSU n p f) : Group.IsPerfect X := by
  obtain ⟨⟨hp, -, hn, hnq⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect ↥(StatedSU n (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn hnq
  have : Group.IsPerfect (StatedProj (StatedSU n (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (CFSG.RankThree.CentralCover.statedProjMk_surjective _)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem two_pow_mod_three_of_even {f : ℕ} (hf : Even f) : 2 ^ f % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem gcd_three_eq_one {m : ℕ} (h : m % 3 ≠ 0) : Nat.gcd 3 m = 1 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hd => h (Nat.mod_eq_zero_of_dvd hd)

open CFSG.QuasithinUnique.Id2519 in
theorem hasElemAb_nine_psu3 {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 1 ≤ q)
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) : HasElemAb 3 9 (StatedProj (StatedSU 3 q K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add (by ring)
    rw [e]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  have hω3 : ((ω : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ((ω : Kˣ) : K) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    omega
  have hωq : ((ω : Kˣ) : K) ^ q * (ω : K) = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [← pow_succ, hm, pow_mul, hω3, one_pow]
  have hωq2 : (((ω : Kˣ) : K) ^ 2) ^ q * (ω : K) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm 2 q, pow_mul, ← mul_pow, hωq, one_pow]
  have hq0 : (0 : K) ^ q = 0 := zero_pow (by omega)
  have htU : tGL ((ω : Kˣ) : K) hω3 ∈ StatedSU 3 q K := by
    refine Subgroup.subset_closure ⟨det_tMat hω3, ?_⟩
    rw [coe_tGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tMat, Matrix.mul_apply, Matrix.diagonal, hq0, hωq, hωq2]
  have hpU : (pGL : GL (Fin 3) K) ∈ StatedSU 3 q K := by
    refine Subgroup.subset_closure ⟨det_pMat, ?_⟩
    rw [coe_pGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_three, hq0]
  exact hasElemAb_nine_statedProj htU hpU (tGL_pow_three _ _) pGL_pow_three
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2), ⟨ω ^ 2, rfl⟩, tGL_mul_pGL ω hω3⟩
    (tGL_not_scalar ω hω3 hω1) (fun n c hc => by
      obtain ⟨u, rfl⟩ := hc
      exact tGL_pow_mul_scalar_ne _ hω3 n u)

end CFSG.Quasithin.H13.KGLieOut
