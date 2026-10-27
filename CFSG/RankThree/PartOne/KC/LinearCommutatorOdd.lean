module

public import CFSG.RankThree.PartOne.KC.LinearCommutantSetting
public import CFSG.RankThree.PartOne.KC.LinearCommutantAction
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.KC.OddCommutatorSkeleton
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCLinComm
open scoped commutatorElement

namespace KCLinCommOdd

theorem mem_semilinearAutGroup_of_pow_eq_one {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {α : MulAut (projectiveSL n K)} {j : ℕ}
    (hα : α ^ p ^ j = 1) : α ∈ semilinearAutGroup n K :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2).pow hα


theorem card_commutator_eq_subgroupOf {G : Type*} [Group G] {S A C : Subgroup G} (hS : S ≤ C)
    (hA : A ≤ C) :
    Nat.card (⁅S, A⁆ : Subgroup G) = Nat.card (⁅S.subgroupOf C, A.subgroupOf C⁆ : Subgroup C) := by
  have h : (⁅S.subgroupOf C, A.subgroupOf C⁆ : Subgroup C).map C.subtype = ⁅S, A⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS,
      Subgroup.map_subgroupOf_eq_of_le hA]
  rw [← h, Subgroup.card_map_of_injective C.subtype_injective]


theorem lift_data {p ℓ n : ℕ} {K : Type} [Field K] [CharP K ℓ] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (hℓ : ℓ.Prime) {x : SpecialLinearGroup (Fin n) K} (hxo : orderOf x = p) :
    x ^ p = 1 ∧ Squarefree (minpoly K (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) := by
  have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
  refine ⟨hxp, ?_⟩
  have hpK : (p : K) ≠ 0 := by
    intro h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0))
  refine squarefree_minpoly_of_pow_eq_one hpK ?_
  rw [← Matrix.toLin'_pow, ← Matrix.SpecialLinearGroup.coe_pow, hxp,
    Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
  rfl


theorem actE_eq_of_commute {p n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1) {a : GL (Fin n) K} (hap : a ^ p = 1)
    (hdet : (a : Matrix (Fin n) (Fin n) K).det = 1) (α : ↥(semilinPsi n K).range)
    (hα : (α : MulAut (projectiveSL n K)) * conjAut n K a =
      conjAut n K a * (α : MulAut (projectiveSL n K))) :
    actE n K hn α (a : Matrix (Fin n) (Fin n) K) = (a : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨⟨M, σ⟩, hg⟩ := α.2
  have hαeq : α = ⟨semilinPsi n K ⟨M, σ⟩, ⟨⟨M, σ⟩, rfl⟩⟩ := Subtype.ext hg.symm
  have hcomm : semilinPsi n K ⟨M, σ⟩ * conjAut n K a * (semilinPsi n K ⟨M, σ⟩)⁻¹ =
      conjAut n K a := by
    rw [hg, hα, mul_inv_cancel_right]
  have h1 := semilin_conj_eq_self hn hZp hap hdet ⟨M, σ⟩ hcomm
  rw [hαeq, actE_semilinPsi hn ⟨M, σ⟩, ← coe_semilinGLAct, semilinGLAct_mk]
  exact congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) h1


theorem linear_inner_actor_local_core_commutators_odd_of_params {p ℓ f n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hf : 1 ≤ f) (hn : 3 ≤ n) {K : Type} [Field K]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hq : 3 < ℓ ^ f)
    (hZp : ∀ c : Kˣ, c ^ p = 1 → c ^ n = 1 → c = 1)
    (hr : ∀ x : SpecialLinearGroup (Fin n) K, x ^ p = 1 →
      Nat.card (primaryFactors (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K))) < p)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)}
    (ht : t ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    (htp : orderOf t = p) (A : Subgroup (MulAut (projectiveSL n K)))
    (hAle : A ≤ B ⊓ Subgroup.centralizer {t}) (hAp : IsPGroup p A) :
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ :
      Subgroup (MulAut (projectiveSL n K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  have hdesc :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
  have hDn : (conjAut n K).range.Normal := by
    rw [← linearAutGroup_eq_range]
    exact hdesc.2.2.2.2.2.1
  have hcomm : ∀ u v : MulAut (projectiveSL n K), u * v * u⁻¹ * v⁻¹ ∈ (conjAut n K).range := by
    rw [← linearAutGroup_eq_range]
    exact hdesc.2.2.2.2.2.2.1
  obtain ⟨x, hxo, hxt⟩ := exists_special_lift hp hn hZp ht htp
  obtain ⟨hxp, hsq⟩ := lift_data hp hℓp hℓ hxo
  set a : GL (Fin n) K := SpecialLinearGroup.toGL x with ha
  have hap : a ^ p = 1 := by rw [ha, ← map_pow, hxp, map_one]
  have hdet : (a : Matrix (Fin n) (Fin n) K).det = 1 := x.2
  have hta : conjAut n K a = t := by rw [ha, conjAut_toGL, hxt]
  subst hta
  have hr' := hr x hxp
  have S := projSetting hn hK4 hZp hDn B hB a hap hdet hsq
  have hAE : A ≤ (semilinPsi n K).range := by
    intro α hα
    obtain ⟨j, hj⟩ := hAp ⟨α, hα⟩
    rw [range_semilinPsi]
    exact mem_semilinearAutGroup_of_pow_eq_one hn hp2 hp (j := j)
      (by simpa using congrArg Subtype.val hj)
  have hfixA : ∀ α : ↥A, actE n K hn ⟨α, hAE α.2⟩ (a : Matrix (Fin n) (Fin n) K) = a := fun α =>
    actE_eq_of_commute hn hZp hap hdet ⟨α, hAE α.2⟩
      (Subgroup.mem_centralizer_singleton_iff.mp (hAle α.2).2)
  obtain ⟨hSθle, hSθnorm, -⟩ := inSubgroup_theta_normal_prime_complement hp
    (B ⊓ Subgroup.centralizer ({conjAut n K a} : Set (MulAut (projectiveSL n K))))
  set CT : Subgroup (MulAut (projectiveSL n K)) :=
    Subgroup.centralizer ({conjAut n K a} : Set (MulAut (projectiveSL n K))) with hCT
  set Sθ := inSubgroup (aschbacherSolvableCore p) (B ⊓ CT) with hSθ
  set N : Subgroup (MulAut (projectiveSL n K)) :=
    (commutantUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))).range.map (conjAut n K)
    with hN
  have hNeq : (conjAut n K).range ⊓ CT = N := S.N_eq
  have hACT : A ≤ CT := hAle.trans inf_le_right
  have hSCT : Sθ ≤ CT := hSθle.trans inf_le_right
  have hNCT : N ≤ CT := hNeq ▸ inf_le_right
  have : Finite (MulAut (projectiveSL n K)) := inferInstance
  have : Finite ↥CT := Subtype.finite
  rw [card_commutator_eq_subgroupOf hSCT hACT]
  refine KCOddCommutator.odd_commutator_of_central_residue (C := ↥CT) (p := p)
    (hp.odd_of_ne_two hp2) (N := N.subgroupOf CT) (J := (⁅N, N⁆).subgroupOf CT)
    (S := Sθ.subgroupOf CT) (A := A.subgroupOf CT) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    refine ⟨fun y hy c => ?_⟩
    have hy' : (y : MulAut (projectiveSL n K)) ∈ N := hy
    rw [← hNeq] at hy' ⊢
    exact ⟨hDn.conj_mem _ hy'.1 _, CT.mul_mem (CT.mul_mem c.2 hy'.2) (CT.inv_mem c.2)⟩
  ·
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hACT).symm
  ·
    intro α hα s hs
    have hα' : (α : MulAut (projectiveSL n K)) ∈ A := hα
    have hs' : (s : MulAut (projectiveSL n K)) ∈ Sθ := hs
    exact (Subgroup.normal_subgroupOf_iff hSθle).mp hSθnorm (s : MulAut (projectiveSL n K))
      (α : MulAut (projectiveSL n K)) hs' (hAle hα')
  ·
    rw [Subgroup.commutator_le]
    intro s _ α _
    show ((⁅s, α⁆ : ↥CT) : MulAut (projectiveSL n K)) ∈ N
    rw [← hNeq]
    exact ⟨hcomm (s : MulAut (projectiveSL n K)) (α : MulAut (projectiveSL n K)),
      (⁅s, α⁆ : ↥CT).2⟩
  ·
    intro s hs j hj
    have hs' : (s : MulAut (projectiveSL n K)) ∈ Sθ := hs
    have := Subgroup.mem_centralizer_iff.mp (S.core_le_centralizer_derived hp hs')
      (j : MulAut (projectiveSL n K)) hj
    exact Subtype.ext this.symm
  ·
    intro y hy hyJ m hm
    have hyN : (y : MulAut (projectiveSL n K)) ∈ N := hy
    have hmN : (m : MulAut (projectiveSL n K)) ∈ N := hm
    have hyc : (y : MulAut (projectiveSL n K)) ∈
        Subgroup.centralizer ((⁅N, N⁆ : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjCT : j ∈ CT := hNCT (KCUnitary.commutator_self_le N hj)
      exact (congrArg Subtype.val (hyJ ⟨j, hjCT⟩ hj)).symm
    have hyZ : (y : MulAut (projectiveSL n K)) ∈ (Subgroup.center ↥N).map N.subtype := by
      rw [← S.inf_centralizer_derived_eq_center]
      exact ⟨hyN, hyc⟩
    obtain ⟨y0, hy0, hy0eq⟩ := hyZ
    apply Subtype.ext
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy0 ⟨m, hmN⟩)
    have h2 : (y0 : MulAut (projectiveSL n K)) = y := hy0eq
    change (y : MulAut (projectiveSL n K)) * m = m * y
    rw [← h2]
    exact h1.symm
  ·
    intro α hα y hy hyc hyk
    have hα' : (α : MulAut (projectiveSL n K)) ∈ A := hα
    have hyN : (y : MulAut (projectiveSL n K)) ∈ N := hy
    have hyZ : (y : MulAut (projectiveSL n K)) ∈ (Subgroup.center ↥N).map N.subtype := by
      refine ⟨⟨y, hyN⟩, Subgroup.mem_center_iff.mpr fun m => ?_, rfl⟩
      have h1 := congrArg Subtype.val (hyc ⟨m, hNCT m.2⟩ m.2)
      apply Subtype.ext
      exact h1.symm
    rw [S.center_image_eq] at hyZ
    obtain ⟨Y, hY, hYy⟩ := hyZ
    obtain ⟨w, rfl⟩ := hY
    obtain ⟨k, hk⟩ := hyk
    have hk1 : conjAut n K ((centerUnitsToGL (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) w) ^
        2 ^ k) = 1 := by
      rw [map_pow, hYy]
      exact congrArg Subtype.val hk
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp hk1
    have hwk : w ^ 2 ^ k ∈ scalarCenterUnits (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) := by
      rw [mem_scalarCenterUnits, map_pow]
      exact ⟨c, hc⟩
    apply Subtype.ext
    have h3 := conj_centerUnitsToGL_eq hn hAE hfixA hp hp2 hsq hr' hAp ⟨α, hα'⟩ w hwk
    change (α : MulAut (projectiveSL n K)) * (y : MulAut (projectiveSL n K)) *
      (α : MulAut (projectiveSL n K))⁻¹ = y
    rw [← hYy]
    exact h3

end KCLinCommOdd

end CFSG.RankThree.PartOne
