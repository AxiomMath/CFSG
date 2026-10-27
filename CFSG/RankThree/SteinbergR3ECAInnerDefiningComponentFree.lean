module

public import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningFour
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningLog

public section

namespace CFSG.RankThree.CAInnerDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {C : Type*} [Group C]

theorem not_isSolvable_of_isQuasisimple (hQ : CFSG.IsQuasisimple C) : ¬ Group.IsSolvable C := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C

theorem forall_not_isComponent_of_pow {p : ℕ} [Fact p.Prime] [Finite C] (O : Subgroup C)
    (hO : O.Normal) (hOp : ∀ x ∈ O, x ^ p = 1)
    (hcent : ∀ x : C, (∀ y ∈ O, x * y = y * x) → x ^ p = 1) (L : Subgroup C) :
    ¬ CFSG.IsComponent L := by
  intro hL
  have hLp : IsPGroup p L := by
    rcases CFSG.LocalCores.component_normal_subgroup hL hO with hle | hcomm
    · intro x
      exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hOp x (hle x.2))⟩
    · have hle : L ≤ Subgroup.centralizer (O : Set C) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow]
      exact hcent x fun y hy => (Subgroup.mem_centralizer_iff.mp (hle x.2) y hy).symm
  have : Group.IsNilpotent L := hLp.isNilpotent
  exact not_isSolvable_of_isQuasisimple hL.1 inferInstance

theorem forall_not_isComponent_centralizer_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (α : G ≃* H) (x : G)
    (h : ∀ L : Subgroup (Subgroup.centralizer ({α x} : Set H)), ¬ CFSG.IsComponent L)
    (L : Subgroup (Subgroup.centralizer ({x} : Set G))) : ¬ CFSG.IsComponent L := by
  have hmap : (Subgroup.centralizer ({x} : Set G)).map α.toMonoidHom =
      Subgroup.centralizer ({α x} : Set H) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, hz, map_mul]
    · intro hy
      refine ⟨α.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply α.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  let e := ((Subgroup.centralizer ({x} : Set G)).equivMapOfInjective α.toMonoidHom
    α.injective).trans (MulEquiv.subgroupCongr hmap)
  intro hL
  exact h _ (CFSG.LocalCores.isComponent_map_mulEquiv e hL)

theorem eqLocus_conj_eq_centralizer (y : C) :
    ((MulAut.conj y : MulAut C) : C →* C).eqLocus (MonoidHom.id C) =
      Subgroup.centralizer ({y} : Set C) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change y * x * y⁻¹ = x ↔ x * y = y * x
  constructor
  · intro hx
    calc x * y = y * x * y⁻¹ * y := by rw [hx]
      _ = y * x := by group
  · intro hx
    rw [← hx]
    group

end Generic

section Linear

open LinearFlag CFSG.RankThree.RegularUnipotent CFSG.RankThree.NonregularUnipotent
open CFSG.RankThree.LinearPointwise

variable {n : ℕ} {k : Type*} [Field k]

theorem forall_not_isComponent_regU {p : ℕ} [Fact p.Prime] [CharP k p] [Finite k] (hn : 0 < n)
    (hnp : n ≤ p)
    (L : Subgroup (Subgroup.centralizer ({proj n k (regU n k)} : Set (projectiveSL n k)))) :
    ¬ CFSG.IsComponent L := by
  have : NeZero n := ⟨hn.ne'⟩
  refine forall_not_isComponent_of_pow (p := p) ⊥ inferInstance
    (fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]) (fun x _ => ?_) L
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_eq_one_of_commute_proj_regU hnp (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem forall_not_isComponent_of_commutantIdeal {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hn3 : 3 ≤ n) [Finite k] [CharP k p] {N : Matrix (Fin n) (Fin n) k}
    {I : Matrix (Fin n) (Fin n) k → Prop} (hI : CommutantIdeal N I) (hNI : I N)
    (u₀ : SpecialLinearGroup (Fin n) k) (hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = 1 + N)
    (hcent : ∀ A : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ idealSubgroup hI, A * (g : Matrix (Fin n) (Fin n) k) = g * A) →
        ∃ c : k, I (A - c • 1)) :
    ∀ L : Subgroup (Subgroup.centralizer ({proj n k u₀} : Set (projectiveSL n k))),
      ¬ CFSG.IsComponent L := by
  have : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := NeZero.pos n
  set U₀ := idealSubgroup hI with hU₀
  have hu₀U : u₀ ∈ U₀ := by
    rw [hU₀, mem_idealSubgroup, hu₀, add_sub_cancel_left]
    exact hNI
  have hpow : ∀ g ∈ U₀, g ^ p = 1 := fun g hg => idealSubgroup_pow_char hp3 hI hg
  set C := Subgroup.centralizer ({proj n k u₀} : Set (projectiveSL n k)) with hC
  have hexact : ∀ h g : SpecialLinearGroup (Fin n) k, g ^ p = 1 →
      proj n k h * proj n k g = proj n k g * proj n k h → h * g = g * h := by
    intro h g hg hhg
    have hconj : proj n k ((MulAut.conj h).toMonoidHom g) = proj n k g := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, hhg, map_inv,
        mul_inv_cancel_right]
    have hg1 : g ^ p ^ 1 = 1 := by rw [pow_one]; exact hg
    have h1 := eq_of_proj_eq_of_pow_eq_one hn0 _ hg1 hconj
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    calc h * g = h * g * h⁻¹ * h := by group
      _ = g * h := by rw [h1]
  have hlift : ∀ x ∈ C, ∃ h : SpecialLinearGroup (Fin n) k, proj n k h = x ∧
      (h : Matrix (Fin n) (Fin n) k) * N = N * h := by
    intro x hx
    obtain ⟨h, rfl⟩ := proj_surjective n k x
    refine ⟨h, rfl, ?_⟩
    have h2 := hexact h u₀ (hpow u₀ hu₀U) (Subgroup.mem_centralizer_singleton_iff.1 hx)
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
      h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu₀, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at h3
    exact add_left_cancel h3
  have hW0C : U₀.map (proj n k) ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu₀,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, idealSubgroup_comm hI hg]
  have hW0n : ((U₀.map (proj n k)).subgroupOf C).Normal := by
    constructor
    intro w hw x
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨g, hg, hgw⟩ := hw
    obtain ⟨h, hhx, hhN⟩ := hlift x x.2
    refine ⟨h * g * h⁻¹, idealSubgroup_conj_mem hI hhN hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hhx, hgw]
    rfl
  refine forall_not_isComponent_of_pow (p := p) _ hW0n (fun x hx => ?_) (fun x hx => ?_)
  · rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hgx, ← map_pow, hpow g hg, map_one]
  · obtain ⟨h, hhx, -⟩ := hlift x x.2
    have hcomm : ∀ g ∈ U₀, (h : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
        g * h := by
      intro g hg
      have h1 := hx ⟨proj n k g, hW0C ⟨g, hg, rfl⟩⟩
        (Subgroup.mem_subgroupOf.mpr ⟨g, hg, rfl⟩)
      have h2 : proj n k h * proj n k g = proj n k g * proj n k h := by
        have := congrArg Subtype.val h1
        simpa [← hhx] using this
      have h3 := hexact h g (hpow g hg) h2
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        congrArg (fun z : SpecialLinearGroup (Fin n) k => (z : Matrix (Fin n) (Fin n) k)) h3
    obtain ⟨c, hc⟩ := hcent _ hcomm
    have hAX : ((Matrix.SpecialLinearGroup.toGL h : GL (Fin n) k) :
        Matrix (Fin n) (Fin n) k) = c • 1 + ((h : Matrix (Fin n) (Fin n) k) - c • 1) := by
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      abel
    obtain ⟨v, hv⟩ := exists_pow_char_eq_scalar hp3 (Matrix.SpecialLinearGroup.toGL h)
      (hI.cube _ hc) hAX
    have h1 : ((h ^ p : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        scalar (Fin n) (v : k) := by
      have := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k)) hv
      simp only [Units.val_pow_eq_pow_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        GeneralLinearGroup.coe_scalar] at this
      rw [Matrix.SpecialLinearGroup.coe_pow]
      exact this
    have hdet : ((h ^ p : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k).det = 1 :=
      (h ^ p).2
    rw [h1, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hhx, ← map_pow, proj_eq_one_iff, mem_scalars]
    exact ⟨v, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet), h1⟩

theorem linear_centralizer_component_free {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hn : n = 3 ∨ n = 4) [Finite k] [CharP k p] (hk : Nat.card k = p ^ f)
    (x : projectiveSL n k) (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (L : Subgroup (Subgroup.centralizer ({x} : Set (projectiveSL n k)))) :
    ¬ CFSG.IsComponent L := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : NeZero n := ⟨by omega⟩
  have hker : ¬ p ∣ Nat.card (proj n k).ker := by
    rw [ker_proj, CFSG.RankThree.PartOne.card_scalars (by omega), hk]
    intro hdvd
    have h1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 h1
      rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  obtain ⟨u, hux, hup⟩ := CFSG.RankThree.PartOne.exists_lift_pow_eq_one (proj n k) hp hker
    (MonoidHom.mem_range.mpr (proj_surjective n k x)) hxp
  subst hux
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  have hMp : ((u : Matrix (Fin n) (Fin n) k) - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow,
      ← Matrix.SpecialLinearGroup.coe_pow, hup, Matrix.SpecialLinearGroup.coe_one, sub_self]
  have hne : (u : Matrix (Fin n) (Fin n) k) - 1 ≠ 0 := by
    intro h
    apply hu1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.mp h
  have hMn := CFSG.RankThree.PartOne.pow_dim_eq_zero_of_pow_eq_zero hMp
  have hp3' : 3 ≤ p := hp3.le
  rcases hn with rfl | rfl
  · obtain ⟨A, hA, hMA | hMA⟩ :=
      CFSG.RankThree.PartOne.exists_unit_mul_eq_nilpotent_three hMn hne
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (regU 3 k) hA hMA
        coe_regU
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 3 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_regU (by norm_num) (by omega)
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (uA k) hA hMA
        (coe_oneAdd _ _)
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 3 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_of_commutantIdeal hp3' le_rfl commutantIdeal_A idealA_N
        (uA k) (coe_oneAdd _ _) hcent_A
  · obtain ⟨A, hA, hMA | hMA | hMA | hMA⟩ :=
      CFSG.RankThree.PartOne.exists_unit_mul_eq_nilpotent_four hMn hne
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (regU 4 k) hA hMA
        coe_regU
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 4 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_regU (by norm_num) (by omega)
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (uB k) hA hMA
        (coe_oneAdd _ _)
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 4 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_of_commutantIdeal hp3' (by norm_num) commutantIdeal_B
        idealB_N (uB k) (coe_oneAdd _ _) hcent_B
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (uC k) hA hMA
        (coe_oneAdd _ _)
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 4 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_of_commutantIdeal hp3' (by norm_num) commutantIdeal_C
        idealC_N (uC k) (coe_oneAdd _ _) hcent_C
    · obtain ⟨Ag, hAg⟩ := CFSG.RankThree.PartOne.exists_conjAut_of_mul_eq u (uD k) hA hMA
        (coe_oneAdd _ _)
      refine forall_not_isComponent_centralizer_of_mulEquiv (conjAut 4 k Ag) _ ?_ L
      rw [hAg]
      exact forall_not_isComponent_of_commutantIdeal hp3' (by norm_num) commutantIdeal_D
        idealD_N (uD k) (coe_oneAdd _ _) hcent_D

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KCUnitaryDefining CFSG.RankThree.PartOne.KCUnitaryRegular

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem commute_of_mk_commute {n : ℕ} (hn1 : 1 ≤ n) {C : Matrix (Fin n) (Fin n) K}
    {g v : gramSU h C} (hvp : v ^ p = 1)
    (hgv : (g : primeFormP h C) * (v : primeFormP h C) =
      (v : primeFormP h C) * (g : primeFormP h C)) :
    g * v = v * g := by
  have hconjp : (g * v * g⁻¹) ^ p = 1 := by rw [conj_pow, hvp, mul_one, mul_inv_cancel]
  have hconjπ : ((g * v * g⁻¹ : gramSU h C) : primeFormP h C) = (v : primeFormP h C) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgv, mul_assoc,
      mul_inv_cancel, mul_one]
  have hconj : g * v * g⁻¹ = v := eq_of_mk_eq_of_pow_eq_one h hn1 _ hconjp hvp hconjπ
  calc g * v = g * v * g⁻¹ * g := by group
    _ = v * g := by rw [hconj]

theorem primeFormConjHom_eq_conj {n : ℕ} {C : Matrix (Fin n) (Fin n) K} (g : gramSU h C)
    (hg : (g : GL (Fin n) K) ∈ primeFormUnitary h C) :
    primeFormConjHom h C ⟨g, hg⟩ = MulAut.conj (g : primeFormP h C) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun y => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  rfl

theorem forall_not_isComponent_of_radical_data (hp3 : 3 < p) {n : ℕ} (hn : 3 ≤ n)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (u : gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hup : u ^ p = 1) (N : Matrix (Fin n) (Fin n) K)
    (hN : ∀ g : gramSU h (C : Matrix (Fin n) (Fin n) K), g * u = u * g →
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (R : Subgroup (gramSU h (C : Matrix (Fin n) (Fin n) K)))
    (hRu : ∀ r ∈ R, r * u = u * r) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRnorm : ∀ g : gramSU h (C : Matrix (Fin n) (Fin n) K),
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hRpt : ∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      (∀ r ∈ R, (A : GL (Fin n) K) * glAut σ (r : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = r) →
        ∃ r' ∈ R, primeFormConjHom h _ A * primeFormFieldHom h hC σ =
          MulAut.conj (r' : primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(u : primeFormP h (C : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h (C : Matrix (Fin n) (Fin n) K)))), ¬ CFSG.IsComponent L := by
  have hn1 : 1 ≤ n := by omega
  have hq := not_three_and_pow_eq_two (n := n) h hp3
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  set Cen := Subgroup.centralizer ({(u : primeFormP h (C : Matrix (Fin n) (Fin n) K))} :
    Set (primeFormP h (C : Matrix (Fin n) (Fin n) K))) with hCen
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n)
    with hπ
  have hRC : R.map π ≤ Cen := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hCen, Subgroup.mem_centralizer_singleton_iff, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hRu r hr]
  have hnorm : ((R.map π).subgroupOf Cen).Normal := by
    constructor
    intro w hw c
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨r, hr, hrw⟩ := hw
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (c : primeFormP h (C : Matrix (Fin n) (Fin n) K))
    have hgu : g * u = u * g := commute_of_mk_commute h hn1 hup (by
      rw [hg]
      exact Subgroup.mem_centralizer_singleton_iff.mp c.2)
    refine ⟨g * r * g⁻¹, hRnorm g (hN g hgu) r hr, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      hg]
    change (c : primeFormP h (C : Matrix (Fin n) (Fin n) K)) * π r * (c : primeFormP h _)⁻¹ = _
    rw [hrw]
    rfl
  refine forall_not_isComponent_of_pow (p := p) _ hnorm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨r, hr, hrx⟩ := hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hrx, ← map_pow, hRp r hr, map_one]
  · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : primeFormP h (C : Matrix (Fin n) (Fin n) K))
    have hcomm : ∀ r ∈ R, g * r * g⁻¹ = r := by
      intro r hr
      have h1 := hx ⟨π r, hRC ⟨r, hr, rfl⟩⟩ (Subgroup.mem_subgroupOf.mpr ⟨r, hr, rfl⟩)
      have h2 : (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) * (r : primeFormP h _) =
          (r : primeFormP h _) * (g : primeFormP h _) := by
        have := congrArg Subtype.val h1
        rw [hg]
        exact this
      have h3 := commute_of_mk_commute h hn1 (hRp r hr) h2
      calc g * r * g⁻¹ = r * g * g⁻¹ := by rw [h3]
        _ = r := by group
    have hgU : (g : GL (Fin n) K) ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) :=
      (mem_gramSU_iff_unitary h).mp g.2 |>.1
    obtain ⟨r', hr', hr'eq⟩ := hRpt ⟨g, hgU⟩ 1 (fun r hr => by
      rw [map_one, MulAut.one_apply]
      exact congrArg Subtype.val (hcomm r hr))
    rw [map_one, mul_one, primeFormConjHom_eq_conj] at hr'eq
    have hgr : (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = (r' : primeFormP h _) :=
      conj_injective_primeFormP h hC hn hq hr'eq
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hg, hgr, ← QuotientGroup.mk_pow, hRp r' hr',
      QuotientGroup.mk_one]

theorem forall_not_isComponent_regular (hp3 : 3 < p) {n : ℕ} (hn3 : 3 ≤ n) (hnp : n ≤ p)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {N : Matrix (Fin n) (Fin n) K}
    (hNskew : unitaryAdjoint h C N = -N) (hNn : N ^ n = 0) (hNreg : N ^ (n - 1) ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(unitaryExp h hn3 hnp hNn hNskew : primeFormP h (C : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h (C : Matrix (Fin n) (Fin n) K)))), ¬ CFSG.IsComponent L := by
  have hn1 : 1 ≤ n := by omega
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hN0 : IsNilpotent N := ⟨n, hNn⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, c7, -, -⟩ :=
    unitary_small_unipotent_logarithm_calculus h hp3 hn3 hnp hC
  set u := unitaryExp h hn3 hnp hNn hNskew with hu
  have hum : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N := rfl
  have hup : u ^ p = 1 := KCUnitaryNr.unitaryExp_pow_eq_one h hp3 hn3 hnp hC hNn hNskew
  refine forall_not_isComponent_of_pow (p := p) ⊥ inferInstance
    (fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]) (fun x _ => ?_)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (x : primeFormP h (C : Matrix (Fin n) (Fin n) K))
  have hy' : (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
      (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
      (u : primeFormP h (C : Matrix (Fin n) (Fin n) K)) *
        (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
    rw [hg]
    exact Subgroup.mem_centralizer_singleton_iff.1 x.2
  have hgu := commute_of_mk_commute h hn1 hup hy'
  have hcomm : Commute ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (truncExp n N) := by
    have h1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * truncExp n N =
        truncExp n N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have := congrArg (fun z : gramSU h (C : Matrix (Fin n) (Fin n) K) =>
        ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hgu
      simpa [Units.val_mul, hum] using this
    exact h1
  have hgN := (c7 N hN0 (g : GL (Fin n) K)).mp hcomm
  have hmem := pow_mem_normOneScalars_of_commute h hn3 hnp hNn hNreg hgN
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hg, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr hmem

theorem forall_not_isComponent_of_family {n : ℕ} (hn : 3 ≤ n) (hnp : n ≤ p) {C' : GL (Fin n) K}
    {N N' : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin n) K) N = -N)
    (u' : gramSU h (C' : Matrix (Fin n) (Fin n) K))
    (hu' : ((u' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N')
    (b : Fin n → Fin n → K)
    (hb : ∀ i j, gramForm h (1 : Matrix (Fin n) (Fin n) K) (b i) (b j) =
      (C' : Matrix (Fin n) (Fin n) K) i j)
    (hNb : ∀ j, N *ᵥ b j = ∑ i, N' i j • b i)
    (H : ∀ L : Subgroup (Subgroup.centralizer
      ({(u' : primeFormP h (C' : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h (C' : Matrix (Fin n) (Fin n) K)))), ¬ CFSG.IsComponent L) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(unitaryExp h hn hnp hN hskew :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} :
        Set (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))),
      ¬ CFSG.IsComponent L := by
  have hdet : (C' : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp C'.isUnit)
  obtain ⟨Q, hQ, hNQ⟩ := exists_gl_of_family h hdet b hb hNb
  set e := primeFormGramChange h Q hQ with he
  have hx : e (u' : primeFormP h (C' : Matrix (Fin n) (Fin n) K)) =
      (unitaryExp h hn hnp hN hskew :
        primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [he, primeFormGramChange_mk]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change (Q : Matrix (Fin n) (Fin n) K) * ((u' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = truncExp n N
    have hQQ : (Q : Matrix (Fin n) (Fin n) K) *
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hconj : (Q : Matrix (Fin n) (Fin n) K) * N' *
        ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = N := by
      rw [← hNQ, Matrix.mul_assoc, hQQ, Matrix.mul_one]
    rw [hu', ← hconj]
    exact (truncExp_conj Q N').symm
  refine forall_not_isComponent_centralizer_of_mulEquiv e.symm _ ?_
  rw [← hx, MulEquiv.symm_apply_apply]
  exact H

end Unitary

section UnitaryClasses

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KCUnitaryDefining CFSG.RankThree.PartOne.KCUnitaryRegular

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem forall_not_isComponent_trvElt (hp3 : 3 < p) {m : ℕ} (hm : 1 ≤ m) {η : K}
    (hη : h.bar η = -η) (hη0 : η ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(trvElt m h η hη : primeFormP h (trvGram K m))} : Set (primeFormP h (trvGram K m)))),
      ¬ CFSG.IsComponent L := by
  have hn : 1 ≤ m + 2 := by omega
  have hR := KCUnitaryTrv.trvElt_mem_trvR (m := m) h η hη
  refine forall_not_isComponent_of_radical_data h hp3 (by omega)
    (KCUnitaryTrv.isPrimeFormGram_trv (K := K) (m := m)) (trvElt m h η hη)
    (pow_eq_one_of_mem_isotropicRadical h hp3.le hn hR)
    (KCUnitaryTrv.trvN K m η) ?_ (KCUnitaryTrv.trvR h m)
    (fun r hr => KCUnitaryTrv.trvR_comm_trvElt h hη hr)
    (fun r hr => pow_eq_one_of_mem_isotropicRadical h hp3.le hn hr)
    (fun g hg r hr => KCUnitaryTrv.trvR_conj_mem h hη0 hg hr)
    (fun A σ hex => KCUnitaryTrv.trvR_pointwise h hm A σ hex)
  intro g hg
  have h1 := congrArg (fun z : gramSU h (trvGram K m) => ((z : GL (Fin (m + 2)) K) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) K)) hg
  simp only [Subgroup.coe_mul, Units.val_mul] at h1
  rw [coe_trvElt, mul_add, add_mul, mul_one, one_mul] at h1
  exact add_left_cancel h1

theorem forall_not_isComponent_nrEltA (hp3 : 3 < p) {η : K} (hη : h.bar η = -η)
    (hη0 : η ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(nrEltA h hp3 hη : primeFormP h (nrGramA K))} : Set (primeFormP h (nrGramA K)))),
      ¬ CFSG.IsComponent L := by
  have hn : 3 ≤ 4 := by norm_num
  have hnp : 4 ≤ p := by omega
  exact forall_not_isComponent_of_radical_data (C := KCUnitaryNr.nrGLA K) h hp3 hn
    KCUnitaryNr.isPrimeFormGram_nrA (nrEltA h hp3 hη)
    (KCUnitaryNr.unitaryExp_pow_eq_one h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrA
      (KCUnitaryNr.nrNilA_pow_four η) (KCUnitaryNr.nrNilA_skew h hη)) (nrNilA η)
    (fun g hg => (KCUnitaryNr.unitaryExp_comm_iff h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrA
      (KCUnitaryNr.nrNilA_pow_four η) (KCUnitaryNr.nrNilA_skew h hη) g).mp hg)
    (isotropicRadical h (nrGramA K) (nrL K))
    (fun r hr => (KCUnitaryNr.unitaryExp_comm_iff h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrA
      (KCUnitaryNr.nrNilA_pow_four η) (KCUnitaryNr.nrNilA_skew h hη) r).mpr
        (KCUnitaryNr.nrL_fix_comm h hr))
    (fun r hr => pow_eq_one_of_mem_isotropicRadical h hp3.le (by norm_num) hr)
    (fun g hg r hr => KCUnitaryNr.nrAR_conj_mem h hη0 hg hr)
    (fun A σ hex => KCUnitaryNr.nrAR_pointwise h A σ hex)

theorem forall_not_isComponent_nrEltB (hp3 : 3 < p) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({(nrEltB h hp3 : primeFormP h (nrGramB K))} : Set (primeFormP h (nrGramB K)))),
      ¬ CFSG.IsComponent L := by
  have hn : 3 ≤ 4 := by norm_num
  have hnp : 4 ≤ p := by omega
  exact forall_not_isComponent_of_radical_data (C := KCUnitaryNr.nrGLB K) h hp3 hn
    KCUnitaryNr.isPrimeFormGram_nrB (nrEltB h hp3)
    (KCUnitaryNr.unitaryExp_pow_eq_one h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrB
      KCUnitaryNr.nrNilB_pow_four (KCUnitaryNr.nrNilB_skew h)) (nrNilB K)
    (fun g hg => (KCUnitaryNr.unitaryExp_comm_iff h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrB
      KCUnitaryNr.nrNilB_pow_four (KCUnitaryNr.nrNilB_skew h) g).mp hg) (KCUnitaryNr.nrBR h)
    (fun r hr => (KCUnitaryNr.unitaryExp_comm_iff h hp3 hn hnp KCUnitaryNr.isPrimeFormGram_nrB
      KCUnitaryNr.nrNilB_pow_four (KCUnitaryNr.nrNilB_skew h) r).mpr
        ((KCUnitaryNr.mem_nrBR h).mp hr).1)
    (fun r hr => KCUnitaryNr.nrBR_pow_eq_one h hp3 hr)
    (fun g hg r hr => KCUnitaryNr.nrBR_conj_mem h hg hr)
    (fun A σ hex => KCUnitaryNr.nrBR_pointwise h hp3 A σ hex)

end UnitaryClasses

section UnitaryCases

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KCUnitaryDefining CFSG.RankThree.PartOne.KCUnitaryRegular

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem noComp_three_sq_zero (hp3 : 3 < p) {N : Matrix (Fin 3) (Fin 3) K} (hN : N ^ 3 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 3) K) N = -N) (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer ({(unitaryExp h (le_refl 3) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))} :
        Set (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))),
      ¬ CFSG.IsComponent L := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 3) (Fin 3) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin N
  have hNl : ∀ x y, B (Nl x) y = -B x (Nl y) := fun x y => gramForm_one_mulVec_skew h hs x y
  have hNl2 : ∀ x, Nl (Nl x) = 0 := fun x => by
    show N *ᵥ (N *ᵥ x) = 0
    rw [mulVec_mulVec, hN2, zero_mulVec]
  have hNl0 : Nl ≠ 0 := by
    intro h0
    apply hN0
    ext i j
    have := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
    simpa [Nl, mulVec_single_one] using this
  obtain ⟨η, hη, hη0⟩ := KCUnitaryHerm.exists_traceZero h
  obtain ⟨e, g, hee, hgg, heg, hNe, hNg, hWdim, hWsep, hcases⟩ :=
    KCUnitaryHerm.exists_sq_zero_structure hp3 hB hBl hNl hNl2 hNl0 hη hη0
  set W := (Submodule.span K {e, g}).orthogonalBilin B with hW
  have hWd : Module.finrank K W = 1 := by rw [hWdim, Module.finrank_fin_fun]
  have hT : ∀ z ∈ W, Nl z = 0 := by
    rcases hcases with hT | ⟨hfin2, -⟩
    · exact hT
    · omega
  obtain ⟨E, hE⟩ := h.exists_orthonormal_basis (hB.domRestrict W) hWsep
  have hp0 : 0 < Module.finrank K W := by omega
  obtain ⟨z, hzW, hzz⟩ : ∃ z : Fin 3 → K, z ∈ W ∧ B z z = 1 := by
    refine ⟨(E ⟨0, hp0⟩ : Fin 3 → K), (E ⟨0, hp0⟩).2, ?_⟩
    have := hE ⟨0, hp0⟩ ⟨0, hp0⟩
    simpa [LinearMap.domRestrict₁₂_apply] using this
  have hez : B e z = 0 :=
    (Submodule.mem_orthogonalBilin.mp hzW) e (Submodule.subset_span (by simp))
  have hgz : B g z = 0 :=
    (Submodule.mem_orthogonalBilin.mp hzW) g (Submodule.subset_span (by simp))
  have hze : B z e = 0 := by rw [hsymm e z, hez, map_zero]
  have hzg : B z g = 0 := by rw [hsymm g z, hgz, map_zero]
  have hge : B g e = 1 := by rw [hsymm e g, heg, map_one]
  have hNz : N *ᵥ z = 0 := hT z hzW
  have hNe' : N *ᵥ e = 0 := hNe
  have hNg' : N *ᵥ g = η • e := hNg
  refine forall_not_isComponent_of_family h (le_refl 3) (by omega) hN hskew
    (C' := KCUnitaryTrv.trvGL K 1) (N' := KCUnitaryTrv.trvN K 1 η) (trvElt 1 h η hη) ?_
    ![e, z, g] ?_ ?_ ?_
  · have h1 := truncExp_of_mul_self_eq_zero (n := 1 + 2) (K := K) (by norm_num)
      (trvN_mul_self (K := K) 1 η)
    rw [coe_trvElt]
    exact h1.symm
  · intro i j
    simp only [← hBdef]
    fin_cases i <;> fin_cases j <;>
      simp [KCUnitaryTrv.trvGram_one, hee, heg, hgg, hez, hgz, hze, hzg, hge, hzz]
  · intro j
    fin_cases j <;> simp [trvN_one, Fin.sum_univ_three, hNe', hNz, hNg']
  · exact forall_not_isComponent_trvElt h hp3 (by norm_num) hη hη0

theorem noComp_three (hp3 : 3 < p) {N : Matrix (Fin 3) (Fin 3) K} (hN : N ^ 3 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 3) K) N = -N) (hN0 : N ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer ({(unitaryExp h (le_refl 3) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))} :
        Set (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))),
      ¬ CFSG.IsComponent L := by
  by_cases h2 : N ^ 2 = 0
  · exact noComp_three_sq_zero h hp3 hN hskew (by rw [← pow_two]; exact h2) hN0
  · exact forall_not_isComponent_regular h hp3 (le_refl 3) (by omega)
      KCUnitaryDefining.isPrimeFormGram_one hskew hN h2

theorem noComp_four_sq_zero (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer ({(unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))} :
        Set (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))),
      ¬ CFSG.IsComponent L := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 4) (Fin 4) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := Matrix.mulVecLin N
  have hNl : ∀ x y, B (Nl x) y = -B x (Nl y) := fun x y => gramForm_one_mulVec_skew h hs x y
  have hNl2 : ∀ x, Nl (Nl x) = 0 := fun x => by
    show N *ᵥ (N *ᵥ x) = 0
    rw [mulVec_mulVec, hN2, zero_mulVec]
  have hNl0 : Nl ≠ 0 := by
    intro h0
    apply hN0
    ext i j
    have := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
    simpa [Nl, mulVec_single_one] using this
  obtain ⟨η, hη, hη0⟩ := KCUnitaryHerm.exists_traceZero h
  obtain ⟨e, g, hee, hgg, heg, hNe, hNg, hWdim, hWsep, hcases⟩ :=
    KCUnitaryHerm.exists_sq_zero_structure hp3 hB hBl hNl hNl2 hNl0 hη hη0
  set W := (Submodule.span K {e, g}).orthogonalBilin B with hW
  have hpe : ∀ z ∈ W, B e z = 0 ∧ B g z = 0 := fun z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) e (Submodule.subset_span (by simp)),
      (Submodule.mem_orthogonalBilin.mp hz) g (Submodule.subset_span (by simp))⟩
  have hge : B g e = 1 := by rw [hsymm e g, heg, map_one]
  have hNe' : N *ᵥ e = 0 := hNe
  have hNg' : N *ᵥ g = η • e := hNg
  rcases hcases with hT | ⟨-, e', he'W, g', hg'W, hee', hgg', heg', hNe'', hNg''⟩
  ·
    have hWd : Module.finrank K W = 2 := by rw [hWdim, Module.finrank_fin_fun]
    obtain ⟨E, hE⟩ := h.exists_orthonormal_basis (hB.domRestrict W) hWsep
    have hp0 : 0 < Module.finrank K W := by omega
    have hp1 : 1 < Module.finrank K W := by omega
    obtain ⟨z₀, z₁, hz₀W, hz₁W, hn00, hn01, hn10, hn11⟩ : ∃ z₀ z₁ : Fin 4 → K, z₀ ∈ W ∧ z₁ ∈ W ∧
        B z₀ z₀ = 1 ∧ B z₀ z₁ = 0 ∧ B z₁ z₀ = 0 ∧ B z₁ z₁ = 1 := by
      refine ⟨(E ⟨0, hp0⟩ : Fin 4 → K), (E ⟨1, hp1⟩ : Fin 4 → K), (E ⟨0, hp0⟩).2,
        (E ⟨1, hp1⟩).2, ?_, ?_, ?_, ?_⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨0, hp0⟩ ⟨0, hp0⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨0, hp0⟩ ⟨1, hp1⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨1, hp1⟩ ⟨0, hp0⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨1, hp1⟩ ⟨1, hp1⟩
    obtain ⟨hez₀, hgz₀⟩ := hpe z₀ hz₀W
    obtain ⟨hez₁, hgz₁⟩ := hpe z₁ hz₁W
    have hz₀e : B z₀ e = 0 := by rw [hsymm e z₀, hez₀, map_zero]
    have hz₁e : B z₁ e = 0 := by rw [hsymm e z₁, hez₁, map_zero]
    have hz₀g : B z₀ g = 0 := by rw [hsymm g z₀, hgz₀, map_zero]
    have hz₁g : B z₁ g = 0 := by rw [hsymm g z₁, hgz₁, map_zero]
    have hNz₀ : N *ᵥ z₀ = 0 := hT z₀ hz₀W
    have hNz₁ : N *ᵥ z₁ = 0 := hT z₁ hz₁W
    refine forall_not_isComponent_of_family h (by norm_num) (by omega) hN hskew
      (C' := KCUnitaryTrv.trvGL K 2) (N' := KCUnitaryTrv.trvN K 2 η) (trvElt 2 h η hη) ?_
      ![e, z₀, z₁, g] ?_ ?_ ?_
    · have h1 := truncExp_of_mul_self_eq_zero (n := 2 + 2) (K := K) (by norm_num)
        (trvN_mul_self (K := K) 2 η)
      rw [coe_trvElt]
      exact h1.symm
    · intro i j
      simp only [← hBdef]
      fin_cases i <;> fin_cases j <;>
        simp [KCUnitaryTrv.trvGram_two, hee, heg, hgg, hez₀, hez₁, hgz₀, hgz₁, hz₀e, hz₁e, hz₀g,
          hz₁g, hge, hn00, hn01, hn10, hn11]
    · intro j
      fin_cases j <;> simp [trvN_two, Fin.sum_univ_four, hNe', hNz₀, hNz₁, hNg']
    · exact forall_not_isComponent_trvElt h hp3 (by norm_num) hη hη0
  ·
    obtain ⟨hee'e, hge'⟩ := hpe e' he'W
    obtain ⟨heg'e, hgg'e⟩ := hpe g' hg'W
    have he'e : B e' e = 0 := by rw [hsymm e e', hee'e, map_zero]
    have he'g : B e' g = 0 := by rw [hsymm g e', hge', map_zero]
    have hg'e : B g' e = 0 := by rw [hsymm e g', heg'e, map_zero]
    have hg'g : B g' g = 0 := by rw [hsymm g g', hgg'e, map_zero]
    have hg'e' : B g' e' = 1 := by rw [hsymm e' g', heg', map_one]
    have hNe2 : N *ᵥ e' = 0 := hNe''
    have hNg2 : N *ᵥ g' = η • e' := hNg''
    refine forall_not_isComponent_of_family h (by norm_num) (by omega) hN hskew
      (C' := KCUnitaryNr.nrGLA K) (N' := nrNilA η) (nrEltA h hp3 hη) rfl
      ![e, e', g, g'] ?_ ?_ ?_
    · intro i j
      simp only [← hBdef]
      fin_cases i <;> fin_cases j <;>
        simp [nrGramA, hee, heg, hgg, hee'e, hge', heg'e, hgg'e, hee', hgg',
          heg', hge, he'e, he'g, hg'e, hg'g, hg'e']
    · intro j
      fin_cases j <;> simp [nrNilA, Fin.sum_univ_four, hNe', hNg', hNe2, hNg2]
    · exact forall_not_isComponent_nrEltA h hp3 hη hη0

theorem noComp_four_three_one (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN3 : N * N * N = 0)
    (hN2 : N * N ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer ({(unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))} :
        Set (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))),
      ¬ CFSG.IsComponent L := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 4) (Fin 4) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := Matrix.mulVecLin N
  have hNl : ∀ x y, B (Nl x) y = -B x (Nl y) := fun x y => gramForm_one_mulVec_skew h hs x y
  have hNl3 : ∀ x, Nl (Nl (Nl x)) = 0 := fun x => by
    show N *ᵥ (N *ᵥ (N *ᵥ x)) = 0
    rw [mulVec_mulVec, mulVec_mulVec, hN3, zero_mulVec]
  have hNl2 : ∃ x, Nl (Nl x) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ x, Nl (Nl x) = 0 := fun x => by
      by_contra hne
      exact hcon ⟨x, hne⟩
    apply hN2
    ext i j
    have h1 : (N * N) *ᵥ (Pi.single j 1 : Fin 4 → K) = 0 := by
      rw [← mulVec_mulVec]
      exact hcon' _
    have := congrFun h1 i
    simpa [mulVec_single_one] using this
  obtain ⟨b₀, b₁, b₂, b₃, g00, g01, g02, g03, g11, g12, g13, g22, g23, g33, hNb0, hNb1, hNb2,
    hNb3⟩ := KCUnitaryHerm.exists_three_one_family hp3 hB hBl (Module.finrank_fin_fun K) hNl hNl3
      hNl2
  have g10 : B b₁ b₀ = 0 := by rw [hsymm b₀ b₁, g01, map_zero]
  have g20 : B b₂ b₀ = 1 := by rw [hsymm b₀ b₂, g02, map_one]
  have g21 : B b₂ b₁ = 0 := by rw [hsymm b₁ b₂, g12, map_zero]
  have g30 : B b₃ b₀ = 0 := by rw [hsymm b₀ b₃, g03, map_zero]
  have g31 : B b₃ b₁ = 0 := by rw [hsymm b₁ b₃, g13, map_zero]
  have g32 : B b₃ b₂ = 0 := by rw [hsymm b₂ b₃, g23, map_zero]
  have hNb0' : N *ᵥ b₀ = 0 := hNb0
  have hNb1' : N *ᵥ b₁ = b₀ := hNb1
  have hNb2' : N *ᵥ b₂ = b₁ := hNb2
  have hNb3' : N *ᵥ b₃ = 0 := hNb3
  refine forall_not_isComponent_of_family h (by norm_num) (by omega) hN hskew
    (C' := KCUnitaryNr.nrGLB K) (N' := nrNilB K) (nrEltB h hp3) rfl ![b₀, b₁, b₂, b₃] ?_ ?_ ?_
  · intro i j
    simp only [← hBdef]
    fin_cases i <;> fin_cases j <;>
      simp [nrGramB, g00, g01, g02, g03, g11, g12, g13, g22, g23, g33, g10, g20,
        g21, g30, g31, g32]
  · intro j
    fin_cases j <;> simp [nrNilB, Fin.sum_univ_four, hNb0', hNb1', hNb2', hNb3']
  · exact forall_not_isComponent_nrEltB h hp3

theorem noComp_four (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN0 : N ≠ 0) :
    ∀ L : Subgroup (Subgroup.centralizer ({(unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))} :
        Set (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))),
      ¬ CFSG.IsComponent L := by
  have e2 : N ^ 2 = N * N := pow_two N
  have e3 : N ^ 3 = N * N * N := by rw [pow_succ, pow_two]
  by_cases h3 : N ^ 3 = 0
  · by_cases h2 : N ^ 2 = 0
    · exact noComp_four_sq_zero h hp3 hN hskew (by rw [← e2]; exact h2) hN0
    · exact noComp_four_three_one h hp3 hN hskew (by rw [← e3]; exact h3) (by rw [← e2]; exact h2)
  · exact forall_not_isComponent_regular h hp3 (by norm_num) (by omega)
      KCUnitaryDefining.isPrimeFormGram_one hskew hN h3


theorem unitary_centralizer_component_free (hp3 : 3 < p) {n : ℕ} (hn : n = 3 ∨ n = 4)
    (x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) :
    ∀ L : Subgroup (Subgroup.centralizer
      ({x} : Set (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))),
      ¬ CFSG.IsComponent L := by
  rcases hn with rfl | rfl
  · obtain ⟨N, hN, hskew, hN0, hx⟩ :=
      exists_skew_log_of_pow_eq_one h (le_refl 3) (by omega) x hxp hx1
    subst hx
    exact noComp_three h hp3 hN hskew hN0
  · obtain ⟨N, hN, hskew, hN0, hx⟩ :=
      exists_skew_log_of_pow_eq_one h (by norm_num) (by omega) x hxp hx1
    subst hx
    exact noComp_four h hp3 hN hskew hN0

end UnitaryCases

section Main

open CFSG.Assembly.LowTwoRank

theorem center_eq_bot_of_mulEquiv_centerless {G M : Type*} [Group G] [Group M] (e : G ≃* M)
    (hM : Subgroup.center M = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center M := Subgroup.mem_center_iff.mpr fun m => by
    obtain ⟨t, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz t]
  rw [hM, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot]
  exact e.injective (hez.trans (map_one e).symm)

theorem linear_unitary_three_four_inner_defining_fixed_component_free {ℓ f n : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : 3 < ℓ) (hf : 1 ≤ f) (hn : n = 3 ∨ n = 4) {τ : StatedLieTag}
    (hτ : τ = .PSL ∨ τ = .PSU) {T : Type} [Group T] (hT : StatedClassicalModel T τ n ℓ f)
    (β : MulAut T) (hβ : β ∈ (MulAut.conj : T →* MulAut T).range) (hβℓ : orderOf β = ℓ) :
    ∀ L : Subgroup ((β : T →* T).eqLocus (MonoidHom.id T)), ¬ CFSG.IsComponent L := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨y, rfl⟩ := hβ
  rw [eqLocus_conj_eq_centralizer]
  suffices key : ∀ (M : Type) [Group M] (e : T ≃* M), Subgroup.center M = ⊥ →
      (∀ x : M, x ^ ℓ = 1 → x ≠ 1 →
        ∀ L : Subgroup (Subgroup.centralizer ({x} : Set M)), ¬ CFSG.IsComponent L) →
      ∀ L : Subgroup (Subgroup.centralizer ({y} : Set T)), ¬ CFSG.IsComponent L by
    have hn3 : 3 ≤ n := by omega
    rcases hτ with rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hT
      have : Fintype K := Fintype.ofFinite K
      have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
      let e' : T ≃* LinearFlag.projectiveSL n K := e.trans
        ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
          (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center n K)).symm)
      exact key _ e' (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn3)
        fun x hxp hx1 => linear_centralizer_component_free hℓ hℓ3 hf hn hK x hxp hx1
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hT
      have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
      have hq : ¬(n = 3 ∧ ℓ ^ f = 2) :=
        CFSG.RankThree.PartOne.KCUnitaryDefining.not_three_and_pow_eq_two (n := n) h hℓ3
      let e' : T ≃* UnitaryHigher.primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        e.trans ((CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by omega)).symm.trans
          (ComponentClassification.OutcomeLocal.primeFormOneEquiv h n).symm)
      exact key _ e' (CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h
          CFSG.RankThree.PartOne.KCUnitaryDefining.isPrimeFormGram_one hn3 hq)
        fun x hxp hx1 => unitary_centralizer_component_free h hℓ3 hn x hxp hx1
  intro M _ e hM hcomp
  have hconj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_of_center_eq_bot
    (center_eq_bot_of_mulEquiv_centerless e hM)
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hβℓ
    exact hℓ.one_lt.ne hβℓ
  have hyℓ : y ^ ℓ = 1 := by
    apply hconj
    rw [map_pow, map_one, ← hβℓ, pow_orderOf_eq_one]
  refine forall_not_isComponent_centralizer_of_mulEquiv e y ?_
  exact hcomp (e y) (by rw [← map_pow, hyℓ, map_one])
    fun h1 => hy1 (e.injective (h1.trans (map_one e).symm))

end Main

end CFSG.RankThree.CAInnerDefining
