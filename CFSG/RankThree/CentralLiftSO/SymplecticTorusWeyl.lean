module

public import CFSG.RankThree.CentralLiftSO.SymplecticLift
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.RankThree.CentralLiftSO.Sp

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.CentralExt CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {r : ℕ} {k : Type} [Field k] {E : Type*} [Group E] [Finite k] [Finite E]
  {π : E →* StatedSp r k}

section Values

variable (hS : LargeHyp π)
include hS

theorem weylHom_sLift_of_lt {i : Fin r} (h : i.val + 1 < r) :
    (weylHom hS ⟨sLift π i, sLift_mem i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.sumCongr (Equiv.swap i ⟨i.val + 1, h⟩) (Equiv.swap i ⟨i.val + 1, h⟩) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [sLift_of_lt h, pi_vLiftRho hS]
  exact isLinePerm_rho_sl2W _

theorem weylHom_sLift_of_not_lt {i : Fin r} (h : ¬i.val + 1 < r) :
    (weylHom hS ⟨sLift π i, sLift_mem i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.swap (Sum.inl i) (Sum.inr i) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (sLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [sLift_of_not_lt h, pi_vLift hS]
  exact isLinePerm_lam_sl2W _

theorem weylHom_vLift (i : Fin r) :
    (weylHom hS ⟨vLift π i, vLift_mem hS i⟩ : Equiv.Perm (Fin r ⊕ Fin r)) =
      Equiv.swap (Sum.inl i) (Sum.inr i) := by
  apply weylHom_eq hS
  change IsLinePerm _ (((π (vLift π i) : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [pi_vLift hS]
  exact isLinePerm_lam_sl2W _

theorem weylHom_eq_one_of_mem {n : liftWeyl π} (hn : (n : E) ∈ liftTorus π) :
    weylHom hS n = 1 := by
  obtain ⟨t, ht⟩ := (range_thetaHom hS).ge hn
  apply Subtype.ext
  refine weylHom_eq hS ?_
  change IsLinePerm 1 (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
  rw [← ht, ← MonoidHom.comp_apply π, comp_thetaHom hS]
  exact isLinePerm_torusHom t

theorem liftTorus_le_ker_weylHom : (liftTorus π).subgroupOf (liftWeyl π) ≤ (weylHom hS).ker :=
  fun _ hn => weylHom_eq_one_of_mem hS (Subgroup.mem_subgroupOf.1 hn)

theorem weylHom_surjective : Function.Surjective (weylHom hS) := by
  rintro ⟨σ, hσ⟩
  have hle : signedPermGroup r ≤ (weylHom hS).range.map (signedPermGroup r).subtype :=
    signedPermGroup_le (fun i => ⟨_, ⟨⟨vLift π i, vLift_mem hS i⟩, rfl⟩, weylHom_vLift hS i⟩)
      (fun i h => ⟨_, ⟨⟨sLift π i, sLift_mem i⟩, rfl⟩, weylHom_sLift_of_lt hS h⟩)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hle hσ
  exact ⟨n, Subtype.ext hn⟩

end Values

section Coxeter

variable [((liftTorus π).subgroupOf (liftWeyl π)).Normal]

variable (hS : LargeHyp π)
include hS

theorem sClass_mul_self (i : Fin r) : sClass π i * sClass π i = 1 := by
  rw [sClass, qmk_mul, qmk_eq_one_iff]
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho_mul_self]
    exact hLiftRho_mem hS _ _
  · rw [sLift_of_not_lt h, vLift_mul_self]
    exact hLift_mem _ _

theorem sClass_braid {i j : Fin r} (hij : i.val + 1 = j.val) (hj : j.val + 1 < r) :
    sClass π j * sClass π i * sClass π j = sClass π i * sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
  rw [sLift_of_lt hi, sLift_of_lt hj]
  exact vLiftRho_braid hS _ _ (Fin.ne_of_val_ne (by simp only; omega))

theorem sClass_comm {i j : Fin r} (hij : i.val + 1 < j.val) :
    sClass π i * sClass π j = sClass π j * sClass π i := by
  have hi : i.val + 1 < r := by omega
  simp only [sClass, qmk_mul]
  apply qmk_congr
  rw [sLift_of_lt hi]
  by_cases hj : j.val + 1 < r
  · rw [sLift_of_lt hj]
    exact (commute_vLiftRho_vLiftRho hS _ _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega)) (Fin.ne_of_val_ne (by simp only; omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq
  · rw [sLift_of_not_lt hj]
    exact (commute_vLiftRho_vLift hS _ (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp only; omega))).eq

theorem sClass_long {i j : Fin r} (hij : i.val + 1 = j.val) (hj : ¬j.val + 1 < r) :
    sClass π i * sClass π j * sClass π i * (sClass π i * sClass π j * sClass π i) = 1 ∧
      sClass π i * sClass π j * sClass π i * sClass π j =
        sClass π j * (sClass π i * sClass π j * sClass π i) := by
  have hi : i.val + 1 < r := by omega
  have hinv : (sClass π i)⁻¹ = sClass π i := inv_eq_of_mul_eq_one_right (sClass_mul_self hS i)
  have hv : sClass π i * sClass π j * sClass π i =
      (QuotientGroup.mk ⟨vLift π i, vLift_mem hS i⟩ :
        liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) := by
    have h3 : sClass π i * sClass π j * sClass π i =
        sClass π i * sClass π j * (sClass π i)⁻¹ := by rw [hinv]
    rw [h3]
    simp only [sClass, qmk_mul, qmk_inv]
    apply qmk_congr
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij.symm
    rw [sLift_of_lt hi, sLift_of_not_lt hj]
    exact vLiftRho_conj_vLift hS _
  rw [hv]
  constructor
  · rw [qmk_mul, qmk_eq_one_iff, vLift_mul_self]
    exact hLift_mem _ _
  · simp only [sClass, qmk_mul]
    apply qmk_congr
    rw [sLift_of_not_lt hj]
    exact (commute_vLift_vLift hS (Fin.ne_of_val_ne (by omega))).eq

private theorem isLiftable_sClass :
    (CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)).IsLiftable (sClass π) := by
  have key : ∀ i j : Fin r, i < j → (sClass π i * sClass π j) ^
      (CFSG.LieType.RootSystem.coxeterMatrix
        (CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r)) i j = 1 := by
    intro i j hij
    have hij' : i.val < j.val := hij
    by_cases hadj : i.val + 1 = j.val
    · by_cases hj : j.val + 1 < r
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_short r hadj hj]
        exact pow_three_eq_one (sClass_mul_self hS i) (sClass_mul_self hS j)
          (sClass_braid hS hadj hj)
      · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_succ_long r hadj hj]
        exact pow_four_eq_one (sClass_mul_self hS j) (sClass_long hS hadj hj).1
          (sClass_long hS hadj hj).2
    · rw [CFSG.LieType.Universal.Symplectic.coxeterMatrix_of_far r hij.ne hadj (by omega)]
      exact pow_two_eq_one_of_commute (sClass_mul_self hS i) (sClass_mul_self hS j)
        (sClass_comm hS (by omega))
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact key i j h
  · rw [CoxeterMatrix.diagonal, pow_one]
    exact sClass_mul_self hS i
  · rw [CoxeterMatrix.symmetric]
    exact pow_eq_one_comm (key j i h)

end Coxeter

section Kernel

variable (hS : LargeHyp π)
include hS

theorem normal_liftTorus_subgroupOf : ((liftTorus π).subgroupOf (liftWeyl π)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer liftTorus_le_liftWeyl).2 (liftWeyl_le_normalizer hS)

theorem ker_weylHom_le : (weylHom hS).ker ≤ (liftTorus π).subgroupOf (liftWeyl π) := by
  have := normal_liftTorus_subgroupOf hS
  set hA := CFSG.LieType.Universal.Symplectic.isFiniteType_cartanC r
  set cs := (CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem
  set L := cs.lift ⟨sClass π, isLiftable_sClass hS⟩ with hL
  set φbar := QuotientGroup.lift _ (weylHom hS) (liftTorus_le_ker_weylHom hS) with hφbar
  have hsimple : ∀ i, epsAct ((φbar (L (cs.simple i)) : signedPermGroup r) :
      Equiv.Perm (Fin r ⊕ Fin r)) = CFSG.LieType.Universal.Symplectic.stdRefl r i := by
    intro i
    rw [hL, CoxeterSystem.lift_apply_simple, sClass, hφbar, QuotientGroup.lift_mk]
    funext e
    by_cases h : i.val + 1 < r
    · rw [weylHom_sLift_of_lt hS h, epsAct_sumCongr_swap,
        CFSG.LieType.Universal.Symplectic.stdRefl_of_lt r h]
    · rw [weylHom_sLift_of_not_lt hS h, epsAct_swap_inl_inr,
        CFSG.LieType.Universal.Symplectic.stdRefl_of_not_lt r h]
  have hact : ∀ w v, CFSG.LieType.Universal.Symplectic.toStd r
      (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (φbar (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v) := by
    intro w
    refine cs.simple_induction_left (p := fun w => ∀ v,
      CFSG.LieType.Universal.Symplectic.toStd r (CFSG.LieType.RootSystem.weylAction hA w v) =
        epsAct (φbar (L w) : Equiv.Perm (Fin r ⊕ Fin r))
          (CFSG.LieType.Universal.Symplectic.toStd r v)) w ?_ ?_
    · intro v
      rw [map_one, map_one, map_one]
      rfl
    · intro w i ih v
      rw [CFSG.LieType.RootSystem.weylAction_mul_apply,
        CFSG.LieType.RootSystem.weylAction_simple,
        CFSG.LieType.Universal.Symplectic.toStd_reflection, ih, map_mul, map_mul,
        Subgroup.coe_mul, epsAct_mul (φbar (L w)).2, hsimple]
  have hinj : ∀ w, φbar (L w) = 1 → w = 1 := by
    intro w hw
    apply CFSG.LieType.RootSystem.weylAction_injective hA
    rw [map_one]
    refine LinearMap.ext fun v => CFSG.LieType.Universal.Symplectic.toStd_injective r ?_
    rw [hact, hw, Module.End.one_apply]
    rfl
  have hsurj : Function.Surjective L := by
    have key : ∀ x (hx : x ∈ liftWeyl π),
        (QuotientGroup.mk ⟨x, hx⟩ : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π)) ∈
          L.range := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨i, rfl⟩
        · exact ⟨1, by rw [map_one]; exact ((qmk_eq_one_iff _).2 hx).symm⟩
        · exact ⟨cs.simple i, CoxeterSystem.lift_apply_simple _ _ i⟩
      | one => exact L.range.one_mem
      | mul x y hx hy ihx ihy =>
        exact mul_mem ihx ihy
      | inv x hx ihx =>
        exact inv_mem ihx
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact key x hx
  intro n hn
  obtain ⟨w, hw⟩ := hsurj (QuotientGroup.mk n)
  have h1 : φbar (L w) = 1 := by
    rw [hw, hφbar, QuotientGroup.lift_mk]
    exact hn
  rw [hinj w h1, map_one] at hw
  exact (QuotientGroup.eq_one_iff n).1 hw.symm

theorem ker_weylHom : (weylHom hS).ker = (liftTorus π).subgroupOf (liftWeyl π) :=
  le_antisymm (ker_weylHom_le hS) (liftTorus_le_ker_weylHom hS)

theorem injective_pi_comp : Function.Injective (π.comp (liftWeyl π).subtype) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hn' : π n = 1 := hn
  have hw : weylHom hS n = 1 := by
    apply Subtype.ext
    refine weylHom_eq hS ?_
    change IsLinePerm 1 (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
    rw [hn']
    exact isLinePerm_one
  have hH : (n : E) ∈ liftTorus π := Subgroup.mem_subgroupOf.1 (ker_weylHom_le hS hw)
  obtain ⟨t, ht⟩ := (range_thetaHom hS).ge hH
  have h1 : torusHom t = 1 := by
    rw [← comp_thetaHom hS, MonoidHom.comp_apply, ht]
    exact hn'
  have ht1 : t = 1 := torusHom_injective (h1.trans (map_one _).symm)
  apply Subtype.ext
  rw [← ht, ht1, map_one]
  rfl

end Kernel

noncomputable def liftTorusEquiv (hS : LargeHyp π) : (Fin r → kˣ) ≃* liftTorus π :=
  (MonoidHom.ofInjective (thetaHom_injective hS)).trans (MulEquiv.subgroupCongr (range_thetaHom hS))

theorem coe_liftTorusEquiv (hS : LargeHyp π) (t : Fin r → kˣ) :
    ((liftTorusEquiv hS t : liftTorus π) : E) = thetaHom hS t := by
  rw [liftTorusEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]

noncomputable def thetaEquiv (hS : LargeHyp π) : torus r k ≃* liftTorus π :=
  (torusEquiv (r := r) (k := k)).symm.trans (liftTorusEquiv hS)

theorem thetaEquiv_torusHom (hS : LargeHyp π) (t : Fin r → kˣ) :
    (thetaEquiv hS ⟨torusHom t, torusHom_mem_torus t⟩ : E) = thetaHom hS t := by
  have h : (⟨torusHom t, torusHom_mem_torus t⟩ : torus r k) = torusEquiv t :=
    Subtype.ext (coe_torusEquiv t).symm
  rw [h, thetaEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, coe_liftTorusEquiv]

theorem pi_thetaEquiv (hS : LargeHyp π) (x : torus r k) : π (thetaEquiv hS x) = x := by
  obtain ⟨_, ⟨t, rfl⟩⟩ := x
  rw [thetaEquiv_torusHom, ← MonoidHom.comp_apply π, comp_thetaHom hS]

@[expose] noncomputable def weylQuotientEquiv (hS : LargeHyp π)
    [((liftTorus π).subgroupOf (liftWeyl π)).Normal] :
    liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* signedPermGroup r :=
  (QuotientGroup.quotientMulEquivOfEq (ker_weylHom hS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (weylHom hS) (weylHom_surjective hS))

theorem weylQuotientEquiv_mk (hS : LargeHyp π) [((liftTorus π).subgroupOf (liftWeyl π)).Normal]
    (n : liftWeyl π) : weylQuotientEquiv hS n = weylHom hS n :=
  rfl

theorem sLift_sq_mem (hS : LargeHyp π) (i : Fin r) : sLift π i ^ 2 ∈ liftTorus π := by
  rw [sq]
  by_cases h : i.val + 1 < r
  · rw [sLift_of_lt h, vLiftRho_mul_self]
    exact hLiftRho_mem hS _ _
  · rw [sLift_of_not_lt h, vLift_mul_self]
    exact hLift_mem _ _

theorem odd_symplectic_central_large_prime_lifted_torus_and_weyl {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {r : ℕ} (_hr : 1 ≤ r) {E : Type*} [Group E] [Finite E]
    {π : E →* StatedSp r k} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    IsMulCommutative (liftTorus π) ∧
    (∀ (i j : Fin r) (hij : i ≠ j) (a : kˣ),
      hLiftRho π i j hij a = hLift π i a * (hLift π j a)⁻¹) ∧
    (∃ θ : torus r k ≃* liftTorus π,
      (∀ t : Fin r → kˣ, (θ ⟨torusHom t, torusHom_mem_torus t⟩ : E) =
        (List.ofFn fun i => hLift π i (t i)).prod) ∧
      ∀ x : torus r k, π (θ x) = x) ∧
    liftTorus π ≤ liftWeyl π ∧
    liftWeyl π ≤ Subgroup.normalizer (liftTorus π : Set E) ∧
    (∀ i : Fin r, vLift π i ∈ liftWeyl π) ∧
    (∃ φ : liftWeyl π →* signedPermGroup r,
      (∀ (n : liftWeyl π) (x y : Fin r ⊕ Fin r),
        (((π n : StatedSp r k) : GL (Fin r ⊕ Fin r) k) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) y x ≠ 0 ↔
          y = (φ n : Equiv.Perm (Fin r ⊕ Fin r)) x) ∧
      Function.Surjective φ ∧ φ.ker = (liftTorus π).subgroupOf (liftWeyl π) ∧
      ∃ _ : ((liftTorus π).subgroupOf (liftWeyl π)).Normal,
        ∃ e : liftWeyl π ⧸ (liftTorus π).subgroupOf (liftWeyl π) ≃* signedPermGroup r,
          ∀ n : liftWeyl π, e n = φ n) ∧
    Function.Injective (π.comp (liftWeyl π).subtype) ∧
    ∀ i : Fin r, sLift π i ^ 2 ∈ liftTorus π := by
  have hS : LargeHyp π := ⟨hk, ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩⟩
  have hN := normal_liftTorus_subgroupOf hS
  refine ⟨⟨⟨fun x y => Subtype.ext (liftTorus_commute hS x.2 y.2).eq⟩⟩,
    fun i j hij a => hLiftRho_eq hS hij a,
    ⟨thetaEquiv hS, fun t => by rw [thetaEquiv_torusHom, thetaHom_apply], pi_thetaEquiv hS⟩,
    liftTorus_le_liftWeyl, liftWeyl_le_normalizer hS, vLift_mem hS,
    ⟨weylHom hS, fun n x y => isLinePerm_weylHom hS n x y, weylHom_surjective hS,
      ker_weylHom hS, hN, weylQuotientEquiv hS, weylQuotientEquiv_mk hS⟩,
    injective_pi_comp hS, sLift_sq_mem hS⟩

end CFSG.RankThree.CentralLiftSO.Sp
