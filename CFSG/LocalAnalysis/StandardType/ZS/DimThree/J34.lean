module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Inner
public import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame
import CFSG.Quasithin.EmptyFaithful.A38c15IrrBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.PSL2Table.BlocksProduct
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.LieType.SteinbergBRTwoRankBound
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.Defs
import CFSG.RankThree.PartOne.S12.Hyp
import CFSG.RankThree.PartOne.S12.InputsLinear
import CFSG.Sporadic.J4Base
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.ZS.DimThree

open scoped Matrix
open Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)
open CFSG.RankThree.PartOne.N1322
open CFSG.QuasithinUnique.Setup.Family (GL32)

private theorem mat_A0m_mul_invol_pow_twelve_z7 :
    ∀ B : Mat2, B.det = 1 → B * B = 1 → (A0m * B) ^ 12 = 1 := by
  decide +kernel

private theorem gl32_invol_mul_pow_twelve_z7 (a b : GL32) (ha : a * a = 1)
    (hb : b * b = 1) : (a * b) ^ 12 = 1 := by
  by_cases ha1 : a = 1
  · subst a
    rw [one_mul, show (12 : ℕ) = 2 * 6 from rfl, pow_mul, pow_two, hb, one_pow]
  · have hAdet : (a : Mat2).det = 1 := det_GL32 a
    have hA2 : (a : Mat2) * (a : Mat2) = 1 := by
      simpa using congrArg (fun u : GL32 => (u : Mat2)) ha
    have hA1 : (a : Mat2) ≠ 1 := fun h =>
      ha1 (Units.ext (by simpa using h))
    obtain ⟨K, hKdet, hKA⟩ := mat_conj_invol (a : Mat2) hAdet hA2 hA1
    let k : GL32 := matUnit K hKdet
    let a0 : GL32 := matUnit A0m A0m_det
    have hk : (k : Mat2) = K := matUnit_val K hKdet
    have ha0 : (a0 : Mat2) = A0m := matUnit_val A0m A0m_det
    have hka : k * a0 = a * k := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hk, ha0]
      exact hKA
    let b' : GL32 := k⁻¹ * b * k
    have hb'2u : b' * b' = 1 := by
      show (k⁻¹ * b * k) * (k⁻¹ * b * k) = 1
      rw [show (k⁻¹ * b * k) * (k⁻¹ * b * k) = k⁻¹ * (b * b) * k by group, hb]
      group
    have hb'det : (b' : Mat2).det = 1 := det_GL32 b'
    have hb'2 : (b' : Mat2) * (b' : Mat2) = 1 := by
      simpa using congrArg (fun u : GL32 => (u : Mat2)) hb'2u
    have hcheck := mat_A0m_mul_invol_pow_twelve_z7 (b' : Mat2) hb'det hb'2
    have h12 : ((a0 * b') ^ 12 : GL32) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mul, ha0]
      exact hcheck
    have haeq : a = k * a0 * k⁻¹ := by
      rw [hka]
      group
    have hab : a * b = k * (a0 * b') * k⁻¹ := by
      rw [haeq]
      show k * a0 * k⁻¹ * b = k * (a0 * b') * k⁻¹
      rw [show b' = k⁻¹ * b * k from rfl]
      group
    calc (a * b) ^ 12 = k * (a0 * b') ^ 12 * k⁻¹ := by rw [hab, conj_pow]
    _ = 1 := by rw [h12]; group

private theorem gl32_invol_order_le_four_z7 (a b : GL32) (ha : a * a = 1)
    (hb : b * b = 1) : orderOf (a * b) ≤ 4 := by
  have h12 := gl32_invol_mul_pow_twelve_z7 a b ha hb
  have hd12 : orderOf (a * b) ∣ 12 := orderOf_dvd_of_pow_eq_one h12
  rcases G32_orders (a * b) with h4 | h3 | h7
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
  · exact le_trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3))
      (by norm_num)
  · have hd7 : orderOf (a * b) ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    have hd1 : orderOf (a * b) ∣ 1 := by
      simpa using Nat.dvd_gcd hd12 hd7
    rw [Nat.dvd_one] at hd1
    rw [hd1]
    norm_num

private def B0m_z7 : Mat2 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

private theorem A0m_sq_z7 : A0m * A0m = 1 := by decide

private theorem A0m_ne_one_z7 : A0m ≠ 1 := by decide

private theorem B0m_det_z7 : B0m_z7.det = 1 := by decide

private theorem B0m_sq_z7 : B0m_z7 * B0m_z7 = 1 := by decide

private theorem B0m_ne_one_z7 : B0m_z7 ≠ 1 := by decide

private theorem A0m_mul_B0m_data_z7 :
    (A0m * B0m_z7) ^ 4 = 1 ∧ (A0m * B0m_z7) ^ 3 ≠ 1 ∧
      (A0m * B0m_z7) ^ 2 ≠ 1 ∧ A0m * B0m_z7 ≠ 1 := by
  decide

private theorem gl32_A0m_mul_B0m_order_z7 :
    orderOf (matUnit A0m A0m_det * matUnit B0m_z7 B0m_det_z7) = 4 := by
  set x : GL32 := matUnit A0m A0m_det * matUnit B0m_z7 B0m_det_z7 with hx
  obtain ⟨h4, h3, h2, h1⟩ := A0m_mul_B0m_data_z7
  have lift : ∀ n : ℕ, x ^ n = 1 ↔ (A0m * B0m_z7) ^ n = 1 := by
    intro n
    constructor
    · intro h
      have := congrArg (fun u : GL32 => (u : Mat2)) h
      simpa [hx, Units.val_pow_eq_pow_val, Units.val_mul, matUnit_val] using this
    · intro h
      apply Units.ext
      rw [hx, Units.val_pow_eq_pow_val, Units.val_mul, matUnit_val, matUnit_val]
      exact h
  refine (orderOf_eq_iff (by norm_num : 0 < 4)).mpr ⟨(lift 4).mpr h4, ?_⟩
  intro m hm4 hm0
  interval_cases m
  · exact fun h => h1 (by simpa using (lift 1).mp h)
  · exact fun h => h2 ((lift 2).mp h)
  · exact fun h => h3 ((lift 3).mp h)

private noncomputable def a0_z7 : GL32 := matUnit A0m A0m_det

private noncomputable def b0_z7 : GL32 := matUnit B0m_z7 B0m_det_z7

private theorem a0_z7_sq : a0_z7 * a0_z7 = 1 := by
  apply Units.ext
  rw [Units.val_mul, show (a0_z7 : Mat2) = A0m from matUnit_val _ _]
  simpa using A0m_sq_z7

private theorem a0_z7_ne_one : a0_z7 ≠ 1 := by
  intro h
  apply A0m_ne_one_z7
  have := congrArg (fun u : GL32 => (u : Mat2)) h
  simpa [a0_z7, matUnit_val] using this

private theorem b0_z7_sq : b0_z7 * b0_z7 = 1 := by
  apply Units.ext
  rw [Units.val_mul, show (b0_z7 : Mat2) = B0m_z7 from matUnit_val _ _]
  simpa using B0m_sq_z7

private theorem b0_z7_ne_one : b0_z7 ≠ 1 := by
  intro h
  apply B0m_ne_one_z7
  have := congrArg (fun u : GL32 => (u : Mat2)) h
  simpa [b0_z7, matUnit_val] using this

private theorem a0_z7_mul_b0_z7_order : orderOf (a0_z7 * b0_z7) = 4 :=
  gl32_A0m_mul_B0m_order_z7

private def rfr_g0m : Mat2 := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private def rfr_g1m : Mat2 := !![0, 1, 0; 1, 0, 0; 1, 1, 1]

private def rfr_g2m : Mat2 := !![0, 1, 1; 0, 1, 0; 1, 1, 0]

private def rfr_gum : Mat2 := !![1, 0, 0; 1, 1, 0; 1, 0, 1]

private theorem rfr_g0m_det : rfr_g0m.det = 1 := by decide

private theorem rfr_g1m_det : rfr_g1m.det = 1 := by decide

private theorem rfr_g2m_det : rfr_g2m.det = 1 := by decide

private theorem rfr_gum_det : rfr_gum.det = 1 := by decide

private noncomputable def rfr_g0 : GL32 := matUnit rfr_g0m rfr_g0m_det

private noncomputable def rfr_g1 : GL32 := matUnit rfr_g1m rfr_g1m_det

private noncomputable def rfr_g2 : GL32 := matUnit rfr_g2m rfr_g2m_det

private noncomputable def rfr_gu : GL32 := matUnit rfr_gum rfr_gum_det

private theorem rfr_g0_val : (rfr_g0 : Mat2) = rfr_g0m := matUnit_val _ _

private theorem rfr_g1_val : (rfr_g1 : Mat2) = rfr_g1m := matUnit_val _ _

private theorem rfr_g2_val : (rfr_g2 : Mat2) = rfr_g2m := matUnit_val _ _

private theorem rfr_gu_val : (rfr_gu : Mat2) = rfr_gum := matUnit_val _ _

private theorem rfr_g0_sq : rfr_g0 * rfr_g0 = 1 := by
  apply Units.ext; rw [Units.val_mul, rfr_g0_val]; decide

private theorem rfr_g1_sq : rfr_g1 * rfr_g1 = 1 := by
  apply Units.ext; rw [Units.val_mul, rfr_g1_val]; decide

private theorem rfr_g2_sq : rfr_g2 * rfr_g2 = 1 := by
  apply Units.ext; rw [Units.val_mul, rfr_g2_val]; decide

private theorem rfr_gu_sq : rfr_gu * rfr_gu = 1 := by
  apply Units.ext; rw [Units.val_mul, rfr_gu_val]; decide

private theorem rfr_matUnit_ne_one {M : Mat2} (hM : M.det = 1) (h : M ≠ 1) :
    matUnit M hM ≠ 1 := by
  intro h1
  exact h (by simpa [matUnit_val] using congrArg (fun x : GL32 => (x : Mat2)) h1)

private theorem rfr_g0_ne : rfr_g0 ≠ 1 := rfr_matUnit_ne_one rfr_g0m_det (by decide)

private theorem rfr_g1_ne : rfr_g1 ≠ 1 := rfr_matUnit_ne_one rfr_g1m_det (by decide)

private theorem rfr_g2_ne : rfr_g2 ≠ 1 := rfr_matUnit_ne_one rfr_g2m_det (by decide)

private theorem rfr_gu_ne : rfr_gu ≠ 1 := rfr_matUnit_ne_one rfr_gum_det (by decide)

private theorem rfr_orderOf_matUnit_mul {M N : Mat2} (hM : M.det = 1) (hN : N.det = 1) {q : ℕ}
    (hq : 0 < q) (hpow : (M * N) ^ q = 1)
    (hmin : ∀ m, 0 < m → m < q → (M * N) ^ m ≠ 1) :
    orderOf (matUnit M hM * matUnit N hN) = q := by
  set x : GL32 := matUnit M hM * matUnit N hN with hx
  have lift : ∀ n : ℕ, x ^ n = 1 ↔ (M * N) ^ n = 1 := by
    intro n
    constructor
    · intro h
      have := congrArg (fun g : GL32 => (g : Mat2)) h
      simpa [hx, Units.val_pow_eq_pow_val, Units.val_mul, matUnit_val] using this
    · intro h
      apply Units.ext
      rw [hx, Units.val_pow_eq_pow_val, Units.val_mul, matUnit_val, matUnit_val]
      exact h
  exact (orderOf_eq_iff hq).mpr
    ⟨(lift q).mpr hpow, fun m hmq hm => fun h => hmin m hm hmq ((lift m).mp h)⟩

private theorem rfr_g0_mul_g1_order : orderOf (rfr_g0 * rfr_g1) = 4 := by
  refine rfr_orderOf_matUnit_mul rfr_g0m_det rfr_g1m_det (by norm_num) (by decide) ?_
  intro m hm hm4
  interval_cases m <;> decide

private theorem rfr_g1_mul_g2_order : orderOf (rfr_g1 * rfr_g2) = 3 := by
  refine rfr_orderOf_matUnit_mul rfr_g1m_det rfr_g2m_det (by norm_num) (by decide) ?_
  intro m hm hm3
  interval_cases m <;> decide

private theorem rfr_g0_mul_g2_order : orderOf (rfr_g0 * rfr_g2) = 2 := by
  refine rfr_orderOf_matUnit_mul rfr_g0m_det rfr_g2m_det (by norm_num) (by decide) ?_
  intro m hm hm2
  (interval_cases m; decide)

private theorem rfr_g0_mul_gu_order : orderOf (rfr_g0 * rfr_gu) = 3 := by
  refine rfr_orderOf_matUnit_mul rfr_g0m_det rfr_gum_det (by norm_num) (by decide) ?_
  intro m hm hm3
  interval_cases m <;> decide

private theorem rfr_g1_mul_gu_order : orderOf (rfr_g1 * rfr_gu) = 3 := by
  refine rfr_orderOf_matUnit_mul rfr_g1m_det rfr_gum_det (by norm_num) (by decide) ?_
  intro m hm hm3
  interval_cases m <;> decide

private noncomputable def rfr_gsig : GL32 := (rfr_g2 * rfr_g1) * rfr_g0 * (rfr_g2 * rfr_g1)⁻¹

private noncomputable def rfr_gconj : GL32 := rfr_gsig * (rfr_g1 * rfr_g2 * rfr_g1) * rfr_gsig⁻¹

private theorem rfr_g21_cube : (rfr_g2 * rfr_g1) ^ 3 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, rfr_g2_val, rfr_g1_val]
  decide

private theorem rfr_g21_inv : (rfr_g2 * rfr_g1)⁻¹ = (rfr_g2 * rfr_g1) ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact rfr_g21_cube)

private theorem rfr_gsig_sq : rfr_gsig * rfr_gsig = 1 := by
  calc rfr_gsig * rfr_gsig = (rfr_g2 * rfr_g1) * (rfr_g0 * rfr_g0) * (rfr_g2 * rfr_g1)⁻¹ := by
        unfold rfr_gsig; group
    _ = 1 := by rw [rfr_g0_sq]; group

private theorem rfr_gsig_inv : rfr_gsig⁻¹ = rfr_gsig := inv_eq_of_mul_eq_one_right rfr_gsig_sq

private theorem rfr_gu_commute_conj : Commute rfr_gu rfr_gconj := by
  rw [commute_iff_eq]
  unfold rfr_gconj
  rw [rfr_gsig_inv, show rfr_gsig = (rfr_g2 * rfr_g1) * rfr_g0 * (rfr_g2 * rfr_g1) ^ 2 by
    unfold rfr_gsig; rw [rfr_g21_inv]]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, rfr_g0_val, rfr_g1_val, rfr_g2_val,
    rfr_gu_val]
  decide

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem decomp_of_mem_z7 (hp : p ≠ 2) (hp7ne : p ≠ 7)
    {H : Subgroup (GL (Fin 3) (ZMod p))} [Group.IsPerfect H]
    (hirr : IsIrreducibleMatrixRep H.subtype) (e32 : H ≃* GL32)
    {G : Subgroup (GL (Fin 3) (ZMod p))}
    (hn : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∀ t ∈ G, ∃ h₀ ∈ H, ∃ z : GL (Fin 3) (ZMod p),
      (∀ x ∈ H, z * x = x * z) ∧ t = h₀ * z := by
  intro t htG
  have hdetH : ∀ y ∈ H, (y : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 :=
    fun y hy => N1322.det_eq_one_of_perfect hy
  have hg : ∀ x ∈ H, t * x * t⁻¹ ∈ H := fun x hx => hn t htG x hx
  have hg' : ∀ x ∈ H, t⁻¹ * x * t ∈ H := by
    intro x hx
    simpa using hn t⁻¹ (G.inv_mem htG) x hx
  obtain ⟨h, hh, z, hz, htz⟩ :=
    CFSG.Quasithin.A38c15.normalizes_gl32 hp hp7ne hdetH hirr e32 hg hg'
  exact ⟨h, hh, z, fun x hx => ((Subgroup.mem_center_iff.mp hz) x).symm, htz⟩

theorem excData_of_glThreeTwo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e32 : H ≃* GL (Fin 3) (ZMod 2))
    (hp7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) : ExcData p .J34 A := by
  have hp7ne : p ≠ 7 := by
    rintro rfl
    rcases hp7 with h | h | h <;> norm_num at h
  let : Group.IsPerfect GL32 := isPerfect_GL32
  have hcard : 2 * Nat.card GL32 = ExcRow.J34.ord := by
    rw [CFSG.LieType.SteinbergBR.AutGL32.card_GL32]
    decide
  have hZK : Subgroup.center GL32 = ⊥ :=
    CFSG.QuasithinUnique.Setup.Family.center_GL32
  have hcen : 2 = ExcRow.J34.cen := by decide
  let : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e32.symm.toMonoidHom) e32.symm.surjective
  have hdec : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z :=
    fun t ht _ => decomp_of_mem_z7 hp hp7ne hirr e32 hn t ht
  have hle : ∀ a b : GL32, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
      orderOf (a * b) ≤ ExcRow.J34.dmax := by
    intro a b ha _ hb _
    simpa [ExcRow.dmax] using gl32_invol_order_le_four_z7 a b ha hb
  have hatt : ∃ a b : GL32, a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      orderOf (a * b) = ExcRow.J34.dmax :=
    ⟨a0_z7, b0_z7, a0_z7_sq, a0_z7_ne_one, b0_z7_sq, b0_z7_ne_one,
      by simpa [ExcRow.dmax] using a0_z7_mul_b0_z7_order⟩
  have hone : ∀ a b : GL32, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → IsConj a b :=
    fun a b ha ha1 hb hb1 => isConj_iff.mpr (G32_conj_inv a b ha ha1 hb hb1)
  exact excData_of_inner_of_mulEquiv hp e hR hI hHG hirr hdec e32 ExcRow.J34 hp7ne rfl
    hcard hZK hcen G32_noncomm hle hatt hone

private lemma rfr_g32_pull_invol {H : Subgroup (GL (Fin 3) (ZMod p))}
    (e32 : H ≃* GL32) {v : GL32} (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ((e32.symm v : H) : GL (Fin 3) (ZMod p)) * ((e32.symm v : H) : GL (Fin 3) (ZMod p)) = 1 ∧
      ((e32.symm v : H) : GL (Fin 3) (ZMod p)) ≠ 1 := by
  constructor
  · have h : (e32.symm v : H) * (e32.symm v : H) = 1 := by
      apply e32.injective
      rw [map_mul, map_one, e32.apply_symm_apply]
      exact hv2
    simpa using congrArg Subtype.val h
  · intro h
    apply hv1
    have h' : (e32.symm v : H) = 1 := Subtype.ext h
    simpa using congrArg e32 h'

private lemma rfr_g32_lift (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    [Group.IsPerfect H] (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a)
    (hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹)
    (e32 : H ≃* GL32) {v : GL32} (hv2 : v * v = 1) (hv1 : v ≠ 1) :
    ∃ x ∈ A, IsRefl p x ∧ autGL e x = (-1) * ((e32.symm v : H) : GL (Fin 3) (ZMod p)) := by
  obtain ⟨ha2, ha1⟩ := rfr_g32_pull_invol e32 hv2 hv1
  exact exists_isRefl_of_involution hp e hR hI hHG hirr hnc hinn (e32.symm v).2 ha2 ha1

private lemma rfr_g32_order_lift (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {H : Subgroup (GL (Fin 3) (ZMod p))} (e32 : H ≃* GL32)
    {x y : U ≃ₗ[ZMod p] U} {v w : GL32}
    (hx : autGL e x = (-1) * ((e32.symm v : H) : GL (Fin 3) (ZMod p)))
    (hy : autGL e y = (-1) * ((e32.symm w : H) : GL (Fin 3) (ZMod p))) {q : ℕ}
    (hv : orderOf (v * w) = q) : orderOf (x * y) = q := by
  rw [orderOf_mul_eq_of_autGL_eq_neg_mul e hx hy]
  have hcoe : ((e32.symm v : H) : GL (Fin 3) (ZMod p)) *
      ((e32.symm w : H) : GL (Fin 3) (ZMod p)) =
        ((e32.symm (v * w) : H) : GL (Fin 3) (ZMod p)) := by
    have hH : (e32.symm v : H) * (e32.symm w : H) = e32.symm (v * w) := by
      rw [map_mul]
    exact congrArg Subtype.val hH
  rw [hcoe, Subgroup.orderOf_coe]
  exact (MulEquiv.orderOf_eq e32.symm (v * w)).trans hv

private lemma rfr_g32_conj_pull {H : Subgroup (GL (Fin 3) (ZMod p))} (e32 : H ≃* GL32) :
    e32 ((((e32.symm rfr_g2 * e32.symm rfr_g1) * e32.symm rfr_g0 *
        (e32.symm rfr_g2 * e32.symm rfr_g1)⁻¹) *
      (e32.symm rfr_g1 * e32.symm rfr_g2 * e32.symm rfr_g1) *
      ((e32.symm rfr_g2 * e32.symm rfr_g1) * e32.symm rfr_g0 *
        (e32.symm rfr_g2 * e32.symm rfr_g1)⁻¹)⁻¹)) = rfr_gconj := by
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, rfr_gconj, rfr_gsig]

private lemma rfr_g32_conj_map (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {s0 s1 s2 : U ≃ₗ[ZMod p] U} {w0 w1 w2 : GL (Fin 3) (ZMod p)}
    (h0 : autGL e s0 = (-1) * w0) (h1 : autGL e s1 = (-1) * w1)
    (h2 : autGL e s2 = (-1) * w2) :
    autGL e (((s2 * s1) * s0 * (s2 * s1)⁻¹) * (s1 * s2 * s1) *
        ((s2 * s1) * s0 * (s2 * s1)⁻¹)⁻¹) =
      (-1) * (((w2 * w1) * w0 * (w2 * w1)⁻¹) * (w1 * w2 * w1) *
        ((w2 * w1) * w0 * (w2 * w1)⁻¹)⁻¹) := by
  simp only [map_mul, map_inv, h0, h1, h2, mul_inv_rev, inv_neg, inv_one]
  simp only [N1322.neg_one_comm, mul_assoc, N1322.neg_one_mul_neg_one, mul_one]

private lemma rfr_g32_commute_conj_lift (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {H : Subgroup (GL (Fin 3) (ZMod p))} (e32 : H ≃* GL32)
    {a y : U ≃ₗ[ZMod p] U}
    (ha : autGL e a = (-1) * ((e32.symm rfr_gu : H) : GL (Fin 3) (ZMod p)))
    (hy : autGL e y = (-1) * ((e32.symm rfr_gconj : H) : GL (Fin 3) (ZMod p)))
    (hcommGL : Commute rfr_gu rfr_gconj) : Commute a y :=
  (commute_iff_of_autGL_eq_neg_mul e ha hy).mpr (by
    have hH : Commute (e32.symm rfr_gu) (e32.symm rfr_gconj) := by
      rw [commute_iff_eq] at hcommGL ⊢
      apply e32.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hcommGL
    rw [commute_iff_eq]
    simpa using congrArg Subtype.val hH)

theorem j34Frame_of_glThreeTwo (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ A.map (autGL e).toMonoidHom)
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (e32 : H ≃* GL (Fin 3) (ZMod 2))
    (hp7 : p ≠ 7) : J34Frame p A := by
  let : Group.IsPerfect GL32 := isPerfect_GL32
  let : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := e32.symm.toMonoidHom) e32.symm.surjective
  have hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := G32_noncomm
    refine ⟨(e32.symm x : GL (Fin 3) (ZMod p)), (e32.symm x).2,
      (e32.symm y : GL (Fin 3) (ZMod p)), (e32.symm y).2, fun h => hxy ?_⟩
    have h' : (e32.symm x : H) * (e32.symm y : H) = (e32.symm y : H) * (e32.symm x : H) :=
      Subtype.ext h
    simpa using congrArg e32 h'
  have hdec : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ x ∈ H, z * x = x * z) ∧ t = h * z :=
    fun t ht _ => decomp_of_mem_z7 hp hp7 hirr e32 hn t ht
  have hinn : ∀ t ∈ A.map (autGL e).toMonoidHom, N1322.IsRefl t →
      ∃ h₀ ∈ H, ∀ x ∈ H, t * x * t⁻¹ = h₀ * x * h₀⁻¹ := by
    intro t ht hrefl
    obtain ⟨h, hh, z, hzc, htz⟩ := hdec t ht hrefl
    refine ⟨h, hh, fun x hx => ?_⟩
    rw [htz]
    calc h * z * x * (h * z)⁻¹ = h * (z * x * z⁻¹) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hzc x hx]; group
  obtain ⟨h0, h0A, hr0, hh0⟩ := rfr_g32_lift hp e hR hI hHG hirr hnc hinn e32 rfr_g0_sq rfr_g0_ne
  obtain ⟨h1, h1A, hr1, hh1⟩ := rfr_g32_lift hp e hR hI hHG hirr hnc hinn e32 rfr_g1_sq rfr_g1_ne
  obtain ⟨h2, h2A, hr2, hh2⟩ := rfr_g32_lift hp e hR hI hHG hirr hnc hinn e32 rfr_g2_sq rfr_g2_ne
  obtain ⟨a, aA, hra, hha⟩ := rfr_g32_lift hp e hR hI hHG hirr hnc hinn e32 rfr_gu_sq rfr_gu_ne
  have hy : autGL e (((h2 * h1) * h0 * (h2 * h1)⁻¹) * (h1 * h2 * h1) *
      ((h2 * h1) * h0 * (h2 * h1)⁻¹)⁻¹) =
      (-1) * ((e32.symm rfr_gconj : H) : GL (Fin 3) (ZMod p)) := by
    rw [rfr_g32_conj_map e hh0 hh1 hh2]
    congr 1
    rw [← rfr_g32_conj_pull e32, MulEquiv.symm_apply_apply]
    rfl
  exact ⟨h0, h0A, h1, h1A, h2, h2A, a, aA, hr0, hr1, hr2, hra,
    rfr_g32_order_lift e e32 hh0 hh1 rfr_g0_mul_g1_order,
    rfr_g32_order_lift e e32 hh1 hh2 rfr_g1_mul_g2_order,
    rfr_g32_order_lift e e32 hh0 hh2 rfr_g0_mul_g2_order,
    rfr_g32_order_lift e e32 hh0 hha rfr_g0_mul_gu_order,
    rfr_g32_order_lift e e32 hh1 hha rfr_g1_mul_gu_order,
    rfr_g32_commute_conj_lift e e32 hha hy rfr_gu_commute_conj⟩

end CFSG.StandardType.ZS.DimThree
