module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110LmFieldLe
public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110LineCent
public import CFSG.CGT.Timmesfeld75.SLTransvection
import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110EbarSiegel
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusLine
import CFSG.ClassicalGroups.SpecialLinear.InvolutionOrderSix
import CFSG.ClassicalGroups.SpecialLinear.TransvectionRootGroup
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviModel
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.RankThree.OrthogonalInvolutions.A2Pencil
import CFSG.RankThree.GF2n.Stroth80.Sec123Order
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSplit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.RankThree.GF2n.Smith81.Lin31Back
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
public import CFSG.RankThree.GF2n.Stroth80.Sec11Module
public import CFSG.RankThree.GF2n.Stroth80.Sec12Decomp
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Timmesfeld.RankOne
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCLinSylow
import CFSG.ClassicalGroups.Orthogonal.RootGroupPair
import CFSG.RankThree.GF2n.Stroth80.Sec12Aniso
import CFSG.RankThree.GF2n.Stroth80.Sec12Stab

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open Matrix Module QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

private theorem eq_of_map_eq_of_mul_self {X Y : Type*} [Group X] [Finite X] [Group Y]
    {ρ : X →* Y} (hker : ∀ z : X, ρ z = 1 → z ∈ Subgroup.center X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {s s' : X}
    (hs : s * s = 1) (hs' : s' * s' = 1) (h : ρ s = ρ s') : s = s' := by
  have hz : s' * s⁻¹ ∈ Subgroup.center X := by
    refine hker _ ?_
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hz2 : (s' * s⁻¹) ^ 2 = 1 := by
    have hzs : (s' * s⁻¹) * s = s' := by group
    have h2 : (s' * s⁻¹) ^ 2 * s = s := by
      rw [pow_two]
      calc (s' * s⁻¹) * (s' * s⁻¹) * s = (s' * s⁻¹) * ((s' * s⁻¹) * s) := by group
        _ = (s' * s⁻¹) * s' := by rw [hzs]
        _ = s' * (s' * s⁻¹) := (Subgroup.mem_center_iff.mp hz s').symm
        _ = s' * s' * s⁻¹ := by group
        _ = s⁻¹ := by rw [hs', one_mul]
        _ = s := inv_eq_of_mul_eq_one_right hs
    have h2' : (s' * s⁻¹) ^ 2 * s = 1 * s := by rw [one_mul]; exact h2
    exact mul_right_cancel h2'
  have hdvdC : orderOf (s' * s⁻¹) ∣ Nat.card (Subgroup.center X) := by
    simpa [Subgroup.orderOf_mk] using
      orderOf_dvd_natCard (⟨s' * s⁻¹, hz⟩ : Subgroup.center X)
  have hodd' : Odd (orderOf (s' * s⁻¹)) := hodd.of_dvd_nat hdvdC
  have hdvd : orderOf (s' * s⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
  have h1 : orderOf (s' * s⁻¹) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
    · exact h2
    · rw [h2] at hodd'
      exact absurd hodd' (by decide)
  have hz1 : s' * s⁻¹ = 1 := orderOf_eq_one_iff.mp h1
  exact (calc s' = s' * s⁻¹ * s := by group
    _ = s := by rw [hz1, one_mul]).symm

private theorem commute_of_commute_map {X Y : Type*} [Group X] [Finite X] [Group Y]
    {ρ : X →* Y} (hker : ∀ z : X, ρ z = 1 → z ∈ Subgroup.center X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {s s' : X}
    (hs' : s' * s' = 1) (h : ρ s * ρ s' = ρ s' * ρ s) :
    s * s' = s' * s := by
  have hz : s * s' * s⁻¹ * s'⁻¹ ∈ Subgroup.center X := by
    refine hker _ ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    simp
  have hzs : (s * s' * s⁻¹ * s'⁻¹) * s' = s * s' * s⁻¹ := by group
  have h2 : (s * s' * s⁻¹ * s'⁻¹) ^ 2 = 1 := by
    have h3 : (s * s' * s⁻¹ * s'⁻¹) ^ 2 * s' = s' := by
      rw [pow_two]
      calc (s * s' * s⁻¹ * s'⁻¹) * (s * s' * s⁻¹ * s'⁻¹) * s' =
            (s * s' * s⁻¹ * s'⁻¹) * ((s * s' * s⁻¹ * s'⁻¹) * s') := by group
        _ = (s * s' * s⁻¹ * s'⁻¹) * (s * s' * s⁻¹) := by rw [hzs]
        _ = (s * s' * s⁻¹) * (s * s' * s⁻¹ * s'⁻¹) :=
              (Subgroup.mem_center_iff.mp hz (s * s' * s⁻¹)).symm
        _ = (s * s' * s⁻¹) * (s * s' * s⁻¹) * s'⁻¹ := by group
        _ = s' := by
              have h4 : (s * s' * s⁻¹) * (s * s' * s⁻¹) = 1 := by
                calc s * s' * s⁻¹ * (s * s' * s⁻¹) = s * (s' * s') * s⁻¹ := by group
                  _ = 1 := by rw [hs']; group
              rw [h4, one_mul, inv_eq_of_mul_eq_one_right hs']
    have h3' : (s * s' * s⁻¹ * s'⁻¹) ^ 2 * s' = 1 * s' := by rw [one_mul]; exact h3
    exact mul_right_cancel h3'
  have hdvdC : orderOf (s * s' * s⁻¹ * s'⁻¹) ∣ Nat.card (Subgroup.center X) := by
    simpa [Subgroup.orderOf_mk] using
      orderOf_dvd_natCard (⟨s * s' * s⁻¹ * s'⁻¹, hz⟩ : Subgroup.center X)
  have hodd' : Odd (orderOf (s * s' * s⁻¹ * s'⁻¹)) := hodd.of_dvd_nat hdvdC
  have hdvd : orderOf (s * s' * s⁻¹ * s'⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h1 : orderOf (s * s' * s⁻¹ * s'⁻¹) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h2 | h2
    · exact h2
    · rw [h2] at hodd'
      exact absurd hodd' (by decide)
  have hz1 : s * s' * s⁻¹ * s'⁻¹ = 1 := orderOf_eq_one_iff.mp h1
  calc s * s' = s * s' * s⁻¹ * s'⁻¹ * (s' * s) := by group
    _ = s' * s := by rw [hz1, one_mul]

private theorem commSpace_fixed_of_pencil {K : Type*} [Field K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[K] V} (hα : CFSG.RankThree.GF2n.Smith81.IsOrthA2 Q α)
    (hβ : CFSG.RankThree.GF2n.Smith81.IsOrthA2 Q β) (hc : Commute α β)
    (hαβ : CFSG.RankThree.GF2n.Smith81.IsOrthA2 Q (α * β)) :
    ∀ w ∈ commSpace α, β w = w := by
  rcases commSpace_eq_or_pencil_of_mul hQ hα hβ hc hαβ with h | ⟨-, hsing⟩
  · intro w hw
    exact mem_fixSpace.mp (commSpace_le_fixSpace hβ.mul_self (h ▸ hw))
  · intro w hw
    rw [← mem_fixSpace, fixSpace_eq_orthogonal_commSpace hQ hβ.mem hβ.mul_self,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hwu : Q (w + u) = 0 := hsing _ (Submodule.add_mem_sup hw hu)
    have hw0 : Q w = 0 := hsing _ (Submodule.mem_sup_left hw)
    have hu0 : Q u = 0 := hsing _ (Submodule.mem_sup_right hu)
    have h := map_add_eq Q w u
    rw [hwu, hw0, hu0] at h
    have hpol' : polar Q w u = 0 := by simpa using h.symm
    have hpol : polar Q u w = 0 := by
      rw [polar_comm Q u w]
      exact hpol'
    simpa [QuadraticMap.polarBilin_apply_apply] using hpol

private theorem exists_eq_one_add_vecMulVec_of_forall_orderOf_ne_six {n : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] {A : SL(n, K)} (hA : A * A = 1) (hA1 : A ≠ 1)
    (hno : ∀ g : SL(n, K),
      orderOf (QuotientGroup.mk (A * (g * A * g⁻¹)) : projectiveSL n K) ≠ 6) :
    ∃ c a : Fin n → K, c ≠ 0 ∧ a ≠ 0 ∧ a ⬝ᵥ c = 0 ∧
      (A : Matrix (Fin n) (Fin n) K) = 1 + Matrix.vecMulVec c a := by
  rcases vecMulVec_or_exists_conj_orderOf_mk_mul_eq_six (ι := Fin n) hA with
    ⟨v, w, hAw, hwv⟩ | ⟨g, hg⟩
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hA1
      apply Subtype.ext
      rw [hAw, Matrix.zero_vecMulVec, add_zero]
      rfl
    have hw : w ≠ 0 := by
      rintro rfl
      apply hA1
      apply Subtype.ext
      rw [hAw, Matrix.vecMulVec_zero, add_zero]
      rfl
    exact ⟨v, w, hv, hw, hwv, hAw⟩
  · exfalso
    exact hno g (hg (scalars n K) (scalars_le_center n K))

private theorem card_le_of_forall_proj_eq_root {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {c a : Fin n → K}
    {U : Subgroup (projectiveSL n K)}
    (hroot : ∀ u ∈ U, ∃ s : K, ∃ T : SL(n, K), T * T = 1 ∧ proj n K T = u ∧
      (T : Matrix (Fin n) (Fin n) K) = 1 + s • Matrix.vecMulVec c a) :
    Nat.card U ≤ Nat.card K := by
  classical
  have hex : ∀ u : ↥U, ∃ (s : K) (T : SL(n, K)), T * T = 1 ∧
      proj n K T = (u : projectiveSL n K) ∧
      (T : Matrix (Fin n) (Fin n) K) = 1 + s • Matrix.vecMulVec c a := by
    intro u
    by_cases hu : (u : projectiveSL n K) = 1
    · refine ⟨0, 1, by simp, ?_, by simp⟩
      rw [hu, map_one]
    · obtain ⟨s, T, hT, hp, hm⟩ := hroot u u.2
      exact ⟨s, T, hT, hp, hm⟩
  choose s T hT hproj hmat using hex
  have hinj : Function.Injective s := by
    intro u v huv
    apply Subtype.ext
    have hm : (T u : Matrix (Fin n) (Fin n) K) = (T v : Matrix (Fin n) (Fin n) K) := by
      rw [hmat u, hmat v, huv]
    rw [← hproj u, ← hproj v, Subtype.ext hm]
  exact Nat.card_le_card_of_injective s hinj

private theorem Ctx.exists_line_data (hc : Ctx M Q Z B) {a : ↥M}
    (h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)) :
    ∃ (y : G) (_ : IsLBTorus M Q Z B y) (U : Subgroup (Mbar M Q)),
      U ≤ bar M Q (LB M Q B) ∧ Nat.card U = Nat.card Z ∧
      (∀ u ∈ U, u ≠ 1 → u ∈ Ebar M Q Z B) ∧
      (∀ m : ↥M, (m : G) = (a : G) → QuotientGroup.mk' (Q.subgroupOf M) m ∈ U) ∧
      ∀ u ∈ U, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M,
        (m : G) = y ^ i * (a : G) * (y ^ i)⁻¹ ∧
        u = QuotientGroup.mk' (Q.subgroupOf M) m := by
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  obtain ⟨U, hUle, hUcard, hUa, hUelts⟩ := hy.exists_lbLine hc h.1 h.2.2.1
  refine ⟨y, hy, U, hUle, hUcard, fun u hu hu1 => ?_, hUa, hUelts⟩
  obtain ⟨i, -, m, hm, rfl⟩ := hUelts u hu hu1
  have hm' : m = (⟨y, hy.mem_M⟩ : ↥M) ^ i * a * ((⟨y, hy.mem_M⟩ : ↥M) ^ i)⁻¹ := by
    apply Subtype.ext
    rw [hm]
    simp
  have h1 := hc.Ebar_conj (hc.mk_mem_Ebar h.1 h.2)
    ((QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i)
  have h2 : QuotientGroup.mk' (Q.subgroupOf M) m =
      (QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i * QuotientGroup.mk a *
        ((QuotientGroup.mk (⟨y, hy.mem_M⟩ : ↥M) : Mbar M Q) ^ i)⁻¹ := by
    rw [hm', map_mul, map_mul, map_pow, map_inv, map_pow]
    rfl
  rw [h2]
  exact h1

private theorem Ctx.comm_mem_Z_of_pencil {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {a k : G} (haH : a ∈ H0 M Z) (hkH : k ∈ H0 M Z)
    (hEa : QuotientGroup.mk (⟨a, haH.1⟩ : ↥M) ∈ Ebar M Q Z B)
    (hEk : QuotientGroup.mk (⟨k, hkH.1⟩ : ↥M) ∈ Ebar M Q Z B)
    (hEka : QuotientGroup.mk (⟨k * a, ((H0 M Z).mul_mem hkH haH).1⟩ : ↥M) ∈ Ebar M Q Z B)
    (hcomm : Commute (φ ⟨a, haH⟩) (φ ⟨k, hkH⟩)) :
    ∀ x ∈ ⁅Q, Subgroup.zpowers a⁆, ⁅k, x⁆ ∈ Z := by
  have hKZ : Nat.card K = Nat.card Z := hD.card
  have hTa : CFSG.RankThree.GF2n.Smith81.IsOrthA2 M₀.toQuadraticForm (φ ⟨a, haH⟩) :=
    hc.isOrthA2_of_mem_Ebar hD hKZ haH hEa (fun x hx => hφπ ⟨a, haH⟩ x hx)
  have hTk : CFSG.RankThree.GF2n.Smith81.IsOrthA2 M₀.toQuadraticForm (φ ⟨k, hkH⟩) :=
    hc.isOrthA2_of_mem_Ebar hD hKZ hkH hEk (fun x hx => hφπ ⟨k, hkH⟩ x hx)
  have hTka : CFSG.RankThree.GF2n.Smith81.IsOrthA2 M₀.toQuadraticForm
      (φ ⟨k, hkH⟩ * φ ⟨a, haH⟩) := by
    have h1 : φ ⟨k, hkH⟩ * φ ⟨a, haH⟩ = φ (⟨k * a, (H0 M Z).mul_mem hkH haH⟩ : H0 M Z) := by
      rw [← map_mul]
      rfl
    rw [h1]
    exact hc.isOrthA2_of_mem_Ebar hD hKZ ((H0 M Z).mul_mem hkH haH) hEka
      (fun x hx => hφπ ⟨k * a, (H0 M Z).mul_mem hkH haH⟩ x hx)
  have hTka' : CFSG.RankThree.GF2n.Smith81.IsOrthA2 M₀.toQuadraticForm
      (φ ⟨a, haH⟩ * φ ⟨k, hkH⟩) := by
    rw [hcomm.eq]
    exact hTka
  have hfix := commSpace_fixed_of_pencil (polarBilin_toQuadraticForm_nondegenerate M₀)
    hTa hTk hcomm hTka'
  have hcomQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have havM : a ^ j ∈ M := M.zpow_mem haH.1 j
    have e : ⁅u, a ^ j⁆ = u * ((a ^ j) * u⁻¹ * (a ^ j)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hu
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 havM) u⁻¹).mp (Q.inv_mem hu))
  have hQn : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haH.1) x).mp hx
  have hQn' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haH.1)) x).mp hx
    simpa using this
  intro x hx
  have hxQ : x ∈ Q := hcomQ hx
  have hxpi : M₀.π x ∈ commSpace (φ ⟨a, haH⟩) := by
    rw [commSpace, ← Tim79.QuadModel.mem_img_commutator_zpowers (φ ⟨a, haH⟩) hQn hQn'
      (fun y hy => hφπ ⟨a, haH⟩ y hy)]
    exact M₀.pi_mem_img hx hxQ
  have hkx : k * x * k⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hkH.1) x).mp hxQ
  refine (M₀.comm_mem_iff hxQ hkx).mpr ?_
  rw [hφπ ⟨k, hkH⟩ x hxQ]
  exact hfix _ hxpi

private theorem Ctx.not_orderOf_mk_mul_eq_six (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {A : SL(m, K)} {aX : ↥(Xbar M Q Z B)} (hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B)
    (hρa : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = proj m K A) :
    ∀ g : SL(m, K),
      orderOf (QuotientGroup.mk (A * (g * A * g⁻¹)) : projectiveSL m K) ≠ 6 := by
  intro g hg6
  obtain ⟨wX, hwX⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.modelHom_surjective (e := e) (proj m K g)
  let kX : ↥(Xbar M Q Z B) := wX * aX * wX⁻¹
  have hkE : (kX : Mbar M Q) ∈ Ebar M Q Z B := by
    have h1 := hc.Ebar_conj hEa (wX : Mbar M Q)
    simpa [kX] using h1
  have hρk : CFSG.ComponentClassification.RankTwoClassical.modelHom e kX =
      proj m K (g * A * g⁻¹) := by
    change CFSG.ComponentClassification.RankTwoClassical.modelHom e (wX * aX * wX⁻¹) =
      proj m K (g * A * g⁻¹)
    rw [map_mul, map_mul, map_inv, hwX, hρa, map_mul, map_mul, map_inv]
  have hord : orderOf (CFSG.ComponentClassification.RankTwoClassical.modelHom e (kX * aX)) =
      6 := by
    rw [map_mul, hρk, hρa]
    have hconj : proj m K (g * A * g⁻¹) * proj m K A =
        (MulAut.conj (proj m K (g * A * g⁻¹)))
          (proj m K A * proj m K (g * A * g⁻¹)) := by
      rw [MulAut.conj_apply]
      group
    rw [hconj, MulEquiv.orderOf_eq, ← map_mul]
    exact hg6
  have hdvd : 6 ∣ orderOf (kX * aX) := by
    rw [← hord]
    exact orderOf_map_dvd _ _
  have horder_eq : orderOf ((kX : Mbar M Q) * (aX : Mbar M Q)) = orderOf (kX * aX) := by
    rw [← Subgroup.orderOf_coe (kX * aX)]
    rfl
  have hdvdM : 6 ∣ orderOf ((kX : Mbar M Q) * (aX : Mbar M Q)) := horder_eq.symm ▸ hdvd
  rcases hc.orderOf_mul_of_mem_Ebar hkE hEa with h4 | hodd
  · have h64 : 6 ∣ 4 := hdvdM.trans h4
    omega
  · have h2 : 2 ∣ orderOf ((kX : Mbar M Q) * (aX : Mbar M Q)) :=
      (by norm_num : (2 : ℕ) ∣ 6).trans hdvdM
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem Ctx.isTransvection_of_modelHom_eq (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)} {τ : ↥(Xbar M Q Z B)}
    (hτ : (τ : Mbar M Q) ∈ Ebar M Q Z B) {A : SL(m, K)} (hA : A * A = 1)
    (hρ : CFSG.ComponentClassification.RankTwoClassical.modelHom e τ = proj m K A) :
    IsTransvection A := by
  have hkerX : ∀ z : ↥(Xbar M Q Z B),
      CFSG.ComponentClassification.RankTwoClassical.modelHom e z = 1 →
        z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    rw [← CFSG.ComponentClassification.RankTwoClassical.ker_modelHom (e := e)]
    exact MonoidHom.mem_ker.mpr hz
  have hA1 : A ≠ 1 := by
    intro hA1
    have hτ2 : τ * τ = 1 := by
      apply Subtype.ext
      have h2 : orderOf (τ : Mbar M Q) = 2 := Ctx.orderOf_eq_two_of_mem_Ebar hτ
      have h3 := pow_orderOf_eq_one (τ : Mbar M Q)
      rw [h2] at h3
      simpa [pow_two] using h3
    have hτ1 : τ = 1 :=
      eq_of_map_eq_of_mul_self hkerX hc.odd_card_center_Xbar hτ2 (by simp)
        (by rw [hρ, hA1]; simp)
    have h2 := Ctx.orderOf_eq_two_of_mem_Ebar hτ
    rw [show (τ : Mbar M Q) = 1 by rw [hτ1]; rfl, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨c, a₀, hc0, ha0, hac, hAform⟩ :=
    exists_eq_one_add_vecMulVec_of_forall_orderOf_ne_six hA hA1
      (hc.not_orderOf_mk_mul_eq_six hτ hρ)
  exact isTransvection_of_coe hc0 ha0 hac hAform

private theorem Ctx.exists_transvection_of_psl (hc : Ctx M Q Z B) {m x : ℕ}
    {a : G} (ha : a ∈ LB M Q B) (hA2 : IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K))
      (A : SL(m, K)) (c a₀ : Fin m → K),
      Nat.card K = 2 ^ x ∧
      A * A = 1 ∧ A ≠ 1 ∧ (A : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec c a₀ ∧
      c ≠ 0 ∧ a₀ ≠ 0 ∧ a₀ ⬝ᵥ c = 0 ∧
      CFSG.ComponentClassification.RankTwoClassical.modelHom e
        (⟨QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M),
          mk_mem_Xbar_of_LB M Q Z B ⟨a, hc.LB_le_M ha⟩ ha hA2⟩ : ↥(Xbar M Q Z B)) =
        proj m K A := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hx : 1 ≤ x := (h.admissible).2.1
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hx
      hKcard
  let aM : ↥M := ⟨a, hc.LB_le_M ha⟩
  let aX : ↥(Xbar M Q Z B) := ⟨QuotientGroup.mk aM, mk_mem_Xbar_of_LB M Q Z B aM ha hA2⟩
  have haXbar : (aX : Mbar M Q) ∈ bar M Q (LB M Q B) :=
    Subgroup.mem_map.mpr ⟨aM, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hsq : aX * aX = 1 := by
    apply Subtype.ext
    show (aX : Mbar M Q) * (aX : Mbar M Q) = 1
    have h2 := hc.isElemAbelian_bar_LB.2 aX haXbar
    simpa [pow_two] using h2
  have hkerX : ∀ z : ↥(Xbar M Q Z B),
      CFSG.ComponentClassification.RankTwoClassical.modelHom e z = 1 →
        z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    rw [← CFSG.ComponentClassification.RankTwoClassical.ker_modelHom (e := e)]
    exact MonoidHom.mem_ker.mpr hz
  obtain ⟨A, hproj, hA2A⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.exists_sl_lift
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e aX)
      (by rw [← map_mul, hsq, map_one])
  have hA1 : A ≠ 1 := by
    intro h1
    have h1' : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = 1 := by
      rw [← hproj, h1, map_one]
    have hzero : aX = 1 :=
      eq_of_map_eq_of_mul_self hkerX (hc.odd_card_center_Xbar) hsq (by simp)
        (by rw [h1', map_one])
    exact hA2.2.1 ((QuotientGroup.eq_one_iff aM).mp
      (congrArg (fun t : ↥(Xbar M Q Z B) => (t : Mbar M Q)) hzero))
  have hno := hc.not_orderOf_mk_mul_eq_six (hc.mk_mem_Ebar ha hA2) hproj.symm
  obtain ⟨c, a₀, hc0, ha0, hac, hAform⟩ :=
    exists_eq_one_add_vecMulVec_of_forall_orderOf_ne_six hA2A hA1 hno
  exact ⟨K, hKf, hKfin, inferInstance, e, A, c, a₀, hKcard, hA2A, hA1, hAform, hc0, ha0, hac,
    hproj.symm⟩

private theorem isTransvection_of_mem_tvCenter {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {c : Fin m → K} (hc : c ≠ 0) {t : SL(m, K)} (ht : t ∈ tvCenterSL c)
    (ht1 : t ≠ 1) : IsTransvection t := by
  obtain ⟨b, hb, htb⟩ := ht
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply ht1
    apply Subtype.ext
    rw [htb, Matrix.vecMulVec_zero, add_zero]
    rfl
  exact isTransvection_of_coe hc hb0 hb htb

private theorem isTransvection_of_mem_tvAxis {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {a : Fin m → K} (ha : a ≠ 0) {t : SL(m, K)} (ht : t ∈ tvAxisSL a)
    (ht1 : t ≠ 1) : IsTransvection t := by
  obtain ⟨v, hv, htv⟩ := ht
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply ht1
    apply Subtype.ext
    rw [htv, Matrix.zero_vecMulVec, add_zero]
    rfl
  exact isTransvection_of_coe hv0 ha hv htv

private theorem isTransvection_mul_of_mem_tvCenter {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {c : Fin m → K} (hc : c ≠ 0) {t A : SL(m, K)} (ht : t ∈ tvCenterSL c)
    (hA : A ∈ tvCenterSL c) (hne : t * A ≠ 1) : IsTransvection (t * A) := by
  obtain ⟨b, hb, htb⟩ := ht
  obtain ⟨a, ha, hAa⟩ := hA
  have hsum : (a + b) ⬝ᵥ c = 0 := by rw [add_dotProduct, ha, hb, add_zero]
  have hne0 : a + b ≠ 0 := by
    rintro h0
    apply hne
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, htb, hAa, tv_mul_tv_center hb, add_comm b a, h0,
      Matrix.vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]
  refine isTransvection_of_coe hc hne0 hsum ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, htb, hAa, tv_mul_tv_center hb, add_comm b a]

private theorem isTransvection_mul_of_mem_tvAxis {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {a : Fin m → K} (ha : a ≠ 0) {t A : SL(m, K)} (ht : t ∈ tvAxisSL a)
    (hA : A ∈ tvAxisSL a) (hne : t * A ≠ 1) : IsTransvection (t * A) := by
  obtain ⟨v, hv, htv⟩ := ht
  obtain ⟨w, hw, hAw⟩ := hA
  have hsum : a ⬝ᵥ (v + w) = 0 := by rw [dotProduct_add, hv, hw, add_zero]
  have hne0 : v + w ≠ 0 := by
    rintro h0
    apply hne
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, htv, hAw, tv_mul_tv_axis hw, h0,
      Matrix.zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]
  refine isTransvection_of_coe hne0 ha hsum ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, htv, hAw, tv_mul_tv_axis hw]

private theorem Ctx.mem_Ebar_mul_of_transvection (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {c a₀ : Fin m → K} {A : SL(m, K)}
    (hc0 : c ≠ 0) (ha0 : a₀ ≠ 0) (hac : a₀ ⬝ᵥ c = 0)
    (hA2A : A * A = 1)
    (hAform : (A : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec c a₀)
    {aX kX : ↥(Xbar M Q Z B)} (hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B)
    (hA2' : aX * aX = 1) (hkXsq : kX * kX = 1)
    (hρa : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = proj m K A)
    {t : SL(m, K)}
    (hρk : CFSG.ComponentClassification.RankTwoClassical.modelHom e kX = proj m K t)
    (hkcomm : kX * aX = aX * kX)
    (ht : t ∈ tvCenterSL c ∨ t ∈ tvAxisSL a₀) (htA : t ≠ A) :
    (kX : Mbar M Q) * (aX : Mbar M Q) ∈ Ebar M Q Z B := by
  have hAcenter : A ∈ tvCenterSL c := ⟨a₀, hac, hAform⟩
  have hAaxis : A ∈ tvAxisSL a₀ := ⟨c, hac, hAform⟩
  have hAtv : IsTransvection A := isTransvection_of_coe hc0 ha0 hac hAform
  have hkerX : ∀ z : ↥(Xbar M Q Z B),
      CFSG.ComponentClassification.RankTwoClassical.modelHom e z = 1 →
        z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    rw [← CFSG.ComponentClassification.RankTwoClassical.ker_modelHom (e := e)]
    exact MonoidHom.mem_ker.mpr hz
  have hta1 : t * A ≠ 1 := by
    intro h1
    apply htA
    calc t = t * (A * A) := by rw [hA2A, mul_one]
      _ = t * A * A := by group
      _ = A := by rw [h1, one_mul]
  have htaTv : IsTransvection (t * A) := by
    rcases ht with h | h
    · exact isTransvection_mul_of_mem_tvCenter hc0 h hAcenter hta1
    · exact isTransvection_mul_of_mem_tvAxis ha0 h hAaxis hta1
  obtain ⟨W₂, hW₂⟩ := exists_conj_of_isTransvection hAtv htaTv
  obtain ⟨w₂X, hw₂X⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.modelHom_surjective (e := e) (proj m K W₂)
  let k₂ : ↥(Xbar M Q Z B) := w₂X * aX * w₂X⁻¹
  have hk₂E : (k₂ : Mbar M Q) ∈ Ebar M Q Z B := by
    have h1 := hc.Ebar_conj hEa (w₂X : Mbar M Q)
    simpa [k₂] using h1
  have hk₂sq : k₂ * k₂ = 1 := by
    change (w₂X * aX * w₂X⁻¹) * (w₂X * aX * w₂X⁻¹) = 1
    calc (w₂X * aX * w₂X⁻¹) * (w₂X * aX * w₂X⁻¹) = w₂X * (aX * aX) * w₂X⁻¹ := by group
      _ = 1 := by rw [hA2']; group
  have hk₂proj : CFSG.ComponentClassification.RankTwoClassical.modelHom e k₂ =
      proj m K (t * A) := by
    change CFSG.ComponentClassification.RankTwoClassical.modelHom e (w₂X * aX * w₂X⁻¹) =
      proj m K (t * A)
    rw [map_mul, map_mul, map_inv, hw₂X, hρa, ← hW₂, map_mul, map_mul, map_inv]
  have hprod_sq : (kX * aX) * (kX * aX) = 1 := by
    have h1 : (kX * aX) * (kX * aX) = (kX * kX) * (aX * aX) := by
      calc (kX * aX) * (kX * aX) = kX * (aX * kX) * aX := by group
        _ = kX * (kX * aX) * aX := by rw [← hkcomm]
        _ = (kX * kX) * (aX * aX) := by group
    rw [h1, hkXsq, hA2', one_mul]
  have hprod_img : CFSG.ComponentClassification.RankTwoClassical.modelHom e (kX * aX) =
      CFSG.ComponentClassification.RankTwoClassical.modelHom e k₂ := by
    rw [map_mul, hρk, hρa, hk₂proj, map_mul]
  have heq : kX * aX = k₂ :=
    eq_of_map_eq_of_mul_self hkerX hc.odd_card_center_Xbar hprod_sq hk₂sq hprod_img
  rw [show (kX : Mbar M Q) * (aX : Mbar M Q) = (k₂ : Mbar M Q) from
    congrArg (fun z : ↥(Xbar M Q Z B) => (z : Mbar M Q)) heq]
  exact hk₂E

private theorem Ctx.exists_Xbar_conj_of_transvection (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {c a₀ : Fin m → K} {A : SL(m, K)}
    (hc0 : c ≠ 0) (ha0 : a₀ ≠ 0) (hac : a₀ ⬝ᵥ c = 0)
    (hA2A : A * A = 1)
    (hAform : (A : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec c a₀)
    {aX : ↥(Xbar M Q Z B)} (hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B) (hA2' : aX * aX = 1)
    (hρa : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = proj m K A)
    {t : SL(m, K)} (ht : t ∈ tvCenterSL c ∨ t ∈ tvAxisSL a₀) (ht1 : t ≠ 1) (htA : t ≠ A) :
    ∃ kX : ↥(Xbar M Q Z B),
      (kX : Mbar M Q) ∈ Ebar M Q Z B ∧
      CFSG.ComponentClassification.RankTwoClassical.modelHom e kX = proj m K t ∧
      (kX : Mbar M Q) * (aX : Mbar M Q) ∈ Ebar M Q Z B ∧
      (kX : Mbar M Q) * (aX : Mbar M Q) = (aX : Mbar M Q) * (kX : Mbar M Q) := by
  have hAcenter : A ∈ tvCenterSL c := ⟨a₀, hac, hAform⟩
  have hAaxis : A ∈ tvAxisSL a₀ := ⟨c, hac, hAform⟩
  have hAtv : IsTransvection A := isTransvection_of_coe hc0 ha0 hac hAform
  have httv : IsTransvection t := by
    rcases ht with h | h
    · exact isTransvection_of_mem_tvCenter hc0 h ht1
    · exact isTransvection_of_mem_tvAxis ha0 h ht1
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hAtv httv
  obtain ⟨wX, hwX⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.modelHom_surjective (e := e) (proj m K W)
  let kX : ↥(Xbar M Q Z B) := wX * aX * wX⁻¹
  have hkXsq : kX * kX = 1 := by
    change (wX * aX * wX⁻¹) * (wX * aX * wX⁻¹) = 1
    calc (wX * aX * wX⁻¹) * (wX * aX * wX⁻¹) = wX * (aX * aX) * wX⁻¹ := by group
      _ = 1 := by rw [hA2']; group
  have hodd : Odd (Nat.card (Subgroup.center ↥(Xbar M Q Z B))) := hc.odd_card_center_Xbar
  have hkerX : ∀ z : ↥(Xbar M Q Z B),
      CFSG.ComponentClassification.RankTwoClassical.modelHom e z = 1 →
        z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    rw [← CFSG.ComponentClassification.RankTwoClassical.ker_modelHom (e := e)]
    exact MonoidHom.mem_ker.mpr hz
  have hρk : CFSG.ComponentClassification.RankTwoClassical.modelHom e kX = proj m K t := by
    change CFSG.ComponentClassification.RankTwoClassical.modelHom e (wX * aX * wX⁻¹) =
      proj m K t
    rw [map_mul, map_mul, map_inv, hwX, hρa, ← hW, map_mul, map_mul, map_inv]
  have hkcomm : kX * aX = aX * kX := by
    have himg : CFSG.ComponentClassification.RankTwoClassical.modelHom e kX *
        CFSG.ComponentClassification.RankTwoClassical.modelHom e aX =
        CFSG.ComponentClassification.RankTwoClassical.modelHom e aX *
          CFSG.ComponentClassification.RankTwoClassical.modelHom e kX := by
      rw [hρk, hρa]
      rcases ht with h | h
      · rw [← map_mul, tvCenterSL_comm t h A hAcenter, map_mul]
      · rw [← map_mul, tvAxisSL_comm t h A hAaxis, map_mul]
    exact commute_of_commute_map hkerX hodd hA2' himg
  have hka : (kX : Mbar M Q) * (aX : Mbar M Q) = (aX : Mbar M Q) * (kX : Mbar M Q) := by
    simpa using congrArg (fun z : ↥(Xbar M Q Z B) => (z : Mbar M Q)) hkcomm
  have hkE : (kX : Mbar M Q) ∈ Ebar M Q Z B := by
    have h1 := hc.Ebar_conj hEa (wX : Mbar M Q)
    simpa [kX] using h1
  have hkaE := hc.mem_Ebar_mul_of_transvection hc0 ha0 hac hA2A hAform hEa hA2' hkXsq hρa hρk
    hkcomm ht htA
  exact ⟨kX, hkE, hρk, hkaE, hka⟩
private theorem Ctx.exists_hfix_of_Xbar (hc : Ctx M Q Z B)
    {a : G} (ha : a ∈ LB M Q B) (hA2 : IsA2 Q Z a)
    {kX : ↥(Xbar M Q Z B)} (hkE : (kX : Mbar M Q) ∈ Ebar M Q Z B)
    (hkaE : (kX : Mbar M Q) * (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) ∈ Ebar M Q Z B)
    (hcomm : (kX : Mbar M Q) * (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) =
      (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M)) * (kX : Mbar M Q)) :
    ∃ k : ↥M, (k : G) ∈ H0 M Z ∧ IsA2 Q Z (k : G) ∧
      (QuotientGroup.mk k : Mbar M Q) = kX ∧
      (∀ x ∈ ⁅Q, Subgroup.zpowers a⁆, ⁅(k : G), x⁆ ∈ Z) ∧
      ⁅(k : G), a⁆ ∈ Q := by
  obtain ⟨k, hkX, hkA2, hkH⟩ := hc.exists_H0_rep_of_mem_Ebar hkE
  have hkM : (k : G) ∈ M := (Subgroup.mem_inf.mp hkH).1
  have haM : a ∈ M := (Subgroup.mem_inf.mp (hc.LB_le_H0 ha)).1
  have hcommM : (QuotientGroup.mk k : Mbar M Q) *
      (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q) =
      (QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q) *
        (QuotientGroup.mk k : Mbar M Q) := by
    simpa [hkX] using hcomm
  have hcommEl : ⁅(k : G), a⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hkM haM) (M.inv_mem hkM)) (M.inv_mem haM)
  have hkl : ⁅(k : G), a⁆ ∈ Q := by
    have h1 : (QuotientGroup.mk' (Q.subgroupOf M) (⟨⁅(k : G), a⁆, hcommEl⟩ : ↥M) :
        Mbar M Q) = 1 := by
      have h2 : (⟨⁅(k : G), a⁆, hcommEl⟩ : ↥M) =
          ⁅(⟨(k : G), hkM⟩ : ↥M), (⟨a, haM⟩ : ↥M)⁆ := by
        apply Subtype.ext
        rfl
      rw [h2, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcommM
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) ⟨⁅(k : G), a⁆, hcommEl⟩).mp h1
  have hEka : (QuotientGroup.mk (⟨(k : G) * a,
      M.mul_mem hkM haM⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    have h2 : (QuotientGroup.mk (⟨(k : G) * a, M.mul_mem hkM haM⟩ : ↥M) : Mbar M Q) =
        (kX : Mbar M Q) * (QuotientGroup.mk (⟨a, haM⟩ : ↥M) : Mbar M Q) := by
      have h3 : (⟨(k : G) * a, M.mul_mem hkM haM⟩ : ↥M) =
          (⟨(k : G), hkM⟩ : ↥M) * (⟨a, haM⟩ : ↥M) := rfl
      rw [h3]
      change (QuotientGroup.mk (⟨(k : G), hkM⟩ : ↥M) : Mbar M Q) *
        (QuotientGroup.mk (⟨a, haM⟩ : ↥M) : Mbar M Q) = _
      rw [hkX]
    rw [h2]
    exact hkaE
  obtain ⟨n, γ, M₀, -, hD⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, -⟩ := exists_actionHom_H0 hc.hyp hD
  have hcommφ : Commute (φ ⟨a, hc.LB_le_H0 ha⟩) (φ ⟨(k : G), hkH⟩) := by
    have h1 : φ ⁅(⟨(k : G), hkH⟩ : H0 M Z), (⟨a, hc.LB_le_H0 ha⟩ : H0 M Z)⁆ = 1 := by
      rw [hφker]
      change ⁅(k : G), a⁆ ∈ Q
      exact hkl
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hkE' : (QuotientGroup.mk (⟨(k : G), hkM⟩ : ↥M) : Mbar M Q) ∈ Ebar M Q Z B := by
    have hk_eq : (⟨(k : G), hkM⟩ : ↥M) = k := Subtype.ext rfl
    rw [hk_eq, hkX]
    exact hkE
  have hfix := hc.comm_mem_Z_of_pencil hD hφπ (hc.LB_le_H0 ha) hkH
    (hc.mk_mem_Ebar ha hA2) hkE' hEka hcommφ
  exact ⟨k, hkH, hkA2, hkX, hfix, hkl⟩

private theorem Ctx.commute_line_of_hfix (hc : Ctx M Q Z B)
    {y : G} (hy : IsLBTorus M Q Z B y) {a : G} (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a)
    {k : ↥M} (hkH : (k : G) ∈ H0 M Z)
    (hfix : ∀ x ∈ ⁅Q, Subgroup.zpowers a⁆, ⁅(k : G), x⁆ ∈ Z)
    (hkl : ⁅(k : G), a⁆ ∈ Q)
    {U : Subgroup (Mbar M Q)} (hUelts : ∀ u ∈ U, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M,
      (m : G) = y ^ i * a * (y ^ i)⁻¹ ∧ u = QuotientGroup.mk' (Q.subgroupOf M) m) :
    ∀ u ∈ U, (QuotientGroup.mk k : Mbar M Q) * u =
      u * (QuotientGroup.mk k : Mbar M Q) := by
  have hkM : (k : G) ∈ M := (Subgroup.mem_inf.mp hkH).1
  intro u hu
  by_cases hu1 : u = 1
  · subst hu1
    rw [mul_one, one_mul]
  obtain ⟨i, -, m, hm, rfl⟩ := hUelts u hu hu1
  have hkm : ⁅(k : G), (m : G)⁆ ∈ Q := by
    simpa [hm] using hy.comm_conj_mem_Q_of_fix hc ha hA hkH hkl hfix i
  have hcommEl : ⁅(k : G), (m : G)⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hkM m.2) (M.inv_mem hkM)) (M.inv_mem m.2)
  have h1 : (⁅(QuotientGroup.mk' (Q.subgroupOf M) (⟨(k : G), hkM⟩ : ↥M)),
      QuotientGroup.mk' (Q.subgroupOf M) m⁆ : Mbar M Q) = 1 := by
    have h3 : (⁅(QuotientGroup.mk' (Q.subgroupOf M) (⟨(k : G), hkM⟩ : ↥M)),
        QuotientGroup.mk' (Q.subgroupOf M) m⁆ : Mbar M Q) =
        QuotientGroup.mk' (Q.subgroupOf M) (⟨⁅(k : G), (m : G)⁆, hcommEl⟩ : ↥M) := by
      rw [← map_commutatorElement]
      congr 1
    rw [h3]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M)
      (⟨⁅(k : G), (m : G)⁆, hcommEl⟩ : ↥M)).mpr (by rwa [Subgroup.mem_subgroupOf])
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

private theorem mul_self_of_mem_tvCenter {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {c : Fin m → K} {t : SL(m, K)} (ht : t ∈ tvCenterSL c) : t * t = 1 := by
  obtain ⟨b, hb, htb⟩ := ht
  have hbb : b + b = 0 := by
    ext i
    simp [CharTwo.add_self_eq_zero]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, htb, tv_mul_tv_center hb, hbb,
    Matrix.vecMulVec_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]

private theorem mul_self_of_mem_tvAxis {K : Type} [Field K] [CharP K 2] {m : ℕ}
    {a : Fin m → K} {t : SL(m, K)} (ht : t ∈ tvAxisSL a) : t * t = 1 := by
  obtain ⟨v, hv, htv⟩ := ht
  have hvv : v + v = 0 := by
    ext i
    simp [CharTwo.add_self_eq_zero]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, htv, tv_mul_tv_axis hv, hvv,
    Matrix.zero_vecMulVec, add_zero, Matrix.SpecialLinearGroup.coe_one]

private theorem Ctx.proj_commute_of_transvection (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {c a₀ : Fin m → K} {A : SL(m, K)}
    (hc0 : c ≠ 0) (ha0 : a₀ ≠ 0) (hac : a₀ ⬝ᵥ c = 0)
    (hA2A : A * A = 1)
    (hAform : (A : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec c a₀)
    {aX : ↥(Xbar M Q Z B)} (hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B) (hA2' : aX * aX = 1)
    {a : G} (ha : a ∈ LB M Q B) (hA2 : IsA2 Q Z a)
    (haX : (aX : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    (hρa : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = proj m K A)
    {y : G} (hy : IsLBTorus M Q Z B y)
    {U : Subgroup (Mbar M Q)} (hUle : U ≤ bar M Q (LB M Q B))
    (hUelts : ∀ u ∈ U, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M,
      (m : G) = y ^ i * a * (y ^ i)⁻¹ ∧ u = QuotientGroup.mk' (Q.subgroupOf M) m)
    (haXU : (aX : Mbar M Q) ∈ U) {uX : ↥(Xbar M Q Z B)} (huX : (uX : Mbar M Q) ∈ U)
    {T : SL(m, K)}
    (hT : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T =
      CFSG.ComponentClassification.RankTwoClassical.modelHom e uX)
    (hm : 3 ≤ m) {t : SL(m, K)} (ht : t ∈ tvCenterSL c ∨ t ∈ tvAxisSL a₀) :
    T * t = t * T := by
  have hm2 : 3 ≤ m := hm
  haveI : NeZero m := ⟨by omega⟩
  have hu2 : t * t = 1 := by
    rcases ht with h | h
    · exact mul_self_of_mem_tvCenter h
    · exact mul_self_of_mem_tvAxis h
  by_cases ht1 : t = 1
  · rw [ht1, mul_one, one_mul]
  by_cases htA : t = A
  · rw [htA]
    have hUab : (uX : Mbar M Q) * (aX : Mbar M Q) = (aX : Mbar M Q) * (uX : Mbar M Q) :=
      congrArg Subtype.val
        (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨uX, hUle huX⟩ ⟨aX, hUle haXU⟩)
    have hcomm : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K A =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K A *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T := by
      rw [hT, ← hρa]
      have hUX : uX * aX = aX * uX := by
        apply Subtype.ext
        simpa using hUab
      rw [← map_mul, ← map_mul, hUX]
    exact CFSG.ComponentClassification.OutcomeLocal.commute_of_proj_commute (A := T) (s := A)
      hA2A hcomm
  · obtain ⟨kX, hkE, hρk, hkaE, hcomm⟩ := hc.exists_Xbar_conj_of_transvection hc0 ha0 hac hA2A
      hAform hEa hA2' hρa ht ht1 htA
    rw [haX] at hkaE hcomm
    obtain ⟨k, hkH, -, hkXeq, hfix, hkl⟩ := hc.exists_hfix_of_Xbar ha hA2 hkE hkaE hcomm
    have hcommU := hc.commute_line_of_hfix hy ha hA2 hkH hfix hkl hUelts (uX : Mbar M Q) huX
    have hcommX : kX * uX = uX * kX := by
      apply Subtype.ext
      change (kX : Mbar M Q) * (uX : Mbar M Q) = (uX : Mbar M Q) * (kX : Mbar M Q)
      rw [← hkXeq]
      exact hcommU
    have himg : CFSG.ComponentClassification.RankTwoClassical.modelHom e kX *
        CFSG.ComponentClassification.RankTwoClassical.modelHom e uX =
        CFSG.ComponentClassification.RankTwoClassical.modelHom e uX *
          CFSG.ComponentClassification.RankTwoClassical.modelHom e kX := by
      rw [← map_mul, ← map_mul, hcommX]
    rw [hρk, ← hT] at himg
    exact CFSG.ComponentClassification.OutcomeLocal.commute_of_proj_commute (A := T) (s := t)
      hu2 (by simpa using himg.symm)

private theorem Ctx.exists_root_form_of_line (hc : Ctx M Q Z B) {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {c a₀ : Fin m → K} {A : SL(m, K)}
    (hc0 : c ≠ 0) (ha0 : a₀ ≠ 0) (hac : a₀ ⬝ᵥ c = 0)
    (hA2A : A * A = 1)
    (hAform : (A : Matrix (Fin m) (Fin m) K) = 1 + Matrix.vecMulVec c a₀)
    {aX : ↥(Xbar M Q Z B)} (hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B) (hA2' : aX * aX = 1)
    {a : G} (ha : a ∈ LB M Q B) (hA2 : IsA2 Q Z a)
    (haX : (aX : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M))
    (hρa : CFSG.ComponentClassification.RankTwoClassical.modelHom e aX = proj m K A)
    {y : G} (hy : IsLBTorus M Q Z B y)
    {U : Subgroup (Mbar M Q)} (hUle : U ≤ bar M Q (LB M Q B))
    (hUelts : ∀ u ∈ U, u ≠ 1 → ∃ i < Nat.card Z - 1, ∃ m : ↥M,
      (m : G) = y ^ i * a * (y ^ i)⁻¹ ∧ u = QuotientGroup.mk' (Q.subgroupOf M) m)
    (haXU : (aX : Mbar M Q) ∈ U) (hm : 3 ≤ m) :
    ∀ u : ↥(U.subgroupOf (Xbar M Q Z B)),
      ∃ s : K, ∃ T : SL(m, K), T * T = 1 ∧
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T =
          CFSG.ComponentClassification.RankTwoClassical.modelHom e (u : Xbar M Q Z B) ∧
        (T : Matrix (Fin m) (Fin m) K) = 1 + s • Matrix.vecMulVec c a₀ := by
  intro u
  have hu2 : (u : ↥(Xbar M Q Z B)) * (u : ↥(Xbar M Q Z B)) = 1 := by
    apply Subtype.ext
    have h2 := hc.isElemAbelian_bar_LB.2 ((u : ↥(Xbar M Q Z B)) : Mbar M Q) (hUle u.2)
    simpa [pow_two] using h2
  obtain ⟨T, hTproj, hT2⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.exists_sl_lift
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e (u : ↥(Xbar M Q Z B)))
      (by rw [← map_mul, hu2, map_one])
  have hcommC : ∀ t ∈ tvCenterSL c, T * t = t * T := by
    intro t ht
    exact hc.proj_commute_of_transvection hc0 ha0 hac hA2A hAform hEa hA2' ha hA2 haX hρa
      hy hUle hUelts haXU u.2 hTproj hm (Or.inl ht)
  have hcommA : ∀ t ∈ tvAxisSL a₀, T * t = t * T := by
    intro t ht
    exact hc.proj_commute_of_transvection hc0 ha0 hac hA2A hAform hEa hA2' ha hA2 haX hρa
      hy hUle hUelts haXU u.2 hTproj hm (Or.inr ht)
  obtain ⟨s, hs⟩ :=
    exists_eq_one_add_smul_vecMulVec_of_commute (K := K) (m := m) (by omega) hc0 ha0 hT2
      (fun x hx => hcommC x hx) (fun x hx => hcommA x hx)
  exact ⟨s, T, hT2, hTproj, hs⟩

private theorem Ctx.card_Z_le_two_pow_of_root_form {m : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {c a₀ : Fin m → K}
    {U : Subgroup (Mbar M Q)}
    (hUcard : Nat.card U = Nat.card Z) (hUX : U ≤ Xbar M Q Z B)
    (hroot : ∀ u : ↥(U.subgroupOf (Xbar M Q Z B)),
      ∃ s : K, ∃ T : SL(m, K), T * T = 1 ∧
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T =
          CFSG.ComponentClassification.RankTwoClassical.modelHom e (u : Xbar M Q Z B) ∧
        (T : Matrix (Fin m) (Fin m) K) = 1 + s • Matrix.vecMulVec c a₀)
    (hinj : Function.Injective fun u : ↥(U.subgroupOf (Xbar M Q Z B)) =>
      CFSG.ComponentClassification.RankTwoClassical.modelHom e (u : Xbar M Q Z B)) :
    Nat.card Z ≤ Nat.card K := by
  let U' : Subgroup (Xbar M Q Z B) := U.subgroupOf (Xbar M Q Z B)
  have hrootMap : ∀ v ∈ U'.map (CFSG.ComponentClassification.RankTwoClassical.modelHom e),
      ∃ s : K, ∃ T : SL(m, K), T * T = 1 ∧
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m K T = v ∧
        (T : Matrix (Fin m) (Fin m) K) = 1 + s • Matrix.vecMulVec c a₀ := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    exact hroot ⟨u, hu⟩
  have hcard : Nat.card ↥(U'.map
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e)) ≤ Nat.card K :=
    card_le_of_forall_proj_eq_root hrootMap
  have hmap : Nat.card ↥(U'.map
      (CFSG.ComponentClassification.RankTwoClassical.modelHom e)) = Nat.card U := by
    let φ : ↥U' → ↥(U'.map (CFSG.ComponentClassification.RankTwoClassical.modelHom e)) :=
      fun u => ⟨CFSG.ComponentClassification.RankTwoClassical.modelHom e u,
        Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩⟩
    have hφ : Function.Bijective φ := by
      constructor
      · intro u v huv
        exact hinj (congrArg Subtype.val huv)
      · intro v
        obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp v.2
        refine ⟨⟨u, hu⟩, ?_⟩
        apply Subtype.ext
        exact huv
    have h1 : Nat.card ↥(U'.map
        (CFSG.ComponentClassification.RankTwoClassical.modelHom e)) = Nat.card ↥U' :=
      (Nat.card_congr (Equiv.ofBijective φ hφ)).symm
    have h2 : Nat.card ↥U' = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
    rw [h1, h2]
  rw [← hUcard, ← hmap]
  exact hcard

theorem Ctx.card_Z_le_two_pow_of_psl (hc : Ctx M Q Z B) {m x : ℕ}
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) (hm : 3 ≤ m) :
    Nat.card Z ≤ 2 ^ x := by
  obtain ⟨a, ha, hA2⟩ := ha2
  obtain ⟨K, hKf, hKfin, hKchar, e, A, c, a₀, hKcard, hA2A, hA1, hAform, hc0, ha0, hac,
    hρa⟩ := hc.exists_transvection_of_psl ha hA2 h
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  let aM : ↥M := ⟨a, hc.LB_le_M ha⟩
  let aX : ↥(Xbar M Q Z B) := ⟨QuotientGroup.mk aM, mk_mem_Xbar_of_LB M Q Z B aM ha hA2⟩
  have haX : (aX : Mbar M Q) = QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) := rfl
  have hEa : (aX : Mbar M Q) ∈ Ebar M Q Z B := hc.mk_mem_Ebar ha hA2
  have hsq : aX * aX = 1 := by
    apply Subtype.ext
    have h1 : a * a ∈ Q := by simpa [pow_two] using hA2.2.2.1
    show (QuotientGroup.mk' (Q.subgroupOf M) aM : Mbar M Q) *
      (QuotientGroup.mk' (Q.subgroupOf M) aM : Mbar M Q) = 1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (aM * aM)).mpr (by
      rw [Subgroup.mem_subgroupOf]
      exact h1)
  obtain ⟨y, hy, U, hUle, hUcard, hUE, hUa, hUelts⟩ :=
    hc.exists_line_data (a := aM) ⟨ha, hA2⟩
  have hUX : U ≤ Xbar M Q Z B := fun u hu => by
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (hUE u hu hu1)
  have haXU : (aX : Mbar M Q) ∈ U := by
    simpa [aX] using hUa aM rfl
  have hroot := hc.exists_root_form_of_line hc0 ha0 hac hA2A hAform hEa hsq ha hA2
    haX hρa hy hUle hUelts haXU hm
  let U' : Subgroup (Xbar M Q Z B) := U.subgroupOf (Xbar M Q Z B)
  have hker : ∀ z : ↥(Xbar M Q Z B),
      CFSG.ComponentClassification.RankTwoClassical.modelHom e z = 1 →
        z ∈ Subgroup.center ↥(Xbar M Q Z B) := by
    intro z hz
    rw [← CFSG.ComponentClassification.RankTwoClassical.ker_modelHom (e := e)]
    exact MonoidHom.mem_ker.mpr hz
  have hinj : Function.Injective (fun u : ↥U' =>
      CFSG.ComponentClassification.RankTwoClassical.modelHom e (u : Xbar M Q Z B)) := by
    intro u v huv
    have hu2 : (u : Xbar M Q Z B) * (u : Xbar M Q Z B) = 1 := by
      apply Subtype.ext
      have h2 := hc.isElemAbelian_bar_LB.2 ((u : Xbar M Q Z B) : Mbar M Q) (hUle u.2)
      simpa [pow_two] using h2
    have hv2 : (v : Xbar M Q Z B) * (v : Xbar M Q Z B) = 1 := by
      apply Subtype.ext
      have h2 := hc.isElemAbelian_bar_LB.2 ((v : Xbar M Q Z B) : Mbar M Q) (hUle v.2)
      simpa [pow_two] using h2
    exact Subtype.ext
      (eq_of_map_eq_of_mul_self hker hc.odd_card_center_Xbar hu2 hv2 huv)
  have hcount := Ctx.card_Z_le_two_pow_of_root_form hUcard hUX hroot hinj
  rwa [hKcard] at hcount

theorem Ctx.two_pow_eq_card_Z_of_psl (hc : Ctx M Q Z B) {n m x : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL m 2 x) (hm : 3 ≤ m) :
    2 ^ x = Nat.card Z :=
  le_antisymm (Ctx.two_pow_le_card_Z_of_psl hc hw ha2 h)
    (Ctx.card_Z_le_two_pow_of_psl hc ha2 h hm)

end CFSG.RankThree.GF2n.Stroth80
