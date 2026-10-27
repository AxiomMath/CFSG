module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOvoid
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith

public section

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

namespace CFSG.SignalizerFunctorTheorem.McBride.SzModel

theorem sz_eq_suzukiMatrixGroup (n : ℕ) : Sz n = SuzukiMatrixGroup n :=
  (show CFSG.Theory.Comparator.SzModel n = Sz n by
      simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, Sz,
        SzGenerators]).symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n)

noncomputable def szEquiv (n : ℕ) : Sz n ≃* SuzukiMatrixGroup n :=
  MulEquiv.subgroupCongr (sz_eq_suzukiMatrixGroup n)

section Ovoid

variable {m : ℕ}

theorem card_stabilizer_ovoid
    (hm : 0 < m) (a : {p // p ∈ suzukiOvoidSet m}) :
    letI := suzukiOvoidAction m
    Nat.card (MulAction.stabilizer (SuzukiMatrixGroup m) a) =
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let := suzukiOvoidAction m
  have := suzuki_ovoid_two_transitive m
  have : MulAction.IsPretransitive (SuzukiMatrixGroup m) {p // p ∈ suzukiOvoidSet m} :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have h1 := (MulAction.stabilizer (SuzukiMatrixGroup m) a).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive, suzuki_ovoid_card,
    CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula m hm] at h1
  have hpos : 0 < (2 ^ (2 * m + 1)) ^ 2 + 1 := Nat.succ_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  ring

theorem not_mem_stabilizer_of_orderOf_five
    (hm : 0 < m) {x : SuzukiMatrixGroup m}
    (hx : orderOf x = 5) (a : {p // p ∈ suzukiOvoidSet m}) :
    letI := suzukiOvoidAction m
    x • a ≠ a := by
  let := suzukiOvoidAction m
  intro hxa
  have hmem : x ∈ MulAction.stabilizer (SuzukiMatrixGroup m) a := hxa
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [hx, card_stabilizer_ovoid hm a] at hdvd
  exact not_five_dvd_sq_mul_sub_one m hdvd

theorem exists_fixed_point_normalizer (hm : 0 < m) {S : Subgroup (SuzukiMatrixGroup m)}
    (hS : S ≠ ⊥) (hSp : IsPGroup 2 S) :
    letI := suzukiOvoidAction m
    ∃ a : {p // p ∈ suzukiOvoidSet m},
      ∀ x ∈ Subgroup.normalizer (S : Set (SuzukiMatrixGroup m)), x • a = a := by
  let := suzukiOvoidAction m
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ Nat.card {p // p ∈ suzukiOvoidSet m} := by
    rw [suzuki_ovoid_card]
    have h2 : 2 ∣ (2 ^ (2 * m + 1)) ^ 2 :=
      (dvd_pow_self 2 (Nat.succ_ne_zero _)).pow two_ne_zero
    omega
  obtain ⟨a, ha⟩ := hSp.nonempty_fixed_point_of_prime_not_dvd_card
    {p // p ∈ suzukiOvoidSet m} hodd
  have hS2 : 2 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hS (Subgroup.card_eq_one.mp (by simpa using hk))
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 hS2
  have hu2 : orderOf (u : SuzukiMatrixGroup m) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have huniq := suzuki_ovoid_involution_unique_fixed m hm _ hu2
  have hfix : ∀ s : S, s • a = a := fun s => (MulAction.mem_fixedPoints.mp ha) s
  refine ⟨a, fun x hx => ?_⟩
  have hxa : ∀ s ∈ S, s • (x • a) = x • a := by
    intro s hs
    have hs' : x⁻¹ * s * x ∈ S := (Subgroup.mem_normalizer_iff''.mp hx s).mp hs
    have h1 : (x⁻¹ * s * x) • a = a := hfix ⟨_, hs'⟩
    calc s • (x • a) = x • ((x⁻¹ * s * x) • a) := by
          rw [smul_smul, smul_smul]; simp [mul_assoc]
      _ = x • a := by rw [h1]
  have hua : (u : SuzukiMatrixGroup m) • a = a := hfix u
  have hux : (u : SuzukiMatrixGroup m) • (x • a) = x • a := hxa u u.2
  exact huniq.unique hux hua

theorem not_five_dvd_card_normalizer
    (hm : 0 < m) {S : Subgroup (SuzukiMatrixGroup m)}
    (hS : S ≠ ⊥) (hSp : IsPGroup 2 S) :
    ¬ 5 ∣ Nat.card (Subgroup.normalizer (S : Set (SuzukiMatrixGroup m))) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.normalizer (S : Set (SuzukiMatrixGroup m))) 5 h5
  obtain ⟨a, ha⟩ := exists_fixed_point_normalizer hm hS hSp
  have hord : orderOf (x : SuzukiMatrixGroup m) = 5 := by rw [Subgroup.orderOf_coe, hx]
  exact not_mem_stabilizer_of_orderOf_five hm hord a (ha x x.2)

theorem card_centralizer_dvd
    (hm : 0 < m) {x : SuzukiMatrixGroup m} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set (SuzukiMatrixGroup m))) ∣
      (2 ^ (2 * m + 1)) ^ 2 + 1 :=
  suzuki_ovoid_derangement_full_centralizer_card_dvd m hm x
    (fun a => not_mem_stabilizer_of_orderOf_five hm hx a)

end Ovoid

variable {n : ℕ}

theorem sz_involution_centralizer (hn : 1 ≤ n) (u : Sz n) (hu : orderOf u = 2) :
    IsPGroup 2 (Subgroup.centralizer ({u} : Set (Sz n))) := by
  have key : ∀ G : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))),
      G = SuzukiMatrixGroup n → ∀ u : G, orderOf u = 2 →
        IsPGroup 2 (Subgroup.centralizer ({u} : Set G)) := by
    rintro G rfl u hu
    exact suzuki_involution_centralizer_isPGroup n hn u hu
  exact key _ (sz_eq_suzukiMatrixGroup n) u hu

theorem sz_not_five_dvd_card_normalizer
    (hn : 1 ≤ n) {S : Subgroup (Sz n)} (hS : S ≠ ⊥)
    (hSp : IsPGroup 2 S) : ¬ 5 ∣ Nat.card (Subgroup.normalizer (S : Set (Sz n))) := by
  have key : ∀ G : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))),
      G = SuzukiMatrixGroup n → ∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
        ¬ 5 ∣ Nat.card (Subgroup.normalizer (S : Set G)) := by
    rintro G rfl S hS hSp
    exact not_five_dvd_card_normalizer hn hS hSp
  exact key _ (sz_eq_suzukiMatrixGroup n) S hS hSp

theorem sz_card_centralizer_dvd
    (hn : 1 ≤ n) {x : Sz n} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set (Sz n))) ∣ (2 ^ (2 * n + 1)) ^ 2 + 1 := by
  have key : ∀ G : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))),
      G = SuzukiMatrixGroup n → ∀ x : G, orderOf x = 5 →
        Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ (2 ^ (2 * n + 1)) ^ 2 + 1 := by
    rintro G rfl x hx
    exact card_centralizer_dvd hn hx
  exact key _ (sz_eq_suzukiMatrixGroup n) x hx

theorem sz_isSimpleGroup (hn : 1 ≤ n) : IsSimpleGroup (Sz n) := by
  have := (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  exact (szEquiv n).isSimpleGroup

theorem sz_oddSylow_isCyclic
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) (R : Sylow r (Sz n)) :
    IsCyclic R :=
  CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv (szEquiv n) r hr R

theorem card_sz (hn : 1 ≤ n) :
    Nat.card (Sz n) =
      (2 ^ (2 * n + 1)) ^ 2 * ((2 ^ (2 * n + 1)) ^ 2 + 1) * (2 ^ (2 * n + 1) - 1) := by
  rw [Nat.card_congr (szEquiv n).toEquiv,
    CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula n hn]
  ring

end CFSG.SignalizerFunctorTheorem.McBride.SzModel
