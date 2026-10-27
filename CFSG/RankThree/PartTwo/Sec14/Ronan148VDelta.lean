module

public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.Native.ONThreeFusion
import CFSG.RankThree.GroupTheory.SteinbergBMCentralizerPerfectSupplement
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Orders

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf [Finite X] {H K : Subgroup X}
    (hHK : H ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  have hq : Nat.card (↥(H ⊔ K) ⧸ K.subgroupOf (H ⊔ K)) = Nat.card (↥H ⧸ K.subgroupOf H) :=
    (Nat.card_congr e.toEquiv).symm
  have hs : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv
  have hs' : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left K H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)), hs, hq,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf H), hs']
  ring

theorem not_pow_five_dvd_card_ON :
    ¬ 3 ^ 5 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON := by
  have h := CFSG.RankThree.Native.factorization_card_ON
  intro h5
  have hne : Nat.card CFSG.Blueprint.NativeSporadic.ON ≠ 0 := by
    rw [CFSG.Sporadic.ON.card_ON]
    norm_num
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h5
  omega

theorem not_pow_six_dvd_card_of_isTripleCover_ON [Finite X]
    (h : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) : ¬ 3 ^ 6 ∣ Nat.card X := by
  obtain ⟨hc, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hc,
    Nat.card_congr e.toEquiv]
  intro h6
  apply not_pow_five_dvd_card_ON
  have : 3 ^ 5 * 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.ON * 3 := by
    rw [show (3 : ℕ) ^ 5 * 3 = 3 ^ 6 by norm_num]
    exact h6
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this

theorem card_of_isCentralProductA6Covers [Finite X] (h : IsCentralProductA6Covers X) :
    Nat.card X = 388800 := by
  obtain ⟨U, V, -, hVn, hUV, -, h3, hU, hV⟩ := h
  have hcU := HJRes2.card_of_isTripleCover_six hU
  have hcV := HJRes2.card_of_isTripleCover_six hV
  have hN : U ≤ Subgroup.normalizer (V : Set X) := by
    rw [@Subgroup.normalizer_eq_top _ _ V hVn]
    exact le_top
  have key := card_sup_mul_card_inf hN
  rw [hUV, Subgroup.card_top, h3, hcU, hcV] at key
  omega

theorem pow_dvd_card_quotient_of_not_dvd [Finite X] {N : Subgroup X} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {k : ℕ} (h : 3 ^ k ∣ Nat.card X) : 3 ^ k ∣ Nat.card (X ⧸ N) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at h
  exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)).dvd_of_dvd_mul_right h

theorem pow_dvd_of_pow_dvd_mul_left {m n k : ℕ} (hm : ¬ 3 ∣ m) (h : 3 ^ k ∣ m * n) : 3 ^ k ∣ n :=
  (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)).dvd_of_dvd_mul_left h

end Orders

section Delta

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_theta (X : Subgroup G) :
    X ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) := by
  have hch := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.1
  exact Subgroup.le_normalizer.trans
    (CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_of_characteristic
      (F := aschbacherSolvableCore 3) hch)

theorem not_dvd_card_theta (X : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) := by
  have h := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
  change ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 ↥X).map X.subtype)
  rwa [Subgroup.card_map_of_injective X.subtype_injective]

theorem pow_dvd_card_theta_quot {X : Subgroup G} {k : ℕ} (h : 3 ^ k ∣ Nat.card X) :
    3 ^ k ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
  pow_dvd_card_quotient_of_not_dvd
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1 h

theorem not_pow_four_dvd_card_lB
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B : Subgroup G}
    (hB : IsHyperplane A B) : ¬ 3 ^ 4 ∣ Nat.card (lB A B) := by
  by_cases hex : ∃ b d Lb, IsLBConfig A B b d Lb
  · obtain ⟨b, d, Lb, hc⟩ := hex
    rw [Item148HJ.lB_eq_residual hS hB hc]
    obtain ⟨hdL, -, -, -, -, h6, -⟩ := Item148HJ.resProj_facts hS hB hc
    set φ := Item148HJ.resProj Lb d
    have hrange : Nat.card φ.range = 1080 := HJRes2.card_of_isTripleCover_six h6
    have hker : ¬ 3 ∣ Nat.card φ.ker := by
      have hθ := not_dvd_card_theta Lb
      let ι : φ.ker →* ↥(inSubgroup (aschbacherSolvableCore 3) Lb) :=
        { toFun := fun k => ⟨((k : ↥(inSubgroup perfectResidual
              (Lb ⊓ Subgroup.centralizer ({d} : Set G)))) : G),
            (Item148HJ.mem_ker_resProj _).mp k.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hinj : Function.Injective ι := fun x y hxy => by
        have h1 := congrArg (fun t : ↥(inSubgroup (aschbacherSolvableCore 3) Lb) => (t : G)) hxy
        exact Subtype.ext (Subtype.ext h1)
      exact fun h3 => hθ (h3.trans (Subgroup.card_dvd_of_injective ι hinj))
    have hcard : Nat.card ↥(inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))) =
        Nat.card φ.ker * 1080 := by
      rw [← hrange, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
    rw [hcard]
    intro h4
    have h4' : 3 ^ 4 ∣ 1080 := pow_dvd_of_pow_dvd_mul_left hker h4
    norm_num at h4'
  · push Not at hex
    rw [lB_eq_bot hex, Subgroup.card_bot]
    norm_num

theorem not_pow_six_dvd_card_deltaQ
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A))
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (haΩ : Subgroup.zpowers a ∉ omegaA A) :
    ¬ 3 ^ 6 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h6
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  obtain ⟨-, hcase⟩ := h143 a haA ha1 haΩ Q hQ
  have hN₁ : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN₂ : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN₂C : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.centralizer ({a} : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hCN₁ : Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  rcases hcase with h1 | ⟨b, d, Lb, hbΩ, -, -, -, -, -, -, X, hX, hinv, hXcase⟩
  · rw [h1] at h6
    have hd := card_sup_dvd_card_mul (hN₂C.trans hCN₁)
    rw [sup_comm] at hd
    have h3 := (dvd_pow_self 3 (by norm_num : 6 ≠ 0)).trans (h6.trans hd)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hN₂ h
    · exact hN₁ h
  · have hXC : X ≤ Subgroup.centralizer ({a} : Set G) := by
      rcases hXcase with ⟨hXc, -, -⟩ | ⟨-, ⟨𝒳, h𝒳, -, rfl⟩, -⟩
      · exact le_centralizer_of_mem_thetaComponentsAt hXc
      · exact sSup_le fun K hK => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hK)
    have hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
          (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) := by
      rw [hX, sup_right_comm, sup_comm]
    rw [hΔ] at h6
    have hd1 := card_sup_dvd_card_mul (H := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
      (K := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X)
      ((pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le haA))
    have hd2 := card_sup_dvd_card_mul (H := X)
      (K := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) (hXC.trans hCN₁)
    rw [sup_comm] at hd2
    have h6X : 3 ^ 6 ∣ Nat.card X := by
      have h1 := pow_dvd_of_pow_dvd_mul_left hN₂ (h6.trans hd1)
      have h2 := h1.trans hd2
      rw [mul_comm] at h2
      exact pow_dvd_of_pow_dvd_mul_left hN₁ h2
    rcases hXcase with ⟨-, hXeq, -⟩ | ⟨-, -, htype⟩
    ·
      set B := Subgroup.closure ({a, b} : Set G) with hBdef
      have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
      have hab : b ∉ Subgroup.zpowers a := by
        intro hb
        have hb3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
        have ha3 : a ^ 3 = 1 := hS.toSec13Data.isElemAbelian.2 a haA
        have hacard : Nat.card (Subgroup.zpowers a) = 3 := by
          rw [Nat.card_zpowers]
          exact orderOf_eq_prime ha3 ha1
        have heq : Subgroup.zpowers b = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) (by rw [hacard, hb3])
        exact haΩ (heq ▸ hbΩ)
      have hB : IsHyperplane A B := by
        have hAab := hS.toSec13Data.isElemAbelian.1
        have hcomm : a * b = b * a :=
          congrArg Subtype.val (hAab.is_comm.comm ⟨a, haA⟩ ⟨b, hbA⟩)
        have h9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine hcomm
          (hS.toSec13Data.isElemAbelian.2 a haA) ha1 (hS.toSec13Data.isElemAbelian.2 b hbA) hab
        have hBeq : B = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
          rw [hBdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
            ← Subgroup.closure_union]
          rfl
        refine ⟨?_, ?_⟩
        · rw [hBeq]
          exact sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
        · rw [hBeq, h9, hS.isE27.2]
      have hle0 : lB A B ≤ X :=
        calc lB A B ≤ lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X := le_sup_left
          _ = X := hXeq.symm
      have hle : lB A B ≤ Subgroup.normalizer
          ((inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) :=
        hle0.trans (le_normalizer_theta X)
      have hd3 := card_sup_dvd_card_mul hle
      rw [← hXeq] at hd3
      have h6B : 3 ^ 6 ∣ Nat.card (lB A B) := by
        have := h6X.trans hd3
        rw [mul_comm] at this
        exact pow_dvd_of_pow_dvd_mul_left (not_dvd_card_theta X) this
      exact not_pow_four_dvd_card_lB hS hB ((pow_dvd_pow 3 (by norm_num : 4 ≤ 6)).trans h6B)
    ·
      have h6Q := pow_dvd_card_theta_quot h6X
      rcases htype with hON | hA6 | hcp
      · exact not_pow_six_dvd_card_of_isTripleCover_ON hON h6Q
      · rw [HJRes2.card_of_isTripleCover_six hA6] at h6Q
        norm_num at h6Q
      · rw [card_of_isCentralProductA6Covers hcp] at h6Q
        norm_num at h6Q

end Delta

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
