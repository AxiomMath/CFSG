module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.KFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterC0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {n : ℕ}

theorem not_prime_card_suzuki {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ (Nat.card (CFSG.Blueprint.suzukiGroup a K)).Prime := by
  rw [CFSG.LieType.Ree.suzuki_order hK]
  set q := 2 ^ (2 * a + 1) with hq
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdvd : q ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
    refine ⟨q * (q - 1) * (q ^ 2 + 1), ?_⟩
    rw [pow_two]
    ac_rfl
  have hfac : 1 < q * (q - 1) * (q ^ 2 + 1) := by
    have h1 : 1 < q * (q - 1) :=
      Nat.one_lt_mul_iff.mpr ⟨by omega, by omega, Or.inl (by omega)⟩
    exact Nat.one_lt_mul_iff.mpr ⟨by positivity, by positivity, Or.inl h1⟩
  have hlt : q < q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
    calc q = q * 1 := (mul_one q).symm
      _ < q * (q * (q - 1) * (q ^ 2 + 1)) :=
        Nat.mul_lt_mul_of_pos_left hfac (by positivity)
      _ = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by rw [pow_two]; ac_rfl
  exact Nat.not_prime_of_dvd_of_lt hdvd (by omega) hlt

private theorem exists_suzuki_fixed_data (hn : 2 ≤ n)
    (hL : L.Normal) (hSp : IsSp4 ↥L n) (hC : centralizer (L : Set Q) = ⊥) (hodd : Odd n)
    {a : Q} (haL : a ∉ L) (ha : a * a = 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : ↥L ≃* StatedProj (StatedSp 2 K)),
      IsSimpleGroup (fixedSubgroup (MulAut.congr φ (MulAut.conjNormal (H := L) a))) ∧
        ¬ (Nat.card
          (fixedSubgroup (MulAut.congr φ (MulAut.conjNormal (H := L) a)))).Prime := by
  have hcl : StatedClassicalModel ↥L .PSp 2 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hSp (by decide)
  obtain ⟨hadm, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hcl
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hKcard
  obtain ⟨m, hm⟩ := hodd
  have hodd' : Odd n := ⟨m, hm⟩
  have hm1 : 1 ≤ m := by omega
  have hKm : Nat.card K = 2 ^ (2 * m + 1) := by
    rw [← hm]; exact hKcard
  haveI : L.Normal := hL
  let β : MulAut ↥L := MulAut.conjNormal (H := L) a
  have hβ2 : β * β = 1 := by
    change MulAut.conjNormal (H := L) a * MulAut.conjNormal (H := L) a = 1
    rw [← map_mul, ha, map_one]
  let α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr φ β
  have hα2 : α * α = 1 := by
    change MulAut.congr φ β * MulAut.congr φ β = 1
    rw [← map_mul, hβ2, map_one]
  have hαo : α ∉ inner (StatedProj (StatedSp 2 K)) := by
    rintro ⟨p, hp⟩
    exact haL (CFSG.Quasithin.H13.S3320.mem_of_congr_conjNormal_eq hC φ hp.symm)
  have hα1 : α ≠ 1 := fun h => hαo (h ▸ Subgroup.one_mem (inner _))
  have hαord : orderOf α = 2 := orderOf_eq_prime (by rwa [pow_two]) hα1
  have hf : 1 ≤ n := by omega
  obtain ⟨-, -, -, -, -, hγ⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_symplectic_two_exterior_square_automorphism
      hf hKcard
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hoddγ⟩ :=
    hγ (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut K)
      (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_proj)
  obtain ⟨s, hs⟩ := hoddγ hodd' α hαord hαo
  rw [hm] at hs
  obtain ⟨hSimple, -, hLie⟩ :=
    CFSG.SeitzReduction.LinearPilot.psp_suzuki_fixed (m := m) hm1 hKm hα2 s hs
  have hnotPrime : ¬ (Nat.card (fixedSubgroup α)).Prime := by
    obtain ⟨-, a', ha', K', hKf', hKfin', hf', hKcard', ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.twistedB2_iff.1 hLie |>.2
    have hcard : Nat.card (fixedSubgroup α) =
        Nat.card (CFSG.Blueprint.suzukiGroup a' K') := Nat.card_congr e.toEquiv
    rw [hcard]
    exact not_prime_card_suzuki ha' (by rw [← hf']; exact hKcard')
  exact ⟨K, hKf, hKfin, φ, by simpa [β, α] using hSimple,
    by simpa [β, α] using hnotPrime⟩

private theorem isSimpleGroup_inf_centralizer_of_odd
    (hn : 2 ≤ n) (hL : L.Normal) (hSp : IsSp4 ↥L n) (hC : centralizer (L : Set Q) = ⊥)
    (hodd : Odd n) {a : Q} (haL : a ∉ L) (ha : a * a = 1) :
    IsSimpleGroup ↥(L ⊓ centralizer ({a} : Set Q)) ∧
      ¬ (Nat.card ↥(L ⊓ centralizer ({a} : Set Q))).Prime := by
  obtain ⟨K, hKf, hKfin, φ, hSimple, hnotPrime⟩ :=
    exists_suzuki_fixed_data hn hL hSp hC hodd haL ha
  haveI : L.Normal := hL
  let β : MulAut ↥L := MulAut.conjNormal (H := L) a
  let α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr φ β
  let D : Subgroup Q := L ⊓ centralizer ({a} : Set Q)
  have hDle : D ≤ L := inf_le_left
  have hfix : D.subgroupOf L = fixedSubgroup β := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, fixedSubgroup]
    change ((x : Q) ∈ L ∧ (x : Q) ∈ centralizer ({a} : Set Q)) ↔ β x = x
    constructor
    · rintro ⟨-, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      apply Subtype.ext
      change a * (x : Q) * a⁻¹ = (x : Q)
      calc a * (x : Q) * a⁻¹ = (x : Q) * a * a⁻¹ := by rw [hx]
        _ = (x : Q) := by group
    · intro hx
      constructor
      · exact x.2
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hval : a * (x : Q) * a⁻¹ = (x : Q) := by
          have hh := congrArg (fun z : ↥L => (z : Q)) hx
          simpa [β, MulAut.conjNormal_apply] using hh
        calc (x : Q) * a = (a * (x : Q) * a⁻¹) * a := by rw [hval]
          _ = a * (x : Q) := by group
  let Ψ : ↥D ≃* fixedSubgroup α :=
    (Subgroup.subgroupOfEquivOfLe hDle).symm.trans
      ((MulEquiv.subgroupCongr hfix).trans (fixedSubgroupCongrEquiv φ β))
  haveI : IsSimpleGroup (fixedSubgroup α) := by simpa [α, β] using hSimple
  refine ⟨by simpa [D] using Ψ.isSimpleGroup, ?_⟩
  rw [Nat.card_congr Ψ.toEquiv]
  simpa [α, β] using hnotPrime

theorem suzuki_of_odd (hn : 2 ≤ n) (hL : L.Normal)
    (hSp : IsSp4 ↥L n) (hC : centralizer (L : Set Q) = ⊥) (hodd : Odd n) {a : Q} (haL : a ∉ L)
    (ha : a * a = 1) :
    IsSimpleGroup ↥(L ⊓ centralizer ({a} : Set Q)) ∧
      ∃ x y : ↥(L ⊓ centralizer ({a} : Set Q)), x * y ≠ y * x := by
  obtain ⟨hSimple, hnotPrime⟩ :=
    isSimpleGroup_inf_centralizer_of_odd hn hL hSp hC hodd haL ha
  exact ⟨hSimple,
    CFSG.EvenSporadicStandard.Induction.nonabelian_of_isSimpleGroup_of_not_prime hnotPrime⟩

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Model
