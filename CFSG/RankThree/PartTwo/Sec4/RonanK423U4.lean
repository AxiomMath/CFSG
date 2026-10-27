module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423Decomp
public import CFSG.RankThree.PartTwo.Sec4.RonanK423U4Long
public import CFSG.RankThree.PartTwo.Sec4.RonanK423U4Short
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.DataGlue
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofU4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep
public import CFSG.LieType.SeitzGeneration.UnitarySplit

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG Matrix
open CFSG.RankThree.PartTwo.Sec21.U4Lines
open CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
  (exists_normal_form_SU ne_inv_of_cube mem_centralizer_zpowers_of_commute)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.Assembly.RankThreeEven (projSU projSL)
open CFSG.RankThree.PartOne.KFU (diagU diagU_val)
open CFSG.GH74.GLS.IVK.GHInv (isQuasisimple_sl2)
open CFSG.RankThree.PartTwo.Sec8.Item86ResProof (center_specialLinearGroup_two_eq_bot)
open CFSG.AGLEmbeddingD2.Wilson.Census423Three (census423_of_equiv_alpha closure_centralizers_of_map)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open scoped commutatorElement MatrixGroups



section Classes

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem centralizer_eq_subgroupOf (σ : F ≃+* F) (y : ↥(SU σ 4)) :
    Subgroup.centralizer ({y} : Set ↥(SU σ 4)) =
      (SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
        Set (GL (Fin 4) F))).subgroupOf (SU σ 4) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have h' : (x : GL (Fin 4) F) * (y : GL (Fin 4) F) = (y : GL (Fin 4) F) * (x : GL (Fin 4) F) :=
      congrArg Subtype.val h
    exact mem_centralizer_zpowers_of_commute h'
  · rintro ⟨-, h⟩
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp h (y : GL (Fin 4) F) (Subgroup.mem_zpowers _)).symm

theorem centralProductData_long (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    (hq : CFSG.IsQuasisimple ↥(longSL σ))
    (hZ : ∀ z ∈ Subgroup.center ↥(longSL σ), ∃ k : ℕ, z ^ 3 ^ k = 1)
    (y : ↥(SU σ 4)) {α β γ : F}
    (hy : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, β, β, γ])
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    CentralProductData (Subgroup.centralizer ({y} : Set ↥(SU σ 4))) := by
  obtain ⟨A, hA, hAR, hdec⟩ := long_decomp σ hσ hy hαβ hαγ hβγ
  have hLS : longSL σ ≤ SU σ 4 := longSL_le_SU σ
  have hLC : longSL σ ≤ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F)) := le_inf hLS (longSL_le_centralizer σ hy)
  have hperf : ⁅longSL σ, longSL σ⁆ = longSL σ := Subgroup.isPerfect_iff.mp hq.1
  have hCR : ⁅SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F)), SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F))⁆ = longSL σ := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact commutator_mem_longSL σ hy hαβ hαγ hβγ hg hh
    · calc longSL σ = ⁅longSL σ, longSL σ⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hLC hLC
  rw [centralizer_eq_subgroupOf]
  exact centralProductData_subgroupOf (SU σ 4) inf_le_left hCR hq hZ hA hAR hdec

theorem centralProductData_short (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    (hq : CFSG.IsQuasisimple ↥(shortSL σ))
    (hZ : ∀ z ∈ Subgroup.center ↥(shortSL σ), ∃ k : ℕ, z ^ 3 ^ k = 1)
    (y : ↥(SU σ 4)) {α β : F}
    (hy : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal ![α, α, β, β])
    (hαβ : α ≠ β) :
    CentralProductData (Subgroup.centralizer ({y} : Set ↥(SU σ 4))) := by
  obtain ⟨A, hA, hAR, hdec⟩ := short_decomp σ hσ hy hαβ
  have hLS : shortSL σ ≤ SU σ 4 := shortSL_le_SU σ hσ
  have hLC : shortSL σ ≤ SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F)) := le_inf hLS (shortSL_le_centralizer σ hy)
  have hperf : ⁅shortSL σ, shortSL σ⁆ = shortSL σ := Subgroup.isPerfect_iff.mp hq.1
  have hCR : ⁅SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F)), SU σ 4 ⊓ Subgroup.centralizer (Subgroup.zpowers (y : GL (Fin 4) F) :
      Set (GL (Fin 4) F))⁆ = shortSL σ := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact commutator_mem_shortSL σ hy hαβ hg hh
    · calc shortSL σ = ⁅shortSL σ, shortSL σ⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hLC hLC
  rw [centralizer_eq_subgroupOf]
  exact centralProductData_subgroupOf (SU σ 4) inf_le_left hCR hq hZ hA hAR hdec

end Classes

section RootGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem longSL_data {b : ℕ} (hb : 2 ≤ b) (hF : Nat.card F = (2 ^ b) ^ 2) :
    CFSG.IsQuasisimple ↥(longSL (unitaryInvolution F 2 b)) ∧
      ∀ z ∈ Subgroup.center ↥(longSL (unitaryInvolution F 2 b)), ∃ k : ℕ, z ^ 3 ^ k = 1 := by
  obtain ⟨e⟩ := nonempty_longSL_mulEquiv (F := F) (b := b) (by omega) hF
  have hP := Sec8.Item87Proof.isQuasisimple_projSL_two hb
  haveI := Sec21.isSimpleGroup_projSL_two hb
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hP, fun z hz => ?_⟩
  have hc := center_eq_bot_of_mulEquiv e (center_eq_bot_of_simple hP)
  rw [hc, Subgroup.mem_bot] at hz
  exact ⟨0, by simp [hz]⟩

theorem shortSL_data (σ : F ≃+* F) (hF4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥(shortSL σ) ∧
      ∀ z ∈ Subgroup.center ↥(shortSL σ), ∃ k : ℕ, z ^ 3 ^ k = 1 := by
  have e : ↥(shortSL σ) ≃* SL(2, F) := (MonoidHom.ofInjective (iotaS_injective σ)).symm
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 (isQuasisimple_sl2 hF4),
    fun z hz => ?_⟩
  have hc := center_eq_bot_of_mulEquiv e center_specialLinearGroup_two_eq_bot
  rw [hc, Subgroup.mem_bot] at hz
  exact ⟨0, by simp [hz]⟩

end RootGroups

theorem census423_of_u4 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n) (hev : Even n)
    (e : X ≃* projSU 4 2 n) (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥) :
    Census423 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hF : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := CFSG.RankThree.PartTwo.Sec4.Res417Six.card_galoisField_two_mul hn
  have h3 : 3 ∣ 2 ^ n - 1 := CFSG.RankThree.PartTwo.Sec4.Res417Six.three_dvd_two_pow_sub_one hev
  have hF4 : 4 ≤ Nat.card (GaloisField 2 (2 * n)) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)) 2
  have hσ : ∀ c, unitaryInvolution (GaloisField 2 (2 * n)) 2 n
      (unitaryInvolution (GaloisField 2 (2 * n)) 2 n c) = c :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF).invol
  obtain ⟨eS⟩ := nonempty_projSU_mulEquiv_SU n hn
  set σ := unitaryInvolution (GaloisField 2 (2 * n)) 2 n with hσdef
  refine census423_of_equiv_alpha (e.trans eS) ?_
  intro D hDc hDexp hD9
  have hq' : CFSG.IsQuasisimple ↥(SU σ 4) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr (e.trans eS)).1 hq
  have hZ' : Subgroup.center ↥(SU σ 4) = ⊥ := center_eq_bot_of_mulEquiv (e.trans eS).symm hZ
  refine alphaVanishes_of_centralProduct hq' hZ' hDc hDexp hD9 (fun b hbD hb1 => ?_) ?_
  · have hb3 : b ^ 3 = 1 := hDexp b hbD
    have hA3 : (b : GL (Fin 4) (GaloisField 2 (2 * n))) ^ 3 = 1 := by
      have := congrArg Subtype.val hb3
      simpa using this
    have hA1 : (b : GL (Fin 4) (GaloisField 2 (2 * n))) ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨P, α, hP, hα3, hα1, hD⟩ := exists_normal_form_SU hF h3 b.2 hA3 hA1
    set y := conjAut (SU σ 4) P hP b with hy
    have hycoe : (y : GL (Fin 4) (GaloisField 2 (2 * n))) = P * b * P⁻¹ := rfl
    have hbd : CentralProductData (Subgroup.centralizer ({y} : Set ↥(SU σ 4))) := by
      rcases hD with hD | hD
      · have ht : ((y : GL (Fin 4) (GaloisField 2 (2 * n))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) =
            diagonal ![(α : GaloisField 2 (2 * n)), 1, 1, ((α⁻¹ : (GaloisField 2 (2 * n))ˣ) :
              GaloisField 2 (2 * n))] := by
          rw [hycoe, hD, diagU_val]
          congr 1
          funext i
          fin_cases i <;> rfl
        have h1 : (α : GaloisField 2 (2 * n)) ≠ 1 := fun h => hα1 (Units.ext h)
        have h2 : (1 : GaloisField 2 (2 * n)) ≠ ((α⁻¹ : (GaloisField 2 (2 * n))ˣ) :
            GaloisField 2 (2 * n)) := fun h => hα1 (by
          have : α⁻¹ = 1 := Units.ext h.symm
          rw [← inv_inv α, this, inv_one])
        obtain ⟨hqL, hZL⟩ := longSL_data hn2 hF
        exact centralProductData_long σ hσ hqL hZL y ht h1 (ne_inv_of_cube hα3 hα1) h2
      · have ht : ((y : GL (Fin 4) (GaloisField 2 (2 * n))) :
            Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n))) =
            diagonal ![(α : GaloisField 2 (2 * n)), α, ((α⁻¹ : (GaloisField 2 (2 * n))ˣ) :
              GaloisField 2 (2 * n)), ((α⁻¹ : (GaloisField 2 (2 * n))ˣ) :
              GaloisField 2 (2 * n))] := by
          rw [hycoe, hD, diagU_val]
          congr 1
          funext i
          fin_cases i <;> rfl
        obtain ⟨hqS, hZS⟩ := shortSL_data σ hF4
        exact centralProductData_short σ hσ hqS hZS y ht (ne_inv_of_cube hα3 hα1)
    have := hbd.of_map (conjAut (SU σ 4) P hP).symm
    rwa [hy, MulEquiv.symm_apply_apply] at this
  · set φ : ↥(SU σ 4) ≃* unitarySU 2 n (GaloisField 2 (2 * n)) 4 :=
      eS.symm.trans (CFSG.RankThree.PartTwo.Sec4.Res417Six.unitarySUEquivProjSU hn).symm with hφ
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
    have hcomm : ∀ x ∈ D.map φ.toMonoidHom, ∀ y ∈ D.map φ.toMonoidHom, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hDc a ha a' ha']
    have hexp : ∀ x ∈ D.map φ.toMonoidHom, x ^ 3 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hDexp a ha, map_one]
    have hcard : Nat.card (D.map φ.toMonoidHom) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective φ.injective, hD9]
      norm_num
    have hplane := CFSG.LieType.SeitzGeneration.unitarySU_planeGen_split hU Nat.prime_three
      (by norm_num) (by simpa using h3) (by norm_num : 2 ≤ 4) (D.map φ.toMonoidHom) hcomm hexp hcard
    have hg := closure_centralizers_of_map φ D hplane
    refine hg.trans (Subgroup.closure_mono ?_)
    rintro x ⟨d, hd, hd1, hx⟩
    exact ⟨d, hd, hd1, Subgroup.mem_centralizer_singleton_iff.mp hx⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK423
