module

public import CFSG.Quasithin.Background.HPairGen
public import CFSG.Quasithin.Background.P3Sp44Comm
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K]

@[expose] noncomputable def upSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : StatedSp 2 K :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.upperUnipotentSp 2 K hC

theorem coe_upSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((upSp hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 C 0 1 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp hC

theorem lowMat_mem {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (fromBlocks 1 0 C 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
        fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 C 1 = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_transpose, hC, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_one, transpose_zero, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg]
  rw [neg_add_cancel]

@[expose] noncomputable def lowSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : StatedSp 2 K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (fromBlocks 1 0 C 1)
      (by rw [det_fromBlocks_zero₁₂, det_one, one_mul]; exact one_ne_zero),
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr (lowMat_mem hC)⟩

theorem coe_lowSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((lowSp hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 0 C 1 := rfl

theorem up_mulVec (a b d : K) (v : Fin 2 ⊕ Fin 2 → K) :
    fromBlocks 1 (sym2 a b d) 0 1 *ᵥ v =
      v + Pi.single ι₀ (a * v ι₂ + b * v ι₃) + Pi.single ι₁ (b * v ι₂ + d * v ι₃) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [sym2, fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem low_mulVec (a b d : K) (v : Fin 2 ⊕ Fin 2 → K) :
    fromBlocks 1 0 (sym2 a b d) 1 *ᵥ v =
      v + Pi.single ι₂ (a * v ι₀ + b * v ι₁) + Pi.single ι₃ (b * v ι₀ + d * v ι₁) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [sym2, fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    ring

theorem isNatIrr_statedSp : PairG.IsNatIrr (StatedSp 2 K) := by
  intro U hU
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  have hup : ∀ a b d, ∀ u ∈ U,
      Pi.single ι₀ (a * u ι₂ + b * u ι₃) + Pi.single ι₁ (b * u ι₂ + d * u ι₃) ∈ U :=
    fun a b d u hu => by
      have := U.sub_mem (hU _ (upSp (sym2_transpose a b d)).2 u hu) hu
      rwa [coe_upSp, up_mulVec, add_assoc, add_sub_cancel_left] at this
  have hlow : ∀ a b d, ∀ u ∈ U,
      Pi.single ι₂ (a * u ι₀ + b * u ι₁) + Pi.single ι₃ (b * u ι₀ + d * u ι₁) ∈ U :=
    fun a b d u hu => by
      have := U.sub_mem (hU _ (lowSp (sym2_transpose a b d)).2 u hu) hu
      rwa [coe_lowSp, low_mulVec, add_assoc, add_sub_cancel_left] at this
  have hup0 : ∀ c, ∀ u ∈ U, Pi.single ι₀ (c * u ι₂) ∈ U := fun c u hu => by
    simpa using hup c 0 0 u hu
  have hup1 : ∀ c, ∀ u ∈ U, Pi.single ι₁ (c * u ι₃) ∈ U := fun c u hu => by
    simpa using hup 0 0 c u hu
  have hlow0 : ∀ c, ∀ u ∈ U, Pi.single ι₂ (c * u ι₀) ∈ U := fun c u hu => by
    simpa using hlow c 0 0 u hu
  have hlow1 : ∀ c, ∀ u ∈ U, Pi.single ι₃ (c * u ι₁) ∈ U := fun c u hu => by
    simpa using hlow 0 0 c u hu
  have hup01 : ∀ c, ∀ u ∈ U, Pi.single ι₀ (c * u ι₃) + Pi.single ι₁ (c * u ι₂) ∈ U :=
    fun c u hu => by simpa using hup 0 c 0 u hu
  have l0 : (∀ c : K, Pi.single ι₀ c ∈ U) → ∀ c : K, Pi.single ι₂ c ∈ U := fun h0 c => by
    simpa using hlow0 c _ (h0 1)
  have l2 : (∀ c : K, Pi.single ι₂ c ∈ U) → ∀ c : K, Pi.single ι₀ c ∈ U := fun h2 c => by
    simpa using hup0 c _ (h2 1)
  have l1 : (∀ c : K, Pi.single ι₁ c ∈ U) → ∀ c : K, Pi.single ι₃ c ∈ U := fun h1 c => by
    simpa using hlow1 c _ (h1 1)
  have l3 : (∀ c : K, Pi.single ι₃ c ∈ U) → ∀ c : K, Pi.single ι₀ c ∈ U := fun h3 c => by
    simpa using hup01 c _ (h3 1)
  have l2' : (∀ c : K, Pi.single ι₂ c ∈ U) → ∀ c : K, Pi.single ι₁ c ∈ U := fun h2 c => by
    simpa using hup01 c _ (h2 1)
  have hall : (∀ c : K, Pi.single ι₂ c ∈ U) → ∀ i c, Pi.single i c ∈ U := by
    intro h2 i c
    rcases i with i | i <;> fin_cases i
    · exact l2 h2 c
    · exact l2' h2 c
    · exact h2 c
    · exact l1 (l2' h2) c
  obtain ⟨⟨u, hu⟩, hu0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp h
  have hu0' : u ≠ 0 := fun h' => hu0 (Subtype.ext h')
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu0' (funext hc)
  have key : ∀ c : K, Pi.single ι₂ c ∈ U := by
    rcases j with j | j <;> fin_cases j
    · intro c
      have hj' : u ι₀ ≠ 0 := hj
      have := hlow0 (c / u ι₀) u hu
      rwa [div_mul_cancel₀ c hj'] at this
    · intro c
      have hj' : u ι₁ ≠ 0 := hj
      have h3 : ∀ c : K, Pi.single ι₃ c ∈ U := fun c => by
        have := hlow1 (c / u ι₁) u hu
        rwa [div_mul_cancel₀ c hj'] at this
      exact l0 (l3 h3) c
    · intro c
      have hj' : u ι₂ ≠ 0 := hj
      have h0 : ∀ c : K, Pi.single ι₀ c ∈ U := fun c => by
        have := hup0 (c / u ι₂) u hu
        rwa [div_mul_cancel₀ c hj'] at this
      exact l0 h0 c
    · intro c
      have hj' : u ι₃ ≠ 0 := hj
      have h1 : ∀ c : K, Pi.single ι₁ c ∈ U := fun c => by
        have := hup1 (c / u ι₃) u hu
        rwa [div_mul_cancel₀ c hj'] at this
      exact l0 (l3 (l1 h1)) c
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact AddSubgroup.sum_mem _ fun k _ => hall key k (w k)

theorem hasScalarCommutant_statedSp : HasScalarCommutant (StatedSp 2 K) :=
  fun f hf => CFSG.Quasithin.G11.G118.sp44_commutant f hf

variable [CharP K 2]

theorem tauSp_upSp_mulVec (a b d : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (((tauSp (upSp (sym2_transpose a b d)) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      v + Pi.single ι₀ (d * v ι₁ + (a * d + b ^ 2) * v ι₂ + a * v ι₃) +
        Pi.single ι₁ (a * v ι₂) + Pi.single ι₃ (d * v ι₂) := by
  rw [coe_tauSp, coe_upSp]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [CFSG.QuasithinUnique.Lin2.Five.tauMat_apply, CFSG.QuasithinUnique.Lin2.Five.tauPair,
      Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, sym2, fromBlocks,
      CharTwo.sub_eq_add] <;> ring

theorem tauSp_upSp_diag_mulVec (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (((tauSp (upSp (sym2_transpose c 0 0)) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      v + Pi.single ι₀ (c * v ι₃) + Pi.single ι₁ (c * v ι₂) := by
  rw [tauSp_upSp_mulVec]
  simp

end Sp4

end H

end CFSG.Quasithin
