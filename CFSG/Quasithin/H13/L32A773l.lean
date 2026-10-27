module

public import CFSG.Quasithin.H13.L32A773k
import CFSG.Foundations.DecideEnum
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.L32A774k
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.H13.U3L14D4
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def stU1 : H6.Γ := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def stU2 : H6.Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

open scoped CFSG.DecideEnum in
theorem ll_o2_eq : ∀ g : H6.Γ, g ∈ H6.Ll →
    (∀ h : H6.Γ, h ∈ H6.Ll → (g * h * g⁻¹ * h⁻¹) ^ 4 = 1) →
    g = 1 ∨ g = stU1 ∨ g = stU2 ∨ g = stU1 * stU2 := by
  simp only [CFSG.DecideEnum.inv_eq_invSL3]
  decide +kernel

@[expose] def IsStC (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  RuType.stAct stU1 M = M ∧ RuType.stAct stU2 M = M

instance : DecidablePred IsStC := fun _ => inferInstanceAs (Decidable (_ ∧ _))

@[expose] def IsStW (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop :=
  IsStC (RuType.stAct stU1 M - M) ∧ IsStC (RuType.stAct stU2 M - M)

instance : DecidablePred IsStW := fun _ => inferInstanceAs (Decidable (_ ∧ _))

@[expose] def stWF1 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, 0, 0; 0, 0, 0; A 0 0, A 0 1, 0]

@[expose] def stWF2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![A 1 2 + A 1 1, A 0 2 + A 0 0, 0; 0, 0, 0; A 1 0, A 1 1, A 1 2 + A 1 1]

private theorem stAct_eq_invSL3 (g : H6.Γ) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    RuType.stAct g A = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
      (CFSG.DecideEnum.invSL3 g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  congrArg (fun h : H6.Γ => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
    (h : Matrix (Fin 3) (Fin 3) (ZMod 2))) (CFSG.DecideEnum.inv_eq_invSL3 g)

theorem st_W_decomp : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 → IsStW A →
    (stWF1 A).trace = 0 ∧ (stWF2 A).trace = 0 ∧
      A = (RuType.stAct stU1 (stWF1 A) - stWF1 A) + (RuType.stAct stU2 (stWF2 A) - stWF2 A) := by
  delta IsStW IsStC
  simp only [stAct_eq_invSL3]
  decide +kernel

theorem st_W_u12 : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsStW A →
    IsStC (RuType.stAct (stU1 * stU2) A - A) := by
  delta IsStW IsStC
  simp only [stAct_eq_invSL3]
  decide +kernel

theorem st_card_W :
    (Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3) (ZMod 2) => A.trace = 0 ∧ IsStW A).card =
      64 := by
  delta IsStW IsStC
  simp only [stAct_eq_invSL3]
  decide +kernel

theorem st_card_C :
    (Finset.univ.filter fun A : Matrix (Fin 3) (Fin 3) (ZMod 2) => A.trace = 0 ∧ IsStC A).card =
      4 := by
  delta IsStW IsStC
  simp only [stAct_eq_invSL3]
  decide +kernel

theorem st_C_zero : IsStC 0 := by decide

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem theta_QH_mem {θ : ↥L →* H6.Γ} (hθs : Function.Surjective θ)
    (hθLl : ∀ l : ↥L, θ l ∈ H6.Ll ↔ (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G))
    (q : ↥L) (hq : (q : G) ∈ pCoreOf 2 (hz T V)) :
    θ q = 1 ∨ θ q = stU1 ∨ θ q = stU2 ∨ θ q = stU1 * stU2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hNC := normalizer_eq_centralizer_of_card_two hV1
  have hqH : (q : G) ∈ hz T V := pCoreOf_le 2 _ hq
  have hθq : θ q ∈ H6.Ll := (hθLl q).mpr (by rw [hNC]; exact hqH)
  refine ll_o2_eq _ hθq fun h hh => ?_
  obtain ⟨l, rfl⟩ := hθs h
  have hlH : (l : G) ∈ hz T V := by
    have := (hθLl l).mp hh
    rwa [hNC] at this
  have hc : (q * l * q⁻¹ * l⁻¹ : ↥L) ∈ (pCoreOf 2 (hz T V)).subgroupOf L := by
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (q : G) * (l : G) * (q : G)⁻¹ * (l : G)⁻¹ = q * ((l : G) * (q : G)⁻¹ * (l : G)⁻¹) by
      group]
    exact mul_mem hq ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (hz T V) hlH) _).mp (inv_mem hq))
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨_, Subgroup.mem_subgroupOf.mp hc⟩
  have h1 : (q * l * q⁻¹ * l⁻¹) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have h2 := congrArg θ h1
  rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  exact gamma_pow_four h2

omit [Finite G] C in
theorem chi_comm {θ : ↥L →* H6.Γ}
    {χ : ↥(sL T L V) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))}
    (hχe : ∀ (l : ↥L) (s t : ↥(sL T L V)), (t : G) = l * s * (l : G)⁻¹ →
      χ t = Multiplicative.ofAdd (RuType.stAct (θ l) (Multiplicative.toAdd (χ s))))
    (l : ↥L) (s : ↥(sL T L V)) (h : (l : G) * s * (l : G)⁻¹ * (s : G)⁻¹ ∈ sL T L V) :
    Multiplicative.toAdd (χ ⟨_, h⟩) =
      RuType.stAct (θ l) (Multiplicative.toAdd (χ s)) - Multiplicative.toAdd (χ s) := by
  have hls : (l : G) * s * (l : G)⁻¹ ∈ sL T L V :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ l.2) s).mp s.2
  have e : (⟨_, h⟩ : ↥(sL T L V)) = ⟨_, hls⟩ * s⁻¹ := Subtype.ext (by simp)
  rw [e, map_mul, map_inv, hχe l s ⟨_, hls⟩ rfl, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

end Ctx73

end CFSG.Quasithin.H13.L32A
