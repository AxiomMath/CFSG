module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.GLQ.HNTwoRankInputs
public import Certificates.Certificate2081

public noncomputable section

namespace CFSG.Sporadic.GLQ

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open scoped Matrix

namespace HNTwoRank

abbrev GLHN : Type := GL (Fin 133) (ZMod 5)

abbrev mA : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  NativeSporadic.decode 5 133 1 NativeSporadic.HNSeed1

abbrev mB : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  NativeSporadic.decode 5 133 1 NativeSporadic.HNSeed2

theorem hnA_check : (opsP 5 133).eq
    ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed1) 2) (opsP 5 133).one = true :=
  Certificates.certificate2081.1

theorem hnB_check : (opsP 5 133).eq
    ((opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 3) (opsP 5 133).one = true :=
  Certificates.certificate2081.2.1

theorem mA_sq : mA ^ 2 = 1 := by
  have h := (specP 5 133).pow_eq_one_of_check trivial hnA_check
  rwa [(specP 5 133).toMat_decode] at h

theorem mB_cube : mB ^ 3 = 1 := by
  have h := (specP 5 133).pow_eq_one_of_check trivial hnB_check
  rwa [(specP 5 133).toMat_decode] at h

@[expose] def gA : GLHN := Units.ofPowEqOne mA 2 mA_sq two_ne_zero

@[expose] def gB : GLHN := Units.ofPowEqOne mB 3 mB_cube three_ne_zero

@[expose] def J : Subgroup GLHN := Subgroup.closure {gA, gB}

@[expose] def x : GLHN := runProg (initRegs gA gB) hnProg 1

@[expose] def y : GLHN := runProg (initRegs gA gB) hnProg 2

@[expose] def e (j : Fin 5) : GLHN := signedWord x y (hnWords j)

@[expose] def E : Subgroup GLHN := Subgroup.closure (Set.range e)

theorem hn_check : hnCheck = true :=
  Certificates.certificate2081.2.2

abbrev φ : GLHN →* Matrix (Fin 133) (Fin 133) (ZMod 5) := Units.coeHom _

theorem φ_injective : Function.Injective φ := Units.val_injective

theorem φ_gA : φ gA = mA := Units.val_ofPowEqOne mA 2 mA_sq two_ne_zero

theorem φ_gB : φ gB = mB := Units.val_ofPowEqOne mB 3 mB_cube three_ne_zero

theorem φ_gA_inv : φ gA⁻¹ = mA := by
  have h : φ gA⁻¹ = mA ^ (2 - 1) := coe_inv_ofPowEqOne mA_sq two_ne_zero
  rw [h, show 2 - 1 = 1 from rfl, pow_one]

theorem φ_gB_inv : φ gB⁻¹ = mB ^ 2 := coe_inv_ofPowEqOne mB_cube three_ne_zero

theorem rep_gA : Rep (specP 5 133) φ gA
    ((opsP 5 133).decode NativeSporadic.HNSeed1, (opsP 5 133).decode NativeSporadic.HNSeed1) := by
  have hw := (specP 5 133).decode_wf NativeSporadic.HNSeed1
  refine rep_of hw hw ?_ ?_
  · rw [(specP 5 133).toMat_decode, φ_gA]
  · rw [(specP 5 133).toMat_decode, φ_gA_inv]

theorem rep_gB : Rep (specP 5 133) φ gB
    ((opsP 5 133).decode NativeSporadic.HNSeed2,
      (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2) := by
  have hw := (specP 5 133).decode_wf NativeSporadic.HNSeed2
  refine rep_of hw ((specP 5 133).pow_spec hw 2).1 ?_ ?_
  · rw [(specP 5 133).toMat_decode, φ_gB]
  · rw [((specP 5 133).pow_spec hw 2).2, (specP 5 133).toMat_decode, φ_gB_inv]

theorem e_facts : (∀ j, e j ^ 2 = 1) ∧ (∀ i j, Commute (e i) (e j)) ∧
    ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1 := by
  have h := hn_check
  unfold hnCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hprog, hel⟩ := h
  have hR := regsRep_runProg hnProg hprog (regsRep_initRegs (n := 11) rep_gA rep_gB)
  have hX : ∀ j,
      (specP 5 133).WF (signedWordN (opsP 5 133) hnRegs[1]! hnRegs[2]! (hnWords j)) ∧
      (specP 5 133).toMat (signedWordN (opsP 5 133) hnRegs[1]! hnRegs[2]! (hnWords j)) =
        φ (e j) := fun j =>
    rep_signedWord (hR.2 1 (by norm_num)) (hR.2 2 (by norm_num)) (hnWords j)
  exact OpsSpecFacts.elem2_of_ok (specP 5 133) φ φ_injective e _ hX hel

theorem E_le_J : E ≤ J := by
  rw [E, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  have hgA : gA ∈ J := Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ J := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact signedWord_mem J (runProg_mem J hnProg (initRegs_mem J hgA hgB) 1)
    (runProg_mem J hnProg (initRegs_mem J hgA hgB) 2) _

@[expose] def hnEquivJ : NativeSporadic.HN ≃* J := NativeSporadic.unitSeedEquiv gA gB

end HNTwoRank

open HNTwoRank

theorem hn_two_rank_at_least_five :
    (∀ j, HNTwoRank.e j ^ 2 = 1 ∧ HNTwoRank.e j ≠ 1) ∧
    (∀ i j, Commute (HNTwoRank.e i) (HNTwoRank.e j)) ∧
    (∃ η : Multiplicative (Fin 5 → ZMod 2) →* GL (Fin 133) (ZMod 5),
      (∀ a, η a = (List.ofFn fun i => HNTwoRank.e i ^ (Multiplicative.toAdd a i).val).prod) ∧
      Function.Injective η ∧ η.range = HNTwoRank.E) ∧
    Nat.card HNTwoRank.E = 32 ∧ HNTwoRank.E ≤ HNTwoRank.J ∧
    ∀ (K : Type*) [Group K] [Finite K], Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.HN) →
      (∃ A : Subgroup K, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 32) ∧
        5 ≤ CFSG.pRank 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsq, hcomm, hker⟩ := e_facts
  obtain ⟨η, hη, hinj, hrange, hE, hcard⟩ := exists_elemAbelian_two e hsq hcomm hker
  have hne : ∀ j, e j ≠ 1 := ne_one_of_ker e hker
  have hE' : CFSG.IsElementaryAbelian 2 E := hE
  have hcard' : Nat.card E = 32 := hcard.trans rfl
  refine ⟨fun j => ⟨hsq j, hne j⟩, hcomm, ⟨η, hη, hinj, hrange⟩, hcard', E_le_J,
    fun K _ _ hK => ?_⟩
  obtain ⟨f⟩ := hK
  have hE₀ : CFSG.IsElementaryAbelian 2 (E.subgroupOf J) :=
    CFSG.IsElementaryAbelian.subgroupOf E_le_J
  have hE₀c : Nat.card (E.subgroupOf J) = 2 ^ 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe E_le_J).toEquiv).trans (hcard'.trans rfl)
  obtain ⟨⟨A, hA, hAc⟩, hr⟩ :=
    transport_elemAbelian_two (E.subgroupOf J) hE₀ hE₀c (f.trans hnEquivJ)
  exact ⟨⟨A, hA, hAc.trans rfl⟩, hr⟩

end CFSG.Sporadic.GLQ
