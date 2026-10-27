module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2PCore
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem L3C2Gen_conj_mem_centralizer {S : Set G} {g y : G} (hg : g ∈ Subgroup.centralizer S)
    (hy : y ∈ Subgroup.centralizer S) : g * y * g⁻¹ ∈ Subgroup.centralizer S := by
  refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
  have hsg : Commute s g := Subgroup.mem_centralizer_iff.mp hg s hs
  have hsy : Commute s y := Subgroup.mem_centralizer_iff.mp hy s hs
  exact (hsg.mul_right hsy).mul_right hsg.inv_right

omit [Finite G] in
theorem L3C2Gen_le_normalizer_centralizer (S : Set G) :
    Subgroup.centralizer S ≤ Subgroup.normalizer (Subgroup.centralizer S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact L3C2Gen_conj_mem_centralizer hg hx
  · intro hx
    have h := L3C2Gen_conj_mem_centralizer ((Subgroup.centralizer S).inv_mem hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

omit [Finite G] in
theorem L3C2Gen_exists_mul_mem_sup {N P : Subgroup G} (hP : P ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ P) : ∃ n ∈ N, ∃ p ∈ P, n * p = x := by
  have hx' : x ∈ ((N ⊔ P : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N P hP] at hx'
  obtain ⟨n, hn, p, hp, hnp⟩ := Set.mem_mul.mp hx'
  exact ⟨n, hn, p, hp, hnp⟩

theorem L3C2Gen_coprime_three_card_of_two {T : Subgroup G} (hT2 : IsPGroup 2 T) :
    Nat.Coprime 3 (Nat.card T) := by
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem L3C2Gen_inf_centralizer_le {A T : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) {B : Subgroup G}
    (hB : IsHyperplane A B)
    (hq : T ⊓ Subgroup.centralizer (B : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    T ⊓ Subgroup.centralizer (B : Set G) ≤
      (T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) ⊔
        (T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) := by
  haveI : IsMulCommutative A := hA.1
  have hA3 : IsPGroup 3 A := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 3 A hA
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have hbA : b ∈ A := hB.1 hb
    exact congrArg Subtype.val (mul_comm' (⟨b, hbA⟩ : A) ⟨a, ha⟩)
  have hBA : (B : Set G) ⊆ (A : Set G) := SetLike.coe_subset_coe.mpr hB.1
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set CA := Subgroup.centralizer (A : Set G) with hCA
  set NB := pPrimeCoreOf 3 CB with hNB
  set P := pPrimeCoreOf 3 CA with hP
  have hCAB : CA ≤ CB := Subgroup.centralizer_le hBA
  have hCBN : CB ≤ Subgroup.normalizer (NB : Set G) := le_normalizer_pPrimeCoreOf_gen 3 CB
  have hAN : A ≤ Subgroup.normalizer (NB : Set G) := hAC.trans hCBN
  have hCAN : CA ≤ Subgroup.normalizer (NB : Set G) := hCAB.trans hCBN
  have hPCA : P ≤ CA := pPrimeCoreOf_le_self 3 CA
  have hPN : P ≤ Subgroup.normalizer (NB : Set G) := hPCA.trans hCAN
  have hdecomp : ∀ m ∈ T ⊓ CB, ∃ n ∈ NB, ∃ p ∈ P, n * p = m :=
    fun m hm => L3C2Gen_exists_mul_mem_sup hPN (hq hm)
  have hcopT := L3C2Gen_coprime_three_card_of_two hT2
  have hcompl : ¬ 3 ∣ Nat.card (T ⊓ CB : Subgroup G) := by
    have hdvd : Nat.card (T ⊓ CB : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.Coprime.of_dvd_right hdvd hcopT)
  have hnorm : A ≤ Subgroup.normalizer ((T ⊓ CB : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha m hm => ?_
    obtain ⟨hmT, hmC⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hAT a ha m hmT,
      Subgroup.le_normalizer_iff.mp (L3C2Gen_le_normalizer_centralizer (B : Set G)) a (hAC ha) m hmC⟩
  have hfact := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A (T ⊓ CB) hA3 hcompl hnorm
  have hcomm : ⁅(T ⊓ CB), A⁆ ≤ T ⊓ NB := by
    refine Subgroup.commutator_le.mpr fun m hm a ha => ?_
    have hmT : m ∈ T := (Subgroup.mem_inf.mp hm).1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : a * m⁻¹ * a⁻¹ ∈ T := Subgroup.le_normalizer_iff.mp hAT a ha m⁻¹ (T.inv_mem hmT)
      have e : m * a * m⁻¹ * a⁻¹ = m * (a * m⁻¹ * a⁻¹) := by group
      rw [e]
      exact T.mul_mem hmT h1
    · obtain ⟨n, hn, p, hp, rfl⟩ := hdecomp m hm
      have hap : a * p = p * a := Subgroup.mem_centralizer_iff.mp (hPCA hp) a ha
      have hpap : p * a * p⁻¹ = a := by rw [← hap, mul_inv_cancel_right]
      have key : ⁅n * p, a⁆ = n * (a * n⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        calc n * p * a * (n * p)⁻¹ * a⁻¹ = n * (p * a * p⁻¹) * n⁻¹ * a⁻¹ := by group
          _ = n * a * n⁻¹ * a⁻¹ := by rw [hpap]
          _ = n * (a * n⁻¹ * a⁻¹) := by group
      rw [key]
      exact NB.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hAN ha) n⁻¹).mp (NB.inv_mem hn))
  have hnormNCA : ∀ c ∈ CA, ∀ w ∈ NB ⊓ CA, c * w * c⁻¹ ∈ NB ⊓ CA := by
    intro c hc w hw
    obtain ⟨hwN, hwC⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer_iff.mp hCAN c hc w hwN,
      Subgroup.le_normalizer_iff.mp (L3C2Gen_le_normalizer_centralizer (A : Set G)) c hc w hwC⟩
  have hcopNCA : Nat.Coprime 3 (Nat.card (NB ⊓ CA : Subgroup G)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 CB)
  have hNCA : NB ⊓ CA ≤ P := le_pPrimeCoreOf_of_normalized inf_le_right hnormNCA hcopNCA
  have hMCA : (T ⊓ CB) ⊓ CA ≤ T ⊓ P := by
    intro m hm
    obtain ⟨hmM, hmCA⟩ := Subgroup.mem_inf.mp hm
    have hmT : m ∈ T := (Subgroup.mem_inf.mp hmM).1
    obtain ⟨n, hn, p, hp, rfl⟩ := hdecomp m hmM
    have hnCA : n ∈ CA := by
      have h := CA.mul_mem hmCA (CA.inv_mem (hPCA hp))
      rwa [mul_inv_cancel_right] at h
    exact Subgroup.mem_inf.mpr ⟨hmT, P.mul_mem (hNCA (Subgroup.mem_inf.mpr ⟨hn, hnCA⟩)) hp⟩
  refine hfact.le.trans (sup_le ?_ ?_)
  · exact hcomm.trans le_sup_left
  · exact hMCA.trans le_sup_right

theorem le_sup_pPrimeCore_of_hyperplanes {A T : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA9 : 9 ≤ Nat.card A) (hT2 : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hq : ∀ B, IsHyperplane A B →
      T ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    T ≤ (⨆ (B : Subgroup G) (_ : IsHyperplane A B),
        T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) ⊔
      (T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes (p := 3)
    Nat.prime_three hA (by omega) hAT (L3C2Gen_coprime_three_card_of_two hT2)
  refine (le_of_eq hgen.symm).trans ?_
  refine iSup₂_le fun B hB => ?_
  have hBH : IsHyperplane A B := hB
  exact (L3C2Gen_inf_centralizer_le hA hT2 hAT hBH (hq B hBH)).trans
    (sup_le (le_sup_of_le_left (le_iSup₂ (f := fun (B : Subgroup G) (_ : IsHyperplane A B) =>
      T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) B hBH)) le_sup_right)

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
