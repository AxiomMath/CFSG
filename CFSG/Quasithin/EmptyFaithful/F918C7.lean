module

public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.Background.F918C6
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Case1

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

omit [Finite G] in
theorem subgroupOf_pCoreOf (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

noncomputable def kbarEquiv (K : Subgroup G) : KBar K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
  QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf K)

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem modDynkin_of_group (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS' : IsSimpleGroup (KBar K)) (hne : autIH V₁ I H K ≠ ⊥) {s : G} (hsH : s ∈ H)
    (hsK : s ∈ Subgroup.normalizer (K : Set G)) (hdyn : KbarNontrivialOnDynkin K s) :
    ModDynkin (autIH V₁ I H K)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩) := by
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := MulEquiv.isSimpleGroup (kbarEquiv K).symm
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_autI h hIU hS hne
  rcases hdyn with ⟨⟨eL⟩, hout⟩ | ⟨⟨eA⟩, hfuse⟩
  · refine Or.inl ⟨?_, fun hin => not_kbarInducesOuter_of_inner h hIU hS hne hsH hsK hin hout⟩
    exact CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
      ((e.symm.trans (kbarEquiv K).symm).trans eL)
  · refine Or.inr ⟨⟨(e.symm.trans (kbarEquiv K).symm).trans eA⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    exact not_kbarFusesThrees_of_class h hIU hS hne hsH hsK
      (fun x hx hx3 => hcon x hx hx3) hfuse

structure Case1Out (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {s : G} (hsT : s ∈ T) : Prop where
  ne : autIH V₁ I H K ≠ ⊥
  nat : ModNaturalType (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
  dynkin : ModDynkin (autIH V₁ I H K)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, h.T_le_H hsT⟩)
  notNorm : s ∉ Subgroup.normalizer (I : Set G)
  sum : IsSumMod (fixV (autIH V₁ I H K)) (subM V₁ (conjClosure I H) I)
    ((subM V₁ (conjClosure I H) I).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, h.T_le_H hsT⟩).toMonoidHom) ⊤
  std : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
    (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)
  off : ∃ B : Subgroup G, QOff (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H B)
    (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I))

theorem case1_group (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTildeT h hIU)
    (h310 : D310) (h391 : D391) (hNat : Insp14622Nat) (hS' : IsSimpleGroup (KBar K)) {s : G}
    (hsT : s ∈ T) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hdyn : KbarNontrivialOnDynkin K s) : Case1Out h hIU hsT := by
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  have h4 := mod4_core h310 h391 hD hirr' hMp hA
  have hqM := hA.qhat_M hD.sylow.1
  have hstd : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hnat := hNat _ _ _ _ _ _ hstd hMp hqM
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hsH : s ∈ H := h.T_le_H hsT
  have hD' := modDynkin_of_group h hIU hS' hne hsH hsK hdyn
  have hσT := actH_mem_autIH_of_mem (I := I) h h.T_le_H hsT
  have hσM := actH_mem_autIH_of_mem (I := I) h (le_refl H) hsH
  have hσ := actH_mem_normalizer_autIH (I := I) h hsH hsK
  obtain ⟨hns, hsum⟩ := case1_module h4 hσT hσM hσ hnat hD'
  refine ⟨hne, hnat, hD', ?_, hsum, ?_, ?_⟩
  · intro hsI
    apply hns
    exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
      (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) ⟨s, hsH⟩).mpr hsI
  · exact hstd
  · exact ⟨B, hA⟩

end Case1

end CFSG.Quasithin
