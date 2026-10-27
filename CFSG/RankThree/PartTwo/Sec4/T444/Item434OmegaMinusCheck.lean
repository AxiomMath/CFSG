module

public import Certificates.Certificate8096
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeMain
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeModel

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf size_pushWords pushWords_getElem!)
open Item434Kit Subgroup


theorem omegaMinus434_elts_check : eltsCheck = true :=
  Certificates.certificate8096.1

theorem omegaMinus434_wreath_check : wreathCheck = true :=
  Certificates.certificate8096.2.1

theorem omegaMinus434_cent_check : centCheck = true :=
  Certificates.certificate8096.2.2.1

theorem omegaMinus434_chain_check : genChainCheck = true :=
  Certificates.certificate8096.2.2.2

@[expose] noncomputable def zPerm (i : Fin 3) : Equiv.Perm (Fin 136) := permOfArr 136 (zArr i)

@[expose] noncomputable def tPerm : Equiv.Perm (Fin 136) := permOfArr 136 tArr

@[expose] noncomputable def sPerm (k : Fin 3) : Equiv.Perm (Fin 136) :=
  permOfArr 136 sArrs[(k : ℕ)]!

theorem rep_of_memOK {g : Array ℕ} (h : memOK g = true) :
    Rep 136 g (permOfArr 136 g) ∧ Rep 136 (invCand 136 g) (permOfArr 136 g)⁻¹ := by
  simp only [memOK, Bool.and_eq_true] at h
  exact rep_permOfArr h.1

theorem mem_omegaT_of_memOK {g : Array ℕ} (h : memOK g = true) : permOfArr 136 g ∈ omegaT := by
  have hrep := (rep_of_memOK h).1
  simp only [memOK, Bool.and_eq_true] at h
  show permOfArr 136 g ∈ omegaQ.originalSubgroup
  exact (ofArrays_mem_iff (by norm_num) omegaChain_ok.1 hrep).1 h.2

theorem elts_spec : (∀ i : Fin 3, memOK (zArr i) = true) ∧ memOK tArr = true ∧
    ∀ k : Fin 3, memOK sArrs[(k : ℕ)]! = true := by
  have h := omegaMinus434_elts_check
  simp only [eltsCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hz, ht⟩, hs⟩ := h
  exact ⟨fun i => allLt_spec hz i.2, ht, fun k => allLt_spec hs k.2⟩

theorem rep_zPerm (i : Fin 3) : Rep 136 (zArr i) (zPerm i) := (rep_of_memOK (elts_spec.1 i)).1

theorem rep_tPerm : Rep 136 tArr tPerm ∧ Rep 136 (invCand 136 tArr) tPerm⁻¹ :=
  rep_of_memOK elts_spec.2.1

theorem rep_sPerm (k : Fin 3) : Rep 136 sArrs[(k : ℕ)]! (sPerm k) :=
  (rep_of_memOK (elts_spec.2.2 k)).1

theorem zPerm_mem (i : Fin 3) : zPerm i ∈ omegaT := mem_omegaT_of_memOK (elts_spec.1 i)

theorem tPerm_mem : tPerm ∈ omegaT := mem_omegaT_of_memOK elts_spec.2.1

theorem sPerm_mem (k : Fin 3) : sPerm k ∈ omegaT := mem_omegaT_of_memOK (elts_spec.2.2 k)

theorem rep_vecElt (v : Fin 3 → ZMod 3) :
    Rep 136 (vecArr (v 0).val (v 1).val (v 2).val) (vecElt zPerm v) :=
  rep_compA (rep_compA (rep_powArr (rep_zPerm 0) _) (rep_powArr (rep_zPerm 1) _))
    (rep_powArr (rep_zPerm 2) _)

theorem wreathFacts_perm : WreathFacts zPerm tPerm := by
  have h := omegaMinus434_wreath_check
  simp only [wreathCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hz3, hzc⟩, ht3⟩, htz⟩, hind⟩, htn⟩ := h
  obtain ⟨rt, rti⟩ := rep_tPerm
  have hval : ∀ v : Fin 3 → ZMod 3, (v 0).val = 0 → (v 1).val = 0 → (v 2).val = 0 → v = 0 := by
    intro v h0 h1 h2
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h0
    · exact (ZMod.val_eq_zero _).mp h1
    · exact (ZMod.val_eq_zero _).mp h2
  refine ⟨fun i => ?_, fun i j => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, fun v hv => ?_⟩
  · exact eq_of_eqA (rep_powArr (rep_zPerm i) 3) rep_idA (allLt_spec hz3 i.2)
  · exact eq_of_eqA (rep_compA (rep_zPerm i) (rep_zPerm j)) (rep_compA (rep_zPerm j) (rep_zPerm i))
      (allLt_spec (allLt_spec hzc i.2) j.2)
  · have h1 := allLt_spec (allLt_spec (allLt_spec hind (ZMod.val_lt (v 0))) (ZMod.val_lt (v 1)))
      (ZMod.val_lt (v 2))
    have heq : eqA 136 (vecArr (v 0).val (v 1).val (v 2).val) (idA 136) = true :=
      (eqA_iff (rep_vecElt v) rep_idA).2 hv
    rw [heq] at h1
    simp only [Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at h1
    exact hval v h1.1.1 h1.1.2 h1.2
  · exact eq_of_eqA (rep_powArr rt 3) rep_idA ht3
  · exact eq_of_eqA (rep_conjArr rt rti (rep_zPerm 0)) (rep_zPerm 1)
      (allLt_spec htz (show 0 < 3 by norm_num))
  · exact eq_of_eqA (rep_conjArr rt rti (rep_zPerm 1)) (rep_zPerm 2)
      (allLt_spec htz (show 1 < 3 by norm_num))
  · exact eq_of_eqA (rep_conjArr rt rti (rep_zPerm 2)) (rep_zPerm 0)
      (allLt_spec htz (show 2 < 3 by norm_num))
  · have h1 := allLt_spec (allLt_spec (allLt_spec htn (ZMod.val_lt (v 0))) (ZMod.val_lt (v 1)))
      (ZMod.val_lt (v 2))
    have heq : eqA 136 (vecArr (v 0).val (v 1).val (v 2).val) tArr = true :=
      (eqA_iff (rep_vecElt v) rt).2 hv
    rw [heq] at h1
    exact absurd h1 (by decide)

@[expose] noncomputable def zT (i : Fin 3) : omegaT := ⟨zPerm i, zPerm_mem i⟩

@[expose] noncomputable def tT : omegaT := ⟨tPerm, tPerm_mem⟩

@[expose] noncomputable def sT (k : Fin 3) : omegaT := ⟨sPerm k, sPerm_mem k⟩

theorem wreathFacts_omegaT : WreathFacts zT tT :=
  wreathFacts_perm.subtype zPerm_mem tPerm_mem

theorem factorization_card_omegaT : (Nat.card omegaT).factorization 3 = 4 := by
  rw [card_omegaT, show (197406720 : ℕ) = 3 ^ 4 * 2437120 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem card_wreathW_omegaT : Nat.card (wreathW zT tT) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW wreathFacts_omegaT)
  rw [factorization_card_omegaT] at hle
  have := le_card_wreathW wreathFacts_omegaT
  norm_num at hle
  omega

@[expose] noncomputable def hypT (k : Fin 3) : Subgroup omegaT :=
  zpowers (zT (k + 1)) ⊔ zpowers (zT (k + 2))

theorem sPerm_spec : (∀ k : Fin 3, sPerm k ^ 5 = 1) ∧
    ∀ k i : Fin 3, i ≠ k → sPerm k * zPerm i = zPerm i * sPerm k := by
  have h := omegaMinus434_cent_check
  simp only [centCheck, Bool.and_eq_true] at h
  obtain ⟨h5, hc⟩ := h
  refine ⟨fun k => eq_of_eqA (rep_powArr (rep_sPerm k) 5) rep_idA (allLt_spec h5 k.2),
    fun k i hik => ?_⟩
  have h1 := allLt_spec (allLt_spec hc k.2) i.2
  have hne : ((i : ℕ) == (k : ℕ)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hik (Fin.ext h)
  rw [hne, Bool.false_or] at h1
  exact eq_of_eqA (rep_compA (rep_sPerm k) (rep_zPerm i)) (rep_compA (rep_zPerm i) (rep_sPerm k))
    h1

theorem orderOf_sT_coprime (k : Fin 3) : Nat.Coprime (orderOf (sT k)) 3 := by
  have h5 : sT k ^ 5 = 1 := Subtype.ext (by simpa [sT] using sPerm_spec.1 k)
  have hd : orderOf (sT k) ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h | h <;> rw [h] <;> norm_num

theorem hypT_le_centralizer (k : Fin 3) :
    hypT k ≤ Subgroup.centralizer ({sT k} : Set omegaT) := by
  have hc : ∀ i : Fin 3, i ≠ k → zT i ∈ Subgroup.centralizer ({sT k} : Set omegaT) := by
    intro i hik
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (sPerm_spec.2 k i hik).symm
  refine sup_le (zpowers_le.mpr (hc _ ?_)) (zpowers_le.mpr (hc _ ?_)) <;> fin_cases k <;> decide

theorem card_hypT (k : Fin 3) : Nat.card (hypT k) = 9 :=
  (isElemAbelian_sup_zpowers wreathFacts_omegaT (by fin_cases k <;> decide)).2

theorem hypT_le_baseA (k : Fin 3) : hypT k ≤ baseA zT :=
  sup_zpowers_le_baseA _ _

theorem three_le_size_genS : 3 ≤ genS.size := by
  rw [genS, size_pushWords]
  simp [sArrs, sCols, genWords]

theorem closure_range_sPerm : Subgroup.closure (Set.range sPerm) = omegaT := by
  have h := omegaMinus434_chain_check
  simp only [genChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hK := ofArrays_card (n := 136) (hn := by norm_num) (hk := three_le_size_genS)
    (hb := by decide) (by norm_num : 0 < 4) h.1
  rw [h.2, ofArrays_originalSubgroup] at hK
  have hsize : sArrs.size = 3 := by simp [sArrs, sCols]
  have hset : {g | ∃ i < 3, permOfArr 136 genS[i]! = g} = Set.range sPerm := by
    ext g
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      rw [sPerm, genS, pushWords_getElem! _ _ (by rw [hsize]; exact hi)]
    · rintro ⟨k, rfl⟩
      refine ⟨k, k.2, ?_⟩
      rw [sPerm, genS, pushWords_getElem! _ _ (by rw [hsize]; exact k.2)]
  rw [hset] at hK
  have hle : Subgroup.closure (Set.range sPerm) ≤ omegaT := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact sPerm_mem k
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hK, card_omegaT]; rfl)

theorem closure_range_sT : Subgroup.closure (Set.range sT) = ⊤ := by
  apply Subgroup.map_injective omegaT.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact closure_range_sPerm

end CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus
