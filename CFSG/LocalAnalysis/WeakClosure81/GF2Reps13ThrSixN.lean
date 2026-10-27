module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrIso
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoI
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrW6
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_case_three_six_N (h : Cfg133 A t 3)
    (hP : IsPOnePlusTwo 3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆))
    (hr : rk ↥(commSub ⊤ (⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) = 6) :
    ∃ L : Subgroup (MulAut W), L ≤ pCoreOf 3 A ∧ Conc4_133 A t L ∧ IsPOnePlusTwo 3 ↥L ∧
      rk ↥(commSub ⊤ L) = 6 ∧ ∀ n ∈ pCoreOf 3 A, L.map (MulAut.conj n).toMonoidHom = L := by
  let O : Subgroup (MulAut W) := pCoreOf 3 A
  let P : Subgroup (MulAut W) := ⁅O, Subgroup.zpowers t⁆
  have hP' : IsPOnePlusTwo 3 ↥P := hP
  have hr' : rk ↥(commSub ⊤ P) = 6 := hr
  obtain ⟨hPleO, hPgrp, hPne, htP, hPP, hOP⟩ := s13_P_facts h
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  have h132 : Cfg132 t P :=
    { hW := hW2
      ht := orderOf_eq_prime h.ht2 h.ht1
      hrk := h.hrk
      hP := hPgrp
      hne := hPne
      hn := htP
      hc := hPP }
  have hMin : W4Lem13_2MinLe 27 := w16h_minLe w4Lem13_1_holds 27
  obtain ⟨z, hzP, hz3, hzc, hzt, hZP⟩ := w16h_ext_center h132 hP'
  obtain ⟨_, hM6⟩ := w16h_ext_faithful_part hMin h132 hP' hzP hz3 hzc hzt hZP
  have hle : commSub ⊤ (Subgroup.zpowers z) ≤ commSub ⊤ P :=
    commSub_mono le_top (Subgroup.zpowers_le.mpr hzP)
  have hUeq : commSub ⊤ (Subgroup.zpowers z) = commSub ⊤ P :=
    eq_of_le_of_rk_le hW2 hle (by rw [hr', hM6])
  have hirrP : IsIrrOn P (commSub ⊤ P) ⊥ := by
    have h' := s13_W6_irreducible h.hW hP' hzP hz3 hzc hZP hM6
    rwa [hUeq] at h'
  have hodd : Odd (Nat.card P) := by rw [hP'.2.1]; norm_num
  have hOU : StableUnder O (commSub ⊤ P) :=
    stableUnder_commSub hOP (fun _ _ _ _ => Subgroup.mem_top _)
  have hirrO : IsIrrOn O (commSub ⊤ P) ⊥ := by
    refine ⟨hirrP.1, hOU, ?_, ?_⟩
    · intro x hx u hu
      rw [Subgroup.mem_bot.mp hu, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · intro J hJO hbot hJU
      exact hirrP.2.2.2 J (fun p hp u hu => hJO p (hPleO hp) u hu) hbot hJU
  have hss : sSupIndep (conjSubs A (commSub ⊤ P)) :=
    sSupIndep_conjSubs_of_isotypic h.hW A O P (s13_pCore_facts A 3).2.1
      (s13_pCore_facts A 3).1 hPleO (commSub ⊤ P) hirrO
      (s13_isotypic_commSub h.hW hodd)
  refine ⟨P, hPleO, ⟨3, h.hp, hPleO, ?_, hss,
    Or.inr (Or.inr (Or.inl ⟨hP', hr'⟩))⟩, hP', hr',
    fun n hn => s13_map_conj_eq_of_normalizes hOP hn⟩
  rw [hPP]
  exact hPne

end CFSG.LocalAnalysis.WeakClosure81
