module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFive
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem not_le_normalizer_conjSubgroup_of_commutator_ne_bot {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) {k : G} (hne : ⁅V, conjSubgroup V k⁆ ≠ ⊥) :
    ¬ V ≤ Subgroup.normalizer (conjSubgroup V k : Set G) := by
  intro hle
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hne
    rw [hbot, Subgroup.commutator_bot_left]
  have hN : V ⊓ Subgroup.normalizer (conjSubgroup V k : Set G) ≠ ⊥ := by
    rw [inf_eq_left.mpr hle]
    exact hVne
  have hP : IsPGroup 2 ↥(V ⊔ conjSubgroup V k) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_two_of_isElemAbelian hV)
      (isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup' hV k)) hle
  have hcomm := commute_of_isPGroup_sup hV hTI
    ⟨1, (CFSG.Quasithin.conjSubgroup_one V).symm⟩ ⟨k, rfl⟩ hN hP
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (hcomm u hu v hv).symm

theorem pCoreOf_sup_conj_eq_pairY (h : Hyp711 V H E) {k : G} (hk : k ∈ kSub V H E)
    (hne : ⁅V, conjSubgroup V k⁆ ≠ ⊥) :
    pCoreOf 2 (V ⊔ conjSubgroup V k) =
      (V ⊓ Subgroup.normalizer (conjSubgroup V k : Set G)) ⊔
        (conjSubgroup V k ⊓ Subgroup.normalizer (V : Set G)) := by
  have hkH : k ∈ H := kSub_le_of_forall_le h.omega_le hk
  have hVk_mem : conjSubgroup V k ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet h.le h.normal h.mem hkH
  have hVk_ne : conjSubgroup V k ≠ V := by
    intro heq
    apply hne
    rw [heq]
    exact Subgroup.commutator_self_eq_bot_iff.mpr h.elemAbelian.1
  obtain ⟨a, b, hVa, hVkb, hNab⟩ :=
    nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian h.mem hVk_mem
  have hN : conjSubgroup V (1 : G) ⊓
      Subgroup.normalizer (conjSubgroup V k : Set G) ≠ ⊥ := by
    rw [← hVa, ← hVkb] at hNab
    rw [CFSG.Quasithin.conjSubgroup_one]
    exact hNab
  have hne' : conjSubgroup V (1 : G) ≠ conjSubgroup V k := by
    rw [CFSG.Quasithin.conjSubgroup_one]
    exact fun hh => hVk_ne hh.symm
  have hnot : ¬ conjSubgroup V (1 : G) ≤
      Subgroup.normalizer (conjSubgroup V k : Set G) := by
    rw [CFSG.Quasithin.conjSubgroup_one]
    exact not_le_normalizer_conjSubgroup_of_commutator_ne_bot h.elemAbelian h.ti hne
  have hmain := pCoreOf_sup_conj_eq h.elemAbelian h.ti (a := 1) (b := k) hne' hN hnot
  rw [CFSG.Quasithin.conjSubgroup_one] at hmain
  exact hmain

end CFSG.LocalAnalysis.WeakClosure81
