module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoConj
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoRootDown

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.StandardType.TableBUE
  CFSG.StandardType.SmallU CFSG.StandardType.UnitTB CFSG.StandardType.LineU
  CFSG.StandardType.IOneUDvdR CFSG.StandardType.Line63.H5
open scoped commutatorElement

theorem exists_twoGroup_lift {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian 3 A) {a : MulAut L'} (haA : a ∈ A)
    {Ub : Subgroup (Qt L')} (hUb1 : Ub ≠ ⊥) (hUb2 : IsPGroup 2 Ub)
    (hUbL : Ub ≤ LargeEvenLayer (ggFix (qAutHom L' a)))
    (hUbA : ∀ a' ∈ A.map (qAutHom L'), ∀ u ∈ Ub, a' u ∈ Ub) :
    ∃ U : Subgroup L', U ≤ LargeEvenLayer (ggFix a) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
  have hmap := layer_map_eq (π := qmk L') qmk_surjective qmk_ker_le_center (qAutHom_compat a)
  have hlift : ∀ xb ∈ LargeEvenLayer (ggFix (qAutHom L' a)),
      ∃ x ∈ LargeEvenLayer (ggFix a), qmk L' x = xb := fun xb hxb => by
    rw [← hmap] at hxb
    obtain ⟨x, hx, rfl⟩ := hxb
    exact ⟨x, hx, rfl⟩
  refine ⟨LargeEvenLayer (ggFix a) ⊓ Ub.comap (qmk L'), inf_le_left, ?_,
    isPGroup_two_inf_comap hUb2 _, ?_⟩
  · intro hbot
    apply hUb1
    rw [eq_bot_iff]
    intro ub hub
    obtain ⟨u, huE, rfl⟩ := hlift ub (hUbL hub)
    have hu : u ∈ LargeEvenLayer (ggFix a) ⊓ Ub.comap (qmk L') := ⟨huE, hub⟩
    rw [hbot, Subgroup.mem_bot] at hu
    rw [hu, map_one]
    exact Subgroup.one_mem _
  · intro a' ha' u hu
    refine ⟨layer_invariant_A hA haA a' ha' u hu.1, ?_⟩
    show qmk L' (a' u) ∈ Ub
    rw [← qAutHom_mk]
    exact hUbA _ ⟨a', ha', rfl⟩ _ hu.2

theorem ggIOneUnitaryDvdRootSixTwo_holds :
    GGIOneUnitaryDvdRootSixTwoInput := by
  intro K _ _ p hK hp hpq hpd
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := by simpa using hpq
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
  subst hp3
  have hrank : ggUnitaryTorusRank 3 6 = 3 := by simp [ggUnitaryTorusRank]
  rw [hrank]
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα
  classical
  obtain ⟨ψb, hψbmk, hψbs, hkerb, hperfb, hoddb, hAb, hcardAb, hAIb⟩ :=
    six_package hK hψ hker hperf hA hAI
  set Ab := A.map (qAutHom L') with hAbdef
  obtain ⟨U₀, hU1, hU2, hAU⟩ := normTwoR_down hψbmk hα
  have hr3 : 3 ^ 3 ≤ Nat.card Ab := by rw [hcardAb]; simpa using h3
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_frame_odd hK hψbs hkerb hperfb hoddb hAb hAIb hr3
    ⟨U₀, hU1, hU2, hAU⟩
  have hZR : Subgroup.center (UnitaryR K 1 6) = ⊥ := six_center_eq_bot hK
  obtain ⟨s, t, hst, hpair⟩ := exists_pair hM hK (by norm_num) Nat.prime_three (by norm_num)
    hψbs hkerb hZR hAb.2 hdiag hU1 hU2 hAU
  obtain ⟨Usw, hUsw1, hUsw2, hUswA, -, hUswS⟩ :=
    exists_swap_group hM hst (by norm_num) hdiag hpair
  obtain ⟨g, S, hend, hsS, htS, hS45, hlay, hall⟩ :=
    root_downstairs hK hM hAb hdiag hst hpair hr3
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a₀ ∈ A, qAutHom L' a₀ = g := hend.1
  have hendb : GGIsEndNode Ab (qAutHom L' a₀) := by
    rw [ha₀]
    exact hend
  have hend' : GGIsEndNode A a₀ := (isEndNode_iff hperf).mpr hendb
  have hlay₀ : LargeEvenLayer (ggFix (qAutHom L' a₀)) = (blockSU S).map φ := by
    rw [ha₀]
    exact hlay
  obtain ⟨U, hUL, hU1', hU2', hUA⟩ := exists_twoGroup_lift hA ha₀A hUsw1 hUsw2
    (by rw [hlay₀]; exact hUswS S hsS htS) hUswA
  have hrule : GGNonSmallRule 3 A a₀ := by
    rintro - ⟨a₁, hend₁, hns₁⟩
    rcases hS45 with h5 | h4
    ·
      have hc : ∀ l, qAutHom L' a₀ (qmk L' l) = qmk L' (a₀ l) := qAutHom_compat a₀
      have hmapE := layer_map_eq (π := qmk L') qmk_surjective qmk_ker_le_center hc
      have hψeq : ψb.comp (qmk L') = ψ := MonoidHom.ext hψbmk
      refine not_largeEvenSmall_of_map_big ψ _ ?_
      rw [← hψeq, ← Subgroup.map_map, hmapE, hlay₀]
      have hSne : S ≠ Finset.univ := fun e => by
        rw [e, Finset.card_univ, Fintype.card_fin] at h5
        omega
      have hinj : ∀ u ∈ blockSU (n := 1) (K := K) S, ψb (φ u) = 1 → u = 1 :=
        fun u hu hψu => psi_phi_eq_one_of_block hM hkerb hZR hSne hu hψu
      have hbigc : 25920 < Nat.card (blockSU (n := 1) (K := K) S) := by
        rw [← Nat.card_congr (TableBUE.blockSUEquiv S hM.field).toEquiv]
        exact IOneU.suCard_gt_of_five_le hM.field rfl (m := S.card) (by omega)
      exact bigLayer_map_of_block hinj hbigc
    ·
      have hend₁' := (isEndNode_iff hperf).mp hend₁
      obtain ⟨S₁, hS₁, hlay₁⟩ := hall h4 (qAutHom L' a₁) hend₁'
      obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S₁ S (by rw [hS₁, h4])
      obtain ⟨l, hl⟩ := layer_conj_of_perm hM hendb.2.2.1 hend₁'.2.2.1 hlay₀ hlay₁ τ hτ
      exact fun hsm₀ => hns₁ ((largeEvenSmall_conj_iff l hl).mp hsm₀)
  exact ⟨a₀, hend', hrule, U, hUL, hU1', hU2', hUA⟩

end CFSG.StandardType.USixTwo

end
