module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoSetup

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.TableBUE CFSG.StandardType.SmallU
  CFSG.StandardType.IOneUDelta CFSG.StandardType.IOneUDvdR
open scoped commutatorElement

theorem ggIOneUnitaryDvdDeltaSixTwo_holds :
    GGIOneUnitaryDvdDeltaSixTwoInput := by
  intro K _ _ hK L' _ _ ψ hψ hker hperf A As hA hlt hAs hcard hAI hr h3 hadm _hNT
  classical
  have hd3 : 3 ≤ 6 := by norm_num
  have hdq : ((6 : ℕ), 2 ^ 1) ≠ (3, 2) := by norm_num
  have hcen : Subgroup.center (UnitaryR K 1 6) = ⊥ := six_center_eq_bot hK
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hcen
  have hAge : 3 ^ (6 - 2) ≤ Nat.card A :=
    card_ge_delta hK le_rfl hd3 hdq Nat.prime_three (by norm_num) hψ hker hZ hadm
  obtain ⟨ψb, hψbmk, hψbs, hkerb, hperfb, hoddb, hAb, hcardAb, hAIb⟩ :=
    six_package hK hψ hker hperf hA hAI
  set Ab := A.map (qAutHom L') with hAbdef
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_odd hK hψbs hkerb hperfb hoddb hAb hAIb
    (by rw [hcardAb]; simpa using hAge)
  have hh : UnitaryFieldData 2 1 K := hM.field
  have hadmb : GGDeltaAdm 3 (Qt L') Ab := ggDeltaAdm_descent hperf hA hadm
  have hd1 : 0 < 6 := by norm_num
  obtain ⟨ν, hν⟩ := SmallU.exists_nu_actsU hM hd3 hdiag (⟨0, hd1⟩ : Fin 6)
  obtain ⟨δ, hδp, hδ1, hnode⟩ := node_exists hh Nat.prime_three (by norm_num) hM hd3 hAb hadmb
    (⟨0, hd1⟩ : Fin 6) ν hν
  obtain ⟨c, hcs⟩ : ∃ c : Fin 6, c ≠ (⟨0, hd1⟩ : Fin 6) := ⟨⟨1, by norm_num⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨x, hx⟩ := hnode c hcs
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a₀ ∈ A, qAutHom L' a₀ = (x : MulAut (Qt L')) := x.2
  have hxact : ActsU φ (x : MulAut (Qt L')) (nodeDiag c δ) := by
    rw [← hx]
    exact (hν x).1
  have hS : (Finset.univ.erase c : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hcS : c ∉ (Finset.univ.erase c : Finset (Fin 6)) := by simp
  have hτ : IsNodeOn (nodeDiag c δ) (Finset.univ.erase c) := by
    constructor
    · intro i hi j hj
      have hic : i ≠ c := (Finset.mem_erase.mp hi).1
      have hjc : j ≠ c := (Finset.mem_erase.mp hj).1
      simp [nodeDiag, hic, hjc]
    · intro i hi j hj
      have hic : i = c := by
        by_contra h'
        exact hi (Finset.mem_erase.mpr ⟨h', Finset.mem_univ i⟩)
      subst hic
      simp only [nodeDiag, if_neg hj, if_pos rfl]
      exact fun e => hδ1 e.symm
  have hbig : BigOK 1 (Finset.univ.erase c : Finset (Fin 6)) := Or.inl (by omega)
  obtain ⟨hlay, hcomp⟩ := layer_eq_block_of_isNodeOn hM hxact hτ hbig
  have hc : ∀ l, (x : MulAut (Qt L')) (qmk L' l) = qmk L' (a₀ l) := fun l => by
    rw [← ha₀]
    exact qAutHom_mk a₀ l
  have hcompL : IsComponentOf (LargeEvenLayer (ggFix a₀)) (ggFix a₀) :=
    (layer_eq_commutator_comap qmk_surjective qmk_ker_le_center hc hcomp).2
  have hmapE : (LargeEvenLayer (ggFix a₀)).map (qmk L') =
      LargeEvenLayer (ggFix (x : MulAut (Qt L'))) :=
    layer_map_eq qmk_surjective qmk_ker_le_center hc
  have hnotsmall : ¬ LargeEvenSmall (LargeEvenLayer (ggFix a₀)) := by
    have hψeq : ψb.comp (qmk L') = ψ := MonoidHom.ext hψbmk
    refine not_largeEvenSmall_of_map_big ψ _ ?_
    rw [← hψeq, ← Subgroup.map_map, hmapE, hlay]
    have hSne : (Finset.univ.erase c : Finset (Fin 6)) ≠ Finset.univ := fun e =>
      hcS (by rw [e]; exact Finset.mem_univ c)
    have hinj : ∀ u ∈ blockSU (n := 1) (K := K) (Finset.univ.erase c), ψb (φ u) = 1 → u = 1 :=
      fun u hu hψu => psi_phi_eq_one_of_block hM hkerb hcen hSne hu hψu
    have hbigc : 25920 < Nat.card (blockSU (n := 1) (K := K) (Finset.univ.erase c)) := by
      rw [← Nat.card_congr (TableBUE.blockSUEquiv (Finset.univ.erase c) hh).toEquiv]
      exact IOneU.suCard_gt_of_five_le hh rfl (m := (Finset.univ.erase c : Finset (Fin 6)).card)
        (by omega)
    exact bigLayer_map_of_block hinj hbigc
  have hle : LargeEvenLayer (ggFix a₀) ≤ ggFix a₀ := sSup_le fun _ hK' => hK'.1
  have hCentAs : ∀ a' ∈ As, ((∀ j ∈ LargeEvenLayer (ggFix a₀), a' j = j) ↔
      a' ∈ Subgroup.zpowers a₀) := by
    intro a' ha'
    constructor
    · intro hfixL
      have hc' : ∀ l, (qAutHom L' a') (qmk L' l) = qmk L' (a' l) := fun l => qAutHom_mk a' l
      have hfixb := (fix_layer_iff qmk_surjective qmk_ker_le_center hc hc').mp hfixL
      have hfixU : ∀ u ∈ blockSU (n := 1) (K := K) (Finset.univ.erase c),
          (qAutHom L' a') (φ u) = φ u := by
        intro u hu
        apply hfixb
        rw [hlay]
        exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      have hmem := centralizer_L hh hK le_rfl (by norm_num) c Nat.prime_three (by norm_num) hψbs
        hkerb hperfb hM hδp hδ1 hxact (a' := qAutHom L' a')
        (by rw [← map_pow, hAs.2 a' ha', map_one]) hfixU
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, qAutHom_injective hperf ?_⟩
      rw [map_zpow, ha₀, hk]
    · intro hz j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact zpow_fix_of (hle hj) k
  refine ⟨a₀, ⟨ha₀A, ?_, hcompL, fun a' ha' => hCentAs a' (hlt.le ha')⟩, hCentAs,
    fun _ _ => hnotsmall⟩
  intro h1
  have hx1 : x = 1 := Subtype.ext (by rw [← ha₀, h1, map_one]; rfl)
  rw [hx1, map_one] at hx
  have h2 := congrFun hx c
  simp only [nodeDiag, if_pos rfl, Pi.one_apply] at h2
  exact hδ1 h2.symm

end CFSG.StandardType.USixTwo

end
