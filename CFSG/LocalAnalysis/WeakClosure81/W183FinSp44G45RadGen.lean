module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Dyn
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45RadGenClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.GH74.KGroups CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiUnipotent minorAut)
open CFSG.RankThree.PartOne.KCRootAxis

theorem rad_c12 :
    (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
        autConj p (Psub ⊓ innAutOf S4)) ⊔
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
        autConj p (Psub ⊓ innAutOf S4)) = innAutOf S4 := by
  exact w183finSp44rg_rad_c12

theorem rad_c13 : ∀ E : Subgroup (MulAut S4), E ≤ Q1sub → 8 ≤ Nat.card E →
    ¬ E ≤ Q1sub ⊓ Q2sub →
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)), autConj p E) = Q1sub := by
  intro E hE h8 hnot
  have hNle : (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
      autConj p E) ≤ Q1sub := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    calc autConj p E ≤ autConj p Q1sub := Subgroup.map_mono hE
      _ = Q1sub := w183finSp44rg_autConj_normalizer Q1sub p hp.2
  have hEsub : E ≤ ⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
      autConj p E := by
    have h1 : autConj 1 E = E := by
      rw [autConj, map_one]
      exact Subgroup.map_id E
    conv_lhs => rw [← h1]
    exact le_iSup_of_le 1 (le_iSup_of_le (one_mem _) le_rfl)
  have hinv : ∀ q ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
      autConj q (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
        autConj p E) =
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)), autConj p E) :=
    fun q hq => w183finSp44rg_autConj_iSup_self
      (innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4))) E hq
  have h8N : 8 ≤ Nat.card ↥(⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q1sub : Set (MulAut S4)),
      autConj p E) :=
    le_trans h8 (Nat.card_le_card_of_injective (Subgroup.inclusion hEsub)
      (Subgroup.inclusion_injective hEsub))
  exact w183finSp44rg_invariant_Q1 hNle hinv h8N

theorem rad_c14 : ∀ E : Subgroup (MulAut S4), E ≤ Q2sub → 8 ≤ Nat.card E →
    ¬ E ≤ Q1sub ⊓ Q2sub →
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)), autConj p E) = Q2sub := by
  intro E hE h8 hnot
  have hNle : (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
      autConj p E) ≤ Q2sub := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    calc autConj p E ≤ autConj p Q2sub := Subgroup.map_mono hE
      _ = Q2sub := w183finSp44rg_autConj_normalizer Q2sub p hp.2
  have hEsub : E ≤ ⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
      autConj p E := by
    have h1 : autConj 1 E = E := by
      rw [autConj, map_one]
      exact Subgroup.map_id E
    conv_lhs => rw [← h1]
    exact le_iSup_of_le 1 (le_iSup_of_le (one_mem _) le_rfl)
  have hinv : ∀ q ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
      autConj q (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
        autConj p E) =
      (⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)), autConj p E) :=
    fun q hq => w183finSp44rg_autConj_iSup_self
      (innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4))) E hq
  have h8N : 8 ≤ Nat.card ↥(⨆ p ∈ innAutOf S4 ⊓ Subgroup.normalizer (Q2sub : Set (MulAut S4)),
      autConj p E) :=
    le_trans h8 (Nat.card_le_card_of_injective (Subgroup.inclusion hEsub)
      (Subgroup.inclusion_injective hEsub))
  exact w183finSp44rg_invariant_Q2 hNle hinv h8N

theorem rad_c15 :
    ∀ τ ∈ Subgroup.normalizer ((Psub ⊓ innAutOf S4 : Subgroup (MulAut S4)) : Set (MulAut S4)),
      ActsOnDynkinMod ⊥ (innAutOf S4) τ → autConj τ Q1sub = Q2sub ∧ autConj τ Q2sub = Q1sub := by
  intro τ hτ hdyn
  obtain ⟨x, hx, rfl⟩ := autOf_surj τ
  have hodd : x.2 % 2 = 1 := dynkin_exponent_odd hx hdyn
  have hlt : x.2 < 4 := (validB_iff.mp hx).2.2
  have hx2 : x.2 = 1 ∨ x.2 = 3 := by omega
  set g : S4 := toS4 x.1 (validB_symp hx) with hg
  have hauto : autOf x = MulAut.conj g * minorAut GF4 ^ x.2 := by
    rw [autOf, dif_pos hx, ← hg]
  have hτU : (antiUnipotent GF4).map (autOf x).toMonoidHom = antiUnipotent GF4 := by
    have hU := hτ
    rw [Psub_inf_inner] at hU
    have hmap := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hU
    rw [Usub, Subgroup.map_map,
      ← MulEquiv.toMonoidHom_eq_coe (MulAut.conj (autOf x)),
      w183finSp44rg_conj_conj (autOf x), ← Subgroup.map_map] at hmap
    exact Subgroup.map_injective
      (CFSG.QuasithinUnique.Setup.X7b.conj_injective (K := GF4)) hmap
  have hnotA1 : autOf x ∉ autStab (radA1 GF4) := by
    intro hmem
    rw [hauto] at hmem
    rcases hx2 with h1 | h3
    · rw [h1, pow_one] at hmem
      exact not_autStab_odd Axis.one g 0 hmem
    · rw [h3] at hmem
      exact not_autStab_odd Axis.one g 1 hmem
  have hnotA2 : autOf x ∉ autStab (radA2 GF4) := by
    intro hmem
    rw [hauto] at hmem
    rcases hx2 with h1 | h3
    · rw [h1, pow_one] at hmem
      exact not_autStab_odd Axis.two g 0 hmem
    · rw [h3] at hmem
      exact not_autStab_odd Axis.two g 1 hmem
  have hA1card : Nat.card (radA1 GF4) = 64 := by
    rw [(card_radicals (K := GF4)).2.1, Nat.card_eq_fintype_card]
    decide
  have hA2card : Nat.card (radA2 GF4) = 64 := by
    rw [(card_radicals (K := GF4)).2.2.1, Nat.card_eq_fintype_card]
    decide
  have hcard1 : Nat.card ((radA1 GF4).map (autOf x).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (autOf x).injective, hA1card]
  have hcard2 : Nat.card ((radA2 GF4).map (autOf x).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (autOf x).injective, hA2card]
  have hEU1 : (radA1 GF4).map (autOf x).toMonoidHom ≤ antiUnipotent GF4 := by
    rw [← hτU]
    exact Subgroup.map_mono radA1_le_antiUnipotent
  have hEU2 : (radA2 GF4).map (autOf x).toMonoidHom ≤ antiUnipotent GF4 := by
    rw [← hτU]
    exact Subgroup.map_mono radA2_le_antiUnipotent
  have hel1 : ∀ y ∈ (radA1 GF4).map (autOf x).toMonoidHom, y * y = 1 := by
    rintro y ⟨a, ha, rfl⟩
    rw [← map_mul, mul_self_of_mem_radA1 ha, map_one]
  have hel2 : ∀ y ∈ (radA2 GF4).map (autOf x).toMonoidHom, y * y = 1 := by
    rintro y ⟨a, ha, rfl⟩
    rw [← map_mul, mul_self_of_mem_radA2 ha, map_one]
  have hmap1 : (radA1 GF4).map (autOf x).toMonoidHom = radA2 GF4 := by
    rcases elementary_le_radA1_or_radA2 hEU1 hel1 with hle | hle
    · exfalso
      have hEqA1 : (radA1 GF4).map (autOf x).toMonoidHom = radA1 GF4 := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        exact le_of_eq (hA1card.trans hcard1.symm)
      exact hnotA1 (w183finSp44rg_mem_autStab_of_map hEqA1)
    · refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact le_of_eq (hA2card.trans hcard1.symm)
  have hmap2 : (radA2 GF4).map (autOf x).toMonoidHom = radA1 GF4 := by
    rcases elementary_le_radA1_or_radA2 hEU2 hel2 with hle | hle
    · refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact le_of_eq (hA1card.trans hcard2.symm)
    · exfalso
      have hEqA2 : (radA2 GF4).map (autOf x).toMonoidHom = radA2 GF4 := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        exact le_of_eq (hA2card.trans hcard2.symm)
      exact hnotA2 (w183finSp44rg_mem_autStab_of_map hEqA2)
  exact ⟨w183finSp44rg_autConj_Q1_of_map (autOf x) hmap1,
    w183finSp44rg_autConj_Q2_of_map (autOf x) hmap2⟩

theorem br2TwoRadicals_Psub : Br2TwoRadicals S4 (Psub ⊓ innAutOf S4) Q1sub Q2sub :=
  ⟨rad_c1, rad_c2, rad_c3, rad_c4, rad_c5, rad_c6, rad_c7, rad_c8, rad_c9, rad_c10, rad_c11,
    rad_c12, rad_c13, rad_c14, rad_c15⟩

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
