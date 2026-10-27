module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1E3Std

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1e3_rMV_ge_five (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) :
    (5 : ℕ∞) ≤ rMV D.M V := by
  have hmV : 9 ≤ mSub V := by
    have hV1 : 1 < Nat.card (v1Sub D.M ⊥ V hV L) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 S.ne_bot
    have hcard : 2 ^ 9 ≤ Nat.card V := by
      rw [s16c4v1_card_V S]
      calc 2 ^ 9 = 2 ^ 8 * 2 := by norm_num
        _ ≤ 2 ^ 8 * Nat.card (v1Sub D.M ⊥ V hV L) :=
            Nat.mul_le_mul_left _ (by omega)
    have h := card_eq_two_pow_mSub (U := V) hV.isPGroup
    rw [h] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUC⟩ := hU
  have hbad_of : ∀ u ∈ U, u ≠ 1 → s16c4v1_Bad D u := fun u huU hu1 hle =>
    hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huU)).trans hle)
  have hmU : mSub U ≤ 4 := by
    have hU1bot : U ⊓ v1Sub D.M ⊥ V hV L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      obtain ⟨huU, hu1⟩ := Subgroup.mem_inf.1 hu
      by_contra hune
      exact (s16c4v1e3_bad_sing S hstd (hUV huU) hune (hbad_of u huU hune)).1
        ((s16c4v1_vec_eq_zero_iff S (hUV huU)).2 hu1)
    have hts : ∀ x : IntMod V hV, x.val ∈ U →
        S.F.Sing (mkTil (v1Sub D.M ⊥ V hV L) V hV x) := by
      intro x hxU
      have hvec : s16c4v1_vec S x.val = S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x) := by
        unfold s16c4v1_vec
        rw [dif_pos x.val_mem,
          show IntMod.mk hV ⟨x.val, x.val_mem⟩ = x from Subtype.ext rfl]
      show herm S.F.σ (S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x))
        (S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV x)) = 0
      rw [← hvec]
      by_cases hx1 : x.val = 1
      · rw [hx1, s16c4v1_vec_one]
        simp [herm]
      · exact (s16c4v1e3_bad_sing S hstd x.val_mem hx1 (hbad_of x.val hxU hx1)).2
    have hrk := s16c4_rk_imgTil_le_four S.F hts
    have h := s15_Infra_mSub_eq_rk_imgTil_add (v1Sub D.M ⊥ V hV L) V U hV hUV
    have hbot : mSub (⊥ : Subgroup G) = 0 := by rw [mSub, rk_bot]
    rw [hU1bot, hbot, add_zero] at h
    rw [h]
    exact hrk
  have hquot : 5 ≤ E3.mQuot V U := by
    have h := mSub_eq_mQuot_add V U hV hUV
    omega
  exact_mod_cast hquot

theorem s16c4v1e3_cex_inv (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D)
    (hr : (5 : ℕ∞) ≤ rMV D.M V) {g : G} (hg : s16c4v1_Cex D V g) :
    s16c4v1_Cex D V g⁻¹ := by
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hA2 : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hEN : barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g) ≤
      Subgroup.normalizer (lBar (v1Sub D.M ⊥ V hV L) V hV L :
        Set (MulAut (Vtil (v1Sub D.M ⊥ V hV L) V hV))) := by
    intro φ hφ
    obtain ⟨a, haA, rfl⟩ := (mem_barSub _ V hV _ φ).1 hφ
    exact Sixteen24.actTil_v1Sub_mem_normalizer D h1217 S.sect.setting.hyp151 hV (hg.1 haA)
      (by rw [Sixteen24.nBar_eq_of_uFrame D S.sect.setting.hyp151 hV S.F]; exact hg.1 haA)
      (s16c4v1_mem_stabTil S (hg.1 haA))
  have hE2 : IsElemAbelian2 (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) :=
    isElemAbelian2_barSub hV hA2
  have hcardE : Nat.card (barSub (v1Sub D.M ⊥ V hV L) V hV (conjSubgroup V g)) ≤ 2 ^ 4 :=
    S.F.s16c4_card_le_sixteen hEN hE2
  have hrel : (Subgroup.centralizer (V : Set G)).relIndex (conjSubgroup V g) ≤ 16 := by
    rw [← s16c4v1_cxh_card_barSub S h1217 hg.1]
    exact hcardE
  have hmq4 : E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) ≤ 4 := by
    have h := E3.relIndex_eq_two_pow hA2.isPGroup
      (Subgroup.centralizer (V : Set G))
    rw [h, show (16 : ℕ) = 2 ^ 4 by norm_num] at hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hrel
  have hkey : ∀ u ∈ V, g * u * g⁻¹ ∈ D.M := by
    intro u hu
    let C : Subgroup G := conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G)
    let U : Subgroup G := conjSubgroup C g⁻¹
    have hUV : U ≤ V := by
      have h1 : conjSubgroup C g⁻¹ ≤ conjSubgroup (conjSubgroup V g) g⁻¹ :=
        E3.conjSubgroup_mono_left g⁻¹ inf_le_left
      rwa [E3.conjSubgroup_conj_inv] at h1
    have hVU : E3.mQuot V U = E3.mQuot (conjSubgroup V g) C := by
      conv_lhs => rw [show V = conjSubgroup (conjSubgroup V g) g⁻¹ from
        (E3.conjSubgroup_conj_inv V g).symm]
      exact E3.mQuot_conjSubgroup (conjSubgroup V g) C g⁻¹
    have hCS : conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G) ≤ C :=
      le_inf inf_le_left (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hu)))
    have hmC : E3.mQuot (conjSubgroup V g) C ≤
        E3.mQuot (conjSubgroup V g)
          (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) :=
      E3.mQuot_mono hCS
    have hmCeq : E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)) =
        E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) := by
      simp only [E3.mQuot, Subgroup.inf_relIndex_left]
    have hmU : E3.mQuot V U ≤ 4 :=
      hVU.trans_le ((hmC.trans hmCeq.le).trans hmq4)
    have hlt : (E3.mQuot V U : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast hmU)
        (lt_of_lt_of_le (by norm_num : (4 : ℕ∞) < 5) hr)
    have hcentU := CFSG.LocalAnalysis.WeakClosure81.centralizer_le_of_mQuot_lt_rMV hUV hlt
    have hu_cent : u ∈ Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 u
        (Set.mem_singleton u)).symm
    have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      have h1 : g * u * g⁻¹ ∈ conjSubgroup (Subgroup.centralizer (C : Set G)) g⁻¹ := by
        refine (mem_conjSubgroup_iff).2 ?_
        show g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ ∈ Subgroup.centralizer (C : Set G)
        have h2 : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
        rw [h2]
        exact hu_cent
      rwa [E3.conjSubgroup_centralizer C g⁻¹] at h1
    exact hcentU hgu
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxu : g⁻¹ * x * g ∈ V := by
      simpa using (mem_conjSubgroup_iff).1 hx
    have h1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h1]
    exact hkey (g⁻¹ * x * g) hxu
  · intro hbot
    apply hg.2
    have h := E3.conjSubgroup_commutator V (conjSubgroup V g⁻¹) g
    rw [hbot, E3.conjSubgroup_bot, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one] at h
    rw [Subgroup.commutator_comm]
    exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
