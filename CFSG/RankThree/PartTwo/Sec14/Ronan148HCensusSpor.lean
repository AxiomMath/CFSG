module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusL2
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM12
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QSU33
public import CFSG.ClassicalInvolution.Q3.M11Kernel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Row

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.innerThree_of_outer (hcfg : OLCfg P L Q) {Y : Type} [Group Y]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Y) (hY : ¬ 3 ∣ Nat.card (Outer Y)) : InnerThree ↥L :=
  innerThree_of_range fun _ hσ =>
    Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hcfg.perfL e hY hσ

theorem olRow_of_outer (S : Type) [Group S] [IsSimpleGroup S] (hS : ¬ 3 ∣ Nat.card (Outer S))
    (hno : ∀ B V : Subgroup S, ¬ InnerCfg B V) : OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  have hZL : Subgroup.center L = ⊥ :=
    Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hcfg.isQuasisimple e
  have hinn := hcfg.innerThree_of_outer
    (((QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot).trans e) hS
  obtain ⟨hPI, hQI⟩ := hcfg.le_innerSub hinn
  obtain ⟨B, V, hc⟩ := hcfg.exists_innerCfg hZL hPI hQI
  exact hno _ _ (hc.map e)

theorem olRow_spor_M11 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M11)) := by
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M11) :=
    CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
  haveI : Finite (Blueprint.NativeSporadic.Carrier .M11) :=
    inferInstanceAs (Finite Blueprint.NativeSporadic.M11)
  haveI : Finite (Outer (Blueprint.NativeSporadic.Carrier .M11)) :=
    Sec13.Res5Proof.finite_outer _
  refine olRow_of_outer _ (Sec13.Res5Proof.not_three_dvd_of_card_le_two
    CFSG.Sporadic.Schreier.at_m11_schreier.1) ?_
  refine not_innerCfg_of_noKlein fun b hb W hW hK => ?_
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by rintro rfl; rw [orderOf_one] at hb; norm_num at hb
  have h18 := Sec4.Item434SporM11.card_centralizer_eq (x := b) hb3 hb1
  have h4 : Nat.card W ∣ 18 := h18 ▸ Subgroup.card_dvd_of_le hW
  rw [hK.card_four] at h4
  norm_num at h4

theorem olRow_spor_J1 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J1)) := by
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.isSimpleGroup_J1
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J1) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card Blueprint.NativeSporadic.J1 ≠ 0
      rw [CFSG.Sporadic.J1.card_J1]; norm_num)
  refine olRow_of_outer _ ?_ fun B V => not_innerCfg_of_not_dvd ?_ B V
  · change ¬ 3 ∣ Nat.card (Outer Blueprint.NativeSporadic.J1)
    rw [CFSG.Sporadic.Schreier.at_j1_schreier.1]
    norm_num
  · change ¬ 9 ∣ Nat.card Blueprint.NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num

theorem isPGroup_m12S : IsPGroup 3 (Subgroup.closure
    ({Sec4.RonanK432.m12Sx, Sec4.RonanK432.m12Sy} : Set Blueprint.NativeSporadic.M12)) := by
  have hrange : ∀ g ∈ Subgroup.closure
      ({Sec4.RonanK432.m12Sx, Sec4.RonanK432.m12Sy} : Set Blueprint.NativeSporadic.M12),
      ∃ q, Sec4.RonanK432.m12Sf q = g := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact Sec4.RonanK432.m12Sf_one
    | mul_right x hx y hy ih =>
      obtain ⟨q, rfl⟩ := ih
      rcases hy with rfl | rfl
      · exact ⟨_, (Sec4.RonanK432.m12Sf_σx q).symm⟩
      · exact ⟨_, (Sec4.RonanK432.m12Sf_σy q).symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨q, rfl⟩ := ih
      obtain ⟨hx3, hy3⟩ := Sec4.RonanK432.m12S_gen
      rcases hy with rfl | rfl
      · have hi : Sec4.RonanK432.m12Sx⁻¹ = Sec4.RonanK432.m12Sx * Sec4.RonanK432.m12Sx := by
          rw [inv_eq_iff_mul_eq_one, ← hx3, pow_succ, pow_two, mul_assoc]
        refine ⟨CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.m12σx
          (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.m12σx q), ?_⟩
        rw [hi, ← mul_assoc, Sec4.RonanK432.m12Sf_σx, Sec4.RonanK432.m12Sf_σx]
      · have hi : Sec4.RonanK432.m12Sy⁻¹ = Sec4.RonanK432.m12Sy * Sec4.RonanK432.m12Sy := by
          rw [inv_eq_iff_mul_eq_one, ← hy3, pow_succ, pow_two, mul_assoc]
        refine ⟨CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.m12σy
          (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.m12σy q), ?_⟩
        rw [hi, ← mul_assoc, Sec4.RonanK432.m12Sf_σy, Sec4.RonanK432.m12Sf_σy]
  intro g
  obtain ⟨q, hq⟩ := hrange g g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← hq]
  exact Sec4.RonanK432.m12Sf_exp3 q

theorem m12S_noncomm : Sec4.RonanK432.m12Sx * Sec4.RonanK432.m12Sy ≠
    Sec4.RonanK432.m12Sy * Sec4.RonanK432.m12Sx := by
  decide +kernel

end Row

section Row2

set_option linter.unusedSectionVars false


theorem olRow_spor_M12 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M12)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  haveI : IsSimpleGroup (Blueprint.NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Co1Schreier.m12_simple
  have hZL := Sec4.center_eq_bot_of_mulEquiv_isSimpleGroup hcfg.isQuasisimple e
  let f : Blueprint.NativeSporadic.M12 →* L := e.symm.toMonoidHom
  have hT : IsPGroup 3 (Subgroup.closure ({f Sec4.RonanK432.m12Sx,
      f Sec4.RonanK432.m12Sy} : Set L)) := by
    have h := isPGroup_m12S.map f
    rwa [MonoidHom.map_closure, Set.image_pair] at h
  refine hcfg.false_of_nonabelian_three hZL hT fun h => m12S_noncomm ?_
  apply e.symm.injective
  have h' : f (Sec4.RonanK432.m12Sx * Sec4.RonanK432.m12Sy) =
      f (Sec4.RonanK432.m12Sy * Sec4.RonanK432.m12Sx) := by rw [map_mul, map_mul]; exact h
  exact h'

theorem olRow_eight_SU3_three : OLRow (fun T _ => Nonempty (T ≃* projSU 3 3 1)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  have hZL := Sec13.Res5Proof.center_eq_bot_of_projSU ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
    hcfg.isQuasisimple e
  obtain ⟨x, y, -, -, hxy, hT⟩ := CFSG.AGLEmbedding.KFactProofs.G2Q.exists_pair_projSU33 e
  exact hcfg.false_of_nonabelian_three hZL hT hxy

theorem olRow_eight_SU3 (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    OLRow (fun T _ => Nonempty (T ≃* projSU 3 3 e)) := by
  interval_cases e
  · exact olRow_eight_SU3_three
  · exact olRow_eight_SU3_nine

open CFSG.RankThree.Native.ONTriple in
theorem olRow_cover_ON :
    OLRow (fun T _ => Sec4.IsExtOf T (Blueprint.NativeSporadic.Carrier .ONan)
      (Multiplicative (ZMod 3))) := by
  intro X _ _ P L Q hcfg hext
  have hcardL : Nat.card L = Nat.card X := by
    rw [card_of_isExtOf_three hext, card_X hcfg.triple]
    change Nat.card Blueprint.NativeSporadic.ON * 3 = _
    rw [CFSG.Sporadic.ON.card_ON]
  have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L hcardL
  obtain ⟨φ, j, hj, hPφ, -⟩ := exists_model_AG hcfg.perf hcfg.triple hcfg.e27
  have hWQ : ∀ l (hl : l < 4),
      (XG j l 0 hj (by norm_num)).comap φ.toMonoidHom = Q := by
    intro l hl
    set W := (XG j l 0 hj (by norm_num)).comap φ.toMonoidHom with hW
    have hWc : Nat.card W = 4 := by
      rw [← card_XG (l := l) hj (by norm_num : 0 < 3)]
      exact Nat.card_congr (φ.toEquiv.subtypeEquiv fun _ => Iff.rfl)
    have hPW : P ≤ Subgroup.normalizer (W : Set X) := by
      intro p hp
      have hφp : φ p ∈ AG j := by rw [← hPφ]; exact ⟨p, hp, rfl⟩
      have hN := AG_le_normalizer_XG hj hl (by norm_num : 0 < 3) hφp
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [hW, SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul,
        map_inv]
      exact Subgroup.mem_normalizer_iff.mp hN (φ y)
    have hle := hcfg.inv W (by rw [hLtop]; exact le_top.trans le_sup_left)
      ⟨le_top, isPiSubgroup_of_not_dvd (by rw [hWc]; norm_num), hPW⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcfg.klein.card_four, hWc])
  have h01 : XG j 0 0 hj (by norm_num) = XG j 1 0 hj (by norm_num) :=
    Subgroup.comap_injective φ.surjective ((hWQ 0 (by norm_num)).trans (hWQ 1 (by norm_num)).symm)
  exact not_two_lines hj (by norm_num : 0 < 4) (by norm_num : 1 < 4) (by norm_num)
    (by norm_num : 0 < 3) (by norm_num : 0 < 3) (XG j 0 0 hj (by norm_num))
    (isPi_XG hj (by norm_num)) le_rfl (le_of_eq h01.symm)

end Row2

section M22


theorem olRow_spor_M22 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M22)) :=
  olRow_of_E16 _ CFSG.GH74.Uniqueness.SU.K.R3.exists_E16_M22

theorem olRow_cover_M22 :
    OLRow (fun T _ => Sec4.IsExtOf T (Blueprint.NativeSporadic.Carrier .M22)
      (Multiplicative (ZMod 3))) :=
  olRow_of_E16_ext _ CFSG.GH74.Uniqueness.SU.K.R3.exists_E16_M22

end M22

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
