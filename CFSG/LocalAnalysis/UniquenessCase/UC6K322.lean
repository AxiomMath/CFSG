module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Rows
public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Ext
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623d
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6EvenSymplecticCore
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.RepresentationTheory
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.RankThree.SubgroupLists (translate IsTransitiveMonomial)

theorem three_dvd_card_of_monomial {p : ℕ} [Fact p.Prime] {G : Subgroup (GL (Fin 3) (ZMod p))}
    (hmono : IsTransitiveMonomial G) : 3 ∣ Nat.card G := by
  classical
  obtain ⟨L, hL, hL1, hperm, htrans⟩ := hmono
  have hinj := K322Lin.injective_of_isInternal hL hL1
  letI : MulAction ↥G (Submodule (ZMod p) (Fin 3 → ZMod p)) :=
    { smul := fun g W => translate (g : GL (Fin 3) (ZMod p)) W
      one_smul := fun W => CFSG.RankThree.SubgroupLists.translate_one W
      mul_smul := fun a b W => CFSG.RankThree.SubgroupLists.translate_mul _ _ W }
  have horb : MulAction.orbit ↥G (L 0) = Set.range L := by
    ext W
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨j, hj⟩ := hperm g g.2 0
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨g, hg, hgj⟩ := htrans 0 j
      exact ⟨⟨g, hg⟩, hgj⟩
  have hcard : (MulAction.orbit ↥G (L 0)).ncard = 3 := by
    rw [horb, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h := MulAction.index_stabilizer ↥G (L 0)
  rw [hcard] at h
  obtain ⟨k, hk⟩ := Subgroup.index_dvd_card (MulAction.stabilizer ↥G (L 0))
  exact ⟨k, by rw [hk, h]⟩

@[expose] def transvGL' {F : Type*} [Field F] : GL (Fin 3) F :=
  ⟨Matrix.transvection (1 : Fin 3) (0 : Fin 3) 1, Matrix.transvection (1 : Fin 3) (0 : Fin 3) (-1),
    by rw [Matrix.transvection_mul_transvection_same (1 : Fin 3) (0 : Fin 3) (by decide),
      add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same (1 : Fin 3) (0 : Fin 3) (by decide),
      neg_add_cancel, Matrix.transvection_zero]⟩

theorem gl32_not_comm : ∃ a b : GL (Fin 3) (ZMod 2), a * b ≠ b * a := by
  refine ⟨K322Rows.transvGL, transvGL', fun h => ?_⟩
  have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) h
  simp only [Units.val_mul, K322Rows.transvGL, K322Rows.tv, transvGL', Matrix.transvection,
    Matrix.mul_apply, Fin.sum_univ_three] at this
  revert this
  decide

section K322


theorem k322_holds : K322 := by
  intro p _ hp2 G hirr hp' Z hZ x hxG hord hfix
  have hpp : p.Prime := Fact.out
  by_cases hp3 : p = 3
  · subst hp3
    exact (false_of_irreducible_threePrime hirr hp' hxG hord hZ hfix).elim
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hpp) (by norm_num)
    · exact h
  have hG := K322Rows.irreducible_of_irredGL3 hirr
  have hx4 : x ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have ht2 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
  have htG : x ^ 2 ∈ G := G.pow_mem hxG 2
  have hK : LinearMap.ker (Matrix.toLin' (((x ^ 2 : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) - 1)) = Z := by
    ext v
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    exact Set.ext_iff.1 hfix v
  have hfixK : Module.finrank (ZMod p) (LinearMap.ker (Matrix.toLin'
      (((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1))) = 1 := by
    rw [hK, hZ]
  have hZne : ¬ (Z = ⊥ ∨ Z = ⊤) := by
    rintro (h | h)
    · rw [h, finrank_bot] at hZ
      exact zero_ne_one hZ
    · rw [h, finrank_top, Module.finrank_fin_fun] at hZ
      norm_num at hZ
  obtain ⟨H, hHG, hnorm, hHirr, hcase⟩ :=
    CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hp2 hG
  have hHp : ¬ p ∣ Nat.card H := fun h => hp' (h.trans (Subgroup.card_dvd_of_le hHG))
  have h3p : 3 < p := by omega
  rcases hcase with hSL | ⟨M, hMt, hMdet, hΩ⟩ | ⟨⟨e⟩, -, hprod, hint⟩ | ⟨⟨e⟩, h7⟩ |
    ⟨hperf, hZ3, ⟨e6⟩, h30⟩ | ⟨hcyc, -, -⟩ | ⟨h27, hex, h31⟩ | ⟨rfl, hmono⟩
  ·
    exact absurd (by rw [hSL]; exact K322Rows.p_dvd_card_statedSL) hHp
  ·
    exact absurd (by rw [hΩ]; exact K322Rows.p_dvd_card_omegaGL hp5 hMt hMdet) hHp
  ·
    exfalso
    have hc := K322Rows.central_sq_of_alt5 hHG e hprod hint hxG hx4
    apply hZne
    refine hirr Z fun g hg w hw => ?_
    have hw' : ((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w = w := by
      have : w ∈ (Z : Set (Fin 3 → ZMod p)) := hw
      rw [← hfix] at this
      exact this
    have hgoal : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w ∈ (Z : Set (Fin 3 → ZMod p)) := by
      rw [← hfix]
      show ((x ^ 2 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec
        ((g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hc g hg, Units.val_mul, ← Matrix.mulVec_mulVec,
        hw']
    exact hgoal
  ·
    haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
      CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    haveI : IsSimpleGroup ↥H := e.isSimpleGroup
    have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := gl32_not_comm
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    have hq := K322Rows.isQuasisimple_of_simple_k322 hnab
    have hlayer := K322Rows.genFittingLayer_eq hHG hnorm hq hHirr
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, h3p⟩
    · rw [Nat.pow_mod]
      rcases h7 with h | h | h <;> rw [h]
    · exact CFSG.LocalAnalysis.ComponentInitial.SteinbergBI.lieModel_PSL_three_two_of_mulEquiv
        (((MulEquiv.subgroupCongr hlayer).trans (Subgroup.subgroupOfEquivOfLe hHG)).trans e)
    · have hcardH : Nat.card H = 168 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.ComponentClassification.GHarris.card_GL32_gh
      exact (show 3 ∣ Nat.card H by rw [hcardH]; norm_num).trans (Subgroup.card_dvd_of_le hHG)
  ·
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hq : CFSG.Open.IsQuasisimple ↥H := ⟨hperf.commutator_eq_top, e6.isSimpleGroup⟩
    have hlayer := K322Rows.genFittingLayer_eq hHG hnorm hq hHirr
    let eE : ↥(genFittingLayer ↥G) ≃* ↥H :=
      (MulEquiv.subgroupCongr hlayer).trans (Subgroup.subgroupOfEquivOfLe hHG)
    have hcen := K322Rows.map_center_k322 eE
    refine ⟨Or.inr (Or.inl ⟨h30, K322Rows.isQuasisimple_of_mulEquiv_k322 eE hq, ?_, ?_⟩), ?_, h3p⟩
    · calc Nat.card ↥(Subgroup.center ↥(genFittingLayer ↥G))
          = Nat.card ↥((Subgroup.center ↥(genFittingLayer ↥G)).map eE.toMonoidHom) :=
            (Subgroup.card_map_of_injective eE.injective).symm
        _ = Nat.card ↥(Subgroup.center ↥H) := by rw [hcen]
        _ = 3 := hZ3
    · exact ⟨(QuotientGroup.congr _ _ eE hcen).trans e6⟩
    · have h3 : 3 ∣ Nat.card H := by
        have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥H)
        rwa [hZ3] at this
      exact h3.trans (Subgroup.card_dvd_of_le hHG)
  ·
    exfalso
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hHz : H = Subgroup.zpowers (g : GL (Fin 3) (ZMod p)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hy⟩)
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        have := congrArg Subtype.val hk
        simpa using this
      · intro hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact H.zpow_mem g.2 k
    have hmem : x ^ 2 * (g : GL (Fin 3) (ZMod p)) * (x ^ 2)⁻¹ ∈
        Subgroup.zpowers (g : GL (Fin 3) (ZMod p)) := hHz ▸ hnorm _ htG _ g.2
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.2 hmem
    rw [hHz] at hHirr
    exact K322Lin.false_of_cyclic_involution hHirr ht2 hm.symm hfixK
  ·
    have hω : ∃ ω : ZMod p, ω ^ 3 = 1 ∧ ω ≠ 1 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdvd : 3 ∣ Nat.card (ZMod p)ˣ := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units]
        omega
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      refine ⟨(u : ZMod p), ?_, ?_⟩
      · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
      · intro h
        have : u = 1 := Units.ext h
        rw [this, orderOf_one] at hu
        norm_num at hu
    obtain ⟨ω, hω3, hω1⟩ := hω
    have hexp := K322Ext.exponent_three_of_involution hHirr h27 hex hω3 hω1 ht2
      (fun y hy => hnorm _ htG y hy) hfixK
    have hHn : (H.subgroupOf G).Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (hnorm g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
    refine ⟨Or.inr (Or.inr (Or.inl ⟨h31, H, hHG, hHn, ⟨by rw [h27]; norm_num, ?_, hexp⟩⟩)), ?_,
      h3p⟩
    · intro hcomm
      have htop : Subgroup.center ↥H = ⊤ := eq_top_iff.2 fun y _ =>
        Subgroup.mem_center_iff.2 fun z => hcomm.is_comm.comm z y
      have hZ3 := hex.2.2.2
      rw [htop, Subgroup.card_top, h27] at hZ3
      norm_num at hZ3
    · exact (show 3 ∣ Nat.card H by rw [h27]; norm_num).trans (Subgroup.card_dvd_of_le hHG)
  ·
    exact ⟨Or.inr (Or.inr (Or.inr (K322Rows.monomial_conclusion hp2 hmono hxG hx4 hZ hfix))),
      three_dvd_card_of_monomial hmono, h3p⟩

end K322

end CFSG.LocalAnalysis.UniquenessCase.UCK
