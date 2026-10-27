module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofCover
import CFSG.RankThree.PartTwo.Sec15.Item156StepsProofHJ
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KS1515A7Aut : Prop :=
  ∀ (Q : Type) [Group Q], Nonempty (Q ≃* alternatingGroup (Fin 7)) →
    ∀ σ : Q ≃* Q, (∀ q, σ (σ (σ q)) = q) → ∀ x : Q, orderOf x = 5 → σ x = x → ∀ q, σ q = q

@[expose] def KS1515J2NoA7 : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ (K : Type) [Group K] (ι : K →* X), Function.Injective ι →
      ∀ f : K →* alternatingGroup (Fin 7), ¬ Function.Surjective f

namespace Proof1515Res

variable {G : Type} [Group G] [Finite G]

theorem theta_eq_pCore_two_of_isSimpleGroup {Y : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hs : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) (h3 : 3 ∣ Nat.card Y) :
    aschbacherSolvableCore 3 ↥Y = CFSG.pCore 2 ↥Y := by
  obtain ⟨-, hθc, hθ3, -, -, -, hcore⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥Y).Characteristic := hθc
  have : (aschbacherSolvableCore 3 ↥Y).Normal := Subgroup.normal_of_characteristic _
  have hZ0 : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    Proof1517.center_eq_bot_of_isSimpleGroup hq.1
  refine Proof1515.normal_eq_pCore_two_of hq
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3) (hcore 2 Nat.prime_two (by norm_num))
    (fun htop => hθ3 ?_) fun Z _ hZc _ _ => le_bot_iff.mp (hZ0 ▸ hZc)
  rw [htop, Subgroup.card_top]
  exact h3

theorem thetaQuotMulAut_pow_three {Y : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (q : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) :
    Sec4.thetaQuotMulAut ↥Y (Y.normalizerMonoidHom ⟨c, hcN⟩)
      (Sec4.thetaQuotMulAut ↥Y (Y.normalizerMonoidHom ⟨c, hcN⟩)
        (Sec4.thetaQuotMulAut ↥Y (Y.normalizerMonoidHom ⟨c, hcN⟩) q)) = q := by
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [Sec4.thetaQuotMulAut_mk, Sec4.thetaQuotMulAut_mk, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    simp only [Sec4.normalizerMonoidHom_apply_coe]
    have hccc : c * c * c = 1 := by rw [← pow_three']; exact hc3
    calc c * (c * (c * (y : G) * c⁻¹) * c⁻¹) * c⁻¹
        = (c * c * c) * (y : G) * (c * c * c)⁻¹ := by group
      _ = (y : G) := by rw [hccc, one_mul, inv_one, mul_one]

end Proof1515Res

open Proof1515 Proof1515Res

theorem step1515HJListA7_of (h142 : Item142R) (haut : KS1515A7Aut) (hJ2 : KS1515J2NoA7) :
    Step1515HJListA7 := by
  intro G _ _ A c L h hJ Y hY hm hsmall
  refine ⟨fun φY => ?_⟩
  have hD := h.toSec13Data
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYc : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 2520 := by
    rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven]
  have hsY : IsSimpleGroup (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    Proof1514.isSimpleGroup_of_mulEquiv_alternating (by norm_num) φY
  have := hsY
  have h3Y : 3 ∣ Nat.card Y :=
    (show 3 ∣ 2520 by norm_num).trans (hYc ▸ Subgroup.card_quotient_dvd_card _)
  have hθY := theta_eq_pCore_two_of_isSimpleGroup hY4.2.2.2 hsY h3Y
  have eYQ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y ⧸ aschbacherSolvableCore 3 ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hθY).symm
  have ψ : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y ≃* alternatingGroup (Fin 7) := eYQ.symm.trans φY
  have hq : CFSG.IsQuasisimple (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eYQ hY4.2.2.2
  have hsQ : IsSimpleGroup (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := eYQ.symm.isSimpleGroup
  have := hsQ
  have : Group.IsPerfect (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := hq.1
  have hQc : Nat.card (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = 2520 := by
    rw [← Nat.card_congr eYQ.toEquiv, hYc]
  have h3Q : 3 ∣ Nat.card (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by rw [hQc]; norm_num
  have hZQ : Subgroup.center (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = ⊥ :=
    Proof1517.center_eq_bot_of_isSimpleGroup hq.1
  have hX3 : 3 ∣ Nat.card ((↥Y ⧸ aschbacherSolvableCore 3 ↥Y) ⧸
      Subgroup.center (↥Y ⧸ aschbacherSolvableCore 3 ↥Y)) := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZQ).trans
      QuotientGroup.quotientBot).toEquiv]
    exact h3Q
  obtain ⟨X, hX4, hXLY⟩ := hm
  have h5X : 5 ∣ Nat.card X := by
    have hd := Subgroup.card_quotient_dvd_card (CFSG.pPrimeCore 3 ↥X)
    rcases hsmall X hX4 hXLY with h60 | h2520
    · rw [h60] at hd
      exact (show 5 ∣ 60 by norm_num).trans hd
    · rw [h2520] at hd
      exact (show 5 ∣ 2520 by norm_num).trans hd
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5X
  have hxL : (x : G) ∈ L := (hXLY.trans inf_le_left) x.2
  have hxY : (x : G) ∈ Y := (hXLY.trans inf_le_right) x.2
  have hx5G : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx5]
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hY4.1.2 hD.mem_A
  have hc3 : c ^ 3 = 1 := by rw [← hD.orderOf_eq]; exact pow_orderOf_eq_one c
  set σ := Sec4.thetaQuotMulAut ↥Y (Y.normalizerMonoidHom ⟨c, hcN⟩) with hσ
  set xb : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y :=
    ((⟨(x : G), hxY⟩ : ↥Y) : ↥Y ⧸ aschbacherSolvableCore 3 ↥Y) with hxb
  have hxc : c * (x : G) * c⁻¹ = (x : G) := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hxL)
    rw [← h1, mul_inv_cancel_right]
  have hσx : σ xb = xb := by
    rw [hσ, hxb, Sec4.thetaQuotMulAut_mk]
    congr 1
    exact Subtype.ext (by rw [Sec4.normalizerMonoidHom_apply_coe]; exact hxc)
  have hxb5 : orderOf xb = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hxb, ← QuotientGroup.mk_pow]
      have : ((⟨(x : G), hxY⟩ : ↥Y) ^ 5 : ↥Y) = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, ← hx5G, pow_orderOf_eq_one, Subgroup.coe_one])
      rw [this, QuotientGroup.mk_one]
    · intro h1
      have hmem : (⟨(x : G), hxY⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := by
        rw [← hθY]
        exact (QuotientGroup.eq_one_iff _).mp h1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨_, hmem⟩ : CFSG.pCore 2 ↥Y)
      have hk' : (x : G) ^ 2 ^ k = 1 := by
        have := congrArg (fun z : CFSG.pCore 2 ↥Y => ((z : ↥Y) : G)) hk
        simpa using this
      have h5 : 5 ∣ 2 ^ k := hx5G ▸ orderOf_dvd_of_pow_eq_one hk'
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_two).mp
        ((show Nat.Prime 5 by norm_num).dvd_of_dvd_pow h5)
      omega
  have hσ1 : σ = 1 := by
    have hall := haut (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) ⟨ψ⟩ σ
      (Proof1515Res.thetaQuotMulAut_pow_three hcN hc3) xb hxb5 hσx
    ext q
    rw [hall q, MulAut.one_apply]
  have hcC : c ∈ Sec4.thetaQuotCentralizer Y :=
    Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨hcN, hσ1⟩
  have hAnc := Proof156.not_le_thetaQuotCentralizer_of_mem_partTwoF hD.mem_partTwoF hY4.1.2
    hq.1 h3Q
  have hle := Proof156.le_inf_sup_theta_of_item142 h.toSec14Std hJ (h142 G A c L h) hY4.1.2
    hY4.2.2.1 hq hX3 hcC hAnc
  set M := Y ⊓ L with hM
  set g : ↥M →* ↥Y ⧸ aschbacherSolvableCore 3 ↥Y :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Y)).comp
    (Subgroup.inclusion (inf_le_left : M ≤ Y)) with hg
  have hgs : Function.Surjective g := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Y) q
    have hy : (y : G) ∈ ((M ⊔ inSubgroup (aschbacherSolvableCore 3) Y : Subgroup G) : Set G) :=
      hle y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M _
      (inf_le_left.trans (Sec6.le_normalizer_theta Y))] at hy
    obtain ⟨m, hm', t, ht, hmt⟩ := hy
    obtain ⟨t', ht', rfl⟩ := ht
    refine ⟨⟨m, hm'⟩, ?_⟩
    rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have he : (Subgroup.inclusion (inf_le_left : M ≤ Y) ⟨m, hm'⟩)⁻¹ * y = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hmt, Subgroup.coe_subtype]
      group
    rw [he]
    exact ht'
  set πL : ↥M →* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp
      (Subgroup.inclusion (inf_le_right : M ≤ L)) with hπL
  have hθLs : Group.IsSolvable (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hker : πL.ker ≤ (ψ.toMonoidHom.comp g).ker := by
    have hmap : πL.ker.map (Subgroup.inclusion (inf_le_right : M ≤ L)) ≤
        aschbacherSolvableCore 3 ↥L := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hsolv : Group.IsSolvable πL.ker := by
      have : Group.IsSolvable ((πL.ker.map (Subgroup.inclusion (inf_le_right : M ≤ L))).subgroupOf
          (aschbacherSolvableCore 3 ↥L)) := subgroup_solvable_of_solvable _
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hmap).symm.toMonoidHom.comp
          (πL.ker.equivMapOfInjective _ (Subgroup.inclusion_injective _)).toMonoidHom)
        ((Subgroup.subgroupOfEquivOfLe hmap).symm.injective.comp
          (πL.ker.equivMapOfInjective _ (Subgroup.inclusion_injective _)).injective)
    have hn : (πL.ker.map g).Normal := πL.normal_ker.map g hgs
    have hgk : πL.ker ≤ g.ker := by
      rcases hn.eq_bot_or_eq_top with h1 | h1
      · exact (Subgroup.map_eq_bot_iff _).mp h1
      · exfalso
        have hs' : Group.IsSolvable (πL.ker.map g) :=
          Group.isSolvable_of_surjective (g.subgroupMap_surjective πL.ker)
        have htop : Group.IsSolvable (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by
          rw [h1] at hs'
          exact Group.isSolvable_of_surjective
            (f := (⊤ : Subgroup (↥Y ⧸ aschbacherSolvableCore 3 ↥Y)).subtype)
            (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)
        have := hsQ.toNontrivial
        exact Group.IsPerfect.not_isSolvable _ htop
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (MonoidHom.mem_ker).mp (hgk hy)]
    exact map_one _
  have hf : Function.Surjective (QuotientGroup.lift πL.ker (ψ.toMonoidHom.comp g) hker) := by
    intro z
    obtain ⟨m, hm⟩ := hgs (ψ.symm z)
    refine ⟨(m : ↥M ⧸ πL.ker), ?_⟩
    rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hm,
      MulEquiv.apply_symm_apply]
  exact hJ2 _ hJ _ (QuotientGroup.kerLift πL) (QuotientGroup.kerLift_injective πL) _ hf

end CFSG.RankThree.PartTwo.Sec15
