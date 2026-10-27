module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.ZMod.Torsion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 5.1(b) from BG Section 5 -/

section

set_option maxHeartbeats 800000 in
private theorem CFSG.elementaryAbelian_card_ge_pow_generatorRank
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    p ^ generatorRank G ≤ Nat.card G := by
  letI : CommGroup G := IsMulCommutative.instCommGroup
  have hcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    calc
      Nat.card G = Nat.card (Additive G) := (Nat.card_congr Additive.toMul).symm
      _ = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (Additive G) :=
        Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)
      _ = p ^ Module.finrank (ZMod p) (Additive G) := by simp [ZMod.card]
  have hgr_le_finrank : generatorRank G ≤ Module.finrank (ZMod p) (Additive G) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) G
  rw [hcard]
  exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hgr_le_finrank

public theorem CFSG.generatorRank_at_least_three_of_elementaryAbelian_card_p3
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 3) :
    3 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 3 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank


private theorem CFSG.generatorRank_at_least_of_elementaryAbelian_subgroup_card_p3
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {G : Type*} [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)]
    {B : Subgroup G} [IsElementaryAbelian p B] (hBcard : Nat.card B = p ^ 3) :
    3 ≤ generatorRank G := by
  classical
  letI : CommGroup G := IsMulCommutative.instCommGroup
  by_contra hlt
  have hle_two : generatorRank G ≤ 2 := by omega
  have hmeta : IsMetacyclic G :=
    isMetacyclic_of_generatorRank_le_two_of_commutative G hle_two
  have hncyc : ¬ IsCyclic G := by
    intro hcyc
    letI : IsCyclic G := hcyc
    haveI : IsCyclic B := isCyclic_of_injective B.subtype B.subtype_injective
    have hB_rank : 3 ≤ generatorRank B :=
      generatorRank_at_least_three_of_elementaryAbelian_card_p3 (p := p) (A := B) hBcard
    have hB_le_one : generatorRank B ≤ 1 := by
      exact generatorRank_le_one_of_isCyclic (G := B) (by infer_instance)
    exact (by decide : ¬ 3 ≤ (1 : ℕ)) (hB_rank.trans hB_le_one)
  obtain ⟨hΩcard, _hΩelem⟩ := lemma_4_10 (R := G) (p := p) hpodd hmeta hncyc
  have hB_le_Ω : B ≤ omega₁ (G := G) (p := p) := elementaryAbelian_le_omega₁
  have hcard_le : p ^ 3 ≤ p ^ 2 := by
    rw [← hBcard, ← hΩcard]
    exact Subgroup.card_le_of_le hB_le_Ω
  exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_le |>.not_gt (by decide : 2 < 3)


private theorem CFSG.scnSubgroup_contains_of_normal_elementaryAbelian_card_p3
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {B : Subgroup R} [B.Normal] [IsElementaryAbelian p B]
    (hBcard : Nat.card B = p ^ 3) :
    ∃ A ∈ scnSubgroups 3 R, B ≤ A := by
  classical
  obtain ⟨A, hBA, hAnorm, hAcomm, hAmax⟩ :=
    exists_maximal_normal_abelian_subgroup_containing (G := R) B
      inferInstance (inferInstance : IsMulCommutative B)
  haveI : Fact (IsPGroup p R) := ⟨hpR⟩
  have hAself_le : Subgroup.centralizer (A : Set R) ≤ A :=
    maximal_normal_abelian_selfCentralizing_local (p := p) (A := A) hAnorm hAcomm hAmax
  have hAself : Subgroup.centralizer (A : Set R) = A := by
    exact le_antisymm hAself_le ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm)
  let Bsub : Subgroup A := B.subgroupOf A
  have hBsub_card : Nat.card Bsub = p ^ 3 := by
    exact (natCard_subgroupOf_eq B A hBA).trans hBcard
  have hBsub_elem : IsElementaryAbelian p Bsub := by
    refine { exponent_dvd_p := ?_ }
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      apply Subtype.ext
      have hxB : ((x : A) : R) ∈ B := by
        exact (Subgroup.mem_subgroupOf.mp x.property)
      have hxpow : ((⟨((x : A) : R), hxB⟩ : B) ^ p) = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p B) ⟨((x : A) : R), hxB⟩
      simpa using congrArg Subtype.val hxpow
  have hAp : IsPGroup p A := hpR.to_subgroup A
  have hArank : 3 ≤ generatorRank A := by
    letI : IsElementaryAbelian p Bsub := hBsub_elem
    letI : Fact (IsPGroup p A) := ⟨hAp⟩
    exact generatorRank_at_least_of_elementaryAbelian_subgroup_card_p3
      (p := p) hpodd (G := A) (B := Bsub) hBsub_card
  have hArank' : 3 ≤ groupRank A := by
    letI : IsMulCommutative A := hAcomm
    letI : Fact (IsPGroup p A) := ⟨hAp⟩
    exact hArank.trans (generatorRank_le_groupRank_of_commutative_pgroup (p := p) A)
  refine ⟨A, ?_, hBA⟩
  exact ⟨hAnorm, hAself, hArank'⟩

public theorem CFSG.quotient_centralizer_card_le_p_of_elementaryAbelian_rank_two
    {p : ℕ} [Fact p.Prime]
    {E Q : Type*} [Group E] [Finite E] [Group Q] [Finite Q]
    [IsElementaryAbelian p E] [Fact (IsPGroup p Q)]
    (hEcard : Nat.card E = p ^ 2)
    (_hoddQ : Odd (Nat.card Q))
    (i : Q →* MulAut E) (hi : Function.Injective i) :
    Nat.card Q ≤ p := by
  classical
  letI : MulDistribMulAction Q E := MulDistribMulAction.compHom E i
  have hQp : IsPGroup p Q := Fact.out
  have hfix_ne_bot : fixedPointSubgroup Q E ≠ ⊥ := by
    have hEcard_dvd : p ∣ Nat.card E := by
      rw [hEcard, pow_two]
      exact dvd_mul_right p p
    have hone_fix : (1 : E) ∈ MulAction.fixedPoints Q E := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨v, hvfix, hv_ne_one'⟩ :=
      hQp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := E) hEcard_dvd hone_fix
    have hv_ne_one : v ≠ 1 := by
      intro hv
      exact hv_ne_one' hv.symm
    intro hbot
    have hv_mem : v ∈ fixedPointSubgroup Q E := by
      rw [FixedPoints.mem_subgroup]
      exact MulAction.mem_fixedPoints.mp hvfix
    have hv_bot : v ∈ (⊥ : Subgroup E) := by simpa [hbot] using hv_mem
    exact hv_ne_one (Subgroup.mem_bot.mp hv_bot)
  by_cases hfix_top : fixedPointSubgroup Q E = ⊤
  · have htriv : ActsTrivially (A := Q) (G := E) := by
      intro q x
      have hxfix : x ∈ fixedPointSubgroup Q E := by simp [hfix_top]
      exact (FixedPoints.mem_subgroup (M := Q) (a := x)).mp hxfix q
    have hsub : Subsingleton Q := by
      refine ⟨?_⟩
      intro a b
      apply hi
      ext x
      change a • x = b • x
      exact (htriv a x).trans (htriv b x).symm
    have hcard_one : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hcard_one]
    exact (Fact.out : Nat.Prime p).one_lt.le
  · have hfix_pgroup : IsPGroup p (fixedPointSubgroup Q E) := by
      have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
      exact hEp.to_subgroup (fixedPointSubgroup Q E)
    have hfix_card_dvd : Nat.card (fixedPointSubgroup Q E) ∣ p ^ 2 := by
      simpa [hEcard] using Subgroup.card_subgroup_dvd_card (fixedPointSubgroup Q E)
    have hfix_card_eq_p : Nat.card (fixedPointSubgroup Q E) = p := by
      rcases hfix_pgroup.exists_card_eq with ⟨n, hn⟩
      have hnle : n ≤ 2 := by
        have hpow_dvd : p ^ n ∣ p ^ 2 := hn ▸ hfix_card_dvd
        exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_dvd
      have hne_zero : n ≠ 0 := by
        intro hn0
        have hcard_one : Nat.card (fixedPointSubgroup Q E) = 1 := by simpa [hn0] using hn
        exact hfix_ne_bot ((Subgroup.card_eq_one (H := fixedPointSubgroup Q E)).1 hcard_one)
      have hne_two : n ≠ 2 := by
        intro hn2
        apply hfix_top
        apply (Subgroup.card_eq_iff_eq_top (H := fixedPointSubgroup Q E)).1
        simpa [hn2, hEcard] using hn
      have hn_one : n = 1 := by omega
      simpa [hn_one] using hn
    have hfix_inv : IsInvariant Q E (fixedPointSubgroup Q E) := by
      refine ⟨?_⟩
      intro a g
      constructor
      · intro hg
        rw [FixedPoints.mem_subgroup] at hg ⊢
        intro b
        have hgfix := hg (a⁻¹ * b * a)
        calc
          b • (a • g) = a • ((a⁻¹ * b * a) • g) := by simp [mul_smul, mul_assoc]
          _ = a • g := by rw [hgfix]
      · intro hg
        rw [FixedPoints.mem_subgroup] at hg ⊢
        intro b
        have hgfix := hg (a * b * a⁻¹)
        calc
          b • g = a⁻¹ • ((a * b * a⁻¹) • (a • g)) := by simp [mul_smul, mul_assoc]
          _ = a⁻¹ • (a • g) := by rw [hgfix]
          _ = g := by simp
    letI : MulAction.QuotientAction Q (fixedPointSubgroup Q E) :=
      quotientAction_of_isInvariant (A := Q) (G := E) (fixedPointSubgroup Q E) hfix_inv
    letI : MulDistribMulAction Q (E ⧸ fixedPointSubgroup Q E) :=
      quotientMulDistribMulAction (A := Q) (G := E) (fixedPointSubgroup Q E) hfix_inv
    have hcard_quot :
        Nat.card (E ⧸ fixedPointSubgroup Q E) = p := by
      have hmul :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (α := E) (s := fixedPointSubgroup Q E)
      rw [hEcard, hfix_card_eq_p, pow_two] at hmul
      have hmul' : p * Nat.card (E ⧸ fixedPointSubgroup Q E) = p * p := by
        calc
          p * Nat.card (E ⧸ fixedPointSubgroup Q E)
              = Nat.card (E ⧸ fixedPointSubgroup Q E) * p := by rw [Nat.mul_comm]
          _ = p * p := hmul.symm
      exact Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos (Fact.out : Nat.Prime p)) hmul'
    have hquot_triv : ActsTrivially (A := Q) (G := E ⧸ fixedPointSubgroup Q E) := by
      have hcyc_quot : IsCyclic (E ⧸ fixedPointSubgroup Q E) := by
        exact isCyclic_of_prime_card hcard_quot
      letI : IsCyclic (E ⧸ fixedPointSubgroup Q E) := hcyc_quot
      let φ : Q →* MulAut (E ⧸ fixedPointSubgroup Q E) :=
        MulDistribMulAction.toMulAut Q (E ⧸ fixedPointSubgroup Q E)
      have hQ_top : IsPGroup p (⊤ : Subgroup Q) := by
        simpa using hQp.to_subgroup (⊤ : Subgroup Q)
      have hφrange_p : IsPGroup p φ.range := by
        rw [MonoidHom.range_eq_map]
        exact IsPGroup.map (p := p) (H := (⊤ : Subgroup Q)) hQ_top φ
      have hmulAut_card : Nat.card (MulAut (E ⧸ fixedPointSubgroup Q E)) = p - 1 := by
        rw [IsCyclic.card_mulAut, hcard_quot, Nat.totient_prime (Fact.out : Nat.Prime p)]
      have hp_not_dvd_mulAut : ¬ p ∣ Nat.card (MulAut (E ⧸ fixedPointSubgroup Q E)) := by
        intro hp_dvd
        have hdiv_one : p ∣ 1 := by
          have hdiv_sub : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) (hmulAut_card ▸ hp_dvd)
          have hsub : p - (p - 1) = 1 := by
            have hp_eq : p = (p - 1) + 1 := by
              simpa [Nat.succ_eq_add_one] using
                (Nat.succ_pred_eq_of_pos (Nat.Prime.pos (Fact.out : Nat.Prime p))).symm
            rw [hp_eq]
            exact Nat.add_sub_cancel_left (p - 1) 1
          rw [hsub] at hdiv_sub
          exact hdiv_sub
        exact (Fact.out : Nat.Prime p).not_dvd_one hdiv_one
      have hp_not_dvd_range : ¬ p ∣ Nat.card φ.range := by
        intro hp_dvd
        exact hp_not_dvd_mulAut (hp_dvd.trans (Subgroup.card_subgroup_dvd_card φ.range))
      have hφrange_card_one : Nat.card φ.range = 1 :=
        (hφrange_p.card_eq_or_dvd).resolve_right hp_not_dvd_range
      have hφrange_bot : φ.range = ⊥ := (Subgroup.card_eq_one (H := φ.range)).1 hφrange_card_one
      intro a g
      have ha_range : φ a ∈ φ.range := ⟨a, rfl⟩
      have ha_bot : φ a ∈ (⊥ : Subgroup (MulAut (E ⧸ fixedPointSubgroup Q E))) := by
        simpa [hφrange_bot] using ha_range
      have ha_one : φ a = 1 := by simpa using ha_bot
      simpa [φ, MulDistribMulAction.toMulAut_apply] using
        congrArg (fun f : MulAut (E ⧸ fixedPointSubgroup Q E) => f g) ha_one
    have hy_exists : ∃ y : E, y ∉ fixedPointSubgroup Q E := by
      by_contra hy
      push Not at hy
      apply hfix_top
      exact (Subgroup.eq_top_iff' (H := fixedPointSubgroup Q E)).2 hy
    obtain ⟨y, hy_notin_fix⟩ := hy_exists
    let q : E →* E ⧸ fixedPointSubgroup Q E := QuotientGroup.mk' (fixedPointSubgroup Q E)
    have hqy_ne_one : q y ≠ 1 := by
      intro hq1
      exact hy_notin_fix ((QuotientGroup.eq_one_iff (N := fixedPointSubgroup Q E) y).1 hq1)
    have hqy_zpow_top : Subgroup.zpowers (q y) = ⊤ := by
      have hcard_dvd : Nat.card (Subgroup.zpowers (q y)) ∣ Nat.card (E ⧸ fixedPointSubgroup Q E) :=
        Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (q y))
      have hcard_ne_one : Nat.card (Subgroup.zpowers (q y)) ≠ 1 := by
        intro hcard
        have hbot : Subgroup.zpowers (q y) = ⊥ :=
          (Subgroup.eq_bot_iff_card (H := Subgroup.zpowers (q y))).2 hcard
        have ha_bot : q y ∈ (⊥ : Subgroup (E ⧸ fixedPointSubgroup Q E)) := by
          simpa [hbot] using (Subgroup.mem_zpowers (q y))
        exact hqy_ne_one (by simpa using ha_bot)
      have hprime_quot : Nat.Prime (Nat.card (E ⧸ fixedPointSubgroup Q E)) := by
        simpa [hcard_quot] using (Fact.out : Nat.Prime p)
      have hcard_eq_or :
          Nat.card (Subgroup.zpowers (q y)) = 1 ∨
            Nat.card (Subgroup.zpowers (q y)) = Nat.card (E ⧸ fixedPointSubgroup Q E) :=
        hprime_quot.eq_one_or_self_of_dvd (Nat.card (Subgroup.zpowers (q y))) hcard_dvd
      have hcard_eq :
          Nat.card (Subgroup.zpowers (q y)) = Nat.card (E ⧸ fixedPointSubgroup Q E) :=
        hcard_eq_or.resolve_left hcard_ne_one
      exact (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers (q y))).1 hcard_eq
    have hfix_sup_zpowers : fixedPointSubgroup Q E ⊔ Subgroup.zpowers y = ⊤ := by
      apply (Subgroup.eq_top_iff' (H := fixedPointSubgroup Q E ⊔ Subgroup.zpowers y)).2
      intro g
      have hqg : q g ∈ Subgroup.zpowers (q y) := by
        rw [hqy_zpow_top]
        simp
      rcases (Subgroup.mem_zpowers_iff.mp hqg) with ⟨k, hk⟩
      have hqg_eq : q g = q y ^ k := by
        simpa [q] using hk.symm
      have hgu : g * (y ^ k)⁻¹ ∈ fixedPointSubgroup Q E := by
        exact (QuotientGroup.eq_one_iff (N := fixedPointSubgroup Q E) (g * (y ^ k)⁻¹)).mp <| by
          calc
            q (g * (y ^ k)⁻¹) = q g * (q (y ^ k))⁻¹ := by simp [q, map_mul]
            _ = (q y ^ k) * (q (y ^ k))⁻¹ := by rw [hqg_eq]
            _ = 1 := by simp [q]
      exact (Subgroup.mem_sup_of_normal_left (x := g) (s := fixedPointSubgroup Q E)
          (t := Subgroup.zpowers y)).2
        ⟨g * (y ^ k)⁻¹, hgu, y ^ k, Subgroup.zpow_mem_zpowers y k, by simp [mul_assoc]⟩
    let φ : Q → fixedPointSubgroup Q E := fun q =>
      ⟨(q • y) * y⁻¹, by
        exact (QuotientGroup.eq_one_iff (N := fixedPointSubgroup Q E) ((q • y) * y⁻¹)).mp <| by
          have hybar_fix : ((q • y : E) : E ⧸ fixedPointSubgroup Q E) =
              ((y : E) : E ⧸ fixedPointSubgroup Q E) := by
            simpa using hquot_triv q ((y : E) : E ⧸ fixedPointSubgroup Q E)
          calc
            (((q • y) * y⁻¹ : E) : E ⧸ fixedPointSubgroup Q E)
                = ((q • y : E) : E ⧸ fixedPointSubgroup Q E) *
                    (((y : E) : E ⧸ fixedPointSubgroup Q E))⁻¹ := by simp
            _ = ((y : E) : E ⧸ fixedPointSubgroup Q E) *
                  (((y : E) : E ⧸ fixedPointSubgroup Q E))⁻¹ := by rw [hybar_fix]
            _ = 1 := by simp⟩
    have hφ_injective : Function.Injective φ := by
      intro a b hab
      apply hi
      ext z
      change a • z = b • z
      have hyab : a • y = b • y := by
        have hφeq_val :
            (((φ a : fixedPointSubgroup Q E) : E)) = (((φ b : fixedPointSubgroup Q E) : E)) :=
          congrArg Subtype.val hab
        simpa [φ, mul_assoc] using congrArg (fun t : E => t * y) hφeq_val
      have hz_sup : z ∈ fixedPointSubgroup Q E ⊔ Subgroup.zpowers y := by
        simp [hfix_sup_zpowers]
      rcases (Subgroup.mem_sup_of_normal_left (x := z) (s := fixedPointSubgroup Q E)
          (t := Subgroup.zpowers y)).1 hz_sup with ⟨u, hu_fix, w, hw_zpow, rfl⟩
      rcases (Subgroup.mem_zpowers_iff.mp hw_zpow) with ⟨k, rfl⟩
      have hua : a • u = u := (FixedPoints.mem_subgroup (M := Q) (a := u)).mp hu_fix a
      have hub : b • u = u := (FixedPoints.mem_subgroup (M := Q) (a := u)).mp hu_fix b
      have hyk_ab : a • (y ^ k) = b • (y ^ k) := by
        calc
          a • (y ^ k) = (a • y) ^ k := by
            simpa using (map_zpow (MulDistribMulAction.toMulAut Q E a) y k)
          _ = (b • y) ^ k := by
            simpa using congrArg (fun t : E => t ^ k) hyab
          _ = b • (y ^ k) := by
            simpa using (map_zpow (MulDistribMulAction.toMulAut Q E b) y k).symm
      calc
        a • (u * y ^ k) = a • u * (a • (y ^ k)) := by simp
        _ = u * (a • (y ^ k)) := by rw [hua]
        _ = u * (b • (y ^ k)) := by rw [hyk_ab]
        _ = b • u * (b • (y ^ k)) := by rw [hub]
        _ = b • (u * y ^ k) := by simp
    exact (Nat.card_le_card_of_injective (f := φ) hφ_injective).trans hfix_card_eq_p.le


public theorem CFSG.scnSubgroup_normal_commutative
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] [Finite R] (_hpR : IsPGroup p R)
    {A : Subgroup R} (hA : A ∈ scnSubgroups 3 R) :
    A.Normal ∧ IsMulCommutative A := by
  rcases hA with ⟨hAnorm, hAcent, _hArank⟩
  have hAcomm : IsMulCommutative A := by
    have hAle : A ≤ Subgroup.centralizer (A : Set R) := by
      simp [hAcent]
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 hAle
  exact ⟨hAnorm, hAcomm⟩

public theorem CFSG.scnSubgroup_generatorRank_at_least_three
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {A : Subgroup R} (hA : A ∈ scnSubgroups 3 R) :
    3 ≤ generatorRank A := by
  rcases hA with ⟨_hAnorm, hAcent, hArank⟩
  have hAcomm : IsMulCommutative A := by
    have hAle : A ≤ Subgroup.centralizer (A : Set R) := by
      simp [hAcent]
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 hAle
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hpA : IsPGroup p A := hpR.to_subgroup A
  have hnonempty : (selfCentralizingAbelianSubgroupsAtLeast A 3 : Set (Subgroup A)).Nonempty := by
    by_contra hempty
    have hAempty : selfCentralizingAbelianSubgroupsAtLeast A 3 = ∅ := by
      ext B
      constructor
      · intro hB
        exact False.elim (hempty ⟨B, hB⟩)
      · intro hB
        simp at hB
    have h47 := lemma_4_7 (R := A) (p := p) hpodd
    have hAle : groupRank A ≤ 2 := (h47 hpA).mp hAempty
    exact (by decide : ¬ 3 ≤ (2 : ℕ)) (le_trans hArank hAle)
  obtain ⟨B, ⟨⟨_hBnorm, hBcent⟩, hBgen⟩⟩ := hnonempty
  have hcenter : Subgroup.center A = ⊤ := by
    refine (Subgroup.eq_top_iff' (H := Subgroup.center A)).2 ?_
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    exact mul_comm y x
  have hBcent_top : Subgroup.centralizer (B : Set A) = ⊤ := by
    apply (Subgroup.centralizer_eq_top_iff_subset).2
    intro x hx
    rw [hcenter]
    exact Subgroup.mem_top x
  have hBtop : B = ⊤ := by
    calc
      B = Subgroup.centralizer (B : Set A) := hBcent.symm
      _ = ⊤ := hBcent_top
  have htop_rank : generatorRank (⊤ : Subgroup A) = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr Subgroup.topEquiv
  have hB_rank : generatorRank B = generatorRank A := by
    rw [hBtop, htop_rank]
  exact hB_rank ▸ hBgen

public theorem CFSG.omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [IsMulCommutative G] :
    IsElementaryAbelian p (omega₁ (G := G) (p := p)) := by
  letI : CommGroup G := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : G | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

private theorem CFSG.omega1_card_eq_card_quotient_frattini_of_commutative
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)] :
    Nat.card (omega₁ (G := G) (p := p)) = Nat.card (G ⧸ frattini G) := by
  classical
  letI : CommGroup G := IsMulCommutative.instCommGroup
  let φ : G →* G := powMonoidHom p
  have hφker : φ.ker = omega₁ (G := G) (p := p) := by
    ext x
    constructor
    · intro hx
      change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [φ, pow_one] using hx
    · intro hx
      refine
        Subgroup.closure_induction (k := {y : G | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ∈ φ.ker) (x := x) (by
            intro y hy
            simpa [φ, pow_one] using hy) (by simp [φ]) (by
            intro y z _ _ hy hz
            have hy' : y ^ p = 1 := by simpa [φ] using hy
            have hz' : z ^ p = 1 := by simpa [φ] using hz
            simp [φ, mul_pow, hy', hz']) (by
            intro y _ hy
            exact φ.ker.inv_mem hy) hx
  have hφrange : φ.range = frattini G := by
    have hcomm_top :
        (⊤ : Subgroup G) ≤ Subgroup.centralizer (((⊤ : Subgroup G) : Set G)) := by
      intro x _hx
      rw [Subgroup.mem_centralizer_iff]
      intro y _hy
      exact mul_comm y x
    have hcomm_bot : _root_.commutator G = ⊥ := by
      have htop_comm_bot : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcomm_top
      simpa [_root_.commutator_def] using htop_comm_bot
    have hderived_bot : derivedSubgroup G = ⊥ := by
      change derivedSeries G 1 = ⊥
      rw [derivedSeries_one]
      exact hcomm_bot
    have hrange :
        Set.range (fun x : G => x ^ p) = ((φ.range : Subgroup G) : Set G) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [φ]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa [φ] using hx⟩
    have hfrattini : frattini G = φ.range := by
      calc
        frattini G =
            Subgroup.closure ((derivedSubgroup G : Set G) ∪ Set.range (fun x : G => x ^ p)) := by
              simpa using (lemma_1_7_d (R := G) (p := p))
        _ = Subgroup.closure (Set.range (fun x : G => x ^ p)) := by
              rw [hderived_bot]
              simp
        _ = Subgroup.closure ((φ.range : Subgroup G) : Set G) := by rw [hrange]
        _ = φ.range := by simpa using (Subgroup.closure_eq (K := φ.range))
    exact hfrattini.symm
  have hcard_range :
      Nat.card (G ⧸ φ.ker) = Nat.card φ.range := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hmul_ker :
      Nat.card G = Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) := by
    calc
      Nat.card G = Nat.card (G ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hcard_range]
      _ = Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) := by
        rw [hφrange, hφker]
  have hmul_frattini :
      Nat.card G = Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
    calc
      Nat.card G = Nat.card (G ⧸ frattini G) * Nat.card (frattini G) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := frattini G)
      _ = Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
        rw [Nat.mul_comm]
  have hΦpos : 0 < Nat.card (frattini G) := by
    exact Nat.card_pos (α := frattini G)
  have hmul_eq :
      Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) =
        Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
    exact hmul_ker.symm.trans hmul_frattini
  exact Nat.eq_of_mul_eq_mul_left hΦpos hmul_eq

public theorem CFSG.isElementaryAbelian_of_le
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] {H K : Subgroup G}
    [IsElementaryAbelian p K] (hHK : H ≤ K) :
    IsElementaryAbelian p H := by
  refine
    { toIsMulCommutative := by
        exact
          { is_comm := ⟨fun x y =>
              Subtype.ext <|
                setLike_mul_comm (s := K)
                  (hHK x.2) (hHK y.2)⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  let xK : K := ⟨(x : G), hHK x.2⟩
  have hxpow : xK ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p K) xK
  simpa [xK] using congrArg Subtype.val hxpow

private theorem CFSG.isElementaryAbelian_sup_of_le_centralizer
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {E C : Subgroup G} [E.Normal]
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  refine
    { toIsMulCommutative := by
        refine (Subgroup.le_centralizer_iff_isMulCommutative (K := E ⊔ C)).1 ?_
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        change u ∈ E ⊔ C at hu
        change v ∈ E ⊔ C at hv
        rcases (Subgroup.mem_sup_of_normal_left (x := u) (s := E) (t := C)).1 hu with
          ⟨e₁, he₁, c₁, hc₁, rfl⟩
        rcases (Subgroup.mem_sup_of_normal_left (x := v) (s := E) (t := C)).1 hv with
          ⟨e₂, he₂, c₂, hc₂, rfl⟩
        symm
        have hc₁e₂ : c₁ * e₂ = e₂ * c₁ :=
          ((Subgroup.mem_centralizer_iff.mp (hCE hc₁)) e₂ he₂).symm
        have hc₂e₁ : c₂ * e₁ = e₁ * c₂ :=
          ((Subgroup.mem_centralizer_iff.mp (hCE hc₂)) e₁ he₁).symm
        have he₁e₂ : e₁ * e₂ = e₂ * e₁ := by
          simpa using congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := E)).comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
        have hc₁c₂ : c₁ * c₂ = c₂ * c₁ := by
          simpa using congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := C)).comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩)
        calc
          (e₁ * c₁) * (e₂ * c₂) = e₁ * e₂ * (c₁ * c₂) := by
            rw [mul_assoc, ← mul_assoc c₁ e₂ c₂, hc₁e₂]
            simp [mul_assoc]
          _ = e₂ * e₁ * (c₂ * c₁) := by rw [he₁e₂, hc₁c₂]
          _ = e₂ * (c₂ * (e₁ * c₁)) := by
            have hinner : e₁ * (c₂ * c₁) = c₂ * (e₁ * c₁) := by
              calc
                e₁ * (c₂ * c₁) = (e₁ * c₂) * c₁ := by simp [mul_assoc]
                _ = (c₂ * e₁) * c₁ := by rw [← hc₂e₁]
                _ = c₂ * (e₁ * c₁) := by simp [mul_assoc]
            rw [mul_assoc, hinner]
          _ = (e₂ * c₂) * (e₁ * c₁) := by
            simp [mul_assoc]
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases (Subgroup.mem_sup_of_normal_left (x := (x : G)) (s := E) (t := C)).1 x.2 with
    ⟨e, he, c, hc, hxec⟩
  have hepow : (⟨e, he⟩ : E) ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨e, he⟩
  have hcpow : (⟨c, hc⟩ : C) ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p C) ⟨c, hc⟩
  have hec : Commute e c := by
    show e * c = c * e
    exact (Subgroup.mem_centralizer_iff.mp (hCE hc)) e he
  have hepow' : e ^ p = 1 := by
    simpa using congrArg Subtype.val hepow
  have hcpow' : c ^ p = 1 := by
    simpa using congrArg Subtype.val hcpow
  calc
    ((x : G)) ^ p = (e * c) ^ p := by simp [hxec]
    _ = e ^ p * c ^ p := by simpa using hec.mul_pow p
    _ = 1 := by simp [hepow', hcpow']

public theorem CFSG.isElementaryAbelian_sup_of_le_centralizer'
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {E C : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  let s : Set G := (E : Set G) ∪ (C : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  letI : IsMulCommutative ↥(Subgroup.closure s) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
  refine
    { toIsMulCommutative := by
        rw [hsup]
        infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          show y * z = z * y
          exact setLike_mul_comm (s := Subgroup.closure s) hy hz
        · calc
            (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
            _ = 1 := by simp [hypow, hzpow]
        ) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

public theorem CFSG.isElementaryAbelian_zpowers_of_pow_eq_one
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)


private theorem CFSG.exists_normal_elementaryAbelian_card_p3_of_scn_three_checked
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R)
    {A : Subgroup R} (hA : A ∈ scnSubgroups 3 R) :
    ∃ B : Subgroup R, B.Normal ∧ IsElementaryAbelian p B ∧ Nat.card B = p ^ 3 ∧ B ≤ A := by
  classical
  have hArank : 3 ≤ generatorRank A :=
    scnSubgroup_generatorRank_at_least_three (p := p) hpodd (R := R) hpR hA
  obtain ⟨hAnorm, hAcomm⟩ := scnSubgroup_normal_commutative (p := p) (R := R) hpR hA
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
  let Ω : Subgroup R := Ωsub.map A.subtype
  have hΩnorm : Ω.Normal := by
    letI : A.Normal := hAnorm
    letI : Ωsub.Characteristic := by
      simpa [Ωsub] using (omega₁_characteristic (G := A) (p := p))
    simpa [Ω] using (inferInstance : Ω.Normal)
  have hΩle : Ω ≤ A := by
    simpa [Ω] using (Subgroup.map_subtype_le Ωsub)
  have hΩsub_elem : IsElementaryAbelian p Ωsub := by
    letI : IsMulCommutative A := hAcomm
    simpa [Ωsub] using omega1_isElementaryAbelian_of_commutative (p := p) A
  letI : IsElementaryAbelian p Ωsub := hΩsub_elem
  have hΩelem : IsElementaryAbelian p Ω := by
    refine
      { toIsMulCommutative := by
          simpa [Ω] using (Subgroup.map_isMulCommutative (f := A.subtype) (H := Ωsub))
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    rcases Subgroup.mem_map.mp x.2 with ⟨y, hyΩ, hyx⟩
    let yΩ : Ωsub := ⟨y, hyΩ⟩
    have hy_pow : yΩ ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Ωsub) yΩ
    have hy_pow_R : ((((yΩ : Ωsub) : A) : R) ^ p) = 1 := by
      simpa using congrArg A.subtype (congrArg Subtype.val hy_pow)
    have hx_eq : ((x : Ω) : R) = (((yΩ : Ωsub) : A) : R) := by
      simpa [yΩ] using hyx.symm
    calc
      ((x : Ω) : R) ^ p = (((yΩ : Ωsub) : A) : R) ^ p := by simp [hx_eq]
      _ = 1 := hy_pow_R
  letI : IsElementaryAbelian p Ω := hΩelem
  haveI : Fact (IsPGroup p A) := ⟨hpR.to_subgroup A⟩
  have hΩsub_card :
      Nat.card Ωsub = Nat.card (A ⧸ frattini A) := by
    letI : IsMulCommutative A := hAcomm
    simpa [Ωsub] using omega1_card_eq_card_quotient_frattini_of_commutative (p := p) A
  have hquot_rank : 3 ≤ generatorRank (A ⧸ frattini A) := by
    exact hArank.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A)
  have hpow_le_quot : p ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    letI : IsElementaryAbelian p (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p)
    calc
      p ^ 3 ≤ p ^ generatorRank (A ⧸ frattini A) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquot_rank
      _ ≤ Nat.card (A ⧸ frattini A) := by
        exact elementaryAbelian_card_ge_pow_generatorRank (p := p) (G := A ⧸ frattini A)
  have hpow_le_Ωsub : p ^ 3 ≤ Nat.card Ωsub := by
    rw [hΩsub_card]
    exact hpow_le_quot
  have hΩsub_card_map :
      Nat.card Ωsub = Nat.card Ω := by
    simpa [Ω] using
      Nat.card_congr
        (Subgroup.equivMapOfInjective (f := A.subtype) Ωsub A.subtype_injective).toEquiv
  have hpow_le_Ω : p ^ 3 ≤ Nat.card Ω := by
    calc
      p ^ 3 ≤ Nat.card Ωsub := hpow_le_Ωsub
      _ = Nat.card Ω := hΩsub_card_map
  have hΩp : IsPGroup p Ω := hpR.to_subgroup Ω
  rcases hΩp.exists_card_eq with ⟨k, hk⟩
  have hk3 : 3 ≤ k := by
    rw [hk] at hpow_le_Ω
    exact
      (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le_Ω
  haveI : Fact (IsPGroup p R) := ⟨hpR⟩
  obtain ⟨B, hBnorm, hBΩ, hBcard⟩ :=
    lemma_1_22 (G := R) p Ω hΩnorm k hk 3 hk3
  have hBelem : IsElementaryAbelian p B := by
    letI : IsMulCommutative Ω := hΩelem.toIsMulCommutative
    refine
      { toIsMulCommutative := by
          exact
            { is_comm := ⟨fun x y =>
                Subtype.ext <|
                  setLike_mul_comm (s := Ω)
                    (hBΩ x.2) (hBΩ y.2)⟩ }
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    let xΩ : Ω := ⟨(x : R), hBΩ x.2⟩
    have hxpow : xΩ ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Ω) xΩ
    simpa [xΩ] using congrArg Subtype.val hxpow
  exact ⟨B, hBnorm, hBelem, hBcard, hBΩ.trans hΩle⟩

public theorem CFSG.exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} [E.Normal] (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R) :
    ∃ B : Subgroup R, B.Normal ∧ IsElementaryAbelian p B ∧ Nat.card B = p ^ 3 ∧ E ≤ B := by
  classical
  rcases hE with ⟨hEcard, hEelem⟩
  letI : IsElementaryAbelian p E := hEelem
  obtain ⟨A, hA⟩ := lemma_5_1_a (p := p) hpodd (R := R) hpR hR
  obtain ⟨B₀, hB₀norm, hB₀elem, hB₀card, _hB₀A⟩ :=
    exists_normal_elementaryAbelian_card_p3_of_scn_three_checked
      (p := p) hpodd hpR hA
  letI : B₀.Normal := hB₀norm
  letI : IsElementaryAbelian p B₀ := hB₀elem
  let C : Subgroup R := B₀ ⊓ Subgroup.centralizer (E : Set R)
  have hCnorm : C.Normal := by
    letI : (Subgroup.centralizer (E : Set R)).Normal := by infer_instance
    simpa [C] using (inferInstance : C.Normal)
  have hC_le_B₀ : C ≤ B₀ := inf_le_left
  have hCelem : IsElementaryAbelian p C := isElementaryAbelian_of_le (p := p) hC_le_B₀
  letI : IsElementaryAbelian p C := hCelem
  let Csub : Subgroup B₀ := C.subgroupOf B₀
  let φ : B₀ →* MulAut E := (MulAut.conjNormal (H := E)).comp B₀.subtype
  have hker : φ.ker = Csub := by
    ext b
    constructor
    · intro hb
      change (b : R) ∈ C
      refine ⟨b.2, ?_⟩
      show (b : R) ∈ Subgroup.centralizer (E : Set R)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      let eE : E := ⟨e, he⟩
      have hfix : φ b eE = eE := by
        simpa using congrArg (fun f : MulAut E => f eE) hb
      have hconj : (b : R) * e * (b : R)⁻¹ = e := by
        simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
      have hmul : (b : R) * e = e * (b : R) := by
        simpa [mul_assoc] using congrArg (fun t : R => t * (b : R)) hconj
      exact hmul.symm
    · intro hb
      change φ b = 1
      ext e
      have hbcent : (b : R) ∈ Subgroup.centralizer (E : Set R) := hb.2
      have hmul : ((e : E) : R) * (b : R) = (b : R) * ((e : E) : R) :=
        (Subgroup.mem_centralizer_iff.mp hbcent) ((e : E) : R) e.2
      have hconj : (b : R) * ((e : E) : R) * (b : R)⁻¹ = ((e : E) : R) := by
        calc
          (b : R) * ((e : E) : R) * (b : R)⁻¹ = ((e : E) : R) * (b : R) * (b : R)⁻¹ := by
            rw [hmul.symm]
          _ = ((e : E) : R) := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply]
        using hconj
  have hQp : IsPGroup p (B₀ ⧸ φ.ker) := (hpR.to_subgroup B₀).to_quotient (φ.ker)
  haveI : Fact (IsPGroup p (B₀ ⧸ φ.ker)) := ⟨hQp⟩
  have hQodd : Odd (Nat.card (B₀ ⧸ φ.ker)) := by
    rcases hQp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (show Odd p from (Fact.out : Nat.Prime p).odd_of_ne_two hpodd).pow
  have hQle : Nat.card (B₀ ⧸ Csub) ≤ p := by
    simpa [hker] using
      quotient_centralizer_card_le_p_of_elementaryAbelian_rank_two
        (p := p) (E := E) (Q := B₀ ⧸ φ.ker) hEcard hQodd
        (i := QuotientGroup.kerLift φ) (hi := QuotientGroup.kerLift_injective (φ := φ))
  have hCsub_card_ge : p ^ 2 ≤ Nat.card Csub := by
    have hmul :
        Nat.card B₀ = Nat.card (B₀ ⧸ Csub) * Nat.card Csub :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Csub)
    have hmul_le : p ^ 3 ≤ p * Nat.card Csub := by
      calc
        p ^ 3 = Nat.card (B₀ ⧸ Csub) * Nat.card Csub := by simpa [hB₀card] using hmul
        _ ≤ p * Nat.card Csub := Nat.mul_le_mul_right _ hQle
    have hmul_le' : p * (p ^ 2) ≤ p * Nat.card Csub := by
      simpa [pow_succ', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul_le
    exact Nat.le_of_mul_le_mul_left hmul_le' (Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hCsub_card :
      Nat.card Csub = Nat.card C := by
    exact
      (natCard_subgroupOf_eq C B₀ hC_le_B₀)
  have hCcard_ge : p ^ 2 ≤ Nat.card C := by
    rw [← hCsub_card]
    exact hCsub_card_ge
  let D : Subgroup R := E ⊔ C
  have hDnorm : D.Normal := by
    letI : C.Normal := hCnorm
    simpa [D] using (Subgroup.sup_normal E C)
  have hCcentE : C ≤ Subgroup.centralizer (E : Set R) := inf_le_right
  have hDelem : IsElementaryAbelian p D := by
    letI : C.Normal := hCnorm
    simpa [D] using isElementaryAbelian_sup_of_le_centralizer (p := p) (E := E) (C := C) hCcentE
  letI : IsElementaryAbelian p D := hDelem
  have hED : E ≤ D := le_sup_left
  have hD_ge : p ^ 3 ≤ Nat.card D := by
    by_contra hlt
    have hDlt : Nat.card D < p ^ 3 := Nat.lt_of_not_ge hlt
    have hDp : IsPGroup p D := IsElementaryAbelian.isPGroup p D
    rcases hDp.exists_card_eq with ⟨n, hn⟩
    have hnge : 2 ≤ n := by
      have hE_le_D : p ^ 2 ≤ p ^ n := by
        calc
          p ^ 2 = Nat.card E := hEcard.symm
          _ ≤ Nat.card D := Subgroup.card_le_of_le hED
          _ = p ^ n := hn
      exact
        (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hE_le_D
    have hnlt : n < 3 := by
      rw [hn] at hDlt
      exact
        (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hDlt
    have hn2 : n = 2 := by omega
    have hDcard_eq : Nat.card D = p ^ 2 := by simpa [hn2] using hn
    have hDE : E = D :=
      Subgroup.eq_of_le_of_card_ge hED <| by
        rw [hDcard_eq, hEcard]
    have hC_le_E : C ≤ E := by
      intro c hc
      have hcD : c ∈ D := Subgroup.mem_sup_right hc
      simpa [hDE] using hcD
    have hCE : C = E :=
      Subgroup.eq_of_le_of_card_ge hC_le_E <| by
        simpa [hEcard] using hCcard_ge
    have hE_le_B₀ : E ≤ B₀ := by
      simpa [hCE] using hC_le_B₀
    have hB₀_le_cent : B₀ ≤ Subgroup.centralizer (E : Set R) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hmul : b * e = e * b :=
        setLike_mul_comm (s := B₀) hb (hE_le_B₀ he)
      exact hmul.symm
    have hB₀_le_C : B₀ ≤ C := by
      intro b hb
      exact ⟨hb, hB₀_le_cent hb⟩
    have hB₀C : B₀ = C := le_antisymm hB₀_le_C hC_le_B₀
    have hCcard : Nat.card C = p ^ 2 := by simpa [hCE] using hEcard
    have hpow_eq : p ^ 2 = p ^ 3 := by simpa [hB₀C, hCcard] using hB₀card
    have hpinj :=
      Nat.pow_right_injective (Nat.Prime.two_le (Fact.out : Nat.Prime p)) hpow_eq
    omega
  by_cases hDcard : Nat.card D = p ^ 3
  · exact ⟨D, hDnorm, hDelem, hDcard, hED⟩
  · have hDgt : p ^ 3 < Nat.card D := lt_of_le_of_ne hD_ge <| by
      simpa [eq_comm] using hDcard
    letI : D.Normal := hDnorm
    let q : R →* R ⧸ E := QuotientGroup.mk' E
    let Dbar : Subgroup (R ⧸ E) := D.map q
    have hDbar_norm : Dbar.Normal := by
      simpa [Dbar, q] using (QuotientGroup.map_normal E D)
    letI : Dbar.Normal := hDbar_norm
    have hDbar_p : IsPGroup p Dbar := (hpR.to_quotient E).to_subgroup Dbar
    have hDbar_comap : Dbar.comap q = D := by
      calc
        Dbar.comap q = E ⊔ D := by
          change Subgroup.comap (QuotientGroup.mk' E) (Subgroup.map (QuotientGroup.mk' E) D) = E ⊔ D
          exact QuotientGroup.comap_map_mk' (N := E) (H := D)
        _ = D := sup_eq_right.mpr hED
    have hcardQuotD : Nat.card (D ⧸ q.ker.subgroupOf D) = Nat.card Dbar := by
      have hcardQuotD' :
          Nat.card ((Dbar.comap q) ⧸ q.ker.subgroupOf (Dbar.comap q)) = Nat.card Dbar := by
        exact
          card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective E)
            (H := Dbar)
      rw [← hDbar_comap]
      exact hcardQuotD'
    have hcardKerSubD : Nat.card (q.ker.subgroupOf D) = Nat.card E := by
      have hcardKerSubD' :
          Nat.card (q.ker.subgroupOf (Dbar.comap q)) = Nat.card q.ker := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Dbar))).toEquiv
      rw [← hDbar_comap]
      rw [hcardKerSubD']
      simp [q, QuotientGroup.ker_mk']
    have hDcard_expr : Nat.card D = Nat.card Dbar * Nat.card E := by
      calc
        Nat.card D = Nat.card (D ⧸ q.ker.subgroupOf D) * Nat.card (q.ker.subgroupOf D) := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf D))
        _ = Nat.card Dbar * Nat.card E := by rw [hcardQuotD, hcardKerSubD]
    have hDbar_ne_one : Nat.card Dbar ≠ 1 := by
      intro hone
      have hDcard_eq : Nat.card D = p ^ 2 := by
        rw [hDcard_expr, hone, hEcard]
        simp
      have h32 : 3 < 2 := by
        exact
          (Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp <|
            by simpa [hDcard_eq] using hDgt
      omega
    haveI : Fact (IsPGroup p (R ⧸ E)) := ⟨hpR.to_quotient E⟩
    rcases hDbar_p.exists_card_eq with ⟨m, hm⟩
    have h1le : 1 ≤ m := by
      cases m with
      | zero =>
          exfalso
          apply hDbar_ne_one
          simp [hm]
      | succ m =>
          exact Nat.succ_le_succ (Nat.zero_le _)
    obtain ⟨Zbar, hZbar_norm, hZbar_le_Dbar, hZbar_card⟩ :=
      lemma_1_22 (G := R ⧸ E) p Dbar hDbar_norm m hm 1 h1le
    letI : Zbar.Normal := hZbar_norm
    let K : Subgroup R := Zbar.comap q
    have hKnorm : K.Normal := by infer_instance
    have hE_le_K : E ≤ K := by
      simpa [K, q, QuotientGroup.ker_mk'] using
        (Subgroup.ker_le_comap (f := q) (H := Zbar))
    have hK_le_D : K ≤ D := by
      have hKDbar : K ≤ Dbar.comap q := Subgroup.comap_mono hZbar_le_Dbar
      simpa [K, hDbar_comap] using hKDbar
    have hKelem : IsElementaryAbelian p K := isElementaryAbelian_of_le (p := p) hK_le_D
    have hcardQuotK : Nat.card (K ⧸ q.ker.subgroupOf K) = Nat.card Zbar := by
      simpa [K, q] using
        (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective E)
          (H := Zbar))
    have hcardKerSubK : Nat.card (q.ker.subgroupOf K) = Nat.card E := by
      have hcardKerSubK' : Nat.card (q.ker.subgroupOf K) = Nat.card q.ker := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Zbar))).toEquiv
      rw [hcardKerSubK']
      simp [q, QuotientGroup.ker_mk']
    have hKcard : Nat.card K = p ^ 3 := by
      calc
        Nat.card K = Nat.card (K ⧸ q.ker.subgroupOf K) * Nat.card (q.ker.subgroupOf K) := by
          simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf K))
        _ = Nat.card Zbar * Nat.card E := by rw [hcardQuotK, hcardKerSubK]
        _ = p ^ 1 * p ^ 2 := by rw [hZbar_card, hEcard]
        _ = p ^ 3 := by simp [pow_succ']
    exact ⟨K, hKnorm, hKelem, hKcard, hE_le_K⟩

public theorem CFSG.lemma_5_1_b
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} [E.Normal] (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R) :
    ∃ A ∈ scnSubgroups 3 R, E ≤ A := by
  classical
  obtain ⟨B, hBnorm, hBelem, hBcard, hEB⟩ :=
    exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal
      (p := p) hpodd hpR hR hE
  letI : B.Normal := hBnorm
  letI : IsElementaryAbelian p B := hBelem
  obtain ⟨A, hA, hBA⟩ :=
    scnSubgroup_contains_of_normal_elementaryAbelian_card_p3 (p := p) hpodd hpR hBcard
  exact ⟨A, hA, hEB.trans hBA⟩

end
