module

public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofCore
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1919SplitAut : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    ((∃ n : ℕ, 1 ≤ n ∧
        ((Even n ∧ Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∨
          Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) ∨
          Sec8.IsoGTwoEven Y n)) ∨
      Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 3)) →
    ∀ E : Subgroup (MulAut Y), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    ∀ F : Subgroup (MulAut Y), F ≤ E → F ≤ (MulAut.conj : Y →* MulAut Y).range →
      Nat.card F = 9 → ∀ c ∈ E, c ∉ F → ∀ P : Subgroup Y, IsProperParabolic P →
        ¬ ∀ y : Y, c y = y → y ∈ P

namespace Item19ResProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quotAct_eq_conj {J A : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (a : A)
    (haJ : (a : G) ∈ J) :
    Step1910Proof.quotAct hAJ a =
      MulAut.conj (((⟨a, haJ⟩ : J) : J ⧸ CFSG.pCore 2 J)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H k =>
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hAJ a k
    rw [hact, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [hj']
    simp

theorem exists_commute_of_quotAct_fixed {J A : Subgroup G}
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (a : A) (ha3 : (a : G) ^ 3 = 1) (x : J)
    (hx : Step1910Proof.quotAct hAJ a (x : J ⧸ CFSG.pCore 2 J) = x) :
    ∃ y : J, (x : J ⧸ CFSG.pCore 2 J) = y ∧ (a : G) * y = y * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := CFSG.Open.pCoreOf 2 J with hNdef
  have hN3 : ¬ 3 ∣ Nat.card N := by
    rw [hNdef, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective J.subtype_injective]
    exact Step1919EndProof.not_three_dvd_card_pCore J
  have haN : (a : G) ∈ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) J (hAJ a.2)
  set B : Subgroup G := Subgroup.zpowers (a : G) with hB
  have hB3 : IsPGroup 3 B := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((a : G) ^ n) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      ha3, _root_.one_zpow]
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr haN
  set S : Subgroup G := {
    carrier := {b | b ∈ Subgroup.normalizer (N : Set G) ∧ (x : G)⁻¹ * (b * x * b⁻¹) ∈ N}
    mul_mem' := by
      rintro b b' ⟨hb, hbx⟩ ⟨hb', hb'x⟩
      refine ⟨mul_mem hb hb', ?_⟩
      have h1 : b * ((x : G)⁻¹ * (b' * x * b'⁻¹)) * b⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp hb _).mp hb'x
      have h2 := N.mul_mem hbx h1
      rwa [show (x : G)⁻¹ * (b * x * b⁻¹) * (b * ((x : G)⁻¹ * (b' * x * b'⁻¹)) * b⁻¹) =
        (x : G)⁻¹ * (b * b' * x * (b * b')⁻¹) by group] at h2
    one_mem' := ⟨one_mem _, by simp⟩
    inv_mem' := by
      rintro b ⟨hb, hbx⟩
      refine ⟨inv_mem hb, ?_⟩
      have h1 : b⁻¹ * ((x : G)⁻¹ * (b * x * b⁻¹))⁻¹ * b ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) _).mp (N.inv_mem hbx)
        simpa using this
      rwa [show b⁻¹ * ((x : G)⁻¹ * (b * x * b⁻¹))⁻¹ * b = (x : G)⁻¹ * (b⁻¹ * x * b⁻¹⁻¹) by
        group] at h1 } with hS
  have haS : (a : G) ∈ S := by
    refine ⟨haN, ?_⟩
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hAJ a x
    rw [hx] at hact
    have h1 : (x : J)⁻¹ * j' ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp hact
    rw [Step1911EndProof.mem_pCore_iff] at h1
    simpa [hj'] using h1
  obtain ⟨y, hy, hyB⟩ := Step199Proof.exists_fixed_mem_coset hB3 hN3 hBN (k := (x : G))
    (fun b hb => ((Subgroup.zpowers_le.mpr haS) hb).2)
  have hyJ : y ∈ J := by
    have h1 : (x : G)⁻¹ * y ∈ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J hy
    have h2 := J.mul_mem x.2 h1
    simpa using h2
  refine ⟨⟨y, hyJ⟩, ?_, hyB _ (Subgroup.mem_zpowers _)⟩
  apply QuotientGroup.eq.mpr
  rw [Step1911EndProof.mem_pCore_iff]
  simpa using hy

theorem step1919CoreSplitLieRest_of (hK : KS1919SplitAut) : Step1919CoreSplitLieRest := by
  intro G _ _ A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ hlist
    hEJF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE
      (hctx.mem_partTwoE.1.2 c (hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)))
      hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hJM : J ∈ oTwoComponentsIn M := hJ.1
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) := hEN J hJ
  set ρ := Step1910Proof.quotAct hEJ with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra he1
    obtain ⟨k, hk, hkn⟩ := hfaith e e.2 (fun h => he1 (Subtype.ext h))
    apply hkn
    obtain ⟨j', hj', hact⟩ := Step1910Proof.quotAct_mk hEJ e ⟨k, hk⟩
    rw [← hρ, he, MulAut.one_apply] at hact
    have h1 : (⟨k, hk⟩ : J)⁻¹ * j' ∈ CFSG.pCore 2 J := QuotientGroup.eq.mp hact
    rw [Step1911EndProof.mem_pCore_iff] at h1
    have h2 : k⁻¹ * ((e : G) * k * (e : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 J := by
      simpa [hj'] using h1
    have h3 : (e : G) * k * (e : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 J := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J hk) _).mp h2
      rwa [show k * (k⁻¹ * ((e : G) * k * (e : G)⁻¹)) * k⁻¹ =
        (e : G) * k * (e : G)⁻¹ * k⁻¹ by group] at this
    exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM h3
  have hEstar : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc x x.2 y y.2)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by simpa using hEe x x.2)
      rw [this, map_one]
  have hEstar27 : Nat.card ρ.range = 27 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρinj, Subgroup.card_top, hE.2]
  set F := E ⊓ L with hFdef
  have hFJ : F ≤ J := by
    rw [← hEJF]
    exact inf_le_right
  set Fstar := ((F.subgroupOf E)).map ρ with hFstar
  have hFle : Fstar ≤ ρ.range := Subgroup.map_le_range ρ _
  have hFinn : Fstar ≤ (MulAut.conj : (J ⧸ CFSG.pCore 2 J) →* MulAut _).range := by
    rintro _ ⟨f, hf, rfl⟩
    have hfJ : (f : G) ∈ J := hFJ (Subgroup.mem_subgroupOf.mp hf)
    exact ⟨_, (quotAct_eq_conj hEJ f hfJ).symm⟩
  have hF9 : Nat.card Fstar = 9 := by
    rw [hFstar, Subgroup.card_map_of_injective hρinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h9]
  have hcstar : ρ ⟨c, hcE⟩ ∉ Fstar := by
    rintro ⟨f, hf, hfc⟩
    have : f = ⟨c, hcE⟩ := hρinj hfc
    apply hcL
    have hfL := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hf)).2
    rw [this] at hfL
    exact hfL
  have hc3 : c ^ 3 = 1 := hEe c hcE
  have hfix : ∀ y : J ⧸ CFSG.pCore 2 J, ρ ⟨c, hcE⟩ y = y → y ∈ starIm J H := by
    intro y hy
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨z, hz, hzc⟩ := exists_commute_of_quotAct_fixed hEJ ⟨c, hcE⟩ hc3 x hy
      rw [hz]
      refine ⟨z, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (hH.2 (Subgroup.mem_centralizer_singleton_iff.mpr hzc.symm))
  exact hK (J ⧸ CFSG.pCore 2 J) hlist ρ.range hEstar hEstar27 Fstar hFle hFinn hF9
    (ρ ⟨c, hcE⟩) ⟨_, rfl⟩ hcstar (starIm J H) hpp hfix

end Item19ResProof

end CFSG.RankThree.PartTwo.Sec19
