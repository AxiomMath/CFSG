module

public import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofCyc
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofCyclic
import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKS
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec21.Item22L2
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail24

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def SchreierCycThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    CFSG.Assembly.InCatalog X → (∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) →
      Group.IsSolvable (Outer X)

theorem schreierCycThree_of_schreierFor (h : SchreierFor CFSG.Assembly.InCatalog) :
    SchreierCycThree :=
  fun X _ _ _ hab hcat _ => h X hab hcat

namespace Res6Cyc

section Burnside

variable {X : Type*} [Group X] [Finite X]

theorem mem_zpowers_of_commute (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x y : X}
    (hx : orderOf x = 3) (hy : y ^ 3 = 1) (hxy : x * y = y * x) : y ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  have hyo : orderOf y = 3 := orderOf_eq_prime hy hy1
  have hxP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (show Commute x y from hxy) k)).eq
  obtain ⟨S, hS⟩ := (IsPGroup.to_sup_of_normal_left' hxP hyP hyN).exists_le_sylow
  have hcS := hcyc S
  have h1 : Subgroup.zpowers x ≤ (S : Subgroup X) := le_sup_left.trans hS
  have h2 : Subgroup.zpowers y ≤ (S : Subgroup X) := le_sup_right.trans hS
  have heq : (Subgroup.zpowers y).subgroupOf (S : Subgroup X) =
      (Subgroup.zpowers x).subgroupOf (S : Subgroup X) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, hyo, hx]
  rw [Subgroup.subgroupOf_inj, inf_of_le_left h2, inf_of_le_left h1] at heq
  rw [← heq]
  exact Subgroup.mem_zpowers y

theorem not_three_dvd_card_of_le_centralizer
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x : X} (hx : orderOf x = 3)
    {Q : Subgroup X} (hQp : Group.IsPerfect ↥Q) (hQx : Q ≤ Subgroup.centralizer {x}) :
    ¬ 3 ∣ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  have hmem : ∀ y ∈ Q, y ^ 3 = 1 → y ∈ Subgroup.zpowers x := fun y hy hy3 =>
    mem_zpowers_of_commute hcyc hx hy3 (Subgroup.mem_centralizer_singleton_iff.mp (hQx hy)).symm
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 3 h3
  have hq' : orderOf (q : X) = 3 := by rw [Subgroup.orderOf_coe, hq]
  have hqx : (q : X) ∈ Subgroup.zpowers x := by
    refine hmem q q.2 ?_
    rw [← hq']
    exact pow_orderOf_eq_one _
  have hzq : Subgroup.zpowers (q : X) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hqx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hq'])
  have hxQ : x ∈ Q := by
    have hx' : x ∈ Subgroup.zpowers (q : X) := hzq ▸ Subgroup.mem_zpowers x
    exact (Subgroup.zpowers_le.mpr q.2) hx'
  have hcent : ∀ y : ↥Q, y ^ 3 = 1 → y ∈ Subgroup.center ↥Q := by
    intro y hy3
    have hyx : (y : X) ∈ Subgroup.zpowers x :=
      hmem y y.2 (by simpa using congrArg Subtype.val hy3)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hk]
    have hzx : Commute (z : X) x := Subgroup.mem_centralizer_singleton_iff.mp (hQx z.2)
    exact (hzx.zpow_right k).eq
  have hcard : Nat.card {y : ↥Q // y ^ 3 = 1} ≤ 3 := by
    let f : {y : ↥Q // y ^ 3 = 1} → Subgroup.zpowers x := fun y =>
      ⟨(y.1 : X), hmem y.1 y.1.2 (by simpa using congrArg Subtype.val y.2)⟩
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hab
    have h := Nat.card_le_card_of_injective f hinj
    rwa [Nat.card_zpowers, hx] at h
  obtain ⟨N, hN, hN3, hQN⟩ :=
    SuzukiSectionProof.exists_normal_complement (p := 3) (X := ↥Q) (by norm_num) hcent hcard
  have := hQp
  have : Group.IsNilpotent (↥Q ⧸ N) := hQN.isNilpotent
  have hsub : Subsingleton (↥Q ⧸ N) :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact (QuotientGroup.eq_one_iff y).mp (Subsingleton.elim _ _)
  rw [hNtop, Subgroup.card_top] at hN3
  exact hN3 h3

omit [Finite X] in
theorem comap_facts [Group.IsSolvable (Outer X)] (hZ : Subgroup.center X = ⊥)
    {x : X} {Q : Subgroup (MulAut X)} (hQp : Group.IsPerfect ↥Q) (hQx : ∀ σ ∈ Q, σ x = x) :
    Subgroup.map (MulAut.conj : X →* MulAut X) (Q.comap MulAut.conj) = Q ∧
      Nat.card (Q.comap (MulAut.conj : X →* MulAut X)) = Nat.card Q ∧
      Group.IsPerfect ↥(Q.comap (MulAut.conj : X →* MulAut X)) ∧
      Q.comap (MulAut.conj : X →* MulAut X) ≤ Subgroup.centralizer {x} := by
  have := hQp
  have hinner : Q ≤ (MulAut.conj : X →* MulAut X).range := by
    intro σ hσ
    obtain ⟨g, hg⟩ :=
      CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner Q.subtype ⟨σ, hσ⟩
    exact ⟨g, hg.symm⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
    have hac : a ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun σ : MulAut X => σ z) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc z * a = a * z * a⁻¹ * a := by rw [h1]
        _ = a * z := by group
    rw [hZ] at hac
    exact Subgroup.mem_bot.mp hac
  have hmap := Subgroup.map_comap_eq_self hinner
  refine ⟨hmap, ?_, ?_, ?_⟩
  · conv_rhs => rw [← hmap]
    rw [Subgroup.card_map_of_injective hinj]
  · rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmap, Subgroup.commutator_eq_self]
  · intro g hg
    have h1 : (MulAut.conj g) x = x := hQx _ hg
    rw [MulAut.conj_apply] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h1]

theorem not_three_dvd_card_of_fix [Group.IsSolvable (Outer X)] (hZ : Subgroup.center X = ⊥)
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x : X} (hx : orderOf x = 3)
    {Q : Subgroup (MulAut X)} (hQp : Group.IsPerfect ↥Q) (hQx : ∀ σ ∈ Q, σ x = x) :
    ¬ 3 ∣ Nat.card Q := by
  obtain ⟨-, hcard, hp, hle⟩ := comap_facts hZ hQp hQx
  rw [← hcard]
  exact not_three_dvd_card_of_le_centralizer hcyc hx hp hle

end Burnside

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hab
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem eq_bot_of_zpowers_eq_top {X : Type*} [Group X] {x : X}
    (hzx : Subgroup.zpowers x = ⊤) {Q : Subgroup (MulAut X)} (hQx : ∀ σ ∈ Q, σ x = x) :
    Q = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext y
  have hy : y ∈ Subgroup.zpowers x := hzx ▸ Subgroup.mem_top y
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [MulAut.one_apply, map_zpow, hQx σ hσ]

theorem eq_bot_of_schreierCycThree (hS : SchreierCycThree) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) (hO3 : CFSG.pPrimeCore 3 X = ⊥)
    (hcyc : ∀ S : Sylow 3 X, IsCyclic ↥(S : Subgroup X)) {x : X} (hx : orderOf x = 3)
    (hnc : Subgroup.normalClosure ({x} : Set X) = ⊤) {Q : Subgroup (MulAut X)}
    (hQp : Group.IsPerfect ↥Q) (hQx : ∀ σ ∈ Q, σ x = x) (h3 : ¬ 3 ∣ Nat.card Q → Q = ⊥) :
    Q = ⊥ := by
  have hsimp := KS1624CycProof.isSimpleGroup_of hO3 hcyc hx hnc
  by_cases hab : ∃ a b : X, a * b ≠ b * a
  · have hcat : CFSG.Assembly.InCatalog X :=
      CFSG.ComponentClassification.CatalogueKProper.simple_quotient_of_isKGroup hK ⊤ X
        (Subgroup.topEquiv (G := X)).toMonoidHom (Subgroup.topEquiv (G := X)).surjective
    have := hS X hab hcat hcyc
    exact h3 (not_three_dvd_card_of_fix (center_eq_bot_of_simple hab) hcyc hx hQp hQx)
  · have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
      by_contra hne
      exact hab ⟨a, b, hne⟩
    have hnorm : (Subgroup.zpowers x).Normal :=
      ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
    have hzx : Subgroup.zpowers x = ⊤ := by
      rw [eq_top_iff, ← hnc]
      exact Subgroup.normalClosure_le_normal
        (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x))
    exact eq_bot_of_zpowers_eq_top hzx hQx

theorem three_dvd_mul_sq_sub_one (n : ℕ) : 3 ∣ n * (n ^ 2 - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : n ^ 2 - 1 = (n - 1) * (n + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left]
    ring_nf
    omega
  rw [h1]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h0 | h0
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h0) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _

theorem range_eq_bot_of_not_three_dvd {K H : Type*} [Group K] [Group H] [Finite K]
    (hK : Group.IsPerfect K) {V : Subgroup K} [V.Normal]
    (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hS : IsSimpleGroup (K ⧸ V))
    (h3 : 3 ∣ Nat.card (K ⧸ V)) (f : K →* H) (hf : ¬ 3 ∣ Nat.card f.range) : f.range = ⊥ := by
  have hNn : (f.ker.map (QuotientGroup.mk' V)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective V)
  have := hS
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map (QuotientGroup.mk' V)) with
    hbot | htop
  ·
    have hNV : f.ker ≤ V := by
      intro n hn
      have h1 : QuotientGroup.mk' V n ∈ f.ker.map (QuotientGroup.mk' V) :=
        Subgroup.mem_map_of_mem _ hn
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exfalso
    apply hf
    have h1 : Nat.card f.range = f.ker.index := by
      rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    rw [h1]
    exact h3.trans (Subgroup.index_dvd_of_le hNV)
  ·
    have hcov : ∀ k : K, ∃ v ∈ V, f k = f v := by
      intro k
      have hk : QuotientGroup.mk' V k ∈ f.ker.map (QuotientGroup.mk' V) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      refine ⟨n⁻¹ * k, ?_, ?_⟩
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
        exact hnk
      · rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    have hcomm : ⁅f.range, f.range⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨k, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k', rfl⟩
      obtain ⟨v, hv, hkv⟩ := hcov k
      obtain ⟨v', hv', hkv'⟩ := hcov k'
      rw [hkv, hkv', ← map_mul, ← map_mul, hV v' hv' v hv]
    have := hK
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    rw [← Subgroup.commutator_eq_self (H := f.range), hcomm]

end Res6Cyc

open Res6Cyc Proof1624KD CFSG.RankThree.PartTwo.Sec15

theorem step1624KDThree_of_schreier (hS : SchreierCycThree) : Step1624KDThree := by
  intro G _ _ A c L h b n p P hD m V X hVX M hM hKM hcM hcyc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kPara1623 L V with hKdef
  set D := normalClosureSub M (Subgroup.zpowers c) with hDdef
  obtain ⟨hcD', hDM, hMD⟩ := Proof169.normalClosureSub_spec (Subgroup.zpowers_le.mpr hcM)
  have hcD : c ∈ D := hcD' (Subgroup.mem_zpowers c)
  have hMtop : M ≠ ⊤ := by
    obtain ⟨R, hR1, hR2, hMR⟩ := hM.1
    rw [hMR]
    exact Sec14.normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hR1 hR2
  have hDtop : D ≠ ⊤ := fun hD' => hMtop (top_le_iff.mp (hD' ▸ hDM))
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := hKM.trans hMD
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) :=
    ((Subgroup.map_subtype_le _).trans inf_le_left).trans h.le_centralizer
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  set O := CFSG.pPrimeCore 3 ↥D with hO
  set x : ↥D ⧸ O := ((⟨c, hcD⟩ : D) : ↥D ⧸ O) with hx
  have hKG : IsKGroup (↥D ⧸ O) :=
    CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient
      (h.toTheoremFourHyp.sectionFourHyp hDtop).kGroup O
  have hx3 : orderOf x = 3 := orderOf_mk_eq_three (d := ⟨c, hcD⟩) (by
    rw [Subgroup.orderOf_mk, h.orderOf_eq])
  have hcycX := isCyclic_sylow_quot hcyc
  have hncl := normalClosure_eq_top hcM h.orderOf_eq hcD hcycX
  set ψ : ↥K →* MulAut (↥D ⧸ O) :=
    (quotMulAut ↥D).comp (D.normalizerMonoidHom.comp (Subgroup.inclusion hKD)) with hψ
  have hψapp : ∀ (k : ↥K) (d : ↥D), ψ k (d : ↥D ⧸ O) =
      ((⟨(k : G) * d * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKD k.2) d).mp d.2⟩ : D) :
        ↥D ⧸ O) := fun k d => rfl
  have hperf : Group.IsPerfect ↥ψ.range := by
    have := hKperf
    exact Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hfix : ∀ σ ∈ ψ.range, σ x = x := by
    rintro _ ⟨k, rfl⟩
    rw [hx, hψapp]
    congr 2
    show (k : G) * c * (k : G)⁻¹ = c
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hKc k.2), mul_inv_cancel_right]
  have h3 : ¬ 3 ∣ Nat.card ψ.range → ψ.range = ⊥ := by
    intro hnd
    obtain ⟨hVn, ⟨e⟩⟩ := hVX.quot
    set F := GaloisField 2 m with hF
    have hF4 : 4 ≤ Nat.card F := Proof1624KS.four_le_card_galoisField hD.prime hD.three_lt hVX
    have hsimp : IsSimpleGroup (↥K ⧸ V.subgroupOf K) := by
      have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
      exact (e.trans (Sec4.projSLEquivPSL F)).isSimpleGroup
    have hQc : Nat.card (↥K ⧸ V.subgroupOf K) = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr (e.trans (Sec21.projSLTwoEquivSL F)).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hVab : ∀ a ∈ V.subgroupOf K, ∀ b ∈ V.subgroupOf K, a * b = b * a := by
      intro a ha b hb
      rw [Subgroup.mem_subgroupOf] at ha hb
      apply Subtype.ext
      have := isMulCommutative_iff.mp hVX.elem.1 ⟨(a : G), ha⟩ ⟨(b : G), hb⟩
      simpa using congrArg Subtype.val this
    exact range_eq_bot_of_not_three_dvd hKperf hVab hsimp
      (hQc ▸ three_dvd_mul_sq_sub_one _) ψ hnd
  have hbot := eq_bot_of_schreierCycThree hS hKG (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
    hcycX hx3 hncl hperf hfix h3
  rw [Subgroup.commutator_le]
  intro k hk d hd
  have h1 : ψ ⟨k, hk⟩ = 1 := by
    have : ψ ⟨k, hk⟩ ∈ ψ.range := ⟨⟨k, hk⟩, rfl⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have h2 := hψapp ⟨k, hk⟩ ⟨d, hd⟩
  rw [h1, MulAut.one_apply] at h2
  have h3 := (QuotientGroup.eq_iff_div_mem).mp h2.symm
  refine ⟨_, h3, ?_⟩
  simp [commutatorElement_def, div_eq_mul_inv]

end CFSG.RankThree.PartTwo.Sec16
