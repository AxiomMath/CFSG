module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofYd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace HJRes2

omit [Finite G] in
theorem isPGroup_three_of_coprime {X : Type*} [Group X] [Finite X]
    (h : ∀ x : X, ∀ k : ℕ, x ^ k = 1 → k.Coprime 3 → x = 1) : IsPGroup 3 X := by
  intro x
  have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨e, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  refine ⟨e, h _ m ?_ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm⟩
  rw [← pow_mul, ← hm, pow_orderOf_eq_one]

theorem forall_mem_theta_of_isTripleCover {K H : Subgroup G} {b : G} (hb3 : b ^ 3 = 1)
    (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K))
    (hA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)))
    (hHK : H ≤ K) (hHp : Group.IsPerfect H) (h3H : 3 ∣ Nat.card H)
    (hbH : ∀ y ∈ H, b * y = y * b) :
    ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥K with hθ
  set σ := GroupTheory.thetaQuotientConj 3 K ⟨b, hbK⟩ with hσ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have e : (⟨b, hbK⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [e, map_one]
  have hσ1 : σ = 1 := by
    by_contra hσ1
    have hTp : Group.IsPerfect (↥K ⧸ θ) := hKq.1
    obtain ⟨hZ, ⟨e⟩⟩ := hA6
    set ι : ↥H →* ↥K ⧸ θ := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hHK) with hι
    have hfix : ∀ y : ↥H, σ (ι y) = ι y := by
      intro y
      rw [hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hσ, GroupTheory.thetaQuotientConj_mk]
      congr 1
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      change b * (y : G) * b⁻¹ = y
      rw [hbH y y.2, mul_inv_cancel_right]
    have hp : IsPGroup 3 ι.range := by
      refine isPGroup_three_of_coprime fun t k htk hk3 => ?_
      obtain ⟨y, hy⟩ := t.2
      have h1 : ι y = 1 := by
        refine Item148PtRes.eq_one_of_fixed_tripleCover hZ e hσ3 hσ1 (hfix y) (k := k) ?_ hk3
        rw [hy]
        exact congrArg Subtype.val htk
      exact Subtype.ext (hy.symm.trans h1)
    have hrp : Group.IsPerfect ι.range :=
      Group.IsPerfect.ofSurjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
    have hsol : Group.IsSolvable ι.range := by
      have := hp.isNilpotent
      infer_instance
    have hsub : Subsingleton ι.range := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable ι.range hsol
    have hker : ι.ker = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have := Subsingleton.elim (⟨ι y, y, rfl⟩ : ι.range) 1
      exact congrArg Subtype.val this
    apply hθ3
    refine h3H.trans ?_
    have hle : (⊤ : Subgroup ↥H).map (Subgroup.inclusion hHK) ≤ θ := by
      rintro _ ⟨y, -, rfl⟩
      have hy' : y ∈ ι.ker := hker ▸ Subgroup.mem_top y
      have hy : ι y = 1 := MonoidHom.mem_ker.mp hy'
      rw [hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      exact hy
    rw [← Subgroup.card_top (G := ↥H), ← Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective hHK)]
    exact Subgroup.card_dvd_of_le hle
  intro y hy
  exact (GroupTheory.thetaQuotientConj_eq_one_iff 3 K ⟨b, hbK⟩).mp hσ1 y hy

theorem isTripleCover_yb_of_isTripleCover {Y B YB Yd : Subgroup G} {b d : G} (hbB : b ∈ B)
    (hb3 : b ^ 3 = 1) (hCB : Subgroup.centralizer (B : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G))
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hbYd : b ∈ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∧
      ∀ y ∈ Yd, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Yd := by
  have h3YB : 3 ∣ Nat.card YB := by
    rcases htype with hA6' | hA5
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6'))
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inl hA5)
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hbH : ∀ y ∈ YB, b * y = y * b := by
    intro y hy
    have hyB : y ∈ Subgroup.centralizer (B : Set G) := (hYBC hy).2
    exact Subgroup.mem_centralizer_iff.mp hyB b hbB
  have hbc := forall_mem_theta_of_isTripleCover hb3 hbYd
    (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd) hA6 hYBYd
    (isPerfect_of_mem_thetaComponentsIn hYB) h3YB hbH
  obtain ⟨η⟩ := HJRes148.nonempty_theta_quot_equiv_of_mem_sectionCentralizer hb3 hCB hYB h3YB hYd
    hYBYd hbYd hbc
  refine ⟨?_, hbc⟩
  rcases htype with hA6' | ⟨⟨φ⟩⟩
  · exact hA6'
  · exfalso
    have h1 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 1080 := by
      obtain ⟨hc, ⟨e⟩⟩ := hA6
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)), Nat.card_congr e.toEquiv, hc,
        KFacts.KS14.card_alternatingGroup_six]
    have h2 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 60 := by
      rw [← Nat.card_congr η.toEquiv, Nat.card_congr φ.toEquiv]
      exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    omega

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {d : G} (hd3 : d ^ 3 = 1) {k : ℕ}
    (hk : k.Coprime 3) (hdk : d ^ k ∈ H) : d ∈ H := by
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := by
      intro h0
      have : 3 ∣ k := Nat.dvd_of_mod_eq_zero h0
      have h1 := Nat.Coprime.coprime_dvd_left this hk
      norm_num at h1
    omega
  have hdk' : d ^ k = d ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hd3, one_pow, one_mul]
  rw [hdk'] at hdk
  rcases hk3 with h1 | h2
  · rwa [h1, pow_one] at hdk
  · rw [h2] at hdk
    have hinv : d = (d ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ', hd3]
    rw [hinv]
    exact H.inv_mem hdk


theorem mem_yb_of_isTripleCover {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb) {Y YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (hA6 : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)))
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B) : d ∈ YB := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (B : Set G) with hCdef
  set N := pPrimeCoreOf 3 C with hNdef
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  rw [Item148HJ.lB_eq_residual h hB hc] at hle
  have hJC : J ≤ C := Item148HJ.residual_le_centralizer hc
  obtain ⟨hdL, -, -, -, -, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 C
  have hD := h.toSec13Data
  have hdB : d ∈ B := (Main148.lbConfig_points hB h.isE27.2 hc).2.1
  have hdA : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  have hdJ : d ∈ J := Item148HJ.inf_le_residual h hB hc ⟨hdA, hdL⟩
  have hYBC : YB ≤ C := (le_of_mem_thetaComponentsIn hYB).trans inf_le_right
  have hθN : ∀ x ∈ J, x ∈ inSubgroup (aschbacherSolvableCore 3) Lb → x ∈ N := by
    intro x hxJ hxθ
    have hS := Item148HJ.sec14Std_of_isLBConfig h hc
    have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
    have hCLb : C ≤ Subgroup.normalizer (Lb : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)).trans
        (centralizer_le_normalizer_of_j2 hS (Item148HJ.j2_of_isLBConfig hc))
    have hθn : C ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore 3) Lb : Subgroup G) : Set G) :=
      hCLb.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        Lb _ (solvable_prime_complement_core_characterization Nat.prime_three).2.1)
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
    have hle' : inSubgroup (aschbacherSolvableCore 3) Lb ⊓ C ≤ N :=
      le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hθn Subgroup.le_normalizer)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hθ3 (h3.trans (by
          refine (Subgroup.card_dvd_of_le inf_le_left).trans ?_
          rw [inSubgroup, Subgroup.card_map_of_injective Lb.subtype_injective])))
    exact hle' ⟨hxθ, hJC hxJ⟩
  set N₀ := CFSG.pPrimeCore 3 ↥C with hN₀def
  set π := QuotientGroup.mk' N₀ with hπdef
  have hNsub : N.subgroupOf C = N₀ := by
    rw [hNdef, pPrimeCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  have hπN : ∀ x : ↥C, π x = 1 ↔ (x : G) ∈ N := by
    intro x
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hNsub,
      Subgroup.mem_subgroupOf]
  set ψ₁ : ↥J →* (↥C ⧸ N₀) := π.comp (Subgroup.inclusion hJC) with hψ₁
  have hker₁ : (Item148HJ.resProj Lb d).ker ≤ ψ₁.ker := by
    intro j hj
    rw [MonoidHom.mem_ker, hψ₁, MonoidHom.comp_apply, hπN]
    exact hθN j j.2 ((Item148HJ.mem_ker_resProj j).mp hj)
  have hcardR : Nat.card (Item148HJ.resProj Lb d).range = 1080 := by
    obtain ⟨hcz, ⟨e⟩⟩ := htc
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(Item148HJ.resProj Lb d).range), Nat.card_congr e.toEquiv, hcz,
      KFacts.KS14.card_alternatingGroup_six]
  have hcard₁ : Nat.card ψ₁.range ≤ 1080 := by
    have e1 : Nat.card ↥J = Nat.card ψ₁.range * Nat.card ψ₁.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ₁.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ₁).toEquiv]
    have e2 : Nat.card ↥J = Nat.card (Item148HJ.resProj Lb d).range *
        Nat.card (Item148HJ.resProj Lb d).ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Item148HJ.resProj Lb d).ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange (Item148HJ.resProj Lb d)).toEquiv]
    have hk : Nat.card (Item148HJ.resProj Lb d).ker ≤ Nat.card ψ₁.ker :=
      Subgroup.card_le_of_le hker₁
    have hpos : 0 < Nat.card ψ₁.ker := Nat.card_pos
    rw [← hcardR]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ψ₁.range * Nat.card ψ₁.ker
        = Nat.card (Item148HJ.resProj Lb d).range * Nat.card (Item148HJ.resProj Lb d).ker := by
          rw [← e1, ← e2]
      _ ≤ Nat.card (Item148HJ.resProj Lb d).range * Nat.card ψ₁.ker :=
          Nat.mul_le_mul_left _ hk
  set ψ : ↥YB →* (↥C ⧸ N₀) := π.comp (Subgroup.inclusion hYBC) with hψ
  have hψker : ∀ y : ↥YB, y ∈ ψ.ker ↔ (y : G) ∈ N := by
    intro y
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, hπN]
    rfl
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    intro h3
    have hle' : ψ.ker.map YB.subtype ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hψker y).mp hy
    have h3' : 3 ∣ Nat.card N := by
      refine h3.trans ?_
      rw [← Subgroup.card_map_of_injective YB.subtype_injective]
      exact Subgroup.card_dvd_of_le hle'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 h3'
  have hcardYB : Nat.card (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) = 1080 := by
    obtain ⟨hcz, ⟨e⟩⟩ := hA6
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB)), Nat.card_congr e.toEquiv, hcz,
      KFacts.KS14.card_alternatingGroup_six]
  have hcardψ : 1080 ≤ Nat.card ψ.range := by
    have hYBq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB
    have hYBp : Group.IsPerfect YB := isPerfect_of_mem_thetaComponentsIn hYB
    have hrp : Group.IsPerfect ψ.range :=
      Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    have hker' : ψ.rangeRestrict.ker = ψ.ker := MonoidHom.ker_rangeRestrict ψ
    rcases Res148.ker_le_theta_or_subsingleton ψ.rangeRestrict ψ.rangeRestrict_surjective hrp
        hYBq (by rw [hker']; exact hker3) with hle' | hsub
    · rw [hker'] at hle'
      have e1 : Nat.card ↥YB = Nat.card ψ.range * Nat.card ψ.ker := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      have e2 : Nat.card ↥YB = 1080 * Nat.card (aschbacherSolvableCore 3 ↥YB) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
          hcardYB]
      have hk : Nat.card ψ.ker ≤ Nat.card (aschbacherSolvableCore 3 ↥YB) :=
        Subgroup.card_le_of_le hle'
      have hpos : 0 < Nat.card (aschbacherSolvableCore 3 ↥YB) := Nat.card_pos
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc 1080 * Nat.card (aschbacherSolvableCore 3 ↥YB) = Nat.card ψ.range * Nat.card ψ.ker := by
            rw [← e1, ← e2]
        _ ≤ Nat.card ψ.range * Nat.card (aschbacherSolvableCore 3 ↥YB) :=
            Nat.mul_le_mul_left _ hk
    · exfalso
      apply hker3
      have htop : ψ.ker = ⊤ := by
        rw [eq_top_iff]
        intro y _
        have := Subsingleton.elim (ψ.rangeRestrict y) 1
        exact congrArg Subtype.val this
      rw [htop, Subgroup.card_top]
      have h3 : 3 ∣ Nat.card (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) := by
        rw [hcardYB]; norm_num
      exact h3.trans (Subgroup.card_quotient_dvd_card _)
  have hle₁ : ψ.range ≤ ψ₁.range := by
    rintro _ ⟨y, rfl⟩
    have hyNJ : (y : G) ∈ N ⊔ J := hle y.2
    have hyC : (y : G) ∈ C := hYBC y.2
    have hNn : J ≤ Subgroup.normalizer (N : Set G) := hJC.trans hCN
    have hyNJ' : (y : G) ∈ ((N : Set G) * (J : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N J hNn]
      exact hyNJ
    obtain ⟨n, hn, j, hj, hnj⟩ := Set.mem_mul.mp hyNJ'
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [hψ₁, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : ((Subgroup.inclusion hJC ⟨j, hj⟩)⁻¹ * Subgroup.inclusion hYBC y : ↥C) =
        ⟨j⁻¹ * n * j, by
          have hnC : n ∈ C := pPrimeCoreOf_le 3 C hn
          exact C.mul_mem (C.mul_mem (C.inv_mem (hJC hj)) hnC) (hJC hj)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hnj]
      group
    rw [h1, ← hNsub, Subgroup.mem_subgroupOf]
    have hjN := hNn (J.inv_mem hj)
    have := (Subgroup.mem_normalizer_iff.mp hjN n).mp hn
    simpa [mul_assoc] using this
  have heq : ψ.range = ψ₁.range := Subgroup.eq_of_le_of_card_ge hle₁ (by omega)
  have hdψ : ψ₁ ⟨d, hdJ⟩ ∈ ψ.range := heq ▸ ⟨⟨d, hdJ⟩, rfl⟩
  obtain ⟨y, hy⟩ := hdψ
  rw [hψ₁, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, ← hNsub, Subgroup.mem_subgroupOf] at hy
  have hn : (y : G)⁻¹ * d ∈ N := by simpa using hy
  have hyd : Commute (y : G) d := by
    have hyB : (y : G) ∈ C := hYBC y.2
    exact (Subgroup.mem_centralizer_iff.mp hyB d hdB).symm
  set k := Nat.card N with hk
  have hpow : ((y : G)⁻¹ * d) ^ k = 1 := by
    have := pow_card_eq_one' (G := ↥N) (x := ⟨_, hn⟩)
    exact congrArg Subtype.val this
  rw [(hyd.inv_left).mul_pow, inv_pow, inv_mul_eq_one] at hpow
  have hdk : d ^ k ∈ YB := hpow ▸ pow_mem y.2 k
  exact mem_of_pow_mem_of_coprime hd3 hN3.symm hdk

end HJRes2

end CFSG.RankThree.PartTwo.Sec14
