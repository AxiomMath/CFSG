module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofX
public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2InvolNine
public import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof17Res3

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem j2_aut_eq_one_of_coprime
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup X}
    (hE : Nat.card E = 9) {σ : MulAut X} (hσ : Nat.Coprime 3 (orderOf σ))
    (hfix : ∀ e ∈ E, σ e = e) : σ = 1 := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hinn : σ ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
    obtain ⟨e⟩ := hX
    obtain ⟨f⟩ :=
      CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
    set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
    have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
    have h1 : φ ((σ ^ 2 : MulAut X) : Outer X) = 1 := by
      rw [QuotientGroup.mk_pow, map_pow, hsq]
    have h2 : ((σ ^ 2 : MulAut X) : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact (QuotientGroup.eq_one_iff _).mp h2
  obtain ⟨y, hy⟩ := hinn
  have hyC : y ∈ Subgroup.centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := congrArg (fun τ : MulAut X => τ e) hy
    simp only [MulAut.conj_apply] at h1
    rw [pow_two, MulAut.mul_apply, hfix e he, hfix e he] at h1
    calc e * y = (y * e * y⁻¹) * y := by rw [h1]
      _ = y * e := by group
  have hyE : y ∈ E := KFacts.ks17J2CentralizerNine X hX E hE hyC
  have hZ : Subgroup.center X = ⊥ := KFacts.KS14.center_eq_bot_of_j2 h415 hX
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (injective_iff_map_eq_one _).mpr fun z hz => ?_
    have hzc : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun τ : MulAut X => τ g) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * z = z * g * z⁻¹ * z := by rw [h1]
        _ = z * g := by group
    rw [hZ] at hzc
    exact hzc
  have hoy : orderOf y = orderOf (σ ^ 2) := by
    rw [← hy]
    exact (orderOf_injective _ hinj y).symm
  have hdvd9 : orderOf y ∣ 9 := hE ▸ Subgroup.orderOf_dvd_natCard E hyE
  have hcop : Nat.Coprime 3 (orderOf y) := by
    rw [hoy]
    exact hσ.coprime_dvd_right (orderOf_pow_dvd 2)
  have hy1 : y = 1 := by
    have h1 : orderOf y ∣ Nat.gcd 9 (orderOf y) := Nat.dvd_gcd hdvd9 dvd_rfl
    have h2 : Nat.gcd 9 (orderOf y) = 1 := by
      have : Nat.Coprime 9 (orderOf y) := by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
        exact Nat.Coprime.pow_left 2 hcop
      exact this
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hσ2 : σ ^ 2 = 1 := by rw [← hy, hy1, map_one]
  exact KFacts.ks152J2InvolNine X hX E hE σ hσ2 hfix

theorem mem_cQuot_of_j2
    {Y B : Subgroup G}
    (hY : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) (hBY : B ≤ Y)
    (hB : IsPGroup 3 B) (hB9 : Nat.card B = 9) {x : G}
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : Nat.Coprime 3 (orderOf x))
    (hxB : x ∈ Subgroup.centralizer (B : Set G)) : x ∈ cQuot Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set ψ : Subgroup.normalizer (Y : Set G) →* MulAut (↥Y ⧸ N) :=
    (mulAutQuotientHom N).comp Y.normalizerMonoidHom with hψ
  set σ := ψ ⟨x, hxN⟩ with hσ
  set Bb := (B.subgroupOf Y).map π with hBb
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hBb9 : Nat.card Bb = 9 := by
    rw [hBb, TailProof.card_map_of_isPGroup_three π hker (K := B.subgroupOf Y) hB.comap_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, hB9]
  have hfix : ∀ e ∈ Bb, σ e = e := by
    rintro _ ⟨b, hb, rfl⟩
    rw [hσ, hψ, mulAutQuotientHom_comp_apply]
    congr 1
    apply Subtype.ext
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hc := Subgroup.mem_centralizer_iff.mp hxB b hbB
    change x * (b : G) * x⁻¹ = b
    rw [← hc, mul_inv_cancel_right]
  have hσo : Nat.Coprime 3 (orderOf σ) := by
    have h1 : orderOf σ ∣ orderOf (⟨x, hxN⟩ : Subgroup.normalizer (Y : Set G)) :=
      orderOf_map_dvd ψ _
    rw [Subgroup.orderOf_mk] at h1
    exact hx3.coprime_dvd_right h1
  have hσ1 : σ = 1 := j2_aut_eq_one_of_coprime hY hBb9 hσo hfix
  rw [← SetLike.mem_coe, coe_cQuot]
  refine ⟨hxN, fun y hy => ?_⟩
  have h1 := congrArg (fun τ : MulAut (↥Y ⧸ N) => τ (π ⟨y, hy⟩)) hσ1
  simp only [MulAut.one_apply] at h1
  rw [hσ, hψ, mulAutQuotientHom_comp_apply] at h1
  have h2 := (Sec16.Step163Alt.mk_eq_mk_iff _ _).mp h1
  simp only at h2
  have hON : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have h3 := (Subgroup.mem_normalizer_iff.mp (hON hy) _).mp (inv_mem h2)
  have e : y * ((x * y * x⁻¹)⁻¹ * y)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
  rwa [e] at h3

end Proof17Res3

open Proof17Res3 in
theorem claim1722XThree_of_j2
    (h1721 : Item1721) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h166 : Item166S17) (h168 : Item168S17) (hbot : Item145BotS17) :
    Claim1722XThree := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have hA : IsE27 A := hs.isE27
  have hJ := h1721 G A c L Y₀ Y₁ S p P h
  obtain ⟨hJ2, h9, -, -, -, -⟩ := hs.j2_local hJ
  obtain ⟨hΩ, hY, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  obtain ⟨e⟩ := nonempty_quotient_pCore_two_equiv hs.le_y0 hY
  obtain ⟨f⟩ := hJ2
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨e.trans f⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set X := xA A with hXdef
  set B := A ⊓ L with hBdef
  set K := cQuot Y₀ with hKdef
  set N' := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hN'def
  obtain ⟨hSG, -, -, -⟩ := h.item168_at (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  have hSM : S ≤ M := hs.qStar_le S hSG
  have hSQ : S ∈ scriptQ A (lB A) := hSG.prop.1.1
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hSG.prop
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS2.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hBA : B ≤ A := inf_le_left
  have hBY : B ≤ Y₀ := inf_le_right.trans hs.le_y0
  have hB3 : IsPGroup 3 B := hA.isPGroup.to_le hBA
  have hB : IsHyperplane A B := ⟨hBA, by rw [hA.2, h9]⟩
  have hcL : c ∉ L := (Sec14.j2_point_facts hs.toSec13Data hJ).1
  have hLB : lB A B = ⊥ := lB_eq_bot fun b d L' hc => by
    obtain ⟨hBbd, hb, -⟩ := hc
    rw [hΩ, Set.mem_singleton_iff] at hb
    have hbB : b ∈ B := by
      rw [hBbd]
      exact Subgroup.subset_closure (Set.mem_insert b _)
    have hcB : c ∈ B := (Subgroup.zpowers_le.mpr hbB) (hb ▸ Subgroup.mem_zpowers c)
    exact hcL (Subgroup.mem_inf.mp hcB).2
  have hCS : S ⊓ Subgroup.centralizer (B : Set G) ≤ N' ⊔ X := by
    have h1 := hSQ.2 B hB
    rwa [qBound, hLB, sup_bot_eq] at h1
  have hXCA : X ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hXCB : X ≤ Subgroup.centralizer (B : Set G) := hXCA.trans (Subgroup.centralizer_le hBA)
  have hXN' : X ≤ Subgroup.normalizer (N' : Set G) :=
    hXCB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hX3 : ¬ 3 ∣ Nat.card X :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN'3 : ¬ 3 ∣ Nat.card N' :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hN'X3 : ¬ 3 ∣ Nat.card (N' ⊔ X : Subgroup G) := by
    rw [sup_comm]
    exact Sec6.not_dvd_card_sup Nat.prime_three hXN' hX3 hN'3
  have hXM : X ≤ M := hXCA.trans (HeadProof.centralizer_le_M hs)
  have hXK : X ≤ K := by
    intro x hx
    refine mem_cQuot_of_j2 hYJ hBY hB3 h9 (hXM hx) ?_ (hXCB hx)
    exact (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard X hx)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX3))
  have hCSK : S ⊓ Subgroup.centralizer (B : Set G) ≤ K := by
    intro s hs'
    refine mem_cQuot_of_j2 hYJ hBY hB3 h9 (hSM hs'.1) ?_ hs'.2
    exact (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard S hs'.1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS3))
  set U := (N' ⊔ X) ⊓ K with hUdef
  set O := CFSG.Open.pCoreOf 2 Y₀ with hOdef
  set T := (S ⊓ Y₀) ⊔ O with hTdef
  have hU3 : ¬ 3 ∣ Nat.card U := fun h3 => hN'X3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hOY : O ≤ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀
  have hYO : Y₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀
  have hT2 : IsPGroup 2 T :=
    IsPGroup.to_sup_of_normal_right' (hS2.to_le inf_le_left)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀) (inf_le_right.trans hYO)
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hTY : T ≤ Y₀ := sup_le inf_le_right hOY
  have hUT : U ≤ Subgroup.normalizer (T : Set G) := by
    intro u hu
    have huK : u ∈ (K : Set G) := hu.2
    rw [hKdef, coe_cQuot] at huK
    obtain ⟨-, hucomm⟩ := huK
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have h1 : u * t * u⁻¹ * t⁻¹ ∈ T := Subgroup.mem_sup_right (hucomm t (hTY ht))
    have e : u * t * u⁻¹ = (u * t * u⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact mul_mem h1 ht
  have hUT3 : ¬ 3 ∣ Nat.card (U ⊔ T : Subgroup G) :=
    Sec6.not_dvd_card_sup Nat.prime_three hUT hU3 hT3
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := hBA.trans hSQ.1.2.2
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three B S hB3 hS3 hBS
  have hcomm : ⁅S, B⁆ ≤ S ⊓ Y₀ := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hBS) ?_
    calc ⁅S, B⁆ ≤ ⁅S, Y₀⁆ := Subgroup.commutator_mono le_rfl hBY
      _ = ⁅Y₀, S⁆ := Subgroup.commutator_comm _ _
      _ ≤ Y₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hSM
  have hSle : S ≤ U ⊔ T := by
    rw [hfac]
    exact sup_le ((hcomm.trans le_sup_left).trans le_sup_right)
      ((le_inf hCS hCSK).trans le_sup_left)
  have hle : X ⊔ S ≤ U ⊔ T :=
    sup_le ((le_inf le_sup_right hXK).trans le_sup_left) hSle
  exact fun h3 => hUT3 (h3.trans (Subgroup.card_dvd_of_le hle))

end CFSG.RankThree.PartTwo.Sec17
