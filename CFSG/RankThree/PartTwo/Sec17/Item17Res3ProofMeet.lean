module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res2Proof1724
public import CFSG.RankThree.PartTwo.Sec17.Item1722ProofHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofJ2
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)
open scoped Pointwise

namespace Proof17Res3

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem j2_mem_range_conj_of_pow_eq_one'
    {X : Type} [Group X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : MulAut X} {k : ℕ} (hσ : σ ^ (p ^ k) = 1) :
    σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨e⟩ := hX
  obtain ⟨f⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  set φ : Outer X ≃* Multiplicative (ZMod 2) := (equivalence e).trans f
  have hsq : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
  have h1 : φ (σ : Outer X) = 1 := by
    have h3 : φ (σ : Outer X) ^ (p ^ k) = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one, map_one]
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one (hsq _))
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have h2 : (σ : Outer X) = 1 := φ.injective (h1.trans (map_one φ).symm)
  have h4 : σ ∈ inner X := (QuotientGroup.eq_one_iff σ).mp h2
  exact h4

omit [Finite G] in
theorem nonempty_quotient_pCore_two_equiv {L Y : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥L →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hφ
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN, ← hY]
      exact y.2
    obtain ⟨a, ha, b, hb, hab⟩ := hy
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Sec16.Step163Alt.mem_pCore_two_iff]
    have e : (((Subgroup.inclusion hLY ⟨a, ha⟩)⁻¹ * y : ↥Y) : G) = b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hab]
      group
    rw [e]
    exact hb
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm ?_ ?_
    · have hk : φ.ker = (CFSG.pCore 2 ↥Y).comap (Subgroup.inclusion hLY) := by
        ext x
        simp [hφ, QuotientGroup.eq_one_iff]
      refine le_sSup ⟨φ.normal_ker, ?_⟩
      rw [hk]
      exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hLY)
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hn : ((CFSG.pCore 2 ↥L).map φ).Normal := CFSG.pCore_normal.map φ hsurj
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L).map φ) := CFSG.pCore_isPGroup.map φ
      have hle : (CFSG.pCore 2 ↥L).map φ ≤ CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
        le_sSup ⟨hn, hp⟩
      rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
      exact (Subgroup.mem_bot).mp (hle ⟨x, hx, rfl⟩)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

omit [Finite G] in
theorem mulAutQuotientHom_comp_apply (Y : Subgroup G) (g : Subgroup.normalizer (Y : Set G))
    (y : ↥Y) :
    ((mulAutQuotientHom (CFSG.pCore 2 ↥Y)).comp Y.normalizerMonoidHom) g
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
        ⟨(g : G) * y * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2⟩ := by
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, mulAutQuotientHom_mk]
  rfl

theorem mk_conj_eq_of_j2
    {Y D B : Subgroup G}
    (hY : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hD : IsPGroup p D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hBY : B ≤ Y) (hB : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) (hBD : B ≤ Subgroup.normalizer (D : Set G)) {d : G} (hd : d ∈ D)
    (y : ↥Y) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
        ⟨d * y * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDY hd) y).mp y.2⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hp2 : p ≠ 2 := by omega
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set ψ : Subgroup.normalizer (Y : Set G) →* MulAut (↥Y ⧸ N) :=
    (mulAutQuotientHom N).comp Y.normalizerMonoidHom with hψ
  have hψapp : ∀ (g : Subgroup.normalizer (Y : Set G)) (z : ↥Y),
      ψ g (π z) = π ⟨(g : G) * z * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2 z).mp z.2⟩ :=
    fun g z => mulAutQuotientHom_comp_apply Y g z
  have hYN : Y ≤ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer
  have hψY : ∀ (b : G) (hb : b ∈ Y), ψ ⟨b, hYN hb⟩ = MulAut.conj (π ⟨b, hb⟩) := by
    intro b hb
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H z =>
      change ψ ⟨b, hYN hb⟩ (π z) = MulAut.conj (π ⟨b, hb⟩) (π z)
      rw [hψapp, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      rfl
  have hZ : Subgroup.center (↥Y ⧸ N) = ⊥ := KFacts.KS14.center_eq_bot_of_j2 h415 hY
  have hconj : ∀ z : ↥Y ⧸ N, MulAut.conj z = 1 → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center (↥Y ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ g) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * z = z * g * z⁻¹ * z := by rw [h1]
        _ = z * g := by group
    rw [hZ] at hzc
    exact hzc
  set D' := D.subgroupOf (Subgroup.normalizer (Y : Set G)) with hD'
  have hD'p : IsPGroup p D' := hD.comap_subtype
  set Dst := (D'.map ψ).comap (MulAut.conj : (↥Y ⧸ N) →* MulAut (↥Y ⧸ N)) with hDst
  have hDstp : IsPGroup p Dst := by
    rintro ⟨z, hz⟩
    obtain ⟨e, he, hez⟩ := hz
    obtain ⟨k, hk⟩ := hD'p ⟨e, he⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    apply hconj
    rw [map_pow, ← hez, ← map_pow, hek, map_one]
  set Bb := (B.subgroupOf Y).map π with hBb
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hBb9 : Nat.card Bb = 9 := by
    rw [hBb, TailProof.card_map_of_isPGroup_three π hker (K := B.subgroupOf Y) hB.comap_subtype,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, hB9]
  have hBbN : Bb ≤ Subgroup.normalizer (Dst : Set (↥Y ⧸ N)) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨e, he, hez⟩ := hz
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    set b' : Subgroup.normalizer (Y : Set G) := ⟨b, hYN b.2⟩ with hb'
    have hψb : ψ b' = MulAut.conj (π b) := hψY b b.2
    refine ⟨b' * e * b'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have he' : ((e : Subgroup.normalizer (Y : Set G)) : G) ∈ D := Subgroup.mem_subgroupOf.mp he
      simpa [hb'] using (Subgroup.mem_normalizer_iff.mp (hBD hbB) e).mp he'
    · rw [map_mul, map_mul, map_inv, hez, hψb, ← map_inv, ← map_mul, ← map_mul]
  have hDst1 : Dst = ⊥ :=
    j2_eq_bot_of_le_normalizer h415 hY hBb9 hp hp3 hDstp hBbN
  set d' : Subgroup.normalizer (Y : Set G) := ⟨d, hDY hd⟩ with hd'
  have hd'D : d' ∈ D' := by
    rw [hD', Subgroup.mem_subgroupOf]
    exact hd
  obtain ⟨k, hk⟩ := hD'p ⟨d', hd'D⟩
  have hdk : d' ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hψk : ψ d' ^ (p ^ k) = 1 := by rw [← map_pow, hdk, map_one]
  obtain ⟨z, hz⟩ := j2_mem_range_conj_of_pow_eq_one' hY hp hp2 hψk
  have hzD : z ∈ Dst := ⟨d', hd'D, hz.symm⟩
  rw [hDst1, Subgroup.mem_bot] at hzD
  have hψ1 : ψ d' = 1 := by rw [← hz, hzD, map_one]
  have h1 := congrArg (fun σ : MulAut (↥Y ⧸ N) => σ (π y)) hψ1
  simp only [MulAut.one_apply] at h1
  rw [hψapp] at h1
  exact h1

theorem eq_sup_of_mk_conj_eq {Y D : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : IsPGroup p D) (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (htriv : ∀ d (hd : d ∈ D) (y : ↥Y), QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
        ⟨d * y * d⁻¹, (Subgroup.mem_normalizer_iff.mp (hDY hd) y).mp y.2⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) :
    Y = (Y ⊓ Subgroup.centralizer (D : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun y hy => ?_)
    (sup_le inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  have hker : ¬ p ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨y', hy'C, hy'⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action
    p hp D Y hD hDY (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) hker
    (fun member element => htriv member member.2 element) ⟨y, hy⟩
  have hO : (y' : G)⁻¹ * y ∈ CFSG.Open.pCoreOf 2 Y :=
    (Sec16.Step163Alt.mk_eq_mk_iff y' ⟨y, hy⟩).mp hy'
  have e : y = (y' : G) * ((y' : G)⁻¹ * y) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left ⟨y'.2, hy'C⟩) (Subgroup.mem_sup_right hO)

end Proof17Res3

open Proof17Res3 in
theorem claim1724DeltaMeet_of
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) : Claim1724DeltaMeet := by
  intro G _ _ A c L Y₀ Y₁ S p P w Q h hJ
  have hs := h.toSec17Std
  obtain ⟨hJ2, h9, -, -, -, -⟩ := hs.j2_local hJ
  obtain ⟨-, hY, -⟩ := rank3II_17_15_HJ_of hs (h1514 G A c L Y₀ hs) (hMeets G A c L Y₀ hs) hJ
  obtain ⟨e⟩ := nonempty_quotient_pCore_two_equiv hs.le_y0 hY
  obtain ⟨f⟩ := hJ2
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨e.trans f⟩
  have hQp : IsPGroup p Q := isPGroup_of_mem_scriptQPi h.p_prime h.mem_qStar_G.prop
  have hDp : IsPGroup p (Q ⊓ Subgroup.normalizer (Y₀ : Set G) : Subgroup G) :=
    hQp.to_le inf_le_left
  have hAM : A ≤ Subgroup.normalizer
      ((Subgroup.normalizer (Y₀ : Set G) : Subgroup G) : Set G) :=
    hs.le_normalizer_y0.trans Subgroup.le_normalizer
  have hAD : A ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.normalizer (Y₀ : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf h.mem_qStar_G.prop.1.1.1.2.2 hAM
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hs.isE27.isPGroup.to_le inf_le_left
  have hp2 : p ≠ 2 := by
    have := h.three_lt_p
    omega
  exact eq_sup_of_mk_conj_eq h.p_prime hp2 hDp inf_le_right fun d hd y =>
    mk_conj_eq_of_j2 hYJ h.p_prime h.three_lt_p hDp inf_le_right
      (inf_le_right.trans hs.le_y0) hB3 h9 (inf_le_left.trans hAD) hd y

end CFSG.RankThree.PartTwo.Sec17
