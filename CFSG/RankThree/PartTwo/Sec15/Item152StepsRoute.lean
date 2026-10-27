module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsComp
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsEnd
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsGen
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec10.Item109
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

theorem false_of_isPerfect_of_card_fifteen {H : Type*} [Group H] [Finite H]
    (hp : Group.IsPerfect H) (h15 : Nat.card H = 15) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 H) := inferInstance
  have hPcard : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, h15]
    have : Nat.factorization 15 5 = 1 := by
      rw [show (15 : ℕ) = 3 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [this, pow_one]
  have hidx : (P : Subgroup H).index = 3 := by
    have h := Subgroup.card_mul_index (P : Subgroup H)
    rw [hPcard, h15] at h
    omega
  have h1 : Nat.card (Sylow 5 H) = 1 := by
    have hdvd := Sylow.card_dvd_index P
    rw [hidx] at hdvd
    have hmod := card_sylow_modEq_one 5 H
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · rw [h] at hmod
      exact absurd hmod (by decide)
  have : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp h1).1
  have hPn : (P : Subgroup H).Normal := Sylow.normal_of_subsingleton P
  have hq3 : Nat.card (H ⧸ (P : Subgroup H)) = 3 := hidx
  have : IsCyclic (H ⧸ (P : Subgroup H)) := isCyclic_of_prime_card hq3
  have hle : commutator H ≤ (P : Subgroup H) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rw [hp.commutator_eq_top] at hle
  have h := Subgroup.card_le_of_le hle
  rw [Subgroup.card_top, h15, hPcard] at h
  omega

theorem false_of_perfect_sixty_of_le {R : Type*} [Group R] [Finite R] {B N F : Subgroup R}
    (hNB : N ≤ B) (hN : (N.subgroupOf B).Normal) (hN2 : IsPGroup 2 N)
    (hodd : Odd (Nat.card (↥B ⧸ N.subgroupOf B))) (hFB : F ≤ B) (hFp : Group.IsPerfect ↥F)
    (h60 : Nat.card F = 60) : False := by
  set NF := N.subgroupOf F with hNF
  have hNFn : NF.Normal := by
    constructor
    intro n hn f
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hNB hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨f, hFB f.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have hNF2 : IsPGroup 2 NF := hN2.comap_subtype
  set g : ↥F →* ↥B ⧸ N.subgroupOf B :=
    (QuotientGroup.mk' (N.subgroupOf B)).comp (Subgroup.inclusion hFB) with hg
  have hker : g.ker = NF := by
    ext x
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hdvd : Nat.card (↥F ⧸ NF) ∣ Nat.card (↥B ⧸ N.subgroupOf B) := by
    rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd' : Odd (Nat.card (↥F ⧸ NF)) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNF2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup NF
  rw [h60, hk] at hcard
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    have : 2 ^ 3 ∣ 60 := h8.trans (Dvd.intro_left _ hcard.symm)
    norm_num at this
  obtain ⟨m, hm⟩ := hodd'
  have h15 : Nat.card (↥F ⧸ NF) = 15 := by
    interval_cases k <;> omega
  have : Group.IsPerfect (↥F ⧸ NF) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' NF) (QuotientGroup.mk'_surjective NF)
  exact false_of_isPerfect_of_card_fifteen this h15

theorem false_of_perfect_sixty_of_le_map {R Q : Type*} [Group R] [Finite R] [Group Q] [Finite Q]
    (φ : R →* Q) {B N : Subgroup R} (hNB : N ≤ B) (hN : (N.subgroupOf B).Normal)
    (hN2 : IsPGroup 2 N) (hodd : Odd (Nat.card (↥B ⧸ N.subgroupOf B))) {F : Subgroup Q}
    (hFB : F ≤ B.map φ) (hFp : Group.IsPerfect ↥F) (h60 : Nat.card F = 60) : False := by
  have hNB' : N.map φ ≤ B.map φ := Subgroup.map_mono hNB
  have hN' : ((N.map φ).subgroupOf (B.map φ)).Normal := by
    constructor
    intro x hx y
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨b, hb, hby⟩ := y.2
    have h := hN.conj_mem ⟨n, hNB hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨b, hb⟩
    rw [Subgroup.mem_subgroupOf] at h
    refine ⟨b * n * b⁻¹, by simpa using h, ?_⟩
    simp [hnx, hby]
  have hle : N.subgroupOf B ≤ ((N.map φ).subgroupOf (B.map φ)).comap (φ.subgroupMap B) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  set q := QuotientGroup.map (N.subgroupOf B) ((N.map φ).subgroupOf (B.map φ))
    (φ.subgroupMap B) hle with hq
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := φ.subgroupMap_surjective B y
    exact ⟨QuotientGroup.mk' _ x, rfl⟩
  have hodd' : Odd (Nat.card (↥(B.map φ) ⧸ (N.map φ).subgroupOf (B.map φ))) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_surjective hqs)
  exact false_of_perfect_sixty_of_le hNB' hN' (hN2.map φ) hodd' hFB hFp h60

variable {G : Type} [Group G] [Finite G]

theorem not_le_oTwoOddIn_of_perfect {X L : Subgroup G}
    {F : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hFX : F ≤ (X.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)))
    (hFp : Group.IsPerfect ↥F) (hF60 : Nat.card F = 60) : ¬ X ⊓ L ≤ oTwoOddIn X := by
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := X.subgroupOf L with hB
  set N := (CFSG.Open.pCoreOf 2 X).subgroupOf L with hN
  have hNB : N ≤ B := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X
      (Subgroup.mem_subgroupOf.mp hx))
  have hXO : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hNn : (N.subgroupOf B).Normal := by
    constructor
    intro n hn b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
    have hbX : ((b : ↥L) : G) ∈ X := Subgroup.mem_subgroupOf.mp b.2
    have h := (Subgroup.mem_normalizer_iff.mp (hXO hbX) _).mp hn
    simpa using h
  have hN2 : IsPGroup 2 N := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_subtype
  have hodd : Odd (Nat.card (↥B ⧸ N.subgroupOf B)) := by
    set ι : ↥B →* ↥X := (L.subtype.comp B.subtype).codRestrict X
      (fun x => Subgroup.mem_subgroupOf.mp x.2) with hι
    set ω : ↥B →* ↥X ⧸ CFSG.pCore 2 ↥X := (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp ι with hω
    have hker : ω.ker = N.subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, hω, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        CFSG.Open.pCoreOf]
      constructor
      · intro h
        exact ⟨ι x, h, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = ι x := Subtype.ext hyx
        rw [← this]
        exact hy
    have hrange : ω.range ≤ CFSG.oddCore (↥X ⧸ CFSG.pCore 2 ↥X) := by
      rintro _ ⟨x, rfl⟩
      have hxXL : ((x : ↥L) : G) ∈ X ⊓ L := ⟨Subgroup.mem_subgroupOf.mp x.2, (x : ↥L).2⟩
      obtain ⟨y, hy, hyx⟩ := hle hxXL
      have : y = ι x := Subtype.ext hyx
      rw [this] at hy
      exact hy
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange ω).toEquiv]
    exact Odd.of_dvd_nat Sec10.odd_card_oddCore
      ((Subgroup.card_dvd_of_le hrange).trans dvd_rfl)
  exact false_of_perfect_sixty_of_le_map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
    hNB hNn hN2 hodd hFX hFp hF60

theorem step152EndCover_of_genX (hX : Step152GenX) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) : Step152EndCover A (lB A) := by
  intro Y M X hctx c' L' d p P T K S hD hSH _
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hD.omega, mem_lA := hD.mem_lA }
  obtain ⟨F, hFX, hFp, hF60, -⟩ := hX G A c' L' h' Y M X hctx d p P T K S hD hSH
  exact not_le_oTwoOddIn_of_perfect hFX hFp hF60

theorem step152EndCoverR_of (hX : Step152GenX) : Step152EndCoverR :=
  fun _ _ _ _ _ _ hR => step152EndCover_of_genX hX hR.toSec14Std

theorem step152CompR_of'
    (h149 : Sec16.Item149S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) (hJ : Step152CompJR) : Step152CompR :=
  fun G _ _ A c L hR => step152Comp_of hR.toSec14Std h134 h48 h415
    (h149 G A c L hR.toSec14Std) (item148Normal_of_item148 (h148 G A c L hR)) hSz
    (hJ G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
