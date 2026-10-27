module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInternal
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBLift
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem eq_of_mk_eq_of_pow_three {L : Type*} [Group L] [Finite L]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center L)) {a b : L} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : (a : L ⧸ Subgroup.center L) = b) : a = b := by
  have hz : a⁻¹ * b ∈ Subgroup.center L := QuotientGroup.eq.mp hab
  have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hz a
  have hz3 : (a⁻¹ * b) ^ 3 = 1 := by
    have h := hcomm.mul_pow 3
    rw [mul_inv_cancel_left, hb, ha, one_mul] at h
    exact h.symm
  have hzc : (a⁻¹ * b) ^ Nat.card (Subgroup.center L) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hz)
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h1 : (a⁻¹ * b) ^ (Nat.gcd 3 (Nat.card (Subgroup.center L))) = 1 :=
    pow_gcd_eq_one.mpr ⟨hz3, hzc⟩
  rw [hcop, pow_one] at h1
  exact (inv_mul_eq_one.mp h1)

theorem exists_lift_pow_three {L : Type*} [Group L] [Finite L]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center L)) (q : L ⧸ Subgroup.center L) (hq : q ^ 3 = 1) :
    ∃ l : L, l ^ 3 = 1 ∧ (l : L ⧸ Subgroup.center L) = q := by
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective q
  set m := Nat.card (Subgroup.center L)
  have hm : m ^ 2 % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have hc : l₀ ^ 3 ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hq
  have hcm : (l₀ ^ 3) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hc)
  refine ⟨l₀ ^ (m ^ 2), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, sq, pow_mul, hcm, one_pow]
  · rw [QuotientGroup.mk_pow, ← Nat.div_add_mod (m ^ 2) 3, pow_add, pow_mul, hq, one_pow, one_mul,
      hm, pow_one]

theorem toralAt_of_inner {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinn : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center L)) (hC : GGTorusCentSC 3 R) :
    toralAt 3 B Bs x L D J hS R θ hN := by
  have hLperf : commutator L = ⊤ := (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  have hCR : Subgroup.center R = ⊥ := ggQ2Cent_center_eq_bot hLperf θ
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    fun a b h => ggQ2Cent_eq_of_conj_eq hCR h
  have hBsE : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hBsSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  set A := (ggBeta L θ hN).range with hA
  let E : Subgroup R := A.comap (MulAut.conj : R →* MulAut R)
  have hE : IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨a', ha'⟩ := (Subgroup.mem_comap.mp a.2 : MulAut.conj (a : R) ∈ A)
      obtain ⟨b', hb'⟩ := (Subgroup.mem_comap.mp b.2 : MulAut.conj (b : R) ∈ A)
      apply hinj
      have hab : a' * b' = b' * a' := hBsE.1.is_comm.comm a' b'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul,
        hab]
    · obtain ⟨b', hb'⟩ := (Subgroup.mem_comap.mp he : MulAut.conj e ∈ A)
      have hb3 : b' ^ 3 = 1 := Subtype.ext (by simpa using hBsE.2 b' b'.2)
      apply hinj
      rw [map_pow, ← hb', ← map_pow, hb3, map_one, map_one]
  have hcard : 3 ^ 3 ≤ Nat.card E := by
    have hmap : E.map (MulAut.conj : R →* MulAut R) = A := Subgroup.map_comap_eq_self hinn
    have hEA : Nat.card E = Nat.card A := by
      rw [← hmap, Subgroup.card_map_of_injective hinj]
    have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
    have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_largeEvenStandardType hS.1.1.1.2.2.2.2.2.2.2
    have hBsB : B ≤ Bs := hS.1.1.2.1.1
    have hrB := card_range_ggBeta_mul_of Nat.prime_three hSStar.1.1 hSStar.2.1 hSStar.2.2.1
      hSStar.2.2.2.1.1 hSStar.2.2.2.2 hLperf θ hBN
    have hle : (ggBeta L θ hBN).range ≤ A := by
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBsB b.2⟩, rfl⟩
    have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hS.1.1
    have hrank : 4 ≤ LargeEvenTwoLocalRank 3 G := hS.1.1.1.2.2.2.2.2.1.2.2.2
    have hB81 : 3 ^ 4 ≤ Nat.card B := hBcard ▸ Nat.pow_le_pow_right (by norm_num) hrank
    have : Finite A := Finite.of_surjective _ (ggBeta L θ hN).rangeRestrict_surjective
    have hAle : Nat.card (ggBeta L θ hBN).range ≤ Nat.card A := Subgroup.card_le_of_le hle
    rw [hEA]
    omega
  have hSC : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hgE hg3
    have hq3 : (θ.symm g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    obtain ⟨l, hl3, hlq⟩ := exists_lift_pow_three h3 (θ.symm g) hq3
    have hlg : ggQuotHom θ l = g := by
      show θ (l : L ⧸ Subgroup.center L) = g
      rw [hlq, MulEquiv.apply_symm_apply]
    have hlC : (l : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbA : ggBeta L θ hN ⟨b, hb⟩ ∈ A := ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨e, he⟩ := hinn hbA
      have heE : e ∈ E := Subgroup.mem_comap.mpr (he ▸ hbA)
      have hfix : ggBeta L θ hN ⟨b, hb⟩ g = g := by
        rw [← he, MulAut.conj_apply, ← hgE e heE, mul_inv_cancel_right]
      set l' := L.normalizerMonoidHom ⟨b, hN hb⟩ l with hl'
      have himg : (l' : L ⧸ Subgroup.center L) = (l : L ⧸ Subgroup.center L) := by
        apply θ.injective
        rw [← ggLAut_apply]
        change ggBeta L θ hN ⟨b, hb⟩ (ggQuotHom θ l) = ggQuotHom θ l
        rw [hlg, hfix]
      have hl'3 : l' ^ 3 = 1 := by rw [hl', ← map_pow, hl3, map_one]
      have heq : l' = l := eq_of_mk_eq_of_pow_three h3 hl'3 hl3 himg
      have hbl : b * (l : G) * b⁻¹ = l := by
        have h := congrArg Subtype.val heq
        rwa [hl', normalizerMonoidHom_coe] at h
      calc b * (l : G) = b * (l : G) * b⁻¹ * b := by group
        _ = l * b := by rw [hbl]
    have hlBs : (l : G) ∈ Bs := hBsSC _ hlC (by simpa using congrArg Subtype.val hl3)
    refine Subgroup.mem_comap.mpr ⟨⟨l, hlBs⟩, ?_⟩
    rw [ggBeta_eq, ggLAut_of_mem θ l, hlg]
  exact actionThree_of_torusCentSC hC A E hE hcard hSC (Subgroup.map_comap_le _ _)

theorem labelTInput_of_labelAll
    {S : LargeEvenLabel → Prop}
    (hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.n = 1 → S lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusCentSC 3 R ∧
        (∀ φ ∈ I, φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R)) ∧
          GGCenterPrime 3 R) :
    labelTInput S := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, hSlab⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  obtain ⟨R', _, I', F', ⟨-, -, θ', -, -, h3I⟩, hTC, hInn, hCP⟩ :=
    largeEvenRawDatum_exists (hall lab hlab hn hSlab _ hraw)
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center L) := by
    refine hCP L (ggQuotHom θ') ?_ ?_ hperf
    · exact θ'.surjective.comp (QuotientGroup.mk'_surjective _)
    · intro z hz
      rw [MonoidHom.mem_ker] at hz
      have h1 : QuotientGroup.mk' (Subgroup.center L) z = 1 :=
        θ'.injective (by simpa [ggQuotHom] using hz)
      exact (QuotientGroup.eq_one_iff z).mp h1
  have hinn : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro _ ⟨b, rfl⟩
    have hb3 : ggLAut L θ' ⟨b, hN b.2⟩ ^ 3 = 1 := by
      have hb : (⟨b, hN b.2⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (hS.1.1.2.1.2.1.2 b b.2)
      rw [← map_pow, hb, map_one]
    obtain ⟨r', hr'⟩ := hInn _ (ggLAut_mem_of_induces L θ' hN h3I b.2) hb3
    refine ⟨(θ'.symm.trans θ) r', ?_⟩
    rw [ggBeta_eq, ggLAut_congr L θ' θ, ← hr']
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  exact toralAt_of_inner hS θ hN hinn h3Z (ggTorusCentSC_of_mulEquiv (θ.symm.trans θ') hTC)

end CFSG.StandardType.GGQ2CentPort

end
