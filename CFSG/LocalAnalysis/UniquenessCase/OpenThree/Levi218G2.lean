module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218XE3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
import CFSG.LieType.Chevalley.E6GraphRadicalDetector
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG2QTor
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevG2Rank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
import CFSG.GH74.Generic.BProg.B3.S1IdentSl2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley (Tag adjointGroup ModGL)
open CFSG.LieType.Chevalley (posUnipotentSub torusSub simpleRootSL2 SL2)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.AGLEmbedding.KFactProofs.G2Q (tz ia ir tz_pow tz_one_one tz_injective
  tz_mem_adjointGroup tz_mem_torusGroup cartan_ia_ir cartan_ir_ir)

section Torus

variable {K : Type} [Field K]

private theorem tz_sq_commute_unit (a : Kˣ) (c : K) :
    tz (a ^ 2) a * CFSG.Blueprint.Chevalley.xUnit Tag.G2 K ir c =
        CFSG.Blueprint.Chevalley.xUnit Tag.G2 K ir c * tz (a ^ 2) a ∧
      tz (a ^ 2) a * CFSG.Blueprint.Chevalley.yUnit Tag.G2 K ir c =
        CFSG.Blueprint.Chevalley.yUnit Tag.G2 K ir c * tz (a ^ 2) a := by
  have hconj : ∀ g : ModGL Tag.G2 K, tz (a ^ 2) a * g * (tz (a ^ 2) a)⁻¹ = g →
      tz (a ^ 2) a * g = g * tz (a ^ 2) a := fun g hg => by
    calc tz (a ^ 2) a * g = tz (a ^ 2) a * g * (tz (a ^ 2) a)⁻¹ * tz (a ^ 2) a := by group
      _ = g * tz (a ^ 2) a := by rw [hg]
  have hu : ((a ^ 2) ^ (-1 : ℤ) : Kˣ) * (a ^ (2 : ℤ) : Kˣ) = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    group
  have hu' : ((a ^ 2) ^ (-(-1) : ℤ) : Kˣ) * (a ^ (-2 : ℤ) : Kˣ) = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    group
  refine ⟨hconj _ ?_, hconj _ ?_⟩
  · have e : tz (a ^ 2) a * CFSG.Blueprint.Chevalley.xUnit Tag.G2 K ir c * (tz (a ^ 2) a)⁻¹ =
        CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ia (a ^ 2) *
          (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ir a *
            CFSG.Blueprint.Chevalley.xUnit Tag.G2 K ir c *
              (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ir a)⁻¹) *
          (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ia (a ^ 2))⁻¹ := by
      unfold tz
      group
    rw [e, (CFSG.LieType.Chevalley.simple_torus_root_conjugation Tag.G2 K ir ir a c).1,
      (CFSG.LieType.Chevalley.simple_torus_root_conjugation Tag.G2 K ia ir (a ^ 2) _).1,
      cartan_ia_ir, cartan_ir_ir, ← mul_assoc, ← Units.val_mul, hu, Units.val_one, one_mul]
  · have e : tz (a ^ 2) a * CFSG.Blueprint.Chevalley.yUnit Tag.G2 K ir c * (tz (a ^ 2) a)⁻¹ =
        CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ia (a ^ 2) *
          (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ir a *
            CFSG.Blueprint.Chevalley.yUnit Tag.G2 K ir c *
              (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ir a)⁻¹) *
          (CFSG.Blueprint.Chevalley.torusElt Tag.G2 K ia (a ^ 2))⁻¹ := by
      unfold tz
      group
    rw [e, (CFSG.LieType.Chevalley.simple_torus_root_conjugation Tag.G2 K ir ir a c).2,
      (CFSG.LieType.Chevalley.simple_torus_root_conjugation Tag.G2 K ia ir (a ^ 2) _).2,
      cartan_ia_ir, cartan_ir_ir, ← mul_assoc, ← Units.val_mul, hu', Units.val_one, one_mul]

end Torus

section Levi

variable {K : Type} [Field K] [CharP K 2]

private noncomputable def g2Levi : SL2 K →* ↥(adjointGroup Tag.G2 K) :=
  (simpleRootSL2 Tag.G2 K ir).codRestrict _
    (CFSG.LieType.Chevalley.simpleRootSL2_mem_adjointGroup ir)

private theorem g2Levi_injective : Function.Injective (g2Levi (K := K)) := fun _ _ h =>
  CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two (CharTwo.two_eq_zero) ir
    (congrArg Subtype.val h)

omit [CharP K 2] in
private theorem g2Levi_le_centralizer (a : Kˣ) :
    (g2Levi (K := K)).range ≤
      centralizer {(⟨tz (a ^ 2) a, tz_mem_adjointGroup _ _⟩ : ↥(adjointGroup Tag.G2 K))} := by
  have h1 : (simpleRootSL2 Tag.G2 K ir).range ≤ centralizer {tz (a ^ 2) a} := by
    rw [CFSG.LieType.Chevalley.range_simpleRootSL2, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (tz_sq_commute_unit a c).1.symm
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (tz_sq_commute_unit a c).2.symm
  rintro _ ⟨A, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  have h2 := mem_centralizer_singleton_iff.1 (h1 ⟨A, rfl⟩)
  exact h2

end Levi

section Model


variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem levi218_G2_model {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hpq : p ∣ 2 ^ n + 1)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.G2 K)) ≤ 2) :
    Levi218 n (2 ^ n - 1) (posUnipotentSub Tag.G2 K) p := by
  classical
  refine ⟨torusSub Tag.G2 K, (CFSG.Quasithin.H13.Sec53F.G2.fieldAut K).range,
    uc22s218_g2_fieldBorelData_model (by omega) hK, fun {s r} hs hsn hr hrs => ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by
    rw [Nat.card_units, hK]
    exact hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
  have hxo : orderOf (tz (a ^ 2) a : ModGL Tag.G2 K) = r := by
    rw [← ha, orderOf_eq_orderOf_iff]
    intro m
    rw [tz_pow, ← tz_one_one]
    constructor
    · intro h
      exact (tz_injective h).2
    · intro h
      rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  have := Fintype.ofFinite K
  refine ⟨⟨tz (a ^ 2) a, tz_mem_adjointGroup _ _⟩, ?_, ?_, (g2Levi (K := K)).range, n,
    g2Levi_le_centralizer a, hn, Or.inl ?_, Or.inl ⟨hrk, ?_⟩⟩
  · rw [Subgroup.mem_subgroupOf]
    exact tz_mem_torusGroup _ _
  · rw [Subgroup.orderOf_mk, hxo]
  · exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two (by omega)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
      (MonoidHom.ofInjective g2Levi_injective).symm
  · rw [← Nat.card_congr (MonoidHom.ofInjective (g2Levi_injective (K := K))).toEquiv,
      CFSG.GH74.Generic.BProg.B3.S1IdentSl2.card_sl2, hK]
    refine dvd_mul_of_dvd_right (hpq.trans ⟨2 ^ n - 1, ?_⟩) _
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    zify [h1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring

end Model

section Rank


theorem levi218_G2 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsG2 Y n) (hn : ¬ IsPowTwo n)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ n - 1) (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) :
    Levi218 n (2 ^ n - 1) U p := by
  obtain ⟨hn2, K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_g2_exists_model hY
  have hn3 : 3 ≤ n := by
    by_contra h
    have h2 : n = 2 := by omega
    exact hn ⟨1, by rw [h2]; rfl⟩
  have : Finite ↥(adjointGroup Tag.G2 K) := Finite.of_equiv Y e.toEquiv
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hY2 : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup Tag.G2 K)) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
    exact uc22s218_g2_pRank_le_two hY hp hp2
  have hpq1 : p ∣ 2 ^ n + 1 := by
    have h1 : 2 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.rkG2 (Fintype.card K) p := by
      rw [← CFSG.LocalAnalysis.RankThreeUC.S15.pRank_adjointG2_eq K hK' hn2 hp hp2,
        ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
      exact hrk
    have h2 : CFSG.LocalAnalysis.RankThreeUC.S15.eS (Fintype.card K) p = 1 := by
      unfold CFSG.LocalAnalysis.RankThreeUC.S15.rkG2 at h1
      split_ifs at h1 with h3 h4 <;> omega
    have h3 := (CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_one_iff Fintype.card_pos).1 h2
    rw [hK'] at h3
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    rw [hfac] at h3
    rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
    · exact h
    · exact absurd h hpq
  have h1 := (levi218_G2_model hn3 hK hpq1 hY2).map hp e.symm
  exact h1.of_sylow hp hU

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
