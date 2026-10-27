module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Seventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Defs
import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMGeom
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem close16_card_vtil (hS : Close16Setting D V L hV) :
    Nat.card (Vtil ⊥ V hV) = 256 := by
  obtain ⟨-, ⟨L₀, -, -, -, hsum⟩, -⟩ := hS.shape
  obtain ⟨I, hnat, h01, hsup⟩ := s16c167_seventeen_sumOfNat_two hsum
  have hcardI : ∀ i, Nat.card ↥(I i) = 16 := by
    intro i
    obtain ⟨K, _, _, hKcard, _, _, _, _, _, _, _, _, β, hβs, hβk, -⟩ := hnat i
    have h1 : Nat.card ↥(I i) = Nat.card β.range * Nat.card β.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv]
    have hker : β.ker = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker] at hu
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by
        have h : (u : Vtil ⊥ V hV) ∈ (⊥ : Subgroup (Vtil ⊥ V hV)) := (hβk u).mp hu
        simpa using Subgroup.mem_bot.mp h)
    have h3 : Nat.card (↥(FFModel.nat (StatedSL 4 K)).sec ⧸
        (FFModel.nat (StatedSL 4 K)).ker.subgroupOf
          (FFModel.nat (StatedSL 4 K)).sec) = 16 := by
      show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 4 → K))).subgroupOf ⊤) = 16
      rw [Subgroup.bot_subgroupOf,
        Nat.card_congr (QuotientGroup.quotientBot).toEquiv, Subgroup.card_top]
      show Nat.card (Fin 4 → K) = 16
      rw [Nat.card_fun, Nat.card_fin, hKcard]
      norm_num
    have hβrange : Nat.card β.range = Nat.card (↥(FFModel.nat (StatedSL 4 K)).sec ⧸
        (FFModel.nat (StatedSL 4 K)).ker.subgroupOf
          (FFModel.nat (StatedSL 4 K)).sec) := by
      rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top]
    rw [h1, hβrange, h3, hker, Subgroup.card_bot, mul_one]
  have hjoin : Nat.card ↥(I 0 ⊔ I 1) = Nat.card ↥(I 0) * Nat.card ↥(I 1) := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (I 0) (I 1) (by rw [CommGroup.normalizer_eq_top]; exact le_top)
      (disjoint_iff.mpr h01)
    simpa using h
  calc Nat.card (Vtil ⊥ V hV) = Nat.card ↥(I 0 ⊔ I 1) := by
        rw [hsup]; exact (Subgroup.card_top).symm
    _ = Nat.card ↥(I 0) * Nat.card ↥(I 1) := hjoin
    _ = 16 * 16 := by rw [hcardI 0, hcardI 1]
    _ = 256 := by norm_num

theorem close16_card_V (hS : Close16Setting D V L hV) : Nat.card ↥V = 256 := by
  rw [card_Vtil_eq ⊥ V hV bot_le, Subgroup.card_bot, one_mul, close16_card_vtil hS]

theorem close16_four_le_card_centralizer (hS : Close16Setting D V L hV) {A : Subgroup G}
    (hAM : A ≤ D.M) (hA : Nat.card A = 7) :
    4 ≤ Nat.card ↥(V ⊓ centralizer (A : Set G)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := ↥A)).mp
    (isCyclic_of_prime_card (α := ↥A) hA)
  have ha7 : orderOf (a : G) = 7 := by
    rw [Subgroup.orderOf_coe a, ← Nat.card_zpowers a, ha, Subgroup.card_top, hA]
  have hnorm : D.M ≤ Subgroup.normalizer (V : Set G) :=
    hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hzale : Subgroup.zpowers (a : G) ≤ A := Subgroup.zpowers_le.2 a.2
  have hF : ∀ g ∈ Subgroup.zpowers (a : G), ∀ s ∈ (V : Set G), g * s * g⁻¹ ∈ V := by
    intro g hg s hs
    exact (Subgroup.mem_normalizer_iff.mp (hnorm (hAM (hzale hg))) s).mp hs
  have hmod := CFSG.HardMathSupport.Dickson.Sec6.I1431.ncard_modEq_fixed
    (p := 7) (by norm_num) ha7 (F := (V : Set G)) hF
  have hAeq : A = Subgroup.zpowers (a : G) := by
    refine le_antisymm ?_ hzale
    intro h hh
    have hmem : (⟨h, hh⟩ : ↥A) ∈ Subgroup.zpowers a := by
      rw [ha]; exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hset : {s : G | s ∈ (V : Set G) ∧ (a : G) * s = s * (a : G)} =
      (↑(V ⊓ centralizer (A : Set G)) : Set G) := by
    ext s
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hsV, hcomm⟩
      refine ⟨hsV, ?_⟩
      intro h hh
      have hh' : h ∈ Subgroup.zpowers (a : G) := hAeq ▸ hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh'
      rw [← hk]
      exact (Commute.zpow_left ((commute_iff_eq (a : G) s).2 hcomm) k).eq
    · rintro ⟨hsV, hcent⟩
      exact ⟨hsV, hcent (a : G) a.2⟩
  have hvcard : (V : Set G).ncard = 256 := by
    rw [← Nat.card_coe_set_eq]
    exact close16_card_V hS
  have hmod' : Nat.card ↥(V ⊓ centralizer (A : Set G)) ≡ 256 [MOD 7] := by
    change ((V ⊓ centralizer (A : Set G) : Subgroup G) : Set G).ncard ≡ 256 [MOD 7]
    rw [← hset]
    have h256 : (256 : ℕ) ≡ (V : Set G).ncard [MOD 7] := by rw [hvcard]
    exact Nat.ModEq.symm (h256.trans hmod)
  have hmod7 : Nat.card ↥(V ⊓ centralizer (A : Set G)) % 7 = 4 := by
    have h := hmod'
    rw [Nat.ModEq] at h
    norm_num at h
    exact h
  calc 4 = Nat.card ↥(V ⊓ centralizer (A : Set G)) % 7 := hmod7.symm
    _ ≤ Nat.card ↥(V ⊓ centralizer (A : Set G)) := Nat.mod_le _ _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
