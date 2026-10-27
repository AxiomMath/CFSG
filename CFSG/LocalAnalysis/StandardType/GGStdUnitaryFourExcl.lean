module

public import CFSG.LocalAnalysis.StandardType.GGStdSpSixExcl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Split
public import CFSG.CGT.Timmesfeld75.JLemma35
public import CFSG.CGT.Timmesfeld75.JLemmaTrans
public import CFSG.CGT.Timmesfeld75.Sec5SevenB
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOthV
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I163
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem twoLocalPrimeRank_largeEvenProj_unitary_four_le (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ)
    (hK : Nat.card F = (2 ^ f) ^ 2) (hrq : r ∣ 2 ^ f + 1) :
    twoLocalPrimeRank r (LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ f))) ≤ 2 := by
  have h := CFSG.LocalAnalysis.GLTheoremA.twoLocalPrimeRank_statedSU_quot_le_of_dvd
    r hr hr2 F f 4 hK (by norm_num) hrq
    ((CFSG.Open.StatedScalars (Fin 4) F).subgroupOf (CFSG.Open.StatedSU 4 (2 ^ f) F))
    (CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_le_center _)
  rwa [show (4 : ℕ) - 2 = 2 from rfl] at h

theorem not_ggInnerDiagOnLabel_unitary_four
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : CFSG.StandardType.GGConfig p B Bs x L D J) :
    ¬ CFSG.StandardType.GGInnerDiagOnLabel
      (fun p lab => (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1) p Bs L := by
  intro hM
  obtain ⟨⟨-, -, -, -, -, hβ, hS, hst⟩, ⟨hBBs, -, -, -⟩, -⟩ := hC
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, hlabU, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, hdvd⟩ := hlabU
  dsimp only at ht hr hdvd
  subst hr
  obtain ⟨hp, hp2, -, h4⟩ := hβ
  have h4' : 4 ≤ twoLocalPrimeRank p G := h4
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hdvd)) hp2
    · exact h0
  have hpd : ¬ p ∣ 4 := by
    intro h
    have : p ∣ 2 ^ 2 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
  have key : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
      IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) →
      (∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)), a * b ≠ b * a) →
      ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      False := by
    intro K _ _ hK _ _ θ hBsN h3s
    have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
    have h3 : ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (LargeEvenGUSet (Fin 4) K (2 ^ n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
      fun b hb => h3s b (hBBs hb)
    have hZ := TableBUE.center_proj_eq_bot hK (by norm_num) hdq
    have hrk : 2 ≤ ggUnitaryTorusRank p 4 := by
      simp [ggUnitaryTorusRank, hpd]
    have hnc := UnitTB.exists_noncyclic_of_torusLift hp hrk hL θ
      (ggTorusLift_unitary hK hn (by norm_num) hdq hp hdvd)
    have hOP := InndiagSU.ggOutdiagPrime_unitary hK hn (by norm_num) hdq hp hdvd hpd
    have hinn : ∀ b (hb : b ∈ B), ggLAut L θ ⟨b, hBN hb⟩ ∈
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →* _).range := by
      intro b hb
      refine hOP _ (ggLAut_mem_of_induces L θ hBN h3 hb) ?_
      have hbp : (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, OneMemClass.coe_one]
        exact hS.1.1.2 b hb)
      rw [← map_pow, hbp, map_one]
    set ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
      θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hψdef
    have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : ψ.ker ≤ Subgroup.center L := by
      intro l hl
      rw [MonoidHom.mem_ker] at hl
      have h1 : (QuotientGroup.mk' (Subgroup.center L)) l = 1 :=
        θ.injective (by rw [map_one]; exact hl)
      exact (QuotientGroup.eq_one_iff l).mp h1
    have hδ : ¬ ∃ T₀ : Subgroup G, T₀ ≤ Subgroup.centralizer (L : Set G) ∧
        T₀ ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T₀ ∧
        B ≤ Subgroup.normalizer (T₀ : Set G) ∧ (⁅T₀, B⁆ : Subgroup G) ≠ ⊥ := by
      intro hδ
      obtain ⟨-, hδ2⟩ := ggDeltaAdm_of_delta hp hS hBN hδ
      rcases hδ2 with ⟨⟨a, ⟨b, rfl⟩, hna'⟩, -⟩ | ⟨hdvd', -, -⟩
      · obtain ⟨g, hg⟩ := isInner_of_induces hψ hker hL (ggGamma L hBN b) (hinn b b.2)
          (fun l => ggLAut_apply L θ _ l)
        exact hna' ⟨g, hg.symm⟩
      · exact StdSubRestU.ggCenterPrime_unitary hK hn (by norm_num) hdq hp hp2 hpd L ψ hψ hker hL
          hdvd'
    have hcard := card_le_pow_twoLocalPrimeRank_of_sstar hp hp2 hS hnc hL
      hZ θ hBN h3 (InndiagSU.ggOutdiagOdd_unitary hK hn (by norm_num) (fun h => absurd h.1 (by norm_num)) p) hinn
      hst.2.1 hδ
    have hR2 : twoLocalPrimeRank p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) ≤ 2 :=
      haveI : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
      twoLocalPrimeRank_largeEvenProj_unitary_four_le p hp hp2 K n hK hdvd
    have hB : Nat.card B = p ^ twoLocalPrimeRank p G := hS.1.2.1
    have hpow4 : p ^ 4 ≤ Nat.card B := hB ▸ Nat.pow_le_pow_right hp.pos h4'
    have hpow3 : Nat.card B ≤ p ^ 3 :=
      hcard.trans (Nat.pow_le_pow_right hp.pos (Nat.add_le_add_right hR2 1))
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd (lt_of_lt_of_le hlt (hpow4.trans hpow3)) (lt_irrefl _)
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK hs hna θ hBsN h3s
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK hs hna θ hBsN h3s

end CFSG.StandardType

end
