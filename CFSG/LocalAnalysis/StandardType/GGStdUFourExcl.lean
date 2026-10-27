module

public import CFSG.LocalAnalysis.StandardType.GGStdSpSixExcl
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem not_ggInnerDiagOnLabel_u4
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : CFSG.StandardType.GGConfig 3 B Bs x L D J) :
    ¬ CFSG.StandardType.GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 3 ∧ lab.n = 1) 3 Bs L := by
  intro hM
  obtain ⟨⟨-, -, -, -, -, hβ, hS, hst⟩, ⟨hBBs, -, -, -⟩, -⟩ := hC
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, hlabU, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, hn⟩ := hlabU
  dsimp only at ht hr hn
  subst hr hn
  have key : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
      IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) →
      (∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)), a * b ≠ b * a) →
      ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
          (LargeEvenGUSet (Fin 4) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      False := by
    intro K _ _ hK _ _ θ hBsN h3s
    have hdq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
    have h3 : ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) (LargeEvenGUSet (Fin 4) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
      fun b hb => h3s b (hBBs hb)
    have hZ := TableBUE.center_proj_eq_bot hK (by norm_num) hdq
    have hnc := UnitTB.exists_noncyclic_of_torusLift Nat.prime_three
      (by norm_num [ggUnitaryTorusRank]) hL θ
      (ggTorusLift_unitary hK le_rfl (by norm_num) hdq Nat.prime_three (by norm_num))
    have hOP := InndiagSU.ggOutdiagPrime_unitary hK le_rfl (by norm_num) hdq Nat.prime_three
      (by norm_num) (by norm_num)
    have hinn : ∀ b (hb : b ∈ B), ggLAut L θ ⟨b, hBN hb⟩ ∈
        (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) →* _).range := by
      intro b hb
      refine hOP _ (ggLAut_mem_of_induces L θ hBN h3 hb) ?_
      have hb3 : (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, OneMemClass.coe_one]
        exact hS.1.1.2 b hb)
      rw [← map_pow, hb3, map_one]
    set ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) :=
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
      obtain ⟨-, hδ2⟩ := ggDeltaAdm_of_delta Nat.prime_three hS hBN hδ
      rcases hδ2 with ⟨⟨a, ⟨b, rfl⟩, hna'⟩, -⟩ | ⟨hdvd, -, -⟩
      · obtain ⟨g, hg⟩ := isInner_of_induces hψ hker hL (ggGamma L hBN b) (hinn b b.2)
          (fun l => ggLAut_apply L θ _ l)
        exact hna' ⟨g, hg.symm⟩
      · exact StdSubRestU.ggCenterPrime_unitary hK le_rfl (by norm_num) hdq Nat.prime_three
          (by norm_num) (by norm_num) L ψ hψ hker hL hdvd
    have hcard := card_le_pow_twoLocalPrimeRank_of_sstar Nat.prime_three (by norm_num) hS hnc hL
      hZ θ hBN h3 (InndiagSU.ggOutdiagOdd_unitary hK le_rfl (by norm_num) (by norm_num) 3) hinn
      hst.2.1 hδ
    have hR2 : twoLocalPrimeRank 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) ≤ 2 :=
      CFSG.RankThree.PartTwo.Census.localRank_three_statedSU_four_le
        (TableBU.unitaryFieldData_of_card hK le_rfl)
    have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
    have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
    have h81 : 3 ^ 4 ≤ Nat.card B := hB ▸ Nat.pow_le_pow_right (by norm_num) h4
    have h27 : Nat.card B ≤ 3 ^ 3 :=
      hcard.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK hs hna θ hBsN h3s
  · obtain ⟨K, _, _, hK, hs, hna, θ, -, hBsN, h3s⟩ := hraw
    exact key K hK hs hna θ hBsN h3s

end CFSG.StandardType

end
