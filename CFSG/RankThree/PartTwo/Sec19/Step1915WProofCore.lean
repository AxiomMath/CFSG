module

public import CFSG.GH74.KGroups.U33
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec19.Step1919CoreDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Step1919CoreSplitLieRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      Sec4.IsExtOf
        (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        (∀ J ∈ scriptJ M H,
          (IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) ∧
          ((IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              IsProperParabolic (starIm J H)) ∨
            (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5))
                (Multiplicative (Fin 4 → ZMod 2))))) →
        (∀ J ∈ scriptJ M H, E ≤ Subgroup.normalizer (J : Set G)) →
        (∀ J ∈ scriptJ M H, ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
        ∀ J ∈ scriptJ M H,
          (∀ g ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
              Subgroup.normalizer (E : Set G),
            (∃ k : ℕ, g ^ 3 ^ k = 1) → g ∈ Subgroup.normalizer (J : Set G)) →
          IsProperParabolic (starIm J H) →
          (∀ e ∈ E, e ≠ 1 → ∃ j ∈ J, e * j * e⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
          3 ^ 6 ∣ Nat.card (MulAut (J ⧸ CFSG.pCore 2 J)) →
          Subgroup.center (J ⧸ CFSG.pCore 2 J) = ⊥ →
          ((∃ n : ℕ, 1 ≤ n ∧
              ((Even n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∨
                Nonempty (J ⧸ CFSG.pCore 2 J ≃*
                  CFSG.Assembly.RankThreeEven.projSp 2 (GaloisField 2 n)) ∨
                Sec8.IsoGTwoEven (J ⧸ CFSG.pCore 2 J) n)) ∨
            Nonempty (J ⧸ CFSG.pCore 2 J ≃* CFSG.Assembly.RankThreeEven.projSU 4 2 3)) →
          E ⊓ J ≠ E ⊓ L

namespace Step1915WProof

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank

theorem lieModel_of_mulEquiv_projSU_three {X : Type} [Group X] (ψ : X ≃* projSU 3 3 1) :
    CFSG.Blueprint.LieModel X .PSU 3 3 1 := by
  have e₀ : projSU 3 3 1 ≃* StatedProj (StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) :=
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 3 1))).symm
  refine Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1),
    inferInstance, inferInstance, ?_, ⟨ψ.trans e₀⟩⟩
  rw [GaloisField.card 3 (2 * 1) (by norm_num)]
  norm_num

theorem not_dvd_card_mulAut_of_mulEquiv_projSU_three
    {X : Type} [Group X]
    (ψ : X ≃* projSU 3 3 1) : ¬ 3 ^ 6 ∣ Nat.card (MulAut X) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (lieModel_of_mulEquiv_projSU_three ψ)
  rw [CFSG.GH74.KGroups.U33.card_mulAut e]
  norm_num

theorem pRank_le_one_of_mulEquiv_SL_odd {X : Type} [Group X] [Finite X] {n : ℕ} (hn : Odd n)
    (ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 :=
  Sec20.kFactL3OddThreeRank n hn X ⟨(ψ.trans
    (specialLinearGroupEquivStatedSL 3 (GaloisField 2 n))).trans
      (Sec20.projSLEquivStatedSL hn).symm⟩

theorem center_ne_bot_of_mulEquiv_SL_even {X : Type} [Group X] {n : ℕ} (hn : 0 < n)
    (he : Even n) (ψ : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) :
    Subgroup.center X ≠ ⊥ := by
  intro h
  have h3 := Sec21.Item222Proof.card_center_SL3 hn he
  rw [← Subgroup.map_center_eq ψ, h, Subgroup.map_bot, Subgroup.card_bot] at h3
  norm_num at h3

open Step1919EndProof in
theorem step1919CoreSplitLie_of_rest
    (hrest : Step1919CoreSplitLieRest) : Step1919CoreSplitLie := by
  intro G _ _ A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ hlist
    hEJF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := isE27_of_mem_partTwoE hctx.mem_partTwoT.1
  set F := E ⊓ L with hFdef
  have hFel : CFSG.Assembly.IsElemAbelian 3 F := isElemAbelian_of_le hE.1 inf_le_left
  have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hFel.2 x x.2)⟩
  have hFJ : F ≤ J := by
    rw [← hEJF]
    exact inf_le_right
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (J ⧸ CFSG.pCore 2 J)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top (isElemAbelian_starIm hFel)
      (by rw [card_starIm hF3 hFJ, h9]; norm_num)
  rcases hlist with ⟨n, hn, h | h | h | h⟩ | h | h
  ·
    exfalso
    obtain ⟨ψ⟩ := h
    rcases Nat.even_or_odd n with he | ho
    · exact center_ne_bot_of_mulEquiv_SL_even hn he ψ hZ
    · have := pRank_le_one_of_mulEquiv_SL_odd ho ψ
      omega
  ·
    rcases Nat.even_or_odd n with he | ho
    · exact hrest G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ
        (Or.inl ⟨n, hn, Or.inl ⟨he, h⟩⟩) hEJF
    · exfalso
      have := Sec20.kFactL3OddThreeRank n ho _ h
      omega
  · exact hrest G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ
      (Or.inl ⟨n, hn, Or.inr (Or.inl h)⟩) hEJF
  · exact hrest G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ
      (Or.inl ⟨n, hn, Or.inr (Or.inr h)⟩) hEJF
  · exact hrest G A c L E M hctx hLM h9 hX H hH hHM hJall hEN hcJ J hJ hP3 hpp hfaith h729 hZ
      (Or.inr h) hEJF
  ·
    obtain ⟨ψ⟩ := h
    exact absurd h729 (not_dvd_card_mulAut_of_mulEquiv_projSU_three ψ)

end Step1915WProof

end CFSG.RankThree.PartTwo.Sec19
