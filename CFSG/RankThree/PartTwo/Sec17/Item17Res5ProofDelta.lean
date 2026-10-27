module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res5ProofFit
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofMain
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] noncomputable def Step1712DeltaF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      ⁅V, Subgroup.zpowers c⁆ = ⊥ →
        (∃ R ∈ fourGroups A, R = ⁅R, Subgroup.zpowers c⁆ ∧ R ∈ scriptQ A (lB A) ∧
          R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) ∨
        ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧
          (CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) ≠ ⊥ ∨
            ∃ Z ∈ fourGroups A, Z ∈ scriptQ A (lB A) ∧
              Z ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
                Subgroup.centralizer ({a} : Set G) ∧
              ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
                ⁅CFSG.Open.pCoreOf p (delta A (lB A) (Subgroup.centralizer ({a} : Set G))),
                  Z⁆ = ⊥)

section Certified

theorem step1712Delta_of_F (hF : Step1712DeltaF) (h166 : Sec16.Item166S17)
    (hKM : Step1711KM) : Step1712Delta := by
  intro G _ _ A c L Y₀ h V hV hVc
  rcases hF G A c L Y₀ h V hV hVc with hR | ⟨a, ha, hac, hO2 | ⟨Z, hZ, hZQ, hZM, hZp⟩⟩
  · exact Or.inl hR
  · exact Or.inr ⟨a, ha, hac, hO2⟩
  refine Or.inr ⟨a, ha, hac, fun hO2 => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  set D := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hD
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  have hZD : Z ≤ D := le_delta hZQ (hZM.trans inf_le_right)
  have hZO2 : Z ≤ CFSG.Open.pCoreOf 2 M := hZM.trans inf_le_left
  have hZ4 : Nat.card Z = 4 := (mem_fourGroups_iff.mp hZ).2.2
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZ4]; norm_num)
  have hZbot : Z = ⊥ := by
    by_cases hDM : D ≤ M
    · have hZO : Z ≤ CFSG.Open.pCoreOf 2 D := (le_inf hZO2 hZD).trans
        (inf_le_pCoreOf_of_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
          (hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)))
      rw [hO2, le_bot_iff] at hZO
      exact hZO
    · have hKM' : k1711 A a ≤ (k1711 A a ⊓ M) ⊔ pPrimeCoreOf 3 (k1711 A a) := by
        by_cases h3 : 3 ∣ Nat.card D
        · exact hKM G A c L Y₀ h a ha ha1 hO2 hDM h3
        · rw [Proof1711.k1711_eq_bot_of_not_dvd h3]
          exact bot_le
      have hZK : Z ≤ Subgroup.normalizer (k1711 A a : Set G) :=
        hZD.trans (le_normalizer_oPrimeResidualOf Subgroup.le_normalizer)
      have hcomm : ⁅k1711 A a, Z⁆ ≤ pPrimeCoreOf 3 (k1711 A a) :=
        Proof1711.commutator_le_pPrimeCoreOf hZO2 hZK hKM'
      exact Proof17Res5.eq_bot_of_commutator_pCoreOf h (h166 G A c L Y₀ h) ha1 hZ2 hZD hZO2 hO2
        hcomm hZp
  rw [hZbot, Subgroup.card_bot] at hZ4
  omega

end Certified

end CFSG.RankThree.PartTwo.Sec17
