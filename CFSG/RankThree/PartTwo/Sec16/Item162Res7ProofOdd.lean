module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res6ProofOdd
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofAlt
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def Step162UJOddOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J₀ ∈ scriptY0 A (lB A),
        J₀ ∈ thetaComponentsIn
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
        (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) 2 n) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J₀) ⊔ CFSG.Open.pCoreOf 2 L') →
        (∀ I ∈ scriptY0Star A (lB A), J₀ ≤ I → I ≠ J₀ ⊔ CFSG.Open.pCoreOf 2 I) →
        ∀ I ∈ scriptY0Star A (lB A), J₀ ≤ I →
        ∀ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
          MeetsY4 A (lB A) Le I →
          I = (I ⊓ Le) ⊔ CFSG.Open.pCoreOf 2 I → Le = (Le ⊓ I) ⊔ CFSG.Open.pCoreOf 2 Le →
          omegaA A = {Subgroup.zpowers e} →
          Nonempty (lBarA e Le A ≃* Multiplicative (ZMod 3) × Sec12.lBar e Le) →
          IsEmpty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.M12) →
          ¬ TransOn A (lB A) (xA A) (Subgroup.centralizer ({e} : Set G)) →
          ∃ J ∈ scriptY0 A (lB A),
            J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧
              ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n

namespace Res162Seven

variable {G : Type} [Group G] [Finite G]

theorem exists_not_transOn_point (hX : Claim1411NonsolvXR) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂)
    (hnt : ¬ TransOn A (lB A) (xA A)
      (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))))
    {J₀ : Subgroup G} (hJ₀ : J₀ ∈ scriptY0 A (lB A))
    (hJ₀K : J₀ ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) :
    ∃ a : G, Subgroup.zpowers a ∈ omegaA A ∧
      ¬ TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ := hmax.1.s₁
  have hS₂ := hmax.1.s₂
  have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS₁.prop.1.1.1.2.2 hS₂.prop.1.1.1.2.2
  have hUQ : S₁ ⊓ S₂ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hS₁.prop.1.1 inf_le_left hAU
  have hU2 : IsPGroup 2 (S₁ ⊓ S₂ : Subgroup G) :=
    (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁.prop).to_le inf_le_left
  have hK3 := Proof169.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian
    hmax.1.ne_bot hU2 hUQ
  have hsol : ¬ Group.IsSolvable ↥(delta A (lB A)
      (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) := fun hs =>
    Proof162.not_isSolvable_of_mem_scriptY4 hJ₀.1
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ₀K))
  by_contra hall
  push Not at hall
  exact hnt (hX G A c L h hall _ hK3.2 hK3.1.1 hsol)

end Res162Seven

open Res162Seven in
theorem step162UJOddProper_of_one
    (h1514 : Item1514R) (h1523 : Item1523R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R) (hMP : Step163MeetsPoint)
    (hX : Claim1411NonsolvXR) (hOne : Step162UJOddOne) : Step162UJOddProper := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov hside
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hJ₀
  obtain ⟨e, Le, he, hLe, hm⟩ := exists_point_meetsY4 h
    (fun G _ _ A c L hR _ => h1514 G A c L hR) h1523 h153 hobs h1411 hMP hI
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  rcases h1514 G A e Le he' I hI hm with ⟨hI1, hL1, hΩ, hbar, hM12⟩ | ⟨-, -, -, hI7⟩ |
      ⟨-, hI7, -⟩
  ·
    obtain ⟨a, ha, hna⟩ := exists_not_transOn_point hX h hmax hnt hJ₀
      (le_of_mem_thetaComponentsIn hJ₀K)
    have hae : Subgroup.zpowers a = Subgroup.zpowers e := by
      rw [hΩ] at ha
      exact ha
    rw [KFacts.KS14.centralizer_eq_of_zpowers_eq hae] at hna
    exact hOne G A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov hside I hI hJI e Le
      he hLe hm hI1 hL1 hΩ hbar hM12 hna
  ·
    exfalso
    obtain ⟨n, hn, hn'⟩ := hty
    exact ks162AltNoL3Two G I J₀ hJI hI7 hJ₀.1.2.2.2 n hn hn'
  ·
    exfalso
    obtain ⟨n, hn, hn'⟩ := hty
    exact ks162AltNoL3Two G I J₀ hJI (Or.inl hI7) hJ₀.1.2.2.2 n hn hn'

end CFSG.RankThree.PartTwo.Sec16
