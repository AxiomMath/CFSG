module

public import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsOrders
import CFSG.RankThree.PartTwo.Sec19.Step1917StepsBasic
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec19.Step1918ProofEnd

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step1917JPar :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M →
    ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c →
    A ≤ Subgroup.normalizer (K : Set G) →
    ∀ n : ℕ, 1 ≤ n →
    (Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))) →
    ∀ P : Subgroup (K ⧸ CFSG.pCore 2 K), IsProperParabolic P →
    (∀ a ∈ A, ∀ k k' : K, (k' : G) = a * k * a⁻¹ →
      (k : K ⧸ CFSG.pCore 2 K) ∈ P → (k' : K ⧸ CFSG.pCore 2 K) ∈ P) →
    False

namespace Step1917Steps

variable {G : Type} [Group G] [Finite G]

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p e : ℕ} [Fact p.Prime]
    (φ : Y ≃* X) (h : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi Y p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩

theorem kStar_of_alt
    (h1913 : Step1913)
    {A L E M K : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M) (hLK : L ≤ K)
    (halt : Step1917Proof.Alt1915W L K c)
    (hlist : IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K)) :
    (∃ n : ℕ, 1 ≤ n ∧
      (Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n)))) ∧
      IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) := by
  rcases halt with hKL | ⟨p, e, hp, he, -, hKq, -⟩ | ⟨n, -, -, hD4, -⟩
  ·
    obtain ⟨ι, -⟩ := Step1918Proof.exists_quotientEquiv hLK hKL
    refine kStar_of_source ?_ hlist
    rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | ⟨⟨ψ⟩⟩
    · exact Or.inl ⟨p, e, hp, he, isoLThreePi_of_mulEquiv ι.symm hiso⟩
    · exact Or.inr ⟨ι.symm.trans ψ⟩
  ·
    exact kStar_of_source (Or.inl ⟨p, 3 * e, hp, by omega, hKq⟩) hlist
  ·
    exfalso
    rcases hlist with h | h
    · exact Step1911Proof.not_isList194_of_trialityD4 h hD4
    · exact Step1911Proof.not_isSmall194_of_trialityD4 h hD4

omit [Finite G] in
theorem conj_mem_starIm {K H : Subgroup G} {a : G} (haH : a ∈ H)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) {k k' : K} (hk' : (k' : G) = a * k * a⁻¹)
    (hk : (k : K ⧸ CFSG.pCore 2 K) ∈ starIm K H) : (k' : K ⧸ CFSG.pCore 2 K) ∈ starIm K H := by
  obtain ⟨x, hxH, hx⟩ := hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Step1911EndProof.mem_pCore_iff] at hx
  have hax : a * (x : G) * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp haK x).mp x.2
  refine ⟨⟨a * (x : G) * a⁻¹, hax⟩, Subgroup.mem_subgroupOf.mpr
    (H.mul_mem (H.mul_mem haH (Subgroup.mem_subgroupOf.mp hxH)) (H.inv_mem haH)), ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Step1911EndProof.mem_pCore_iff]
  have haO : a ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K haK
  have h1 := (Subgroup.mem_normalizer_iff.mp haO _).mp hx
  convert h1 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
  group

end Step1917Steps

open Step1917Steps in
theorem step1917J_of
    (h1913 : Step1913) (hpar : Step1917JPar) : Step1917J := by
  intro G _ _ A c L E M hctx hLM d hdD _ _ H hH _ K hK hLK halt _ hlist hpar'
  obtain ⟨⟨n, hn, hiso⟩, hA10⟩ := kStar_of_alt h1913 hctx hLK halt hlist
  have hP : IsProperParabolic (starIm K H) := by
    rcases hpar' with ⟨-, h⟩ | ⟨⟨φ⟩, -⟩
    · exact h
    · exact (hA10.false φ).elim
  obtain ⟨-, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hAM := le_M h1913 hctx
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Step1918Proof.map_conj_eq_of_mem hctx hZ hK hLK hFL hF hF9 (hAM ha))
  have hAH : A ≤ H := le_H (Step1916Proof2.isE27_A hctx).1.1 hdD.1 hH.2
  exact hpar G A c L E M hctx hLM K hK hLK halt hAK n hn hiso (starIm K H) hP
    fun a ha k k' hk' hk => conj_mem_starIm (hAH ha) (hAK ha) hk' hk

end CFSG.RankThree.PartTwo.Sec19
