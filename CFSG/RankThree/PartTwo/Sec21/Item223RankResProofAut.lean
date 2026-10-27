module

public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.Explicit
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

theorem rankG2_holds :
    ∀ (X : Type) [Group X] (p : ℕ) [Fact p.Prime], 3 < p →
      ChevalleyExceptionalModel X .G2 p 1 → CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3 :=
  fun X _ p _ hp hX => (g2OddThreeRankTwo_holds p hp X hX).trans (by norm_num)

section Even


namespace Item223RankResProof

theorem adjointG2_even_card_le_nine {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (F : Subgroup (adjointGroup .G2 K))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Nat.card F ≤ 9 := by
  obtain ⟨e⟩ := CFSG.Quasithin.B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hn
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  let φ : adjointGroup .G2 K ≃* cayleyGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e.symm
  have := cayleyGroup_card_le_nine (F.map φ.toMonoidHom) (Sec4.isElemAbelian_map _ hF)
  rwa [Subgroup.card_map_of_injective φ.injective] at this

end Item223RankResProof

open Item223RankResProof

theorem rankAutG2_holds : ∀ (X : Type) [Group X] (n : ℕ),
    ChevalleyExceptionalModel X .G2 2 n → CFSG.pRank 3 (MulAut X) ≤ 3 := by
  intro X _ n hX
  have hn := (CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hX).1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  have : CharP K 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hK
  refine Sec4.pRank_three_le_of_card_le (Sec4.card_le_of_mulEquiv_mulAut e fun B hB => ?_)
  obtain ⟨ec⟩ := CFSG.Quasithin.B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hn
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hfin : Finite (adjointGroup .G2 K) := by
    have : Finite (cayleyGroup K) :=
      Finite.of_injective _ (zornGL_injective.comp (Subtype.val_injective (p := fun g =>
        g ∈ cayleyGroup K)))
    exact Finite.of_equiv _
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
        ec.symm).symm.toEquiv
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .G2 K) with hNdef
  have hCN : Subgroup.zpowers (CFSG.LocalAnalysis.EvenBN.G2.Model.fieldAut K) ≤
      Subgroup.normalizer (N : Set (MulAut (adjointGroup .G2 K))) := by
    have : N.Normal := inner_normal _
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hBNC : ∀ b ∈ B, ∃ m ∈ N, ∃ c ∈ Subgroup.zpowers
      (CFSG.LocalAnalysis.EvenBN.G2.Model.fieldAut K), b = m * c := by
    intro b _
    obtain ⟨g, k, -, rfl⟩ :=
      CFSG.LocalAnalysis.EvenBN.G2.Model.exists_eq_conj_mul_fieldAut_pow hK hn b
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, _, pow_mem (Subgroup.mem_zpowers _) k, rfl⟩
  have h1 := Sec4.card_le_three_mul_card_inf hB inferInstance hCN hBNC
  have hconj : Function.Injective
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    (CFSG.LocalAnalysis.EvenBN.G2.Model.yamada_3_18 hK hn).1
  set E := (B ⊓ N).comap (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))
  have hle : B ⊓ N ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range :=
    inf_le_right
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    have h := Subgroup.card_map_of_injective (K := E) hconj
    rw [Subgroup.map_comap_eq_self hle] at h
    exact h.symm
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hBc _ (Subgroup.mem_comap.mp x.2).1 _ (Subgroup.mem_comap.mp y.2).1
    · rw [map_pow, map_one]
      exact hB.2 _ (Subgroup.mem_comap.mp hx).1
  have h9 := adjointG2_even_card_le_nine hK hn E hE
  omega

end Even

end CFSG.RankThree.PartTwo.Sec21
