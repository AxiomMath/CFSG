module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalSection
public import CFSG.Blueprint.Catalog
import CFSG.RankThree.GF2n.Stroth80.Sec7TailLeviQuotient
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.ParabolicRadicalLevi
import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Blueprint.ChevalleyWeyl
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

section Levi

variable {τ : Tag} {K : Type} [Field K]

private theorem parabolicRadical_subgroupOf_normal (J : Set (Fin τ.rank)) :
    ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J)).Normal :=
  (parabolic_root_radical_Levi_factors (τ := τ) (K := K) J).2.1

attribute [local instance] parabolicRadical_subgroupOf_normal

private theorem closure_levi_eq_rootSpan (J : Set (Fin τ.rank)) :
    Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} =
      rootSpan τ K {α | ∃ j ∈ J, α = Pi.single j 1 ∨ α = -Pi.single j 1} := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨j, hj, c, rfl | rfl⟩
    · have hx : xUnit τ K j c ∈ rootSubgroup τ K (Pi.single j 1) := by
        rw [← pinnedX_single]
        exact Subgroup.subset_closure ⟨c, rfl⟩
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ⟨j, hj, Or.inl rfl⟩ hx)
    · have hy : yUnit τ K j c ∈ rootSubgroup τ K (-Pi.single j 1) := by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨c, rfl⟩
      exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ⟨j, hj, Or.inr rfl⟩ hy)
  · refine iSup₂_le fun α hα => ?_
    obtain ⟨j, hj, rfl | rfl⟩ := hα
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inl rfl⟩
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩

private theorem torusGroup_le_normalizer_levi (J : Set (Fin τ.rank)) :
    torusGroup τ K ≤ Subgroup.normalizer ((Subgroup.closure
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  rw [closure_levi_eq_rootSpan]
  refine torusGroup_le_normalizer_rootSpan ?_
  rintro α ⟨j, -, rfl | rfl⟩
  · exact isRoot_single τ j
  · exact isRoot_neg_single τ j

private theorem commutator_parabolicQuotient_le (J : Set (Fin τ.rank)) :
    commutator (↥(parabolicSubgroup τ K J) ⧸
        (parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J)) ≤
      ((Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}).subgroupOf
        (parabolicSubgroup τ K J)).map (QuotientGroup.mk'
          ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J))) := by
  have hLevi := parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
  have hMP : parabolicLevi τ K J ≤ parabolicSubgroup τ K J := hLevi.2.2.2.1
  have hHN := torusGroup_le_normalizer_levi (K := K) J
  refine commutator_quotient_le_map_of_factor hLevi.1 (le_sup_left.trans hMP)
    (le_sup_right.trans hMP) (fun g hg => ?_) hHN (triangular_borel_structure.{0, 0} τ K).1
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hg⟩, -⟩ := hLevi.2.2.2.2.2.2.1 g hg
  have hm' : m ∈ ((torusGroup τ K : Set (ModGL τ K)) *
      (Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c} :
        Set (ModGL τ K))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN]
    exact hm
  obtain ⟨h, hh, l, hl, rfl⟩ := hm'
  exact ⟨q, hq, h, hh, l, hl, hg⟩

private theorem nonempty_mulEquiv_levi (J : Set (Fin τ.rank)) :
    Nonempty (↥(((Subgroup.closure
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}).subgroupOf
        (parabolicSubgroup τ K J)).map (QuotientGroup.mk'
          ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J)))) ≃*
      ↥(Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c})) := by
  have hLevi := parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
  have hMP : parabolicLevi τ K J ≤ parabolicSubgroup τ K J := hLevi.2.2.2.1
  refine nonempty_mulEquiv_map_subgroupOf_of_inf_eq_bot (le_sup_right.trans hMP) ?_
  rw [eq_bot_iff, ← hLevi.2.2.2.2.1, inf_comm]
  exact inf_le_inf_left _ le_sup_right

private theorem nonempty_mulEquiv_levi_singleton_sl2 [CharP K 2] (i : Fin τ.rank) :
    Nonempty (↥(Subgroup.closure {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
      g = xUnit τ K j c ∨ g = yUnit τ K j c}) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨ρ, -, -, -, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  have hL : Subgroup.closure {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
      g = xUnit τ K j c ∨ g = yUnit τ K j c} = ρ.range := by
    rw [hrange]
    congr 1
    ext g
    simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_range]
    constructor
    · rintro ⟨c, rfl | rfl⟩
      · exact Or.inl ⟨c, rfl⟩
      · exact Or.inr ⟨c, rfl⟩
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨c, Or.inl rfl⟩
      · exact ⟨c, Or.inr rfl⟩
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    obtain ⟨l, hl2, hgl⟩ := hker g hg
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hl1 : (l : K) = 1 := by
      have h0 : ((l : K) - 1) ^ 2 = 0 := by linear_combination hl2 + (1 - (l : K)) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
    rw [hl1, one_smul] at hgl
    exact Subgroup.mem_bot.2 (Subtype.ext hgl)
  exact ⟨(MulEquiv.subgroupCongr hL).trans (MonoidHom.ofInjective hρ).symm⟩

private theorem levi_dichotomy [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (J : Set (Fin τ.rank)) (i : Fin τ.rank) (hJ : J ⊆ {i}) :
    ((Subgroup.closure {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}).subgroupOf
        (parabolicSubgroup τ K J)).map (QuotientGroup.mk'
          ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J))) = ⊥ ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (s : ℕ), Nat.card F = 2 ^ s ∧
        ∃ ι : ↥(((Subgroup.closure
            {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}).subgroupOf
              (parabolicSubgroup τ K J)).map (QuotientGroup.mk'
                ((parabolicRadical τ K J).subgroupOf (parabolicSubgroup τ K J)))) →*
            Matrix.SpecialLinearGroup (Fin 2) F, Function.Injective ι := by
  rcases Set.subset_singleton_iff_eq.1 hJ with rfl | rfl
  · left
    have hgen : {g : ModGL τ K | ∃ j ∈ (∅ : Set (Fin τ.rank)), ∃ c : K,
        g = xUnit τ K j c ∨ g = yUnit τ K j c} = ∅ := by
      ext g
      simp
    rw [hgen, Subgroup.closure_empty, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · right
    obtain ⟨e₁⟩ := nonempty_mulEquiv_levi (K := K) ({i} : Set (Fin τ.rank))
    obtain ⟨e₂⟩ := nonempty_mulEquiv_levi_singleton_sl2 (K := K) i
    exact ⟨K, inferInstance, inferInstance, m, hK, (e₁.trans e₂).toMonoidHom,
      (e₁.trans e₂).injective⟩

end Levi

section Parabolic

variable {τ : Tag} {K : Type} [Field K] [Finite K]

private theorem exists_mulEquiv_map_eq_parabolicSubgroup {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] [CharP K p] (ψ : X ≃* ↥(adjointGroup τ K)) {P : Subgroup X}
    (S₂ : Sylow p X) (hSP : Subgroup.normalizer ((S₂ : Subgroup X) : Set X) ≤ P) :
    ∃ ψ' : X ≃* ↥(adjointGroup τ K),
      (P.map ψ'.toMonoidHom).map (adjointGroup τ K).subtype =
        parabolicSubgroup τ K
          {i | weylElt τ K i 1 ∈ (P.map ψ'.toMonoidHom).map (adjointGroup τ K).subtype} := by
  classical
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv X ψ.toEquiv
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨U₀, hU₀⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀
  let S' : Sylow p ↥(adjointGroup τ K) := Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective S₂
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(adjointGroup τ K) S' U₀
  let ψ' : X ≃* ↥(adjointGroup τ K) := ψ.trans (MulAut.conj c)
  refine ⟨ψ', ?_⟩
  have hS'U : (S₂ : Subgroup X).map ψ'.toMonoidHom = U₀ := by
    rw [← hc, Sylow.coe_subgroup_smul]
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hBle : borelGroup τ K ≤ (P.map ψ'.toMonoidHom).map (adjointGroup τ K).subtype := by
    intro b hb
    have hbC : b ∈ adjointGroup τ K :=
      ((triangular_borel_structure τ K).2.2.2.2.2.2.2.2.2.2.2 K).1 hb
    have hBN : b ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [← (borel_self_normalizers τ K).1] at hb
      exact hb.2
    have hbN : (⟨b, hbC⟩ : ↥(adjointGroup τ K)) ∈
        Subgroup.normalizer ((U₀ : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
      rw [hU₀, Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.1 hBN (u : ModGL τ K)
      exact ⟨fun hu => Subgroup.mem_subgroupOf.2 (this.1 (Subgroup.mem_subgroupOf.1 hu)),
        fun hu => Subgroup.mem_subgroupOf.2 (this.2 (Subgroup.mem_subgroupOf.1 hu))⟩
    rw [← hS'U, ← Subgroup.map_equiv_normalizer_eq] at hbN
    obtain ⟨x, hx, hxb⟩ := hbN
    exact ⟨⟨b, hbC⟩, ⟨x, hSP hx, hxb⟩, rfl⟩
  exact eq_parabolicSubgroup_of_borelGroup_le hBle (Subgroup.map_subtype_le _)

end Parabolic

attribute [local instance] parabolicRadical_subgroupOf_normal

theorem radicalTwoSubgroup_g2 :
    ∀ (X : Type) [Group X] [Finite X],
      (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) →
      ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
        inSubgroup (pCore 2) (Subgroup.normalizer (U : Set X)) = U →
        ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set X)) ⧸
            U.subgroupOf (Subgroup.normalizer (U : Set X))),
          S.Normal → IsQuasisimple S →
            ∃ (s : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 2 ≤ s ∧ Nat.card K = 2 ^ s ∧
              ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
                Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL 2 K)) := by
  classical
  rintro X _ _ ⟨m, -, hX⟩ U hU1 hU2 hrad S - hSq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  let ψ : X ≃* ↥(adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  haveI : Finite ↥(adjointGroup .G2 K) := Finite.of_equiv X ψ.toEquiv
  obtain ⟨S₂, P, hPtop, hNP, -, -, hSP⟩ :=
    (CFSG.LieType.BorelTits.Holds.of_mulEquiv ψ.symm (holds_adjointGroup_tag .G2 K 2)) U hU1 hU2
  obtain ⟨ψ', hP'⟩ := exists_mulEquiv_map_eq_parabolicSubgroup ψ S₂ hSP
  generalize hJdef : {i | weylElt .G2 K i 1 ∈
    (P.map ψ'.toMonoidHom).map (adjointGroup .G2 K).subtype} = J at hP'
  have hJ : J ≠ Set.univ := by
    rintro rfl
    apply hPtop
    rw [(standard_parabolic_cells .G2 K).2.2.2.2.2.1] at hP'
    rw [eq_top_iff]
    intro x _
    have hx : ((ψ' x : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
        (P.map ψ'.toMonoidHom).map (adjointGroup .G2 K).subtype := by
      rw [hP']
      exact (ψ' x).2
    obtain ⟨y, ⟨z, hz, rfl⟩, hyx⟩ := hx
    have hzx : z = x := ψ'.injective (Subtype.ext hyx)
    rw [← hzx]
    exact hz
  obtain ⟨k, hk⟩ : ∃ k, k ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  have hother : ∀ k : Fin Tag.G2.rank, ∃ i, i ≠ k := by decide
  have htwo : ∀ k j₁ j₂ : Fin Tag.G2.rank, j₁ ≠ k → j₂ ≠ k → j₁ = j₂ := by decide
  obtain ⟨i, hik⟩ := hother k
  have hJi : J ⊆ {i} := fun j hj => htwo k j i (fun h => hk (h ▸ hj)) hik
  have hLevi := parabolic_root_radical_Levi_factors (τ := .G2) (K := K) J
  let χ : ↥(Subgroup.normalizer (U : Set X)) →* ModGL .G2 K :=
    (adjointGroup .G2 K).subtype.comp
      (ψ'.toMonoidHom.comp (Subgroup.normalizer (U : Set X)).subtype)
  have hχ : Function.Injective χ :=
    Subtype.val_injective.comp (ψ'.injective.comp Subtype.val_injective)
  have hmemP : ∀ n, χ n ∈ parabolicSubgroup .G2 K J := fun n => by
    rw [← hP']
    exact ⟨ψ' n, ⟨n, hNP n.2, rfl⟩, rfl⟩
  let f : ↥(Subgroup.normalizer (U : Set X)) →* ↥(parabolicSubgroup .G2 K J) ⧸
      (parabolicRadical .G2 K J).subgroupOf (parabolicSubgroup .G2 K J) :=
    (QuotientGroup.mk' _).comp (χ.codRestrict _ hmemP)
  have hmemQ : ∀ n : ↥f.ker, χ n ∈ parabolicRadical .G2 K J := fun n => by
    have h := n.2
    rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  have hQp : IsPGroup 2 (parabolicRadical .G2 K J) :=
    (hLevi.2.2.2.2.2.2.2.2.2.2.2.2 2).2.1
  have hf : IsPGroup 2 f.ker :=
    hQp.of_injective ((χ.comp f.ker.subtype).codRestrict _ hmemQ) fun a b h =>
      Subtype.ext (hχ (congrArg (Subtype.val : ↥(parabolicRadical .G2 K J) → ModGL .G2 K) h))
  exact exists_statedProj_of_hom hrad f hf _
    ((Subgroup.commutator_mono le_top le_top).trans (commutator_parabolicQuotient_le J))
    (levi_dichotomy hK J i hJi) S hSq

end CFSG.RankThree.GF2n.Stroth80

end
