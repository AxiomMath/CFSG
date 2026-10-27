module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


@[expose] def Item4_29Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → aschbacherSolvableCore 3 G = ⊥ →
    partTwoE G = partTwoF G → ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 →
    ∀ L : Subgroup G, IsComponent L → A ≤ Subgroup.normalizer (L : Set G) →
    A ⊓ Subgroup.centralizer (L : Set G) = ⊥ → ¬ L ≤ Subgroup.centralizer {c} →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M22) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.J2)) →
      Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G) →
      (Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ Nonempty (L ≃* alternatingGroup (Fin 10))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧ IsoLThreePi L 2 (3 * n) ∧
        InducesStdKind L c .field) ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧ Blueprint.ChevalleyExceptionalModel L .trialityD4 2 n ∧
        InducesStdKind L c .graphField)

end Certs

namespace Res429

variable {G : Type} [Group G] [Finite G]

theorem eq_top_or_le_center_of_isSubnormal {Q : Type*} [Group Q] (hQ : IsQuasisimple Q)
    {P : Subgroup Q} (hP : P.IsSubnormal) : P = ⊤ ∨ P ≤ Subgroup.center Q := by
  induction hP with
  | top => exact Or.inl rfl
  | step H K hHK _ hN ih =>
    rcases ih with rfl | hK
    · have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN))
      exact CFSG.LocalCores.quasisimple_normal_subgroups hQ hHn
    · exact Or.inr (hHK.trans hK)

theorem eq_of_le_of_isSubnormal_of_isQuasisimple {Γ : Type*} [Group Γ] {K J : Subgroup Γ}
    (hKJ : K ≤ J) (hJ : IsQuasisimple ↥J) (hKp : Group.IsPerfect ↥K) (hK1 : Nontrivial ↥K)
    (hKs : (K.subgroupOf J).IsSubnormal) : K = J := by
  rcases eq_top_or_le_center_of_isSubnormal hJ hKs with htop | hcen
  · exact le_antisymm hKJ (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    have hcomm : ∀ a b : ↥K, a * b = b * a := by
      intro a b
      have ha : (⟨a, hKJ a.2⟩ : ↥J) ∈ Subgroup.center ↥J := hcen a.2
      have h := Subgroup.mem_center_iff.mp ha ⟨b, hKJ b.2⟩
      exact Subtype.ext (congrArg Subtype.val h).symm
    exact Group.IsPerfect.not_isSolvable ↥K (Group.isSolvable_of_comm hcomm)

omit [Finite G] in
theorem eq_of_isComponent_of_le_centralizer {L : Subgroup G} {c : G}
    (hL : IsComponent L) (hLc : L ≤ Subgroup.centralizer {c})
    (K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G)) (hK : IsComponent K) :
    K.map (L ⊓ Subgroup.centralizer {c}).subtype = L := by
  have hML : L ⊓ Subgroup.centralizer {c} ≤ L := inf_le_left
  have hLM : L ≤ L ⊓ Subgroup.centralizer {c} := le_inf le_rfl hLc
  have hK'M : K.map (L ⊓ Subgroup.centralizer {c}).subtype ≤ L ⊓ Subgroup.centralizer {c} :=
    Subgroup.map_subtype_le K
  have eK : ↥K ≃* ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) :=
    K.equivMapOfInjective _ (Subgroup.subtype_injective _)
  have hK'q : IsQuasisimple ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'1 : Nontrivial ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) := by
    have : Nontrivial (↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype) ⧸
        Subgroup.center ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype)) :=
      hK'q.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective
      (Subgroup.center ↥(K.map (L ⊓ Subgroup.centralizer {c}).subtype))).nontrivial
  have hsub : ((K.map (L ⊓ Subgroup.centralizer {c}).subtype).subgroupOf L).IsSubnormal := by
    have hsurj : Function.Surjective (Subgroup.inclusion hML) := by
      intro x
      exact ⟨⟨x, hLM x.2⟩, rfl⟩
    have h := hK.2.map hsurj
    have heq : K.map (Subgroup.inclusion hML) =
        (K.map (L ⊓ Subgroup.centralizer {c}).subtype).subgroupOf L := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        exact ⟨y, hy, Subtype.ext hyx⟩
    rwa [heq] at h
  exact eq_of_le_of_isSubnormal_of_isQuasisimple (hK'M.trans hML) hL.1 hK'q.1 hK'1 hsub

theorem inf_centralizer_eq_bot {A L K : Subgroup G} {c : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hKL : K ≤ L) (hLc : ¬ L ≤ Subgroup.centralizer {c})
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K : Set G)) :
    A ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxc : x ∈ Subgroup.zpowers c := by
    rw [hcent]
    exact ⟨hx.1, Subgroup.centralizer_le hKL hx.2⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hA.1.2 x hx.1) hx1
  have hzx : Subgroup.zpowers x = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hx3])
  have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.zpowers_le.mpr hx.2 (hzx ▸ Subgroup.mem_zpowers c)
  apply hLc
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hcL l hl

end Res429

open Res429

section Certs


theorem item4_29_of (h45 : Item4_5) (hO : Item4_29Outer) : Item4_29 := by
  intro G _ _ hG hθ hE A hA c hc hc1 L hL K hK K' hK' htype hcent
  by_cases hLc : L ≤ Subgroup.centralizer {c}
  · left
    rw [hK']
    exact eq_of_isComponent_of_le_centralizer hL hLc K hK
  · right
    have hLθ := CFSG.RankThree.mem_thetaComponents_of_isComponent Nat.prime_three hθ hL
    have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
      h45 G hG A hA.isPGroup (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L hLθ
    have hK'L : K' ≤ L := by
      rw [hK']
      exact (Subgroup.map_subtype_le K).trans inf_le_left
    have hAC := inf_centralizer_eq_bot hA hc hc1 hK'L hLc hcent
    exact hO G hG hθ hE A hA c hc hc1 L hL hAL hAC hLc K hK K' hK' htype hcent

end Certs

end CFSG.RankThree.PartTwo.Sec4
