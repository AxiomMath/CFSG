module

public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofLinear
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofM22
public import CFSG.RankThree.PartTwo.Sec21.Item218ProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)

open CFSG.Blueprint

theorem not_isList218_of_item218 (h218 : Item218) {G : Type} [Group G] [Finite G]
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) : ¬ IsList218 L := by
  obtain ⟨hM24, hHe, hJ2, hRu, hJ4, hG2, hD4⟩ := h218 G A E U c L hpair
  rintro (e | e | e | e | e | ⟨n, hn⟩ | ⟨n, hn⟩)
  · exact (e.elim hM24.false).elim
  · exact (e.elim hHe.false).elim
  · exact (e.elim hJ2.false).elim
  · exact (e.elim hRu.false).elim
  · exact (e.elim hJ4.false).elim
  · exact hG2 n hn
  · exact hD4 n hn

theorem not_mem_zpowers_symm {G : Type} [Group G] [Finite G] {a c : G} (ha3 : a ^ 3 = 1)
    (hc1 : c ≠ 1) (hac : a ∉ Subgroup.zpowers c) : c ∉ Subgroup.zpowers a := fun h =>
  hac (mem_zpowers_of_mem_zpowers ha3 hc1 h)

section Certs

theorem isList218_of_inf_le_normalizer (h211 : Item211) (h213 : Item213) (h217 : Item217)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hL3 : Item2115LThree) {G : Type} [Group G]
    [Finite G] {A E U₀ X : Subgroup G} {a c : G} (hpair : Sec21Pair G A E U₀ a X)
    (hU₀ : U₀ ∈ fourGroupsMinus E) (hcA : c ∈ A) (hca : c ∉ Subgroup.zpowers a)
    (hcU : c ∈ Subgroup.centralizer (U₀ : Set G))
    (hXc : X ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) : IsList218 X := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hXa' : X ∈ thetaComponentsAt 3 a := (lZeroStarAt_subset A a) hpairs.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa'
  have hXa : ∀ x ∈ X, x * a * x⁻¹ = a := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hx), mul_inv_cancel_right]
  have h4Q : orderOf (QuaternionGroup.a 1 : QuaternionGroup 2) = 4 :=
    QuaternionGroup.orderOf_a_one
  have h4D : orderOf (DihedralGroup.r 1 : DihedralGroup 4) = 4 := DihedralGroup.orderOf_r_one
  have h8 : orderOf (CFSG.Semidihedral.r 4) = 8 := by
    rw [CFSG.Semidihedral.orderOf_r 4 (by norm_num)]
    rfl
  have h4S : orderOf (CFSG.Semidihedral.r 4 ^ 2) = 4 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [h8]; norm_num), h8]
  have four : ∀ {H : Type} [Group H], Nat.card A = 3 ^ 3 → Nonempty (starOf A X ≃* H) →
      ∀ h : H, orderOf h = 4 → False := fun h27 ⟨e⟩ h hh =>
    Item218Res2Proof.false_of_orderOf_four hAe (by rw [h27]; norm_num) haA hcA ha1 hca hXa hXc
      e hh
  have perm : Nat.card A = 3 ^ 4 → ∀ ψ : Equiv.Perm (Fin 4) →* MulAut A,
      Function.Injective ψ → (∀ x, ψ x ∈ starOf A X) → False := fun h81 ψ hψ hmem =>
    Item218Res2Proof.false_of_perm_fix hAe (by rw [h81]; norm_num) haA hcA ha1 hca hXa hXc ψ hψ
      hmem
  rcases h211 G A E U₀ a X hpair with ⟨-, hT, -⟩ | ⟨-, h27, hQ⟩ | ⟨-, h27, hSD⟩ |
      ⟨hM, -, -⟩ | ⟨hJ, -, -⟩ | ⟨hM, -, -⟩ | h7 | ⟨⟨n, -, -, h8⟩, -, -⟩ |
      ⟨-, h27, hD8⟩ | ⟨-, h81, ⟨e⟩⟩ | ⟨hJ, -, -⟩ | ⟨-, h27, hD8⟩ | ⟨-, h81, ⟨e⟩⟩
  · exact (Item218Res2Proof.not_le_normalizer_of_isTripleCover h45 h66 hpair hT hcA hca
      hXc).elim
  · exact (four h27 hQ _ h4Q).elim
  · exact (four h27 hSD _ h4S).elim
  · rcases hM with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl hJ))
  · rcases hM with e | e
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact (hL3 G A E U₀ a X c hpair hU₀ h7 hcA hca hcU hXc).elim
  · rcases h8 with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, h⟩)))))
  · exact (four h27 hD8 _ h4D).elim
  · exact (perm h81 ((starOf A X).subtype.comp e.symm.toMonoidHom)
      ((starOf A X).subtype_injective.comp e.symm.injective) fun x => (e.symm x).2).elim
  · exact (false_of_J3 (h213 G A E U₀ a X hpair) (h217 G A E U₀ a X hpair) hJ).elim
  · exact (four h27 hD8 _ h4D).elim
  · exact (perm h81 ((starOf A X).subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _)))
      ((starOf A X).subtype_injective.comp (e.symm.injective.comp fun x y h => by
        simpa using congrArg Prod.snd h))
      fun x => (e.symm _).2).elim

theorem item2115_of (h211 : Item211) (h213 : Item213) (h214 : Item214) (h215 : Item215)
    (h217 : Item217) (h218 : Item218) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) (hU4 : Item2115U4) : Item2115 := by
  intro G _ _ A E U c L hpair hWH
  by_cases hL : ∃ n : ℕ, Odd n ∧ Nonempty (L ≃* projSU 4 2 n)
  · exact hU4 G A E U c L hpair hL hWH
  obtain ⟨U₀, hU₀, hU₀L⟩ := (h214 G A E U c L hpair).mpr hL
  obtain ⟨a, haB, hac, X, -, haX⟩ := h215 G A E U c L hpair U₀ hU₀
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU₀.1
      mem_pair := haX }
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hca : c ∉ Subgroup.zpowers a :=
    not_mem_zpowers_symm (hAe.2 a (hpair.mem_E.2 haB.1)) hpairs.2.1 hac
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  have hcU : c ∈ Subgroup.centralizer (U₀ : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun u hu => Subgroup.mem_centralizer_singleton_iff.mp (hLC (hU₀L hu))
  exact not_isList218_of_item218 h218 hpair' (isList218_of_inf_le_normalizer h211 h213 h217 h45
    h66 hL3 hpair' hU₀ hcA hca hcU (inf_le_right.trans hWH))

theorem item218Step214_of (h211 : Item211) (h213 : Item213) (h217 : Item217)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hL3 : Item2115LThree) (hN : Item218Normal) :
    Item218Step214 := by
  intro G _ _ A E U c L U₀ b K hpair hL hU₀ hU₀L hb hbc _ hbK
  have hpair' : Sec21Pair G A E U₀ b K :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hU₀.1
      mem_pair := hbK }
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcb : c ∉ Subgroup.zpowers b :=
    not_mem_zpowers_symm (hAe.2 b (hpair.mem_E.2 hb.1)) hpairs.2.1 hbc
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt ((lZeroStarAt_subset A c) hpairs.2.2.1)
  have hcU : c ∈ Subgroup.centralizer (U₀ : Set G) := Subgroup.mem_centralizer_iff.mpr
    fun u hu => Subgroup.mem_centralizer_singleton_iff.mp (hLC (hU₀L hu))
  exact isList218_of_inf_le_normalizer h211 h213 h217 h45 h66 hL3 hpair' hU₀ hcA hcb hcU
    (inf_le_right.trans (hN G A E U c L hpair hL))

end Certs

section Item218

theorem item218_of_normal_final (h211 : Item211) (h213 : Item213) (h214 : Item214)
    (h215 : Item215) (h217 : Item217) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) (hN : Item218Normal) (hF : Item218Final) : Item218 :=
  item218_of_steps h214 h215 Item218Proof.kF218NotU4 hN
    (item218Step214_of h211 h213 h217 h45 h66 hL3 hN) hF

end Item218

end CFSG.RankThree.PartTwo.Sec21
