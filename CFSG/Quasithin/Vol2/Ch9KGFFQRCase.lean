module

public import CFSG.Quasithin.Vol2.Ch9KGFFQRType
import CFSG.Models.PGLSimple
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases11

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Case

variable {Q : Type} [Group Q] [Finite Q]

theorem not_a314_thirteen {B L : Subgroup Q} (hBL : B < L) (hq : CFSG.IsQuasisimple ↥L) :
    L ≠ B ⊔ oddCoreSub L := by
  intro h
  have hBL' : B ≤ L := hBL.le
  set B' := B.subgroupOf L with hB'
  have hO := oddCore_le_center_of_quasisimple hq
  have htop : (⊤ : Subgroup ↥L) = B' ⊔ Subgroup.center ↥L := by
    have h1 := congrArg (fun H : Subgroup Q => H.subgroupOf L) h
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hBL' (Subgroup.map_subtype_le _),
      A4.subgroupOf_map_subtype'] at h1
    exact le_antisymm (h1.le.trans (sup_le_sup_left hO _)) le_top
  have hZN : Subgroup.center ↥L ≤ Subgroup.normalizer (B' : Set ↥L) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro b
    rw [← Subgroup.mem_center_iff.1 hz b, mul_inv_cancel_right]
  have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ B' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [htop] at hx hy
    obtain ⟨b, hb, z, hz, rfl⟩ := QuasithinUnique.Setup.Family.mem_sup_of_le_normalizer hZN hx
    obtain ⟨b', hb', z', hz', rfl⟩ := QuasithinUnique.Setup.Family.mem_sup_of_le_normalizer hZN hy
    rw [H13.A7.commutatorElement_mul_center hz hz']
    exact B'.mul_mem (B'.mul_mem (B'.mul_mem hb hb') (B'.inv_mem hb)) (B'.inv_mem hb')
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := hq.1.commutator_eq_top
  rw [hperf] at hcomm
  apply hBL.ne
  apply le_antisymm hBL'
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hcomm (Subgroup.mem_top (⟨x, hx⟩ : ↥L)))

theorem isSimpleGroup_statedProj_statedSL_two {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
  CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K le_rfl (Or.inr (by omega)) (Or.inr (by omega))

theorem isPSL_two_centerQuot {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) {p f : ℕ}
    (h : IsPSL 2 p f X) (h4 : 4 ≤ p ^ f) : IsPSL 2 p f (X ⧸ Subgroup.center X) := by
  obtain ⟨a, K, k1, k2, hK, ⟨e⟩⟩ := h
  obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective
    (isSimpleGroup_statedProj_statedSL_two (by rw [hK]; exact h4))
  exact ⟨a, K, k1, k2, hK, ⟨eq⟩⟩

theorem isPSL_three_centerQuot {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) {p f : ℕ}
    (ha : StatedLieAdmissible .PSL 3 p f)
    (h : IsPSL 3 p f X ∨ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* ↥(StatedSL 3 K))) :
    IsPSL 3 p f (X ⧸ Subgroup.center X) := by
  rcases h with ⟨a, K, k1, k2, hK, ⟨e⟩⟩ | ⟨K, k1, k2, hK, ⟨e⟩⟩
  · obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective
      (Insp9.isSimpleGroup_statedProj_statedSL_three K)
    exact ⟨a, K, k1, k2, hK, ⟨eq⟩⟩
  · obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq
      ((QuotientGroup.mk' _).comp e.toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp e.surjective)
      (Insp9.isSimpleGroup_statedProj_statedSL_three K)
    exact ⟨ha, K, k1, k2, hK, ⟨eq⟩⟩

theorem isSporadic_centerQuot {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    {s : TauCeti.SporadicName} (hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s))
    (h : IsSporadic s X ∨ IsHat X (CFSG.Blueprint.NativeSporadic.Carrier s)) :
    IsSporadic s (X ⧸ Subgroup.center X) := by
  rcases h with h | ⟨-, -, he⟩
  · obtain ⟨e⟩ := h
    exact nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective hs
  · exact he

theorem a314Type_centerQuot
    {T B L : Subgroup Q} (hBL : B < L) (hq : CFSG.IsQuasisimple ↥L)
    (h314 : A314Statement T B L) : A314Type (↥L ⧸ Subgroup.center ↥L) := by
  rcases h314 with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, ⟨s, h4⟩, -⟩ | ⟨-, h5, -⟩ |
    ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ |
    ⟨-, h11, -⟩ | ⟨-, -, h12, -⟩ | ⟨-, h13⟩ | ⟨-, p, hp, hp5, -, h14⟩
  · rcases h1 with h | h | h | h | h
    · exact A314Type.psl34 (isPSL_three_centerQuot hq h.1 (Or.inl h))
    · obtain ⟨K, k1, k2, hK, he⟩ := h
      exact A314Type.psl34 (isPSL_three_centerQuot hq ⟨Nat.prime_two, by norm_num, by norm_num,
        by decide, by decide⟩ (Or.inr ⟨K, k1, k2, by rw [hK]; norm_num, he⟩))
    · obtain ⟨a, K, k1, k2, hK, ⟨e⟩⟩ := h
      have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2
        (by norm_num) (Or.inl (Or.inr (by rw [hK]; norm_num)))
      obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective hs
      exact A314Type.sp44 ⟨a, K, k1, k2, hK, ⟨eq⟩⟩
    · obtain ⟨a, K, k1, k2, hK, ⟨e⟩⟩ := h
      obtain ⟨eq⟩ := nonempty_centerQuot_equiv_centerQuot hq.1 e
      exact A314Type.g24 ⟨a, K, k1, k2, hK, ⟨eq⟩⟩
    · obtain ⟨a, K, k1, k2, hK, σ, hσ, ⟨e⟩⟩ := h
      obtain ⟨eq⟩ := nonempty_centerQuot_equiv_centerQuot hq.1 e
      exact A314Type.d43 ⟨a, K, k1, k2, hK, σ, hσ, ⟨eq⟩⟩
  · have hs : IsSimpleGroup ↥(alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    refine A314Type.alt7 ?_
    rcases h2 with h | ⟨-, -, he⟩
    · obtain ⟨e⟩ := h
      exact nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective hs
    · exact he
  · rcases h3 with h | ⟨p, hp, hp5, -, h⟩
    · exact A314Type.psl225 (isPSL_two_centerQuot hq h (by norm_num))
    · have h11 := H13.A7.eleven_le_of_sq_mod_five hp hp5
      exact A314Type.psl2p ⟨p, hp, by omega, isPSL_two_centerQuot hq h (by rw [pow_one]; omega)⟩
  · cases s with
    | true =>
      exact A314Type.psl35 (isPSL_three_centerQuot hq
        ⟨Nat.prime_five, le_rfl, by norm_num, by decide, by decide⟩ h4)
    | false =>
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      refine A314Type.psu35 ?_
      rcases h4 with ⟨a, K, k1, k2, hK, ⟨e⟩⟩ | ⟨K, k1, k2, hK, ⟨e⟩⟩
      · obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq e.toMonoidHom e.surjective
          (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 5 1 hK 3 le_rfl
            (by decide))
        exact ⟨a, K, k1, k2, hK, ⟨eq⟩⟩
      · obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq
          ((QuotientGroup.mk' _).comp e.toMonoidHom)
          ((QuotientGroup.mk'_surjective _).comp e.surjective)
          (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 5 1
            (by rw [hK]; norm_num) 3 le_rfl (by decide))
        exact ⟨⟨Nat.prime_five, le_rfl, le_rfl, by decide⟩, K, k1, k2, by rw [hK]; norm_num,
          ⟨eq⟩⟩
  · exact A314Type.psl35 (isPSL_three_centerQuot hq
      ⟨Nat.prime_five, le_rfl, by norm_num, by decide, by decide⟩ h5)
  · exact A314Type.m22 (isSporadic_centerQuot hq CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2 h6)
  · exact A314Type.m23
      (isSporadic_centerQuot hq CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 (Or.inl h7))
  · exact A314Type.j1 (isSporadic_centerQuot hq CFSG.Sporadic.J1.fam_j1_simplicity.2.2 (Or.inl h8))
  · exact A314Type.j2 (isSporadic_centerQuot hq CFSG.Sporadic.J2.fam_j2_simplicity.2.2 (Or.inl h9))
  · exact A314Type.j4
      (isSporadic_centerQuot hq CFSG.Sporadic.J4.fam_j4_simplicity.2.2 (Or.inl h10))
  · exact A314Type.hs
      (isSporadic_centerQuot hq CFSG.Sporadic.HS.fam_hs_simplicity.2.2 (Or.inl h11))
  · exact A314Type.ru
      (isSporadic_centerQuot hq CFSG.Sporadic.Ru.fam_ru_simplicity.2.2 (Or.inl h12))
  · exact absurd h13 (not_a314_thirteen hBL hq)
  · obtain ⟨e14⟩ := h14
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have h11 := H13.A7.eleven_le_of_sq_mod_five hp hp5
    have hs : IsSimpleGroup (StatedProj (StatedSL 2 (ZMod p))) :=
      isSimpleGroup_statedProj_statedSL_two (by rw [Nat.card_zmod]; omega)
    set f : ↥L →* StatedProj (StatedSL 2 (ZMod p)) :=
      ((projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p)).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))))).comp
        (e14.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥L))) with hf
    have hfs : Function.Surjective f :=
      ((projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod p)).surjective.comp
        (QuotientGroup.mk'_surjective _)).comp
        (e14.surjective.comp (QuotientGroup.mk'_surjective _))
    obtain ⟨eq⟩ := nonempty_centerQuot_equiv_simple hq f hfs hs
    exact A314Type.psl2p ⟨p, hp, by omega, ⟨hp, le_rfl, le_rfl, by simp; omega, by simp; omega⟩,
      ZMod p, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨eq⟩⟩

end Case

end CFSG.Quasithin.H13.Ch9.KGFF
