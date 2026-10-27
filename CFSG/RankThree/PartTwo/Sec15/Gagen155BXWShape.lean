module

import CFSG.RankThree.PartTwo.Sec15.Gagen155BXWCover
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155BXW

private theorem exists_split_of_cover_simple {T X : Type*} [Group T] [Group.IsPerfect T]
    [Group X] [IsSimpleGroup X] (e : T ≃* X) {V : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ :=
  exists_split_of_cover (ψ := MonoidHom.id X) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (φ := e.symm.toMonoidHom) e.symm.surjective hV hVq

private theorem exists_split_of_cover_quasisimple {T X : Type*} [Group T] [Group.IsPerfect T]
    [Group X] (hX : CFSG.IsQuasisimple X) (e : T ≃* X) {V : Subgroup T} (hV : V.IsSubnormal)
    (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ := by
  obtain ⟨-, hsimple, -⟩ := hX
  letI : IsSimpleGroup (X ⧸ Subgroup.center X) := hsimple
  exact exists_split_of_cover (ψ := QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (φ := e.symm.toMonoidHom) e.symm.surjective hV hVq

private theorem exists_split_of_cover_triple {T S : Type*} [Group T] [Group.IsPerfect T]
    [Group S] [IsSimpleGroup S] (h : Sec4.IsTripleCover T S) {V : Subgroup T}
    (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V) :
    ∃ E : Subgroup T, ⁅V, E⁆ = ⊥ ∧ Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧
      V ⊔ E = ⊤ := by
  obtain ⟨-, ⟨ε⟩⟩ := h
  obtain ⟨hψ, hk⟩ := Proof153Twin2.tripleCover_cover ε
  exact exists_split_of_cover hψ hk (φ := MonoidHom.id T) Function.surjective_id hV hVq

theorem exists_split_of_item148
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY2 A) :
    letI := ker148_normal hM.1.2
    ∀ V : Subgroup ↥(img148 A M (deltaZero A (lB A) M)), V.IsSubnormal →
      CFSG.IsQuasisimple ↥V →
      ∃ E : Subgroup ↥(img148 A M (deltaZero A (lB A) M)), ⁅V, E⁆ = ⊥ ∧
        Group.IsPerfect ↥E ∧ oPrimeResidualOf 3 E = E ∧ V ⊔ E = ⊤ := by
  intro V hV hVq
  let := ker148_normal hM.1.2
  haveI hperf : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h h148 hM.1
  haveI hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI hJ2s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI hONs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  have hA5nc : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  have hA6nc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  have hJ2nc : ¬ IsMulCommutative CFSG.Blueprint.NativeSporadic.J2 := by
    intro hcomm
    haveI := hcomm
    have hp := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative
      CFSG.Blueprint.NativeSporadic.J2
    rw [CFSG.Sporadic.J2.card_J2] at hp
    norm_num at hp
  have hA5p : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect _ hA5nc
  have hA6p : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect _ hA6nc
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect _ hJ2nc
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num <;> decide
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num <;> decide
  have hA5_3 : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [hA5card]; norm_num
  have hA6_3 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [hA6card]; norm_num
  have hJ2_3 : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [CFSG.Sporadic.J2.card_J2]; norm_num
  rcases (h148 M hM.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    haveI hsub : Subsingleton ↥(img148 A M (deltaZero A (lB A) M)) := by
      rw [hD]
      exact inferInstance
    refine ⟨⊥, Subgroup.commutator_bot_right V, ?_, ?_, ?_⟩
    · refine Group.IsPerfect.mk ?_
      apply le_antisymm
      · exact le_top
      · intro x hx
        rw [show x = 1 from Subsingleton.elim x 1]
        exact Subgroup.one_mem _
    · rw [oPrimeResidualOf]
      have h : oPrimeResidual 3
          ↥(⊥ : Subgroup ↥(img148 A M (deltaZero A (lB A) M))) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
      rw [h, Subgroup.map_bot]
    · rw [sup_bot_eq]
      apply le_antisymm le_top
      intro x hx
      rw [show x = 1 from Subsingleton.elim x 1]
      exact V.one_mem
  ·
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact exists_split_of_cover_quasisimple
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ hV hVq
    · exact exists_split_of_cover_simple φ hV hVq
    · haveI : Fact p.Prime := hp
      rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · haveI : IsSimpleGroup
            (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
        exact exists_split_of_cover_simple φ hV hVq
      · haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 p f) :=
          Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact exists_split_of_cover_simple φ hV hVq
    · exact exists_split_of_cover_triple h6 hV hVq
    · exact exists_split_of_cover_simple φ hV hVq
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, -, hU6, hV6⟩ |
        ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hU6, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
    · exact exists_split_of_cover_triple hON hV hVq
    ·
      haveI : U₀.Normal := hU₀
      haveI : V₀.Normal := hV₀
      obtain ⟨hψ₁, hk₁⟩ := Proof153Twin2.tripleCover_cover hU6.2.some
      obtain ⟨hψ₂, hk₂⟩ := Proof153Twin2.tripleCover_cover hV6.2.some
      exact exists_split_of_prod hsup hcomm hA6p hA6_3 hψ₁ hk₁ hA6p hA6_3 hψ₂ hk₂ hV hVq
    ·
      haveI : U₀.Normal := hU₀
      haveI : V₀.Normal := hV₀
      have hcomm' : ⁅U₀, V₀⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact Subgroup.commutator_le_inf U₀ V₀
      obtain ⟨hψ₁, hk₁⟩ := Proof153Twin2.tripleCover_cover hU6.2.some
      have hk₂ : eV.toMonoidHom.ker ≤ Subgroup.center ↥V₀ := by
        rw [MonoidHom.ker_eq_bot eV.toMonoidHom eV.injective]
        exact bot_le
      exact exists_split_of_prod hsup hcomm' hA6p hA6_3 hψ₁ hk₁ hA5p hA5_3
        (ψ₂ := eV.toMonoidHom) eV.surjective hk₂ hV hVq
    ·
      exact exists_split_of_mulEquiv_prod hA5p hA5_3 hA5p hA5_3 φ hV hVq
    ·
      exact exists_split_of_cover_simple φ hV hVq
    ·
      haveI : Fact (Nat.Prime 7) := hp7
      haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact exists_split_of_cover_simple φ hV hVq
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact exists_split_of_cover_simple φ hV hVq
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · haveI : IsSimpleGroup
          (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (3 * n))) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field _
      exact exists_split_of_cover_simple φ hV hVq
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      haveI : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n)) :=
        Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact exists_split_of_cover_simple φ hV hVq
  ·
    obtain ⟨⟨φ⟩, -⟩ := h6
    exact exists_split_of_mulEquiv_prod hA5p hA5_3 hJ2p hJ2_3 φ hV hVq
  ·
    exact (Proof15Res6.false_of_case148Seven_two h h148 hM h7').elim

end Proof155BXW

end CFSG.RankThree.PartTwo.Sec15
