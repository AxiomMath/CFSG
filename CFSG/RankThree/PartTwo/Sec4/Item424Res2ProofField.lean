module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofL2

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.GorensteinWalter (PSL2)
open scoped commutatorElement

section Defs


@[expose] def K424FieldCentNotL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G),
    KFacts.InducesStdKind L c .field → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
    Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    (¬ ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F)) →
      IsFieldCent424 (L ⧸ aschbacherSolvableCore 3 L)

end Defs

namespace Item424Res2

open Sec11.KS11Lie2Proof

theorem isSolvable_or_not_hasType424_psl2_three {X : Type} [Group X] [Finite X] {F : Type}
    [Field F] [Finite F] (h3 : (3 : F) = 0) (e : X ≃* PSL2 F) {α : MulAut X} (hα3 : α ^ 3 = 1)
    (hout : ¬ KFacts.IsInnerAut α) :
    Group.IsSolvable (Item426.fixSub α) ∨ ¬ HasType424 (Item426.fixSub α) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set β := MulAut.congr e α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨φ⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  have hmap := fixSub_congr e α
  let ψ : Item426.fixSub α ≃* PSL2 (GH74.GLS.IVK.fixedField σ) :=
    ((Item426.fixSub α).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((MulEquiv.subgroupCongr hmap.symm).trans φ)
  set F₀ := GH74.GLS.IVK.fixedField σ with hF₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  have h30 : (3 : F₀) = 0 := by
    apply Subtype.ext
    rw [show ((3 : F₀) : F) = 3 from rfl]
    exact h3
  have : CharP F₀ 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h30
  obtain ⟨n, -, hcard⟩ := FiniteField.card F₀ 3
  have hF₀card : Nat.card F₀ = 3 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  by_cases hn : (n : ℕ) ≤ 1
  · left
    have hF₀3 : Nat.card F₀ ≤ 3 := by
      rw [hF₀card]
      calc 3 ^ (n : ℕ) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn
        _ = 3 := by norm_num
    have : Group.IsSolvable (PSL2 F₀) := Sec11.fieldCent_isSolvable_psl2 hF₀3
    exact Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
  · right
    have hn2 : 2 ≤ (n : ℕ) := by omega
    have h4 : 4 ≤ Nat.card F₀ := by
      rw [hF₀card]
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
    have : IsSimpleGroup (PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    have : IsSimpleGroup (⊤ : Subgroup (PSL2 F₀)) := Subgroup.topEquiv.isSimpleGroup
    have hE9 := Sec8.Item82OneProof.e9Closed_psl2_of_card_eq_three_pow hF₀card hn2
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' (G := PSL2 F₀) 3 (KFacts.three_dvd_card_psl2 F₀)
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx1 : x ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      omega
    obtain ⟨y, hy3, hxy, hyx⟩ := hE9 x hx3 hx1
    have hc : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hxy
    have hnot : ¬ HasType424 (PSL2 F₀) :=
      not_hasType424_of_simple (⊤ : Subgroup (PSL2 F₀)) (fun _ _ => Subgroup.mem_top _)
        (Subgroup.mem_top x) (Subgroup.mem_top y) hx1 hx3 hy3
        (by rw [hc]; exact Commute.one_left _) (by rw [hc]; exact Commute.one_left _) hyx
    exact fun h => hnot (h.of_mulEquiv ψ)

end Item424Res2

open Item424Res2


theorem k424FieldCent_of (h : K424FieldCentNotL2) : K424FieldCent := by
  intro G _ _ L K c hf hc3 hK hT
  by_cases hL2 : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* PSL2 F)
  · obtain ⟨F, _, _, ⟨e⟩⟩ := hL2
    by_cases h3 : (3 : F) = 0
    · exfalso
      obtain ⟨hcN, hα⟩ := hf.inducesOuterTheta L (by intro h; cases h)
      have hα3 := Item426.thetaAut_pow_eq_one L hcN hc3
      have hKL : K ≤ L := (mem_thetaComponentsIn_iff.mp hK).1.trans inf_le_left
      have hJα := Item426.map_mem_thetaComponentsIn_fixSub L hcN hc3 hK
      obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv L hKL
      have hHas := Sec11.KS11Lie2Proof.hasType424_of_mem hJα
        (Sec11.isType424_of_mulEquiv eK.symm hT)
      rcases isSolvable_or_not_hasType424_psl2_three h3 e hα3 hα with hs | hn
      · exact Sec11.fieldCent_false_of_isSolvable hcN hc3 hK hs
      · exact hn hHas
    · exact Or.inl ⟨F, inferInstance, inferInstance, h3, ⟨e⟩⟩
  · exact h G L K c hf hc3 hK hT hL2

end CFSG.RankThree.PartTwo.Sec4
