module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSpor
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open Res417Three Res417Five

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerOutConf417.center_eq_bot_of_theta (h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥) : Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hmk : ((z : L) : L ⧸ aschbacherSolvableCore 3 L) ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz y']
  rw [h.2.2.2.2.2.2.2.2.2.2.1, Subgroup.mem_bot, QuotientGroup.eq_one_iff, hθ] at hmk
  exact hmk

theorem IsInnerOutConf417.false_of_e81 (h : IsInnerOutConf417 L A E c m)
    (hθ : aschbacherSolvableCore 3 L = ⊥) {X : Type} [Group X] (ψ : L ≃* X)
    {P E₀ T₀ : Subgroup X} (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP81 : Nat.card P = 3 ^ 4)
    (hE₀P : E₀ ≤ P) (hE₀9 : Nat.card E₀ = 9) (hT₀ : IsPGroup 2 T₀)
    (hE₀T₀ : E₀ ≤ Subgroup.normalizer (T₀ : Set X))
    (hT₀E₀ : ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set X)) : False := by
  have hZ := h.center_eq_bot_of_theta hθ
  have hcC := h.mem_centralizer
  have hc3 : orderOf c = 3 := h.2.2.2.2.1.2.2.2.1
  have hcL : c ∉ L := h.2.2.2.2.2.2.2.2.2.1
  set ι : X →* G := L.subtype.comp ψ.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι := L.subtype_injective.comp ψ.symm.injective
  have hιL : ∀ x, ι x ∈ L := fun x => (ψ.symm x).2
  have hPL : P.map ι ≤ L := by rintro _ ⟨x, -, rfl⟩; exact hιL x
  have hE₀C : E₀.map ι ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, -, rfl⟩, hxC⟩
    have hz : (⟨ι x, hιL x⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz
  refine false_of_star417 h.1 h.2.2.2.1 hcC hc3 (isElemAbelian_map ι hP) (fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hcC a (hPL ha))) (Subgroup.map_mono hE₀P)
    (by rw [Subgroup.card_map_of_injective hιinj, hE₀9]) hE₀C (T₀ := T₀.map ι)
    (by rintro _ ⟨x, -, rfl⟩; exact hιL x) (hT₀.map ι)
    ((Subgroup.map_mono hE₀T₀).trans (Subgroup.le_normalizer_map ι)) (fun hle => hT₀E₀ ?_) ?_
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    apply hιinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hle ⟨t, ht, rfl⟩) (ι e) ⟨e, he, rfl⟩
  · rw [card_sup_zpowers_of_le_of_not_mem hPL hcC hc3 hcL,
      Subgroup.card_map_of_injective hιinj, hP81]
    norm_num

@[expose] def K417E81McL : Prop :=
  ∃ P E₀ T₀ : Subgroup (NativeSporadic.Carrier .McL), CFSG.Assembly.IsElemAbelian 3 P ∧
    Nat.card P = 3 ^ 4 ∧ E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
    E₀ ≤ Subgroup.normalizer (T₀ : Set (NativeSporadic.Carrier .McL)) ∧
    ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set (NativeSporadic.Carrier .McL))

theorem item417OutMcL_of
    (hK : K417E81McL) : Item417OutMcL := by
  intro G _ _ L A E c m hconf ⟨φ⟩
  have : Group.IsPerfect L := hconf.2.2.1.1.1
  have hθ : aschbacherSolvableCore 3 L = ⊥ :=
    theta_eq_bot_of_two_three hconf.2.1 hconf.2.2.1 fun p hp hp3 hpZ => by
      obtain ⟨hpair, hnot⟩ := CFSG.RankThree.PartOne.Mult.sporadic_residual_of_center
        (hconf.centerEquiv.trans φ) hp hp3 hpZ
      simp only [CFSG.RankThree.PartOne.Mult.SporadicResidualPair, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpair
      rcases hpair with ⟨rfl, -⟩ | ⟨-, hs⟩ | hs
      · exact hnot CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_mcl_five
      · simp at hs
      · simp at hs
  obtain ⟨P, E₀, T₀, hP, hP81, hE₀P, hE₀9, hT₀, hE₀T₀, hT₀E₀⟩ := hK
  exact hconf.false_of_e81 hθ ((Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ) hP hP81 hE₀P
    hE₀9 hT₀ hE₀T₀ hT₀E₀

end Certs

end CFSG.RankThree.PartTwo.Sec4
