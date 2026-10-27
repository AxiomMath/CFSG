module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSL2
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofE27
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

section Transfer


theorem exists_injective_fixSub {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (ht : IsType419 K) {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) :
    IsSimpleGroup K ∧ Subgroup.center K = ⊥ ∧
      ∃ ι : K →* M, Function.Injective ι ∧
        ∀ k, ι k ∈ Item426.fixSub (inducedAutHom L e ⟨a, ha⟩) := by
  have hq : IsQuasisimple K := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hKle) hKc.1
  have hZ : Subgroup.center K = ⊥ := Res419Two.center_eq_bot_of_isType419 ht
  have hs : IsSimpleGroup K := by
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hKL : K ≤ L := hKle.trans inf_le_left
  set τ := inducedAutHom L e ⟨a, ha⟩ with hτ
  set π : K →* M := e.toMonoidHom.comp
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)) with hπ
  have hfix : ∀ k : K, π k ∈ Item426.fixSub τ := by
    intro k
    have hk : a * (k : G) * a⁻¹ = k := by
      rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hKle k.2).2), mul_inv_cancel_right]
    have hφk : compAction L ⟨a, ha⟩ (Subgroup.inclusion hKL k) = Subgroup.inclusion hKL k := by
      apply Subtype.ext
      change a * (k : G) * a⁻¹ = k
      exact hk
    have hπk : π k = e ((Subgroup.inclusion hKL k : L) : L ⧸ aschbacherSolvableCore 3 L) := rfl
    rw [Item426.mem_fixSub, hτ, inducedAutHom_apply, MulAut.congr_apply, hπk,
      MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, thetaQuotMulAut_mk,
      hφk]
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact h
    · exfalso
      have hle : ∀ k : K, Subgroup.inclusion hKL k ∈ aschbacherSolvableCore 3 L := by
        intro k
        have hk : k ∈ π.ker := h ▸ Subgroup.mem_top k
        rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk
        exact hk
      let g : K →* aschbacherSolvableCore 3 L :=
        (Subgroup.inclusion hKL).codRestrict _ hle
      have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) :=
        (solvable_prime_complement_core_characterization Nat.prime_three).1
      have hsolK : Group.IsSolvable K :=
        Group.isSolvable_of_isSolvable_injective (f := g) fun x y hxy =>
          Subgroup.inclusion_injective hKL (congrArg Subtype.val hxy)
      exact Item419Res3.not_isSolvable_isType419 ht hs hZ hsolK
  exact ⟨hs, hZ, π, hinj, hfix⟩

theorem fixSub_conj_eq_centralizer' {X : Type*} [Group X] (x : X) :
    Item426.fixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext y
  rw [Item426.mem_fixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

end Transfer

end CFSG.RankThree.PartTwo.Sec4.HeringOF
