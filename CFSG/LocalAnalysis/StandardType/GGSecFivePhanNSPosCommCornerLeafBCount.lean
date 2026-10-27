module

import Lean
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLift
import CFSG.RankThree.PartOne.CTP.SeitzDiag
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep

public section

namespace CFSG.StandardType

open Matrix

open scoped MatrixGroups commutatorElement

open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

theorem ggNSPosPF3C_exists_commutant_nonscalar {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ) {n : ℕ} (hn : 0 < n)
    {E : Subgroup (GL (Fin n) K ⧸ Subgroup.center (GL (Fin n) K))}
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : p ^ 3 ≤ Nat.card E) {X Y : GL (Fin n) K}
    (hX : X ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))))
    (hY : Y ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K)))) :
    ∃ u ∈ E.comap (QuotientGroup.mk' (Subgroup.center (GL (Fin n) K))),
      u * X = X * u ∧ u * Y = Y * u ∧
        ¬ ∃ c : Kˣ, u = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Q : Subgroup (GL (Fin n) K) := E.comap (pglMk n K) with hQ
  have hZQ : Subgroup.center (GL (Fin n) K) ≤ Q := center_le_comap_pglMk E
  set U : Subgroup (GL (Fin n) K) :=
    Q ⊓ Subgroup.centralizer {X} ⊓ Subgroup.centralizer {Y} with hU
  have hmemU : ∀ u, u ∈ U ↔ u ∈ Q ∧ u * X = X * u ∧ u * Y = Y * u := by
    intro u
    simp only [hU, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    tauto
  have hZU : Subgroup.center (GL (Fin n) K) ≤ U := by
    intro c hc
    exact (hmemU c).2 ⟨hZQ hc, (Subgroup.mem_center_iff.1 hc X).symm,
      (Subgroup.mem_center_iff.1 hc Y).symm⟩
  set T : Subgroup (GL (Fin n) K) :=
    (rootsOfUnity p K).map (GeneralLinearGroup.scalar (Fin n)) with hT
  have hTcard : Nat.card T ≤ p := by
    rw [hT, Subgroup.card_map_of_injective
      (fun a b h => CFSG.LinearAlgebra.generalLinearGroup_scalar_injective h)]
    exact card_rootsOfUnity K p
  have hTZ : T ≤ Subgroup.center (GL (Fin n) K) := by
    rintro _ ⟨ζ, -, rfl⟩
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨ζ, rfl⟩
  have hcomT : ∀ u ∈ Q, ∀ V ∈ Q, ⁅u, V⁆ ∈ T := by
    intro u hu V hV
    obtain ⟨ζ, hζ⟩ := exists_conj_eq_scalar hE hV hu
    obtain ⟨a, ha⟩ := exists_pow_eq_scalar hE hV
    have hζp : ζ ^ p = 1 := CFSG.LinearAlgebra.scalar_pow_eq_one_of_conj_eq_scalar hζ ha hn
    refine ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp, ?_⟩
    rw [commutatorElement_def, hζ]
    group
  let κ : ↥Q →* ↥T × ↥T :=
    { toFun := fun u => (⟨⁅(u : GL (Fin n) K), X⁆, hcomT u u.2 X hX⟩,
        ⟨⁅(u : GL (Fin n) K), Y⁆, hcomT u u.2 Y hY⟩)
      map_one' := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp
      map_mul' := fun u v => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact commutatorElement_mul_left_of_mem_center (hTZ (hcomT v v.2 X hX))
        · exact commutatorElement_mul_left_of_mem_center (hTZ (hcomT v v.2 Y hY)) }
  have hκker : κ.ker = U.subgroupOf Q := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemU]
    change ((⟨⁅(u : GL (Fin n) K), X⁆, _⟩, ⟨⁅(u : GL (Fin n) K), Y⁆, _⟩) : ↥T × ↥T) = 1 ↔ _
    rw [Prod.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one,
      commutatorElement_eq_one_iff_mul_comm]
    exact ⟨fun h => ⟨u.2, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  have hUQ : U ≤ Q := fun u hu => ((hmemU u).1 hu).1
  have hQcard : Nat.card Q ≤ Nat.card U * p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range κ
    rw [hκker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv] at h1
    have h2 : Nat.card κ.range ≤ p ^ 2 := by
      calc Nat.card κ.range ≤ Nat.card (↥T × ↥T) := Subgroup.card_le_card_group _
        _ = Nat.card T * Nat.card T := Nat.card_prod _ _
        _ ≤ p * p := Nat.mul_le_mul hTcard hTcard
        _ = p ^ 2 := (sq p).symm
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2
  set E₂ := U.map (pglMk n K) with hE₂
  have hQE : Q.map (pglMk n K) = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) E
  have hcQ := card_eq_card_map_mul_card_center hZQ
  have hcU := card_eq_card_map_mul_card_center hZU
  rw [hQE] at hcQ
  have hZpos : 0 < Nat.card (Subgroup.center (GL (Fin n) K)) := Nat.card_pos
  have hEle : Nat.card E ≤ Nat.card E₂ * p ^ 2 := by
    have h3 : Nat.card E * Nat.card (Subgroup.center (GL (Fin n) K)) ≤
        Nat.card E₂ * p ^ 2 * Nat.card (Subgroup.center (GL (Fin n) K)) := by
      rw [← hcQ]
      calc Nat.card Q ≤ Nat.card U * p ^ 2 := hQcard
        _ = Nat.card E₂ * p ^ 2 * Nat.card (Subgroup.center (GL (Fin n) K)) := by
          rw [hcU]
          ring
    exact Nat.le_of_mul_le_mul_right h3 hZpos
  have hcardE₂ : Nat.card E₂ ≠ 1 := by
    have hmul : p * p ^ 2 ≤ Nat.card E₂ * p ^ 2 := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card E := hcard
        _ ≤ Nat.card E₂ * p ^ 2 := hEle
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    exact ne_of_gt (lt_of_lt_of_le hp.one_lt (Nat.le_of_mul_le_mul_right hmul hp2pos))
  have hE₂bot : E₂ ≠ ⊥ := fun h => hcardE₂ (by rw [Subgroup.card_eq_one, h])
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E₂, e ≠ 1 := by
    by_contra h
    exact hE₂bot ((Subgroup.eq_bot_iff_forall E₂).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩)
  obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 he
  have hu_ne : pglMk n K u ≠ 1 := fun h1 => he1 (hue ▸ h1)
  refine ⟨u, ((hmemU u).1 hu).1, ((hmemU u).1 hu).2.1, ((hmemU u).1 hu).2.2, ?_⟩
  rintro ⟨c, hc⟩
  exact hu_ne (pglMk_eq_one_iff.2 ⟨c, hc⟩)

end CFSG.StandardType

end
