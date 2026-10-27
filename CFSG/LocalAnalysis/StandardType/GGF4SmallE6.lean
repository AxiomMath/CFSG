module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.StandardType.GGE6OppConjDatum
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly
open scoped commutatorElement

theorem ggF4Small_e6_false
    (hE6 : GGE6TwoThreeComp) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (hG : GGHasLabel ⟨.E6, 0, 1⟩ (G ⧸ Subgroup.center G))
    {x : G} (hx : orderOf x = 3) {L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hlab : GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L)) : False := by
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · obtain ⟨a, b, hab⟩ := hna
      have hc : ⁅a, b⁆ ∈ commutator G := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact absurd hc hab
    · exact h
  haveI : Group.IsPerfect G := ⟨hperf⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hH : (GGHasLabel ⟨.E6, 0, 1⟩ (G ⧸ Subgroup.center G) ∧ 3 ∣ 2 ^ 1 + 1) ∨
      (GGHasLabel ⟨.twE6, 0, 1⟩ (G ⧸ Subgroup.center G) ∧ 3 ∣ 2 ^ 1 - 1) :=
    Or.inl ⟨hG, by norm_num⟩
  obtain ⟨-, -, hδ3, hδ1, hJ, -, lab, -, hraw⟩ :=
    ggTorsionDatum_conj_of_e6Opp (f := 1) le_rfl hH hx1 hx3 hL
  obtain ⟨R, _, I, F, -, -, θ, hPl, -⟩ := largeEvenRawDatum_exists hraw
  have hlabE : lab = ⟨.E6, 0, 1⟩ := by
    rcases hPl with ⟨h, -⟩ | ⟨-, h3⟩
    · exact h
    · exfalso
      norm_num at h3
  subst hlabE
  have hmain := hE6 _ hraw
  obtain ⟨R', _, I', F', hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hQ, hP⟩ := hQR
  obtain ⟨-, -, θ', -, hm'⟩ := hQ
  let ψ : G →* R' := θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ'.surjective r
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
    refine ⟨y, ?_⟩
    show θ' (QuotientGroup.mk' (Subgroup.center G) y) = r
    rw [hy]
    exact hq
  have hker : ψ.ker ≤ Subgroup.center G := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hy' : θ' (QuotientGroup.mk' (Subgroup.center G) y) = 1 := by simpa [ψ] using hy
    have hy'' : QuotientGroup.mk' (Subgroup.center G) y = 1 :=
      θ'.injective (by simpa using hy')
    exact (QuotientGroup.eq_one_iff y).mp hy''
  have hφ_apply : ∀ l : G, ggInducedAut θ' (MulAut.conj x) (ψ l) = ψ ((MulAut.conj x) l) := by
    intro l
    change ggInducedAut θ' (MulAut.conj x) (θ' (l : G ⧸ Subgroup.center G)) =
      θ' (((MulAut.conj x) l : G) : G ⧸ Subgroup.center G)
    exact ggInducedAut_apply θ' (MulAut.conj x) l
  have hJ' : CFSG.Assembly.IsComponentOf L (ggFixSub (MulAut.conj x)) := by
    have hsub : ggFixSub (MulAut.conj x) = ggAutFixedSubgroup (MulAut.conj x) := by
      ext y
      simp [ggFixSub, ggAutFixedSubgroup]
    rw [hsub]
    exact hJ
  obtain ⟨labJ, hS, hlabJ⟩ := hP G ψ hψ hker hperf (MulAut.conj x) hδ3 hδ1
    ⟨ggInducedAut θ' (MulAut.conj x), hm', hφ_apply⟩ L hJ'
  have hΛ1 : LargeEvenInLambda2 (⟨.A, 3, 2⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    decide
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · have hiso := ggLabelRigidInput_holds ⟨.A, 3, 2⟩ _ (L ⧸ Subgroup.center L) hΛ1
      (by unfold LargeEvenInLambda2; decide) hlab hlabJ
    simp [GGLabelIso] at hiso
  · have hiso := ggLabelRigidInput_holds ⟨.A, 3, 2⟩ _ (L ⧸ Subgroup.center L) hΛ1
      (by unfold LargeEvenInLambda2; decide) hlab hlabJ
    simp [GGLabelIso] at hiso
  · have hiso := ggLabelRigidInput_holds ⟨.A, 3, 2⟩ _ (L ⧸ Subgroup.center L) hΛ1
      (by unfold LargeEvenInLambda2; decide) hlab hlabJ
    simp [GGLabelIso] at hiso

end CFSG.StandardType

end
