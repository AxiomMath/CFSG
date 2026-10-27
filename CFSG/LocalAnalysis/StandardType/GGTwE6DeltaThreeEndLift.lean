module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreePure
import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly CFSG.StandardType.USixTwo

section Lift

variable {L' R : Type} [Group L'] [Group R] [Finite L'] [Finite R] {ψ : L' →* R}

theorem indAutHom_apply_mk (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (a : MulAut L') (l : L') :
    ggIE_indAutHom hψ hZ hker a (ψ l) = ψ (a l) :=
  ggIE_indAut_apply hψ hZ hker a l

theorem layer_fix_iff_of_data (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') {t : MulAut L'} {X D : Subgroup R}
    (hfix : ggFix (ggIE_indAutHom hψ hZ hker t) = X ⊔ D) (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set R)) (hDq : CFSG.IsQuasisimple D) (s : MulAut L') :
    (∀ j ∈ LargeEvenLayer (ggFix t), s j = j) ↔ ∀ x ∈ D, ggIE_indAutHom hψ hZ hker s x = x := by
  have hlay := (layer_sup_eq hX hXD ((TableBSymp.isQuasisimple_iff _).2 hDq)).1
  rw [← hfix] at hlay
  have h := fix_layer_iff hψ hker (indAutHom_apply_mk hψ hZ hker t)
    (indAutHom_apply_mk hψ hZ hker s)
  rwa [hlay] at h

theorem endNode_of_data (hψ : Function.Surjective ψ) (hZ : Subgroup.center R = ⊥)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {Y : Subgroup (MulAut L')}
    (hY : IsElemAbelian 3 Y) {t : MulAut L'} (htY : t ∈ Y) (ht1 : t ≠ 1) {X D : Subgroup R}
    (hfix : ggFix (ggIE_indAutHom hψ hZ hker t) = X ⊔ D) (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set R)) (hDq : CFSG.IsQuasisimple D)
    (h7 : 7 ∣ Nat.card D)
    (hcent : ∀ y ∈ Y, (∀ x ∈ D, ggIE_indAutHom hψ hZ hker y x = x) →
      ∃ x ∈ X, ggIE_indAutHom hψ hZ hker y = MulAut.conj x) :
    GGIsEndNode Y t ∧ ¬ LargeEvenSmall (LargeEvenLayer (ggFix t)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := ggIE_indAutHom hψ hZ hker with hρdef
  have hc : ∀ a l, ρ a (ψ l) = ψ (a l) := indAutHom_apply_mk hψ hZ hker
  obtain ⟨hlay, hcomp⟩ := layer_sup_eq hX hXD ((TableBSymp.isQuasisimple_iff _).2 hDq)
  rw [← hfix] at hlay hcomp
  obtain ⟨-, hLcomp⟩ := layer_eq_commutator_comap hψ hker (hc t) hcomp
  have hmap : (LargeEvenLayer (ggFix t)).map ψ = D :=
    (layer_map_eq hψ hker (hc t)).trans hlay
  have hnS : ¬ LargeEvenSmall (LargeEvenLayer (ggFix t)) :=
    IOneOrthEnd.not_largeEvenSmall_of_map ψ _ (by rw [hmap]; exact h7)
  refine ⟨⟨htY, ht1, hLcomp, fun a' ha' => ⟨fun hfixL => ?_, fun hz => ?_⟩⟩, hnS⟩
  ·
    set F : Subgroup (MulAut L') :=
      Y ⊓ (fixingSubgroup (MulAut R) (D : Set R)).comap ρ with hF
    have hmemF : ∀ y, y ∈ F ↔ y ∈ Y ∧ ∀ x ∈ D, ρ y x = x := fun y => by
      simp only [hF, Subgroup.mem_inf, Subgroup.mem_comap, mem_fixingSubgroup_iff,
        SetLike.mem_coe, MulAut.smul_def]
    have hFmem : ∀ y : F, ρ y ∈ X.map (MulAut.conj : R →* MulAut R) := fun y => by
      obtain ⟨hyY, hyfix⟩ := (hmemF y).1 y.2
      obtain ⟨x, hxX, hx⟩ := hcent y hyY hyfix
      exact ⟨x, hxX, hx.symm⟩
    let f : F →* ↥(X.map (MulAut.conj : R →* MulAut R)) := (ρ.comp F.subtype).codRestrict _ hFmem
    have hρinj : Function.Injective ρ := ggIE_indAutHom_injective hψ hZ hker hperf
    have hfinj : Function.Injective f := fun a b h =>
      Subtype.ext (hρinj (congrArg Subtype.val h))
    haveI : IsCyclic ↥(X.map (MulAut.conj : R →* MulAut R)) :=
      haveI : IsCyclic X := hX
      isCyclic_of_surjective ((MulAut.conj : R →* MulAut R).subgroupMap X)
        (MonoidHom.subgroupMap_surjective _ _)
    have hFcard : Nat.card F ≤ 3 :=
      card_le_three_of_injective_cyclic inferInstance f hfinj fun c =>
        Subtype.ext (hY.2 c ((hmemF c).1 c.2).1)
    have htF : t ∈ F := (hmemF t).2 ⟨htY, fun x hx =>
      mem_ggFix.1 (by rw [hfix]; exact (le_sup_right : D ≤ X ⊔ D) hx)⟩
    have hzt : Nat.card (Subgroup.zpowers t) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hY.2 t htY) ht1
    have hFeq : Subgroup.zpowers t = F :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 htF) (by rw [hzt]; exact hFcard)
    rw [hFeq]
    exact (hmemF a').2 ⟨ha', (layer_fix_iff_of_data hψ hZ hker hfix hX hXD hDq a').1 hfixL⟩
  · have hle : LargeEvenLayer (ggFix t) ≤ ggFix t := sSup_le fun _ hK' => hK'.1
    exact fixes_of_mem_zpowers (fun j hj => mem_ggFix.1 (hle hj)) hz

end Lift

end CFSG.StandardType.TwE6D3
