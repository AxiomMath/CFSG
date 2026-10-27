module

public import CFSG.Quasithin.EmptyFaithful.S1422Recog

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Tools

variable {G : Type*} [Group G]

theorem thompsonJ_le_self' (T : Subgroup G) : thompsonJ T ≤ T :=
  iSup₂_le fun _ hA => hA.1

theorem isMaxElemAbelian_thompsonJ [Finite G] {T : Subgroup G}
    (h : IsElemAbelian 2 (thompsonJ T)) : IsMaxElemAbelian T (thompsonJ T) := by
  refine ⟨thompsonJ_le_self' T, h, fun B hBT hB => ?_⟩
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hAJ : A ≤ thompsonJ T := le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) A hA
  exact (hA.2.2 B hBT hB).trans (Subgroup.card_le_of_le hAJ)

theorem isWeaklyClosedIn_thompsonJ [Finite G] {T : Subgroup G}
    (h : IsElemAbelian 2 (thompsonJ T)) : IsWeaklyClosedIn (thompsonJ T) T := by
  intro g hg
  have hmax := isMaxElemAbelian_thompsonJ h
  have hel : IsElemAbelian 2 (cjSub g⁻¹ (thompsonJ T)) := isElemAbelian_cjSub h
  have hcard : Nat.card (cjSub g⁻¹ (thompsonJ T)) = Nat.card (thompsonJ T) := card_cjSub _ _
  have hconj : conjSubgroup (thompsonJ T) g = cjSub g⁻¹ (thompsonJ T) := rfl
  rw [hconj] at hg ⊢
  have hA : IsMaxElemAbelian T (cjSub g⁻¹ (thompsonJ T)) :=
    ⟨hg, hel, fun B hBT hB => (hmax.2.2 B hBT hB).trans hcard.ge⟩
  have hle : cjSub g⁻¹ (thompsonJ T) ≤ thompsonJ T :=
    le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian T A) => A) _ hA
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem AmalgamFusion.exists_conj {P₁ P₂ : Subgroup G} {x y : G} (h : AmalgamFusion P₁ P₂ x y) :
    ∃ g : G, g * x * g⁻¹ = y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨1, by simp⟩
  | head hxz _ ih =>
    obtain ⟨-, -, hh⟩ := hxz
    obtain ⟨g, hg⟩ := ih
    rcases hh with ⟨h, -, rfl⟩ | ⟨h, -, rfl⟩
    · exact ⟨g * h, by rw [← hg]; group⟩
    · exact ⟨g * h, by rw [← hg]; group⟩

theorem pResidual_two_eq_top_of_simple [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : pResidual 2 G = ⊤ := by
  refine eq_top_iff.2 (le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    have h2 : IsPGroup 2 G := fun x => by
      obtain ⟨k, hk⟩ := hp x
      rw [h, Subgroup.mem_bot] at hk
      exact ⟨k, hk⟩
    have hc : Nontrivial (Subgroup.center G) := h2.center_nontrivial
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz] at hc
      obtain ⟨x, y, hxy⟩ := hc
      exact hxy (Subsingleton.elim x y)
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center G := by rw [hz]; trivial
      exact (Subgroup.mem_center_iff.mp ha b).symm
  · rw [h]

end Tools

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem autm12_case (hSz : Nat.card ↥(Sz 0) = 20) (hAut : AutM12AmalgamFacts)
    (S : Setting1422 T M Y H)
    (hHc : H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hC : CaseAutM12 H (Y ⊔ T)) : False := by
  have hM : M = Y ⊔ T := S.M_eq_YT hSz hHc
  have hHT : H ⊓ (Y ⊔ T) = T := S.H_inf_YT hSz
  obtain ⟨R, hRle, hRidx, hJel, hJnorm, ⟨j0, hj0J, hj0R⟩, hhyp, hfus⟩ :=
    hAut G H (Y ⊔ T) hC.1 hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.2.2.2.2
  rw [hHT] at hRle hRidx hJel hJnorm hhyp hfus hj0J
  obtain ⟨P, rfl⟩ := S.exists_sylow
  set W : Subgroup G := thompsonJ (P : Subgroup G) with hWdef
  have hj01 : j0 ≠ 1 := fun h => hj0R (h ▸ R.one_mem)
  have hj0sq : j0 ^ 2 = 1 := hJel.2 j0 hj0J
  have hord : orderOf j0 = 2 := orderOf_eq_prime hj0sq hj01
  have hWle : W ≤ (P : Subgroup G) := thompsonJ_le_self' _
  have hW2 : IsPGroup 2 W := (P.isPGroup').to_le hWle
  have hWne : W ≠ ⊥ := fun h => hj01 (by
    have : j0 ∈ (⊥ : Subgroup G) := h ▸ hj0J
    exact this)
  have hwc : IsWeaklyClosedIn W (P : Subgroup G) := isWeaklyClosedIn_thompsonJ hJel
  have hNle : Subgroup.normalizer (W : Set G) ≤ Y ⊔ P := by
    have hloc : IsTwoLocal (Subgroup.normalizer (W : Set G)) := ⟨W, hWne, hW2, rfl⟩
    obtain ⟨K, hK, hle⟩ := exists_maxTwoLocal_ge hloc
    have hKM : K = M := S.data.unique.2 K ⟨hK, hJnorm.trans hle⟩
    exact hle.trans (hKM ▸ hM ▸ le_rfl)
  have hWcomm : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := fun w hw w' hw' => by
    have := hJel.1.is_comm.comm (⟨w, hw⟩ : W) (⟨w', hw'⟩ : W)
    exact congrArg Subtype.val this
  have hfix : ∀ x ∈ W, ∀ w ∈ W, conjSet {x} w = {x} := by
    intro x hx w hw
    rw [conjSet_singleton]
    have : w⁻¹ * x * w = x := by
      calc w⁻¹ * x * w = w⁻¹ * (x * w) := mul_assoc _ _ _
        _ = w⁻¹ * (w * x) := by rw [hWcomm x hx w hw]
        _ = x := inv_mul_cancel_left w x
    rw [this]
  have hstar : ∀ g : G, g * j0 * g⁻¹ ∉ R := by
    intro g hgR
    have hr2 : (g * j0 * g⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hj0sq]
      group
    obtain ⟨j', hj'WR, hfus'⟩ := hfus (g * j0 * g⁻¹) hgR hr2
    obtain ⟨g', hg'⟩ := hfus'.exists_conj
    have hconj : (g' * g) * j0 * (g' * g)⁻¹ = j' := by rw [← hg']; group
    obtain ⟨n, hn, hnconj⟩ := burnside_fusion_lemma P hWle hwc (hfix j0 hj0J) (hfix j' hj'WR.1)
      (g := (g' * g)⁻¹) (by rw [conjSet_singleton, inv_inv, hconj])
    rw [conjSet_singleton] at hnconj
    have hnj : n⁻¹ * j0 * n = j' := Set.singleton_eq_singleton_iff.mp hnconj
    have hy : n⁻¹ ∈ Y ⊔ P := Subgroup.inv_mem _ (hNle hn)
    apply hhyp j0 hj0J hj0R n⁻¹ hy
    rw [inv_inv, hnj]
    exact hj'WR.2
  have hnot := thompson_transfer_lemma P hRle hRidx hord (fun x => by simpa using hstar x⁻¹)
  rw [pResidual_two_eq_top_of_simple S.hyp.simple S.hyp.nonabelian] at hnot
  exact hnot (Subgroup.mem_top _)

end Setting1422

end CFSG.Quasithin
