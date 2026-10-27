module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.OddTranspositions.PartThree.Ten.CentralSymSplit
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
@[expose] noncomputable def tenHom (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    Halpha D hC.alpha →* L2Wreath f n :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha)))

omit [Finite G] in
theorem tenBase_eq (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    tenBase hC e = ((l2WreathBase f n).comap (tenHom hC e)).map (Halpha D hC.alpha).subtype :=
  rfl

omit [Finite G] in
theorem tenHom_surjective (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    Function.Surjective (tenHom hC e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem tenHom_ker (hC : HypothesisC D) {f n : ℕ}
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    (tenHom hC e).ker = Subgroup.center (Halpha D hC.alpha) := by
  ext x
  rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff x]
  change e (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff e e.injective]
  rfl

theorem nontrivial_l2Wreath {f n : ℕ} (hn : 2 ≤ n) : Nontrivial (L2Wreath f n) := by
  refine ⟨⟨SemidirectProduct.inr (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩), 1,
    fun h => ?_⟩⟩
  have h1 := congrArg SemidirectProduct.right h
  simp only [SemidirectProduct.right_inr, SemidirectProduct.one_right] at h1
  exact absurd (Equiv.swap_eq_one_iff.1 h1) (by simp [Fin.ext_iff])

theorem tenHom_image_DstarH (hC : HypothesisC D) {f n : ℕ} (hf : 2 ≤ f) (hn : 5 ≤ n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    tenHom hC e '' DstarH hC = WreathEndgame.swapSet f n := by
  have : Nontrivial (L2Wreath f n) := nontrivial_l2Wreath (by omega)
  set q := tenHom hC e with hq
  have hqs : Function.Surjective q := tenHom_surjective hC e
  have hCls : IsOddTranspClass (DstarH hC) :=
    ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
  have hne : ∀ c ∈ DstarH hC, q c ≠ 1 := by
    obtain ⟨d₀, hd₀⟩ := DstarH_isClass hC
    intro c hc
    rw [hd₀] at hc
    exact CentralSymSplit.map_ne_one_of_isConj q hqs (hd₀ ▸ DstarH_closure_eq_top hC) hc
  obtain ⟨⟨c₀, hc₀⟩, hodd, hgen⟩ := isOddTranspClass_map q hqs hCls hne
  have hconj : ∀ c ∈ q '' DstarH hC, ∀ g : L2Wreath f n, g * c * g⁻¹ ∈ q '' DstarH hC := by
    intro c hc g
    rw [hc₀] at hc ⊢
    exact (show IsConj c₀ c from hc).trans (isConj_iff.2 ⟨g, rfl⟩)
  have hsub : q '' DstarH hC ⊆ WreathEndgame.swapSet f n := by
    set π : L2Wreath f n →* Equiv.Perm (Fin n) := SemidirectProduct.rightHom with hπ
    have hπs : Function.Surjective π := SemidirectProduct.rightHom_surjective
    have : Nontrivial (Equiv.Perm (Fin n)) :=
      ⟨⟨Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩, 1, fun h => by
        have h1 := Equiv.swap_eq_one_iff.1 h
        exact absurd h1 (by simp [Fin.ext_iff])⟩⟩
    have hgenC : Subgroup.closure {g | IsConj c₀ g} = ⊤ := by rw [← hc₀]; exact hgen
    have hodd' : IsOddTransp (π '' (q '' DstarH hC)) :=
      CentralSymSplit.isOddTransp_image π hodd fun c hc =>
        CentralSymSplit.map_ne_one_of_isConj π hπs hgenC (by rw [hc₀] at hc; exact hc)
    have hcls : ∃ σ₀ : Equiv.Perm (Fin n), π '' (q '' DstarH hC) = {g | IsConj σ₀ g} := by
      refine ⟨π c₀, ?_⟩
      rw [hc₀]
      exact CentralSymSplit.image_isConj_class π hπs c₀
    have hgen' : Subgroup.closure (π '' (q '' DstarH hC)) = ⊤ :=
      CentralSymSplit.closure_image_eq_top π hπs hgen
    intro x hx
    rcases isSwap_or_triple_of_isOddTransp hn hodd' hcls hgen' with hsw | ⟨h6, htr⟩
    · exact WreathClass.mem_swapSet_of_isSwap_right hf hn hodd hconj hx (hsw _ ⟨x, hx, rfl⟩)
    · subst h6
      exact absurd (htr _ ⟨x, hx, rfl⟩) (WreathClass.not_triple_right hf hodd hconj hx)
  refine Set.Subset.antisymm hsub fun s hs => ?_
  obtain ⟨x, hx⟩ := (DstarH_nonempty hC).image q
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hxc : IsConj c₀ x := by
    have hx' := hx
    rw [hc₀] at hx'
    exact hx'
  rw [hc₀]
  exact hxc.trans ((WreathEndgame.isConj_of_mem_swapSet h01 (hsub hx)).symm.trans
    (WreathEndgame.isConj_of_mem_swapSet h01 hs))

end CFSG.OddTranspositions.PartThree

end
