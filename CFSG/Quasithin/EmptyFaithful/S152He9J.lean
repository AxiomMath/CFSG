module

public import CFSG.Quasithin.EmptyFaithful.S152He9R

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_of_ker_eq {A B : Type*} [Group A] [Group B] {π ψ : A →* B}
    (hπ : Function.Surjective π) (hψ : Function.Surjective ψ) (hk : ψ.ker = π.ker) :
    ∃ α : B ≃* B, ∀ x, α (π x) = ψ x := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) =
      (x : A ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl

theorem card_perm_fin (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Nat.card_perm, Nat.card_fin]

theorem card_wreath_s3 :
    Nat.card (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) = 72 := by
  rw [RegularWreathProduct.card, card_perm_fin, W5.card_Q2]
  norm_num [Nat.factorial]

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem card_OTwoQuot : Nat.card (OTwoQuot H) = 28800 := by
  have e : OTwoQuot H ≃* W5 :=
    (QuotientGroup.quotientMulEquivOfEq c.wr.ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π c.wr.data.surj)
  rw [Nat.card_congr e.toEquiv, W5.card_W5]

theorem thompsonJ_le_S (h15112 : StageLemma15112) (h15206 : StageLemma15206)
    (h15207 : StageLemma15207) : thompsonJ T ≤ sOf T K₁ := by
  have hc := (h15112 G T Mc M c.hs.qtfe c.hs.mf c.hs.ce H c.hH).1
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M c.hs
  have c15207 := h15207 G T Mc M c.hs Y₁ hY₁
  obtain ⟨L, N, hst, hnc, -⟩ := S152Fin.exists_noncentral_of_series hc.chief (by norm_num : 1 ≤ 2)
  have hshape := hc.shape trivial L N hst hnc
  have hC := S152L08.cSecIn_eq_pCoreOf c.hs c.hH c.h1519 c15207 hc.elemAbelian hst hshape
  obtain ⟨hNorm, h | h | h | h⟩ := hshape
  · exfalso
    have h1 := h.1
    rw [hC] at h1
    obtain ⟨e⟩ := S152L08.nonempty_oTwoQuot_equiv h1
    have := Nat.card_congr e.toEquiv
    rw [c.card_OTwoQuot, card_perm_fin] at this
    norm_num [Nat.factorial] at this
  · exfalso
    have h1 := h.1
    rw [hC] at h1
    obtain ⟨e⟩ := S152L08.nonempty_oTwoQuot_equiv h1
    have := Nat.card_congr e.toEquiv
    rw [c.card_OTwoQuot, card_perm_fin] at this
    norm_num [Nat.factorial] at this
  · exfalso
    have h1 := h.1
    rw [hC] at h1
    obtain ⟨e⟩ := S152L08.nonempty_oTwoQuot_equiv h1
    have := Nat.card_congr e.toEquiv
    rw [c.card_OTwoQuot, card_wreath_s3] at this
    omega
  · have h1 := h.1
    rw [hC] at h1
    obtain ⟨ψ, hψ, hker, ⟨e⟩⟩ := h1
    have hker' : ψ.ker = π.ker := by
      rw [hker, S152Fin.pCoreOf_subgroupOf, c.wr.ker_eq]
    obtain ⟨α, hα⟩ := exists_mulEquiv_of_ker_eq c.wr.data.surj hψ hker'
    let J' : Subgroup ↥H := (thompsonJ H).subgroupOf H
    have hQP : J'.map ψ = (J'.map π).map α.toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun x => (hα x).symm
    have eQ : ↥(J'.map π) ≃* S5 × S5 :=
      (Subgroup.equivMapOfInjective _ α.toMonoidHom α.injective).trans
        ((MulEquiv.subgroupCongr hQP.symm).trans e)
    have hbase : J'.map π = W5.base := W5.eq_base_of_equiv_prod eQ
    intro x hx
    have hxT : x ∈ T := (thompsonJ_le_self T) hx
    have hxH : x ∈ H := c.hT.1 hxT
    have hxJ : x ∈ thompsonJ H := thompsonJ_le_thompsonJ_of_isSylowTwoOf c.hT hx
    refine ⟨hxT, (c.wr.mem_normalizer₁ hxH).2 ?_⟩
    rw [← hbase]
    exact ⟨⟨x, hxH⟩, hxJ, rfl⟩

end Ctx15204

end CFSG.Quasithin.He9
