module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.exists_lift_a2 [Finite G] [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)} :
    ∃ s : ↥(XbarH M Q Z B), ((s : ↥(H0 M Z)) : G) = (a : G) ∧
      xbarHToXbar M Q Z B s =
        ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ := by
  have haX : (a : G) ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc a.2).mpr (mk_mem_Xbar_of_LB M Q Z B a h.1 h.2)
  exact ⟨⟨⟨(a : G), XbarPre_le_H0 hc haX⟩, (mem_XbarH_iff hc _).mpr haX⟩, rfl, rfl⟩


theorem Ctx.exists_hom_statedSp_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {m x : ℕ}
    (hLm : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSp m 2 x)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ x) :
    ∃ (ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K) (Θ : ↥(XbarH M Q Z B) →* StatedSp m K),
      (∀ s, Θ s = ψ (xbarHToXbar M Q Z B s)) ∧ Function.Surjective Θ ∧
      ∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := by
  classical
  obtain ⟨K', _, _, hcard', _, ⟨ψ'⟩⟩ := hc.exists_mulEquiv_statedSp_of_lieModel_psp hLm
  have := Fintype.ofFinite K'
  have := Fintype.ofFinite K
  have hcard : Fintype.card K' = Fintype.card K := by
    have h1 := hcard'
    have h2 := hK
    rw [Nat.card_eq_fintype_card] at h1 h2
    exact h1.trans h2.symm
  let τ : K' ≃+* K := FiniteField.ringEquivOfCardEq hcard
  let ψ : ↥(Xbar M Q Z B) ≃* StatedSp m K := ψ'.trans (statedSpMapEquiv τ)
  refine ⟨ψ, ψ.toMonoidHom.comp (xbarHToXbar M Q Z B), fun s => rfl,
    ψ.surjective.comp (xbarHToXbar_surjective hc), fun s => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one ψ, ψ.injective.eq_iff]
  exact xbarHToXbar_eq_one_iff s

end CFSG.RankThree.GF2n.Stroth80
