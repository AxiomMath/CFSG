module

public import CFSG.Quasithin.Background.SmithB45U33Mid
public import CFSG.Quasithin.Background.SmithB42U33SixProof
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Orbit
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor

variable {V : Type} [CommGroup V] [Finite V]

theorem natural_of_irr
    (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} (hP : B42TypeU33 ↥L)
    (hirr : ∀ U : Subgroup V, (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcard : Nat.card V ≤ 2 ^ 12) : Nat.card V = 2 ^ 6 ∧ G2NaturalDerived L ⊤ ⊥ 1 := by
  classical
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary (fun v : V => by rw [← pow_two]; exact hV v)
  set ψ := binPsi θ with hψ
  obtain ⟨θL⟩ := B42U33.nonempty_equiv_g2Derived hP
  let σ : ↥(g2Derived (ZMod 2)) →* (M →ₗ[ZMod 2] M) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp
      (ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom))
  have hσ : ∀ h u, σ h u = ψ ((θL.symm h : ↥L) : MulAut V) u := fun _ _ => rfl
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ h, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h2 := hU (θL ⟨y, hy⟩) u hu
    rwa [hσ, MulEquiv.symm_apply_apply] at h2
  have hntσ : ∃ h, σ h ≠ 1 := by
    have h6048 := B42U33.card_of_b42TypeU33 hP
    have : Nontrivial ↥L := by
      rw [← Finite.one_lt_card_iff_nontrivial, h6048]
      norm_num
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    refine ⟨θL x, fun h => hx1 ?_⟩
    have h2 : ψ ((x : ↥L) : MulAut V) = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have h3 := h
      change (ψ ((θL.symm (θL x) : ↥L) : MulAut V)).toLinearMap = 1 at h3
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3
    exact Subtype.ext (ψ.injective (h2.trans (map_one ψ).symm))
  have hMV : Nat.card M = Nat.card V := (natCard_eq θ).symm
  have h6 := B45U33.card_le_of_g2Derived σ hntσ hirrM (hMV ▸ hcard)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 := B42U33.six_le_of_card_dvd hV hk L (B42U33.card_of_b42TypeU33 hP)
  have hV6 : Nat.card V = 2 ^ 6 := by
    rw [hMV, hk] at h6
    rw [hk, show k = 6 from le_antisymm ((Nat.pow_le_pow_iff_right (by norm_num)).mp h6) hk6]
  exact ⟨hV6, B42U33.u33SixNatural V hV hV6 L hP⟩

end CFSG.Quasithin.H13.L32A.M753
