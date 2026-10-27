module

public import CFSG.Monster.B.GSide.Setup
public import CFSG.Sporadic.B

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB

noncomputable def shatEquivB :
    Shat ≃* Blueprint.NativeSporadic.B :=
  (iotaEquiv.trans sEquiv).symm

theorem isSimpleGroup_Shat :
    IsSimpleGroup Shat := by
  have := CFSG.Sporadic.B.fam_b_simplicity
  with_reducible_and_instances exact MulEquiv.isSimpleGroup shatEquivB

theorem natCard_Shat_eq_B :
    Nat.card Shat = Nat.card Blueprint.NativeSporadic.B :=
  Nat.card_congr shatEquivB.toEquiv

theorem nonempty_mulEquiv_B_of_amalgam
    {G : Type*} [Group G] [Finite G]
    (horder : Nat.card G = Nat.card Blueprint.NativeSporadic.B)
    (φv : vStab cv0 →* G) (hφv : Function.Injective φv) (φe : cvSetStab {cv0, cw0} →* G)
    (φt : ∀ j, cvSetStab {cv0, cw0, cu j} →* G)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    Nonempty (G ≃* Blueprint.NativeSporadic.B) := by
  obtain ⟨Φ, ⟨hΦv, -, -⟩, -⟩ := native_universal_completion φv φe φt hve hvt het
  have := isSimpleGroup_Shat
  have hker : Φ.ker = ⊥ := by
    rcases (Φ.normal_ker).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hc : (cV0 : vStab cv0) ≠ 1 := by
        intro h1
        have := orderOf_cV0
        rw [h1, orderOf_one] at this
        omega
      apply hc
      apply hφv
      rw [map_one, ← hΦv]
      exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
  have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).1 hker
  have hfinS : Finite Shat := Nat.finite_of_card_ne_zero (by
    rw [natCard_Shat_eq_B, ← horder]
    exact Nat.card_pos.ne')
  have hcard : Nat.card Shat = Nat.card G := by rw [natCard_Shat_eq_B, horder]
  have hbij : Function.Bijective Φ :=
    (Function.Injective.bijective_of_nat_card_le hinj hcard.ge)
  exact ⟨(MulEquiv.ofBijective Φ hbij).symm.trans shatEquivB⟩

end CFSG.Monster.B.GSide
