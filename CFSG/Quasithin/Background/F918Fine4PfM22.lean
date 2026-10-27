module

public import CFSG.Quasithin.Background.F918Fine4PfCen
public import CFSG.Sporadic.Recognition.M22MultiplierCert

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace F918Fine4Pf

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem isQuasisimple_of_quot_m22 {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) :
    CFSG.IsQuasisimple Q := by
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hsQ : IsSimpleGroup (Q ⧸ Subgroup.center Q) := e.isSimpleGroup
  refine ⟨hQ, hsQ, ?_⟩
  by_contra hc
  push Not at hc
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) this

theorem m22_or_hat_of_quot
    (h : HypF918 T V L V₁ Vp H K) (hK : conjClosure K T = K)
    (hS : IsSporadic .M22 (↥(autIH V₁ Vp H K) ⧸ Subgroup.center ↥(autIH V₁ Vp H K))) :
    IsSporadic .M22 ↥(autIH V₁ Vp H K) ∨
      IsHat ↥(autIH V₁ Vp H K) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  obtain ⟨e⟩ := hS
  have hperf := isPerfect_autIH h Vp
  obtain ⟨-, hdvd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate hperf
      (e.trans (MulEquiv.refl _ : CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
        ↥CFSG.Blueprint.NativeSporadic.M22))
  have hodd := odd_card_center_autIH h hK
  have h13 : Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) = 1 ∨
      Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) = 3 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨m, hm⟩ := hodd
    rw [hm] at hdvd ⊢
    rw [hm] at hle
    have hm5 : m ≤ 5 := by omega
    interval_cases m <;> omega
  rcases h13 with h1 | h3
  · left
    have hbot : Subgroup.center ↥(autIH V₁ Vp H K) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact ⟨((QuotientGroup.quotientBot (G := ↥(autIH V₁ Vp H K))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e⟩
  · exact Or.inr ⟨isQuasisimple_of_quot_m22 hperf e, h3, ⟨e⟩⟩

end F918Fine4Pf

end CFSG.Quasithin
