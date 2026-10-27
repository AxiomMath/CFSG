module

public import CFSG.Quasithin.Background.F7TwoInvBenderInner
public import CFSG.CGT.Timmesfeld75.BenderInputsBasic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GH74.Uniqueness.Bender

theorem benderType_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel S p f) : ∃ a : ℕ, 1 ≤ a ∧ BenderType S (2 * a + 1) 2 1 := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  let e' : S ≃* CFSG.Open.Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  exact ⟨a, ha, .suzuki a ha (e'.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))⟩

theorem invAutGen_of_benderType_suzuki {S : Type} [Group S]
    [Finite S] {n e : ℕ} (h : BenderType S n 2 e) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  intro φ hφ2 hφ1
  obtain ⟨v, hv2, hv⟩ := h.exists_inner_of_sq_eq_one_suzuki φ hφ2
  have hφ : φ = MulAut.conj v := MulEquiv.ext fun k => by rw [hv k]; rfl
  have hv1 : v ≠ 1 := fun h1 => hφ1 (by rw [hφ, h1, map_one])
  rw [hφ]
  exact invAutGen_conj_of_benderType h hv2 hv1

theorem invAutGen_of_suzukiModel {S : Type} [Group S] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel S p f) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  obtain ⟨a, -, hT⟩ := benderType_of_suzukiModel h
  have : Finite S := CFSG.CGT.Timmesfeld75.finite_of_isBenderGroup
    (isBenderGroup_iff_exists_benderType.mpr ⟨_, _, _, hT⟩)
  exact invAutGen_of_benderType_suzuki hT

end CFSG.Quasithin.F7Two
