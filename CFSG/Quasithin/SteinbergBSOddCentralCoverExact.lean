module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {E : Type*} [Group E]

theorem ker_eq_bot_of_section_of_closure_involutions [Finite E] {H : Type*} [Group H]
    (hgen : closure {x : E | orderOf x = 2} = ⊤) (π : E →* H) (s : H →* E)
    (hs : ∀ h, π (s h) = h) (hcen : π.ker ≤ center E) (hodd : Odd (Nat.card π.ker)) :
    π.ker = ⊥ := by
  have hinv : closure {x : E | orderOf x = 2} ≤ s.range := by
    rw [closure_le]
    intro x hx
    have hx' : orderOf x = 2 := hx
    have hx2 : x * x = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hx', pow_two] at h
    set y := s (π x) with hy
    have hy2 : y * y = 1 := by rw [hy, ← map_mul, ← map_mul, hx2, map_one, map_one]
    have hcker : x * y⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, hs, mul_inv_cancel]
    set c := x * y⁻¹ with hc
    have hcZ := mem_center_iff.1 (hcen hcker)
    have hxc : x = c * y := by rw [hc, inv_mul_cancel_right]
    have hc2 : c * c = 1 := by
      have h1 : x * x = c * c * (y * y) := by
        rw [hxc]
        calc c * y * (c * y) = c * (y * c) * y := by group
          _ = c * (c * y) * y := by rw [hcZ y]
          _ = c * c * (y * y) := by group
      rw [hy2, mul_one, hx2] at h1
      exact h1.symm
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hc2])
      have h2 : orderOf c ∣ Nat.card π.ker := by
        have h3 := orderOf_dvd_natCard (⟨c, hcker⟩ : π.ker)
        rwa [Subgroup.orderOf_mk] at h3
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h1 h2)
    refine ⟨π x, ?_⟩
    show y = x
    rw [hxc, hc1, one_mul]
  have hrange : s.range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact hinv
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨h, rfl⟩ : c ∈ s.range := hrange ▸ mem_top c
  have h1 : h = 1 := (hs h).symm.trans (MonoidHom.mem_ker.1 hc)
  rw [mem_bot, h1, map_one]

theorem unique_involution_generated_odd_central_linear_or_suzuki_cover_is_exact
    [Finite E]
    (hgen : closure {x : E | orderOf x = 2} = ⊤) (R : Subgroup E) [R.Normal]
    (hRZ : R ≤ center E) (hRodd : Odd (Nat.card R))
    (hmodel : (∃ (f : ℕ) (k : Type) (_ : Field k), 2 ≤ f ∧ Nat.card k = 2 ^ f ∧
        Nonempty (E ⧸ R ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) ∨
      ∃ (a : ℕ) (k : Type) (_ : Field k), 1 ≤ a ∧ Nat.card k = 2 ^ (2 * a + 1) ∧
        Nonempty (E ⧸ R ≃* CFSG.Blueprint.suzukiGroup a k)) :
    R = ⊥ ∧ Function.Bijective (QuotientGroup.mk' R) ∧
      ∀ (X : Type*) [Group X], Nonempty (E ⧸ R ≃* X) → Nonempty (E ≃* X) := by
  have key : ∀ {H : Type} [Group H] (η : E →* H), η.ker = R →
      (∃ s : H →* E, ∀ h, η (s h) = h) → R = ⊥ := by
    intro H _ η hker ⟨s, hs⟩
    rw [← hker]
    exact ker_eq_bot_of_section_of_closure_involutions hgen η s hs (by rw [hker]; exact hRZ)
      (by rw [hker]; exact hRodd)
  have hkerq : ∀ {H : Type} [Group H] (e : E ⧸ R ≃* H),
      (e.toMonoidHom.comp (QuotientGroup.mk' R)).ker = R := by
    intro H _ e
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurjq : ∀ {H : Type} [Group H] (e : E ⧸ R ≃* H),
      Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' R)) := fun e =>
    e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hR : R = ⊥ := by
    rcases hmodel with ⟨f, k, _, hf, hk, ⟨e⟩⟩ | ⟨a, k, _, ha, hk, ⟨e⟩⟩
    · have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
      have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hk
      set e' := e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).trans
        (LinearCover.projectiveSLTwoEquivSL k))
      obtain ⟨s, hs, -, -⟩ :=
        CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting (le_refl 2)
          (hsurjq e') (by rw [hkerq e']; exact hRZ) (by rw [hkerq e']; exact hRodd)
      exact key _ (hkerq e') ⟨s, hs⟩
    · have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
      set e' := e.trans
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hk)
      obtain ⟨⟨σ, hσ, -⟩, -⟩ := CFSG.SectionRank.suzuki_odd_central_extension_splitting a
        (by omega) _ (hsurjq e') (by rw [hkerq e']; exact hRZ) (by rw [hkerq e']; exact hRodd)
      exact key _ (hkerq e') ⟨σ, fun h => DFunLike.congr_fun hσ h⟩
  have hbij : Function.Bijective (QuotientGroup.mk' R) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hR),
      QuotientGroup.mk'_surjective R⟩
  exact ⟨hR, hbij, fun X _ ⟨e⟩ => ⟨(MulEquiv.ofBijective _ hbij).trans e⟩⟩

end CFSG.Quasithin.SteinbergBS
