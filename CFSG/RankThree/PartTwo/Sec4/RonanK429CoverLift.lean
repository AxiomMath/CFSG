module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverBase
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.SectionRank.EvenCover

theorem exists_compatible_cover {H X : Type} [Group H] [Finite H] [Group X] [Finite X]
    [Group.IsPerfect X] {D : Subgroup H} [D.Normal] (hodd : Odd (Nat.card (Subgroup.center X)))
    (hZ : Subgroup.center X ≠ ⊥) (e : X ⧸ Subgroup.center X ≃* H ⧸ D) (hD : Nat.card D ∣ 3)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → ∃ s : H →* E, ∀ g, π (s g) = g) :
    ∃ Ψ : H ≃* X, (∀ g, e (Ψ g : X ⧸ Subgroup.center X) = (g : H ⧸ D)) ∧
      Nat.card (Subgroup.center X) = 3 ∧ Nat.card D = 3 := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ⟩ := hsplit _ _ hsurj hcen (Odd.of_dvd_nat hodd hdvd)
  set φ : H →* X := (MonoidHom.snd H X).comp
    ((pullback (centralQuotientMap e) (QuotientGroup.mk' D)).subtype.comp σ) with hφ
  have hfφ : (centralQuotientMap e).comp φ = QuotientGroup.mk' D := comp_snd_section σ hσ
  have hfφ' : ∀ h, centralQuotientMap e (φ h) = (h : H ⧸ D) := fun h => congrArg (· h) hfφ
  have hker := ker_centralQuotientMap e
  have hsurjφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine eq_top_of_forall_mul_center fun x => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective D (centralQuotientMap e x)
    refine ⟨φ h, ⟨h, rfl⟩, ?_⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hfφ', ← hh, QuotientGroup.mk'_apply,
      inv_mul_cancel]
  have hmap : D.map φ = Subgroup.center X := by
    ext z
    constructor
    · rintro ⟨h, hh, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ', (QuotientGroup.eq_one_iff h).2 hh]
    · intro hz
      obtain ⟨h, rfl⟩ := hsurjφ z
      refine ⟨h, ?_, rfl⟩
      rw [← hker, MonoidHom.mem_ker, hfφ'] at hz
      exact (QuotientGroup.eq_one_iff h).1 hz
  have h3 : Nat.card (Subgroup.center X) = 3 := by
    have hdvd3 : Nat.card (Subgroup.center X) ∣ 3 := by
      rw [← hmap]
      exact (Subgroup.card_map_dvd D φ).trans hD
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd3).resolve_left
      fun h1 => hZ (Subgroup.card_eq_one.mp h1)
  obtain ⟨hD3, hbij⟩ := QuasithinUnique.Ch1.bijective_of_scalar_cover e h3 hD hsurjφ
  exact ⟨MulEquiv.ofBijective φ hbij, fun g => hfφ' g, h3, hD3⟩

@[expose] def CoverNormalForm (L : Type) [Group L] (α : MulAut L) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧ ModThree π (p ^ f) ∧
    ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ ρ : K ≃+* K,
      ((∀ c, ρ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, ρ c = c ^ (piCard π (p ^ f₀) ^ 2)) ∧
      ∃ g ∈ glPi π 3 (p ^ f) K, ∃ e : L ≃* slPi π 3 (p ^ f) K,
        ∀ l, (e (α l) : Matrix.GeneralLinearGroup (Fin 3) K) = g * frobGL ρ (e l) * g⁻¹

end CFSG.RankThree.PartTwo.Sec4.RonanK429
