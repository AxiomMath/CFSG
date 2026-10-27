module

public import CFSG.Quasithin.EmptyFaithful.S151cOm4
public import CFSG.Quasithin.EmptyFaithful.S151cCases

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {U : Type} [CommGroup U] [Finite U]

namespace S151cOm4b

open S152O4 S151cOm4

@[irreducible] def orbitSet (b : Vec) : Finset Vec := Finset.univ.image (fun γ : Gam => act γ b)

@[irreducible] def sumSet (S : Finset Vec) : Finset Vec :=
  S ∪ (S ×ˢ S).image (fun p => p.1 * p.2)

theorem mem_orbitSet_iff {b x : Vec} : x ∈ orbitSet b ↔ ∃ γ : Gam, act γ b = x := by
  simp [orbitSet]

theorem mem_sumSet_iff {S : Finset Vec} {x : Vec} :
    x ∈ sumSet S ↔ x ∈ S ∨ ∃ y ∈ S, ∃ z ∈ S, y * z = x := by
  simp only [sumSet, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro (h | ⟨a, b, ⟨ha, hb⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, rfl⟩
  · rintro (h | ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, ⟨ha, hb⟩, rfl⟩

theorem orbit_sums_univ : ∀ b : Vec, b ≠ 1 → sumSet (sumSet (orbitSet b)) = Finset.univ := by
  decide +kernel

theorem mem_of_sumSet {P : Vec → Prop} (hP : ∀ x y, P x → P y → P (x * y)) {S : Finset Vec}
    (hS : ∀ s ∈ S, P s) : ∀ x ∈ sumSet S, P x := by
  intro x hx
  rcases mem_sumSet_iff.mp hx with h | ⟨y, hy, z, hz, rfl⟩
  · exact hS x h
  · exact hP _ _ (hS _ hy) (hS _ hz)

omit [Finite U] in
theorem isElemAbelian2_zpowers_of_sq {s : MulAut U} (hs : s ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers s) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs

omit [Finite U] in
theorem commV_mono_of_le {X X' : Subgroup (MulAut U)} (h : X ≤ X') : commV X ≤ commV X' := by
  rw [commV_eq_commSub, commV_eq_commSub]
  exact commSub_mono le_rfl h

theorem not_isQuadratic_of_card_four (c : U ≃* Vec) {A : Subgroup (MulAut U)}
    (hA : IsA2 (rhoV c).range A) (h4 : Nat.card A = 4) : ¬ IsQuadratic A := by
  intro hq
  have hr := rAV_of_card_four c hA h4
  have hrkA : rk ↥A = 2 := rk_eq_of_card_eq_pow (n := 2) (by rw [h4]; rfl)
  have hidx : rkIdx (fixV A) = 3 := by
    unfold rAV at hr
    rw [hrkA] at hr
    have h3 : (rkIdx (fixV A) : ℚ) = 3 := by
      push_cast at hr
      linarith
    exact_mod_cast h3
  have hsum := rk_add_rkIdx (fixV A)
  rw [rk_V_eq_four (card_of_equiv c), hidx] at hsum
  obtain ⟨s, hsA, hs1⟩ : ∃ s ∈ A, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA.ne_bot ((Subgroup.eq_bot_iff_forall A).mpr hcon)
  have hs2 : s ^ 2 = 1 := hA.isElemAbelian2.2 s hsA
  have hzA : Subgroup.zpowers s ≤ A := Subgroup.zpowers_le.mpr hsA
  have hA' : IsA2 (rhoV c).range (Subgroup.zpowers s) :=
    hA.mono hzA (fun h => hs1 (Subgroup.zpowers_eq_bot.mp h))
  have h2 : Nat.card ↥(Subgroup.zpowers s) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hs2 hs1
  have hr' := rAV_of_card_two c hA' h2
  have hrkA' : rk ↥(Subgroup.zpowers s) = 1 := rk_eq_of_card_eq_pow (n := 1) (by rw [h2]; rfl)
  have hidx' : rkIdx (fixV (Subgroup.zpowers s)) = 2 := by
    unfold rAV at hr'
    rw [hrkA'] at hr'
    have h3 : (rkIdx (fixV (Subgroup.zpowers s)) : ℚ) = 2 := by
      push_cast at hr'
      linarith
    exact_mod_cast h3
  have hrkcomm : rk (commV (Subgroup.zpowers s)) = 2 := by
    rw [← rkIdx_fixV_zpowers]
    exact hidx'
  have hle : commV (Subgroup.zpowers s) ≤ fixV A := (commV_mono_of_le hzA).trans hq
  have := rk_mono hle
  omega

end S151cOm4b

open S152O4 S151cOm4 S151cOm4b in
theorem isOmegaFourPlus_irreducible {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y)
    {B : Subgroup U} (hB : ∀ y ∈ Y, ∀ b ∈ B, y b ∈ B) (hne : B ≠ ⊥) : B = ⊤ := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall B).mpr hcon)
  have hcb₀ : c b₀ ≠ 1 := fun h => hb₀1 (c.injective (by rw [h, map_one]))
  refine eq_top_iff.mpr fun u _ => ?_
  have hP : ∀ x ∈ orbitSet (c b₀), c.symm x ∈ B := by
    intro x hx
    obtain ⟨γ, rfl⟩ := mem_orbitSet_iff.mp hx
    have : c.symm (act γ (c b₀)) = rhoV c γ b₀ := by
      apply c.injective
      rw [MulEquiv.apply_symm_apply, rhoV_apply]
    rw [this]
    exact hB _ ⟨γ, rfl⟩ b₀ hb₀B
  have hmul : ∀ x y : Vec, c.symm x ∈ B → c.symm y ∈ B → c.symm (x * y) ∈ B := by
    intro x y hx hy
    rw [map_mul]
    exact B.mul_mem hx hy
  have h1 := mem_of_sumSet (P := fun x => c.symm x ∈ B) hmul hP
  have h2 := mem_of_sumSet (P := fun x => c.symm x ∈ B) hmul h1
  have h3 : c u ∈ sumSet (sumSet (orbitSet (c b₀))) := by
    rw [orbit_sums_univ (c b₀) hcb₀]
    exact Finset.mem_univ _
  simpa using h2 (c u) h3

open S152O4 S151cOm4 in
theorem isOmegaFourPlus_twoNilp {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y) :
    TwoNilpAut Y := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  refine ⟨subP.map (rhoV c), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  · rintro _ ⟨γ, rfl⟩ _ ⟨ε, hε, rfl⟩
    exact ⟨γ * ε * γ⁻¹, conj_pow_three γ ε hε, by rw [map_mul, map_mul, map_inv]⟩
  · rw [Subgroup.card_map_of_injective (rhoV_injective c), card_subP]
    decide
  · rintro _ ⟨γ, rfl⟩
    refine ⟨1, γ ^ 2, ?_, ?_⟩
    · show (γ ^ 2) ^ 3 = 1
      rw [← pow_mul]
      exact pow_six γ
    · rw [pow_one, map_pow]

open S152O4 S151cOm4 S151cOm4b in
theorem qOf_eq_of_isOmegaFourPlus {Y : Subgroup (MulAut U)} (hY : IsOmegaFourPlus Y) :
    qOf Y = ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨c, hc⟩ := om4_model hY
  subst hc
  show kq _ 2 = _
  rw [kq_eq_coe_iff]
  refine ⟨?_, ?_⟩
  ·
    have hβ2 : ((DihedralGroup.sr 0, 1) : Gam) ^ 2 = 1 := by decide
    have hβ1 : ((DihedralGroup.sr 0, 1) : Gam) ≠ 1 := by decide
    have hb2 : rhoV c (DihedralGroup.sr 0, 1) ^ 2 = 1 := by rw [← map_pow, hβ2, map_one]
    have hb1 : rhoV c (DihedralGroup.sr 0, 1) ≠ 1 := fun h =>
      hβ1 (rhoV_injective c (by rw [h, map_one]))
    have hA : IsA2 (rhoV c).range (Subgroup.zpowers (rhoV c (DihedralGroup.sr 0, 1))) :=
      ⟨Subgroup.zpowers_le.mpr ⟨_, rfl⟩, fun h => hb1 (Subgroup.zpowers_eq_bot.mp h),
        isElemAbelian2_zpowers_of_sq hb2⟩
    have h2 : Nat.card ↥(Subgroup.zpowers (rhoV c (DihedralGroup.sr 0, 1))) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hb2 hb1
    exact ⟨_, hA, (isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers (exp_of_equiv c) hb2),
      rAV_of_card_two c hA h2⟩
  · intro A hA hAk
    rcases card_two_or_four c hA with h2 | h4
    · rw [rAV_of_card_two c hA h2]
    · exact absurd ((isQuadratic_iff_commSeries_two A).mpr hAk)
        (not_isQuadratic_of_card_four c hA h4)

end CFSG.Quasithin
