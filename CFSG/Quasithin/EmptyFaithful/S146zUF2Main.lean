module

public import CFSG.Quasithin.EmptyFaithful.S146zUF0Cond
public import CFSG.Quasithin.EmptyFaithful.S146zUF2Pair
public import CFSG.Quasithin.EmptyFaithful.S146zUF2Trans

public section

namespace CFSG.Quasithin.S146zU

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace UF2

section Kernels

variable {Gam Y VE F : Type} [Group Gam] [CommGroup Y] [CommGroup VE] [CommGroup F]
  {ρY : Gam →* MulAut Y} {ρE : Gam →* MulAut VE} {ρF : Gam →* MulAut F}

theorem rhoE_eq_one_of_rhoY_eq_one {ι : VE →* Y} (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (ρE g v) = ρY g (ι v)) {g : Gam} (hg : ρY g = 1) : ρE g = 1 := by
  ext v
  apply hι
  rw [hιρ, hg]
  rfl

theorem rhoF_eq_one_of_rhoY_eq_one {q : Y →* F} (hq : Function.Surjective q)
    (hqρ : ∀ g y, q (ρY g y) = ρF g (q y)) {g : Gam} (hg : ρY g = 1) : ρF g = 1 := by
  ext f
  obtain ⟨y, rfl⟩ := hq f
  rw [← hqρ, hg]
  rfl

end Kernels

section Sides

variable {Gam : Type} [Group Gam] {Y : Type} [CommGroup Y] [Finite Y]

theorem eSide {VE : Type} [CommGroup VE] [Finite VE] (hVE : ∀ v : VE, v ^ 2 = 1)
    {ρY : Gam →* MulAut Y} {ρE : Gam →* MulAut VE} {ι : VE →* Y} (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (ρE g v) = ρY g (ι v)) (hkE : ∀ g, ρE g = 1 → ρY g = 1)
    {L₁ L₂ : Subgroup (MulAut VE)} {τ : MulAut VE} (PE : PairPkg ρE.range L₁ L₂ τ)
    {A : Subgroup (MulAut Y)} (hAΓ : A ≤ ρY.range) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(ι.range ⊓ fixV A) ≤ Nat.card ↥ι.range ∧
    (Nat.card ↥ι.range = Nat.card ↥A * Nat.card ↥(ι.range ⊓ fixV A) →
      ∀ s ∈ ι.range, s ∉ fixV A → 4 ≤ (Set.range fun a : ↥A => (a : MulAut Y) s).ncard) := by
  have hkE' : ∀ g, ρY g = 1 → ρE g = 1 := fun g hg => rhoE_eq_one_of_rhoY_eq_one hι hιρ hg
  have hAE := transport_le_range ρY ρE A
  have hAE1 := transport_ne_bot hkE hAΓ hA1
  have hAE2 := isElemAbelian2_transport hkE' hA2
  have hcardA : Nat.card ↥(transport ρY ρE A) = Nat.card ↥A := card_transport hkE' hkE hAΓ
  have hcardF : Nat.card ↥(ι.range ⊓ fixV A) = Nat.card ↥(fixV (transport ρY ρE A)) := by
    have heq : ι.range ⊓ fixV A = (fixV (transport ρY ρE A)).map ι := by
      ext y
      constructor
      · rintro ⟨⟨v, rfl⟩, hy⟩
        exact ⟨v, (mem_fixV_transport_iff hι hιρ hAΓ).mp hy, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨v, rfl⟩, (mem_fixV_transport_iff hι hιρ hAΓ).mpr hv⟩
    rw [heq, Subgroup.card_map_of_injective hι]
  have hrange : Nat.card ↥ι.range = Nat.card VE := card_range_of_injective hι
  refine ⟨?_, fun hEq s hs hsA => ?_⟩
  · rw [hrange, hcardF, ← hcardA]
    exact pair_card_mul_card_fixV_le PE hVE hAE hAE1 hAE2
  · obtain ⟨s', rfl⟩ := hs
    have hcard : Nat.card VE =
        Nat.card ↥(transport ρY ρE A) * Nat.card ↥(fixV (transport ρY ρE A)) := by
      rw [hcardA, ← hcardF, ← hrange]
      exact hEq
    have hoff := pair_isFFStarOffender_of_card_eq PE hVE hAE hAE1 hAE2 hcard
    have hs' : s' ∉ fixV (transport ρY ρE A) := fun h =>
      hsA ((mem_fixV_transport_iff hι hιρ hAΓ).mpr h)
    have h4 := pair_four_mul_card_stabilizer_le PE hoff hs'
    exact (four_le_ncard_range _ s' h4).trans (ncard_orbit_le hι hιρ A s')

theorem H3_of_pair {F : Type} [CommGroup F] [Finite F] (hF : ∀ f : F, f ^ 2 = 1)
    {ρY : Gam →* MulAut Y} {ρF : Gam →* MulAut F} {q : Y →* F} (hq : Function.Surjective q)
    (hqρ : ∀ g y, q (ρY g y) = ρF g (q y)) (hkF : ∀ g, ρF g = 1 → ρY g = 1)
    {L₁' L₂' : Subgroup (MulAut F)} {τ' : MulAut F} (PF : PairPkg ρF.range L₁' L₂' τ')
    {A : Subgroup (MulAut Y)} (hAΓ : A ≤ ρY.range) (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) :
    Nat.card ↥A * Nat.card ↥(cF A q.ker) ≤ Nat.card Y := by
  have hkF' : ∀ g, ρY g = 1 → ρF g = 1 := fun g hg => rhoF_eq_one_of_rhoY_eq_one hq hqρ hg
  have hAF := transport_le_range ρY ρF A
  have hAF1 := transport_ne_bot hkF hAΓ hA1
  have hAF2 := isElemAbelian2_transport hkF' hA2
  have hcardA : Nat.card ↥(transport ρY ρF A) = Nat.card ↥A := card_transport hkF' hkF hAΓ
  have hcF : cF A q.ker = (fixV (transport ρY ρF A)).comap q := by
    ext y
    exact mem_cF_ker_iff hqρ hAΓ
  have hcardcF : Nat.card ↥(cF A q.ker) =
      Nat.card ↥q.ker * Nat.card ↥(fixV (transport ρY ρF A)) := by
    rw [hcF]
    exact card_comap_of_surjective hq _
  rw [hcardcF, card_eq_card_ker_mul hq, ← hcardA]
  have h1 := pair_card_mul_card_fixV_le PF hF hAF hAF1 hAF2
  calc Nat.card ↥(transport ρY ρF A) *
        (Nat.card ↥q.ker * Nat.card ↥(fixV (transport ρY ρF A)))
      = Nat.card ↥q.ker * (Nat.card ↥(transport ρY ρF A) *
        Nat.card ↥(fixV (transport ρY ρF A))) := by ring
    _ ≤ Nat.card ↥q.ker * Nat.card F := Nat.mul_le_mul_left _ h1

omit [Finite Y] in
theorem H5F_of_pair {F : Type} [CommGroup F] [Finite F] (hF : ∀ f : F, f ^ 2 = 1)
    {ρY : Gam →* MulAut Y} {ρF : Gam →* MulAut F} {q : Y →* F} (hq : Function.Surjective q)
    (hqρ : ∀ g y, q (ρY g y) = ρF g (q y)) (hkF : ∀ g, ρF g = 1 → ρY g = 1)
    {L₁' L₂' : Subgroup (MulAut F)} {τ' : MulAut F} (PF : PairPkg ρF.range L₁' L₂' τ')
    {A : Subgroup (MulAut Y)} (hAΓ : A ≤ ρY.range) (hA1 : A ≠ ⊥) :
    ∃ y₁ y₂ : Y, ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ y₁ * y₁⁻¹ ∉ q.ker ∧ a₂ y₂ * y₂⁻¹ ∉ q.ker ∧
      (a₁ y₁ * y₁⁻¹)⁻¹ * (a₂ y₂ * y₂⁻¹) ∉ q.ker := by
  have hAF := transport_le_range ρY ρF A
  have hAF1 := transport_ne_bot hkF hAΓ hA1
  obtain ⟨x₁, hx₁, f₁, x₂, hx₂, f₂, hc₁, hc₂, hc₁₂⟩ :=
    exists_two_comm hF (pair_card_commV_ge_four PF hAF hAF1)
  obtain ⟨g₁, hg₁, rfl⟩ := mem_transport.mp hx₁
  obtain ⟨g₂, hg₂, rfl⟩ := mem_transport.mp hx₂
  obtain ⟨y₁, rfl⟩ := hq f₁
  obtain ⟨y₂, rfl⟩ := hq f₂
  have hcomm : ∀ g y, q (ρY g y * y⁻¹) = ρF g (q y) * (q y)⁻¹ := fun g y => by
    rw [map_mul, map_inv, hqρ]
  refine ⟨y₁, y₂, ρY g₁, hg₁, ρY g₂, hg₂, ?_, ?_, ?_⟩
  · intro h
    exact hc₁ (by rw [← hcomm]; exact h)
  · intro h
    exact hc₂ (by rw [← hcomm]; exact h)
  · intro h
    apply hc₁₂
    have h1 := MonoidHom.mem_ker.mp h
    rw [map_mul, map_inv, hcomm, hcomm, inv_mul_eq_one] at h1
    exact h1

end Sides

end UF2

section Headline

variable {Gam : Type} [Group Gam] {Y : Type} [CommGroup Y] [Finite Y]

theorem nt_of_pairPkg_E {VE : Type} [CommGroup VE] [Finite VE] (ρY : Gam →* MulAut Y)
    (ρE : Gam →* MulAut VE) (ι : VE →* Y) (hι : Function.Injective ι)
    (hιρ : ∀ g v, ι (ρE g v) = ρY g (ι v)) (hkE : ∀ g, ρE g = 1 → ρY g = 1)
    {L₁ L₂ : Subgroup (MulAut VE)} {τ : MulAut VE} (PE : PairPkg ρE.range L₁ L₂ τ) :
    ∀ x ∈ ρY.range, x ≠ 1 → 4 ≤ Nat.card ↥(commV (Subgroup.zpowers x)) := by
  rintro _ ⟨g, rfl⟩ hg1
  have hE1 : ρE g ≠ 1 := fun h => hg1 (hkE g h)
  have h4 := UC2.nt_of_twoNat PE.twoNat PE.comm PE.card₁ PE.card₂ PE.norm PE.cen
    (x := ρE g) ⟨g, rfl⟩ hE1
  refine h4.trans ?_
  have hle : (commV (Subgroup.zpowers (ρE g))).map ι ≤ commV (Subgroup.zpowers (ρY g)) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : ι (((ρE g) ^ k) v) = ((ρY g) ^ k) (ι v) := by
      have := hιρ (g ^ k) v
      rwa [map_zpow, map_zpow] at this
    show ι (((ρE g) ^ k) v * v⁻¹) ∈ commV (Subgroup.zpowers (ρY g))
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨(ρY g) ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, ι v, rfl⟩
  calc Nat.card ↥(commV (Subgroup.zpowers (ρE g)))
      = Nat.card ↥((commV (Subgroup.zpowers (ρE g))).map ι) :=
        (Subgroup.card_map_of_injective hι).symm
    _ ≤ Nat.card ↥(commV (Subgroup.zpowers (ρY g))) := Subgroup.card_le_of_le hle

end Headline

theorem module_claim_false {Gam : Type} [Group Gam]
    {Y : Type} [CommGroup Y] [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1) {VE : Type} [CommGroup VE]
    [Finite VE] (hVE : ∀ v : VE, v ^ 2 = 1) {F : Type} [CommGroup F] [Finite F]
    (hF : ∀ f : F, f ^ 2 = 1)
    (ρY : Gam →* MulAut Y) (ρE : Gam →* MulAut VE) (ρF : Gam →* MulAut F)
    (ι : VE →* Y) (hι : Function.Injective ι) (q : Y →* F) (hq : Function.Surjective q)
    (hexact : q.ker = ι.range)
    (hιρ : ∀ g v, ι (ρE g v) = ρY g (ι v)) (hqρ : ∀ g y, q (ρY g y) = ρF g (q y))
    (hkE : ∀ g, ρE g = 1 → ρY g = 1) (hkF : ∀ g, ρF g = 1 → ρY g = 1)
    {L₁ L₂ : Subgroup (MulAut VE)} {τ : MulAut VE} (PE : PairPkg ρE.range L₁ L₂ τ)
    {L₁' L₂' : Subgroup (MulAut F)} {τ' : MulAut F} (PF : PairPkg ρF.range L₁' L₂' τ')
    (hgeom : (∀ x ∈ ρY.range, x ≠ 1 → 4 ≤ Nat.card ↥(commV (Subgroup.zpowers x))) →
      ∃ A : Subgroup (MulAut Y), A ≤ ρY.range ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧
        Nat.card Y ≤ Nat.card A * Nat.card A * Nat.card ↥(fixV A) ∧
        (Nat.card Y = Nat.card A * Nat.card A * Nat.card ↥(fixV A) →
          ∃ (D : Subgroup Y) (c : Y), Nat.card Y = Nat.card A * Nat.card D ∧
            ∀ a ∈ A, ∀ d ∈ D, a d * d⁻¹ = 1 ∨ a d * d⁻¹ = c)) : False := by
  have _ := hY
  obtain ⟨A, hAΓ, hA1, hA2, H1, H4⟩ := hgeom (nt_of_pairPkg_E ρY ρE ι hι hιρ hkE PE)
  have hEA : ∀ a ∈ A, ∀ e ∈ ι.range, a e ∈ ι.range := by
    rintro a ha _ ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := hAΓ ha
    exact ⟨ρE g v, hιρ g v⟩
  obtain ⟨H2, H5⟩ := UF2.eSide hVE hι hιρ hkE PE hAΓ hA1 hA2
  have H3 : Nat.card ↥A * Nat.card ↥(cF A ι.range) ≤ Nat.card Y := by
    rw [← hexact]
    exact UF2.H3_of_pair hF hq hqρ hkF PF hAΓ hA1 hA2
  have H5F : Nat.card Y = Nat.card ↥A * Nat.card ↥(cF A ι.range) →
      ∃ y₁ y₂ : Y, ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ y₁ * y₁⁻¹ ∉ ι.range ∧ a₂ y₂ * y₂⁻¹ ∉ ι.range ∧
        (a₁ y₁ * y₁⁻¹)⁻¹ * (a₂ y₂ * y₂⁻¹) ∉ ι.range := fun _ => by
    rw [← hexact]
    exact UF2.H5F_of_pair hF hq hqρ hkF PF hAΓ hA1
  exact numerics_core_cond hEA H1 H2 H3 H4 H5 H5F

end CFSG.Quasithin.S146zU
