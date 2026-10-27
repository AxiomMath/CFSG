module

public import CFSG.RankThree.PartOne.S11c.HeisenbergSylow
public import CFSG.RankThree.PartOne.S11c.SuzukiReeTitsFiveFixed
public import CFSG.RankThree.PartOne.KLR.SectorOrder
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.PartOne.KLR.SectorTori

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.Chevalley

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem exists_abelian_of_twisted_torus (w : WeylGroup ReeTag.F4.tag)
    (E : Subgroup (ModGL ReeTag.F4.tag L)) (hEH : E ≤ torusGroup ReeTag.F4.tag L)
    (hEF : E ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ T : Subgroup (ReeTag.F4.reeGamma K a), Nat.card T = Nat.card E ∧
      ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  classical
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  set E' : Subgroup (ModGL ReeTag.F4.tag L) := E.map (MulAut.conj g₀).toMonoidHom with hE'
  have hE'θ : ∀ u ∈ E', ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = u := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hEF he)
    exact D.exists_theta_of_fixed hadj hfix
  let T : Subgroup (ReeTag.F4.reeGamma K a) := E'.comap (thetaGamma L a)
  refine ⟨T, ?_, ?_⟩
  · have e1 : Nat.card E = Nat.card E' :=
      Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj g₀).toMonoidHom
        (MulAut.conj g₀).injective).toEquiv
    rw [e1]
    refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨thetaGamma L a γ.1, γ.2⟩) ⟨?_, ?_⟩)
    · intro γ₁ γ₂ h12
      exact Subtype.ext (thetaGamma_injective L (congrArg Subtype.val h12))
    · rintro ⟨u, hu⟩
      obtain ⟨γ, rfl⟩ := hE'θ u hu
      exact ⟨⟨γ, hu⟩, rfl⟩
  · intro x hx y hy
    obtain ⟨e1, he1, h1⟩ := hx
    obtain ⟨e2, he2, h2⟩ := hy
    have hcomm : e1 * e2 = e2 * e1 :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hEH he1))
        (torusGroup_le_diagonalGroup (hEH he2))
    apply thetaGamma_injective L
    rw [map_mul, map_mul, ← h1, ← h2, ← map_mul, ← map_mul, hcomm]

end Sector

theorem five_dvd_phi4 (a : ℕ) : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have h : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  rw [h]
  omega

theorem reeGamma_fiveSubgroupsCommute {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FiveSubgroupsCommute (ReeTag.F4.reeGamma K a) := by
  classical
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have h5 : 5 ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := five_dvd_phi4 a
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rcases dvd_phi4_cases Nat.prime_five (by norm_num) h5 with ⟨hpp, -⟩ | ⟨hpm, -⟩
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4p D.isFrob
    obtain ⟨T, hT, hab⟩ := exists_abelian_of_twisted_torus D wPhi4p E hEH hEF
    refine fiveSubgroupsCommute_of_abelian T ?_ hab
    rw [hT, hE]
    exact pow_factorization_card_reeGamma_dvd_phi4p hK Nat.prime_five (by norm_num) hpp
  · obtain ⟨E, hEH, hEF, hE⟩ := torus_phi4m D.isFrob
    obtain ⟨T, hT, hab⟩ := exists_abelian_of_twisted_torus D wPhi4m E hEH hEF
    refine fiveSubgroupsCommute_of_abelian T ?_ hab
    rw [hT, hE]
    exact pow_factorization_card_reeGamma_dvd_phi4m hK Nat.prime_five (by norm_num) hpm

theorem exists_gamma_of_largeRee_model {X : Type} [Group X] {ℓ f : ℕ}
    (h : ReeTitsModel X .twistedF4 ℓ f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ^ (2 * a + 1) ∧ Nonempty (X ≃* ReeTag.F4.reeGamma K a) := by
  obtain ⟨hFin, -, -, hℓ2, ⟨a, ha, hfa⟩, hmodel⟩ := ReeTag.large_Ree_model_Schreier X ℓ f h
  subst hℓ2
  obtain ⟨-, a', hfa', hrel⟩ := h
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K ReeTag.F4.prime := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have haa : a' = a := by omega
  subst haa
  obtain ⟨e'⟩ := hmodel a' K hfa' hKcard ⟨e⟩
  exact ⟨a', K, inferInstance, inferInstance, hchar, by rw [hKcard, hfa'], ⟨e'⟩⟩

theorem largeReeFiveFixedExcluded_aux : LargeReeFiveFixedExcluded := by
  intro H _ _ hrank X hX β K hFive ℓ f h
  have hK : StatedClassicalModel K .PSU 3 5 1 := hFive.2.2
  obtain ⟨a, Kf, _, _, hchar, hKf, ⟨e⟩⟩ := exists_gamma_of_largeRee_model h
  let ι : ↥K →* ReeTag.F4.reeGamma Kf a := e.toMonoidHom.comp K.subtype
  have hι : Function.Injective ι := e.injective.comp K.subtype_injective
  exact no_unitary_three_five_of_fiveSubgroupsCommute (reeGamma_fiveSubgroupsCommute hKf) hK ι hι

theorem largeReeFiveFixedExcluded_holds :
    LargeReeFiveFixedExcluded := by
  exact largeReeFiveFixedExcluded_aux

theorem fiveFixedExcludesSuzukiReeTits_holds :
    FiveFixedExcludesSuzukiReeTits :=
  fiveFixedExcludesSuzukiReeTits_of_largeRee largeReeFiveFixedExcluded_holds

end CFSG.RankThree.PartOne.HNRed
