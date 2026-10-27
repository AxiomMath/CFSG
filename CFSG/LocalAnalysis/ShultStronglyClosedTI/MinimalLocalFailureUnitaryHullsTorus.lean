module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsCoordinates
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G]

theorem map_centralizer_eq {L : Subgroup G} {P : Type*} [Group P] (θ : P ≃* L)
    (X : Subgroup P) :
    (Subgroup.centralizer (X : Set P)).map (L.subtype.comp θ.toMonoidHom) =
      L ⊓ Subgroup.centralizer ((X.map (L.subtype.comp θ.toMonoidHom) : Subgroup G) : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(θ x).2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    change (θ y : G) * (θ x : G) = (θ x : G) * (θ y : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_iff.mp hx y hy]
  · rintro ⟨hgL, hg⟩
    refine ⟨θ.symm ⟨g, hgL⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, ?_⟩
    · apply θ.injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.mp hg _ ⟨y, hy, rfl⟩
    · change ((θ (θ.symm ⟨g, hgL⟩) : L) : G) = g
      rw [MulEquiv.apply_symm_apply]

namespace UnitaryHullCoordinates

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G} {L : Subgroup G}
  (c : UnitaryHullCoordinates H z beta t L)

theorem map_pairStabilizerL (htL : t ∈ L) (ht2 : t * t = 1)
    (hbeta : beta = rightCosetMk H t) :
    (pairStabilizerL c.J c.C c.hJ c.hC).map (L.subtype.comp c.θ.toMonoidHom) =
      pairPointStabilizer H beta ⊓ L := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(c.mem_pairPointStabilizer_iff htL ht2 hbeta x).mpr hx, (c.θ x).2⟩
  · rintro ⟨hgB, hgL⟩
    refine ⟨c.θ.symm ⟨g, hgL⟩, (c.mem_pairPointStabilizer_iff htL ht2 hbeta _).mp ?_, ?_⟩
    · rw [MulEquiv.apply_symm_apply]
      exact hgB
    · change ((c.θ (c.θ.symm ⟨g, hgL⟩) : L) : G) = g
      rw [MulEquiv.apply_symm_apply]

theorem exists_torus [Finite G] (htL : t ∈ L) (ht2 : t * t = 1)
    (hbeta : beta = rightCosetMk H t) :
    let Φ := L.subtype.comp c.θ.toMonoidHom
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let A₀ := (torusL c.J c.C c.hJ).map Φ
    A₀ ≤ pairPointStabilizer H beta ⊓ L ∧ IsCyclic A₀ ∧ Odd (Nat.card A₀) ∧
      A₀ ≤ Subgroup.centralizer (K : Set G) ∧
      pairPointStabilizer H beta ⊓ L ⊓ Subgroup.centralizer (Q : Set G) = A₀ ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card Q + 1 ∧
        ∃ A : Subgroup G, A ≤ A₀ ∧ IsCyclic A ∧ IsPGroup p A ∧ A ≠ ⊥ ∧
          (∃ γ : normOne c.J, ((γ : c.kˣ) : c.k) ^ 3 ≠ 1 ∧
            Φ (QuotientGroup.mk' c.C (torusHom c.J c.hJ γ)) ∈ A) ∧
          (∃ e : K × A₀ ≃* (L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G),
            ∀ x, (e x : G) = (x.1 : G) * (x.2 : G)) ∧
          ∀ g ∈ L ⊓ Subgroup.centralizer (A : Set G), g ^ 2 = 1 → g ∈ K := by
  intro Φ K Q A₀
  have hΦ : Function.Injective Φ := c.map_injective
  obtain ⟨-, -, -, -, -, -, -, hA₀cyc, -, -, -, hpairc,
      ⟨p, hp, hpodd, hpq, A', hA'A₀, hA'cyc, hA'p, hA'1, γ, hγ3, hγA'⟩, hcent, -, -⟩ :=
    unitary_central_cover_subline_torus_centralizer c.J c.f c.hf c.hcard c.hfixed c.hJ c.C c.hC
  have hq2 : 2 < 2 ^ c.f :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos c.hf)
  have hM : Nat.card (normOne c.J) = 2 ^ c.f + 1 :=
    card_normOne Nat.prime_two hq2 c.hcard c.hfixed
  have hf2 := c.hf
  have hqodd : Odd (2 ^ c.f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hA₀card : Nat.card A₀ = Nat.card (torusL c.J c.C c.hJ) :=
    Subgroup.card_map_of_injective hΦ
  have hA₀odd : Odd (Nat.card A₀) := by
    rw [hA₀card]
    refine Odd.of_dvd_nat hqodd ⟨Nat.card c.C, ?_⟩
    rw [← hM, card_torusL_mul_card c.hJ c.hC]
  have hKeq : K = (sublineL c.J c.C c.hJ).map Φ := c.subline.symm
  have hcentK : A₀ ≤ Subgroup.centralizer (K : Set G) := by
    rw [hKeq]
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    change (c.θ x : G) * (c.θ y : G) = (c.θ y : G) * (c.θ x : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      sublineL_commute_torusL c.hJ x hx y hy]
  have hpairB := c.map_pairStabilizerL htL ht2 hbeta
  have hA₀B : A₀ ≤ pairPointStabilizer H beta ⊓ L := by
    rw [← hpairB]
    exact Subgroup.map_mono (torusL_le_pairStabilizerL c.hJ c.hC)
  have hpairQ : pairPointStabilizer H beta ⊓ L ⊓ Subgroup.centralizer (Q : Set G) = A₀ := by
    have h := congrArg (Subgroup.map Φ) hpairc
    rw [Subgroup.map_inf _ _ _ hΦ, hpairB, map_centralizer_eq c.θ, c.upper] at h
    change _ = Subgroup.map Φ (torusL c.J c.C c.hJ)
    rw [← h]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  obtain ⟨hcentA', ⟨e', he'⟩, hinvA'⟩ := hcent A' hA'A₀ ⟨γ, hγ3, hγA'⟩
  set A := A'.map Φ
  have hCmap := map_centralizer_eq c.θ A'
  let eK : sublineL c.J c.C c.hJ ≃* K :=
    ((sublineL c.J c.C c.hJ).equivMapOfInjective Φ hΦ).trans (MulEquiv.subgroupCongr c.subline)
  let eA : torusL c.J c.C c.hJ ≃* A₀ := (torusL c.J c.C c.hJ).equivMapOfInjective Φ hΦ
  let eC : Subgroup.centralizer (A' : Set (c.J.specialSubgroup ⧸ c.C)) ≃*
      (L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    ((Subgroup.centralizer (A' : Set (c.J.specialSubgroup ⧸ c.C))).equivMapOfInjective Φ
      hΦ).trans (MulEquiv.subgroupCongr hCmap)
  have heK : ∀ x : K, Φ (eK.symm x) = x := fun x => by
    have h := congrArg (fun y : K => (y : G)) (eK.apply_symm_apply x)
    exact h
  have heA : ∀ x : A₀, Φ (eA.symm x) = x := fun x => by
    have h := congrArg (fun y : A₀ => (y : G)) (eA.apply_symm_apply x)
    exact h
  refine ⟨hA₀B, ?_, hA₀odd, hcentK, hpairQ, p, hp, hpodd, ?_, A, Subgroup.map_mono hA'A₀, ?_,
    hA'p.map Φ, ?_, ⟨γ, hγ3, ⟨_, hγA', rfl⟩⟩,
    ⟨((eK.symm.prodCongr eA.symm).trans e').trans eC, fun x => ?_⟩, ?_⟩
  · exact isCyclic_of_surjective ((torusL c.J c.C c.hJ).equivMapOfInjective Φ hΦ).toMonoidHom
      (MulEquiv.surjective _)
  · rw [c.hq]
    exact hpq
  · exact isCyclic_of_surjective (A'.equivMapOfInjective Φ hΦ).toMonoidHom (MulEquiv.surjective _)
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hΦ]
    exact hA'1
  · change Φ (e' (eK.symm x.1, eA.symm x.2) : c.J.specialSubgroup ⧸ c.C) = _
    rw [he', map_mul, heK, heA]
  · rintro g hg hg2
    rw [← hCmap] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    have hy2 : y ^ 2 = 1 := hΦ (by rw [map_pow, hg2, map_one])
    rw [hKeq]
    exact ⟨y, hinvA' y hy hy2, rfl⟩

end UnitaryHullCoordinates

end CFSG.ShultStronglyClosedTI.UnitaryHulls
