module

public import CFSG.RankThree.PartOne.SEITZ8.D4TwoSeven
public import CFSG.RankThree.PartOne.SEITZ8.D4BigCell

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K] {σ : K →+* K} [CharP K 2]

theorem ordT_split (hσ : ∀ c, σ (σ (σ c)) = c) (c : ℕ → K) :
    ordT σ c = ordT σ (mkT (c 0) 0 (c 4)
      (c 8 + (c 1 * σ (c 4) + σ (c 1) * c 4))
      (c 3 + (c 1 * σ (c 1) * σ (σ (c 4)) + c 1 * σ (σ (c 1)) * σ (c 4) +
        σ (c 1) * σ (σ (c 1)) * c 4) + (c 1 * σ (c 8) + σ (c 1) * σ (σ (c 8)) +
          σ (σ (c 1)) * c 8))
      (c 7 + (c 1 * σ (c 4) * σ (σ (c 4)) + σ (c 1) * c 4 * σ (σ (c 4)) +
        σ (σ (c 1)) * c 4 * σ (c 4)) +
        (c 4 * σ (c 1 * σ (c 4) + σ (c 1) * c 4) +
          σ (c 4) * σ (σ (c 1 * σ (c 4) + σ (c 1) * c 4)) +
          σ (σ (c 4)) * (c 1 * σ (c 4) + σ (c 1) * c 4)))) * xA σ (c 1) := by
  rw [ordT_zero_one]
  unfold ordT xA xAB xAAB xB xN xH
  simp only [map_add, map_mul, hσ]
  d4coll
  d4fin

omit [CharP K 2] in
theorem Tt_conj_Uhat {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) {y : adjointGroup d4 K}
    (hy : y ∈ Uhat σ) : (t : adjointGroup d4 K) * y * (t : adjointGroup d4 K)⁻¹ ∈ Uhat σ := by
  refine CFSG.LieType.Steinberg.conj_mem_of_forall_mem
    (X := fun p => twistedRootSubgroupD4 σ (rt p)) (P := {p | p ∈ posT})
    (fun p hp z hz => ?_) hy
  exact le_iSup₂_of_le (f := fun p (_ : p ∈ posT) => twistedRootSubgroupD4 σ (rt p)) p hp le_rfl
    (Tt_conj_X ht (isRoot_rt (lt_twelve_of_mem_posT hp)) hz)

omit [CharP K 2] in
theorem cartan_theta_check :
    (∑ j, d4.cartan (nd 0) j * (d4Root 22) j = 0) ∧ (∑ j, d4.cartan (nd 1) j * (d4Root 22) j = 0) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 22) j = 1) ∧ (∑ j, d4.cartan (nd 3) j * (d4Root 22) j = 0) ∧
    (∑ j, d4.cartan (nd 0) j * (d4Root 23) j = 0) ∧ (∑ j, d4.cartan (nd 1) j * (d4Root 23) j = 0) ∧
    (∑ j, d4.cartan (nd 2) j * (d4Root 23) j = -1) ∧
    (∑ j, d4.cartan (nd 3) j * (d4Root 23) j = 0) := by
  decide +kernel

theorem conj3 {G : Type*} [Group G] (a b c x : G) :
    a * b * c * x * (a * b * c)⁻¹ = a * (b * (c * x * c⁻¹) * b⁻¹) * a⁻¹ := by
  group

omit [CharP K 2] in
theorem torus_scalar {t : twistedGroup σ} (ht : t ∈ ⨆ i, hHat σ i) :
    ∃ χ : Kˣ, ∀ c : K,
      (t : adjointGroup d4 K) * xd 22 c * (t : adjointGroup d4 K)⁻¹ = xd 22 ((χ : K) * c) ∧
      (t : adjointGroup d4 K) * xd 23 c * (t : adjointGroup d4 K)⁻¹ =
        xd 23 (((χ⁻¹ : Kˣ) : K) * c) := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := cartan_theta_check
  refine Subgroup.iSup_induction (fun i => hHat σ i)
    (C := fun t : twistedGroup σ => ∃ χ : Kˣ, ∀ c : K,
      (t : adjointGroup d4 K) * xd 22 c * (t : adjointGroup d4 K)⁻¹ = xd 22 ((χ : K) * c) ∧
      (t : adjointGroup d4 K) * xd 23 c * (t : adjointGroup d4 K)⁻¹ =
        xd 23 (((χ⁻¹ : Kˣ) : K) * c)) ht ?_ ?_ ?_
  · intro i x hx
    match i with
    | ⟨0, _⟩ =>
      have hx' : (x : adjointGroup d4 K) ∈ (hLongHom σ).range := Subgroup.mem_subgroupOf.1 hx
      obtain ⟨s, hs⟩ := hx'
      have hT : (hLongHom σ s : adjointGroup d4 K) =
          torusElement d4 K (nd 2) ((s : fixedUnits σ) : Kˣ) := rfl
      refine ⟨((s : fixedUnits σ) : Kˣ), fun c => ?_⟩
      rw [← hs, hT, torusElement_conj_xd (nd 2) (by norm_num),
        torusElement_conj_xd (nd 2) (by norm_num), a2, b2]
      simp
    | ⟨1, _⟩ =>
      have hx' : (x : adjointGroup d4 K) ∈ (hShortHom σ).range := Subgroup.mem_subgroupOf.1 hx
      obtain ⟨s, hs⟩ := hx'
      refine ⟨1, fun c => ?_⟩
      rw [← hs, hShortHom_apply, conj3, conj3]
      rw [torusElement_conj_xd (nd 3) (by norm_num), torusElement_conj_xd (nd 1) (by norm_num),
        torusElement_conj_xd (nd 0) (by norm_num), a3, a1, a0,
        torusElement_conj_xd (nd 3) (by norm_num), torusElement_conj_xd (nd 1) (by norm_num),
        torusElement_conj_xd (nd 0) (by norm_num), b3, b1, b0]
      simp
  · exact ⟨1, fun c => by simp⟩
  · rintro x y ⟨χ, hχ⟩ ⟨χ', hχ'⟩
    refine ⟨χ * χ', fun c => ?_⟩
    rw [Subgroup.coe_mul, show ((x : adjointGroup d4 K) * (y : adjointGroup d4 K)) * xd 22 c *
        ((x : adjointGroup d4 K) * (y : adjointGroup d4 K))⁻¹ = (x : adjointGroup d4 K) *
          ((y : adjointGroup d4 K) * xd 22 c * (y : adjointGroup d4 K)⁻¹) *
            (x : adjointGroup d4 K)⁻¹ by group,
      show ((x : adjointGroup d4 K) * (y : adjointGroup d4 K)) * xd 23 c *
        ((x : adjointGroup d4 K) * (y : adjointGroup d4 K))⁻¹ = (x : adjointGroup d4 K) *
          ((y : adjointGroup d4 K) * xd 23 c * (y : adjointGroup d4 K)⁻¹) *
            (x : adjointGroup d4 K)⁻¹ by group, (hχ' c).1, (hχ' c).2, (hχ _).1, (hχ _).2]
    refine ⟨by rw [Units.val_mul, mul_assoc], ?_⟩
    rw [mul_inv_rev, Units.val_mul]
    ring_nf

theorem exists_ordT_noA (hσ : ∀ c, σ (σ (σ c)) = c) {u : adjointGroup d4 K} (hu : u ∈ Uhat σ) :
    ∃ (c : ℕ → K) (a : K), c 1 = 0 ∧ σ (c 0) = c 0 ∧ σ (c 3) = c 3 ∧ σ (c 7) = c 7 ∧
      u = ordT σ c * xA σ a := by
  obtain ⟨c0, h0, h3, h7, rfl⟩ := exists_ordT hσ hu
  refine ⟨mkT (c0 0) 0 (c0 4) (c0 8 + (c0 1 * σ (c0 4) + σ (c0 1) * c0 4))
      (c0 3 + (c0 1 * σ (c0 1) * σ (σ (c0 4)) + c0 1 * σ (σ (c0 1)) * σ (c0 4) +
        σ (c0 1) * σ (σ (c0 1)) * c0 4) + (c0 1 * σ (c0 8) + σ (c0 1) * σ (σ (c0 8)) +
          σ (σ (c0 1)) * c0 8))
      (c0 7 + (c0 1 * σ (c0 4) * σ (σ (c0 4)) + σ (c0 1) * c0 4 * σ (σ (c0 4)) +
        σ (σ (c0 1)) * c0 4 * σ (c0 4)) +
        (c0 4 * σ (c0 1 * σ (c0 4) + σ (c0 1) * c0 4) +
          σ (c0 4) * σ (σ (c0 1 * σ (c0 4) + σ (c0 1) * c0 4)) +
          σ (σ (c0 4)) * (c0 1 * σ (c0 4) + σ (c0 1) * c0 4))), c0 1, by simp [mkT], ?_, ?_, ?_,
    ordT_split hσ c0⟩
  · simpa [mkT] using h0
  · simp only [mkT]
    norm_num
    simp only [hσ, h3]
    ring
  · simp only [mkT]
    norm_num
    simp only [hσ, h7]
    ring

theorem normal_form [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) (g : twistedGroup σ)
    (hne0 : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ≠ 0) :
    ∃ (c : ℕ → K) (μ : K), c 1 = 0 ∧ σ (c 0) = c 0 ∧ σ (c 3) = c 3 ∧ σ (c 7) = c 7 ∧ σ μ = μ ∧
      μ = coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) ∧
      ∀ s : K, (g : adjointGroup d4 K) * xd 22 s * (g : adjointGroup d4 K)⁻¹ =
        ordT σ c * xd 23 (μ * s) * (ordT σ c)⁻¹ := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, hχ₁, a1, bb1, c1⟩ := borel_stab_tw hσ hb₁
  obtain ⟨χ₂, hχ₂, a2, bb2, c2⟩ := borel_stab_tw hσ hb₂
  obtain ⟨t, ht, hv, hc⟩ := nrep_stab_tw hσ w
  have hlam : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * coordAt (d4Root 23) (rv t : RootModule d4 K)) := by
    rw [hg, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, a2, smul_smul_comm', hv, bb1,
      coordAt_smul]
  have ht23 : t = 23 := by
    by_contra hne
    apply hne0
    have h1 : d4Root 23 ≠ d4Root t := fun h => hne (d4Root_inj t (lt_of_mem_longPos ht) 23
      (by norm_num) h.symm)
    rw [hlam, rv, coordAt_rootVec_ne h1]
    simp
  subst ht23
  have hlam' : coordAt (d4Root 23) ((g : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) =
      ((χ₁⁻¹ : Kˣ) : K) * (χ₂ : K) := by
    rw [hlam, rv, coordAt_rootVec_self (isRoot_d4 (by norm_num))]
    simp
  have hy : ∀ s : K, (g : adjointGroup d4 K) * xd 22 s * (g : adjointGroup d4 K)⁻¹ =
      (b₁ : adjointGroup d4 K) * xd 23 ((χ₂ : K) * s) * (b₁ : adjointGroup d4 K)⁻¹ := by
    intro s
    have hgc : (g : adjointGroup d4 K) = (b₁ : adjointGroup d4 K) *
        ((nrep hct w : twistedGroup σ) : adjointGroup d4 K) * (b₂ : adjointGroup d4 K) := by
      rw [hg]
      rfl
    rw [hgc]
    set n : adjointGroup d4 K := ((nrep hct w : twistedGroup σ) : adjointGroup d4 K) with hn
    rw [show (b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K) * xd 22 s *
        ((b₁ : adjointGroup d4 K) * n * (b₂ : adjointGroup d4 K))⁻¹ =
        (b₁ : adjointGroup d4 K) * (n * ((b₂ : adjointGroup d4 K) * xd 22 s *
          (b₂ : adjointGroup d4 K)⁻¹) * n⁻¹) * (b₁ : adjointGroup d4 K)⁻¹ by group]
    rw [c2 s, hc]
  have hb' : b₁ ∈ (borel (twistedDatum σ) (hHat σ) : Set (twistedGroup σ)) := hb₁
  rw [coe_borel hct, Set.mem_mul] at hb'
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
  have hu0U : ((u0 : twistedGroup σ) : adjointGroup d4 K) ∈ Uhat σ := by
    rw [posUnipotent_twisted] at hu0
    exact Subgroup.mem_subgroupOf.1 hu0
  obtain ⟨χ, hχ⟩ := torus_scalar ht0
  have hχχ : χ₁ = χ := by
    have h1 := c1 1
    have hcu : (u0 : adjointGroup d4 K) * xe 22 1 = xe 22 1 * (u0 : adjointGroup d4 K) :=
      commute_Uhat_xH hσ hu0U 1
    rw [Subgroup.coe_mul,
      show ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K)) * xe 22 1 *
        ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K))⁻¹ =
        (t0 : adjointGroup d4 K) * ((u0 : adjointGroup d4 K) * xe 22 1 *
          (u0 : adjointGroup d4 K)⁻¹) * (t0 : adjointGroup d4 K)⁻¹ by group,
      hcu, mul_inv_cancel_right, (hχ 1).1] at h1
    exact Units.ext (by simpa using (xH_inj h1).symm)
  rw [← hχχ] at hχ
  have hu0' : (t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K) * (t0 : adjointGroup d4 K)⁻¹ ∈
      Uhat σ := Tt_conj_Uhat ht0 hu0U
  obtain ⟨c, a, hc1, hc0, hc3, hc7, hca⟩ := exists_ordT_noA hσ hu0'
  refine ⟨c, ((χ₁⁻¹ : Kˣ) : K) * (χ₂ : K), hc1, hc0, hc3, hc7, ?_, hlam'.symm, fun s => ?_⟩
  · rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hχ₁, hχ₂]
  · rw [hy s, Subgroup.coe_mul,
      show ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K)) * xd 23 ((χ₂ : K) * s) *
        ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K))⁻¹ =
        ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K) * (t0 : adjointGroup d4 K)⁻¹) *
          ((t0 : adjointGroup d4 K) * xd 23 ((χ₂ : K) * s) * (t0 : adjointGroup d4 K)⁻¹) *
            ((t0 : adjointGroup d4 K) * (u0 : adjointGroup d4 K) *
              (t0 : adjointGroup d4 K)⁻¹)⁻¹ by group,
      (hχ _).2, hca,
      show (ordT σ c * xA σ a) * xd 23 (((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * s)) *
        (ordT σ c * xA σ a)⁻¹ = ordT σ c * (xA σ a * xd 23 (((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * s)) *
          (xA σ a)⁻¹) * (ordT σ c)⁻¹ by group,
      commute_xA_x23 σ a, mul_inv_cancel_right, ← mul_assoc]

end CFSG.RankThree.PartOne.SEITZ8
