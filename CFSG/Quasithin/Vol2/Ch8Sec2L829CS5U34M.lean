module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5U3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5Rk1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

abbrev PsuKCS5 (n : ℕ) : Type := FiniteField.Extension (GaloisField 2 n) 2 2

theorem psuK_charP_cs5 (n : ℕ) : CharP (PsuKCS5 n) 2 :=
  CharP.of_ringHom_of_ne_zero (algebraMap (GaloisField 2 n) (PsuKCS5 n)) 2 (by norm_num)

theorem psuK_card_cs5 (n : ℕ) (hn : 0 < n) : Nat.card (PsuKCS5 n) = (2 ^ n) ^ 2 := by
  rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]

theorem psuK_conj_apply_cs5 (n : ℕ) (hn : 0 < n) (x : PsuKCS5 n) :
    (binaryQuadraticHermitian n hn).conj x = x ^ 2 ^ n := by
  show FiniteField.Extension.frob (GaloisField 2 n) 2 2 x = _
  rw [FiniteField.Extension.frob_apply, GaloisField.card 2 n (by omega)]

theorem exists_unit_orderOf_five_cs5 :
    ∃ k : (PsuKCS5 2)ˣ, orderOf k = 5 ∧ (k : PsuKCS5 2) ^ 4 = (k : PsuKCS5 2)⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (PsuKCS5 2)ˣ = 15 := by
    rw [Nat.card_units, psuK_card_cs5 2 (by norm_num)]
    norm_num
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := (PsuKCS5 2)ˣ) 5 (by rw [hcard]; norm_num)
  refine ⟨k, hk, ?_⟩
  have h5 : k ^ 5 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
  have h5K : (k : PsuKCS5 2) ^ 5 = 1 := by
    have := congrArg Units.val h5
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have h5' : (k : PsuKCS5 2) ^ 4 * (k : PsuKCS5 2) = 1 := by
    rw [← pow_succ]
    exact h5K
  exact eq_inv_of_mul_eq_one_left h5'

section FiveTorus

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut

noncomputable abbrev psuJ4CS5 : HermitianForm 3 (PsuKCS5 2) :=
  binaryQuadraticHermitian 2 (by norm_num)

theorem psuJ4CS5_form : psuJ4CS5.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl

theorem psuJ4CS5_fixed : Nat.card {x : PsuKCS5 2 // psuJ4CS5.conj x = x} = 2 ^ 2 :=
  quadraticBinaryFrobenius_fixed_card 2 (by norm_num)

theorem exists_order_five_torus_cs5 :
    ∃ c : ProjectiveSpecialUnitaryMatrixGroup psuJ4CS5, orderOf c = 5 ∧
      (∀ z ∈ sylowCenter (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form), c * z = z * c) ∧
      c * hermitianWeylPSU psuJ4CS5 psuJ4CS5_form = hermitianWeylPSU psuJ4CS5 psuJ4CS5_form * c := by
  haveI := psuK_charP_cs5 2
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk5, hk4⟩ := exists_unit_orderOf_five_cs5
  have hconj : psuJ4CS5.conj (k : PsuKCS5 2) = (k : PsuKCS5 2)⁻¹ := by
    rw [psuK_conj_apply_cs5 2 (by norm_num)]
    simpa using hk4
  have hkne : (k : PsuKCS5 2) ≠ 0 := Units.ne_zero k
  have hconjU : Units.map psuJ4CS5.conj.toMonoidHom k = k⁻¹ := Units.ext (by simpa using hconj)
  have hKcard := psuK_card_cs5 2 (by norm_num)
  have hfixed := psuJ4CS5_fixed
  refine ⟨hermitianTorusPSU psuJ4CS5 psuJ4CS5_form k, ?_, ?_, ?_⟩
  · have hpow : (hermitianTorusPSU psuJ4CS5 psuJ4CS5_form k) ^ 5 = 1 := by
      rw [← map_pow]
      have : k ^ 5 = 1 := by rw [← hk5]; exact pow_orderOf_eq_one k
      rw [this, map_one]
    refine orderOf_eq_prime hpow ?_
    intro h1
    obtain ⟨z, hz⟩ := unitaryCoverFirstCoord_surjective psuJ4CS5 (2 ^ 2) hKcard hfixed psuJ4CS5_form
      (Multiplicative.ofAdd 1)
    have hz1 : z.1.1 = 1 := congrArg Multiplicative.toAdd hz
    have h2 := unitaryCoverTorus_conj_root psuJ4CS5 psuJ4CS5_form k z
    rw [h1, one_mul, inv_one, mul_one] at h2
    have h3 : z = hermitianTorusAction psuJ4CS5 k z :=
      CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective psuJ4CS5 psuJ4CS5_form h2
    have h4 := congrArg (fun w : hermitianUnipotentCoord psuJ4CS5 => w.1.1) h3
    simp only [hermitianTorusAction_fst, hconj, hz1, inv_inv] at h4
    have h5 : (k : PsuKCS5 2) ^ 3 = 1 := by
      have : (k : PsuKCS5 2) ^ 3 = (k : PsuKCS5 2) * (k : PsuKCS5 2) ^ 2 := by ring
      rw [this]
      simpa using h4.symm
    have h6 : k ^ 3 = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h5)
    have h7 := orderOf_dvd_of_pow_eq_one h6
    rw [hk5] at h7
    omega
  · intro z hz
    obtain ⟨hzR, -⟩ := mem_sylowCenter.mp hz
    obtain ⟨z₀, rfl⟩ := hzR
    have hz0 : z₀.1.1 = 0 :=
      (mem_sylowCenter_root psuJ4CS5 (2 ^ 2) hKcard hfixed (by norm_num) psuJ4CS5_form z₀).mp hz
    have hact : hermitianTorusAction psuJ4CS5 k z₀ = z₀ := by
      apply Subtype.ext
      apply Prod.ext
      · show z₀.1.1 * (k : PsuKCS5 2) * (psuJ4CS5.conj (k : PsuKCS5 2))⁻¹ ^ 2 = z₀.1.1
        rw [hz0]
        simp
      · show z₀.1.2 * (psuJ4CS5.conj (k : PsuKCS5 2))⁻¹ * (k : PsuKCS5 2)⁻¹ = z₀.1.2
        rw [hconj, inv_inv, mul_assoc, mul_inv_cancel₀ hkne, mul_one]
    rw [hermitianTorusPSU_mul_unipotent, hact]
  · have h := weyl_conj_torus psuJ4CS5 psuJ4CS5_form k
    rw [hconjU, inv_inv] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem finite_psu_cs5 {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Finite.of_injective Subtype.val Subtype.coe_injective

theorem commute_conj_cs5 {G : Type} [Group G] (s : G) {a b : G} (h : Commute a b) :
    Commute (s * a * s⁻¹) (s * b * s⁻¹) := by
  have := h.map (MulAut.conj s)
  simpa [MulAut.conj_apply] using this

end FiveTorus

section FiveCentCS5

@[expose] def FiveCentCS5 {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (S : Set G) → ∃ c : G, orderOf c = 5 ∧
    (∀ z ∈ centerSub S, c * z = z * c) ∧
    ∀ z ∈ centerSub S, c * (g * z * g⁻¹) = g * z * g⁻¹ * c

theorem FiveCentCS5.map_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {S : Subgroup G}
    (h : FiveCentCS5 S) : FiveCentCS5 (S.map e.toMonoidHom) := by
  intro g' hg'
  obtain ⟨g, rfl⟩ := e.surjective g'
  have hg : g ∉ Subgroup.normalizer (S : Set G) := fun hc =>
    hg' ((mem_normalizer_map_mulEquiv_cs5 e S (e g)).mpr (by
      rw [MulEquiv.symm_apply_apply]
      exact hc))
  obtain ⟨c, hc5, hcz, hcg⟩ := h g hg
  refine ⟨e c, ?_, ?_, ?_⟩
  · have := orderOf_injective e.toMonoidHom e.injective c
    exact this.trans hc5
  · intro z' hz'
    rw [centerSub_map_mulEquiv_cs5 e S] at hz'
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
    have := congrArg e (hcz z hz)
    simpa [map_mul] using this
  · intro z' hz'
    rw [centerSub_map_mulEquiv_cs5 e S] at hz'
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
    have := congrArg e (hcg z hz)
    simpa [map_mul, map_inv] using this

theorem FiveCentCS5.of_one_sylow {G : Type} [Group G] [Finite G] {S₀ : Subgroup G}
    (h₀ : IsSylowTwoOf S₀ ⊤) (h : FiveCentCS5 S₀) :
    ∀ S : Subgroup G, IsSylowTwoOf S ⊤ → FiveCentCS5 S := by
  intro S hS
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top_cs5 h₀ hS
  rw [hg]
  exact h.map_mulEquiv (MulAut.conj g)

theorem FiveCentCS5.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : ∀ S : Subgroup G, IsSylowTwoOf S ⊤ → FiveCentCS5 S) :
    ∀ S' : Subgroup G', IsSylowTwoOf S' ⊤ → FiveCentCS5 S' := by
  intro S' hS'
  have hS : IsSylowTwoOf (S'.map e.symm.toMonoidHom) ⊤ :=
    (isSylowTwoOf_top_map_mulEquiv_cs5 e.symm S').mpr hS'
  have hT := (h _ hS).map_mulEquiv e
  rwa [map_map_symm_cs5 e S'] at hT

end FiveCentCS5

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut in
theorem fiveCent_root_cs5 : FiveCentCS5 (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) := by
  haveI := psuK_charP_cs5 2
  haveI := finite_psu_cs5 psuJ4CS5
  obtain ⟨c, hc5, hcZ, hcw⟩ := exists_order_five_torus_cs5
  have hKcard := psuK_card_cs5 2 (by norm_num)
  have hfixed := psuJ4CS5_fixed
  have hR : RankOneSyl (⊤ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup psuJ4CS5))
      (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) (2 ^ 2) :=
    rankOneSyl_root_psu3_cs5 psuJ4CS5 2 le_rfl hKcard hfixed psuJ4CS5_form
  have hw := weyl_not_mem_normalizer psuJ4CS5 (2 ^ 2) hKcard hfixed psuJ4CS5_form
  have hcen : centerSub (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) =
      sylowCenter (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) := map_center_eq_sylowCenter _
  intro g hg
  obtain ⟨s, hs, hsn⟩ := hR.trans (g₁ := hermitianWeylPSU psuJ4CS5 psuJ4CS5_form) (Subgroup.mem_top _) hw
    (Subgroup.mem_top _) hg
  obtain ⟨n, hn, rfl⟩ : ∃ n ∈ Subgroup.normalizer
      ((unitaryCoverRoot psuJ4CS5 psuJ4CS5_form : Subgroup _) :
        Set (ProjectiveSpecialUnitaryMatrixGroup psuJ4CS5)),
      g = s * hermitianWeylPSU psuJ4CS5 psuJ4CS5_form * n :=
    ⟨(s * hermitianWeylPSU psuJ4CS5 psuJ4CS5_form)⁻¹ * g, hsn,
      (mul_inv_cancel_left (s * hermitianWeylPSU psuJ4CS5 psuJ4CS5_form) g).symm⟩
  set w := hermitianWeylPSU psuJ4CS5 psuJ4CS5_form with hwdef
  have hZR : ∀ z ∈ centerSub (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form), Commute c z := fun z hz =>
    hcZ z (hcen ▸ hz)
  refine ⟨s * c * s⁻¹, ?_, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective c
    rw [hc5] at this
    exact this
  · intro z hz
    have hsz : s * z = z * s := (mem_centerSub_cs5.mp hz).2 s hs
    have hz' : s * z * s⁻¹ = z := by rw [hsz, mul_inv_cancel_right]
    have := commute_conj_cs5 s (hZR z hz)
    rw [hz'] at this
    exact this.eq
  · intro z hz
    have hz' : n * z * n⁻¹ ∈ centerSub (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) :=
      conj_mem_centerSub_cs5 hn hz
    have hcw' : Commute c w := hcw
    have h1 : Commute c (w * (n * z * n⁻¹) * w⁻¹) :=
      (hcw'.mul_right (hZR _ hz')).mul_right hcw'.inv_right
    have h2 := commute_conj_cs5 s h1
    have h3 : s * w * n * z * (s * w * n)⁻¹ = s * (w * (n * z * n⁻¹) * w⁻¹) * s⁻¹ := by group
    rw [h3]
    exact h2.eq

theorem fiveCent_top_of_isPSU_cs5 {G : Type} [Group G] [Finite G] (hG : IsPSU 3 2 2 G) :
    ∀ S : Subgroup G, IsSylowTwoOf S ⊤ → FiveCentCS5 S := by
  haveI := psuK_charP_cs5 2
  obtain ⟨e⟩ := exists_mulEquiv_psu3_proj_cs5 (n := 2) le_rfl hG
  haveI : Finite (ProjectiveSpecialUnitaryMatrixGroup psuJ4CS5) := Finite.of_equiv G e.toEquiv
  have hR : IsSylowTwoOf (unitaryCoverRoot psuJ4CS5 psuJ4CS5_form) ⊤ :=
    (rankOneSyl_root_psu3_cs5 psuJ4CS5 2 le_rfl (psuK_card_cs5 2 (by norm_num)) psuJ4CS5_fixed
      psuJ4CS5_form).sylow
  exact FiveCentCS5.of_mulEquiv e.symm (FiveCentCS5.of_one_sylow hR fiveCent_root_cs5)

end CFSG.Quasithin.H13
