module

public import CFSG.LieType.Chevalley.GraphFixedData
import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusIntersection

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2 TrialitySplitInner TrialityFold
  SteinbergBT.TrialityPlane

private def transvD4 (L : Type*) [Field L] : Matrix.SpecialLinearGroup (Fin 2) L :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem transvD4_sq (L : Type*) [Field L] [CharP L 2] : transvD4 L ^ 2 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, sq]
  fin_cases i <;> fin_cases j <;>
    simp [transvD4, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

private theorem exists_involution_of_comap_eq {L : Type*} [Field L] [CharP L 2]
    {L₀ : Subfield L} {G : Type*} [Group G] {Φ : SL2 L →* G} (hΦ : Function.Injective Φ)
    {R : Subgroup G} {P : GL (Fin 2) L}
    (hR : R.comap Φ = (Matrix.SpecialLinearGroup.map (algebraMap L₀ L)).range.map (conjSL P)) :
    ∃ r ∈ R, r ≠ 1 ∧ r ^ 2 = 1 := by
  have : CharP L₀ 2 := RingHom.charP L₀.subtype Subtype.val_injective 2
  set M : SL2 L := conjSL P (Matrix.SpecialLinearGroup.map (algebraMap L₀ L) (transvD4 L₀))
    with hM
  have hMR : M ∈ R.comap Φ := by
    rw [hR]
    exact ⟨_, ⟨transvD4 L₀, rfl⟩, rfl⟩
  refine ⟨Φ M, hMR, fun h1 => ?_, ?_⟩
  · have h2 : M = 1 := hΦ (h1.trans (map_one _).symm)
    set X : Matrix (Fin 2) (Fin 2) L :=
      ((Matrix.SpecialLinearGroup.map (algebraMap L₀ L) (transvD4 L₀) :
        Matrix.SpecialLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hX
    have h3 : (P : Matrix (Fin 2) (Fin 2) L) * X * (↑P⁻¹ : Matrix (Fin 2) (Fin 2) L) = 1 :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) L => (A : Matrix (Fin 2) (Fin 2) L)) h2
    have key : (↑P⁻¹ : Matrix (Fin 2) (Fin 2) L) *
        ((P : Matrix (Fin 2) (Fin 2) L) * X * (↑P⁻¹ : Matrix (Fin 2) (Fin 2) L)) *
          (P : Matrix (Fin 2) (Fin 2) L) = X := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, P.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        P.inv_mul, Matrix.one_mul]
    rw [h3, Matrix.mul_one, P.inv_mul] at key
    have h5 := congrFun (congrFun key 0) 1
    rw [hX] at h5
    change (0 : L) = algebraMap L₀ L 1 at h5
    rw [map_one] at h5
    exact zero_ne_one h5
  · rw [← map_pow, hM, ← map_pow, ← map_pow, transvD4_sq, map_one, map_one, map_one]

private theorem exists_singular_D4_qplus_aux
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ 2 ^ f + 1) {Pl : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hPp : IsPGroup p Pl) (hPpow : ∀ c ∈ Pl, c ^ p = 1) (hPcard : Nat.card Pl = p ^ 2) :
    ∃ b ∈ Pl, b ≠ 1 ∧ ∃ w, w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b := by
  classical
  have hℓ : (2 : ℕ).Prime := Nat.prime_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₂, _, _, σ₂, τ, g, hK₂, hσ₂, hτ, hg, hzg⟩ := exists_qplus_setting hℓ hf hK σ hσ
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact (2 : ℕ).Prime := ⟨hℓ⟩
  have : CharP K₂ 2 := finite_field_prime_power_characteristic hℓ (k := f * 6) (by omega)
    (by rw [hK₂, pow_mul])
  obtain ⟨u, -, hrange, hPT⟩ := exists_realization_le_torus hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg hp hp3
    hpq hPp
  obtain ⟨F, hFdef⟩ : ∃ F, F = trialityRealization (σ := σ) (u * g) := ⟨_, rfl⟩
  rw [← hFdef] at hrange hPT
  have hF : Function.Injective F := by
    rw [hFdef]
    exact trialityRealization_injective _
  have hσ₂3 := sigma₂_pow_three hℓ hK₂ hσ₂
  obtain ⟨-, -, -, hL1, -⟩ := triality_all_characteristic_faithful_torus_coordinates K₂ σ₂ hσ₂3
  obtain ⟨V, hV⟩ : ∃ V : Subgroup (ModGL TwistTag.D4.tag K₂), ∀ x, x ∈ V ↔
      x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ x ^ p = 1 :=
    ⟨{ carrier := {x | x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ x ^ p = 1}
       mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
         rw [Commute.mul_pow (commute_of_mem_torusGroup
           (graphFixedRootTorus_le_torusGroup _ hx.1) (graphFixedRootTorus_le_torusGroup _ hy.1)),
           hx.2, hy.2, one_mul]⟩
       one_mem' := ⟨one_mem _, one_pow _⟩
       inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ },
      fun x => Iff.rfl⟩
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2f : 2 ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have hpq2 : p ∣ 2 ^ (2 * f) - 1 := hpq.trans ⟨2 ^ f - 1, by
    rw [h2f]
    zify [Nat.one_le_pow 2 (2 ^ f) (by omega), hq1]
    ring⟩
  obtain ⟨hVcard, -, -, -, -, -, -, -, -, -, -, hζV⟩ :=
    triality_both_orientations_split_prime_plane_normalizers hℓ (f := 2 * f) (by omega) K₂
      (by rw [hK₂, h2f]; ring) (r := 2) (Or.inr rfl) σ₂ (fun c => by rw [hσ₂, h2f]; ring_nf)
      hp hp3 hpq2 V hV
  have hPV : Pl.map F = V := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨c, hc, rfl⟩
      exact (hV _).2 ⟨(Subgroup.mem_inf.1 (hPT c hc)).1, by rw [← map_pow, hPpow c hc, map_one]⟩
    · rw [hVcard, ← Nat.card_congr (Subgroup.equivMapOfInjective Pl F hF).toEquiv, hPcard]
  have hk₂ : Nat.card (trialityFixedField K₂ σ₂.toRingHom) = (2 ^ f) ^ 2 := by
    rw [← hL1, natCard_orbitField_K₂ hℓ hf hK₂ hσ₂,
      show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (trialityFixedField K₂ σ₂.toRingHom)ˣ) p
    (by rw [Nat.card_units, hk₂, ← h2f]; exact hpq2)
  have hζ' : orderOf (trialityFixedUnit K₂ σ₂ ζ) = p := by
    rw [orderOf_injective _ (fun a b h => Units.ext (Subtype.ext (congrArg Units.val h))) ζ, hζ]
  have hz1 : trialityFixedUnit K₂ σ₂ ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ'
    exact hp.one_lt.ne hζ'
  obtain ⟨hVζ, -⟩ := hζV ζ hζ
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = trialityOuterTorus K₂ σ₂ (trialityFixedUnit K₂ σ₂ ζ ^ 1) *
      trialityMiddleTorus K₂ σ₂ (ζ ^ 2) := ⟨_, rfl⟩
  have hx₁V : x₁ ∈ V := (hVζ _).2 ⟨1, 2, by rw [hx₁]; norm_num⟩
  have hx₁1 : x₁ ≠ 1 := by
    rw [hx₁, trialityOuter_mul_middle_pow_eq, ← rootDiagUnit_one]
    intro h
    have h2 : (trialityFixedUnit K₂ σ₂ ζ ^ 1 * trialityFixedUnit K₂ σ₂ ζ ^ 1 *
        trialityFixedUnit K₂ σ₂ ζ ^ 1)⁻¹ * (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 = 1 :=
      congrFun (rootDiagUnit_injective h) i2
    exact hz1 (calc trialityFixedUnit K₂ σ₂ ζ = (trialityFixedUnit K₂ σ₂ ζ ^ 1 *
        trialityFixedUnit K₂ σ₂ ζ ^ 1 * trialityFixedUnit K₂ σ₂ ζ ^ 1)⁻¹ *
          (trialityFixedUnit K₂ σ₂ ζ ^ 2) ^ 2 := by group
      _ = 1 := h2)
  have hai₁ : ∀ a : Fin TwistTag.D4.tag.rank → K₂ˣ, x₁ = rootDiagUnit TwistTag.D4.tag a →
      a i0 = 1 := fun a ha => by
    rw [hx₁, trialityOuter_mul_middle_pow_eq] at ha
    rw [← rootDiagUnit_injective ha]
    change (trialityFixedUnit K₂ σ₂ ζ ^ 1) ^ 2 * (trialityFixedUnit K₂ σ₂ ζ ^ 2)⁻¹ = 1
    group
  have hx₁p : orderOf x₁ = p := orderOf_eq_prime ((hV _).1 hx₁V).2 hx₁1
  obtain ⟨c₁, hc₁, rfl⟩ : ∃ c ∈ Pl, F c = x₁ := by
    rw [← hPV] at hx₁V
    obtain ⟨c, hc, hcx⟩ := hx₁V
    exact ⟨c, hc, hcx⟩
  obtain ⟨-, hinj, -, P, hP, -, -⟩ := qplus_simple_orbit_derived hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg
    hp hp3 hpq (hPT c₁ hc₁) hx₁p (b := ⟨0, by decide⟩) (by decide) hai₁
  have : CharP (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩) 2 :=
    RingHom.charP (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩).subtype
      Subtype.val_injective 2
  obtain ⟨r, hrR, hr1, hr2⟩ := exists_involution_of_comap_eq hinj hP
  have hrC : r ∈ trialityConjImage K σ.toRingHom g ⊓ Subgroup.centralizer {F c₁} :=
    Subgroup.commutator_le.mpr (fun y hy z hz =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hz) (Subgroup.inv_mem _ hy))
        (Subgroup.inv_mem _ hz)) hrR
  obtain ⟨w, hw⟩ : ∃ w, F w = r := by
    have : r ∈ F.range := hrange ▸ hrC.1
    exact this
  refine ⟨c₁, hc₁, fun h1 => hx₁1 (by rw [h1, map_one]), w, fun h1 => hr1 (by
    rw [← hw, h1, map_one]), hF (by rw [map_pow, hw, hr2, map_one]), hF ?_⟩
  rw [map_mul, map_mul, hw]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hrC.2).symm

end CFSG.RankThree.Chevalley

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc


theorem exists_singular_D4_qplus {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f)
    (hk : Nat.card k = (2 ^ f) ^ 3) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ 2 ^ f + 1)
    {A : Subgroup ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 k σ.toRingHom)}
    (hA : CFSG.Open.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ b ∈ A, b ≠ 1 ∧ ∃ w, w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b :=
  have : Fact p.Prime := ⟨hp⟩
  CFSG.RankThree.Chevalley.exists_singular_D4_qplus_aux hf hk σ hσ hp hp3 hpq
    (IsPGroup.of_card hAc) hA.2 hAc

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
