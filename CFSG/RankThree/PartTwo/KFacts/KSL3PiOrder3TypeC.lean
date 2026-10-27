module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

@[expose] def KSL3PiOrder3TypeC : Prop :=
  ∀ (π : Bool) (p f : ℕ) (K : Type) [Field K], PiField π p f K → ModThree π (p ^ f) →
    (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) →
    ∀ x ∈ projImage (slPi π 3 (p ^ f) K), x ^ 3 = 1 → x ≠ 1 →
      ∃ D : Subgroup (GL (Fin 3) K), IsTypeC π (p ^ f) K D ∧ D ≤ slPi π 3 (p ^ f) K ∧
        ∃ y ∈ D, ProjGenLinGroup.mk y = x

section T27

variable {K : Type} [Field K]

@[expose] def t27Units (K : Type) [Field K] : Subgroup (Kˣ × Kˣ × Kˣ) where
  carrier := {t | t.1 ^ 3 = t.2.1 ^ 3 ∧ t.1 ^ 3 = t.2.2 ^ 3 ∧ t.1 * t.2.1 * t.2.2 = 1}
  mul_mem' := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, ?_, ?_⟩
    · change (a * a') ^ 3 = (b * b') ^ 3
      rw [mul_pow, mul_pow, h1, h1']
    · change (a * a') ^ 3 = (c * c') ^ 3
      rw [mul_pow, mul_pow, h2, h2']
    · change a * a' * (b * b') * (c * c') = 1
      calc a * a' * (b * b') * (c * c') = a * b * c * (a' * b' * c') := by
            rw [mul_mul_mul_comm a a' b b', mul_mul_mul_comm (a * b) (a' * b') c c']
        _ = 1 := by rw [h3, h3', one_mul]
  one_mem' := ⟨rfl, rfl, by simp⟩
  inv_mem' := by
    rintro ⟨a, b, c⟩ ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · change a⁻¹ ^ 3 = b⁻¹ ^ 3
      rw [inv_pow, inv_pow, h1]
    · change a⁻¹ ^ 3 = c⁻¹ ^ 3
      rw [inv_pow, inv_pow, h2]
    · change a⁻¹ * b⁻¹ * c⁻¹ = 1
      rw [← mul_inv, ← mul_inv, h3, inv_one]

theorem pow_nine_eq_one_of_mem_t27Units {t : Kˣ × Kˣ × Kˣ} (ht : t ∈ t27Units K) :
    t.1 ^ 9 = 1 ∧ t.2.1 ^ 9 = 1 ∧ t.2.2 ^ 9 = 1 := by
  obtain ⟨h1, h2, h3⟩ := ht
  have hc : (t.1 * t.2.1 * t.2.2) ^ 3 = 1 := by rw [h3, one_pow]
  rw [mul_pow, mul_pow, ← h1, ← h2] at hc
  have h9 : t.1 ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 + 3 + 3 from rfl, pow_add, pow_add]
    exact hc
  refine ⟨h9, ?_, ?_⟩
  · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, ← h1, ← pow_mul]
    exact h9
  · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, ← h2, ← pow_mul]
    exact h9

@[expose] noncomputable def t27Conj (h : GL (Fin 3) K) : Subgroup (GL (Fin 3) K) :=
  (t27Units K).map ((MulAut.conj h).toMonoidHom.comp diagHom)

theorem det_conj_eq (h y : GL (Fin 3) K) :
    ((h * y * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (y : Matrix (Fin 3) (Fin 3) K).det := by
  have h1 := congrArg Units.val (det_inv_conj h⁻¹ y)
  rwa [inv_inv, GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply] at h1

theorem det_diagHom (t : Kˣ × Kˣ × Kˣ) :
    ((diagHom t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((t.1 * t.2.1 * t.2.2 : Kˣ) : K) := by
  rw [coe_diagHom, det_diagonal, Fin.prod_univ_three]
  simp

theorem scalar_eq_diagHom (ζ : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) ζ = diagHom (ζ, ζ, ζ) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem det_scalar_eq (ζ : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) ζ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (ζ : K) ^ 3 := by
  rw [scalar_eq_diagHom, det_diagHom]
  simp [pow_three, mul_assoc]

theorem t27Conj_le_slPi {π : Bool} {p f : ℕ} (hK : PiField π p f K)
    (h9 : 9 ∣ qSubPi π (p ^ f)) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    t27Conj h ≤ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨h1, h2, h3⟩ := pow_nine_eq_one_of_mem_t27Units ht
  have hr : ∀ u : Kˣ, u ^ 9 = 1 → u ∈ rootsOfUnity (qSubPi π (p ^ f)) K := fun u hu => by
    obtain ⟨k, hk⟩ := h9
    rw [mem_rootsOfUnity, hk, pow_mul, hu, one_pow]
  have hdH : diagHom t ∈ glPi π 3 (p ^ f) K :=
    diagUnits_mem_glPi hK (hr _ h1) (hr _ h2) (hr _ h3)
  rw [mem_slPi_iff hπ]
  refine ⟨mul_mem (mul_mem hh hdH) (inv_mem hh), ?_⟩
  change ((h * diagHom t * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
  rw [det_conj_eq, det_diagHom, ht.2.2, Units.val_one]

theorem exists_pow_three_eq [Finite K] (h9 : 9 ∣ Nat.card K - 1) {ε : Kˣ} (hε : ε ^ 3 = 1) :
    ∃ μ : Kˣ, μ ^ 3 = ε := by
  have hcard : Nat.card (rootsOfUnity 9 K) = 9 := CFSG.LinearGroups.card_rootsOfUnity_of_dvd h9
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity 9 K)
  have hog : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hε9 : ε ∈ rootsOfUnity 9 K := by
    rw [mem_rootsOfUnity, show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hε, one_pow]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨ε, hε9⟩)
  have h3k : g ^ (k * 3) = 1 := by
    rw [_root_.zpow_mul, hk]
    apply Subtype.ext
    change ε ^ 3 = 1
    exact hε
  rw [← orderOf_dvd_iff_zpow_eq_one, hog] at h3k
  obtain ⟨m, hm⟩ : (3 : ℤ) ∣ k := by omega
  refine ⟨((g ^ m : rootsOfUnity 9 K) : Kˣ), ?_⟩
  have h1 : (g ^ m) ^ 3 = (⟨ε, hε9⟩ : rootsOfUnity 9 K) := by
    rw [← hk, hm, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]
    rfl
  exact congrArg Subtype.val h1

theorem isTypeC_t27Conj {π : Bool} {p f : ℕ} (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : 9 ∣ qSubPi π (p ^ f)) {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    IsTypeC π (p ^ f) K (t27Conj h) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have := hK.finite
  have h9K : 9 ∣ Nat.card K - 1 := dvd_trans h9 (qSubPi_dvd hK)
  refine ⟨(t27Conj_le_slPi hK h9 hh).trans (slPi_le_glPi hπ), ?_, ?_, ?_⟩
  ·
    rintro _ ⟨t, ht, rfl⟩
    change (h * diagHom t * h⁻¹) ^ 3 ∈ StatedScalars (Fin 3) K
    rw [conj_pow, ← map_pow]
    have hs : diagHom (t ^ 3) ∈ StatedScalars (Fin 3) K := by
      rw [diagHom_mem_statedScalars_iff]
      obtain ⟨h1, h2, -⟩ := ht
      simp only [ratioHom, MonoidHom.coe_mk, OneHom.coe_mk, Prod.pow_fst, Prod.pow_snd,
        Prod.mk_eq_one, mul_inv_eq_one]
      exact ⟨h1.symm, h2.symm⟩
    exact (StatedScalars.normal (Fin 3) K).conj_mem _ hs h
  ·
    set E := t27Units K with hE
    set ψ : E →* GL (Fin 3) K ⧸ StatedScalars (Fin 3) K :=
      (QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp
        (((MulAut.conj h).toMonoidHom.comp diagHom).comp E.subtype) with hψ
    have hker : ψ.ker = (ratioHom.comp E.subtype).ker := by
      ext t
      simp only [MonoidHom.mem_ker, hψ, MonoidHom.coe_comp, Function.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype]
      rw [← diagHom_mem_statedScalars_iff]
      change h * diagHom (t : Kˣ × Kˣ × Kˣ) * h⁻¹ ∈ StatedScalars (Fin 3) K ↔ _
      have h1 := inv_conj_mem_statedScalars_iff h⁻¹ (diagHom (t : Kˣ × Kˣ × Kˣ))
      rwa [inv_inv] at h1
    have hrange : ψ.range = (t27Conj h).map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) := by
      rw [hψ, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have hχ : (ratioHom.comp E.subtype).range =
        (rootsOfUnity 3 K).prod (rootsOfUnity 3 K) := by
      apply le_antisymm
      · rintro _ ⟨⟨t, h1, h2, -⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · change (t.2.1 * t.1⁻¹) ∈ rootsOfUnity 3 K
          rw [mem_rootsOfUnity, mul_pow, inv_pow, ← h1, mul_inv_cancel]
        · change (t.2.2 * t.1⁻¹) ∈ rootsOfUnity 3 K
          rw [mem_rootsOfUnity, mul_pow, inv_pow, ← h2, mul_inv_cancel]
      · rintro ⟨s, u⟩ ⟨hs, hu⟩
        change s ∈ rootsOfUnity 3 K at hs
        change u ∈ rootsOfUnity 3 K at hu
        rw [mem_rootsOfUnity] at hs hu
        obtain ⟨a, ha⟩ := exists_pow_three_eq h9K (ε := (s * u)⁻¹)
          (by rw [inv_pow, mul_pow, hs, hu, mul_one, inv_one])
        have htE : (a, a * s, a * u) ∈ E := by
          refine ⟨?_, ?_, ?_⟩
          · change a ^ 3 = (a * s) ^ 3
            rw [mul_pow, hs, mul_one]
          · change a ^ 3 = (a * u) ^ 3
            rw [mul_pow, hu, mul_one]
          · change a * (a * s) * (a * u) = 1
            calc a * (a * s) * (a * u) = a ^ 3 * (s * u) := by
                  apply Units.ext
                  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
                  ring
              _ = 1 := by rw [ha, inv_mul_cancel]
        refine ⟨⟨_, htE⟩, ?_⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, ratioHom,
          MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk.injEq]
        exact ⟨by rw [mul_comm a s, mul_inv_cancel_right],
          by rw [mul_comm a u, mul_inv_cancel_right]⟩
    rw [← hrange, card_range_eq_of_ker_eq _ _ hker, hχ, card_mu3_prod hK hq]
  ·
    have hhu : IsUnit (h : Matrix (Fin 3) (Fin 3) K) := h.isUnit
    refine ⟨fun i => (h : Matrix (Fin 3) (Fin 3) K).col i, linearIndependent_cols_of_isUnit hhu,
      ?_⟩
    rintro _ ⟨t, -, rfl⟩ i
    refine ⟨![(t.1 : K), t.2.1, t.2.2] i, ?_⟩
    have hcol : (h : Matrix (Fin 3) (Fin 3) K).col i =
        (h : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 := by
      ext j
      simp
    change ((h * diagHom t * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (h : Matrix (Fin 3) (Fin 3) K).col i =
        ![(t.1 : K), t.2.1, t.2.2] i • (h : Matrix (Fin 3) (Fin 3) K).col i
    rw [hcol, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
      ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one, Matrix.mul_one, coe_diagHom,
      ← Matrix.mulVec_mulVec]
    have hd : diagonal ![(t.1 : K), t.2.1, t.2.2] *ᵥ Pi.single i 1 =
        ![(t.1 : K), t.2.1, t.2.2] i • Pi.single i 1 := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp [Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply]
      · simp [Matrix.mulVec, dotProduct, diagonal_apply, Pi.single_apply, hij]
    rw [hd, Matrix.mulVec_smul]

end T27

section Main

theorem mk_eq_one_iff_mem_statedScalars' {K : Type} [Field K] {w : GL (Fin 3) K} :
    ProjGenLinGroup.mk w = 1 ↔ w ∈ StatedScalars (Fin 3) K := by
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  rfl

theorem kSL3PiOrder3TypeC : KSL3PiOrder3TypeC := by
  intro π p f K _ hK hq h9 x hx hx3 hx1
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
  have hq9 : 9 ∣ qSubPi π (p ^ f) := by
    rw [← modNine_iff hq1]
    cases π
    · change p ^ f % 3 = 2 at hq
      change p ^ f % 9 = 8
      omega
    · change p ^ f % 3 = 1 at hq
      change p ^ f % 9 = 1
      omega
  have h9K : 9 ∣ Nat.card K - 1 := dvd_trans hq9 (qSubPi_dvd hK)
  obtain ⟨g, hg, rfl⟩ := hx
  have hg3 : g ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars', map_pow]
    exact hx3
  obtain ⟨ε, hε⟩ := hg3
  have hdetg : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hg).2
  have hε3 : ε ^ 3 = 1 := by
    have h1 := congrArg (fun y : GL (Fin 3) K => (y : Matrix (Fin 3) (Fin 3) K).det) hε
    simp only [det_scalar_eq, Units.val_pow_eq_pow_val, det_pow, hdetg, one_pow] at h1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
  obtain ⟨μ, hμ⟩ := exists_pow_three_eq h9K hε3
  have hgs : g ∉ StatedScalars (Fin 3) K := fun h =>
    hx1 (mk_eq_one_iff_mem_statedScalars'.mpr h)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨y, ⟨z, hz, rfl⟩, h, hh, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1
    (slPi_le_glPi hπ hg) hgs (μ := μ) (by rw [hμ, hε])
  obtain ⟨ζ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Kˣ × Kˣ × Kˣ,
      h⁻¹ * (g * GeneralLinearGroup.scalar (Fin 3) ζ) * h = diagHom t₀ := by
    rcases hcase with hD | ⟨e, -, hD⟩
    · exact ⟨(Units.mk0 τ hτ0, Units.mk0 τ hτ0 ^ 2, 1), by
        rw [hD, diagTau_eq_diagUnits hτ hτ0]
        rfl⟩
    · exact ⟨(e, 1, 1), hD⟩
  have hsc : ∀ (u : Kˣ) (B : GL (Fin 3) K),
      B * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * B :=
    fun u B => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u B).eq
  set t : Kˣ × Kˣ × Kˣ := t₀ * (ζ⁻¹, ζ⁻¹, ζ⁻¹) with ht
  have hgt : h⁻¹ * g * h = diagHom t := by
    have e1 : diagHom t = diagHom t₀ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by
      rw [ht, map_mul, scalar_eq_diagHom]
    have hs1 : GeneralLinearGroup.scalar (Fin 3) ζ * GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [e1, ← ht₀]
    calc h⁻¹ * g * h = h⁻¹ * g * h * (GeneralLinearGroup.scalar (Fin 3) ζ *
          GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) := by rw [hs1, mul_one]
      _ = h⁻¹ * g * (h * GeneralLinearGroup.scalar (Fin 3) ζ) *
          GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by group
      _ = h⁻¹ * g * (GeneralLinearGroup.scalar (Fin 3) ζ * h) *
          GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by rw [hsc ζ h]
      _ = h⁻¹ * (g * GeneralLinearGroup.scalar (Fin 3) ζ) * h *
          GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ := by group
  have htE : t ∈ t27Units K := by
    have hdet : ((diagHom t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← hgt]
      have h1 := det_conj_eq h⁻¹ g
      rw [inv_inv] at h1
      rw [h1, hdetg]
    rw [det_diagHom] at hdet
    have h3 : diagHom (t ^ 3) = diagHom (ε, ε, ε) := by
      rw [map_pow, ← hgt, ← scalar_eq_diagHom]
      have h0 := conj_pow (a := h⁻¹) (b := g) (i := 3)
      rw [inv_inv] at h0
      rw [h0, ← hε, hsc ε h⁻¹, inv_mul_cancel_right]
    have h3' := diagHom_injective h3
    have e1 : t.1 ^ 3 = ε := congrArg Prod.fst h3'
    have e2 : t.2.1 ^ 3 = ε := congrArg (fun s => s.2.1) h3'
    have e3 : t.2.2 ^ 3 = ε := congrArg (fun s => s.2.2) h3'
    exact ⟨e1.trans e2.symm, e1.trans e3.symm, Units.ext (by rw [hdet, Units.val_one])⟩
  refine ⟨t27Conj h, isTypeC_t27Conj hK hq hq9 hh, t27Conj_le_slPi hK hq9 hh, g, ⟨t, htE, ?_⟩,
    rfl⟩
  change h * diagHom t * h⁻¹ = g
  rw [← hgt]
  group

end Main

end CFSG.RankThree.PartTwo.KFacts
