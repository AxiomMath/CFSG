module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary

public section

namespace CFSG.StandardType

namespace TableBUR

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

section Inner

variable {R : Type*} [Group R]

theorem conj_injective_of_center (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro x
    have e := congrArg (fun α : MulAut R => α x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at e
    calc x * g = g * x * g⁻¹ * g := by rw [e]
      _ = g * x := by group
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact hgZ

theorem mul_conj_mul_inv_eq (α : MulAut R) (g : R) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem congr_conj {H : Type*} [Group H] (e : R ≃* H) (g : R) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
    MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem apply_eq_of_inf_inn_eq_bot (hZ : Subgroup.center R = ⊥) {U : Subgroup (MulAut R)}
    (hU : U ⊓ (MulAut.conj : R →* MulAut R).range = ⊥) {g : R}
    (hg : MulAut.conj g ∈ Subgroup.normalizer (U : Set (MulAut R))) {u : MulAut R}
    (hu : u ∈ U) : u g = g := by
  have h1 : MulAut.conj g * u * (MulAut.conj g)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have h2 : MulAut.conj g * u * (MulAut.conj g)⁻¹ * u⁻¹ ∈
      U ⊓ (MulAut.conj : R →* MulAut R).range := by
    refine ⟨U.mul_mem h1 (U.inv_mem hu), ⟨g * u g⁻¹, ?_⟩⟩
    rw [map_mul, ← mul_conj_mul_inv_eq u g⁻¹, map_inv]
    group
  rw [hU, Subgroup.mem_bot] at h2
  have h3 : MulAut.conj g * u = u * MulAut.conj g := by
    calc MulAut.conj g * u = MulAut.conj g * u * (MulAut.conj g)⁻¹ * u⁻¹ * (u * MulAut.conj g) := by
          group
      _ = u * MulAut.conj g := by rw [h2, one_mul]
  have h4 : u * MulAut.conj g * u⁻¹ = MulAut.conj g := by
    rw [← h3]
    group
  rw [mul_conj_mul_inv_eq] at h4
  exact conj_injective_of_center hZ h4

end Inner

section Unitary

variable {K : Type} [Field K] [Finite K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
include h in
theorem diag_pow_norm {x : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hx : (x : GL (Fin d) K) = diagHom d σ) (i : Fin d) : (σ i : K) ^ (2 ^ n + 1) = 1 := by
  have h1 := ((mem_unitarySU_iff h).mp x.2).2
  rw [hx, coe_diagHom, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] at h1
  have h2 := congrFun (congrFun h1 i) i
  simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, UnitaryFieldData.bar_apply] at h2
  rw [pow_succ]
  exact h2

omit [Finite K] in
include h in
theorem eq_bot_of_normalizes_twoSubgroup {A : Subgroup ↥(unitarySU 2 n K d)}
    (hdist : ∀ i j : Fin d, i ≠ j → ∃ x ∈ A, ∃ σ : Fin d → Kˣ,
      (x : GL (Fin d) K) = diagHom d σ ∧ σ i ≠ σ j)
    {V : Subgroup (LargeEvenProj (unitarySU 2 n K d))} (hV2 : IsPGroup 2 V)
    (hAV : A.map (LargeEvenProjMk (unitarySU 2 n K d)) ≤
      Subgroup.normalizer (V : Set (LargeEvenProj (unitarySU 2 n K d)))) : V = ⊥ := by
  by_contra hV1
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hVr : V ≤ π.range := by
    rw [hπ, LargeEvenProjMk, QuotientGroup.range_mk']
    exact le_top
  obtain ⟨s, t, hst, hpair⟩ := SURepair.exists_framePair_of_twoSubgroup h
    TableBUE.ker_projMk_le_center hV1 hV2 hVr hAV
  obtain ⟨x, hxA, σ, hxσ, hσ⟩ := hdist s t hst
  refine hσ (hpair (π x) ⟨x, hxA, rfl⟩ σ ⟨fun i => diag_pow_norm h hxσ i, fun y y' hy' => ?_⟩)
  have hy : y' = x * y * x⁻¹ := by
    apply Subtype.ext
    rw [hy', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
  rw [hy, map_mul, map_mul, map_inv]

omit [Finite K] in
include h in
theorem outer_case (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    (hbot : (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) = ⊥)
    {A : Subgroup ↥(unitarySU 2 n K d)}
    (hout : ∀ φ : K ≃+* K, φ ≠ 1 → ∃ x ∈ A, ∃ σ : Fin d → Kˣ,
      (x : GL (Fin d) K) = diagHom d σ ∧ ∃ i, ∀ j, φ (σ j : K) ≠ (σ i : K))
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U)
    (hAU : (A.map (LargeEvenProjMk (unitarySU 2 n K d))).map MulAut.conj ≤
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d)))))
    (hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥)
    (hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range = ⊥) :
    False := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  obtain ⟨⟨u, huU⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
  have hfix : ∀ x ∈ A, u (π x) = π x := fun x hx =>
    apply_eq_of_inf_inn_eq_bot hZ hUI (hAU ⟨π x, ⟨x, hx, rfl⟩, rfl⟩) huU
  have hd1 : 1 ≤ d := by omega
  have hC := isPrimeFormGram_one (K := K) (n := d)
  set e : LargeEvenProj (unitarySU 2 n K d) ≃*
      primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    InndiagSU.projEquiv h hd1 with he
  set E := MulAut.congr e with hE
  obtain ⟨-, -, -, -, hreal, -, -, -, -, -, hcardD⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hd hq
  obtain ⟨φ, ⟨B, hB⟩, -⟩ := hreal (E u)
  by_cases hφ : φ = 1
  ·
    subst hφ
    rw [map_one, mul_one] at hB
    obtain ⟨k, hk⟩ := hU2 ⟨u, huU⟩
    have hk' : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
    set D := primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hD
    set N := (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))).subgroupOf D with hN
    set y : D := ⟨E u, ⟨B, hB.symm⟩⟩ with hy
    have hy2 : y ^ 2 ^ k = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hy]
      change (E u) ^ 2 ^ k = 1
      rw [← map_pow, hk', map_one]
    have hord : orderOf (y : D ⧸ N) = 1 := by
      have h1 : orderOf (y : D ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one])
      have h2 : orderOf (y : D ⧸ N) ∣ 2 ^ n + 1 := (orderOf_dvd_natCard _).trans hcardD
      have hodd : Nat.Coprime (2 ^ k) (2 ^ n + 1) := by
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_two_left]
        exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)
      exact Nat.eq_one_of_dvd_coprimes hodd h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hord
    obtain ⟨y', hy'⟩ := hord
    have hu : u = MulAut.conj (e.symm y') := by
      apply E.injective
      rw [hE, congr_conj, MulEquiv.apply_symm_apply]
      exact hy'.symm
    apply hu1'
    have hmem : u ∈ U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range :=
      ⟨huU, ⟨e.symm y', hu.symm⟩⟩
    rw [hUI, Subgroup.mem_bot] at hmem
    exact hmem
  ·
    obtain ⟨x, hxA, σ, hxσ, i, hi⟩ := hout φ hφ
    have hZC : normOneScalars h (gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) d =
        ⊥ := by
      have hbot' : (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n)) =
          ⊥ := hbot
      rw [← InndiagSU.map_scalars_subgroupOf h hd1, hbot', Subgroup.map_bot]
    have h1 : E u (e (π x)) = e (π x) := by
      rw [hE, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply, hfix x hxA]
    set xg : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      ⟨x, InndiagSU.largeEvenSUGroup_eq_gramSU (d := d) h ▸ x.2⟩ with hxg
    have hex : e (π x) = (xg : primeFormP h _) := InndiagSU.projEquiv_mk h hd1 x
    rw [hex, hB, MulAut.mul_apply] at h1
    change primeFormConjHom h _ B (primeFormFieldAut h hC φ _) = _ at h1
    rw [primeFormFieldAut_mk, primeFormConjHom_mk, QuotientGroup.eq, hZC, Subgroup.mem_bot,
      inv_mul_eq_one] at h1
    have h2 : (B : GL (Fin d) K) * glAut φ (x : GL (Fin d) K) * (B : GL (Fin d) K)⁻¹ = x :=
      congrArg (fun z : gramSU h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =>
        (z : GL (Fin d) K)) h1
    have h3 : (((B : GL (Fin d) K) * glAut φ (x : GL (Fin d) K) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (((x : GL (Fin d) K) * (B : GL (Fin d) K) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) := by
      congr 1
      calc (B : GL (Fin d) K) * glAut φ (x : GL (Fin d) K) =
          (B : GL (Fin d) K) * glAut φ (x : GL (Fin d) K) * (B : GL (Fin d) K)⁻¹ *
            (B : GL (Fin d) K) := by group
        _ = x * B := by rw [h2]
    rw [Units.val_mul, Units.val_mul, coe_glAut, hxσ, coe_diagHom,
      Matrix.diagonal_map (map_zero φ)] at h3
    have hrow : ∀ j, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
      intro j
      have h4 := congrFun (congrFun h3 i) j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h4
      have h5 : (φ (σ j : K) - (σ i : K)) * ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          0 := by
        rw [sub_mul, mul_comm, h4, sub_self]
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd (sub_eq_zero.mp h6) (hi j)
      · exact h6
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (B : GL (Fin d) K).isUnit).ne_zero
      (Matrix.det_eq_zero_of_row_eq_zero i hrow)

include h in
theorem not_exists_twoSubgroup_of_diag (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    (hbot : (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) = ⊥)
    {A : Subgroup ↥(unitarySU 2 n K d)}
    (hdist : ∀ i j : Fin d, i ≠ j → ∃ x ∈ A, ∃ σ : Fin d → Kˣ,
      (x : GL (Fin d) K) = diagHom d σ ∧ σ i ≠ σ j)
    (hout : ∀ φ : K ≃+* K, φ ≠ 1 → ∃ x ∈ A, ∃ σ : Fin d → Kˣ,
      (x : GL (Fin d) K) = diagHom d σ ∧ ∃ i, ∀ j, φ (σ j : K) ≠ (σ i : K))
    {U : Subgroup (MulAut (LargeEvenProj (unitarySU 2 n K d)))} (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U)
    (hAU : (A.map (LargeEvenProjMk (unitarySU 2 n K d))).map MulAut.conj ≤
      Subgroup.normalizer (U : Set (MulAut (LargeEvenProj (unitarySU 2 n K d))))) : False := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun he => hq ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    TableBUE.center_proj_eq_bot hK hd hdq
  have hinj := conj_injective_of_center hZ
  by_cases hUI : U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range = ⊥
  · exact outer_case h hd hq hbot hout hU1 hU2 hAU hZ hUI
  ·
    set V := (U ⊓ (MulAut.conj : LargeEvenProj (unitarySU 2 n K d) →* MulAut _).range).comap
      MulAut.conj with hV
    have hV2 : IsPGroup 2 V := (hU2.to_le inf_le_left).comap_of_injective _ hinj
    have hAV : A.map π ≤ Subgroup.normalizer (V : Set (LargeEvenProj (unitarySU 2 n K d))) := by
      intro b hb
      have hcb := hAU ⟨b, hb, rfl⟩
      rw [Subgroup.mem_normalizer_iff] at hcb ⊢
      intro v
      change MulAut.conj v ∈ U ⊓ _ ↔ MulAut.conj (b * v * b⁻¹) ∈ U ⊓ _
      rw [map_mul, map_mul, map_inv, Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, -⟩
        exact ⟨(hcb _).mp h1, ⟨b * v * b⁻¹, by rw [map_mul, map_mul, map_inv]⟩⟩
      · rintro ⟨h1, -⟩
        exact ⟨(hcb _).mpr h1, ⟨v, rfl⟩⟩
    have hVbot := eq_bot_of_normalizes_twoSubgroup h hdist hV2 hAV
    apply hUI
    rw [eq_bot_iff]
    rintro α ⟨hαU, ⟨g, rfl⟩⟩
    have hg : g ∈ V := ⟨hαU, ⟨g, rfl⟩⟩
    rw [hVbot, Subgroup.mem_bot] at hg
    rw [hg, map_one]
    exact Subgroup.one_mem _

end Unitary

end TableBUR

end CFSG.StandardType
