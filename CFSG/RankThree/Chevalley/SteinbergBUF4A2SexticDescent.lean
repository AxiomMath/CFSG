module

public import CFSG.RankThree.Chevalley.SteinbergBUF4A2SexticFields
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusA2Unitary

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN

section Twist

variable {M : Type} [Field M] [CharP M 2] {w₀ : WeylGroup Tag.F4}

theorem f4A2Equiv_negOne_entrywise (κ : F4A2Kind) (σ : M →+* M)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    ∃ hg : canonicalRep (coxeterSystem Tag.F4) M w₀ * Units.map (entrywiseHom σ) g *
        (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
      ((f4A2Equiv M κ ⟨_, hg⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) =
        ((((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M).map σ)⁻¹)ᵀ := by
  obtain ⟨-, -, -, -, -, -, hmapσ, -, hneg, -⟩ :=
    even_F4_native_A2_root_groups_exact_SL3_restriction M κ
  obtain ⟨hσg, hσr⟩ := hmapσ σ g
  obtain ⟨hN, hNr⟩ := hneg w₀ hw₀
  exact ⟨hN _ hσg, by rw [hNr ⟨_, hσg⟩, hσr]⟩

theorem f4A2_negOne_twist_conj (κ : F4A2Kind) (σ : M →+* M)
    (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) {m : ModGL Tag.F4 M}
    (hm : m ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}) (a : subsystemGroup Tag.F4 M {κ.i, κ.j})
    (ha : ((f4A2Equiv M κ ⟨m, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) =
      (f4A2Equiv M κ a : Matrix (Fin 3) (Fin 3) M) *
        ((f4A2Equiv M κ a : Matrix (Fin 3) (Fin 3) M).map σ)ᵀ) (g : ModGL Tag.F4 M) :
    m * canonicalRep (coxeterSystem Tag.F4) M w₀ * Units.map (entrywiseHom σ) g *
        (m * canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ =
      (a : ModGL Tag.F4 M) * (canonicalRep (coxeterSystem Tag.F4) M w₀ *
        Units.map (entrywiseHom σ) ((a : ModGL Tag.F4 M)⁻¹ * g * (a : ModGL Tag.F4 M)) *
          (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹) * (a : ModGL Tag.F4 M)⁻¹ := by
  obtain ⟨hθa, hr⟩ := f4A2Equiv_negOne_entrywise κ σ hw₀ a
  have hXdet : IsUnit (((f4A2Equiv M κ a : Matrix.SpecialLinearGroup (Fin 3) M) :
      Matrix (Fin 3) (Fin 3) M).map σ)ᵀ.det := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.SpecialLinearGroup.det_coe, map_one]
    exact isUnit_one
  have hmeq : m = (a : ModGL Tag.F4 M) * (canonicalRep (coxeterSystem Tag.F4) M w₀ *
      Units.map (entrywiseHom σ) a * (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹)⁻¹ := by
    have e : (⟨m, hm⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) = a * (⟨_, hθa⟩)⁻¹ := by
      apply (f4A2Equiv M κ).injective
      apply Subtype.ext
      rw [map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul, Classical2.coe_inv_eq_nonsing_inv,
        hr, ha, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hXdet]
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this
  rw [hmeq]
  simp only [map_mul, map_inv]
  group

end Twist

section Unitary

variable {K₂ K₆ : Type} [Field K₂] [Field K₆] [Algebra K₂ K₆] [CharP K₂ 2] [CharP K₆ 2]

theorem f4A2_unitary_iff_baseChange (κ : F4A2Kind) (σ : K₆ ≃+* K₆) (σ₂ : K₂ ≃+* K₂)
    (hcomp : ∀ b, σ (algebraMap K₂ K₆ b) = algebraMap K₂ K₆ (σ₂ b))
    (hfix : ∀ B : Matrix (Fin 3) (Fin 3) K₆, (B.map σ).map σ = B →
      ∃ B₂ : Matrix (Fin 3) (Fin 3) K₂, B₂.map (algebraMap K₂ K₆) = B)
    (g : subsystemGroup Tag.F4 K₆ {κ.i, κ.j}) :
    ((f4A2Equiv K₆ κ g : Matrix (Fin 3) (Fin 3) K₆).map σ)ᵀ *
        (f4A2Equiv K₆ κ g : Matrix (Fin 3) (Fin 3) K₆) = 1 ↔
      ∃ u : subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
        ((f4A2Equiv K₂ κ u : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
          (f4A2Equiv K₂ κ u : Matrix (Fin 3) (Fin 3) K₂) = 1 ∧
        (g : ModGL Tag.F4 K₆) = baseChangeGL (algebraMap K₂ K₆) u := by
  have hσι : ∀ B₂ : Matrix (Fin 3) (Fin 3) K₂,
      (B₂.map (algebraMap K₂ K₆)).map σ = (B₂.map σ₂).map (algebraMap K₂ K₆) := fun B₂ => by
    rw [Matrix.map_map, Matrix.map_map]
    congr 1
    funext b
    exact hcomp b
  have hunit : ∀ B₂ : Matrix (Fin 3) (Fin 3) K₂,
      (((B₂.map (algebraMap K₂ K₆)).map σ)ᵀ * B₂.map (algebraMap K₂ K₆) = 1 ↔
        (B₂.map σ₂)ᵀ * B₂ = 1) := fun B₂ => by
    rw [hσι, ← Matrix.transpose_map, ← Matrix.map_mul,
      ← Matrix.map_one (algebraMap K₂ K₆) (map_zero _) (map_one _)]
    exact (Matrix.map_injective (algebraMap K₂ K₆).injective).eq_iff
  constructor
  · intro hB
    obtain ⟨B₂, hB₂⟩ := hfix _ (map_map_eq_of_unitary σ hB)
    have hdet : B₂.det = 1 := (algebraMap K₂ K₆).injective (by
      rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hB₂,
        Matrix.SpecialLinearGroup.det_coe])
    obtain ⟨u, hu⟩ := (f4A2Equiv K₂ κ).surjective ⟨B₂, hdet⟩
    have hru : (f4A2Equiv K₂ κ u : Matrix (Fin 3) (Fin 3) K₂) = B₂ := by rw [hu]
    refine ⟨u, ?_, ?_⟩
    · rw [hru, ← hunit, hB₂]
      exact hB
    · have e : (⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K₂ K₆) u.2⟩ :
          subsystemGroup Tag.F4 K₆ {κ.i, κ.j}) = g := by
        apply (f4A2Equiv K₆ κ).injective
        apply Subtype.ext
        rw [f4A2Equiv_baseChange_algebraMap κ u, hru, hB₂]
      exact (congrArg Subtype.val e).symm
  · rintro ⟨u, hu, hg⟩
    have e : g = ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K₂ K₆) u.2⟩ := Subtype.ext hg
    rw [e, f4A2Equiv_baseChange_algebraMap κ u, hunit]
    exact hu

theorem f4A2_sextic_fixed_eq (κ : F4A2Kind) (σ : K₆ ≃+* K₆) (σ₂ : K₂ ≃+* K₂)
    (hcomp : ∀ b, σ (algebraMap K₂ K₆ b) = algebraMap K₂ K₆ (σ₂ b))
    (hfix : ∀ B : Matrix (Fin 3) (Fin 3) K₆, (B.map σ).map σ = B →
      ∃ B₂ : Matrix (Fin 3) (Fin 3) K₂, B₂.map (algebraMap K₂ K₆) = B)
    {w₀ : WeylGroup Tag.F4} (hw₀ : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    {m : ModGL Tag.F4 K₆} (hm : m ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j})
    (a : subsystemGroup Tag.F4 K₆ {κ.i, κ.j})
    (ha : ((f4A2Equiv K₆ κ ⟨m, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) K₆) :
        Matrix (Fin 3) (Fin 3) K₆) =
      (f4A2Equiv K₆ κ a : Matrix (Fin 3) (Fin 3) K₆) *
        ((f4A2Equiv K₆ κ a : Matrix (Fin 3) (Fin 3) K₆).map σ)ᵀ)
    (θ : ModGL Tag.F4 K₆ →* ModGL Tag.F4 K₆)
    (hθ : ∀ g, θ g = m * canonicalRep (coxeterSystem Tag.F4) K₆ w₀ *
      Units.map (entrywiseHom σ.toRingHom) g * (m * canonicalRep (coxeterSystem Tag.F4) K₆ w₀)⁻¹)
    {U : Subgroup (ModGL Tag.F4 K₂)}
    (hU : ∀ v, v ∈ U ↔ ∃ hv : v ∈ subsystemGroup Tag.F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨v, hv⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1) :
    subsystemGroup Tag.F4 K₆ {κ.i, κ.j} ⊓ θ.eqLocus (MonoidHom.id _) =
      U.map ((MulAut.conj (a : ModGL Tag.F4 K₆)).toMonoidHom.comp
        (baseChangeGL (algebraMap K₂ K₆))) := by
  ext g
  rw [Subgroup.mem_inf, show g ∈ θ.eqLocus (MonoidHom.id _) ↔ θ g = g from Iff.rfl,
    Subgroup.mem_map, hθ, f4A2_negOne_twist_conj κ σ.toRingHom hw₀ hm a ha g]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, hfg⟩
    have hg' : (a : ModGL Tag.F4 K₆)⁻¹ * g * (a : ModGL Tag.F4 K₆) ∈
        subsystemGroup Tag.F4 K₆ {κ.i, κ.j} :=
      mul_mem (mul_mem (inv_mem a.2) hg) a.2
    have hfix' : twistedEntrywise (canonicalRep (coxeterSystem Tag.F4) K₆ w₀) σ.toRingHom
        ((a : ModGL Tag.F4 K₆)⁻¹ * g * (a : ModGL Tag.F4 K₆)) =
          (a : ModGL Tag.F4 K₆)⁻¹ * g * (a : ModGL Tag.F4 K₆) := by
      rw [twistedEntrywise_apply]
      calc _ = (a : ModGL Tag.F4 K₆)⁻¹ * ((a : ModGL Tag.F4 K₆) *
            (canonicalRep (coxeterSystem Tag.F4) K₆ w₀ *
              Units.map (entrywiseHom σ.toRingHom)
                ((a : ModGL Tag.F4 K₆)⁻¹ * g * (a : ModGL Tag.F4 K₆)) *
              (canonicalRep (coxeterSystem Tag.F4) K₆ w₀)⁻¹) * (a : ModGL Tag.F4 K₆)⁻¹) *
                (a : ModGL Tag.F4 K₆) := by
            group
        _ = _ := by rw [hfg]
    have hunit := (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ σ.toRingHom hw₀
      ⟨_, hg'⟩).1 hfix'
    obtain ⟨u, hu, hgu⟩ := (f4A2_unitary_iff_baseChange κ σ σ₂ hcomp hfix ⟨_, hg'⟩).1 hunit
    refine ⟨u, (hU u).2 ⟨u.2, hu⟩, ?_⟩
    change (a : ModGL Tag.F4 K₆)⁻¹ * g * (a : ModGL Tag.F4 K₆) =
      baseChangeGL (algebraMap K₂ K₆) u at hgu
    rw [← hgu]
    group
  · rintro ⟨u, huU, rfl⟩
    obtain ⟨hu2, hu⟩ := (hU u).1 huU
    have hbu : baseChangeGL (algebraMap K₂ K₆) u ∈ subsystemGroup Tag.F4 K₆ {κ.i, κ.j} :=
      baseChangeGL_mem_subsystemGroup _ hu2
    refine ⟨mul_mem (mul_mem a.2 hbu) (inv_mem a.2), ?_⟩
    have e : (a : ModGL Tag.F4 K₆)⁻¹ * ((a : ModGL Tag.F4 K₆) * baseChangeGL (algebraMap K₂ K₆) u *
        (a : ModGL Tag.F4 K₆)⁻¹) * (a : ModGL Tag.F4 K₆) = baseChangeGL (algebraMap K₂ K₆) u := by
      group
    rw [e]
    have hunit := (f4A2_unitary_iff_baseChange κ σ σ₂ hcomp hfix ⟨_, hbu⟩).2
      ⟨⟨u, hu2⟩, hu, rfl⟩
    have hfx := (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ σ.toRingHom hw₀
      ⟨_, hbu⟩).2 hunit
    rw [twistedEntrywise_apply] at hfx
    change canonicalRep (coxeterSystem Tag.F4) K₆ w₀ *
      Units.map (entrywiseHom σ.toRingHom) (baseChangeGL (algebraMap K₂ K₆) u) *
        (canonicalRep (coxeterSystem Tag.F4) K₆ w₀)⁻¹ = baseChangeGL (algebraMap K₂ K₆) u at hfx
    rw [hfx]

end Unitary

end CFSG.RankThree.Chevalley
