module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofLin
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3

open CFSG.RankThree.Classical2 (unitarySet)
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open scoped Matrix

theorem mem_fixedField_iff {Ω : Type} [Field Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (c : Ω) :
    c ∈ RingHom.eqLocusField (iterateFrobenius Ω ℓ (2 * f)) (RingHom.id Ω) ↔
      c ^ (ℓ ^ f) ^ 2 = c := by
  have hqq : ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 := by ring
  rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply, hqq]

theorem natCard_fixedField {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) :
    Nat.card (RingHom.eqLocusField (iterateFrobenius Ω ℓ (2 * f)) (RingHom.id Ω)) =
      (ℓ ^ f) ^ 2 := by
  have hqq : ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 := by ring
  rw [← hqq]
  exact CFSG.RankThree.Chevalley.natCard_eqLocusField_frob hℓ.out (by omega)
    (fun c => iterateFrobenius_def ℓ (2 * f) c)

theorem mapMatrix_scalar {F Ω : Type} [Field F] [Field Ω] (ι : F →+* Ω) (μ : F) (n : ℕ) :
    ι.mapMatrix (Matrix.scalar (Fin n) μ) = Matrix.scalar (Fin n) (ι μ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem sq_add_add_one_of_cube' {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h1)

theorem transfer_forward {F Ω : Type} [Field F] [Field Ω] (ι : F →+* Ω)
    (hι : Function.Injective ι) (σ : F ≃+* F) {q : ℕ} (hσ : ∀ c : F, ι (σ c) = ι c ^ q)
    {X₀ : Matrix (Fin 3) (Fin 3) F} {X : Matrix (Fin 3) (Fin 3) Ω} (hXm : ι.mapMatrix X₀ = X)
    (hdet : X.det = 1) (hU : (X.map (· ^ q))ᵀ * X = 1) (hX3 : X ^ 3 = 1)
    (hXs : ∀ μ : Ω, X ≠ Matrix.scalar (Fin 3) μ) :
    X₀.det = 1 ∧ CFSG.LieType.Universal.Unitary.conjTr σ X₀ * X₀ = 1 ∧ X₀ ^ 3 = 1 ∧
      ∀ μ : F, X₀ ≠ Matrix.scalar (Fin 3) μ := by
  have hinj : Function.Injective
      (ι.mapMatrix : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) Ω) :=
    fun M N h => Matrix.map_injective hι h
  have hent : ∀ i j, ι (X₀ i j) = X i j := fun i j => congrFun (congrFun hXm i) j
  have hσm : (X₀.map σ).map ι = X.map (· ^ q) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [hσ, hent]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hι
    rw [map_one, RingHom.map_det, hXm, hdet]
  · apply hinj
    rw [map_one, map_mul, hXm]
    have hc : ι.mapMatrix (CFSG.LieType.Universal.Unitary.conjTr σ X₀) =
        (X.map (· ^ q))ᵀ := by
      rw [CFSG.LieType.Universal.Unitary.conjTr, RingHom.mapMatrix_apply, Matrix.transpose_map,
        hσm]
    rw [hc]
    exact hU
  · apply hinj
    rw [map_pow, map_one, hXm, hX3]
  · intro μ hμ
    apply hXs (ι μ)
    rw [← hXm, hμ, mapMatrix_scalar]

theorem transfer_backward {F Ω : Type} [Field F] [Field Ω] (ι : F →+* Ω)
    (hι : Function.Injective ι) (σ : F ≃+* F) {q : ℕ} (hσ : ∀ c : F, ι (σ c) = ι c ^ q)
    {X₀ : Matrix (Fin 3) (Fin 3) F} {X : Matrix (Fin 3) (Fin 3) Ω} (hXm : ι.mapMatrix X₀ = X)
    {G₀ : Matrix (Fin 3) (Fin 3) F} (hGdet : G₀.det = 1)
    (hGU : CFSG.LieType.Universal.Unitary.conjTr σ G₀ * G₀ = 1)
    {l : F} (hl3 : l ^ 3 = 1) (hl1 : l ≠ 1) (hGX : G₀ * X₀ = l • (X₀ * G₀)) :
    (ι.mapMatrix G₀).det = 1 ∧ ((ι.mapMatrix G₀).map (· ^ q))ᵀ * ι.mapMatrix G₀ = 1 ∧
      ι.mapMatrix G₀ * X = ι l • (X * ι.mapMatrix G₀) ∧ ι l ^ 3 = 1 ∧ ι l ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← RingHom.map_det, hGdet, map_one]
  · have hσG : (G₀.map σ).map ι = (G₀.map ι).map (· ^ q) := by
      ext i j
      simp only [Matrix.map_apply]
      exact hσ _
    have hc : ((ι.mapMatrix G₀).map (· ^ q))ᵀ = ι.mapMatrix (CFSG.LieType.Universal.Unitary.conjTr σ G₀) := by
      show ((G₀.map ι).map (· ^ q))ᵀ = ((G₀.map σ)ᵀ).map ι
      rw [Matrix.transpose_map, hσG]
    have h1 : ι.mapMatrix (CFSG.LieType.Universal.Unitary.conjTr σ G₀ * G₀) = 1 := by
      rw [hGU, map_one]
    rw [map_mul] at h1
    rw [hc, h1]
  · have hsmul : ∀ (c : F) (M : Matrix (Fin 3) (Fin 3) F),
        ι.mapMatrix (c • M) = ι c • ι.mapMatrix M := by
      intro c M
      ext i j
      simp [RingHom.mapMatrix_apply, Matrix.map_apply]
    have h2 : ι.mapMatrix (G₀ * X₀) = ι.mapMatrix (l • (X₀ * G₀)) := by rw [hGX]
    rw [map_mul, hXm, hsmul, map_mul, hXm] at h2
    exact h2
  · rw [← map_pow, hl3, map_one]
  · intro h
    apply hl1
    apply hι
    rw [h, map_one]

theorem charP_subfield {Ω : Type} [Field Ω] {ℓ : ℕ} [CharP Ω ℓ] (F : Subfield Ω) :
    CharP F ℓ := by
  refine ⟨fun x => ?_⟩
  have hx : ((x : F) : Ω) = (x : Ω) := map_natCast F.subtype x
  rw [← CharP.cast_eq_zero_iff Ω ℓ x, ← hx]
  exact ⟨fun h => by simp [h], fun h => Subtype.ext (by simpa using h)⟩

theorem exists_rot_unitarySet {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hq1 : ℓ ^ f % 3 = 2) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ]
    {X : GL (Fin 3) Ω} (hX : X ∈ unitarySet (ℓ ^ f) 3) (hX3 : X ^ 3 = 1)
    (hXs : ∀ μ : Ω, (X : Matrix (Fin 3) (Fin 3) Ω) ≠ Matrix.scalar (Fin 3) μ) :
    ∃ G : GL (Fin 3) Ω, G ∈ unitarySet (ℓ ^ f) 3 ∧ ∃ l : Ω, l ^ 3 = 1 ∧ l ≠ 1 ∧
      (G : Matrix (Fin 3) (Fin 3) Ω) * (X : Matrix (Fin 3) (Fin 3) Ω) =
        l • ((X : Matrix (Fin 3) (Fin 3) Ω) * (G : Matrix (Fin 3) (Fin 3) Ω)) := by
  obtain ⟨F, hF⟩ : ∃ F : Subfield Ω,
      F = RingHom.eqLocusField (iterateFrobenius Ω ℓ (2 * f)) (RingHom.id Ω) := ⟨_, rfl⟩
  have hmem : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hF]; exact mem_fixedField_iff c
  have hcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hF]; exact natCard_fixedField hf
  haveI : Finite F := Nat.finite_of_card_ne_zero
    (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.out.ne_zero))
  haveI : CharP F ℓ := charP_subfield F
  have h3Ω : (3 : Ω) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : Ω) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff Ω ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three Ω h3Ω
  have hζ3u : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ3 : (ζ : Ω) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hζ3u, Units.val_one]
  have hζ1 : (ζ : Ω) ≠ 1 := by
    intro h
    have h' : ζ = 1 := Units.ext h
    rw [h', orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  obtain ⟨k, hk⟩ : ∃ k, (ℓ ^ f) ^ 2 = 3 * k + 1 := by
    have h9 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq1]
    exact ⟨(ℓ ^ f) ^ 2 / 3, by omega⟩
  have hζF : (ζ : Ω) ∈ F := by
    rw [hmem, hk, pow_succ, pow_mul, hζ3, one_pow, one_mul]
  obtain ⟨ωF, hωF⟩ : ∃ w : F, (w : Ω) = (ζ : Ω) := ⟨⟨(ζ : Ω), hζF⟩, rfl⟩
  have hωF3 : ωF ^ 3 = 1 := Subtype.ext (by simp [hωF, hζ3])
  have hωF1 : ωF ≠ 1 := by
    intro h
    apply hζ1
    simp [← hωF, h]
  have hωF2 : ωF ^ 2 + ωF + 1 = 0 := sq_add_add_one_of_cube' hωF3 hωF1
  have hσ3 : ∀ x : F, x ^ 3 = 1 → unitaryInvolution F ℓ f x * x = 1 := by
    intro x hx
    obtain ⟨t, ht⟩ : 3 ∣ ℓ ^ f + 1 := Nat.dvd_of_mod_eq_zero (by omega)
    rw [unitaryInvolution_apply, ← pow_succ, ht, pow_mul, hx, one_pow]
  have hσσ : ∀ x : F, unitaryInvolution F ℓ f (unitaryInvolution F ℓ f x) = x :=
    unitaryInvolution_involutive hcard
  have hnorm : ∀ c : F, c ≠ 0 → unitaryInvolution F ℓ f c = c →
      ∃ a, unitaryInvolution F ℓ f a * a = c :=
    fun c hc0 hcσ => CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hcard hcσ hc0
  have hσι : ∀ c : F, F.subtype (unitaryInvolution F ℓ f c) = F.subtype c ^ (ℓ ^ f) := by
    intro c
    rw [unitaryInvolution_apply, map_pow]
  unfold unitarySet at hX
  obtain ⟨hX1, hX2, hX4⟩ := hX
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Matrix (Fin 3) (Fin 3) F, ∀ i j,
      ((X₀ i j : F) : Ω) = (X : Matrix (Fin 3) (Fin 3) Ω) i j :=
    ⟨Matrix.of fun i j => ⟨(X : Matrix (Fin 3) (Fin 3) Ω) i j, (hmem _).2 (hX1 i j)⟩,
      fun i j => rfl⟩
  have hXm : F.subtype.mapMatrix X₀ = (X : Matrix (Fin 3) (Fin 3) Ω) :=
    Matrix.ext fun i j => hX₀ i j
  have hXm3 : (X : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hX3, Units.val_one]
  obtain ⟨hdetF, hUF, hcubeF, hnsF⟩ := transfer_forward F.subtype F.subtype.injective
    (unitaryInvolution F ℓ f) hσι hXm hX2 hX4 hXm3 hXs
  obtain ⟨G₀, hG₀det, hG₀U, l₀, hl₀3, hl₀1, hG₀X⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res424Seven.exists_rot_unitary (unitaryInvolution F ℓ f)
      hσσ hnorm hσ3 hωF2 hωF1 hdetF hUF hcubeF hnsF
  obtain ⟨hdetG, hUG, hGX, hl3, hl1⟩ := transfer_backward F.subtype F.subtype.injective
    (unitaryInvolution F ℓ f) hσι hXm hG₀det hG₀U hl₀3 hl₀1 hG₀X
  have hMdet : (F.subtype.mapMatrix G₀).det ≠ 0 := by
    rw [hdetG]; exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hMdet, ?_, F.subtype l₀, hl3, hl1, ?_⟩
  · unfold unitarySet
    rw [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact ⟨fun i j => (hmem _).1 (G₀ i j).2, hdetG, hUG⟩
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hGX

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3

end
