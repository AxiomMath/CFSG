module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalA2
open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
open CFSG.Open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.E6
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.UnitaryPair
open scoped MatrixGroups
variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem unitary_full_intertwining {ℓ f : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω]
    [Algebra k Ω] {n : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    [IsAlgClosure k Ω] (hn : 3 ≤ n) (σ : Ω →+* Ω) (hσc : ∀ c, σ c = c ^ ℓ ^ f)
    (π : Equiv.Perm (Fin n)) (Φ : SL(n, Ω) ≃* SL(n, Ω)) (b : Fin n → Fin n → Ωˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f)) :
    ∃ H : SL(n, Ω),
      (∀ X : SL(n, Ω),
        Matrix.SpecialLinearGroup.toGL (Φ (H * X * H⁻¹)) =
          Matrix.SpecialLinearGroup.toGL H *
            invTransposeHom (Matrix.GeneralLinearGroup.map σ (Matrix.SpecialLinearGroup.toGL X)) *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
        ∃ Y ∈ unitarySet (ℓ ^ f) n, Matrix.SpecialLinearGroup.toGL X =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hσ : ⇑σ = (· ^ ℓ ^ f) := funext hσc
  obtain ⟨A, hA⟩ := exists_conj_map_inv_transpose_of_root_permuting hn σ π Φ.toMonoidHom b
    (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσc])
  have hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) := fun X => by
    have := hA X
    rwa [MulEquiv.coe_toMonoidHom, hσ] at this
  obtain ⟨H, hHdet, hdescent, hset⟩ :=
    matrix_graph_frobenius_unitary_descent hℓ hf hk (by omega : 1 ≤ n) A
  set Hs : SL(n, Ω) := ⟨H, hHdet⟩ with hHsdef
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  have hfix : ∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) n,
      Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL Hs * Y * (Matrix.SpecialLinearGroup.toGL Hs)⁻¹ := by
    intro X
    have hX := Set.ext_iff.mp hset (Matrix.SpecialLinearGroup.toGL X)
    rw [mem_fixSubgroup, hHs]
    constructor
    · intro h
      obtain ⟨Y, hY, hXY⟩ := hX.mp ⟨X.2, by
        show (A : Matrix (Fin n) (Fin n) Ω) *
            (((X : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
              (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω) = (X : Matrix (Fin n) (Fin n) Ω)
        rw [← hA' X, h]⟩
      exact ⟨Y, hY, hXY.symm⟩
    · rintro ⟨Y, hY, hXY⟩
      have h := (hX.mpr ⟨Y, hY, hXY.symm⟩).2
      apply Subtype.ext
      rw [hA' X]
      exact h
  refine ⟨Hs, ?_, hfix⟩
  intro X
  set τG : GL (Fin n) Ω →* GL (Fin n) Ω :=
    invTransposeHom.comp (Matrix.GeneralLinearGroup.map σ) with hτGdef
  have hτG : ∀ Y : GL (Fin n) Ω, (τG Y : Matrix (Fin n) (Fin n) Ω) =
      (((Y : Matrix (Fin n) (Fin n) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ := by
    intro Y
    rw [hτGdef, MonoidHom.comp_apply, coe_invTransposeHom, Matrix.coe_units_inv,
      coe_generalLinearGroup_map, hσ]
  have hdGL : H⁻¹ * (A * τG (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * A⁻¹) * H =
      τG (Matrix.SpecialLinearGroup.toGL X) := by
    apply Units.ext
    simp only [Units.val_mul, hτG]
    exact hdescent (Matrix.SpecialLinearGroup.toGL X) X.2
  have hmain : A * τG (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * A⁻¹ =
      H * τG (Matrix.SpecialLinearGroup.toGL X) * H⁻¹ := by
    rw [← hdGL]; group
  have harg : ((Hs * X * Hs⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (H : Matrix (Fin n) (Fin n) Ω) * (X : Matrix (Fin n) (Fin n) Ω) *
        (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) := by
    have hHs_inv : ((Hs⁻¹ : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
        (↑H⁻¹ : Matrix (Fin n) (Fin n) Ω) :=
      congrArg (fun Z : GL (Fin n) Ω => (Z : Matrix (Fin n) (Fin n) Ω))
        (show Matrix.SpecialLinearGroup.toGL (Hs⁻¹) = H⁻¹ by rw [map_inv, hHs])
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hHs_inv]
  have hΦGL : Matrix.SpecialLinearGroup.toGL (Φ (Hs * X * Hs⁻¹)) =
      A * τG (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * A⁻¹ := by
    apply Units.ext
    change ((Φ (Hs * X * Hs⁻¹) : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      ((A * τG (H * Matrix.SpecialLinearGroup.toGL X * H⁻¹) * A⁻¹ : GL (Fin n) Ω) :
        Matrix (Fin n) (Fin n) Ω)
    rw [hA' (Hs * X * Hs⁻¹)]
    simp only [Units.val_mul, hτG]
    rw [harg]
    rfl
  rw [hΦGL, hmain]
  simp only [hHs, hτGdef, MonoidHom.comp_apply]

theorem unitary_full_intertwining_diagonal_algClosed {f : ℕ} {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] {n : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) (σ : Ω →+* Ω)
    (hσc : ∀ c, σ c = c ^ 2 ^ f) (Φ : SL(n, Ω) ≃* SL(n, Ω))
    (b : Fin n → Fin n → Ωˣ)
    (hΦ : ∀ (i j : Fin n) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω) = 1 + single j i ((b i j : Ω) * t ^ 2 ^ f)) :
    ∃ H : SL(n, Ω),
      (∀ i j : Fin n, i ≠ j → (H : Matrix (Fin n) (Fin n) Ω) i j = 0) ∧
      (∀ X : SL(n, Ω),
        Matrix.SpecialLinearGroup.toGL (Φ (H * X * H⁻¹)) =
          Matrix.SpecialLinearGroup.toGL H *
            invTransposeHom (Matrix.GeneralLinearGroup.map σ
              (Matrix.SpecialLinearGroup.toGL X)) *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
      (∀ X : SL(n, Ω), X ∈ fixSubgroup Φ ↔
        ∃ Y ∈ unitarySet (Ω := Ω) (2 ^ f) n,
          Matrix.SpecialLinearGroup.toGL X =
            Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hq : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  obtain ⟨d, hd⟩ := exists_diag_conj_map_inv_transpose_of_root_hom hn σ Φ.toMonoidHom b
    (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσc])
  obtain ⟨H, c, hHdet, hHoff, hDrel⟩ :=
    exists_diag_conj_invTransposeHom_of_diagonal (q := 2 ^ f) hq hn1 σ hσc
      (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d) d
      (by rw [CFSG.SectionRank.OddCover.coe_diagHom])
  let Hs : SL(n, Ω) := ⟨H, hHdet⟩
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  set τG : GL (Fin n) Ω →* GL (Fin n) Ω :=
    invTransposeHom.comp (Matrix.GeneralLinearGroup.map σ) with hτGdef
  have hτG : ∀ Y : GL (Fin n) Ω, (τG Y : Matrix (Fin n) (Fin n) Ω) =
      (((Y : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ := by
    intro Y
    rw [hτGdef, MonoidHom.comp_apply, coe_invTransposeHom, Matrix.GeneralLinearGroup.coe_inv,
      coe_generalLinearGroup_map]
  have hΦGL : ∀ X : SL(n, Ω), Matrix.SpecialLinearGroup.toGL (Φ X) =
      (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d) *
        τG (Matrix.SpecialLinearGroup.toGL X) *
        (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d)⁻¹ := by
    intro X
    apply Units.ext
    simpa only [MulEquiv.coe_toMonoidHom, Units.val_mul, hτG,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hd X
  have hmainGL : ∀ Y : GL (Fin n) Ω,
      (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d) * τG (H * Y * H⁻¹) *
          (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d)⁻¹ =
        H * τG Y * H⁻¹ := by
    intro Y
    have hτmul : τG (H * Y * H⁻¹) =
        invTransposeHom (Matrix.GeneralLinearGroup.map σ H) * τG Y *
          (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹ := by
      rw [hτGdef]
      simp only [MonoidHom.comp_apply, map_mul, map_inv]
    have hsinv : ∀ Z : GL (Fin n) Ω,
        Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * Z *
          (Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹)⁻¹ = Z := by
      intro Z
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      group
    rw [hDrel, hτmul]
    calc
      Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * H *
          (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹ *
          (invTransposeHom (Matrix.GeneralLinearGroup.map σ H) * τG Y *
            (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * H *
            (invTransposeHom (Matrix.GeneralLinearGroup.map σ H))⁻¹)⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * (H * τG Y * H⁻¹) *
              (Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹)⁻¹ := by
            group
      _ = H * τG Y * H⁻¹ := hsinv _
  refine ⟨Hs, hHoff, ?_, ?_⟩
  · intro X
    have harg : Matrix.SpecialLinearGroup.toGL (Hs * X * Hs⁻¹) =
        H * Matrix.SpecialLinearGroup.toGL X * H⁻¹ := by
      rw [map_mul, map_mul, map_inv, hHs]
    have hτX : τG (Matrix.SpecialLinearGroup.toGL X) =
        invTransposeHom (Matrix.GeneralLinearGroup.map σ
          (Matrix.SpecialLinearGroup.toGL X)) := by
      rw [hτGdef]
      rfl
    rw [hΦGL (Hs * X * Hs⁻¹), harg, hmainGL (Matrix.SpecialLinearGroup.toGL X), hHs, hτX]
  · intro X
    rw [mem_fixSubgroup]
    constructor
    · intro hX
      have hXfix : (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d) *
          τG (Matrix.SpecialLinearGroup.toGL X) *
          (CFSG.SectionRank.OddCover.diagHom (K := Ω) n d)⁻¹ =
          Matrix.SpecialLinearGroup.toGL X := by
        rw [← hΦGL X, hX]
      refine ⟨H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H, ?_, by rw [hHs]; group⟩
      have hYdet : ((H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H : GL (Fin n) Ω) :
          Matrix (Fin n) (Fin n) Ω).det = 1 := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix, X.2, mul_one,
          ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
      have hYfix : τG (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H) =
          H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H := by
        have h1 := hmainGL (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H)
        have hargY : H * (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H) * H⁻¹ =
            Matrix.SpecialLinearGroup.toGL X := by group
        rw [hargY, hXfix] at h1
        have h2 : H * τG (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H) * H⁻¹ =
            H * (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H) * H⁻¹ := by
          rw [← h1, hargY]
        exact mul_left_cancel (mul_right_cancel h2)
      have hYgl : invTransposeHom (Matrix.GeneralLinearGroup.map σ
            (H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H)) =
          H⁻¹ * Matrix.SpecialLinearGroup.toGL X * H := by
        rw [hτGdef] at hYfix
        exact hYfix
      exact (invTransposeHom_map_eq_iff_mem_unitarySet σ hσc hYdet).mp hYgl
    · rintro ⟨Y, hYU, hXY⟩
      rw [hHs] at hXY
      apply Matrix.SpecialLinearGroup.toGL_injective
      have hYdet : (Y : Matrix (Fin n) (Fin n) Ω).det = 1 := hYU.2.1
      have hYfix : invTransposeHom (Matrix.GeneralLinearGroup.map σ Y) = Y :=
        (invTransposeHom_map_eq_iff_mem_unitarySet σ hσc hYdet).mpr hYU
      have hτY : τG Y = Y := by
        rw [hτGdef]
        exact hYfix
      rw [hΦGL X]
      have hmainY := hmainGL Y
      rw [← hXY, hτY] at hmainY
      rw [hmainY]
      exact hXY.symm

section SplitKappa

variable {Ω k : Type} [Field Ω] [Field k] [Algebra k Ω]

variable (ρ : SL(3, Ω) →* ModGL Tag.F4 Ω) (H : SL(3, Ω))

def kappaSL : SL(3, k) →* ModGL Tag.F4 Ω :=
  ρ.comp ((MulAut.conj H).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k Ω)))

@[simp]
theorem kappaSL_apply (X : SL(3, k)) :
    kappaSL (k := k) ρ H X =
      ρ (H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) X * H⁻¹) :=
  rfl

theorem kappaSL_injective (hρinj : Function.Injective ρ) :
    Function.Injective (kappaSL (k := k) ρ H) := by
  intro X Y h
  have h1 : H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) X * H⁻¹ =
      H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹ := hρinj h
  have h2 : Matrix.SpecialLinearGroup.map (algebraMap k Ω) X =
      Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y := (MulAut.conj H).injective h1
  exact specialLinearGroup_map_injective (algebraMap k Ω).injective h2

theorem kappaSL_range (Ψ : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) (Φ' : SL(3, Ω) ≃* SL(3, Ω))
    (hρinj : Function.Injective ρ) (hΦ' : ∀ X, Ψ (ρ X) = ρ (Φ' X))
    (hfix : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ' ↔ ∃ Y : SL(3, k),
      X = H * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H⁻¹) :
    (kappaSL (k := k) ρ H).range = ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) := by
  rw [kappaSL, MonoidHom.range_comp, MonoidHom.range_comp]
  have hmap : ((Matrix.SpecialLinearGroup.map (algebraMap k Ω)).range.map
      (MulAut.conj H).toMonoidHom) = fixSubgroup Φ' := by
    ext X
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      obtain ⟨Z, hZ⟩ := hY
      exact (hfix (H * Y * H⁻¹)).2 ⟨Z, by rw [← hZ]⟩
    · intro hX
      obtain ⟨Y, hYX⟩ := (hfix X).1 hX
      exact ⟨Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y, ⟨Y, rfl⟩, hYX.symm⟩
  rw [hmap]
  exact (IsSLFrame.range_inf_eqLocus_eq_map hρinj Ψ Φ' hΦ').symm

theorem kappaSL_pair
    {r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hgen : ∀ (i j : Fin 3) (hij : i ≠ j), ∃ ε : Ωˣ, ∀ t : Ω,
      ρ (Matrix.SpecialLinearGroup.transvection hij t) =
        pinnedX Tag.F4 Ω (r i j) ((ε : Ω) * t)) :
    (∃ ε02 : Ωˣ, ∀ t : k,
        kappaSL (k := k) ρ H (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠
            2 by decide) t) =
          ρ H * pinnedX Tag.F4 Ω (r 0 2) ((ε02 : Ω) * algebraMap k Ω t) * (ρ H)⁻¹) ∧
      (∃ ε20 : Ωˣ, ∀ t : k,
        kappaSL (k := k) ρ H (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠
            0 by decide) t) =
          ρ H * pinnedX Tag.F4 Ω (r 2 0) ((ε20 : Ω) * algebraMap k Ω t) * (ρ H)⁻¹) := by
  constructor
  · obtain ⟨ε, hε⟩ := hgen 0 2 (by decide)
    refine ⟨ε, fun t => ?_⟩
    simp only [kappaSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, Matrix.SpecialLinearGroup.map_transvection, hε]
  · obtain ⟨ε, hε⟩ := hgen 2 0 (by decide)
    refine ⟨ε, fun t => ?_⟩
    simp only [kappaSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, Matrix.SpecialLinearGroup.map_transvection, hε]

end SplitKappa

section UnitaryKappa

variable {Ω : Type} [Field Ω]

variable (ρ : SL(3, Ω) →* ModGL τ Ω) (H : SL(3, Ω))

def kappaSU (F : Subfield Ω) (ℓ f : ℕ) : StatedSU 3 (ℓ ^ f) F →* ModGL τ Ω :=
  ρ.comp ((MulAut.conj H).toMonoidHom.comp (statedSUToSL F 3 (ℓ ^ f)))

@[simp]
theorem kappaSU_apply (F : Subfield Ω) (ℓ f : ℕ) (Y : StatedSU 3 (ℓ ^ f) F) :
    kappaSU ρ H F ℓ f Y = ρ (H * statedSUToSL F 3 (ℓ ^ f) Y * H⁻¹) :=
  rfl

theorem kappaSU_injective (F : Subfield Ω) (ℓ f : ℕ) (hρinj : Function.Injective ρ) :
    Function.Injective (kappaSU ρ H F ℓ f) :=
  hρinj.comp ((MulAut.conj H).injective.comp (statedSUToSL_injective F 3 (ℓ ^ f)))

theorem kappaSU_range (F : Subfield Ω) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) (hFcard : Nat.card F = (ℓ ^ f) ^ 2)
    (hρinj : Function.Injective ρ) (Ψ : ModGL τ Ω →* ModGL τ Ω)
    (Φ' : SL(3, Ω) ≃* SL(3, Ω)) (hΦ' : ∀ X, Ψ (ρ X) = ρ (Φ' X))
    (hfix : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
        (Matrix.SpecialLinearGroup.toGL H)⁻¹) :
    (kappaSU ρ H F ℓ f).range = ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) := by
  rw [kappaSU, MonoidHom.range_comp, MonoidHom.range_comp]
  have hmap : ((statedSUToSL F 3 (ℓ ^ f)).range.map (MulAut.conj H).toMonoidHom) =
      fixSubgroup Φ' := by
    ext X
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      have hY' : Matrix.SpecialLinearGroup.toGL Y ∈ unitarySet (ℓ ^ f) 3 :=
        (mem_range_statedSUToSL_iff hℓ F hF hFcard (by norm_num) Y).mp hY
      exact (hfix (H * Y * H⁻¹)).2 ⟨_, hY', by rw [map_mul, map_mul, map_inv]⟩
    · intro hX
      obtain ⟨Ygl, hYgl, hXY⟩ := (hfix X).1 hX
      let Ysl : SL(3, Ω) := ⟨Ygl, hYgl.2.1⟩
      have hYsl : Ysl ∈ (statedSUToSL F 3 (ℓ ^ f)).range :=
        (mem_range_statedSUToSL_iff hℓ F hF hFcard (by norm_num) Ysl).mpr (by
          change Ygl ∈ unitarySet (ℓ ^ f) 3
          exact hYgl)
      refine ⟨Ysl, hYsl, ?_⟩
      apply Matrix.SpecialLinearGroup.toGL_injective
      change Matrix.SpecialLinearGroup.toGL (H * Ysl * H⁻¹) = Matrix.SpecialLinearGroup.toGL X
      rw [map_mul, map_mul, map_inv, hXY]
      rw [show Matrix.SpecialLinearGroup.toGL Ysl = Ygl from Units.ext rfl]
  rw [hmap]
  exact (IsSLFrame.range_inf_eqLocus_eq_map hρinj Ψ Φ' hΦ').symm

end UnitaryKappa

end CFSG.StandardType.F4ExplicitPos.RationalA2
end

end
