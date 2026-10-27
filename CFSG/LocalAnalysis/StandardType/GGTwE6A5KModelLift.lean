module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModelTheta
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KNormSU
import CFSG.RankThree.Classical2.SLnConjLemmas
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Assembly CFSG.RankThree.Classical2 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix MatrixGroups

private theorem mem_fixSubgroup_stdUnitary_iff {Ω : Type} [Field Ω] {q : ℕ} {σQ : Ω ≃+* Ω}
    (hσQ : ∀ c, σQ c = c ^ q) (Y : SL(6, Ω)) :
    Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ) ↔
      ((Y : Matrix (Fin 6) (Fin 6) Ω).map (· ^ q))ᵀ * (Y : Matrix (Fin 6) (Fin 6) Ω) = 1 := by
  have hmap : (Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom =
      (Y : Matrix (Fin 6) (Fin 6) Ω).map (· ^ q) := by
    ext i j
    simp [hσQ]
  have hdet : IsUnit ((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Y.2, map_one]
    exact isUnit_one
  rw [mem_fixSubgroup, stdUnitaryEquiv_apply, ← hmap]
  constructor
  · intro h
    have h1 : (((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)⁻¹)ᵀ =
        (Y : Matrix (Fin 6) (Fin 6) Ω) := by
      rw [← coe_stdUnitary, h]
    calc ((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)ᵀ * (Y : Matrix (Fin 6) (Fin 6) Ω)
        = ((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)ᵀ *
            (((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)⁻¹)ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  · intro h
    apply Subtype.ext
    rw [coe_stdUnitary]
    have hinv : ((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)⁻¹ =
        (Y : Matrix (Fin 6) (Fin 6) Ω)ᵀ := by
      apply Matrix.inv_eq_left_inv
      rw [← Matrix.transpose_transpose ((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom),
        ← Matrix.transpose_mul, h, Matrix.transpose_one]
    rw [hinv, Matrix.transpose_transpose]

private theorem center_le_fixSubgroup_stdUnitary {Ω : Type} [Field Ω] [CharP Ω 2] {n : ℕ}
    (h3 : 3 ∣ 2 ^ n + 1) {σQ : Ω ≃+* Ω} (hσQ : ∀ c, σQ c = c ^ 2 ^ n) {k : SL(6, Ω)}
    (hk : k ∈ Subgroup.center SL(6, Ω)) : k ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ) := by
  obtain ⟨r, hr6, hrk⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hk
  have hr6' : r ^ 6 = 1 := by simpa using hr6
  have hr3 : r ^ 3 = 1 := by
    have h0 : (r ^ 3 - 1) ^ 2 = 0 := by
      linear_combination hr6' - (r ^ 3 - 1) * (CharTwo.two_eq_zero : (2 : Ω) = 0)
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  obtain ⟨m, hm⟩ := h3
  have hrq : r ^ 2 ^ n * r = 1 := by rw [← pow_succ, hm, pow_mul, hr3, one_pow]
  rw [mem_fixSubgroup_stdUnitary_iff hσQ, ← hrk, Matrix.scalar_apply,
    Matrix.diagonal_map (f := fun x : Ω => x ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero)),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  simp only [hrq]
  exact Matrix.diagonal_one

theorem exists_gu_lift {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] {n : ℕ}
    (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {σQ : Ω ≃+* Ω} (hσQ : ∀ c, σQ c = c ^ 2 ^ n)
    {G : Type} [Group G] {ψ : SL(6, Ω) →* G} (hker : ψ.ker ≤ Subgroup.center SL(6, Ω)) {z : G}
    {L' : Type} [Group L'] {J : Subgroup L'} {ι : L' →* G} (hι : Function.Injective ι)
    (hJ : ∀ g : G, g ∈ J.map ι ↔
      ∃ Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ), g = z * ψ Y * z⁻¹)
    {F : Subfield Ω} (hF : ∀ c, c ∈ F ↔ c ^ (2 ^ n) ^ 2 = c) {Φ : StatedSU 6 (2 ^ n) F →* J}
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n))}
    (hΦ : ∀ s, ι (Φ s) = z * ψ (statedSUToSL F 6 (2 ^ n) s) * z⁻¹)
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n)) s)
    {a : MulAut L'} (hJa : J.map a.toMonoidHom = J) {x : G} {M : GL (Fin 6) Ω}
    (hM : ∀ Y, ψ (conjSLn M Y) = z⁻¹ * (x * (z * ψ Y * z⁻¹) * x⁻¹) * z)
    (hx : ∀ l ∈ J, ι (a l) = x * ι l * x⁻¹) :
    ∃ A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n), ∃ u : Ωˣ,
      Matrix.GeneralLinearGroup.map F.subtype A = M * Matrix.GeneralLinearGroup.scalar (Fin 6) u ∧
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n))) {A},
        LargeEvenInduces θ (fun l l' : ↥J => (l' : L') = a l) φ := by
  classical
  have hMfix : ∀ Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ),
      conjSLn M Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ) := by
    intro Y hY
    obtain ⟨l, hl, hlY⟩ := (hJ _).2 ⟨Y, hY, rfl⟩
    have hal : a l ∈ J := by
      rw [← hJa]
      exact Subgroup.mem_map_of_mem a.toMonoidHom hl
    obtain ⟨Y₂, hY₂, hY₂e⟩ := (hJ _).1 (Subgroup.mem_map_of_mem ι hal)
    have hψ2 : ψ (conjSLn M Y) = ψ Y₂ := by
      rw [hM, ← hlY, ← hx l hl, hY₂e]
      group
    have hk : conjSLn M Y * Y₂⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψ2, mul_inv_cancel]
    have := Subgroup.mul_mem _ (center_le_fixSubgroup_stdUnitary h3 hσQ (hker hk)) hY₂
    rwa [inv_mul_cancel_right] at this
  have hSU : ∀ g ∈ StatedSU 6 (2 ^ n) Ω, M * g * M⁻¹ ∈ StatedSU 6 (2 ^ n) Ω := by
    have hle : StatedSU 6 (2 ^ n) Ω ≤ (StatedSU 6 (2 ^ n) Ω).comap (MulAut.conj M).toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro A ⟨hA1, hA2⟩
      let A' : SL(6, Ω) := ⟨(A : Matrix (Fin 6) (Fin 6) Ω), hA1⟩
      have hY := hMfix A' ((mem_fixSubgroup_stdUnitary_iff hσQ A').2 hA2)
      have hmat : ((M * A * M⁻¹ : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) =
          ((conjSLn M A' : SL(6, Ω)) : Matrix (Fin 6) (Fin 6) Ω) := by
        rw [coe_conjSLn, Units.val_mul, Units.val_mul]
      show M * A * M⁻¹ ∈ StatedSU 6 (2 ^ n) Ω
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [hmat]
        exact (conjSLn M A').2
      · rw [hmat]
        exact (mem_fixSubgroup_stdUnitary_iff hσQ _).1 hY
    exact fun g hg => hle hg
  obtain ⟨c, μ, hc0, hμ0, hμq, hcM, hcU⟩ :=
    exists_smul_unitary_of_normalizes_statedSU (ν := 6) (by norm_num) hn hSU
  have hent : ∀ i j, (c • (M : Matrix (Fin 6) (Fin 6) Ω)) i j ∈ F := fun i j => by
    rw [hF]
    have := congrFun (congrFun hcM i) j
    rwa [Matrix.map_apply] at this
  let A₀ : Matrix (Fin 6) (Fin 6) F := Matrix.of fun i j => ⟨_, hent i j⟩
  have hA₀ : A₀.map F.subtype = c • (M : Matrix (Fin 6) (Fin 6) Ω) := by
    ext i j
    rfl
  have hMdet : (M : Matrix (Fin 6) (Fin 6) Ω).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hdet : A₀.det ≠ 0 := by
    intro h0
    have h1 : F.subtype A₀.det = 0 := by rw [h0, map_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA₀, Matrix.det_smul, Fintype.card_fin] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact hc0 ((pow_eq_zero_iff (by norm_num)).1 h)
    · exact hMdet h
  let A : GL (Fin 6) F := Matrix.GeneralLinearGroup.mkOfDetNeZero A₀ hdet
  have hAmap : Matrix.GeneralLinearGroup.map F.subtype A =
      M * Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
      ← (Matrix.scalar_commute c (fun _ => mul_comm _ _) _).eq, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, ← hA₀]
    rfl
  have hμF : μ ∈ F := (hF μ).2 (by rw [sq, pow_mul, hμq, hμq])
  have hAGU : A ∈ LargeEvenGUSet (Fin 6) F (2 ^ n) := by
    refine ⟨⟨μ, hμF⟩, fun h => hμ0 (by simpa using congrArg Subtype.val h),
      Subtype.ext (by simpa using hμq), ?_⟩
    apply Matrix.map_injective F.subtype.injective
    have hpow : (A₀.map (· ^ 2 ^ n)).map F.subtype = (A₀.map F.subtype).map (· ^ 2 ^ n) := by
      ext i j
      exact map_pow F.subtype _ _
    change ((A₀.map (· ^ 2 ^ n))ᵀ * A₀).map F.subtype =
      ((⟨μ, hμF⟩ : F) • (1 : Matrix (Fin 6) (Fin 6) F)).map F.subtype
    rw [Matrix.map_mul, Matrix.transpose_map, hpow, hA₀, hcU]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let aJ : J ≃* J := (J.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hJa)
  have haJ : ∀ l, ((aJ l : J) : L') = a l := fun _ => rfl
  let ā : ↥J ⧸ Subgroup.center ↥J ≃* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.congr _ _ aJ (Subgroup.map_center_eq aJ)
  have hkey : ∀ s s' : StatedSU 6 (2 ^ n) F, (s' : GL (Fin 6) F) = A * s * A⁻¹ →
      aJ (Φ s) = Φ s' := by
    intro s s' hss'
    have hst : statedSUToSL F 6 (2 ^ n) s' = conjSLn M (statedSUToSL F 6 (2 ^ n) s) := by
      rw [← conjSLn_mul_scalar M (Units.mk0 c hc0), ← hAmap]
      apply Subtype.ext
      rw [coe_statedSUToSL, coe_conjSLn, coe_statedSUToSL, hss', ← map_inv, Units.val_mul,
        Units.val_mul, Matrix.map_mul, Matrix.map_mul]
      rfl
    apply Subtype.ext
    apply hι
    rw [haJ, hx _ (Φ s).2, hΦ, hΦ, hst, hM]
    group
  refine ⟨A, hAGU, Units.mk0 c hc0, hAmap, θ.symm.trans (ā.trans θ),
    ⟨A, Set.mem_singleton A, fun s s' hss' => ?_⟩, fun l l' hll' => ?_⟩
  · have h1 : θ.symm (LargeEvenProjMk _ s) = QuotientGroup.mk (Φ s) := by
      rw [← hθ s, MulEquiv.symm_apply_apply]
    show θ (ā (θ.symm (LargeEvenProjMk _ s))) = LargeEvenProjMk _ s'
    rw [h1, ← hθ s', ← hkey s s' hss']
    rfl
  · have hl : aJ l = l' := Subtype.ext ((haJ l).trans hll'.symm)
    show θ (ā (θ.symm (θ (QuotientGroup.mk l)))) = θ (QuotientGroup.mk l')
    rw [MulEquiv.symm_apply_apply, ← hl]
    rfl

private theorem exists_gu_lifts_of_frame_matrices {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharP Ω 2] {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {σQ : Ω ≃+* Ω}
    (hσQ : ∀ c, σQ c = c ^ 2 ^ n) {G : Type} [Group G] {ψ : SL(6, Ω) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(6, Ω)) {z : G}
    {W : GL (Fin 6) Ω} (hW : ∀ X, z * ψ X * z⁻¹ = ψ (conjSLn W X)) {L' : Type} [Group L']
    {J : Subgroup L'} {ι : L' →* G} (hι : Function.Injective ι)
    (hJ : ∀ g : G, g ∈ J.map ι ↔
      ∃ Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ), g = z * ψ Y * z⁻¹)
    {F : Subfield Ω} (hF : ∀ c, c ∈ F ↔ c ^ (2 ^ n) ^ 2 = c) {Φ : StatedSU 6 (2 ^ n) F →* J}
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n))}
    (hΦ : ∀ s, ι (Φ s) = z * ψ (statedSUToSL F 6 (2 ^ n) s) * z⁻¹)
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n)) s)
    {a₁ a₂ : MulAut L'} (hJ₁ : J.map a₁.toMonoidHom = J) (hJ₂ : J.map a₂.toMonoidHom = J)
    {x₁ x₂ : G} {B₁ B₂ : GL (Fin 6) Ω}
    (hB₁ : ∀ Y, x₁ * ψ Y * x₁⁻¹ = ψ (conjSLn B₁ Y))
    (hB₂ : ∀ Y, x₂ * ψ Y * x₂⁻¹ = ψ (conjSLn B₂ Y))
    (hx₁ : ∀ l ∈ J, ι (a₁ l) = x₁ * ι l * x₁⁻¹)
    (hx₂ : ∀ l ∈ J, ι (a₂ l) = x₂ * ι l * x₂⁻¹) :
    ∃ A₁ ∈ LargeEvenGUSet (Fin 6) F (2 ^ n), ∃ A₂ ∈ LargeEvenGUSet (Fin 6) F (2 ^ n),
      ∃ u₁ u₂ : Ωˣ,
        Matrix.GeneralLinearGroup.map F.subtype A₁ =
          (W⁻¹ * B₁ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₁ ∧
        Matrix.GeneralLinearGroup.map F.subtype A₂ =
          (W⁻¹ * B₂ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₂ ∧
        (∃ φ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n))) {A₁},
          LargeEvenInduces θ (fun l l' : ↥J => (l' : L') = a₁ l) φ) ∧
        ∃ φ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n))) {A₂},
          LargeEvenInduces θ (fun l l' : ↥J => (l' : L') = a₂ l) φ := by
  classical
  have hWi : ∀ X, z⁻¹ * ψ X * z = ψ (conjSLn W⁻¹ X) := fun X => by
    have h1 := hW (conjSLn W⁻¹ X)
    rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one] at h1
    rw [← h1]
    group
  have hM : ∀ {x : G} {B : GL (Fin 6) Ω}, (∀ Y, x * ψ Y * x⁻¹ = ψ (conjSLn B Y)) →
      ∀ Y, ψ (conjSLn (W⁻¹ * B * W) Y) = z⁻¹ * (x * (z * ψ Y * z⁻¹) * x⁻¹) * z := by
    intro x B hB Y
    rw [conjSLn_mul, conjSLn_mul, ← hWi, ← hB, ← hW]
  obtain ⟨A₁, hA₁, u₁, hu₁, hφ₁⟩ :=
    exists_gu_lift hn h3 hσQ hker hι hJ hF hΦ hθ hJ₁ (hM hB₁) hx₁
  obtain ⟨A₂, hA₂, u₂, hu₂, hφ₂⟩ :=
    exists_gu_lift hn h3 hσQ hker hι hJ hF hΦ hθ hJ₂ (hM hB₂) hx₂
  exact ⟨A₁, hA₁, A₂, hA₂, u₁, u₂, hu₁, hu₂, hφ₁, hφ₂⟩

private theorem frame_matrices_commute_of_gu_lifts {Ω : Type} [Field Ω] {F : Subfield Ω}
    {A₁ A₂ : GL (Fin 6) F} {W B₁ B₂ : GL (Fin 6) Ω} {u₁ u₂ : Ωˣ}
    (h₁ : Matrix.GeneralLinearGroup.map F.subtype A₁ =
      (W⁻¹ * B₁ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₁)
    (h₂ : Matrix.GeneralLinearGroup.map F.subtype A₂ =
      (W⁻¹ * B₂ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₂)
    (hc : A₁ * A₂ = A₂ * A₁) : B₁ * B₂ = B₂ * B₁ := by
  have hc' := congrArg (Matrix.GeneralLinearGroup.map F.subtype) hc
  rw [map_mul, map_mul, h₁, h₂] at hc'
  have hsc : ∀ (u : Ωˣ) (P : GL (Fin 6) Ω),
      Matrix.GeneralLinearGroup.scalar (Fin 6) u * P =
        P * Matrix.GeneralLinearGroup.scalar (Fin 6) u := fun u P => Units.ext (by
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute u.1 (fun _ => mul_comm _ _) _).eq)
  have e : ∀ (P Q : GL (Fin 6) Ω) (u v : Ωˣ),
      P * Matrix.GeneralLinearGroup.scalar (Fin 6) u *
          (Q * Matrix.GeneralLinearGroup.scalar (Fin 6) v) =
        P * Q * (Matrix.GeneralLinearGroup.scalar (Fin 6) u *
          Matrix.GeneralLinearGroup.scalar (Fin 6) v) := fun P Q u v => by
    rw [mul_assoc P, ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 6) u) Q, hsc u Q,
      mul_assoc Q, ← mul_assoc P]
  rw [e, e, hsc u₂ (Matrix.GeneralLinearGroup.scalar (Fin 6) u₁)] at hc'
  have h12 := mul_right_cancel hc'
  have e2 : ∀ P Q : GL (Fin 6) Ω,
      W⁻¹ * P * W * (W⁻¹ * Q * W) = W⁻¹ * (P * Q) * W := fun P Q => by group
  rw [e2, e2] at h12
  exact mul_left_cancel (mul_right_cancel h12)

theorem frame_matrices_commute_of_commLifts {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {σQ : Ω ≃+* Ω} (hσQ : ∀ c, σQ c = c ^ 2 ^ n)
    {G : Type} [Group G] {ψ : SL(6, Ω) →* G} (hker : ψ.ker ≤ Subgroup.center SL(6, Ω)) {z : G}
    {W : GL (Fin 6) Ω} (hW : ∀ X, z * ψ X * z⁻¹ = ψ (conjSLn W X)) {L' : Type} [Group L']
    {J : Subgroup L'} {ι : L' →* G} (hι : Function.Injective ι)
    (hJ : ∀ g : G, g ∈ J.map ι ↔
      ∃ Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ), g = z * ψ Y * z⁻¹)
    {S : Set (MulAut L')} (hCL : CFSG.StandardType.GGUnitaryCommLifts J n 6 S)
    {a₁ a₂ : MulAut L'} (ha₁ : a₁ ∈ S) (ha₂ : a₂ ∈ S) (hJ₁ : J.map a₁.toMonoidHom = J)
    (hJ₂ : J.map a₂.toMonoidHom = J) {x₁ x₂ : G} {B₁ B₂ : GL (Fin 6) Ω}
    (hB₁ : ∀ Y, x₁ * ψ Y * x₁⁻¹ = ψ (conjSLn B₁ Y)) (hB₂ : ∀ Y, x₂ * ψ Y * x₂⁻¹ = ψ (conjSLn B₂ Y))
    (hx₁ : ∀ l ∈ J, ι (a₁ l) = x₁ * ι l * x₁⁻¹) (hx₂ : ∀ l ∈ J, ι (a₂ l) = x₂ * ι l * x₂⁻¹) :
    B₁ * B₂ = B₂ * B₁ := by
  classical
  obtain ⟨F, hFcard, hF, Φ, θ, hΦ, hθ, -, -⟩ := exists_psu_equiv_of_conj_frame Nat.prime_two hn
    hσQ (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num)) hker z hι hJ
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hFcard]; positivity)
  have hJa : ∀ {a : MulAut L'}, J.map a.toMonoidHom = J → ∀ l ∈ J, a l ∈ J := fun h l hl =>
    h ▸ Subgroup.mem_map_of_mem _ hl
  obtain ⟨A₁, hA₁, A₂, hA₂, u₁, u₂, hu₁, hu₂, hφ₁, hφ₂⟩ :=
    exists_gu_lifts_of_frame_matrices hn h3 hσQ hker hW hι hJ hF hΦ hθ hJ₁ hJ₂ hB₁ hB₂ hx₁ hx₂
  have hc := hCL F hFcard θ a₁ ha₁ a₂ ha₂ (hJa hJ₁) (hJa hJ₂) A₁ hA₁ A₂ hA₂ hφ₁ hφ₂
  exact frame_matrices_commute_of_gu_lifts hu₁ hu₂ hc

theorem exists_noncommuting_gu_lifts_of_frame_matrices {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [CharP Ω 2] {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {σQ : Ω ≃+* Ω}
    (hσQ : ∀ c, σQ c = c ^ 2 ^ n) {G : Type} [Group G] {ψ : SL(6, Ω) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(6, Ω)) {z : G}
    {W : GL (Fin 6) Ω} (hW : ∀ X, z * ψ X * z⁻¹ = ψ (conjSLn W X)) {L' : Type} [Group L']
    {J : Subgroup L'} {ι : L' →* G} (hι : Function.Injective ι)
    (hJ : ∀ g : G, g ∈ J.map ι ↔
      ∃ Y ∈ fixSubgroup (stdUnitaryEquiv (ν := 6) σQ), g = z * ψ Y * z⁻¹)
    {F : Subfield Ω} (hF : ∀ c, c ∈ F ↔ c ^ (2 ^ n) ^ 2 = c) {Φ : StatedSU 6 (2 ^ n) F →* J}
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) F (2 ^ n))}
    (hΦ : ∀ s, ι (Φ s) = z * ψ (statedSUToSL F 6 (2 ^ n) s) * z⁻¹)
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n)) s)
    {a₁ a₂ : MulAut L'} (hJ₁ : J.map a₁.toMonoidHom = J) (hJ₂ : J.map a₂.toMonoidHom = J)
    {x₁ x₂ : G} {B₁ B₂ : GL (Fin 6) Ω}
    (hB₁ : ∀ Y, x₁ * ψ Y * x₁⁻¹ = ψ (conjSLn B₁ Y))
    (hB₂ : ∀ Y, x₂ * ψ Y * x₂⁻¹ = ψ (conjSLn B₂ Y))
    (hx₁ : ∀ l ∈ J, ι (a₁ l) = x₁ * ι l * x₁⁻¹)
    (hx₂ : ∀ l ∈ J, ι (a₂ l) = x₂ * ι l * x₂⁻¹)
    (hB₁₂ : B₁ * B₂ ≠ B₂ * B₁) :
    ∃ A₁ ∈ LargeEvenGUSet (Fin 6) F (2 ^ n), ∃ A₂ ∈ LargeEvenGUSet (Fin 6) F (2 ^ n),
      ∃ u₁ u₂ : Ωˣ,
        Matrix.GeneralLinearGroup.map F.subtype A₁ =
          (W⁻¹ * B₁ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₁ ∧
        Matrix.GeneralLinearGroup.map F.subtype A₂ =
          (W⁻¹ * B₂ * W) * Matrix.GeneralLinearGroup.scalar (Fin 6) u₂ ∧
        (∃ φ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n))) {A₁},
          LargeEvenInduces θ (fun l l' : ↥J => (l' : L') = a₁ l) φ) ∧
        (∃ φ ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F (2 ^ n))) {A₂},
          LargeEvenInduces θ (fun l l' : ↥J => (l' : L') = a₂ l) φ) ∧
        A₁ * A₂ ≠ A₂ * A₁ := by
  obtain ⟨A₁, hA₁, A₂, hA₂, u₁, u₂, hu₁, hu₂, hφ₁, hφ₂⟩ :=
    exists_gu_lifts_of_frame_matrices hn h3 hσQ hker hW hι hJ hF hΦ hθ hJ₁ hJ₂ hB₁ hB₂ hx₁ hx₂
  refine ⟨A₁, hA₁, A₂, hA₂, u₁, u₂, hu₁, hu₂, hφ₁, hφ₂, ?_⟩
  intro hA
  exact hB₁₂ (frame_matrices_commute_of_gu_lifts hu₁ hu₂ hA)

end CFSG.StandardType.SCFourCover

end
