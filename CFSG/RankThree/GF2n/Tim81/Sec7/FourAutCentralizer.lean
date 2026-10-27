module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairFrame
import CFSG.Timmesfeld.Transvection.ModelSUFour
import CFSG.Timmesfeld.Transvection.ModelSUAutLine
import CFSG.Timmesfeld.Transvection.ModelSUFourAut
import CFSG.Timmesfeld.Bridge.SchurNarrowTransport
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryField
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
  CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryField
open scoped MatrixGroups commutatorElement

private theorem four_lift_field_part {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {K : Type} [Group K]
    {Ψ : SU (unitaryInvolution F 2 f) 4 →* K} (hΨ : Function.Injective Ψ) {y : K}
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1),
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t : SU (unitaryInvolution F 2 f) 4,
        suMat (unitaryInvolution F 2 f) 4 t = uTrans (unitaryInvolution F 2 f) u 1 →
          y * Ψ t = Ψ t * y)
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ y A φ α) :
    ((∀ c, φ c = c) ∨ ∀ c, φ c = unitaryInvolution F 2 f c) ∧
      ∃ l : F, l ≠ 0 ∧ (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 1 1 = l • Pi.single 1 1 ∧
        (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 2 1 = l • Pi.single 2 1 := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hσ : ∀ c, σ (σ c) = c := fun c => unitaryInvolution_involutive hF c
  have hker : Ψ.ker ≤ Subgroup.center (SU σ 4) := by
    rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hΨ]
    exact bot_le
  have hMinj : ∀ v, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v = 0 → v = 0 :=
    fun v hv => Matrix.mulVec_injective_of_isUnit A.isUnit (by rw [hv, Matrix.mulVec_zero])
  have hEig : ∀ u ∈ perpPair σ (Pi.single 0 1) (Pi.single 3 1), uForm σ u u = 0 →
      ∃ μ : F, (A : Matrix (Fin 4) (Fin 4) F) *ᵥ (fun i => φ (u i)) = μ • u := by
    intro u hu huu
    obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ huu (c := 1)
      (by rw [map_one]; exact CharTwo.add_self_eq_zero 1)
    exact hL.exists_smul hker huu ht (hP u hu huu t ht)
  obtain ⟨hfix, l, hl0, h1, h2⟩ :=
    fixed_of_isotropic_eigen_four (σ := σ) (A : Matrix (Fin 4) (Fin 4) F) hMinj φ hEig
  refine ⟨?_, l, hl0, h1, h2⟩
  rcases eq_id_or_eq_conj_of_fix σ hσ φ.toRingHom hfix with h | h
  · exact Or.inl fun c => h c
  · exact Or.inr fun c => h c

private theorem four_lift_centralizer {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {K : Type} [Group K]
    {Ψ : SU (unitaryInvolution F 2 f) 4 →* K} (hΨ : Function.Injective Ψ)
    {s : SU (unitaryInvolution F 2 f) 4}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1) {y : K} (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hys : y * Ψ s = Ψ s * y)
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1),
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t : SU (unitaryInvolution F 2 f) 4,
        suMat (unitaryInvolution F 2 f) 4 t = uTrans (unitaryInvolution F 2 f) u 1 →
          y * Ψ t = Ψ t * y)
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ y A φ α) (hφ : ∀ c, φ c = c) :
    y ∈ Subgroup.centralizer (Ψ.range : Set K) := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hσ : ∀ c, σ (σ c) = c := fun c => unitaryInvolution_involutive hF c
  have hker : Ψ.ker ≤ Subgroup.center (SU σ 4) := by
    rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hΨ]
    exact bot_le
  have haa : uForm σ (Pi.single (0 : Fin 4) 1) (Pi.single 0 1) = 0 :=
    uForm_single_self (by decide)
  have hdd : uForm σ (Pi.single (3 : Fin 4) 1) (Pi.single 3 1) = 0 :=
    uForm_single_self (by decide)
  have had : uForm σ (Pi.single (0 : Fin 4) 1) (Pi.single 3 1) = 1 :=
    uForm_single_zero_last (m := 2)
  exact hL.mem_centralizer_range hF hf le_rfl hφ hker haa hdd had hs hord hy2 hys hP

private theorem four_lift_alpha_comp_self {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {K : Type} [Group K]
    {Ψ : SU (unitaryInvolution F 2 f) 4 →* K} (hΨ : Function.Injective Ψ)
    {s : SU (unitaryInvolution F 2 f) 4}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1) {y : K} (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hys : y * Ψ s = Ψ s * y)
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1),
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t : SU (unitaryInvolution F 2 f) 4,
        suMat (unitaryInvolution F 2 f) 4 t = uTrans (unitaryInvolution F 2 f) u 1 →
          y * Ψ t = Ψ t * y)
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ y A φ α) (hφ : ∀ c, φ c = unitaryInvolution F 2 f c) :
    ∀ g, α (α g) = g := by
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hσ : ∀ c, σ (σ c) = c := fun c => unitaryInvolution_involutive hF c
  have hφ' : ∀ c, (φ.trans φ) c = c := by
    intro c
    change φ (φ c) = c
    rw [hφ (φ c), hφ c, hσ c]
  have hy2' : IsPGroup 2 (Subgroup.zpowers (y * y)) := by
    have h : y * y ∈ Subgroup.zpowers y := by
      simpa [pow_two] using Subgroup.npow_mem_zpowers y 2
    exact hy2.to_le (Subgroup.zpowers_le.2 h)
  have hys' : (y * y) * Ψ s = Ψ s * (y * y) := by
    rw [mul_assoc, hys, ← mul_assoc, hys, mul_assoc]
  have hP' : ∀ u ∈ perpPair σ (Pi.single 0 1) (Pi.single 3 1), uForm σ u u = 0 →
      ∀ t : SU σ 4, suMat σ 4 t = uTrans σ u 1 → (y * y) * Ψ t = Ψ t * (y * y) := by
    intro u hu huu t ht
    rw [mul_assoc, hP u hu huu t ht, ← mul_assoc, hP u hu huu t ht, mul_assoc]
  have hcent : y * y ∈ Subgroup.centralizer (Ψ.range : Set K) :=
    four_lift_centralizer hF hf hΨ hs hord hy2' hys' hP' (hL.comp hL) hφ'
  intro g
  apply hΨ
  have hconj := (hL.comp hL).conj g
  change Ψ (α (α g)) = (y * y) * Ψ g * (y * y)⁻¹ at hconj
  rw [hconj]
  have hcomm : Ψ g * (y * y) = (y * y) * Ψ g :=
    Subgroup.mem_centralizer_iff.mp hcent (Ψ g) (MonoidHom.mem_range.2 ⟨g, rfl⟩)
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem four_lift {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {K : Type} [Group K]
    {Ψ : SU (unitaryInvolution F 2 f) 4 →* K} (hΨ : Function.Injective Ψ)
    {s : SU (unitaryInvolution F 2 f) 4}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1) {y : K} (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hys : y * Ψ s = Ψ s * y)
    (hP : ∀ u ∈ perpPair (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1),
      uForm (unitaryInvolution F 2 f) u u = 0 → ∀ t : SU (unitaryInvolution F 2 f) 4,
        suMat (unitaryInvolution F 2 f) 4 t = uTrans (unitaryInvolution F 2 f) u 1 →
          y * Ψ t = Ψ t * y)
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ y A φ α) :
    ((∀ c, φ c = c) → y ∈ Subgroup.centralizer (Ψ.range : Set K)) ∧
      ((∀ c, φ c = c) ∨ ∀ c, φ c = unitaryInvolution F 2 f c) ∧
      ∀ i : Fin 4, (i = 0 ∨ i = 3) → ∀ (t : SU (unitaryInvolution F 2 f) 4) (c : F),
        c + unitaryInvolution F 2 f c = 0 →
        suMat (unitaryInvolution F 2 f) 4 t = uTrans (unitaryInvolution F 2 f) (Pi.single i 1) c →
          y * Ψ t = Ψ t * y := by
  refine ⟨fun hφ => four_lift_centralizer hF hf hΨ hs hord hy2 hys hP hL hφ,
    (four_lift_field_part hF hΨ hP hL).1, ?_⟩
  obtain ⟨htri, l, -, h1, h2⟩ := four_lift_field_part hF hΨ hP hL
  intro i hi t c hc ht
  rcases htri with hid | hconj
  · have hcent := four_lift_centralizer hF hf hΨ hs hord hy2 hys hP hL hid
    exact (Subgroup.mem_centralizer_iff.mp hcent (Ψ t) (MonoidHom.mem_range.2 ⟨t, rfl⟩)).symm
  · have hαα := four_lift_alpha_comp_self hF hf hΨ hs hord hy2 hys hP hL hconj
    refine hL.commute_of_sigma_four hF hΨ hconj hαα h1 h2 hs ?_ hys hi hc ht
    exact mul_self_ne_one_of_orderOf Ψ (by omega) hord

section FourCentralizer

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
  {K : Type} [Group K] [Finite K] {Ψ : SU (unitaryInvolution F 2 f) 4 →* K}
  {s : SU (unitaryInvolution F 2 f) 4}
  {T₀ T₃ : Subgroup (SU (unitaryInvolution F 2 f) 4)} {Δ : Set (Subgroup K)}

private theorem four_centralizer_lift_trivial (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ)
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    {v : K} (hPv : v ∈ Subgroup.centralizer
      ((perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K) : Set K))
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hysv : v * Ψ s = Ψ s * v)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))))
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ v A φ α) (hφ : ∀ c, φ c = c) : v = 1 := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have hP := SUTrans.commute_of_mem_centralizer_perpRoots hσ
    (fun a ha => exists_add_unitaryInvolution_eq hF ha) (m := 2) (by norm_num) hΔ hT₀ hT₃ hPv
  have hcent := (four_lift hF hf hΨ hs hord hv2 hysv hP hL).1 hφ
  exact CFSG.Timmesfeld.Bridge.eq_one_of_mem_odd_of_mem_two hodd hv2 hcent
    (Subgroup.mem_zpowers _)

private theorem four_centralizer_nontrivial_field (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ)
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    {v : K} (hPv : v ∈ Subgroup.centralizer
      ((perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K) : Set K))
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hysv : v * Ψ s = Ψ s * v)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))))
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Ψ v A φ α) (hv : v ≠ 1) :
    ∀ c, φ c = unitaryInvolution F 2 f c := by
  have hP := SUTrans.commute_of_mem_centralizer_perpRoots (unitaryInvolution_involutive hF)
    (fun a ha => exists_add_unitaryInvolution_eq hF ha) (m := 2) (by norm_num) hΔ hT₀ hT₃ hPv
  obtain ⟨htri, -⟩ := four_lift_field_part hF hΨ hP hL
  rcases htri with hid | hconj
  · exact absurd (four_centralizer_lift_trivial hF hf hΨ hs hord hT₀ hT₃ hΔ hPv hv2 hysv hodd
      hL hid) hv
  · exact hconj

private theorem four_centralizer_sylow_prod_eq_one (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ) (hN : Ψ.range.Normal)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))))
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    (hhs : Ψ s ∈ T₀.map Ψ ⊔ T₃.map Ψ) {Y : Subgroup K}
    (hY : Y = Subgroup.centralizer (((T₀.map Ψ ⊔ T₃.map Ψ ⊔
      perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K)) : Set K))
    (S : Sylow 2 ↥Y) {v w : ↥S} (hv : (v : K) ≠ 1) (hw : (w : K) ≠ 1) :
    (v : ↥Y) * (w : ↥Y) = 1 := by
  classical
  have hker : Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) 4) := by
    rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hΨ]
    exact bot_le
  have hmemY : ∀ x : ↥Y, (x : K) ∈
      Subgroup.centralizer ((T₀.map Ψ ⊔ T₃.map Ψ : Subgroup K) : Set K) ∧
        (x : K) ∈ Subgroup.centralizer
          ((perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K) : Set K) := by
    intro x
    have hx : (x : K) ∈ Subgroup.centralizer
        (((T₀.map Ψ ⊔ T₃.map Ψ ⊔ perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) :
          Subgroup K)) : Set K) := hY ▸ x.2
    exact ⟨Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_left hy) hx,
      Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_right hy) hx⟩
  have hysv : ∀ x : ↥Y, (x : K) * Ψ s = Ψ s * (x : K) := fun x =>
    (Subgroup.mem_centralizer_iff.mp (hmemY x).1 (Ψ s) hhs).symm
  have h2elem : ∀ x : ↥S, IsPGroup 2 (Subgroup.zpowers (x : K)) := by
    intro x
    have h1 : IsPGroup 2 (Subgroup.zpowers (x : ↥Y)) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.2 x.2)
    have h2 := h1.map Y.subtype
    rwa [MonoidHom.map_zpowers] at h2
  have hLift : ∀ x : ↥Y, ∃ (A : GL (Fin 4) F) (φ : F ≃+* F)
      (α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4),
      IsSemilinearLift Ψ (x : K) A φ α := fun x =>
    exists_isSemilinearLift hF (by omega) (n := 4) (by norm_num) (by norm_num) hker hN (x : K)
  choose A_v φ_v α_v hL_v using hLift
  have hvσ := four_centralizer_nontrivial_field hF hf hΨ hs hord hT₀ hT₃ hΔ
    (v := ((v : ↥S) : ↥Y)) (hmemY ((v : ↥S) : ↥Y)).2 (h2elem v) (hysv _) hodd (hL_v _) hv
  have hwσ := four_centralizer_nontrivial_field hF hf hΨ hs hord hT₀ hT₃ hΔ
    (v := ((w : ↥S) : ↥Y)) (hmemY ((w : ↥S) : ↥Y)).2 (h2elem w) (hysv _) hodd (hL_v _) hw
  have hcomp := (hL_v ((v : ↥S) : ↥Y)).comp (hL_v ((w : ↥S) : ↥Y))
  have hid : ∀ c, ((φ_v ((w : ↥S) : ↥Y)).trans (φ_v ((v : ↥S) : ↥Y))) c = c := by
    intro c
    change (φ_v ((v : ↥S) : ↥Y)) ((φ_v ((w : ↥S) : ↥Y)) c) = c
    rw [hwσ c, hvσ (unitaryInvolution F 2 f c), unitaryInvolution_involutive hF c]
  have hysw : ((v : K) * (w : K)) * Ψ s = Ψ s * ((v : K) * (w : K)) := by
    rw [mul_assoc, hysv, ← mul_assoc, hysv, mul_assoc]
  have h2prod : IsPGroup 2 (Subgroup.zpowers ((v : K) * (w : K))) := by
    have h1 : IsPGroup 2 (Subgroup.zpowers ((v * w : ↥S) : ↥Y)) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.2 ((S : Subgroup ↥Y).mul_mem v.2 w.2))
    have h2 := h1.map Y.subtype
    rwa [MonoidHom.map_zpowers] at h2
  have h1 : (v : K) * (w : K) = 1 :=
    four_centralizer_lift_trivial hF hf hΨ hs hord hT₀ hT₃ hΔ
      (v := ((v * w : ↥S) : ↥Y)) (hmemY ((v * w : ↥S) : ↥Y)).2 h2prod hysw hodd hcomp hid
  exact Subtype.ext h1

private theorem four_centralizer_sylow_card (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ) (hN : Ψ.range.Normal)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))))
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    (hhs : Ψ s ∈ T₀.map Ψ ⊔ T₃.map Ψ) {Y : Subgroup K}
    (hY : Y = Subgroup.centralizer (((T₀.map Ψ ⊔ T₃.map Ψ ⊔
      perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K)) : Set K))
    (S : Sylow 2 ↥Y) : Nat.card ↥S ≤ 2 := by
  classical
  by_cases hbot : (S : Subgroup ↥Y) = ⊥
  · have hsub : Subsingleton ↥S := ⟨fun a b => Subtype.ext (by
      have hmem : ∀ x ∈ (S : Subgroup ↥Y), x = 1 :=
        (Subgroup.eq_bot_iff_forall (S : Subgroup ↥Y)).1 hbot
      rw [hmem a a.2, hmem b b.2])⟩
    have h1 : Nat.card ↥S = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨1, (S : Subgroup ↥Y).one_mem⟩⟩⟩
    omega
  · have hex : ∃ v ∈ (S : Subgroup ↥Y), v ≠ 1 := by
      by_contra hcon
      refine hbot ((Subgroup.eq_bot_iff_forall (S : Subgroup ↥Y)).2 fun x hx => ?_)
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    obtain ⟨v₀, hv₀S, hv₀⟩ := hex
    have hinj : Function.Injective
        (fun w : ↥S => if (w : ↥Y) = 1 then (0 : Fin 2) else 1) := by
      intro x y hxy
      by_cases hx : ((x : ↥S) : ↥Y) = 1
      · have hy : ((y : ↥S) : ↥Y) = 1 := by
          by_contra hy
          simp [hx, hy] at hxy
        exact Subtype.ext (by rw [hx, hy])
      · have hy : ((y : ↥S) : ↥Y) ≠ 1 := by
          intro hy
          simp [hx, hy] at hxy
        have hxK : (x : K) ≠ 1 := fun h => hx (Subtype.ext h)
        have hyK : (y : K) ≠ 1 := fun h => hy (Subtype.ext h)
        have hv₀K : ((⟨v₀, hv₀S⟩ : ↥S) : K) ≠ 1 := fun h => hv₀ (Subtype.ext h)
        have hxv := four_centralizer_sylow_prod_eq_one hF hf hΨ hN hodd hs hord hT₀ hT₃ hΔ hhs hY
          S hxK hv₀K
        have hyv := four_centralizer_sylow_prod_eq_one hF hf hΨ hN hodd hs hord hT₀ hT₃ hΔ hhs hY
          S hyK hv₀K
        exact Subtype.ext (mul_right_cancel (by rw [hxv, hyv] :
          (x : ↥Y) * ((⟨v₀, hv₀S⟩ : ↥S) : ↥Y) = (y : ↥Y) * ((⟨v₀, hv₀S⟩ : ↥S) : ↥Y)))
    exact (Nat.card_le_card_of_injective _ hinj).trans (by simp : Nat.card (Fin 2) ≤ 2)

private theorem four_centralizer_index_le_two (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ) (hN : Ψ.range.Normal)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))))
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    (hhs : Ψ s ∈ T₀.map Ψ ⊔ T₃.map Ψ) {Y : Subgroup K}
    (hY : Y = Subgroup.centralizer (((T₀.map Ψ ⊔ T₃.map Ψ ⊔
      perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K)) : Set K)) :
    (pPrimeCore 2 ↥Y).index ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Y) := Sylow.nonempty
  have hcard := four_centralizer_sylow_card hF hf hΨ hN hodd hs hord hT₀ hT₃ hΔ hhs hY S
  have hcyc : IsCyclic ↥S := by
    have hdvd : Nat.card ↥S ∣ 2 := by
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      have hk' : Nat.card ↥S = 2 ^ k := hk
      have hk1 : k ≤ 1 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by rw [← hk']; exact hcard)
      rw [hk']
      simpa using Nat.pow_dvd_pow 2 hk1
    exact isCyclic_of_card_dvd_prime hdvd
  rw [(cyclic_sylow_normal_odd_complement S hcyc).2.2.2.1.2.2.1]
  exact hcard

private theorem four_centralizer_line (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hΨ : Function.Injective Ψ) (hN : Ψ.range.Normal)
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hord : orderOf (Ψ s) = 2 ^ f + 1)
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₃ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 3 1) T₃)
    (hΔ : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU (unitaryInvolution F 2 f) 4,
      U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hF) 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ)
    {y : K} (hyP : y ∈ Subgroup.centralizer
      ((perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K) : Set K))
    (hys : y * Ψ s = Ψ s * y) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) :
    y ∈ Subgroup.centralizer ((T₀.map Ψ ⊔ T₃.map Ψ : Subgroup K) : Set K) := by
  have hker : Ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) 4) := by
    rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hΨ]
    exact bot_le
  have hP := SUTrans.commute_of_mem_centralizer_perpRoots (unitaryInvolution_involutive hF)
    (fun a ha => exists_add_unitaryInvolution_eq hF ha) (m := 2) (by norm_num) hΔ hT₀ hT₃ hyP
  obtain ⟨A, φ, α, hL⟩ :=
    exists_isSemilinearLift hF (by omega) (n := 4) (by norm_num) (by norm_num) hker hN y
  have hcomm := (four_lift hF hf hΨ hs hord hy2 hys hP hL).2.2
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_union] at hx
  rcases hx with hx | hx
  · obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨c, hc, htc⟩ := (hT₀.1 t).1 ht
    exact (hcomm 0 (Or.inl rfl) t c hc htc).symm
  · obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨c, hc, htc⟩ := (hT₃.1 t).1 ht
    exact (hcomm 3 (Or.inr rfl) t c hc htc).symm

end FourCentralizer

theorem unitaryFourAutCentralizer : UnitaryFourAutCentralizer := by
  intro K _ _ X₀ Δ f hf hf2 hN hX hodd A hA B hB hAB h hh hord
  obtain ⟨Ψ, hker, hrange, hΔ, T₀, T₃, hT₀, hT₃, hAΨ, hBΨ⟩ :=
    (show IsSUImage X₀ Δ f (2 + 2) hf (by norm_num) from hX).exists_frame (m := 2) hA hB
      hAB.commutator_ne_bot
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hΔ' : ∀ U : Subgroup K, U ∈ Δ ↔ ∃ x : SU σ 4, U = (conjSub
      (Unitary.rootGroup σ hσ 4 (unitaryLongRoot 4 (by norm_num))) x).map Ψ := hΔ
  have hΨ : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff Ψ]
    exact le_bot_iff.mp (hker.trans (le_of_eq (center_SU_four_eq_bot hσ)))
  obtain ⟨s, hs, hΦs⟩ :=
    SUTrans.exists_mem_lineSL_of_mem_sup hσ Ψ hT₀ hT₃ (by rw [← hAΨ, ← hBΨ]; exact hh)
  have hodd' : Odd (Nat.card ↥(Subgroup.centralizer (Ψ.range : Set K))) := by
    rw [hrange]
    exact hodd
  have hhs : Ψ s ∈ T₀.map Ψ ⊔ T₃.map Ψ := by
    rw [hΦs, ← hAΨ, ← hBΨ]
    exact hh
  refine ⟨fun y hy hy2 => ?_, ?_⟩
  · have hy' := hy
    rw [hAΨ, hBΨ] at hy'
    have hyP : y ∈ Subgroup.centralizer
        ((perpRoots Δ (T₀.map Ψ ⊔ T₃.map Ψ) : Subgroup K) : Set K) := (Subgroup.mem_inf.1 hy').1
    have hys : y * Ψ s = Ψ s * y := by
      have h2 : y * h = h * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.1 hy').2
      rwa [hΦs]
    rw [hAΨ, hBΨ]
    have hord' : orderOf (Ψ s) = 2 ^ f + 1 := by rw [hΦs]; exact hord
    exact four_centralizer_line hF hf2 hΨ (hrange ▸ hN) hs hord' hT₀ hT₃ hΔ' hyP hys hy2
  · rw [hAΨ, hBΨ]
    have hord' : orderOf (Ψ s) = 2 ^ f + 1 := by rw [hΦs]; exact hord
    exact four_centralizer_index_le_two hF hf2 hΨ (hrange ▸ hN) hodd' hs hord' hT₀ hT₃ hΔ' hhs rfl

end CFSG.RankThree.GF2n.Tim81
