module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitFieldSU
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUFrame
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitary
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryMat

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff gramSU unitarySU_eq_gramSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace OrdPFieldNsUD

section InnerDiag

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem ggPsiInnerDiag_of_frame_conj (h : UnitaryFieldData 2 f F) (hn : 4 ≤ n) {G : Type}
    [Group G] {ψ : SU (unitaryInvolution F 2 f) n →* G} {P : GL (Fin n) F}
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    {A : GL (Fin n) F} (hA : A ∈ primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {y : G} (hy : ∀ x x' : ↥(unitarySU 2 f F n), (x' : GL (Fin n) F) = A * x * A⁻¹ →
      y⁻¹ * SURep.ggFrameU hF ψ P hP x * y = SURep.ggFrameU hF ψ P hP x') :
    GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAid : InnerDiagSU.IsIdUnitary (unitaryInvolution F 2 f) A := by
    have hσ : (⇑(unitaryInvolution F 2 f) : F → F) = ⇑h.bar :=
      funext fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
    have h1 := mem_primeFormUnitary.mp hA
    unfold InnerDiagSU.IsIdUnitary conjTr
    rw [hσ]
    rwa [Units.val_one, Matrix.mul_one] at h1
  have hA' := MpStdSU.isJUnitary_conj_inv hP hAid
  set e := SURep.ggFrameEquiv hF P hP with he
  have hψ : ∀ u, ψ u = SURep.ggFrameU hF ψ P hP (e u) := fun u => by
    simp [SURep.ggFrameU, he]
  have hcoe : ∀ u, ((e u : ↥(unitarySU 2 f F n)) : GL (Fin n) F) = P * u * P⁻¹ := fun u => by
    have h1 := SURep.coe_ggFrameEquiv_symm hF P hP (e u)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [h1]
    group
  have hconj : ∀ u, y⁻¹ * ψ u * y = ψ (InnerDiagSU.conjSU _ hA' u) := by
    intro u
    rw [hψ, hψ]
    apply hy
    rw [hcoe, hcoe, InnerDiagSU.coe_conjSU]
    group
  obtain ⟨d, hd, s, hs⟩ := MpStdSU.exists_SU_mul_diag (by omega : 2 ≤ n) hA'
  have hsD : ∀ z, s⁻¹ * InnerDiagSU.conjSU _ hA' z * s =
      InnerDiagSU.conjSU (InnerDiagSU.diagJ d hd) (InnerDiagSU.isJUnitary_diagJ d hd) z :=
    fun z => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, InnerDiagSU.coe_conjSU, hs]
      group
  refine ⟨ψ s, ⟨s, rfl⟩, fun γ hγ => ?_⟩
  obtain ⟨h', hh', hzh⟩ := MpStdSU.exists_torus_conj hF hn d hd hγ
  refine ⟨h', hh', fun z hz => ?_⟩
  calc (y * ψ s)⁻¹ * ψ z * (y * ψ s) = (ψ s)⁻¹ * (y⁻¹ * ψ z * y) * ψ s := by group
    _ = ψ (s⁻¹ * InnerDiagSU.conjSU _ hA' z * s) := by rw [hconj, map_mul, map_mul, map_inv]
    _ = ψ (h' * z * h'⁻¹) := by rw [hsD z, hzh z hz]

end InnerDiag

section Diag

variable {F : Type} [Field F] {f n : ℕ}

theorem diagHom_mem_normalizer (h : UnitaryFieldData 2 f F) {τ : Fin n → Fˣ}
    (hτ : ∀ i, (τ i : F) ^ (2 ^ f + 1) = 1) :
    diagHom n τ ∈ Subgroup.normalizer (unitarySU 2 f F n : Set (GL (Fin n) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨fun hs => SURep.conj_mem_unitarySU h hτ hs, fun hs => ?_⟩
  have h1 := SURep.conj_mem_unitarySU h (SURep.norm_inv_eq_one hτ) hs
  have hinv : diagHom n τ⁻¹ = (diagHom n τ)⁻¹ := map_inv _ τ
  rw [hinv, inv_inv] at h1
  have e : (diagHom n τ)⁻¹ * (diagHom n τ * s * (diagHom n τ)⁻¹) * diagHom n τ = s := by group
  rwa [e] at h1

end Diag

section Setting

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

include hF in
theorem exists_conj_mem_centralizer_of_frame {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hf : 1 ≤ f) {ψ : SU (unitaryInvolution F 2 f) n →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Unitary.rootDatum hF n) .PSU n f ψ)
    (hpq : p ∣ 2 ^ f + 1) {P : GL (Fin n) F}
    (hP : conjTr (unitaryInvolution F 2 f) (P : Matrix (Fin n) (Fin n) F) *
      (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hBsD : ∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU hF ψ P hP) b) {y : G}
    (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag (Unitary.rootDatum hF n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hrk : 2 ≤ n / 2 := hrank
  have hn : 4 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  have hpp := hS.prime
  have hp2 := hS.ne_two
  set φ := SURep.ggFrameU hF ψ P hP with hφ
  have hrφ : φ.range = G₀ := (SURep.range_ggFrameU hF ψ P hP).trans hrange
  have hker₁ : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f F n) :=
    SURep.ker_ggFrameU_le hF ψ P hP hker
  have hC₁ : Subgroup.centralizer (φ.range : Set G) = ⊥ := by
    rw [hrφ]
    exact hS.centralizer_eq_bot
  set π := OrdPFieldSU.projP h hn1 with hπdef
  have hk : π.ker = φ.ker := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπdef, OrdPFieldSU.projP_eq_one_iff]
    constructor
    · rintro ⟨c, hc⟩
      have hz : φ z ∈ Subgroup.centralizer (φ.range : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨u, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← hc, TypeA.PGLTor.scalar_mul_comm]
      rw [hC₁, Subgroup.mem_bot] at hz
      exact hz
    · intro hz
      obtain ⟨e, he⟩ := SURep.ggFrameKer_of_ker_le_center hF hn3 hnq hker₁ z hz
      have he0 : e ≠ 0 := by
        rintro rfl
        have h1 := (z : GL (Fin n) F).det_ne_zero
        rw [he, map_zero, det_zero] at h1
        exact h1 rfl
      refine ⟨Units.mk0 e he0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, he, Units.val_mk0]
  set Θ := AutSt.modelEquiv φ π (OrdPFieldSU.projP_surjective h hn1) hk with hΘdef
  have hΘ : ∀ x, ((Θ (π x) : φ.range) : G) = φ x :=
    AutSt.modelEquiv_apply φ π (OrdPFieldSU.projP_surjective h hn1) hk
  have hyM' : y ∈ Subgroup.normalizer (φ.range : Set G) := by
    rw [hrφ]
    exact hyM
  set a : MulAut φ.range := φ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : φ.range, ((a x : φ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (φ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ x x' : ↥(unitarySU 2 f F n), β (π x) = π x' → y⁻¹ * φ x * y = φ x' := by
    intro x x' hxx'
    have e := congrArg (fun z => ((Θ z : φ.range) : G)) hxx'
    simp only [hβ, ha, hΘ] at e
    exact e
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨⟨A, θ⟩, hAθ⟩ := primeFormPsi_surjective h hC1 hn3 hq β
  rw [primeFormPsi_apply] at hAθ
  have hθ1 : θ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hAθ
    apply hyI
    refine ggPsiInnerDiag_of_frame_conj hF h hn hP A.2 fun x x' hx' => hrel x x' ?_
    rw [← hAθ, hπdef, OrdPFieldSU.projP_apply h hn1 x (OrdPFieldSU.mem_gramSU_one h x),
      primeFormConjHom_mk, OrdPFieldSU.projP_apply h hn1 x' (OrdPFieldSU.mem_gramSU_one h x')]
    congr 1
    apply Subtype.ext
    exact hx'.symm
  obtain ⟨hθo, H, hH⟩ := RecipeFieldSpU.primeForm_conj_of_pow_eq_one h hn3 hq hpp hp2 A θ hθ1
    (by rw [hAθ]; exact hβp)
  have hθp : θ ^ p = 1 := hθo ▸ pow_orderOf_eq_one θ
  have hβH : β = primeFormConjHom h _ H * primeFormFieldHom h hC1 θ *
      (primeFormConjHom h _ H)⁻¹ := by
    rw [← hAθ]
    exact hH
  obtain ⟨τ₀, hHτ⟩ := OrdPInnerSU.exists_mul_diagHom_mem h hn1 H.2
  set H' : ↥(unitarySU 2 f F n) := ⟨_, hHτ⟩ with hH'def
  have hH' : (H' : GL (Fin n) F) = (H : GL (Fin n) F) * diagHom n τ₀ := rfl
  have hSU : ∀ g : GL (Fin n) F,
      g ∈ gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) → g ∈ unitarySU 2 f F n :=
    fun g hg => by
      rw [unitarySU_eq_gramSU h]
      exact hg
  set E : GL (Fin n) F := (diagHom n τ₀)⁻¹ * glAut θ (diagHom n τ₀) with hEdef
  set w := (φ H')⁻¹ * y * φ H' with hwdef
  have hw : ∀ s : ↥(unitarySU 2 f F n), ∃ s'' : ↥(unitarySU 2 f F n),
      (s'' : GL (Fin n) F) = E * glAut θ s * E⁻¹ ∧ w⁻¹ * φ s * w = φ s'' := by
    intro s
    set x : ↥(unitarySU 2 f F n) := H' * s * H'⁻¹ with hxdef
    have hx : (x : GL (Fin n) F) = (H : GL (Fin n) F) * diagHom n τ₀ * (s : GL (Fin n) F) *
        ((H : GL (Fin n) F) * diagHom n τ₀)⁻¹ := by
      rw [hxdef, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hH']
    have hx₁ : diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹ ∈
        gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      have h1 := conj_mem_gramSU h _ (inv_mem H.2) (OrdPFieldSU.mem_gramSU_one h x)
      have e : ((H : GL (Fin n) F))⁻¹ * (x : GL (Fin n) F) * ((H : GL (Fin n) F))⁻¹⁻¹ =
          diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹ := by rw [hx]; group
      rwa [e] at h1
    have hx₃ : (H : GL (Fin n) F) * glAut θ (diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹) *
        (H : GL (Fin n) F)⁻¹ ∈ unitarySU 2 f F n :=
      hSU _ (conj_mem_gramSU h _ H.2 (glAut_mem_gramSU h hC1 θ hx₁))
    set x₃ : ↥(unitarySU 2 f F n) := ⟨_, hx₃⟩ with hx₃def
    have hβx : β (π x) = π x₃ := by
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply, ← map_inv, hπdef,
        OrdPFieldSU.projP_apply h hn1 x (OrdPFieldSU.mem_gramSU_one h x), primeFormConjHom_mk]
      change primeFormConjHom h _ H (primeFormFieldAut h hC1 θ _) = _
      rw [primeFormFieldAut_mk, primeFormConjHom_mk,
        OrdPFieldSU.projP_apply h hn1 x₃ (OrdPFieldSU.mem_gramSU_one h x₃)]
      congr 1
      apply Subtype.ext
      change (H : GL (Fin n) F) * glAut θ (((H⁻¹ : ↥(primeFormUnitary h _)) : GL (Fin n) F) *
        (x : GL (Fin n) F) * ((H⁻¹ : ↥(primeFormUnitary h _)) : GL (Fin n) F)⁻¹) *
          (H : GL (Fin n) F)⁻¹ =
          (H : GL (Fin n) F) * glAut θ (diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹) *
            (H : GL (Fin n) F)⁻¹
      rw [Subgroup.coe_inv, hx, show ((H : GL (Fin n) F))⁻¹ *
        ((H : GL (Fin n) F) * diagHom n τ₀ * (s : GL (Fin n) F) *
          ((H : GL (Fin n) F) * diagHom n τ₀)⁻¹) * ((H : GL (Fin n) F))⁻¹⁻¹ =
          diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹ by group]
    refine ⟨H'⁻¹ * x₃ * H', ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hH', hEdef]
      change ((H : GL (Fin n) F) * diagHom n τ₀)⁻¹ * ((H : GL (Fin n) F) *
        glAut θ (diagHom n τ₀ * (s : GL (Fin n) F) * (diagHom n τ₀)⁻¹) * (H : GL (Fin n) F)⁻¹) *
          ((H : GL (Fin n) F) * diagHom n τ₀) = _
      simp only [map_mul, map_inv]
      group
    · have h1 := hrel x x₃ hβx
      calc w⁻¹ * φ s * w = (φ H')⁻¹ * (y⁻¹ * φ x * y) * φ H' := by
            rw [hwdef, hxdef, map_mul, map_mul, map_inv]
            group
        _ = φ (H'⁻¹ * x₃ * H') := by rw [h1, map_mul, map_mul, map_inv]
  have hmN : φ H' ∈ Subgroup.normalizer (G₀ : Set G) :=
    Subgroup.le_normalizer (by rw [← hrφ]; exact ⟨H', rfl⟩)
  refine ⟨φ H', hmN, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨τ, hτ1, hτ2⟩ := hBsD b hb
  set T := diagHom n τ with hT
  have hbinv : ∀ s s₁ : ↥(unitarySU 2 f F n), (s₁ : GL (Fin n) F) = T⁻¹ * s * T →
      b⁻¹ * φ s * b = φ s₁ := by
    intro s s₁ hs₁
    have h1 := hτ2 s₁ s (by rw [hs₁]; group)
    rw [← h1]
    group
  have hconjT : ∀ s : ↥(unitarySU 2 f F n), T⁻¹ * (s : GL (Fin n) F) * T ∈
      unitarySU 2 f F n := by
    intro s
    have h1 := SURep.conj_mem_unitarySU h (SURep.norm_inv_eq_one hτ1) s.2
    have hinv : diagHom n τ⁻¹ = T⁻¹ := map_inv _ τ
    rwa [hinv, inv_inv] at h1
  have hpair : (b, T) ∈ SUTorus.suPairs φ :=
    SUTorus.mem_suPairs.mpr ⟨diagHom_mem_normalizer h hτ1, fun u v hv => hτ2 u v hv⟩
  have hpair_p : ((1 : G), T ^ p) ∈ SUTorus.suPairs φ := by
    have h1 := (SUTorus.suPairs φ).pow_mem hpair p
    rwa [Prod.pow_mk, hS.elem.2 b hb] at h1
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn3 hnq hpp hpq hker₁ hpair_p
  have hτp : ∀ i, τ i ^ p = c := by
    intro i
    have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i i) hc
    simp only [hT, ← map_pow, coe_diagHom, Matrix.diagonal_apply_eq, Pi.pow_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h1)
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set lam : Fˣ := Units.map (θ : F →* F) (τ i₀) * (τ i₀)⁻¹ with hlam
  have hθτ : ∀ i, Units.map (θ : F →* F) (τ i) = lam * τ i := by
    intro i
    have hr : (τ i * (τ i₀)⁻¹) ^ p = 1 := by rw [mul_pow, inv_pow, hτp, hτp, mul_inv_cancel]
    have hfix := OrdPRest.ringAut_fix_of_pow_eq_one hpp hθp
      (x := ((τ i * (τ i₀)⁻¹ : Fˣ) : F)) (by rw [← Units.val_pow_eq_pow_val, hr, Units.val_one])
    have hu : Units.map (θ : F →* F) (τ i * (τ i₀)⁻¹) = τ i * (τ i₀)⁻¹ :=
      Units.ext (by rw [Units.coe_map]; exact hfix)
    rw [map_mul, map_inv] at hu
    calc Units.map (θ : F →* F) (τ i) = Units.map (θ : F →* F) (τ i) *
          (Units.map (θ : F →* F) (τ i₀))⁻¹ * Units.map (θ : F →* F) (τ i₀) := by group
      _ = τ i * (τ i₀)⁻¹ * Units.map (θ : F →* F) (τ i₀) := by rw [hu]
      _ = lam * τ i := by
        rw [hlam, mul_comm (τ i * (τ i₀)⁻¹), mul_comm (τ i), ← mul_assoc]
  have hLd : Matrix.GeneralLinearGroup.scalar (Fin n) lam = diagHom n (fun _ => lam) :=
    Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply])
  have hθT : glAut θ T = Matrix.GeneralLinearGroup.scalar (Fin n) lam * T := by
    rw [hLd, hT, ← map_mul, TableBUM.glAut_diagHom]
    congr 1
    funext k
    exact hθτ k
  have hEd : E = diagHom n (τ₀⁻¹ * fun k => Units.map (θ : F →* F) (τ₀ k)) := by
    rw [hEdef, TableBUM.glAut_diagHom, ← map_inv, ← map_mul]
  have hET : T⁻¹ * E * T = E := by
    have h1 : E * T = T * E := by
      rw [hEd, hT]
      exact (CFSG.RankThree.Classical2.diagHom_commute _ _).eq
    rw [mul_assoc, h1]
    group
  have hL : ∀ X : GL (Fin n) F, (Matrix.GeneralLinearGroup.scalar (Fin n) lam)⁻¹ * X *
      Matrix.GeneralLinearGroup.scalar (Fin n) lam = X := fun X => by
    rw [mul_assoc, ← TypeA.PGLTor.scalar_mul_comm lam X]
    group
  have hkey : ∀ s : ↥(unitarySU 2 f F n),
      (w * b)⁻¹ * φ s * (w * b) = (b * w)⁻¹ * φ s * (b * w) := by
    intro s
    obtain ⟨s'', hs''c, hs''⟩ := hw s
    set s₁ : ↥(unitarySU 2 f F n) := ⟨_, hconjT s⟩ with hs₁def
    obtain ⟨s₁₂, hs₁₂c, hs₁₂⟩ := hw s₁
    set s₃ : ↥(unitarySU 2 f F n) := ⟨_, hconjT s''⟩ with hs₃def
    have heq : s₃ = s₁₂ := by
      apply Subtype.ext
      change T⁻¹ * (s'' : GL (Fin n) F) * T = s₁₂
      rw [hs''c, hs₁₂c]
      change T⁻¹ * (E * glAut θ s * E⁻¹) * T = E * glAut θ (T⁻¹ * (s : GL (Fin n) F) * T) * E⁻¹
      rw [map_mul, map_mul, map_inv, hθT]
      calc T⁻¹ * (E * glAut θ s * E⁻¹) * T =
            (T⁻¹ * E * T) * (T⁻¹ * glAut θ s * T) * (T⁻¹ * E * T)⁻¹ := by group
        _ = E * (T⁻¹ * glAut θ s * T) * E⁻¹ := by rw [hET]
        _ = E * (T⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin n) lam)⁻¹ * glAut θ s *
            Matrix.GeneralLinearGroup.scalar (Fin n) lam) * T) * E⁻¹ := by rw [hL]
        _ = E * ((Matrix.GeneralLinearGroup.scalar (Fin n) lam * T)⁻¹ * glAut θ s *
            (Matrix.GeneralLinearGroup.scalar (Fin n) lam * T)) * E⁻¹ := by group
    calc (w * b)⁻¹ * φ s * (w * b) = b⁻¹ * (w⁻¹ * φ s * w) * b := by group
      _ = b⁻¹ * φ s'' * b := by rw [hs'']
      _ = φ s₃ := hbinv s'' s₃ rfl
      _ = φ s₁₂ := by rw [heq]
      _ = w⁻¹ * φ s₁ * w := hs₁₂.symm
      _ = w⁻¹ * (b⁻¹ * φ s * b) * w := by rw [hbinv s s₁ rfl]
      _ = (b * w)⁻¹ * φ s * (b * w) := by group
  have hc' : (w * b) * (b * w)⁻¹ ∈ Subgroup.centralizer (φ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, rfl⟩
    calc φ s * ((w * b) * (b * w)⁻¹) =
          (w * b) * ((w * b)⁻¹ * φ s * (w * b)) * (b * w)⁻¹ := by group
      _ = (w * b) * ((b * w)⁻¹ * φ s * (b * w)) * (b * w)⁻¹ := by rw [hkey s]
      _ = (w * b) * (b * w)⁻¹ * φ s := by group
  rw [hC₁, Subgroup.mem_bot] at hc'
  exact (mul_inv_eq_one.mp hc').symm

end Setting

theorem exists_conj_mem_centralizer_delta {G : Type} [Group G] [Finite G] {p f n : ℕ}
    {Bs G₀ : Subgroup G}
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) n →* G}
    (hS : GGSixFusionSetting p Bs G₀
      (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) n) .PSU n
        (f + 1) ψ)
    (hpq : p ∣ 2 ^ (f + 1) + 1) (hpn : p ∣ n) {y : G}
    (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag
      (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) n) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hn : 4 ≤ n := by
    have hrk : 2 ≤ n / 2 := hrank
    omega
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  obtain ⟨P, hP, hBsD⟩ := UnitModel.exists_frame_of_su_gen hS.prime hS.ne_two hn
    (OrdPOutSU.div_add_one_lt_sub_two hS.prime hS.ne_two hpn hn) hpq hker hC
    (by rw [hrange]; exact hS.bstar_le) hS.elem hS.innerDiag (by rw [hrange]; exact hS.unique)
  exact exists_conj_mem_centralizer_of_frame _ (by omega) hS hpq hP hBsD hyM hyp hyI

end OrdPFieldNsUD

section Family

theorem ggOrdPFieldConjPSUDelta_holds : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSU n f).D .PSU n f ψ → p ∣ 2 ^ f + 1 → p ∣ n →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .PSU n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hpq hpn y hyM hyo hyI
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  exact OrdPFieldNsUD.exists_conj_mem_centralizer_delta hS hpq hpn hyM hyp hyI

theorem ggOrdPFieldConjPSURest_holds : GGOrdPFieldConjPSURest := by
  intro G _ _ p Bs G₀ n f ψ hS _ hc y hyM hyo _ hyI
  rcases hc with hpq | hpn
  · exact ggOrdPFieldConjPSUNonsplit_holds G p Bs G₀ n f ψ hS hpq y hyM hyo hyI
  · by_cases hpq : p ∣ 2 ^ f + 1
    · exact ggOrdPFieldConjPSUDelta_holds G p Bs G₀ n f ψ hS hpq hpn y hyM hyo hyI
    · exact ggOrdPFieldConjPSUNonsplit_holds G p Bs G₀ n f ψ hS hpq y hyM hyo hyI

theorem ggOrdPFieldConjAt_PSU : GGOrdPFieldConjAt .PSU :=
  ggOrdPFieldConjAt_PSU_of_rest ggOrdPFieldConjPSURest_holds

end Family

end CFSG.StandardType
