module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCore
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
import CFSG.RankThree.PartTwo.Sec6.Item65UsedTools
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section Matrices

variable {K : Type} [Field K]

theorem pow_eq_self_of_mod_three {τ : K} (hτ : τ ^ 3 = 1) {r : ℕ} (hr : r % 3 = 1) :
    τ ^ r = τ := by
  rw [← Nat.div_add_mod r 3, hr, pow_add, pow_mul, hτ, one_pow, one_mul, pow_one]

theorem frobGL_diagTau {τ : K} (hτ : τ ^ 3 = 1) {σ : K ≃+* K} (hστ : σ τ = τ) :
    frobGL σ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hστ]

theorem frobGL_cycThree (σ : K ≃+* K) : frobGL σ (cycThree : GL (Fin 3) K) = cycThree :=
  CFSG.RankThree.PartTwo.Sec12.KS128Move.frobGL_cycThree σ

theorem cycThree_pow_three : (cycThree : GL (Fin 3) K) ^ 3 = 1 :=
  CFSG.RankThree.PartTwo.Sec4.cycThree_pow_three

theorem mk_diagTau_mul_mk_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) =
      ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) := by
  have h1 : (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ := by
    apply Units.ext
    rw [cycThree_conj_diagTau hτ, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul,
      Matrix.one_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  have h2 : ProjGenLinGroup.mk ((cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹) =
      ProjGenLinGroup.mk (diagTau hτ) := by
    rw [h1, map_mul, mk_eq_one_iff_mem_statedScalars.mpr ⟨_, rfl⟩, one_mul]
  rw [map_mul, map_mul, map_inv] at h2
  calc ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) =
      (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) *
        (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹) *
          ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by rw [h2]
    _ = _ := by group

theorem mk_cycThree_ne_mk_pow {τ : K} (hτ : τ ^ 3 = 1) (n : ℕ) :
    ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ≠ ProjGenLinGroup.mk (diagTau hτ ^ n) := by
  intro h
  have h1 : (diagTau hτ ^ n)⁻¹ * cycThree ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨z, hz⟩ := h1
  have h2 : (cycThree : GL (Fin 3) K) = diagTau hτ ^ n * GeneralLinearGroup.scalar (Fin 3) z := by
    rw [hz]
    group
  have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 0) h2
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal,
    Matrix.diagonal_pow, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal, coe_cycThree] at h3
  simp at h3

end Matrices

variable {G : Type} [Group G] [Finite G]

theorem false_of_field {Y K : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hc3 : c ^ 3 = 1) (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hT : IsType424 (K ⧸ aschbacherSolvableCore 3 K))
    {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf] (hKf : PiField π p f Kf)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {f₀ : ℕ} (hf : f = 3 * f₀) {σ : Kf ≃+* Kf}
    (hσ : (∀ x, σ x = x ^ piCard π (p ^ f₀)) ∨ ∀ x, σ x = x ^ (piCard π (p ^ f₀) ^ 2))
    {g : GL (Fin 3) Kf} (hg : g ∈ glPi π 3 (p ^ f) Kf)
    (hα : ∀ s (hs : s ∈ slPi π 3 (p ^ f) Kf),
      (MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩))
        (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (g * frobGL σ s * g⁻¹)) : False := by
  have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hKf.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Kf)) :=
    Sec13.isPerfect_projImage_slPi hKf hq2
  have := hKf.finite
  have : Fact p.Prime := ⟨hKf.prime⟩
  obtain ⟨φ₀, hφ₀, hφ₀3⟩ := exists_frob hKf hf
  have hψ : σ = φ₀ ∨ σ = φ₀ ^ 2 := eq_or_eq_sq_of_pow hφ₀ hσ
  have hΨ3 := frobGL_three' hφ₀3 hψ
  set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
  set α := MulAut.congr φ τc with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, hτc, thetaQuotMulAut_pow_three hcN hc3, map_one]
  have hTmem : ∀ s ∈ slPi π 3 (p ^ f) Kf, g * frobGL σ s * g⁻¹ ∈ slPi π 3 (p ^ f) Kf :=
    fun s hs => conj_mem_slPi hπ hg (frobGL_mem_slPi hKf σ hs)
  have hαs : ∀ s (hs : s ∈ slPi π 3 (p ^ f) Kf),
      α (projOf _ ⟨s, hs⟩) = projOf _ ⟨g * frobGL σ s * g⁻¹, hTmem s hs⟩ :=
    fun s hs => Subtype.ext (by rw [hα, coe_projOf])
  set N := g * frobGL σ g * frobGL σ (frobGL σ g) with hN
  have hW : ∀ A, g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) * g⁻¹ =
      N * A * N⁻¹ := by
    intro A
    rw [hN]
    simp only [map_mul, map_inv, hΨ3]
    group
  have hmod : ∀ A ∈ slPi π 3 (p ^ f) Kf, N * A * N⁻¹ * A⁻¹ ∈ StatedScalars (Fin 3) Kf := by
    intro A hA
    have h1 := congrArg (fun β : MulAut (projImage (slPi π 3 (p ^ f) Kf)) =>
      ((β (projOf _ ⟨A, hA⟩) : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) hα3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hαs, hαs, hαs] at h1
    have h2 : ProjGenLinGroup.mk (g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) *
        g⁻¹) = ProjGenLinGroup.mk A := h1
    rw [hW] at h2
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h2, mul_inv_cancel]
  have hNc := commute_of_comm_mod_scalars hmod
  have hσ3' : ∀ A ∈ slPi π 3 (p ^ f) Kf,
      g * frobGL σ (g * frobGL σ (g * frobGL σ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
    intro A hA
    rw [hW, hNc A hA, mul_inv_cancel_right]
  obtain ⟨h, hh, hconj⟩ := exists_conj_frobGL hKf hq hf hφ₀ hφ₀3 hψ hg hσ3'
  set Q := fixedIn (slPi π 3 (p ^ f) Kf) (frobGL σ) with hQ
  have hhQ : ∀ B ∈ Q, h * B * h⁻¹ ∈ slPi π 3 (p ^ f) Kf := fun B hB =>
    conj_mem_slPi hπ hh hB.1
  set ρL : Q →* slPi π 3 (p ^ f) Kf :=
    ((MulAut.conj h).toMonoidHom.comp Q.subtype).codRestrict _ (fun B => hhQ B B.2) with hρL
  set ρX : Q →* projImage (slPi π 3 (p ^ f) Kf) := (projOf (slPi π 3 (p ^ f) Kf)).comp ρL with hρX
  have hρXapply : ∀ B : Q, ((ρX B : projImage (slPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h * (B : GL (Fin 3) Kf) * h⁻¹) := fun B => rfl
  set F := α.toMonoidHom.eqLocus (MonoidHom.id (projImage (slPi π 3 (p ^ f) Kf))) with hF
  have hρF : ∀ B : Q, ρX B ∈ F := by
    intro B
    change α (ρX B) = ρX B
    have hB := B.2.2
    change frobGL σ (B : GL (Fin 3) Kf) = B at hB
    apply Subtype.ext
    change ((α (projOf _ ⟨h * (B : GL (Fin 3) Kf) * h⁻¹, hhQ B B.2⟩) :
        projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (h * (B : GL (Fin 3) Kf) * h⁻¹)
    rw [hα, hconj _ (hhQ B B.2)]
    congr 2
    rw [show h⁻¹ * (h * (B : GL (Fin 3) Kf) * h⁻¹) * h = B by group, hB]
  set ρ : Q →* F := ρX.codRestrict F hρF with hρ
  have hlift : ∀ m : F, ∃ A ∈ slPi π 3 (p ^ f) Kf, ∃ z ∈ StatedScalars (Fin 3) Kf,
      ((m : projImage (slPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf) =
          ProjGenLinGroup.mk A ∧
        g * frobGL σ A * g⁻¹ = z * A := by
    intro m
    obtain ⟨⟨A, hA⟩, hmA⟩ := projOf_surjective _ (m : projImage (slPi π 3 (p ^ f) Kf))
    refine ⟨A, hA, g * frobGL σ A * g⁻¹ * A⁻¹, ?_, by rw [← hmA]; rfl, by group⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv]
    have h1 : α (m : projImage (slPi π 3 (p ^ f) Kf)) = m := m.2
    rw [← hmA, hαs] at h1
    have h2 := congrArg (fun x : projImage (slPi π 3 (p ^ f) Kf) =>
      (x : ProjGenLinGroup (Fin 3) Kf)) h1
    simp only [coe_projOf] at h2
    rw [h2, mul_inv_cancel]
  have hcommF : ⁅(⊤ : Subgroup F), ⊤⁆ ≤ ρ.range := by
    rw [Subgroup.commutator_le]
    rintro m₁ - m₂ -
    obtain ⟨A₁, hA₁, z₁, hz₁, hm₁, hT₁⟩ := hlift m₁
    obtain ⟨A₂, hA₂, z₂, hz₂, hm₂, hT₂⟩ := hlift m₂
    set C := A₁ * A₂ * A₁⁻¹ * A₂⁻¹ with hC
    have hCL : C ∈ slPi π 3 (p ^ f) Kf :=
      mul_mem (mul_mem (mul_mem hA₁ hA₂) (inv_mem hA₁)) (inv_mem hA₂)
    have hTC : g * frobGL σ C * g⁻¹ = C := by
      have hc1 := commute_of_mem_statedScalars hz₁
      have hc2 := commute_of_mem_statedScalars hz₂
      have e1 : g * frobGL σ C * g⁻¹ = (g * frobGL σ A₁ * g⁻¹) * (g * frobGL σ A₂ * g⁻¹) *
          (g * frobGL σ A₁ * g⁻¹)⁻¹ * (g * frobGL σ A₂ * g⁻¹)⁻¹ := by
        rw [hC]
        simp only [map_mul, map_inv]
        group
      rw [e1, hT₁, hT₂]
      calc z₁ * A₁ * (z₂ * A₂) * (z₁ * A₁)⁻¹ * (z₂ * A₂)⁻¹ =
          (A₁ * z₁) * (A₂ * z₂) * (z₁ * A₁)⁻¹ * (z₂ * A₂)⁻¹ := by rw [← hc1 A₁, ← hc2 A₂]
        _ = A₁ * (z₁ * A₂) * z₂ * (z₁ * A₁)⁻¹ * (z₂ * A₂)⁻¹ := by group
        _ = A₁ * (A₂ * z₁) * z₂ * (z₁ * A₁)⁻¹ * (z₂ * A₂)⁻¹ := by rw [hc1 A₂]
        _ = A₁ * A₂ * (z₁ * z₂ * A₁⁻¹ * z₁⁻¹) * A₂⁻¹ * z₂⁻¹ := by group
        _ = A₁ * A₂ * (A₁⁻¹ * z₁ * z₂ * z₁⁻¹) * A₂⁻¹ * z₂⁻¹ := by
            rw [show z₁ * z₂ * A₁⁻¹ = A₁⁻¹ * (z₁ * z₂) by
              rw [← (commute_of_mem_statedScalars (mul_mem hz₁ hz₂) A₁⁻¹)]]
            group
        _ = A₁ * A₂ * A₁⁻¹ * (z₁ * z₂ * z₁⁻¹) * A₂⁻¹ * z₂⁻¹ := by group
        _ = A₁ * A₂ * A₁⁻¹ * z₂ * A₂⁻¹ * z₂⁻¹ := by
            rw [show z₁ * z₂ * z₁⁻¹ = z₂ by
              rw [← hc1 z₂]
              group]
        _ = C := by
            rw [hC, mul_assoc (A₁ * A₂ * A₁⁻¹) z₂, ← hc2 A₂⁻¹]
            group
    have hBL : h⁻¹ * C * h ∈ slPi π 3 (p ^ f) Kf := by
      simpa using conj_mem_slPi hπ (inv_mem hh) hCL
    have hBQ : h⁻¹ * C * h ∈ Q := by
      refine ⟨hBL, ?_⟩
      change frobGL σ (h⁻¹ * C * h) = h⁻¹ * C * h
      have h1 := hconj C hCL
      rw [hTC] at h1
      calc frobGL σ (h⁻¹ * C * h) = h⁻¹ * (h * frobGL σ (h⁻¹ * C * h) * h⁻¹) * h := by group
        _ = h⁻¹ * C * h := by rw [← h1]
    refine ⟨⟨h⁻¹ * C * h, hBQ⟩, Subtype.ext (Subtype.ext ?_)⟩
    change ProjGenLinGroup.mk (h * (h⁻¹ * C * h) * h⁻¹) = _
    rw [show h * (h⁻¹ * C * h) * h⁻¹ = C by group]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, hm₁, hm₂, hC,
      map_mul, map_inv]
  obtain ⟨K', hK', rfl⟩ := hK
  have hψmem : ∀ m : (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G),
      φ (cMap Y c m) ∈ F := by
    intro m
    have h1 : τc (cMap Y c m) = cMap Y c m := by
      have hk : cMap Y c m ∈ (cMap Y c).range := ⟨m, rfl⟩
      rw [range_cMap hcN hc3] at hk
      exact hk
    change φ (τc (φ.symm (φ (cMap Y c m)))) = φ (cMap Y c m)
    rw [MulEquiv.symm_apply_apply, h1]
  set ψY : (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →* F :=
    (φ.toMonoidHom.comp (cMap Y c)).codRestrict F hψmem with hψYdef
  have hψs : Function.Surjective ψY := by
    rintro ⟨z, hz⟩
    have hz' : τc (φ.symm z) = φ.symm z := by
      have := congrArg φ.symm hz
      change φ.symm (φ (τc (φ.symm z))) = φ.symm z at this
      rwa [MulEquiv.symm_apply_apply] at this
    have hmem : φ.symm z ∈ (cMap Y c).range := by
      rw [range_cMap hcN hc3]
      exact hz'
    obtain ⟨m, hm⟩ := hmem
    refine ⟨m, Subtype.ext ?_⟩
    change φ (cMap Y c m) = z
    rw [hm, MulEquiv.apply_symm_apply]
  set K₁ := K'.map ψY with hK₁
  have hK₁sn : K₁.IsSubnormal := hK'.2.1.map hψs
  have : Group.IsPerfect K' := hK'.1
  have hK₁p : Group.IsPerfect K₁ := Group.IsPerfect.map _
  have hK₁ne : K₁ ≠ ⊥ := by
    intro hbot
    apply fieldCent_map_cMap_ne_bot hK'
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨k, hk, rfl⟩
    have h1 : ψY k ∈ K₁ := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : φ (cMap Y c k) = 1 := congrArg Subtype.val h1
    exact (MulEquiv.map_eq_one_iff φ).mp h2
  have hK₁le : K₁ ≤ ρ.range := by
    calc K₁ = ⁅K₁, K₁⁆ := (Subgroup.isPerfect_iff.mp hK₁p).symm
      _ ≤ ⁅(⊤ : Subgroup F), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ ρ.range := hcommF
  have hP := hK₁sn.comap ρ
  have hK₁abel : ∀ P : Subgroup Q, P ≤ Subgroup.center Q → K₁ ≤ P.map ρ → False := by
    intro P hPZ hK₁P
    apply hK₁ne
    have hcomm : ⁅K₁, K₁⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := hK₁P hx
      obtain ⟨b, hb, rfl⟩ := hK₁P hy
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hPZ hb)) a]
    rw [← Subgroup.isPerfect_iff.mp hK₁p, hcomm]
  have hmapcomap : (K₁.comap ρ).map ρ = K₁ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hK₁le]
  have hfull : ρ.range ≤ K₁ := by
    obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = (1 : ℕ) := ⟨1, rfl⟩
    have hf₀ : 1 ≤ f₀ := by have := hKf.one_le; omega
    by_cases hq₀ : 2 < p ^ f₀
    ·
      obtain ⟨K₀, _, hK₀⟩ : ∃ (K₀ : Type) (_ : Field K₀), PiField π p f₀ K₀ := by
        cases π
        · refine ⟨GaloisField p (2 * f₀), inferInstance, ⟨hKf.prime, hf₀, ?_⟩⟩
          rw [GaloisField.card p _ (by omega)]
          change p ^ (2 * f₀) = (p ^ f₀) ^ 2
          rw [← pow_mul, mul_comm]
        · exact ⟨GaloisField p f₀, inferInstance, ⟨hKf.prime, hf₀,
            GaloisField.card p _ (by omega)⟩⟩
      obtain ⟨ι, hιinj, -, hιL⟩ := exists_embedding_fixedIn hKf hf hφ₀ hφ₀3 K₀ hK₀
      have hQeq : Q = fixedIn (slPi π 3 (p ^ f) Kf) (frobGL φ₀) := by
        ext A
        rw [mem_fixedIn, mem_fixedIn]
        refine and_congr_right fun _ => ?_
        constructor
        · intro hA
          apply Units.ext
          rw [coe_frobGL]
          ext i j
          have := congrArg (fun B : GL (Fin 3) Kf => (B : Matrix (Fin 3) (Fin 3) Kf) i j) hA
          simp only [coe_frobGL, Matrix.map_apply] at this
          exact (fixed_iff_of_sq hφ₀3 hψ _).mp this
        · intro hA
          apply Units.ext
          rw [coe_frobGL]
          ext i j
          have := congrArg (fun B : GL (Fin 3) Kf => (B : Matrix (Fin 3) (Fin 3) Kf) i j) hA
          simp only [coe_frobGL, Matrix.map_apply] at this
          exact (fixed_iff_of_sq hφ₀3 hψ _).mpr this
      have eQ : slPi π 3 (p ^ f₀) K₀ ≃* Q :=
        (Subgroup.equivMapOfInjective _ ι hιinj).trans (MulEquiv.subgroupCongr
          (show (slPi π 3 (p ^ f₀) K₀).map ι = Q by rw [hιL, hQeq]))
      have hQq : IsQuasisimple Q :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ (Sec13.isQuasisimple_slPi hK₀ hq₀)
      rcases Sec6.subnormal_le_center_or_eq_top_of_isQuasisimple hQq hP with hPZ | hPtop
      · exact (hK₁abel _ hPZ (le_of_eq hmapcomap.symm)).elim
      · rintro _ ⟨B, rfl⟩
        have : B ∈ K₁.comap ρ := hPtop ▸ Subgroup.mem_top B
        exact this
    ·
      exfalso
      have h2 : p ^ f₀ = 2 := by
        have : 2 ≤ p ^ f₀ := le_trans hKf.prime.two_le (Nat.le_self_pow (by omega) _)
        omega
      have hπ2 : π = false := by
        cases π
        · rfl
        · exfalso
          have hq₀3 : ModThree true (p ^ f₀) := modThree_of_cube (by
            rw [← pow_mul, mul_comm, ← hf]
            exact hq)
          change p ^ f₀ % 3 = 1 at hq₀3
          omega
      subst hπ2
      have hK₀ : PiField false p f₀ (GaloisField p (2 * f₀)) := by
        refine ⟨hKf.prime, hf₀, ?_⟩
        rw [GaloisField.card p _ (by omega)]
        change p ^ (2 * f₀) = (p ^ f₀) ^ 2
        rw [← pow_mul, mul_comm]
      obtain ⟨ι, hιinj, -, hιL⟩ := exists_embedding_fixedIn hKf hf hφ₀ hφ₀3 _ hK₀
      have hQeq : Q = fixedIn (slPi false 3 (p ^ f) Kf) (frobGL φ₀) := by
        ext A
        rw [mem_fixedIn, mem_fixedIn]
        refine and_congr_right fun _ => ?_
        constructor
        · intro hA
          apply Units.ext
          rw [coe_frobGL]
          ext i j
          have := congrArg (fun B : GL (Fin 3) Kf => (B : Matrix (Fin 3) (Fin 3) Kf) i j) hA
          simp only [coe_frobGL, Matrix.map_apply] at this
          exact (fixed_iff_of_sq hφ₀3 hψ _).mp this
        · intro hA
          apply Units.ext
          rw [coe_frobGL]
          ext i j
          have := congrArg (fun B : GL (Fin 3) Kf => (B : Matrix (Fin 3) (Fin 3) Kf) i j) hA
          simp only [coe_frobGL, Matrix.map_apply] at this
          exact (fixed_iff_of_sq hφ₀3 hψ _).mpr this
      have eQ : slPi false 3 (p ^ f₀) (GaloisField p (2 * f₀)) ≃* Q :=
        (Subgroup.equivMapOfInjective _ ι hιinj).trans (MulEquiv.subgroupCongr
          (show (slPi false 3 (p ^ f₀) (GaloisField p (2 * f₀))).map ι = Q by rw [hιL, hQeq]))
      have hQs : Group.IsSolvable Q :=
        have := Sec13.isSolvable_slPi_two hK₀ h2
        Group.isSolvable_of_surjective (f := eQ.toMonoidHom) eQ.surjective
      have hRs : Group.IsSolvable ρ.range :=
        Group.isSolvable_of_surjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
      have hK₁s : Group.IsSolvable K₁ :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK₁le)
      have : Nontrivial K₁ := (Subgroup.nontrivial_iff_ne_bot _).mpr hK₁ne
      exact Group.IsPerfect.not_isSolvable K₁ hK₁s
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hKf hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hr1 : piCard π (p ^ f₀) % 3 = 1 := by
    have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (by
      rw [← pow_mul, mul_comm, ← hf]
      exact hq)
    cases π
    · change p ^ f₀ % 3 = 2 at hq₀
      change (p ^ f₀) ^ 2 % 3 = 1
      rw [Nat.pow_mod, hq₀]
    · exact hq₀
  have hστ : σ τ = τ := by
    rcases hσ with hσ | hσ
    · rw [hσ, pow_eq_self_of_mod_three hτ hr1]
    · rw [hσ, pow_eq_self_of_mod_three hτ (by rw [Nat.pow_mod, hr1])]
  have hdQ : diagTau hτ ∈ Q := ⟨diagTau_mem_slPi hπ hq' hτ, frobGL_diagTau hτ hστ⟩
  have hcQ : (cycThree : GL (Fin 3) Kf) ∈ Q := ⟨cycThree_mem_slPi hπ, frobGL_cycThree σ⟩
  set u : F := ρ ⟨diagTau hτ, hdQ⟩ with hu
  set v : F := ρ ⟨cycThree, hcQ⟩ with hv
  have hcoeρ : ∀ B : Q, (((ρ B : F) : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk h * ProjGenLinGroup.mk (B : GL (Fin 3) Kf) *
        (ProjGenLinGroup.mk h)⁻¹ := by
    intro B
    change ProjGenLinGroup.mk (h * (B : GL (Fin 3) Kf) * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hinjF : ∀ x y : F, (((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) = (((y : projImage (slPi π 3 (p ^ f) Kf)) :
        ProjGenLinGroup (Fin 3) Kf)) → x = y := fun x y hxy =>
    Subtype.ext (Subtype.ext hxy)
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← map_pow]
    have : (⟨diagTau hτ, hdQ⟩ : Q) ^ 3 = 1 := Subtype.ext (diagTau_pow_three hτ)
    rw [this, map_one]
  have hv3 : v ^ 3 = 1 := by
    rw [hv, ← map_pow]
    have : (⟨cycThree, hcQ⟩ : Q) ^ 3 = 1 := Subtype.ext cycThree_pow_three
    rw [this, map_one]
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : F => ((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) h1
    simp only [hu, hcoeρ, Subgroup.coe_one] at h2
    have h3 : ProjGenLinGroup.mk (diagTau hτ) = 1 := by
      have : ProjGenLinGroup.mk (diagTau hτ) = (ProjGenLinGroup.mk h)⁻¹ *
          (ProjGenLinGroup.mk h * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk h)⁻¹) *
            ProjGenLinGroup.mk h := by group
      rw [this, h2]
      group
    have h4 : ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf) ≠
        ProjGenLinGroup.mk (diagTau hτ ^ 0) := mk_cycThree_ne_mk_pow hτ 0
    obtain ⟨z, hz⟩ := mk_eq_one_iff_mem_statedScalars.mp h3
    have e00 : (z : Kf) = τ := by
      have := congrArg (fun A : GL (Fin 3) Kf => (A : Matrix (Fin 3) (Fin 3) Kf) 0 0) hz
      simpa [GeneralLinearGroup.coe_scalar, coe_diagTau] using this
    have e22 : (z : Kf) = 1 := by
      have := congrArg (fun A : GL (Fin 3) Kf => (A : Matrix (Fin 3) (Fin 3) Kf) 2 2) hz
      simpa [GeneralLinearGroup.coe_scalar, coe_diagTau] using this
    exact hτ1 (e00.symm.trans e22)
  have huv : u * v = v * u := by
    apply hinjF
    simp only [Subgroup.coe_mul, hu, hv, hcoeρ]
    have hc := mk_diagTau_mul_mk_cycThree hτ hτ0
    calc ProjGenLinGroup.mk h * ProjGenLinGroup.mk (diagTau hτ) * (ProjGenLinGroup.mk h)⁻¹ *
          (ProjGenLinGroup.mk h * ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf) *
            (ProjGenLinGroup.mk h)⁻¹) =
        ProjGenLinGroup.mk h * (ProjGenLinGroup.mk (diagTau hτ) *
          ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf)) * (ProjGenLinGroup.mk h)⁻¹ := by group
      _ = ProjGenLinGroup.mk h * (ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf) *
          ProjGenLinGroup.mk (diagTau hτ)) * (ProjGenLinGroup.mk h)⁻¹ := by rw [hc]
      _ = _ := by group
  have hvu : v ∉ Subgroup.zpowers u := by
    intro hmem
    have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hu3⟩
    rw [← hfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨n, hn⟩ := hmem
    apply mk_cycThree_ne_mk_pow hτ n
    have h1 := congrArg (fun x : F => ((x : projImage (slPi π 3 (p ^ f) Kf)) :
      ProjGenLinGroup (Fin 3) Kf)) hn
    simp only [hu, hv, ← map_pow, hcoeρ] at h1
    have h2 : ((((⟨diagTau hτ, hdQ⟩ : Q) ^ n : Q)) : GL (Fin 3) Kf) = diagTau hτ ^ n := by
      simp
    rw [h2] at h1
    calc ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf) = (ProjGenLinGroup.mk h)⁻¹ *
          (ProjGenLinGroup.mk h * ProjGenLinGroup.mk (cycThree : GL (Fin 3) Kf) *
            (ProjGenLinGroup.mk h)⁻¹) * ProjGenLinGroup.mk h := by group
      _ = (ProjGenLinGroup.mk h)⁻¹ * (ProjGenLinGroup.mk h *
            ProjGenLinGroup.mk (diagTau hτ ^ n) * (ProjGenLinGroup.mk h)⁻¹) *
              ProjGenLinGroup.mk h := by rw [h1]
      _ = ProjGenLinGroup.mk (diagTau hτ ^ n) := by group
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set eK : K' ≃* K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype :=
    K'.equivMapOfInjective _ (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype_injective with heK
  set eQK : K' ⧸ aschbacherSolvableCore 3 K' ≃*
      K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype ⧸
        aschbacherSolvableCore 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype) :=
    QuotientGroup.congr _ _ eK (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv
      Nat.prime_three eK) with heQK
  have hQK : IsQuasisimple (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype ⧸
      aschbacherSolvableCore 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eQK hK'.2.2
  have hcycK : ∀ S : Sylow 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype ⧸
      aschbacherSolvableCore 3 (K'.map (Y ⊓ Subgroup.centralizer ({c} : Set G)).subtype)),
      IsCyclic S := isCyclic_sylow_three_of_isType424 hT hQK
  have hcycK' : ∀ P : Sylow 3 K', IsCyclic P := by
    refine isCyclic_sylow_of_quotient (aschbacherSolvableCore 3 K')
      (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1 ?_
    exact isCyclic_sylow_of_mulEquiv eQK.symm hcycK
  have hcyc₁ : ∀ P : Sylow 3 K₁, IsCyclic P :=
    isCyclic_sylow_of_surjective (ψY.subgroupMap K') (MonoidHom.subgroupMap_surjective _ _)
      hcycK'
  have hukK : u ∈ K₁ := hfull ⟨_, rfl⟩
  have hvkK : v ∈ K₁ := hfull ⟨_, rfl⟩
  refine false_of_isCyclic_sylow hcyc₁ (u := ⟨u, hukK⟩) (v := ⟨v, hvkK⟩)
    (Subtype.ext hu3) (Subtype.ext hv3) (fun h1 => hu1 (congrArg Subtype.val h1))
    (Subtype.ext huv) ?_
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hvu
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
