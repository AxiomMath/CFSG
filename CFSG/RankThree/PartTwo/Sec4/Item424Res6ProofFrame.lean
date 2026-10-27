module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofPerm
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofFrameP
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix Res417Frame

namespace Res424Six

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_permGL_eq_sign (σ : Equiv.Perm (Fin 3)) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K) := by
  change (σ⁻¹.permMatrix K).det = _
  rw [Matrix.det_permutation, Equiv.Perm.sign_inv]

theorem permGL_mem_glPi (hK : PiField π p f K) (σ : Equiv.Perm (Fin 3)) :
    permGL σ ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h]
    have hmap : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar =
        ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      rw [Matrix.map_apply, permGL_apply]
      split_ifs <;> simp
    rw [hmap]
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, permGL_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (σ i)]
    simp only [Finset.mem_univ, ite_true, σ.injective.eq_iff]
  · exact mem_glPi_true _ _

theorem neg_one_mem_glPi (hK : PiField π p f K) : (-1 : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h, Units.val_neg, Units.val_one]
    have hmap : (-1 : Matrix (Fin 3) (Fin 3) K).map h.bar = -1 := by
      ext i j
      rw [Matrix.map_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.one_apply_ne hij]
    rw [hmap, Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, Matrix.one_mul]
  · exact mem_glPi_true _ _

theorem exists_slPi_mk_permGL (hK : PiField π p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (σ : Equiv.Perm (Fin 3)) :
    ∃ s ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk s = ProjGenLinGroup.mk (g * permGL σ * g⁻¹) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hdet : ∀ M : GL (Fin 3) K, ((g * M * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (M : Matrix (Fin 3) (Fin 3) K).det := by
    intro M
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  have hP := permGL_mem_glPi (p := p) (f := f) hK σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · refine ⟨g * permGL σ * g⁻¹, (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hg hP) (inv_mem hg), ?_⟩,
      rfl⟩
    rw [hdet, det_permGL_eq_sign, hs]
    simp
  · refine ⟨g * (-1 * permGL σ) * g⁻¹, (mem_slPi_iff hπ).mpr
      ⟨mul_mem (mul_mem hg (mul_mem (neg_one_mem_glPi hK) hP)) (inv_mem hg), ?_⟩, ?_⟩
    · rw [hdet, neg_one_mul, Units.val_neg, Matrix.det_neg, det_permGL_eq_sign, hs]
      norm_num
    · have h1 : ProjGenLinGroup.mk (-1 : GL (Fin 3) K) = 1 := by
        rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
        refine ⟨-1, Units.ext ?_⟩
        rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_neg, Units.val_one,
          Units.val_one, Matrix.scalar_apply, ← Matrix.diagonal_one, Matrix.diagonal_neg]
      simp only [map_mul, h1, one_mul]

theorem sign_eq_one_of_pow_three : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    Equiv.Perm.sign σ = 1 := by
  decide

theorem isDiag_scalar_mul_diagUnits (l s t : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, coe_diagUnits]
  exact (Matrix.isDiag_diagonal _).smul _

variable {H : Type} [Group H] {L : Subgroup H} [L.Normal]

theorem nonempty_autIn_equiv_perm_of_frameP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup H} {c : H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b)
    (hbd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHomP hK hq A hpgl).range →
        ∀ i, ∃ d : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i) :
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hR9 : Nat.card (pglHomP hK hq A hpgl).range = 9 := by
    have hcardA := card_eq_card_inf_mul_card_rangeP (L := L) (e := e) (hK := hK) (hq := hq)
      (A' := A) (hA' := hpgl)
    rw [hAc, Nat.card_zpowers, hc3, hA27] at hcardA
    omega
  set R := (pglHomP hK hq A hpgl).range with hR
  set D : Subgroup (GL (Fin 3) K) :=
    R.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hDdef
  have hmemD : ∀ y, y ∈ D ↔ (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R ∧
      y ∈ glPi π 3 (p ^ f) K := fun y => Iff.rfl
  have hRpow := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA.1.2
  have hmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = R := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ((hmemD y).mp hy).1
    · rintro x ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hpgl a a.2
      refine ⟨y, (hmemD y).mpr ⟨mk_mem_range_pglHomP a.2 hy, hy.1⟩, ?_⟩
      exact (pglHomP_apply a hy).symm
  have hC : IsTypeC π (p ^ f) K D := by
    refine ⟨inf_le_right, fun a ha => ?_, by rw [hmap, hR9], b, hb,
      fun a ha => hbd a ((hmemD a).mp ha).1⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hRpow _ ((hmemD a).mp ha).1
  obtain ⟨g, hgH, hform, hall⟩ := isTypeC_conj_std hK hq hC
  have hdiagR : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro y hy
    obtain ⟨⟨a, ha⟩, hay⟩ := hy
    obtain ⟨ya, hya⟩ := hpgl a ha
    rw [pglHomP_apply ⟨a, ha⟩ hya, QuotientGroup.eq] at hay
    obtain ⟨μ, hμ⟩ := hay
    have hyaD : ya ∈ D := (hmemD ya).mpr ⟨mk_mem_range_pglHomP ha hya, hya.1⟩
    obtain ⟨l, s, t, -, -, hl⟩ := hform ya hyaD
    have hy' : y = ya * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ g).eq
    have h1 : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) (l * μ) * diagUnits 1 s t := by
      calc g⁻¹ * y * g = g⁻¹ * ya * (GeneralLinearGroup.scalar (Fin 3) μ * g) := by
            rw [hy']; group
        _ = g⁻¹ * ya * g * GeneralLinearGroup.scalar (Fin 3) μ := by rw [← hc]; group
        _ = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t *
            GeneralLinearGroup.scalar (Fin 3) μ := by rw [hl]
        _ = GeneralLinearGroup.scalar (Fin 3) (l * μ) * diagUnits 1 s t := by
            rw [map_mul, mul_assoc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ
              (diagUnits 1 s t)).eq, ← mul_assoc]
    rw [h1]
    exact isDiag_scalar_mul_diagUnits _ _ _
  have hdiag : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    fun a ha y hy => hdiagR y (mk_mem_range_pglHomP ha hy)
  set τu : Kˣ := Units.mk0 τ hτ0 with hτu
  have hτu3 : τu ∈ rootsOfUnity 3 K := by
    rw [mem_rootsOfUnity]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hτu, Units.val_mk0, hτ, Units.val_one])
  obtain ⟨y₀, hy₀D, l₀, hy₀⟩ := hall τu hτu3 (τu ^ 2) (pow_mem hτu3 2)
  obtain ⟨hy₀R, hy₀H⟩ := (hmemD y₀).mp hy₀D
  obtain ⟨a₀, ha₀, hya₀⟩ := exists_isPGLAtP_of_mk_mem hy₀H hy₀R
  set d₀ : Fin 3 → K := fun i => (l₀ : K) * (![1, τ, τ ^ 2] : Fin 3 → K) i with hd₀def
  have hd₀ : Function.Injective d₀ := injective_smul_tau hτ hτ1 l₀.ne_zero
  have hd₀0 : ∀ i, d₀ i ≠ 0 := by
    intro i
    refine mul_ne_zero l₀.ne_zero ?_
    fin_cases i
    · exact one_ne_zero
    · exact hτ0
    · exact pow_ne_zero 2 hτ0
  have hy₀D' : ((g⁻¹ * y₀ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d₀ := by
    rw [hy₀, Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, coe_diagUnits]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d₀, τu, Matrix.diagonal]
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hcube : ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
    intro a ha y hy i j
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPiP hK hq (hA.1.2 a ha) hy)
    have h3 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [← Units.val_pow_eq_pow_val, e1, ← hℓ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ g⁻¹).eq, inv_mul_cancel_right,
        coe_scalar_eq_smul]
    have hD := hdiag a ha y hy
    have hk : ∀ k, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = ℓ := by
      intro k
      have := congrFun (congrFun h3 k) k
      rw [← hD.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
      simpa using this
    rw [hk i, hk j]
  have hcent : ∀ m (hm : m ∈ L) (s : GL (Fin 3) K),
      ((e ⟨m, hm⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk s →
      ((g⁻¹ * s * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag →
      ∀ a ∈ A, a * m = m * a := by
    intro m hm s hms hsD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := ‹L.Normal›.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAtP hy hm hmL
    have hc : y * s = s * y := by
      have hc := commute_of_isDiag (hdiag a ha y hy) hsD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * s * g) = (g⁻¹ * s * g) * (g⁻¹ * y * g) :=
        Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hc)
      apply hψinj
      rw [hψmul, hψmul, hc']
    rw [hms, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right, ← hms] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ := e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  let ρ : Equiv.Perm (Fin 3) →* ProjGenLinGroup (Fin 3) K :=
    (ProjGenLinGroup.mk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K).comp
      ((MulAut.conj g).toMonoidHom.comp permGL)
  have hρ : ∀ σ, ρ σ = ProjGenLinGroup.mk (g * permGL σ * g⁻¹) := fun σ => rfl
  have hρmem : ∀ σ, ρ σ ∈ projImage (slPi π 3 (p ^ f) K) := by
    intro σ
    obtain ⟨s, hs, hsσ⟩ := exists_slPi_mk_permGL hK hgH σ
    exact ⟨s, hs, by rw [hρ, hsσ]⟩
  let Θ : Equiv.Perm (Fin 3) →* H :=
    L.subtype.comp (e.symm.toMonoidHom.comp (ρ.codRestrict _ hρmem))
  have hΘL : ∀ σ, Θ σ ∈ L := fun σ => (e.symm _).2
  have heΘ : ∀ σ, ((e ⟨Θ σ, hΘL σ⟩ : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (g * permGL σ * g⁻¹) := by
    intro σ
    have : (⟨Θ σ, hΘL σ⟩ : L) = e.symm (ρ.codRestrict _ hρmem σ) := rfl
    rw [this, MulEquiv.apply_symm_apply]
    rfl
  refine nonempty_autIn_equiv_perm Θ hΘL ?_ ?_ ?_
  ·
    intro σ a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have htL : Θ σ ∈ L := hΘL σ
    have ht'L : a * (Θ σ)⁻¹ * a⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (L.inv_mem htL) a
    have hmL : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ L := L.mul_mem htL ht'L
    set C : GL (Fin 3) K := (g * permGL σ * g⁻¹) * y * (g * permGL σ * g⁻¹)⁻¹ * y⁻¹ with hC
    have hem : ((e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk C := by
      have e1 : (⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨Θ σ, htL⟩ * ⟨a * (Θ σ)⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAtP hy (L.inv_mem htL) ht'L]
      have e2 : (⟨(Θ σ)⁻¹, L.inv_mem htL⟩ : L) = (⟨Θ σ, htL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv, heΘ σ, hC]
      simp only [map_mul, map_inv]
      group
    have hψC : g⁻¹ * C * g = permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      rw [hC]
      group
    obtain ⟨hCD, hC3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψC] at hCD hC3
    have hmA : Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL C hem hCD a' ha'
      have hC1 : C ^ 3 = 1 := by
        have e1 : (g⁻¹ * C * g) ^ 3 = g⁻¹ * C ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hC3
        calc C ^ 3 = g * (g⁻¹ * C ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hC3]; group
      have h1 : (e ⟨Θ σ * (a * (Θ σ)⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hem, ← map_pow, hC1, map_one, Subgroup.coe_one]
      rw [← map_pow, map_eq_one_iff _ e.injective] at h1
      exact congrArg Subtype.val h1
    have : Θ σ * a * (Θ σ)⁻¹ = (Θ σ * (a * (Θ σ)⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  ·
    intro σ hσ
    have key : ∀ σ : Equiv.Perm (Fin 3), (∃ k, σ k = k) ∨ σ ^ 3 = 1 := by decide
    rcases key σ with ⟨k, hk⟩ | h3
    · have h1 := hσ a₀ ha₀
      have ha₀L : a₀ * Θ σ * a₀⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (hΘL σ) a₀
      have h2 := coe_e_conj_of_isPGLAtP hya₀ (hΘL σ) ha₀L
      have h3 : (⟨a₀ * Θ σ * a₀⁻¹, ha₀L⟩ : L) = ⟨Θ σ, hΘL σ⟩ := Subtype.ext (by
        change a₀ * Θ σ * a₀⁻¹ = Θ σ
        rw [← h1]
        group)
      rw [h3, heΘ] at h2
      have h4 : (g * permGL σ * g⁻¹)⁻¹ * (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹) ∈
          Subgroup.center (GL (Fin 3) K) := by
        rw [← ProjGenLinGroup.mk_eq_one]
        have : ProjGenLinGroup.mk ((g * permGL σ * g⁻¹)⁻¹ *
            (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹)) =
            (ProjGenLinGroup.mk (g * permGL σ * g⁻¹))⁻¹ *
              (ProjGenLinGroup.mk y₀ * ProjGenLinGroup.mk (g * permGL σ * g⁻¹) *
                (ProjGenLinGroup.mk y₀)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [this, ← h2, inv_mul_cancel]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h4
      obtain ⟨μ, hμ⟩ := h4
      have h5 : y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) μ * (g * permGL σ * g⁻¹) := by
        rw [← (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ (g * permGL σ * g⁻¹)).eq, hμ]
        group
      have h6 : (g⁻¹ * y₀ * g) * permGL σ =
          GeneralLinearGroup.scalar (Fin 3) μ * (permGL σ * (g⁻¹ * y₀ * g)) := by
        calc (g⁻¹ * y₀ * g) * permGL σ =
            g⁻¹ * (y₀ * (g * permGL σ * g⁻¹) * y₀⁻¹) * g * (g⁻¹ * y₀ * g) := by group
          _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * (g * permGL σ * g⁻¹)) * g *
              (g⁻¹ * y₀ * g) := by rw [h5]
          _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g * (permGL σ * (g⁻¹ * y₀ * g)) := by
              group
          _ = GeneralLinearGroup.scalar (Fin 3) μ * (permGL σ * (g⁻¹ * y₀ * g)) := by
              rw [(CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ g⁻¹).eq,
                inv_mul_cancel_right]
      apply eq_one_of_diagonal_mul_permGL hd₀ hd₀0 (μ := (μ : K)) _ hk
      have h7 := congrArg (fun Z : GL (Fin 3) K => (Z : Matrix (Fin 3) (Fin 3) K)) h6
      simp only [Units.val_mul, hy₀D', coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul] at h7
      exact h7
    · have hΘA : Θ σ ∈ A := by
        refine mem_of_maximal_of_commute hA ?_ fun a ha => (hσ a ha).symm
        rw [← map_pow, h3, map_one]
      have hs := sign_eq_one_of_pow_three σ h3
      have hP := permGL_mem_glPi (p := p) (f := f) hK σ
      have hsl : g * permGL σ * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
        refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hgH hP) (inv_mem hgH), ?_⟩
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_permGL_eq_sign, hs,
          mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.det_one]
        simp
      have hyΘ : IsPGLAtP e (Θ σ) (g * permGL σ * g⁻¹) :=
        isPGLAtP_of_mem e hπ (hΘL σ) hsl (heΘ σ)
      have hD := hdiag _ hΘA _ hyΘ
      apply eq_one_of_permGL_isDiag (K := K)
      have : g⁻¹ * (g * permGL σ * g⁻¹) * g = permGL σ := by group
      rw [this] at hD
      exact hD
  ·
    intro l hl hlN
    obtain ⟨s₀, hs₀, hs₀l⟩ := (e ⟨l, hl⟩).2
    have hel : ((e ⟨l, hl⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk s₀ := hs₀l.symm
    set X : GL (Fin 3) K := g⁻¹ * s₀ * g with hX
    set Hd : Subgroup (GL (Fin 3) K) := (R.comap
      (QuotientGroup.mk' (StatedScalars (Fin 3) K))).map (MulAut.conj g⁻¹).toMonoidHom with hHd
    have hmemHd : ∀ u, u ∈ Hd ↔ ∃ y : GL (Fin 3) K,
        (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R ∧ g⁻¹ * y * g = u := by
      intro u
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        change g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹
        rw [inv_inv]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y, hy, ?_⟩
        change g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g
        rw [inv_inv]
    have hHdiag : ∀ u ∈ Hd, (u : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      intro u hu
      obtain ⟨y, hy, rfl⟩ := (hmemHd u).mp hu
      exact hdiagR y hy
    have hsep : ∀ i j : Fin 3, i ≠ j →
        ∃ u ∈ Hd, (u : Matrix (Fin 3) (Fin 3) K) i i ≠ (u : Matrix (Fin 3) (Fin 3) K) j j := by
      intro i j hij
      refine ⟨g⁻¹ * y₀ * g, (hmemHd _).mpr ⟨y₀, mk_mem_range_pglHomP ha₀ hya₀, rfl⟩, ?_⟩
      rw [hy₀D', Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      exact fun h => hij (hd₀ h)
    have hlinv : l⁻¹ ∈ L := L.inv_mem hl
    have hel' : ((e ⟨l⁻¹, hlinv⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s₀⁻¹ := by
      have : (⟨l⁻¹, hlinv⟩ : L) = (⟨l, hl⟩ : L)⁻¹ := rfl
      rw [this, map_inv, Subgroup.coe_inv, hel, map_inv]
    have hnorm : ∀ u ∈ Hd, X⁻¹ * u * X ∈ Hd := by
      intro u hu
      obtain ⟨y, ⟨⟨a, ha⟩, hay⟩, rfl⟩ := (hmemHd u).mp hu
      obtain ⟨ya, hya⟩ := hpgl a ha
      rw [pglHomP_apply ⟨a, ha⟩ hya, QuotientGroup.eq] at hay
      obtain ⟨μ, hμ⟩ := hay
      have hyya : y = ya * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
      have hla : l⁻¹ * a * l ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) a).mp ha
        rwa [inv_inv] at this
      have hy' : IsPGLAtP e (l⁻¹ * a * l) (s₀⁻¹ * ya * s₀) :=
        isPGLAtP_mul e (isPGLAtP_mul e (isPGLAtP_of_mem e hπ hlinv (inv_mem hs₀) hel') hya)
          (isPGLAtP_of_mem e hπ hl hs₀ hel)
      refine (hmemHd _).mpr ⟨s₀⁻¹ * y * s₀, ?_, by rw [hX]; group⟩
      have hmk : ((s₀⁻¹ * y * s₀ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) =
          ((s₀⁻¹ * ya * s₀ : GL (Fin 3) K) : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) := by
        rw [QuotientGroup.eq]
        refine ⟨μ⁻¹, ?_⟩
        rw [hyya]
        have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ⁻¹ s₀⁻¹).eq
        calc GeneralLinearGroup.scalar (Fin 3) μ⁻¹ =
            s₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * s₀ := by
              rw [hc, inv_mul_cancel_right]
          _ = (s₀⁻¹ * (ya * GeneralLinearGroup.scalar (Fin 3) μ) * s₀)⁻¹ *
              (s₀⁻¹ * ya * s₀) := by
              rw [map_inv]
              group
      rw [hmk]
      exact mk_mem_range_pglHomP hla hy'
    obtain ⟨σ₀, hσ₀⟩ := exists_monomial_of_normalizes hHdiag hsep hnorm
    obtain ⟨σ, hσ⟩ := exists_perm_of_isMonomialWith hσ₀
    refine ⟨σ, fun a ha => ?_⟩
    have hmL : (Θ σ)⁻¹ * l ∈ L := L.mul_mem (L.inv_mem (hΘL σ)) hl
    have hem : ((e ⟨(Θ σ)⁻¹ * l, hmL⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk ((g * permGL σ * g⁻¹)⁻¹ * s₀) := by
      have e1 : (⟨(Θ σ)⁻¹ * l, hmL⟩ : L) = (⟨Θ σ, hΘL σ⟩ : L)⁻¹ * ⟨l, hl⟩ := rfl
      rw [e1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, heΘ σ, hel]
      simp only [map_mul, map_inv]
    have hmD : ((g⁻¹ * ((g * permGL σ * g⁻¹)⁻¹ * s₀) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := by
      have e2 : g⁻¹ * ((g * permGL σ * g⁻¹)⁻¹ * s₀) * g = (permGL σ)⁻¹ * X := by
        rw [hX]
        group
      rw [e2]
      exact hσ
    have hc := hcent _ hmL _ hem hmD a ha
    calc l * a * l⁻¹ = Θ σ * (((Θ σ)⁻¹ * l) * a) * l⁻¹ := by group
      _ = Θ σ * (a * ((Θ σ)⁻¹ * l)) * l⁻¹ := by rw [← hc]
      _ = Θ σ * a * (Θ σ)⁻¹ := by group

end Res424Six

end CFSG.RankThree.PartTwo.Sec4
