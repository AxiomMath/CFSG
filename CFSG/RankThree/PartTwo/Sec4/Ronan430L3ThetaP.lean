module

public import CFSG.RankThree.PartTwo.Sec4.Ronan430L3ThetaSL
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix Res417Frame Res424Six

variable {K : Type} [Field K]

section PSL

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [hLn : L.Normal] {p f : ℕ} {π : Bool}

theorem exists_mem_of_frameP (hK : PiField π p f K) (e : L ≃* projImage (slPi π 3 (p ^ f) K))
    {A : Subgroup H} (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {g : GL (Fin 3) K}
    (hdiag : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hcube : ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3)
    (σ : Equiv.Perm (Fin 3)) {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K) {μ : Kˣ}
    (hsσ : s = g * permGL σ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ) :
    ∃ n ∈ L, n ∈ Subgroup.normalizer (A : Set H) ∧
      ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∃ y', IsPGLAtP e (n * a * n⁻¹) y' ∧
        g⁻¹ * y' * g = permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hsc : ∀ (u : Kˣ) (X : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * X = X * GeneralLinearGroup.scalar (Fin 3) u :=
    fun u X => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u X).eq.symm
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hsconj : ∀ X : GL (Fin 3) K, g⁻¹ * (s * X * s⁻¹) * g =
      permGL σ * (g⁻¹ * X * g) * (permGL σ)⁻¹ := by
    intro X
    rw [hsσ]
    calc g⁻¹ * (g * permGL σ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * X *
          (g * permGL σ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ)⁻¹) * g =
        permGL σ * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * X) *
          (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * g * (permGL σ)⁻¹ := by group
      _ = permGL σ * g⁻¹ * (X * GeneralLinearGroup.scalar (Fin 3) μ) *
          (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * g * (permGL σ)⁻¹ := by rw [hsc]
      _ = _ := by group
  have hcent : ∀ m (hm : m ∈ L) (t : GL (Fin 3) K),
      ((e ⟨m, hm⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk t →
      ((g⁻¹ * t * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag →
      ∀ a ∈ A, a * m = m * a := by
    intro m hm t hmt htD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := hLn.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAtP hy hm hmL
    have hc : y * t = t * y := by
      have hc := commute_of_isDiag (hdiag a ha y hy) htD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * y * g) :=
        Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hc)
      apply hψinj
      rw [hψmul, hψmul, hc']
    rw [hmt, ← map_inv, ← map_mul, ← map_mul, hc, mul_inv_cancel_right, ← hmt] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ := e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  have hsP : ProjGenLinGroup.mk s ∈ projImage (slPi π 3 (p ^ f) K) := ⟨s, hs, rfl⟩
  set n : H := (e.symm ⟨ProjGenLinGroup.mk s, hsP⟩ : H) with hndef
  have hnL : n ∈ L := (e.symm _).2
  have hen : ((e ⟨n, hnL⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk s := by
    have : (⟨n, hnL⟩ : L) = e.symm ⟨ProjGenLinGroup.mk s, hsP⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hen' : ((e ⟨n⁻¹, L.inv_mem hnL⟩ : projImage (slPi π 3 (p ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s⁻¹ := by
    have e2 : (⟨n⁻¹, L.inv_mem hnL⟩ : L) = (⟨n, hnL⟩ : L)⁻¹ := rfl
    rw [e2, map_inv, Subgroup.coe_inv, hen, map_inv]
  have hns : IsPGLAtP e n s := isPGLAtP_of_mem e hπ hnL hs hen
  have hns' : IsPGLAtP e n⁻¹ s⁻¹ := isPGLAtP_of_mem e hπ (L.inv_mem hnL) (inv_mem hs) hen'
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have ht'L : a * n⁻¹ * a⁻¹ ∈ L := hLn.conj_mem _ (L.inv_mem hnL) a
    have hmL : n * (a * n⁻¹ * a⁻¹) ∈ L := L.mul_mem hnL ht'L
    set C : GL (Fin 3) K := s * y * s⁻¹ * y⁻¹ with hC
    have hem : ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk C := by
      have e1 : (⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨n, hnL⟩ * ⟨a * n⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAtP hy (L.inv_mem hnL) ht'L, hen,
        hen', hC]
      simp only [map_mul, map_inv]
      group
    have hψC : g⁻¹ * C * g =
        permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      rw [← hsconj]
      rw [hC]
      group
    obtain ⟨hCD, hC3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψC] at hCD hC3
    have hmA : n * (a * n⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL C hem hCD a' ha'
      have hC1 : C ^ 3 = 1 := by
        have e1 : (g⁻¹ * C * g) ^ 3 = g⁻¹ * C ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hC3
        calc C ^ 3 = g * (g⁻¹ * C ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hC3]; group
      have h1 : (e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hem, ← map_pow, hC1, map_one, Subgroup.coe_one]
      rw [← map_pow, map_eq_one_iff _ e.injective] at h1
      exact congrArg Subtype.val h1
    have : n * a * n⁻¹ = (n * (a * n⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  refine ⟨n, hnL, mem_normalizer_of_conj_mem hnA, fun a ha y hy => ?_⟩
  exact ⟨_, isPGLAtP_mul e (isPGLAtP_mul e hns hy) hns', hsconj y⟩

theorem exists_ratio_of_frameP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup H}
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {g : GL (Fin 3) K}
    (hdiag : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ∃ r : H → K × K, (∀ x ∈ A, ∀ y, IsPGLAtP e x y →
        r x = diagRatio ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∧
      (1 ∈ A → r 1 = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, r (x * y) = r x * r y) ∧
      ∀ x ∈ A, r x = 1 → x ∈ Subgroup.centralizer (L : Set H) := by
  classical
  have hsc : ∀ (u : Kˣ) (X : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * X = X * GeneralLinearGroup.scalar (Fin 3) u :=
    fun u X => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u X).eq.symm
  let r : H → K × K := fun x => if hx : x ∈ A then
    diagRatio ((g⁻¹ * (hpgl x hx).choose * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) else 1
  have hr : ∀ x ∈ A, ∀ y, IsPGLAtP e x y →
      r x = diagRatio ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx y hy
    have hr' : r x = diagRatio ((g⁻¹ * (hpgl x hx).choose * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := dif_pos hx
    rw [hr']
    obtain ⟨μ, hμ⟩ := isPGLAtP_inv_mul_mem hK hq (hpgl x hx).choose_spec hy
    have hyμ : y = (hpgl x hx).choose * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
    have : g⁻¹ * y * g = g⁻¹ * (hpgl x hx).choose * g * GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [hyμ, mul_assoc g⁻¹, mul_assoc, hsc μ g, ← mul_assoc, ← mul_assoc]
    rw [this, diagRatio_mul_scalar]
  refine ⟨r, hr, fun h1 => ?_, fun x hx x' hx' => ?_, fun x hx hx1 => ?_⟩
  · rw [hr 1 h1 1 (isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)), mul_one, inv_mul_cancel,
      Units.val_one]
    simp [diagRatio]
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy'⟩ := hpgl x' hx'
    rw [hr _ (A.mul_mem hx hx') _ (isPGLAtP_mul e hy hy'), hr x hx y hy, hr x' hx' y' hy']
    have : g⁻¹ * (y * y') * g = (g⁻¹ * y * g) * (g⁻¹ * y' * g) := by group
    rw [this, Units.val_mul]
    exact diagRatio_mul (hdiag x hx y hy) (hdiag x' hx' y' hy')
  · obtain ⟨y, hy⟩ := hpgl x hx
    rw [hr x hx y hy] at hx1
    have hD := hdiag x hx y hy
    have hD0 := apply_self_ne_zero_of_isDiag hD 0
    have h1 := eq_smul_one_of_diagRatio hD hD0 hx1
    apply mem_centralizer_of_isPGLAtP_scalar hy
    refine ⟨Units.mk0 _ hD0, ?_⟩
    have h2 : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) :=
      Units.ext (by rw [coe_scalar_eq_smul, Units.val_mk0]; exact h1)
    calc GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) =
        g * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) * g⁻¹ := by
          rw [← hsc, mul_inv_cancel_right]
      _ = y := by rw [← h2]; group

theorem exists_theta_of_frameP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
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
    ∃ P ∈ L, ∃ T ∈ L, P ∈ Subgroup.normalizer (A : Set H) ∧
      T ∈ Subgroup.normalizer (A : Set H) ∧ ∃ r : H → K × K, r 1 = 1 ∧
        (∀ x ∈ A, ∀ y ∈ A, r (x * y) = r x * r y) ∧
        (∀ x ∈ A, r x = 1 → x ∈ Subgroup.zpowers c) ∧
        (∀ x ∈ A, r (P * x * P⁻¹) = ((r x).2⁻¹, (r x).1 * (r x).2⁻¹)) ∧
        (∀ x ∈ A, r (T * x * T⁻¹) = ((r x).1⁻¹, (r x).2 * (r x).1⁻¹)) := by
  classical
  have := hK.finite
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
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
  obtain ⟨g, hgH, hform, -⟩ := isTypeC_conj_std hK hq hC
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
  have hmkP : ∀ σ : Equiv.Perm (Fin 3), ∃ s ∈ slPi π 3 (p ^ f) K, ∃ μ : Kˣ,
      s = g * permGL σ * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ := by
    intro σ
    obtain ⟨s, hs, hsσ⟩ := exists_slPi_mk_permGL hK hgH σ
    have h := QuotientGroup.eq.mp hsσ.symm
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨μ, hμ⟩ := h
    exact ⟨s, hs, μ, by rw [hμ]; group⟩
  obtain ⟨sP, hsP, μP, hsPσ⟩ := hmkP (finRotate 3)
  obtain ⟨sT, hsT, μT, hsTσ⟩ := hmkP (Equiv.swap (0 : Fin 3) 1)
  obtain ⟨P, hPL, hPN, hPy⟩ := exists_mem_of_frameP hK e hA hpgl hdiag hcube _ hsP hsPσ
  obtain ⟨T, hTL, hTN, hTy⟩ := exists_mem_of_frameP hK e hA hpgl hdiag hcube _ hsT hsTσ
  obtain ⟨r, hr, hr1, hrmul, hrker⟩ := exists_ratio_of_frameP hK hq e hpgl hdiag
  have hconjA : ∀ {n : H}, n ∈ Subgroup.normalizer (A : Set H) → ∀ x ∈ A, n * x * n⁻¹ ∈ A :=
    fun {n} hn x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  refine ⟨P, hPL, T, hTL, hPN, hTN, r, hr1 (Subgroup.one_mem _), hrmul,
    fun x hx hx1 => hAc ▸ ⟨hx, hrker x hx hx1⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy', hyy'⟩ := hPy x hx y hy
    have hD := hdiag x hx y hy
    rw [hr _ (hconjA hPN x hx) y' hy', hyy', permGL_conj_diagonal _ hD, hr x hx y hy]
    have hDd := hD.diagonal_diag.symm
    conv_rhs => rw [hDd]
    exact diagRatio_finRotate (d := fun j => ((g⁻¹ * y * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) j j) (apply_self_ne_zero_of_isDiag hD 0)
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy', hyy'⟩ := hTy x hx y hy
    have hD := hdiag x hx y hy
    rw [hr _ (hconjA hTN x hx) y' hy', hyy', permGL_conj_diagonal _ hD, hr x hx y hy]
    have hDd := hD.diagonal_diag.symm
    conv_rhs => rw [hDd]
    exact diagRatio_swap (d := fun j => ((g⁻¹ * y * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) j j) (apply_self_ne_zero_of_isDiag hD 0)

end PSL

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
