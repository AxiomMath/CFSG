module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofLinear
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofFourData
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.SEITZQ1
open CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof (xr eq_top_of_xr10_xr12 diagSL_mul_xr10
  diagSL_mul_xr12 conj_eq_of_mul_eq)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K]

variable {p f : ℕ}

theorem torusC_mem_invSet142 [Finite K] (hπ : true = false → UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0) {cβ c : GL (Fin 3) K}
    (hcβ : cβ ∈ glPi true 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K) {ν : K}
    (hc3 : (c : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1) (hν : ¬ ∃ μ : K, μ ^ 3 = ν) {s₁ s₂ : Kˣ}
    (h1 : cβ * c * cβ⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s₁ * c)
    (h2 : diagTau hτ * c * (diagTau hτ)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s₂ * c) :
    (torusSL c).map (rhoSL (p ^ f) K) ∈
      invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) := by
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (c : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    eq_bot_or_eq_top_of_invariant (fun μ hμ => hν ⟨μ, hμ⟩) hc3 hW
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  refine ⟨not_three_dvd_card_of_pow_three ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ hg3
    have hs3 : SpecialLinearGroup.toGL g ^ 3 ∈ StatedScalars (Fin 3) K := by
      have e := congrArg Subtype.val hg3
      rw [Subgroup.coe_pow, coe_rhoSL, OneMemClass.coe_one, ← map_pow] at e
      exact mk_eq_one_iff_mem_statedScalars.mp e
    have hsZ : SpecialLinearGroup.toGL g ∈ StatedScalars (Fin 3) K := by
      by_contra hsZ
      refine Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 g.2 hs3 hsZ ?_ hirr
      exact Units.ext ((mem_torusSL.mp hg).trans rfl)
    apply Subtype.ext
    rw [coe_rhoSL, OneMemClass.coe_one, mk_eq_one_iff_mem_statedScalars]
    exact hsZ
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨conjUnit cβ g, conjUnit_mem_torusSL h1 hg, rhoSL_conjUnit hπ hcβ g⟩
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨conjUnit (diagTau hτ) g, conjUnit_mem_torusSL h2 hg, rhoSL_conjUnit hπ hd g⟩

theorem mem_four_of_card [Finite K] (hcard : Nat.card K = 4) {τ : K} (hτ : τ ^ 2 + τ + 1 = 0)
    (h2 : (2 : K) = 0) (x : K) : x = 0 ∨ x = 1 ∨ x = τ ∨ x = τ + 1 := by
  classical
  have := Fintype.ofFinite K
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    have : (3 : K) = 0 := by linear_combination hτ
    have h1 : (1 : K) = 0 := by linear_combination this - h2
    exact one_ne_zero h1
  have hτ1' : τ + 1 ≠ 0 := by
    intro h
    apply hτ1
    linear_combination h - h2
  have hτ1'' : τ + 1 ≠ 1 := fun h => hτ0 (by linear_combination h)
  have hτ1''' : τ + 1 ≠ τ := fun h => one_ne_zero (by linear_combination h)
  set s : Finset K := {0, 1, τ, τ + 1} with hs
  have hscard : s.card = 4 := by
    rw [hs, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair hτ1'''.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hτ1.symm, hτ1''.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨zero_ne_one, hτ0.symm, hτ1'.symm⟩
  have huniv : s = Finset.univ := Finset.eq_univ_of_card s (by
    rw [hscard, ← Nat.card_eq_fintype_card, hcard])
  have hx : x ∈ s := huniv ▸ Finset.mem_univ x
  simpa [hs] using hx

variable [CharP K 2]

@[expose] noncomputable def slOfF4 {τ : K} (hτ : τ ^ 2 + τ + 1 = 0) (A : F4M)
    (hA : f4MDet A = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨f4MEv τ A, by rw [f4MEv_det hτ, hA]; rfl⟩

theorem mem_of_wordOK {τ : K} (hτ : τ ^ 2 + τ + 1 = 0) {β' : Fin 4} {L : Fin 5 → F4M}
    {I : Fin 5 → Fin 3} {P : Fin 5 → F4M} {target : F4M} (hw : WordOK β' L I P target)
    {K₁ : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hT : ∀ i, ∀ y : SpecialLinearGroup (Fin 3) K,
      f4MEv τ (f4Cj β' (I i)) * (y : Matrix (Fin 3) (Fin 3) K) =
        (y : Matrix (Fin 3) (Fin 3) K) * f4MEv τ (f4Cj β' (I i)) → y ∈ K₁)
    (ht : f4MDet target = 1) : slOfF4 hτ target ht ∈ K₁ := by
  obtain ⟨hdet, hcomm, hP0, hPs, hP4, hdetP⟩ := hw
  have hL : ∀ i, slOfF4 hτ (L i) (hdet i) ∈ K₁ := by
    intro i
    refine hT i _ ?_
    change f4MEv τ (f4Cj β' (I i)) * f4MEv τ (L i) = f4MEv τ (L i) * f4MEv τ (f4Cj β' (I i))
    rw [← f4MEv_mul hτ, ← f4MEv_mul hτ, hcomm i]
  have hPmem : ∀ i, slOfF4 hτ (P i) (hdetP i) ∈ K₁ := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have e : slOfF4 hτ (P 0) (hdetP 0) = slOfF4 hτ (L 0) (hdet 0) := by
        apply Subtype.ext
        change f4MEv τ (P 0) = f4MEv τ (L 0)
        rw [hP0]
      rw [e]
      exact hL 0
    | succ i ih =>
      have e : slOfF4 hτ (P i.succ) (hdetP i.succ) =
          slOfF4 hτ (P i.castSucc) (hdetP i.castSucc) * slOfF4 hτ (L i.succ) (hdet i.succ) := by
        apply Subtype.ext
        change f4MEv τ (P i.succ) = f4MEv τ (P i.castSucc) * f4MEv τ (L i.succ)
        rw [← f4MEv_mul hτ, hPs i]
      rw [e]
      exact K₁.mul_mem ih (hL i.succ)
  have e : slOfF4 hτ target ht = slOfF4 hτ (P 4) (hdetP 4) := by
    apply Subtype.ext
    change f4MEv τ target = f4MEv τ (P 4)
    rw [hP4]
  rw [e]
  exact hPmem 4

theorem slOfF4_tv {τ : K} (hτ : τ ^ 2 + τ + 1 = 0) {i j : Fin 3} (hij : i ≠ j)
    (ht : f4MDet (f4MTv i j 1) = 1) :
    slOfF4 hτ (f4MTv i j 1) ht = SpecialLinearGroup.transvection hij 1 := by
  apply Subtype.ext
  change f4MEv τ (f4MTv i j 1) = (SpecialLinearGroup.transvection hij (1 : K) :
    Matrix (Fin 3) (Fin 3) K)
  rw [f4MEv_tv hij, SpecialLinearGroup.transvection_coe]
  rfl

theorem eq_top_of_four [Finite K] (hcard : Nat.card K = 4)
    {K₁ : Subgroup (SpecialLinearGroup (Fin 3) K)} {τ : K} (hτ : τ ^ 2 + τ + 1 = 0) {β' : Fin 4}
    (hβ' : β' = 2 ∨ β' = 3)
    (hT : ∀ j : Fin 3, ∀ y : SpecialLinearGroup (Fin 3) K,
      f4MEv τ (f4Cj β' j) * (y : Matrix (Fin 3) (Fin 3) K) =
        (y : Matrix (Fin 3) (Fin 3) K) * f4MEv τ (f4Cj β' j) → y ∈ K₁)
    (hD : ∀ h : 1 * τ * τ ^ 2 = 1, diagSL 1 τ (τ ^ 2) h ∈ K₁) {gα : GL (Fin 3) K}
    (hgα : (gα : Matrix (Fin 3) (Fin 3) K) = heisC (f4Ev τ β'))
    (hinv : ∀ x ∈ K₁, conjUnit gα x ∈ K₁) : K₁ = ⊤ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ3 : τ ^ 3 = 1 := by linear_combination (τ - 1) * hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hτsq : τ ^ 2 = τ + 1 := by linear_combination hτ - (τ + 1) * h2
  have hD1 : (1 : K) * τ * τ ^ 2 = 1 := by linear_combination hτ3
  have hDm := hD hD1
  have ht10 : f4MDet (f4MTv 1 0 1) = 1 := by decide
  have ht12 : f4MDet (f4MTv 1 2 1) = 1 := by decide
  have hT' : ∀ (I : Fin 5 → Fin 3) i, ∀ y : SpecialLinearGroup (Fin 3) K,
      f4MEv τ (f4Cj β' (I i)) * (y : Matrix (Fin 3) (Fin 3) K) =
        (y : Matrix (Fin 3) (Fin 3) K) * f4MEv τ (f4Cj β' (I i)) → y ∈ K₁ :=
    fun I i => hT (I i)
  have hx10 : xr (by decide : (1 : Fin 3) ≠ 0) (1 : K) ∈ K₁ := by
    rw [xr, ← slOfF4_tv hτ (by decide) ht10]
    rcases hβ' with rfl | rfl
    · exact mem_of_wordOK hτ wordOK_A10 (hT' _) ht10
    · exact mem_of_wordOK hτ wordOK_B10 (hT' _) ht10
  have hx12 : xr (by decide : (1 : Fin 3) ≠ 2) (1 : K) ∈ K₁ := by
    rw [xr, ← slOfF4_tv hτ (by decide) ht12]
    rcases hβ' with rfl | rfl
    · exact mem_of_wordOK hτ wordOK_A12 (hT' _) ht12
    · exact mem_of_wordOK hτ wordOK_B12 (hT' _) ht12
  have hsc10 : ∀ c : K, xr (by decide : (1 : Fin 3) ≠ 0) c ∈ K₁ →
      xr (by decide : (1 : Fin 3) ≠ 0) (τ * c) ∈ K₁ := by
    intro c hc
    have e := conj_eq_of_mul_eq (diagSL_mul_xr10 1 τ (τ ^ 2) hD1 c)
    rw [div_one] at e
    rw [← e]
    exact K₁.mul_mem (K₁.mul_mem hDm hc) (K₁.inv_mem hDm)
  have hsc12 : ∀ c : K, xr (by decide : (1 : Fin 3) ≠ 2) c ∈ K₁ →
      xr (by decide : (1 : Fin 3) ≠ 2) (τ ^ 2 * c) ∈ K₁ := by
    intro c hc
    have e := conj_eq_of_mul_eq (diagSL_mul_xr12 1 τ (τ ^ 2) hD1 c)
    have hq : τ / τ ^ 2 = τ ^ 2 := by
      rw [div_eq_iff (pow_ne_zero 2 hτ0)]
      linear_combination (-τ) * hτ3
    rw [hq] at e
    rw [← e]
    exact K₁.mul_mem (K₁.mul_mem hDm hc) (K₁.inv_mem hDm)
  have hmem := mem_four_of_card hcard hτ h2
  have h10 : ∀ c : K, xr (by decide : (1 : Fin 3) ≠ 0) c ∈ K₁ := by
    intro c
    rcases hmem c with h | h | h | h <;> rw [h]
    · rw [Sec19.Item19Res5Proof.xr_zero]; exact K₁.one_mem
    · exact hx10
    · simpa using hsc10 1 hx10
    · have := hsc10 τ (by simpa using hsc10 1 hx10)
      rwa [← sq, hτsq] at this
  have h12 : ∀ c : K, xr (by decide : (1 : Fin 3) ≠ 2) c ∈ K₁ := by
    intro c
    rcases hmem c with h | h | h | h <;> rw [h]
    · rw [Sec19.Item19Res5Proof.xr_zero]; exact K₁.one_mem
    · exact hx12
    · have := hsc12 (τ ^ 2) (by simpa using hsc12 1 hx12)
      rwa [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, hτ3, one_mul] at this
    · have := hsc12 1 hx12
      rwa [mul_one, hτsq] at this
  have hβ0 : f4Ev τ β' ≠ 0 := by
    rcases hβ' with rfl | rfl
    · exact hτ0
    · intro h
      change τ + 1 = 0 at h
      exact one_ne_zero (by linear_combination hτ - τ * h)
  exact eq_top_of_xr10_xr12 hβ0 hgα hinv h10 h12

omit [CharP K 2] in
theorem sSup_invSet142_eq_top_of [Finite K] (hπ : true = false → UnitaryFieldData p f K)
    [Group.IsPerfect (projImage (slPi true 3 (p ^ f) K))] {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {β : K} {cβ : GL (Fin 3) K} (hcβ : cβ ∈ glPi true 3 (p ^ f) K)
    (hd : diagTau hτ ∈ glPi true 3 (p ^ f) K)
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β)
    (hgen : ∀ K₁ : Subgroup (SpecialLinearGroup (Fin 3) K),
      (∀ X ∈ invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd),
        X.comap (rhoSL (p ^ f) K) ≤ K₁) →
      (∀ h : 1 * τ * τ ^ 2 = 1, diagSL 1 τ (τ ^ 2) h ∈ K₁) →
      (∀ x ∈ K₁, conjUnit cβ x ∈ K₁) → K₁ = ⊤) :
    sSup (invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd)) = ⊤ := by
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  set σ := Res8Hess.conjM' hπ hcβ with hσ
  set N := sSup (invSet142 σ (Res8Hess.conjM' hπ hd)) with hN
  have hτ' : τ * τ ^ 2 * 1 = 1 := by linear_combination hτ
  set D := rhoSL (p ^ f) K (diagSL τ (τ ^ 2) 1 hτ') with hD
  have hDm : SpecialLinearGroup.toGL (diagSL τ (τ ^ 2) 1 hτ') = diagTau hτ := by
    apply Units.ext
    rw [coe_diagTau]
    rfl
  have hconjD : Res8Hess.conjM' hπ hd = MulAut.conj D := by
    ext m
    rw [Res8Hess.coe_conjM', MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hD, coe_rhoSL, hDm]
  have hσD : σ D = D := by
    apply Subtype.ext
    rw [hσ, Res8Hess.coe_conjM', hD, coe_rhoSL, hDm, ← map_inv, ← map_mul, ← map_mul,
      ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 (τ ^ 2)⁻¹ (inv_ne_zero (pow_ne_zero 2 hτ0)), Units.ext ?_⟩
    have e := heisC_mul_diagTau hτ β
    rw [← hcβm] at e
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0, e, Matrix.smul_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one, Matrix.smul_mul, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero 2 hτ0), one_smul]
  set Y := N ⊔ Subgroup.zpowers D with hY
  set K₁ := Y.comap (rhoSL (p ^ f) K) with hK₁
  have hinvN := map_sSup_invSet142_le (σ := σ) (τ := Res8Hess.conjM' hπ hd)
  have hXK : ∀ X ∈ invSet142 σ (Res8Hess.conjM' hπ hd), X.comap (rhoSL (p ^ f) K) ≤ K₁ :=
    fun X hX => Subgroup.comap_mono ((le_sSup hX).trans le_sup_left)
  have hD1 : ∀ h : 1 * τ * τ ^ 2 = 1, diagSL 1 τ (τ ^ 2) h ∈ K₁ := by
    intro h
    have e : rhoSL (p ^ f) K (diagSL 1 τ (τ ^ 2) h) = D := by
      apply Subtype.ext
      rw [hD, coe_rhoSL, coe_rhoSL, ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 τ hτ0, Units.ext ?_⟩
      change (diagSL 1 τ (τ ^ 2) h : Matrix (Fin 3) (Fin 3) K) *
          ((Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) = (diagSL τ (τ ^ 2) 1 hτ' : Matrix (Fin 3) (Fin 3) K)
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination hτ
    change rhoSL (p ^ f) K (diagSL 1 τ (τ ^ 2) h) ∈ Y
    rw [e]
    exact le_sup_right (a := N) (Subgroup.mem_zpowers D)
  have hinv : ∀ x ∈ K₁, conjUnit cβ x ∈ K₁ := by
    intro x hx
    change rhoSL (p ^ f) K (conjUnit cβ x) ∈ Y
    rw [rhoSL_conjUnit hπ hcβ]
    have hYσ : Y.map σ.toMonoidHom ≤ Y := by
      rw [hY, Subgroup.map_sup]
      refine sup_le (hinvN.1.trans le_sup_left) ?_
      rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hσD]
      exact le_sup_right
    exact hYσ ⟨_, hx, rfl⟩
  have hK₁top : K₁ = ⊤ := hgen K₁ hXK hD1 hinv
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨g, rfl⟩ := rhoSL_surjective (p ^ f) m
    have : g ∈ K₁ := hK₁top ▸ Subgroup.mem_top g
    exact this
  have hND : N.map (MulAut.conj D).toMonoidHom ≤ N := by
    rw [← hconjD]
    exact hinvN.2
  exact eq_top_of_sup_zpowers hND hYtop

omit [CharP K 2] in
theorem conj_relations {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) {β : K} {cβ : GL (Fin 3) K}
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) :
    cβ * diagTau hτ * cβ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ ∧
      diagTau hτ * cβ * (diagTau hτ)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * cβ := by
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
        Matrix.GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  constructor
  · have e : cβ * diagTau hτ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (diagTau hτ * cβ) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hcβm, heisC_mul_diagTau hτ β,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_pow_eq_pow_val,
        Units.val_mk0]
    calc cβ * diagTau hτ * cβ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (diagTau hτ * cβ) *
          cβ⁻¹ := by rw [e]
      _ = _ := by group
  · have e : diagTau hτ * cβ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cβ * diagTau hτ) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hcβm, diagTau_mul_heisC hτ β,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_mk0]
    calc diagTau hτ * cβ * (diagTau hτ)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cβ * diagTau hτ) *
          (diagTau hτ)⁻¹ := by rw [e]
      _ = _ := by group

theorem ks142L3PGLGenStdFour : KS142L3PGLGenStdFour := by
  intro K _ hπ hK hperf τ hτ hτ1 β cβ hcβ hd hcβm hβ
  have := hK.finite
  have := Fintype.ofFinite K
  have hcard : Nat.card K = 4 := by rw [hK.card]; rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hcard]; rfl)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hω : τ ^ 2 + τ + 1 = 0 := by
    have h1 : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hτ1)
  have hτsq : τ ^ 2 = τ + 1 := by linear_combination hω - (τ + 1) * h2
  have h3 : (3 : K) ≠ 0 := by
    intro h
    exact one_ne_zero (by linear_combination h - h2)
  obtain ⟨β', hβ', hββ'⟩ : ∃ β' : Fin 4, (β' = 2 ∨ β' = 3) ∧ f4Ev τ β' = β := by
    rcases mem_four_of_card hcard hω h2 β with h | h | h | h
    · exact absurd ⟨0, by rw [h]; ring⟩ hβ
    · exact absurd ⟨1, by rw [h]; ring⟩ hβ
    · exact ⟨2, Or.inl rfl, h.symm⟩
    · exact ⟨3, Or.inr rfl, h.symm⟩
  have hchk := f4Cj_checks β' (by rcases hβ' with rfl | rfl <;> decide)
  obtain ⟨hC1, hC2, hcube⟩ := hchk
  have hC0 : f4MEv τ (f4Cj β' 0) = (cβ : Matrix (Fin 3) (Fin 3) K) := by
    rw [hcβm, ← hββ']
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hDt : f4MEv τ f4Dt = ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [coe_diagTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [f4MEv, f4Dt, f4Ev, hτsq]
  set c : Fin 3 → GL (Fin 3) K := ![cβ, cβ * diagTau hτ, cβ * diagTau hτ * diagTau hτ] with hc
  have hcm : ∀ j, ((c j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = f4MEv τ (f4Cj β' j) := by
    intro j
    fin_cases j
    · exact hC0.symm
    · change ((cβ * diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        f4MEv τ (f4Cj β' 1)
      rw [hC1, f4MEv_mul hω, hC0, hDt, Units.val_mul]
    · change ((cβ * diagTau hτ * diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        f4MEv τ (f4Cj β' 2)
      rw [hC2, f4MEv_mul hω, hC1, f4MEv_mul hω, hC0, hDt, Units.val_mul, Units.val_mul]
  have hc3 : ∀ j, ((c j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = β • 1 := by
    intro j
    rw [hcm, pow_three, ← mul_assoc, ← f4MEv_mul hω, ← f4MEv_mul hω, hcube j, ← hββ']
    ext i k
    fin_cases i <;> fin_cases k <;> simp [f4MEv, f4Ev]
  obtain ⟨hCD, hDC⟩ := conj_relations hτ hτ0 hcβm
  set z := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) with hz
  set w := Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) with hw
  have hzc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ x).eq
  have hwc : ∀ x : GL (Fin 3) K, x * w = w * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar _ x).eq
  set dd := diagTau hτ with hdd
  have hCD' : cβ * dd = z * dd * cβ := by
    calc cβ * dd = cβ * dd * cβ⁻¹ * cβ := by group
      _ = z * dd * cβ := by rw [hCD]
  have hDC' : dd * cβ = w * cβ * dd := by
    calc dd * cβ = dd * cβ * dd⁻¹ * dd := by group
      _ = w * cβ * dd := by rw [hDC]
  have hrel : ∀ j, (∃ s₁ : Kˣ, cβ * c j * cβ⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 3) s₁ * c j) ∧
      ∃ s₂ : Kˣ, dd * c j * dd⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s₂ * c j := by
    intro j
    fin_cases j
    · refine ⟨⟨1, by rw [map_one, one_mul]; change cβ * cβ * cβ⁻¹ = cβ; group⟩,
        ⟨Units.mk0 τ hτ0, hDC⟩⟩
    · refine ⟨⟨Units.mk0 τ hτ0 ^ 2, ?_⟩, ⟨Units.mk0 τ hτ0, ?_⟩⟩
      · change cβ * (cβ * dd) * cβ⁻¹ = z * (cβ * dd)
        calc cβ * (cβ * dd) * cβ⁻¹ = cβ * (cβ * dd * cβ⁻¹) := by group
          _ = cβ * (z * dd) := by rw [hCD]
          _ = z * (cβ * dd) := by rw [← mul_assoc, hzc cβ, mul_assoc]
      · change dd * (cβ * dd) * dd⁻¹ = w * (cβ * dd)
        calc dd * (cβ * dd) * dd⁻¹ = dd * cβ * dd⁻¹ * dd := by group
          _ = w * (cβ * dd) := by rw [hDC]; group
    · refine ⟨⟨Units.mk0 τ hτ0 ^ 2 * Units.mk0 τ hτ0 ^ 2, ?_⟩, ⟨Units.mk0 τ hτ0, ?_⟩⟩
      · change cβ * (cβ * dd * dd) * cβ⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2 * Units.mk0 τ hτ0 ^ 2) *
            (cβ * dd * dd)
        rw [map_mul, ← hz]
        calc cβ * (cβ * dd * dd) * cβ⁻¹ = cβ * ((cβ * dd * cβ⁻¹) * (cβ * dd * cβ⁻¹)) := by
              group
          _ = cβ * ((z * dd) * (z * dd)) := by rw [hCD]
          _ = z * z * (cβ * dd * dd) := by
              have e1 : cβ * (z * dd * (z * dd)) = cβ * z * dd * z * dd := by group
              rw [e1, hzc cβ]
              have e2 : z * cβ * dd * z * dd = z * (cβ * dd * z) * dd := by group
              rw [e2, hzc (cβ * dd)]
              group
      · change dd * (cβ * dd * dd) * dd⁻¹ = w * (cβ * dd * dd)
        calc dd * (cβ * dd * dd) * dd⁻¹ = dd * cβ * dd⁻¹ * dd * dd := by group
          _ = w * (cβ * dd * dd) := by rw [hDC]; group
  refine sSup_invSet142_eq_top_of hπ hτ hτ1 hcβ hd hcβm ?_
  intro K₁ hXK hD1 hinv
  refine eq_top_of_four hcard hω hβ' ?_ hD1 (gα := cβ) (by rw [hcβm, hββ']) hinv
  intro j y hy
  obtain ⟨⟨s₁, h1⟩, ⟨s₂, h2'⟩⟩ := hrel j
  have hX := torusC_mem_invSet142 hπ hτ hτ1 h3 hcβ hd (hc3 j) hβ h1 h2'
  refine hXK _ hX ?_
  refine ⟨y, mem_torusSL.mpr ?_, rfl⟩
  rw [hcm]
  exact hy

end CFSG.RankThree.PartTwo.Sec14.L3PGL
