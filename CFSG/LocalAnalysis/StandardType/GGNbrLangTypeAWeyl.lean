module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeABstarDvd
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphField

public section

namespace CFSG.StandardType

namespace NbrLangTypeA

open Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d : ℕ} {F : Type} [Field F]

@[expose] def swapElt [CharP F 2] (k l : Fin d) : Matrix.SpecialLinearGroup (Fin d) F :=
  ⟨(Equiv.swap k l).permMatrix F, by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap k l)) with h | h <;> rw [h]
    · simp
    · rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, CharTwo.neg_eq]⟩

theorem coe_swapElt [CharP F 2] (k l : Fin d) :
    ((swapElt (F := F) k l : Matrix.SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (Equiv.swap k l).permMatrix F :=
  rfl

theorem swapElt_mul_self [CharP F 2] (k l : Fin d) :
    swapElt (F := F) k l * swapElt k l = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_swapElt, ← Matrix.permMatrix_mul,
    Equiv.swap_mul_self, Matrix.permMatrix_one, Matrix.SpecialLinearGroup.coe_one]

theorem swapElt_inv [CharP F 2] (k l : Fin d) : (swapElt (F := F) k l)⁻¹ = swapElt k l :=
  inv_eq_of_mul_eq_one_right (swapElt_mul_self k l)

theorem map_swapElt [CharP F 2] (τ : F ≃+* F) (k l : Fin d) :
    Matrix.SpecialLinearGroup.map τ.toRingHom (swapElt k l) = swapElt k l := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    coe_swapElt]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  split_ifs <;> simp

theorem swap_mul_diagonal (k l : Fin d) (t : Fin d → F) :
    (Equiv.swap k l).permMatrix F * diagonal t * (Equiv.swap k l).permMatrix F =
      diagonal (t ∘ Equiv.swap k l) := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_swap,
    Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id,
    Matrix.submatrix_diagonal_equiv]

theorem slConjugation_of_isDiag {D : GL (Fin d) F} (hD : (D : Matrix (Fin d) (Fin d) F).IsDiag)
    {g : Matrix.SpecialLinearGroup (Fin d) F} (hg : (g : Matrix (Fin d) (Fin d) F).IsDiag) :
    CatalogueBHigherLinearAction.slConjugation d F D g = g := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation]
  have h1 : diagonal (diag (D : Matrix (Fin d) (Fin d) F)) = D :=
    (isDiag_iff_diagonal_diag _).mp hD
  have h2 : diagonal (diag (g : Matrix (Fin d) (Fin d) F)) = g :=
    (isDiag_iff_diagonal_diag _).mp hg
  have hcomm : (D : Matrix (Fin d) (Fin d) F) * (g : Matrix (Fin d) (Fin d) F) =
      (g : Matrix (Fin d) (Fin d) F) * D := by
    rw [← h1, ← h2, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    exact mul_comm _ _
  rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem map_of_isDiag {τ : F ≃+* F} {g : Matrix.SpecialLinearGroup (Fin d) F}
    (hg : (g : Matrix (Fin d) (Fin d) F).IsDiag)
    (hfix : ∀ j, τ ((g : Matrix (Fin d) (Fin d) F) j j) = (g : Matrix (Fin d) (Fin d) F) j j) :
    Matrix.SpecialLinearGroup.map τ.toRingHom g = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  by_cases hab : a = b
  · subst hab
    exact hfix a
  · rw [hg hab]
    exact map_zero τ

theorem diag_ne_zero {D : GL (Fin d) F} {t : Fin d → F}
    (hD : (D : Matrix (Fin d) (Fin d) F) = diagonal t) (j : Fin d) : t j ≠ 0 := by
  intro hj
  have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := F))
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
    Finset.prod_eq_zero (Finset.mem_univ j) hj] at h1
  exact not_isUnit_zero h1

theorem coe_swap_mul_slConjugation [CharP F 2] {D : GL (Fin d) F} {t : Fin d → F}
    (hD : (D : Matrix (Fin d) (Fin d) F) = diagonal t) (k l : Fin d) :
    ((swapElt k l * CatalogueBHigherLinearAction.slConjugation d F D (swapElt k l) :
      Matrix.SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      diagonal fun j => t (Equiv.swap k l j) * (t j)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_slConjugation, coe_swapElt,
    TypeA.coe_inv_of_diagonal hD, hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    swap_mul_diagonal, diagonal_mul_diagonal]
  rfl

theorem slConjugation_toGL (g h : Matrix.SpecialLinearGroup (Fin d) F) :
    CatalogueBHigherLinearAction.slConjugation d F (Matrix.SpecialLinearGroup.toGL g) h =
      g * h * g⁻¹ := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, ← map_inv]
  rfl

theorem pow_conj_eq {X : Type*} [Group X] {φ : Matrix.SpecialLinearGroup (Fin d) F →* X} {x : X}
    {A : GL (Fin d) F}
    (hx : ∀ h, x * φ h * x⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F A h))
    (n : ℕ) (h : Matrix.SpecialLinearGroup (Fin d) F) :
    x ^ n * φ h * (x ^ n)⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F (A ^ n) h) := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    have e1 : x ^ (n + 1) * φ h * (x ^ (n + 1))⁻¹ = x * (x ^ n * φ h * (x ^ n)⁻¹) * x⁻¹ := by
      group
    rw [e1, ih, hx, pow_succ', map_mul]
    rfl

theorem exists_scalar_of_forall_conj_eq [Finite F] {X : Type*} [Group X]
    {φ : Matrix.SpecialLinearGroup (Fin d) F →* X}
    (hφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F)) {A B : GL (Fin d) F}
    (h : ∀ g, φ (CatalogueBHigherLinearAction.slConjugation d F A g) =
      φ (CatalogueBHigherLinearAction.slConjugation d F B g)) :
    ∃ c : F, ((B⁻¹ * A : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = scalar (Fin d) c := by
  apply TypeA.exists_scalar_of_conjAut_eq_one
  ext q
  obtain ⟨g, rfl⟩ := proj_surjective d F q
  rw [MulAut.one_apply, map_mul, MulAut.mul_apply, conjAut_proj, map_inv]
  change (conjAut d F B).symm _ = _
  rw [MulEquiv.symm_apply_eq, conjAut_proj, proj_eq_proj_iff, scalars_eq_center]
  apply hφ
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

theorem exists_weyl_elt {G : Type*} [Group G] [Finite G] [Finite F] [CharP F 2]
    (φ : Matrix.SpecialLinearGroup (Fin d) F →* G)
    (hφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F)) {σ : F ≃+* F}
    {Bs : Subgroup G} (hBc : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a)
    (hact : ∀ b ∈ Bs, ∃ (D₁ : GL (Fin d) F) (k : ℕ), (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
      (∀ j, σ ((D₁ : Matrix (Fin d) (Fin d) F) j j) = (D₁ : Matrix (Fin d) (Fin d) F) j j) ∧
      ∀ h, b * φ h * b⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F D₁
        (Matrix.SpecialLinearGroup.map (σ ^ k).toRingHom h)))
    {x : G} {Dx : GL (Fin d) F} (hDx : (Dx : Matrix (Fin d) (Fin d) F).IsDiag)
    (hx : ∀ h, x * φ h * x⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F Dx h))
    {i k l : Fin d} (hik : i ≠ k) (hil : i ≠ l)
    (heq : (Dx : Matrix (Fin d) (Fin d) F) i i = (Dx : Matrix (Fin d) (Fin d) F) k k)
    (hne : (Dx : Matrix (Fin d) (Fin d) F) l l ≠ (Dx : Matrix (Fin d) (Fin d) F) k k) :
    ∃ w ∈ φ.range, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  set P := swapElt (F := F) k l with hP
  have hPinv : φ P⁻¹ = (φ P)⁻¹ := map_inv φ P
  refine ⟨φ P, ⟨P, rfl⟩, fun b hb => ?_, ?_⟩
  · obtain ⟨D₁, k₁, hD₁, hσD₁, hb₁⟩ := hact b hb
    set t := diag (D₁ : Matrix (Fin d) (Fin d) F) with ht
    have hD₁t : (D₁ : Matrix (Fin d) (Fin d) F) = diagonal t :=
      ((isDiag_iff_diagonal_diag _).mp hD₁).symm
    set Y := P * CatalogueBHigherLinearAction.slConjugation d F D₁ P with hY
    have hYm : (Y : Matrix (Fin d) (Fin d) F) = diagonal fun j => t (Equiv.swap k l j) * (t j)⁻¹ :=
      coe_swap_mul_slConjugation hD₁t k l
    have hYd : (Y : Matrix (Fin d) (Fin d) F).IsDiag := by
      rw [hYm]
      exact isDiag_diagonal _
    have hYσ : ∀ (m : ℕ) (j : Fin d),
        (σ ^ m) ((Y : Matrix (Fin d) (Fin d) F) j j) = (Y : Matrix (Fin d) (Fin d) F) j j := by
      intro m j
      have hfix : ∀ a : Fin d, σ (t a) = t a := fun a => hσD₁ a
      have hmem : ∀ a : Fin d, σ ^ m ∈ fixingSubgroup (t a) := fun a =>
        Subgroup.pow_mem _ (show σ ∈ fixingSubgroup (t a) from hfix a) m
      rw [hYm, diagonal_apply_eq, map_mul, map_inv₀]
      change (σ ^ m) (t (Equiv.swap k l j)) * ((σ ^ m) (t j))⁻¹ = _
      rw [show (σ ^ m) (t (Equiv.swap k l j)) = t (Equiv.swap k l j) from hmem _,
        show (σ ^ m) (t j) = t j from hmem j]
    have hwb : φ P * b * (φ P)⁻¹ = φ Y * b := by
      have h1 := hb₁ P
      rw [hP, map_swapElt, ← hP] at h1
      calc φ P * b * (φ P)⁻¹ = φ P * (b * φ P * b⁻¹) * b := by
            rw [← hPinv, hP, swapElt_inv, ← hP]
            group
        _ = φ P * φ (CatalogueBHigherLinearAction.slConjugation d F D₁ P) * b := by rw [h1]
        _ = φ Y * b := by rw [hY, map_mul]
    have hYc : ∀ b' ∈ Bs, b' * φ Y = φ Y * b' := by
      intro b' hb'
      obtain ⟨D₂, k₂, hD₂, -, hb₂⟩ := hact b' hb'
      have h1 := hb₂ Y
      rw [map_of_isDiag hYd (hYσ k₂), slConjugation_of_isDiag hD₂ hYd] at h1
      calc b' * φ Y = b' * φ Y * b'⁻¹ * b' := by group
        _ = φ Y * b' := by rw [h1]
    rw [hwb, Subgroup.mem_centralizer_iff]
    intro b' hb'
    rw [← mul_assoc, hYc b' hb', mul_assoc, hBc b' hb' b hb, mul_assoc]
  · intro hmem
    have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x ^ n = φ P * x * (φ P)⁻¹ :=
      hxfin.mem_powers_iff_mem_zpowers.mpr hmem
    set PG := Matrix.SpecialLinearGroup.toGL P with hPG
    have hcomp : ∀ h, φ (CatalogueBHigherLinearAction.slConjugation d F (PG * Dx * PG) h) =
        φ (CatalogueBHigherLinearAction.slConjugation d F (Dx ^ n) h) := by
      intro h
      have e1 : φ P * x * (φ P)⁻¹ * φ h * (φ P * x * (φ P)⁻¹)⁻¹ =
          φ P * (x * φ (P⁻¹ * h * P) * x⁻¹) * φ P⁻¹ := by
        rw [map_mul, map_mul, hPinv]
        group
      rw [← pow_conj_eq hx n h, hn, e1, hx, ← map_mul, ← map_mul]
      congr 1
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, slConjugation_toGL,
        slConjugation_toGL, hP, swapElt_inv]
    obtain ⟨c, hc⟩ := exists_scalar_of_forall_conj_eq hφ hcomp
    set t := diag (Dx : Matrix (Fin d) (Fin d) F) with ht
    have hDxt : (Dx : Matrix (Fin d) (Fin d) F) = diagonal t :=
      ((isDiag_iff_diagonal_diag _).mp hDx).symm
    have hpow : ((Dx ^ n : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = diagonal (t ^ n) := by
      rw [Units.val_pow_eq_pow_val, hDxt, diagonal_pow]
    have hPm : ((PG : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        (Equiv.swap k l).permMatrix F := rfl
    have hm : ((((Dx ^ n)⁻¹ * (PG * Dx * PG) : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) =
        diagonal fun j => ((t j) ^ n)⁻¹ * t (Equiv.swap k l j) := by
      rw [Units.val_mul, TypeA.coe_inv_of_diagonal hpow, Units.val_mul, Units.val_mul, hPm,
        hDxt, swap_mul_diagonal, diagonal_mul_diagonal]
      rfl
    rw [hm] at hc
    have hci := congrFun (congrFun hc i) i
    have hck := congrFun (congrFun hc k) k
    rw [diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at hci hck
    rw [Equiv.swap_apply_of_ne_of_ne hik hil] at hci
    rw [Equiv.swap_apply_left] at hck
    have htk : t k ≠ 0 := diag_ne_zero hDxt k
    have heq' : t i = t k := heq
    rw [heq'] at hci
    have h1 : t k = t l := by
      have h2 := hci.trans hck.symm
      have h3 : ((t k) ^ n)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero n htk)
      exact mul_left_cancel₀ h3 h2
    exact hne h1.symm

end NbrLangTypeA

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

@[expose] def GGNbrTypeAXNonRegularInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      commutator K = ⊤ → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
      ∀ (d : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ d →
      ∀ (θ : K ⧸ Subgroup.center K ≃* projectiveSL d F) (M D₁ : GL (Fin d) F),
        (D₁ : Matrix (Fin d) (Fin d) F).IsDiag →
        ggLAut K θ ⟨x, hxK⟩ = conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹ →
        ∃ i k l : Fin d, i ≠ k ∧ i ≠ l ∧
          (D₁ : Matrix (Fin d) (Fin d) F) i i = (D₁ : Matrix (Fin d) (Fin d) F) k k ∧
          (D₁ : Matrix (Fin d) (Fin d) F) l l ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k

@[expose] def GGNbrTypeAXRepeatedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      commutator K = ⊤ → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
      ∀ (d : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ d →
      ∀ (θ : K ⧸ Subgroup.center K ≃* projectiveSL d F) (M D₁ : GL (Fin d) F),
        (D₁ : Matrix (Fin d) (Fin d) F).IsDiag →
        ggLAut K θ ⟨x, hxK⟩ = conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹ →
        ∃ i k : Fin d, i ≠ k ∧
          (D₁ : Matrix (Fin d) (Fin d) F) i i = (D₁ : Matrix (Fin d) (Fin d) F) k k

namespace NbrLangTypeA

variable {G : Type} [Group G] {d : ℕ} {F : Type} [Field F]

theorem exists_ne_diag_of_nbr [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G}
    {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K) (hperf : commutator K = ⊤)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hd : 0 < d)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL d F) {M D₁ : GL (Fin d) F}
    (hD₁ : (D₁ : Matrix (Fin d) (Fin d) F).IsDiag)
    (hx : ggLAut K θ ⟨x, hxK⟩ = conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹) :
    ∃ k l : Fin d, (D₁ : Matrix (Fin d) (Fin d) F) l l ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k := by
  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  set i₀ : Fin d := ⟨0, hd⟩
  set t := diag (D₁ : Matrix (Fin d) (Fin d) F) with ht
  have hDt : (D₁ : Matrix (Fin d) (Fin d) F) = diagonal t :=
    ((isDiag_iff_diagonal_diag _).mp hD₁).symm
  have hc0 : t i₀ ≠ 0 := diag_ne_zero hDt i₀
  have hscal : D₁ = Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (t i₀) hc0) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hDt, scalar_apply]
    congr 1
    funext l
    exact hall i₀ l
  have h1 : ggLAut K θ ⟨x, hxK⟩ = 1 := by
    rw [hx, hscal, conjAut_scalar, mul_one, mul_inv_cancel]
  have h2 := mem_centralizer_of_ggLAut_eq_one K θ hperf h1
  apply hK.2.2.2
  have h3 : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.zpowers_le).mpr h2
  have h4 : (⁅Subgroup.zpowers x, K⁆ : Subgroup G) = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr h3
  rw [Subgroup.commutator_comm, h4]
  exact bot_le

end NbrLangTypeA

@[expose] def GGTypeARegularCentralizerInput : Prop :=
  ∀ (d : ℕ) (F : Type) [Field F] [Finite F] (M D₁ : GL (Fin d) F), 3 ≤ d →
    (D₁ : Matrix (Fin d) (Fin d) F).IsDiag →
    (∀ i k : Fin d, i ≠ k →
      (D₁ : Matrix (Fin d) (Fin d) F) i i ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k) →
    Group.IsSolvable ↥((conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹).toMonoidHom.eqLocus
      (MonoidHom.id (projectiveSL d F)))

theorem ggNbrTypeAXRepeatedInput_of_regular (hI3 : GGNbrSubcomponentInput)
    (hreg : GGTypeARegularCentralizerInput) : GGNbrTypeAXRepeatedInput := by
  intro G _ _ p B Bs x L D J hC y K hK hperf hxK d F _ _ hd θ M D₁ hD₁ hx
  by_contra hno
  have hdist : ∀ i k : Fin d, i ≠ k →
      (D₁ : Matrix (Fin d) (Fin d) F) i i ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k :=
    fun i k hik h => hno ⟨i, k, hik, h⟩
  set α := conjAut d F M * conjAut d F D₁ * (conjAut d F M)⁻¹ with hα
  have hsolv : Group.IsSolvable ↥(α.toMonoidHom.eqLocus (MonoidHom.id (projectiveSL d F))) :=
    hreg d F M D₁ hd hD₁ hdist
  have hJK : J ≤ K := hI3 G p B x L D J hC.1 hC.2.2 y K hK
  obtain ⟨-, -, -, hxD, -, hJcomp, -⟩ := hC.2.2.1
  have hJx : ∀ j ∈ J, x * j * x⁻¹ = j := by
    intro j hj
    have h1 : j ∈ Subgroup.centralizer (D : Set G) := (hJcomp.1 hj).2
    rw [Subgroup.mem_centralizer_iff.mp h1 x hxD, mul_inv_cancel_right]
  let ψ₀ : ↥J →* projectiveSL d F := θ.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hJK))
  have hψ₀ : ∀ j : ↥J, α (ψ₀ j) = ψ₀ j := by
    intro j
    change α (θ (QuotientGroup.mk (⟨j, hJK j.2⟩ : K))) = θ (QuotientGroup.mk ⟨j, hJK j.2⟩)
    rw [← hx, ggLAut_apply]
    congr 2
    apply Subtype.ext
    exact hJx j j.2
  let ψ : ↥J →* ↥(α.toMonoidHom.eqLocus (MonoidHom.id (projectiveSL d F))) :=
    ψ₀.codRestrict _ hψ₀
  have hcen : ∀ a : ↥J, ψ a = 1 → (⟨a, hJK a.2⟩ : K) ∈ Subgroup.center K := by
    intro a ha
    have h1 : ψ₀ a = 1 := congrArg Subtype.val ha
    apply (QuotientGroup.eq_one_iff _).mp
    apply θ.injective
    rw [map_one]
    exact h1
  have hkerab : ∀ a b : ↥ψ.ker, a * b = b * a := by
    intro a b
    have h1 := Subgroup.mem_center_iff.mp (hcen a.1 a.2) ⟨b.1, hJK b.1.2⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Subtype.val h1).symm
  have : Group.IsSolvable ↥ψ.ker := Group.isSolvable_of_comm hkerab
  have : Group.IsSolvable ↥J :=
    Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by rw [Subgroup.range_subtype])
  obtain ⟨hJperf, hJsimp⟩ := hJcomp.2.2
  have : Nontrivial ↥J := by
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    exact nontrivial_of_ne j 1 (fun h => hq (by rw [h, QuotientGroup.mk_one]))
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J
  rw [hJperf] at hlt
  exact lt_irrefl _ hlt

open NbrLangTypeA in
theorem ggNbrTypeAXNonRegularInput_of_repeated (h : GGNbrTypeAXRepeatedInput) :
    GGNbrTypeAXNonRegularInput := by
  intro G _ _ p B Bs x L D J hC y K hK hperf hxK d F _ _ hd θ M D₁ hD₁ hx
  obtain ⟨i, k, hik, hik'⟩ := h G p B Bs x L D J hC y K hK hperf hxK d F hd θ M D₁ hD₁ hx
  obtain ⟨k', l, hkl⟩ := exists_ne_diag_of_nbr hK hperf hxK (by omega) θ hD₁ hx
  have hl : ∃ l : Fin d,
      (D₁ : Matrix (Fin d) (Fin d) F) l l ≠ (D₁ : Matrix (Fin d) (Fin d) F) k k := by
    by_cases hlk : (D₁ : Matrix (Fin d) (Fin d) F) l l = (D₁ : Matrix (Fin d) (Fin d) F) k k
    · exact ⟨k', fun h' => hkl (hlk.trans h'.symm)⟩
    · exact ⟨l, hlk⟩
  obtain ⟨l₁, hl₁⟩ := hl
  refine ⟨i, k, l₁, hik, fun h' => hl₁ ?_, hik', hl₁⟩
  rw [← h', hik']

namespace NbrLangTypeA

variable {G : Type} [Group G] {d : ℕ} {F : Type} [Field F]

theorem weyl_of_linear (hframe : GGTypeASplitFrameInput)
    (hnonreg : GGNbrTypeAXNonRegularInput) [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hK : GGNbr p B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) (hd : 3 ≤ d)
    [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hpF : p ∣ 2 ^ m - 1) (hpd : ¬ p ∣ d)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (hxI : ggLAut K θ ⟨x, hxK⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hC.2.1.2.1
  have hxBs : x ∈ Bs := hC.2.1.1 hC.1.2.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hm : 2 ≤ m := by
    have h1 := Finite.one_lt_card (α := F)
    rw [hF] at h1
    have h2 : 0 < 2 ^ m - 1 := by omega
    have h3 := Nat.le_of_dvd h2 hpF
    by_contra h4
    interval_cases m <;> simp at h3 <;> omega
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  set θ₁ := θ.trans (TypeA.recipeEquiv d F) with hθ₁
  have hgr : ∀ (b : G) (hb : b ∈ Bs),
      ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ,
      ∃ f ∈ Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))),
        ggLAut K θ ⟨b, hN hb⟩ = u * f := fun b hb =>
    NbrGraphLinear.ggOddAutInnField_linear (K := F) (by omega) (hp.odd_of_ne_two hp2) _
      (ggLAut_pow_eq_one K θ (hN hb) (hBs.2 b hb))
  have hsemi : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ₁ ⟨b, hN hb⟩ ∈ semilinearAutGroup d F :=
    fun b hb => mem_semilinear_of_eq_mul θ _ (hgr b hb)
  set αB : ↥Bs →* MulAut (projectiveSL d F) := (ggLAut K θ₁).comp (Subgroup.inclusion hN)
    with hαB
  obtain ⟨M, σ, -, hfr, -⟩ := hframe p d F hp hp2 hd (by rw [hF]; exact hpF) hpd αB.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm a c])
    (by
      rintro _ ⟨a, rfl⟩
      have ha : a ^ p = 1 := Subtype.ext (by simpa using hBs.2 a a.2)
      rw [← map_pow, ha, map_one])
    (by
      rintro _ ⟨a, rfl⟩
      exact hsemi a a.2)
  obtain ⟨Dx, kx, hDx, -, hfrx⟩ := hfr _ ⟨⟨x, hxBs⟩, rfl⟩
  have hfrx' : ggLAut K θ₁ ⟨x, hxK⟩ = conjAut d F M * conjAut d F Dx *
      fieldAut d F (σ ^ kx) * (conjAut d F M)⁻¹ := hfrx
  have hxlin : ggLAut K θ₁ ⟨x, hxK⟩ ∈ linearAutGroup d F := (mem_conjImage_iff θ _).mp hxI
  rw [hfrx'] at hxlin
  have hkx : σ ^ kx = 1 := eq_one_of_frame_mem_linear hd hxlin
  rw [hkx, map_one, mul_one] at hfrx'
  obtain ⟨i, k, l, hik, hil, heq, hne⟩ :=
    hnonreg G p B Bs x L D J hC y K hK hperf hxK d F hd θ₁ M Dx hDx hfrx'
  have hF4 : Nat.card F = 4 → p = 3 := by
    intro h4
    rw [hF] at h4
    have hm2 : m = 2 := by
      rcases Nat.lt_or_ge m 3 with h | h
      · omega
      · have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
        omega
    rw [hm2] at hpF
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpF
  have h2m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨φ₀, -, hφker, hlift⟩ := exists_lift hd (by omega)
    (fun h => hpd (by rw [h.1, hF4 h.2])) (by omega) hperf θ₁
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hd)).commutator_eq_top
  set φ' : Matrix.SpecialLinearGroup (Fin d) F →* G := (K.subtype.comp φ₀).comp
    (CatalogueBHigherLinearAction.slConjugation d F M).toMonoidHom with hφ'
  have hφ'ker : φ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    refine ker_comp_slConjugation_le (K.subtype.comp φ₀) ?_ M
    intro h hh
    apply hφker
    rw [MonoidHom.mem_ker] at hh ⊢
    exact K.subtype_injective (by rw [← MonoidHom.comp_apply, hh, map_one])
  have hact : ∀ b ∈ Bs, ∃ (D₁ : GL (Fin d) F) (k : ℕ),
      (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
      (∀ j, σ ((D₁ : Matrix (Fin d) (Fin d) F) j j) = (D₁ : Matrix (Fin d) (Fin d) F) j j) ∧
      ∀ h, b * φ' h * b⁻¹ = φ' (CatalogueBHigherLinearAction.slConjugation d F D₁
        (Matrix.SpecialLinearGroup.map (σ ^ k).toRingHom h)) := by
    intro b hb
    obtain ⟨D₁, k₁, hD₁, hσD₁, hbfr⟩ := hfr _ ⟨⟨b, hb⟩, rfl⟩
    exact ⟨D₁, k₁, hD₁, hσD₁, fun h => conj_frame_eq hSL θ₁ φ₀ hlift (hN hb) M D₁ _ hbfr h⟩
  have hx : ∀ h, x * φ' h * x⁻¹ = φ' (CatalogueBHigherLinearAction.slConjugation d F Dx h) := by
    intro h
    have hfrx'' : ggLAut K θ₁ ⟨x, hxK⟩ = conjAut d F M * conjAut d F Dx * fieldAut d F 1 *
        (conjAut d F M)⁻¹ := by
      rw [map_one, mul_one]
      exact hfrx'
    exact (conj_frame_eq hSL θ₁ φ₀ hlift hxK M Dx 1 hfrx'' h).trans rfl
  obtain ⟨w, ⟨h₀, rfl⟩, hwC, hwx⟩ :=
    exists_weyl_elt φ' hφ'ker (fun a ha c hc => TableB.IsElemAbelian.comm hBs ha hc) hact hDx hx
      hik hil heq hne
  exact ⟨φ' h₀, (φ₀ _).2, hwC, hwx⟩

end NbrLangTypeA

open NbrLangTypeA

theorem ggNbrInnerWeylOn_typeASplit (hframe : GGTypeASplitFrameInput)
    (hnonreg : GGNbrTypeAXNonRegularInput) : GGNbrInnerWeylOn GGTypeASplitCoprimeLabel := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : GGTypeASplitCoprimeLabel p lab
  · obtain ⟨t, l, n⟩ := lab
    rcases hS with ⟨ht, hl, hpn, hpd⟩ | ⟨ht, hl, hpn, hpd⟩ <;> dsimp only at ht hl hpn hpd <;>
      subst ht
    · dsimp only [LargeEvenRawDatum] at hraw ⊢
      obtain ⟨F, _, _, hF, hs, hna, θ, hPθ⟩ := hraw
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ, fun _ hxI => ?_⟩
      exact weyl_of_linear hframe hnonreg hC hK hN hxK hperf (by omega) hF hpn hpd θ hxI
    · subst hl
      simp only [LargeEvenRawDatum, ↓reduceIte] at hraw ⊢
      obtain ⟨F, _, _, hF, hs, hna, θ, hPθ⟩ := hraw
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ, fun _ hxI => ?_⟩
      exact weyl_of_linear hframe hnonreg hC hK hN hxK hperf (by omega) hF hpn hpd θ hxI
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h => absurd h hS⟩) hraw

theorem ggNbrInnerWeylInput_of_typeASplit (hframe : GGTypeASplitFrameInput)
    (hnonreg : GGNbrTypeAXNonRegularInput)
    (hrest : GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrInnerWeylInput :=
  ggNbrInnerWeylInput_of_on
    (ggNbrInnerWeylOn_true_of (ggNbrInnerWeylOn_typeASplit hframe hnonreg) hrest)

theorem ggXNotNormalInput_of_typeASplit (hnorm : GGBstarNbrNormalInput)
    (hgraph : GGNbrGraphInput) (hframe : GGTypeASplitFrameInput)
    (hnonreg : GGNbrTypeAXNonRegularInput)
    (hlang : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab)
    (hweyl : GGNbrInnerWeylOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) : GGXNotNormalInput :=
  ggXNotNormalInput_of_torus_weyl hnorm hgraph
    (ggNbrLangTorusInput_of_axis (ggNbrLangTorusAxisInput_of_typeASplit hframe hlang))
    (ggNbrInnerWeylInput_of_typeASplit hframe hnonreg hweyl)

theorem ggNbrFieldTransvectionInput_of_typeASplit (hframe : GGTypeASplitFrameInput)
    (hlang : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrFieldTransvectionInput :=
  ggNbrFieldTransvectionInput_of_torus
    (ggNbrLangTorusInput_of_axis (ggNbrLangTorusAxisInput_of_typeASplit hframe hlang))

end CFSG.StandardType

end
