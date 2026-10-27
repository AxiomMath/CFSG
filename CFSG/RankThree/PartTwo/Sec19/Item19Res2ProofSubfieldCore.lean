module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofFlag
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof

open Matrix Module CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)
open scoped commutatorElement

section Inner

variable {K : Type} [Field K]

theorem exists_cube_of_pow_three_eq_one [Finite K] (h9 : 9 ∣ Nat.card K - 1) {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) : ∃ ν : Kˣ, ν ^ 3 = ζ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg ζ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  obtain ⟨m, hm⟩ := h9
  have h1 : ((Nat.card K - 1 : ℕ) : ℤ) ∣ k * 3 := by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one, _root_.zpow_mul]
    exact_mod_cast hζ
  rw [hm] at h1
  obtain ⟨t, ht⟩ := h1
  refine ⟨g ^ ((m : ℤ) * t), ?_⟩
  rw [← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast at ht ⊢
  linarith

theorem isInnerAut_conjAut_of_det_eq_cube {A : GL (Fin 3) K} {μ : Kˣ}
    (hμ : μ ^ 3 = GeneralLinearGroup.det A) : KFacts.IsInnerAut (conjAut 3 K A) := by
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A with hB
  have hsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ : GL (Fin 3) K) =
      μ⁻¹ ^ 3 := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  have hdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, hsc, ← hμ, inv_pow, inv_mul_cancel]
  have hrange : B ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  obtain ⟨g, hg⟩ := hrange
  have hAB : conjAut 3 K A = conjAut 3 K B := by rw [hB, map_mul, conjAut_scalar, one_mul]
  rw [hAB, ← hg, ← KFacts.conj_proj_eq_conjAut]
  exact KFacts.isInnerAut_conj _

theorem exists_cube_of_commute_involution [CharP K 2] {A t : Matrix (Fin 3) (Fin 3) K} {u : K}
    (hA3 : A ^ 3 = scalar (Fin 3) u) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hAt : A * t = t * A) :
    ∃ μ : K, μ ^ 3 = u := by
  classical
  set N : Matrix (Fin 3) (Fin 3) K := t - 1 with hN
  have hN0 : N ≠ 0 := sub_ne_zero.mpr ht1
  have hNN : N * N = 0 := by
    have e : N * N = t * t - t - t + 1 := by
      rw [hN]
      noncomm_ring
    rw [e, ht2]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination ((1 : Matrix (Fin 3) (Fin 3) K) i j - t i j) * h2
  have hAN : A * N = N * A := by
    rw [hN, mul_sub, sub_mul, hAt, mul_one, one_mul]
  set f := mulVecLin N with hf
  have hrk : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, hf, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, hNN,
      zero_mulVec]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [finrank_fin_fun] at hsum
  have hle := Submodule.finrank_mono hrk
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hN0
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    rwa [mulVec_single_one] at this
  set w := N *ᵥ v with hw
  have hwr : w ∈ LinearMap.range f := ⟨v, rfl⟩
  have hspan : (K ∙ w) = LinearMap.range f := by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwr)
    rw [finrank_span_singleton hv]
    omega
  have hAw : A *ᵥ w ∈ K ∙ w := by
    rw [hspan]
    refine ⟨A *ᵥ v, ?_⟩
    rw [hf, mulVecLin_apply, hw, mulVec_mulVec, mulVec_mulVec, hAN]
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hAw
  refine ⟨μ, ?_⟩
  have hpow : ∀ k : ℕ, A ^ k *ᵥ w = μ ^ k • w := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, one_mulVec, one_smul]
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, ← hμ, smul_smul, pow_succ]
  have h3 := hpow 3
  rw [hA3, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec] at h3
  have h4 : (u - μ ^ 3) • w = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.mp h4 with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hv

theorem isInnerAut_of_conjAut_fix_involution [Finite K] [CharP K 2] (h9 : 9 ∣ Nat.card K - 1)
    {A : GL (Fin 3) K} (hA3 : conjAut 3 K A ^ 3 = 1) {x : projectiveSL 3 K} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hfix : conjAut 3 K A x = x) : KFacts.IsInnerAut (conjAut 3 K A) := by
  classical
  obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl (A ^ 3) 1
    (by rw [map_one, mul_one, map_pow, hA3])
  obtain ⟨s, rfl⟩ := proj_surjective 3 K x
  have h1 : proj 3 K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K
      A s) = proj 3 K s := by
    rw [← conjAut_proj]
    exact hfix
  rw [proj_eq_proj_iff] at h1
  obtain ⟨c, hc3, hc⟩ := h1
  have h2 : proj 3 K (s ^ 2) = 1 := by rw [map_pow]; exact hx2
  rw [proj_eq_one_iff] at h2
  obtain ⟨d, hd3, hd⟩ := h2
  set S : Matrix (Fin 3) (Fin 3) K := (s : Matrix (Fin 3) (Fin 3) K) with hS
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  set Mi : Matrix (Fin 3) (Fin 3) K := ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hMi
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hconj : M * S * Mi = scalar (Fin 3) ((c⁻¹ : Kˣ) : K) * S := by
    set C := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A s
      with hCdef
    have hCm : (C : Matrix (Fin 3) (Fin 3) K) = M * S * Mi := coe_slConjugation A s
    have hCi : ((C⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (C : Matrix (Fin 3) (Fin 3) K) = 1 := coe_inv_mul_coe C
    have hCi' : (C : Matrix (Fin 3) (Fin 3) K) *
        ((C⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
      mul_eq_one_comm.mp hCi
    have hc' : ((C⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * S =
        scalar (Fin 3) (c : K) := hc
    have hSC : S = (C : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
      rw [← hc', ← Matrix.mul_assoc, hCi', Matrix.one_mul]
    have hsc1 : scalar (Fin 3) (c : K) * scalar (Fin 3) ((c⁻¹ : Kˣ) : K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    calc M * S * Mi = (C : Matrix (Fin 3) (Fin 3) K) := hCm.symm
      _ = S * scalar (Fin 3) ((c⁻¹ : Kˣ) : K) := by
        rw [hSC, Matrix.mul_assoc, hsc1, Matrix.mul_one]
      _ = scalar (Fin 3) ((c⁻¹ : Kˣ) : K) * S :=
        ((scalar_commute _ (fun _ => Commute.all _ _) S).eq).symm
  have hS2 : S * S = scalar (Fin 3) (d : K) := by
    rw [← sq]
    exact hd
  have hc3' : ((c⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hc3, inv_one, Units.val_one]
  have hd3' : (d : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hd3, Units.val_one]
  set t : Matrix (Fin 3) (Fin 3) K := S * S * S with ht
  have htt : t * t = 1 := by
    have e : t * t = (S * S) * (S * S) * (S * S) := by
      rw [ht]
      noncomm_ring
    rw [e, hS2, ← map_mul, ← map_mul, ← pow_three', hd3', map_one]
  have ht1 : t ≠ 1 := by
    intro h
    apply hx1
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      change S ^ 3 = 1
      rw [pow_three, ← Matrix.mul_assoc]
      exact h
    have h3 : (proj 3 K s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    calc proj 3 K s = proj 3 K s ^ 3 * (proj 3 K s ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hx2, inv_one, one_mul]
  have hMt : M * t = t * M := by
    set B := scalar (Fin 3) ((c⁻¹ : Kˣ) : K) with hB
    have hBS : B * S = S * B := (scalar_commute _ (fun _ => Commute.all _ _) S).eq
    have hBBB : B * B * B = 1 := by
      rw [hB, ← map_mul, ← map_mul, ← pow_three', hc3', map_one]
    have hMS : M * S = B * S * M := by
      rw [← hconj, Matrix.mul_assoc (M * S), hMiM, Matrix.mul_one]
    have hSB : ∀ X : Matrix (Fin 3) (Fin 3) K, S * (B * X) = B * (S * X) := fun X => by
      rw [← Matrix.mul_assoc, ← hBS, Matrix.mul_assoc]
    calc M * t = M * S * S * S := by rw [ht]; simp only [Matrix.mul_assoc]
      _ = B * S * M * S * S := by rw [hMS]
      _ = B * S * (M * S) * S := by simp only [Matrix.mul_assoc]
      _ = B * S * (B * S * M) * S := by rw [hMS]
      _ = B * S * B * S * (M * S) := by simp only [Matrix.mul_assoc]
      _ = B * S * B * S * (B * S * M) := by rw [hMS]
      _ = (B * B * B) * t * M := by
          rw [ht]
          simp only [Matrix.mul_assoc, hSB]
      _ = t * M := by rw [hBBB, Matrix.one_mul]
  have hM3 : M ^ 3 = scalar (Fin 3) (u : K) := by
    rw [hM, ← Units.val_pow_eq_pow_val, ← hu, GeneralLinearGroup.coe_scalar]
  obtain ⟨μ, hμ⟩ := exists_cube_of_commute_involution hM3 htt ht1 hMt
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact u.ne_zero hμ.symm
  set μ' : Kˣ := Units.mk0 μ hμ0 with hμ'
  have hμ'3 : μ' ^ 3 = u := Units.ext (by rw [Units.val_pow_eq_pow_val, hμ', Units.val_mk0, hμ])
  have hdetsc : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) =
      u ^ 3 := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  have hdet3 : (GeneralLinearGroup.det A) ^ 3 = u ^ 3 := by
    rw [← map_pow, ← hu, hdetsc]
  obtain ⟨ν, hν⟩ := exists_cube_of_pow_three_eq_one h9
    (ζ := GeneralLinearGroup.det A * (μ' ^ 3)⁻¹)
    (by rw [mul_pow, hdet3, inv_pow, hμ'3, mul_inv_cancel])
  refine isInnerAut_conjAut_of_det_eq_cube (μ := μ' * ν) ?_
  rw [mul_pow, hν, mul_comm (GeneralLinearGroup.det A), mul_inv_cancel_left]

end Inner

section Transport

theorem commutatorElement_mul_center {G : Type*} [Group G] (a b : G) {z₁ z₂ : G}
    (h₁ : z₁ ∈ Subgroup.center G) (h₂ : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have c₁ := Subgroup.mem_center_iff.mp h₁
  have c₂ := Subgroup.mem_center_iff.mp h₂
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * (z₁ * (b * z₂)) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by group
    _ = a * ((b * z₂) * z₁) * z₁⁻¹ * a⁻¹ * z₂⁻¹ * b⁻¹ := by rw [← c₁ (b * z₂)]
    _ = a * b * (z₂ * a⁻¹) * z₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z₂) * z₂⁻¹ * b⁻¹ := by rw [← c₂ a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

end Transport

section Field

variable {K : Type} [Field K]

theorem subfieldProj_injective (σ : K ≃+* K) : Function.Injective (subfieldProj σ) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨A, rfl⟩ := proj_surjective 3 _ y
  rw [subfieldProj_proj, proj_eq_one_iff] at hy
  obtain ⟨c, hc3, hc⟩ := hy
  rw [proj_eq_one_iff]
  set a : fixedField σ := (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) 0 0 with ha
  have hentry : ∀ i j, ((A : Matrix (Fin 3) (Fin 3) (fixedField σ)) i j : K) =
      scalar (Fin 3) (c : K) i j := fun i j => congrFun (congrFun hc i) j
  have hca : (c : K) = (a : K) := by
    have := hentry 0 0
    simp only [scalar_apply, diagonal_apply_eq] at this
    exact this.symm
  have hA : (A : Matrix (Fin 3) (Fin 3) (fixedField σ)) = scalar (Fin 3) a := by
    ext i j
    rw [hentry i j]
    by_cases hij : i = j
    · subst hij
      simp [scalar_apply, hca]
    · simp [scalar_apply, diagonal_apply_ne _ hij]
  have ha0 : a ≠ 0 := by
    intro h0
    apply c.ne_zero
    rw [hca, h0]
    rfl
  refine ⟨Units.mk0 a ha0, ?_, hA⟩
  apply Units.ext
  apply Subtype.ext
  have h3 : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
  change (a : K) ^ 3 = 1
  rw [← hca, h3]

theorem card_projectiveSL_three_congr [Finite K] {K' : Type} [Field K'] [Finite K']
    (h : Nat.card K = Nat.card K') :
    Nat.card (projectiveSL 3 K) = Nat.card (projectiveSL 3 K') := by
  rw [card_projectiveSL, card_projectiveSL, card_SL_eq (by norm_num), card_SL_eq (by norm_num),
    card_scalars_eq_gcd K (by norm_num), card_scalars_eq_gcd K' (by norm_num), h]

theorem field_case [Finite K] [CharP K 2] {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {Lb : Subgroup (projectiveSL 3 K)} (hLp : Group.IsPerfect Lb)
    (hfix : ∀ y ∈ Lb, fieldAut 3 K σ y = y)
    (hdvd : Nat.card (projectiveSL 3 (fixedField σ)) ∣ Nat.card Lb)
    {P : Subgroup (projectiveSL 3 K)} (hP : IsProperParabolic P)
    (hPσ : ∀ y ∈ P, fieldAut 3 K σ y ∈ P) :
    Lb = (subfieldProj σ).range ∧ IsProperParabolic ((P ⊓ Lb).subgroupOf Lb) := by
  have hcomm : ⁅Lb, Lb⁆ = Lb := by
    rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hz : ∀ r : SpecialLinearGroup (Fin 3) K, proj 3 K r ∈ Lb →
      r⁻¹ * SpecialLinearGroup.map σ.toRingHom r ∈
        Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro r hr
    have h1 := hfix _ hr
    rw [fieldAut_proj, proj_eq_proj_iff] at h1
    rw [← scalars_eq_center]
    have h2 := (scalars 3 K).inv_mem h1
    simpa using h2
  have hle : Lb ≤ (subfieldProj σ).range := by
    rw [← hcomm, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨s, rfl⟩ := proj_surjective 3 K a
    obtain ⟨t, rfl⟩ := proj_surjective 3 K b
    have hfixc : SpecialLinearGroup.map σ.toRingHom ⁅s, t⁆ = ⁅s, t⁆ := by
      rw [map_commutatorElement]
      have e1 : SpecialLinearGroup.map σ.toRingHom s =
          s * (s⁻¹ * SpecialLinearGroup.map σ.toRingHom s) := by group
      have e2 : SpecialLinearGroup.map σ.toRingHom t =
          t * (t⁻¹ * SpecialLinearGroup.map σ.toRingHom t) := by group
      rw [e1, e2, commutatorElement_mul_center _ _ (hz s ha) (hz t hb)]
    obtain ⟨A₀, hA₀⟩ := KFacts.exists_sl_map_subtype_eq hfixc
    exact ⟨proj 3 _ A₀, by rw [subfieldProj_proj, hA₀, map_commutatorElement]⟩
  have hcardR : Nat.card (subfieldProj σ).range = Nat.card (projectiveSL 3 (fixedField σ)) :=
    (Nat.card_congr (MonoidHom.ofInjective (subfieldProj_injective σ)).toEquiv).symm
  have hLb : Lb = (subfieldProj σ).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardR]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨hLb, ?_⟩
  subst hLb
  have hQ := isProperParabolic_comap_subfieldProj hσ hP hPσ
  set e := MonoidHom.ofInjective (subfieldProj_injective σ) with he
  have heq : (P ⊓ (subfieldProj σ).range).subgroupOf (subfieldProj σ).range =
      (P.comap (subfieldProj σ)).map e.toMonoidHom := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨x, hx⟩ := y.2
      refine ⟨x, ?_, Subtype.ext hx⟩
      change subfieldProj σ x ∈ P
      rw [hx]
      exact hy.1
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hx, ⟨x, rfl⟩⟩
  rw [heq]
  refine isProperParabolic_map_of_surjective e.toMonoidHom e.surjective hQ ?_
  intro x hx
  have : x = 1 := e.injective (by rw [map_one]; exact hx)
  rw [this]
  exact Subgroup.one_mem _

theorem two_dvd_card_projectiveSL_three {K₀ : Type} [Field K₀] [Finite K₀]
    (h2 : 2 ∣ Nat.card K₀) : 2 ∣ Nat.card (projectiveSL 3 K₀) := by
  refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (projUnitriangular 3 K₀))
  rw [card_projUnitriangular]
  exact dvd_pow h2 (by norm_num)

theorem core [Finite K] [CharP K 2] (h9 : 9 ∣ Nat.card K - 1) {α : MulAut (projectiveSL 3 K)}
    (hα3 : α ^ 3 = 1) (hout : ¬ KFacts.IsInnerAut α) {Lb : Subgroup (projectiveSL 3 K)}
    (hLp : Group.IsPerfect Lb) (hfix : ∀ y ∈ Lb, α y = y) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ ^ 3 = Nat.card K) (hdvd : Nat.card (projectiveSL 3 K₀) ∣ Nat.card Lb)
    {P : Subgroup (projectiveSL 3 K)} (hP : IsProperParabolic P) (hPα : ∀ y ∈ P, α y ∈ P) :
    Nat.card Lb = Nat.card (projectiveSL 3 K₀) ∧ IsProperParabolic ((P ⊓ Lb).subgroupOf Lb) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2K : 2 ∣ Nat.card K := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  have h2K₀ : 2 ∣ Nat.card K₀ := by
    rw [← hK₀] at h2K
    exact Nat.prime_two.dvd_of_dvd_pow h2K
  by_cases hlin : α ∈ linearAutGroup 3 K
  · exfalso
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hlin
    have h2 : 2 ∣ Nat.card Lb := (two_dvd_card_projectiveSL_three h2K₀).trans hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    apply hout
    refine isInnerAut_of_conjAut_fix_involution h9 hα3 (x := (x : projectiveSL 3 K)) ?_ ?_
      (hfix _ x.2)
    · rw [← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
    · intro h1
      have : x = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx
      norm_num at hx
  · obtain ⟨σ, hσ, H, hαH⟩ := KFacts.linear_order_three_field_descent le_rfl α hα3 hlin
    set β := conjAut 3 K H with hβ
    have hfσ : fieldAut 3 K σ = β⁻¹ * α * β := by rw [hαH]; group
    set Lb' := Lb.map ((β⁻¹ : MulAut (projectiveSL 3 K)) : projectiveSL 3 K →* projectiveSL 3 K)
      with hLb'
    set P' := P.map ((β⁻¹ : MulAut (projectiveSL 3 K)) : projectiveSL 3 K →* projectiveSL 3 K)
      with hP'
    have hfix' : ∀ y ∈ Lb', fieldAut 3 K σ y = y := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hfσ]
      change β⁻¹ (α (β (β⁻¹ y))) = β⁻¹ y
      rw [MulAut.apply_inv_self, hfix y hy]
    have hPσ' : ∀ y ∈ P', fieldAut 3 K σ y ∈ P' := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hfσ]
      refine ⟨α y, hPα y hy, ?_⟩
      change β⁻¹ (α y) = β⁻¹ (α (β (β⁻¹ y)))
      rw [MulAut.apply_inv_self]
    have hLp' : Group.IsPerfect Lb' := by
      have := hLp
      exact Group.IsPerfect.ofSurjective
        (f := (((β⁻¹ : MulAut (projectiveSL 3 K)) :
          projectiveSL 3 K ≃* projectiveSL 3 K).subgroupMap Lb).toMonoidHom)
        (MulEquiv.surjective _)
    have hcardLb : Nat.card Lb' = Nat.card Lb :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have hcardF : Nat.card (fixedField σ) = Nat.card K₀ := by
      have h1 := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
      rw [hσ] at h1
      exact Nat.pow_left_injective (by norm_num) (h1.trans hK₀.symm)
    have hcardP : Nat.card (projectiveSL 3 (fixedField σ)) = Nat.card (projectiveSL 3 K₀) :=
      card_projectiveSL_three_congr hcardF
    have hP'par : IsProperParabolic P' := by
      refine isProperParabolic_map_of_surjective _ (MulEquiv.surjective _) hP ?_
      intro x hx
      have : x = 1 := (β⁻¹).injective (by rw [map_one]; exact hx)
      rw [this]
      exact Subgroup.one_mem _
    obtain ⟨hLb'eq, hpar'⟩ := field_case hσ hLp' hfix' (by rw [hcardP, hcardLb]; exact hdvd)
      hP'par hPσ'
    refine ⟨?_, ?_⟩
    · rw [← hcardLb, hLb'eq, ← hcardP]
      exact (Nat.card_congr (MonoidHom.ofInjective (subfieldProj_injective σ)).toEquiv).symm
    ·
      set e : Lb' ≃* Lb :=
        (((β : MulAut (projectiveSL 3 K)) : projectiveSL 3 K ≃* projectiveSL 3 K).subgroupMap
          Lb').trans (MulEquiv.subgroupCongr (by
            rw [hLb', Subgroup.map_map]
            convert Subgroup.map_id Lb
            ext y
            simp)) with he
      have he_apply : ∀ y : Lb', ((e y : Lb) : projectiveSL 3 K) = β (y : projectiveSL 3 K) :=
        fun y => rfl
      have heq : (P ⊓ Lb).subgroupOf Lb = ((P' ⊓ Lb').subgroupOf Lb').map e.toMonoidHom := by
        ext y
        constructor
        · intro hy
          rw [Subgroup.mem_subgroupOf] at hy
          refine ⟨e.symm y, ?_, by simp⟩
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
          refine ⟨⟨(y : projectiveSL 3 K), hy.1, ?_⟩, (e.symm y).2⟩
          have h1 : β ((e.symm y : Lb') : projectiveSL 3 K) = (y : projectiveSL 3 K) := by
            rw [← he_apply, MulEquiv.apply_symm_apply]
          rw [← h1]
          change β⁻¹ (β _) = _
          rw [MulAut.inv_apply_self]
        · rintro ⟨x, hx, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
          rw [Subgroup.mem_subgroupOf]
          obtain ⟨⟨p, hp, hpx⟩, -⟩ := hx
          refine ⟨?_, (e x).2⟩
          change ((e x : Lb) : projectiveSL 3 K) ∈ P
          rw [he_apply, ← hpx]
          change β (β⁻¹ p) ∈ P
          rw [MulAut.apply_inv_self]
          exact hp
      rw [heq]
      refine isProperParabolic_map_of_surjective e.toMonoidHom e.surjective hpar' ?_
      intro x hx
      have : x = 1 := e.injective (by rw [map_one]; exact hx)
      rw [this]
      exact Subgroup.one_mem _

end Field

end CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof
