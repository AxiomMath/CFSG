module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.RootGroup
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.F4Eigen
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K]

@[expose] noncomputable def Dhom (K : Type) [Field K] :
    MulAut (CFSG.Open.StatedSL 3 K) →* MulAut (projectiveSL 3 K) :=
  (descendAut 3 K).comp
    (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toMonoidHom

theorem Dhom_injective (K : Type) [Field K] : Function.Injective (Dhom K) := by
  intro a b hab
  have h' : descendAut 3 K (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      3 K).symm a) = descendAut 3 K (MulAut.congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      3 K).symm b) := hab
  exact (MulAut.congr _).injective (descendAut_three_injective h')

theorem two_eq_zero_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (hF.trans (by norm_num))
  exact_mod_cast CharP.cast_eq_zero K 2

theorem ident_matrix (g : MulAut (CFSG.Open.StatedSL 3 K)) (A : GL (Fin 3) K)
    (hg : Dhom K g = conjAut 3 K A) (x : CFSG.Open.StatedSL 3 K) :
    (((g x : CFSG.Open.StatedSL 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      A.val * ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (A⁻¹).val := by
  set E := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K with hE
  have hT : descendAut 3 K (MulAut.congr E.symm g) =
      descendAut 3 K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A) :=
    hg
  have hT2 := descendAut_three_injective hT
  have h1 : E.symm (g x) = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 K A (E.symm x) := by
    have := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) => φ (E.symm x)) hT2
    simpa [MulAut.congr_apply] using this
  have key : g x = E (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 K A (E.symm x)) := by
    rw [← h1, E.apply_symm_apply]
  have hs : ((E.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 K (E.symm x),
      E.apply_symm_apply]
  rw [key, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, hs]

theorem three_ne_zero_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    (3 : K) ≠ 0 := by
  intro h
  have h2 := two_eq_zero_of_card_four hK
  have h1 : (1 : K) = 0 := by linear_combination h - h2
  exact one_ne_zero h1

theorem pow_three_units {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (c : Kˣ) :
    c ^ 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero
  rw [← Nat.card_eq_fintype_card, hK] at h
  ext
  simpa using h

theorem card_units_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card Kˣ = 3 := by
  have h1 : Nat.card Kˣ = Nat.card K - 1 := by
    classical
    have : Fintype K := Fintype.ofFinite K
    simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  rw [h1, hK]

theorem det_scalar_three {K : Type} [Field K] (c : Kˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) c) = c ^ 3 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.det_diagonal]

theorem det_eq_of_conjAut_eq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {A B : GL (Fin 3) K} (h : conjAut 3 K A = conjAut 3 K B) :
    Matrix.GeneralLinearGroup.det A = Matrix.GeneralLinearGroup.det B := by
  have hker : A * B⁻¹ ∈ (conjAut 3 K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [ker_conjAut_three] at hker
  have hker' : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = A * B⁻¹ := hker
  obtain ⟨c, hc⟩ := hker'
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) c * B := by
    rw [hc]
    group
  rw [hA, map_mul, det_scalar_three, pow_three_units hK c, one_mul]

theorem ringAut_orderOf_ne_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) : orderOf σ ≠ 3 := by
  intro h
  have h2 := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
    (K := K) (p := 2) (f := 2) Nat.prime_two (by norm_num) (by rw [hK]; norm_num) h).1
  omega

theorem mem_linearAutGroup_of_pow_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {b : MulAut (projectiveSL 3 K)} (hb : b ^ 3 = 1) : b ∈ linearAutGroup 3 K := by
  by_contra hD
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by norm_num) b hb hD
  exact ringAut_orderOf_ne_three hK σ hσ

theorem rootSL_stable_of_eigen {K : Type} [Field K] {g : MulAut (CFSG.Open.StatedSL 3 K)}
    {A : GL (Fin 3) K} (hg : Dhom K g = conjAut 3 K A) {u : Fin 3 → K} {l : K}
    (hAu : Matrix.mulVec (A : Matrix (Fin 3) (Fin 3) K) u = l • u) :
    ∀ v ∈ rootSL u, g v ∈ rootSL u := by
  intro v hv
  obtain ⟨ψ, hψ, hvψ⟩ := mem_rootGL.mp ((mem_rootSL v).mp hv)
  have hAB : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.mul_inv A
  have hBA : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 :=
    Units.inv_mul A
  refine (mem_rootSL _).mpr (mem_rootGL.mpr
    ⟨l • Matrix.vecMul ψ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      perp_conj hBA hAu hψ, ?_⟩)
  rw [ident_matrix g A hg v, hvψ]
  exact conj_elemMat hAB hAu

theorem sq_eq_one_rootGL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {u : Fin 3 → K}
    {g : GL (Fin 3) K} (hg : g ∈ rootGL u) : g ^ 2 = 1 := by
  obtain ⟨ψ, hψ, hgψ⟩ := mem_rootGL.mp hg
  have h2 := two_eq_zero_of_card_four hK
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two, hgψ, elemMat_mul u ψ ψ hψ,
    ← two_smul K ψ, h2, zero_smul, elemMat_zero]

theorem isPGroup_two_of_sq_eq_one {G : Type} [Group G] {V : Subgroup G}
    (h : ∀ x ∈ V, x ^ 2 = 1) : IsPGroup 2 V := by
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact Subtype.ext (by simpa using h g.1 g.2)

theorem isPGroup_two_rootSL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (u : Fin 3 → K) :
    IsPGroup 2 (rootSL u) := by
  apply isPGroup_two_of_sq_eq_one
  intro x hx
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact sq_eq_one_rootGL hK ((mem_rootSL x).mp hx)

noncomputable def detPGL (K : Type) [Field K] (f : MulAut (projectiveSL 3 K)) : Kˣ := by
  classical
  exact if h : f ∈ (conjAut 3 K).range then
    Matrix.GeneralLinearGroup.det (Classical.choose (MonoidHom.mem_range.mp h)) else 1

theorem detPGL_conjAut {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (A : GL (Fin 3) K) : detPGL K (conjAut 3 K A) = Matrix.GeneralLinearGroup.det A := by
  have h : conjAut 3 K A ∈ (conjAut 3 K).range := ⟨A, rfl⟩
  unfold detPGL
  rw [dif_pos h]
  exact det_eq_of_conjAut_eq hK (Classical.choose_spec (MonoidHom.mem_range.mp h))

theorem detPGL_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    detPGL K 1 = 1 := by
  have h := detPGL_conjAut hK (1 : GL (Fin 3) K)
  simp only [map_one] at h
  exact h

theorem detPGL_mul {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {f g : MulAut (projectiveSL 3 K)} (hf : f ∈ (conjAut 3 K).range)
    (hg : g ∈ (conjAut 3 K).range) : detPGL K (f * g) = detPGL K f * detPGL K g := by
  obtain ⟨A, rfl⟩ := hf
  obtain ⟨B, rfl⟩ := hg
  rw [← map_mul, detPGL_conjAut hK, detPGL_conjAut hK, detPGL_conjAut hK, map_mul]

theorem detPGL_inv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {f : MulAut (projectiveSL 3 K)} (hf : f ∈ (conjAut 3 K).range) :
    detPGL K f⁻¹ = (detPGL K f)⁻¹ := by
  have h := detPGL_mul hK hf (inv_mem hf)
  rw [mul_inv_cancel, detPGL_one hK] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem card_le_three_of_no_kernel {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (E : Subgroup (MulAut (projectiveSL 3 K))) (hE : E ≤ (conjAut 3 K).range)
    (hker : ∀ x ∈ E, detPGL K x = 1 → x = 1) : Nat.card E ≤ 3 := by
  have hinj : Function.Injective (fun x : E => detPGL K (x : MulAut (projectiveSL 3 K))) := by
    intro x y hxy
    have hxr := hE x.2
    have hyr := hE y.2
    have hmem : (x : MulAut (projectiveSL 3 K))⁻¹ * y ∈ E := E.mul_mem (E.inv_mem x.2) y.2
    have hxy' : detPGL K (x : MulAut (projectiveSL 3 K)) =
        detPGL K (y : MulAut (projectiveSL 3 K)) := hxy
    have h1 : detPGL K ((x : MulAut (projectiveSL 3 K))⁻¹ * y) = 1 := by
      rw [detPGL_mul hK (inv_mem hxr) hyr, detPGL_inv hK hxr, hxy', inv_mul_cancel]
    exact Subtype.ext (inv_mul_eq_one.mp (hker _ hmem h1))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_units_three hK] at this

theorem card_le_nine_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    Nat.card F ≤ 9 := by
  have hB : CFSG.Assembly.IsElemAbelian 3 (F.map (Dhom K)) := isElemAbelian_map _ hF
  have hle : F.map (Dhom K) ≤ linearAutGroup 3 K := by
    rintro _ ⟨f, hf, rfl⟩
    exact mem_linearAutGroup_of_pow_three hK (by rw [← map_pow, hF.2 f hf, map_one])
  have hcard := card_inf_linearAutGroup_three_le (three_ne_zero_of_card_four hK) hB
  rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective (Dhom_injective K)] at hcard
  exact hcard

theorem mem_range_of_mem_elemAb {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))} (hF : CFSG.Assembly.IsElemAbelian 3 F)
    {f : MulAut (CFSG.Open.StatedSL 3 K)} (hf : f ∈ F) :
    Dhom K f ∈ (conjAut 3 K).range := by
  have hlin := mem_linearAutGroup_of_pow_three hK (b := Dhom K f)
    (by rw [← map_pow, hF.2 f hf, map_one])
  rwa [linearAutGroup_three_eq_range] at hlin

theorem card_zpowers_eq_three {G : Type} [Group G] {f : G} (h3 : f ^ 3 = 1) (h1 : f ≠ 1) :
    Nat.card (Subgroup.zpowers f) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Nat.card_zpowers, orderOf_eq_prime h3 h1]

theorem stab_zpowers {X : Type} [Group X] {f0 : MulAut X} (h3 : f0 ^ 3 = 1) {V : Subgroup X}
    (hs : ∀ v ∈ V, f0 v ∈ V) : ∀ f ∈ Subgroup.zpowers f0, ∀ v ∈ V, f v ∈ V := by
  intro f hf v hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
  have h3' : f0 ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
  rw [zpow_eq_zpow_emod k h3']
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0))
  rw [hn, zpow_natCast]
  have hn3 : n < 3 := by omega
  interval_cases n
  · simpa using hv
  · simpa using hs v hv
  · rw [pow_two, MulAut.mul_apply]
    exact hs _ (hs v hv)

theorem exists_root_stable {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {f0 : MulAut (CFSG.Open.StatedSL 3 K)} (h3 : Dhom K f0 ^ 3 = 1)
    (hlin : Dhom K f0 ∈ (conjAut 3 K).range) (hdet : detPGL K (Dhom K f0) = 1) :
    ∃ u : Fin 3 → K, u ≠ 0 ∧ ∀ v ∈ rootSL u, f0 v ∈ rootSL u := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hlin
  have hdetA : Matrix.GeneralLinearGroup.det A = 1 := by
    rw [← hA, detPGL_conjAut hK] at hdet
    exact hdet
  have hdetM : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdetA, Units.val_one]
  have hk : A ^ 3 ∈ (conjAut 3 K).ker := by
    rw [MonoidHom.mem_ker, map_pow, hA, h3]
  rw [ker_conjAut_three] at hk
  have hk' : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = A ^ 3 := hk
  obtain ⟨c, hc⟩ := hk'
  have hcube : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = Matrix.scalar (Fin 3) (c : K) := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hc
    simpa [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] using this.symm
  obtain ⟨u, hu0, l, hAu⟩ := exists_eigenvector_of_cube_scalar hK _ hdetM (c : K) hcube
  exact ⟨u, hu0, rootSL_stable_of_eigen hA.symm hAu⟩

theorem caseA_zpowers {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    {f0 : MulAut (CFSG.Open.StatedSL 3 K)} (hf0 : f0 ∈ F) (hf1 : f0 ≠ 1)
    (hdet : detPGL K (Dhom K f0) = 1) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup (CFSG.Open.StatedSL 3 K),
      V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  have h3 : f0 ^ 3 = 1 := hF.2 f0 hf0
  have hD3 : Dhom K f0 ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  obtain ⟨u, hu0, hstab⟩ :=
    exists_root_stable hK hD3 (mem_range_of_mem_elemAb hK hF hf0) hdet
  refine ⟨Subgroup.zpowers f0, ?_, ?_, rootSL u, rootSL_ne_bot hu0, isPGroup_two_rootSL hK u,
    stab_zpowers h3 hstab⟩
  · rw [Subgroup.zpowers_le]
    exact hf0
  · rw [card_zpowers_eq_three h3 hf1]
    have := card_le_nine_of_card_four hK F hF
    omega

theorem caseB_trivial {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hB : ∀ f ∈ F, detPGL K (Dhom K f) = 1 → f = 1) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup (CFSG.Open.StatedSL 3 K),
      V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  have hE : F.map (Dhom K) ≤ (conjAut 3 K).range := by
    rintro _ ⟨f, hf, rfl⟩
    exact mem_range_of_mem_elemAb hK hF hf
  have hker : ∀ x ∈ F.map (Dhom K), detPGL K x = 1 → x = 1 := by
    rintro _ ⟨f, hf, rfl⟩ hd
    rw [hB f hf hd, map_one]
  have hle := card_le_three_of_no_kernel hK (F.map (Dhom K)) hE hker
  rw [Subgroup.card_map_of_injective (Dhom_injective K)] at hle
  have hu0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  refine ⟨⊥, bot_le, ?_, rootSL (![1, 0, 0] : Fin 3 → K), rootSL_ne_bot hu0,
    isPGroup_two_rootSL hK _, ?_⟩
  · rw [Subgroup.card_bot]
    omega
  · intro f hf v hv
    rw [Subgroup.mem_bot.mp hf]
    simpa using hv

theorem ks1012AutHyp_sl34 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup (CFSG.Open.StatedSL 3 K),
      V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  by_cases h : ∃ f0 ∈ F, f0 ≠ 1 ∧ detPGL K (Dhom K f0) = 1
  · obtain ⟨f0, hf0, hf1, hdet⟩ := h
    exact caseA_zpowers hK F hF hf0 hf1 hdet
  · refine caseB_trivial hK F hF ?_
    intro f hf hd
    by_contra hne
    exact h ⟨f, hf, hne, hd⟩

theorem isPGroup_map_mulEquiv {G H : Type} [Group G] [Group H] (p : ℕ) (φ : G ≃* H)
    {V : Subgroup G} (hV : IsPGroup p V) : IsPGroup p (V.map φ.toMonoidHom) := by
  intro x
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨k, hk⟩ := hV ⟨w, hw⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hw' : w ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hx : (x : H) = φ w := hwx.symm
  rw [Subgroup.coe_pow, Subgroup.coe_one, hx, ← map_pow, hw', map_one]

theorem ks1012AutHyp_sl34_of_mulEquiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (Q : Type) [Group Q] (e : Q ≃* CFSG.Open.StatedSL 3 K) (F : Subgroup (MulAut Q))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  obtain ⟨F₁, hF₁, hcard₁, V₁, hV₁ne, hV₁p, hV₁st⟩ :=
    ks1012AutHyp_sl34 hK (F.map (MulAut.congr e).toMonoidHom) (isElemAbelian_map _ hF)
  have hid : ∀ f : MulAut Q,
      (MulAut.congr e.symm).toMonoidHom ((MulAut.congr e).toMonoidHom f) = f := by
    intro f
    ext x
    simp [MulAut.congr_apply]
  refine ⟨F₁.map (MulAut.congr e.symm).toMonoidHom, ?_, ?_, V₁.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hfg⟩ := Subgroup.mem_map.mp (hF₁ hg)
    rw [← hfg, hid]
    exact hf
  · have h1 : Nat.card (F.map (MulAut.congr e).toMonoidHom) = Nat.card F :=
      Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom) (MulEquiv.injective _)
    have h2 : Nat.card (F₁.map (MulAut.congr e.symm).toMonoidHom) = Nat.card F₁ :=
      Subgroup.card_map_of_injective (f := (MulAut.congr e.symm).toMonoidHom)
        (MulEquiv.injective _)
    rw [h2]
    rw [h1] at hcard₁
    exact hcard₁
  · intro h
    apply hV₁ne
    apply Subgroup.map_injective (f := e.symm.toMonoidHom) (MulEquiv.injective _)
    rw [h, Subgroup.map_bot]
  · exact isPGroup_map_mulEquiv 2 e.symm hV₁p
  · intro g hg v hv
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have hkey : (MulAut.congr e.symm g') (e.symm w) = e.symm (g' w) := by
      simp [MulAut.congr_apply]
    show (MulAut.congr e.symm g') (e.symm w) ∈ V₁.map e.symm.toMonoidHom
    rw [hkey]
    exact Subgroup.mem_map.mpr ⟨g' w, hV₁st g' hg' w hw, rfl⟩

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
