module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts1
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NormalFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCoreAA1A
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField Subgroup CFSG.Open

local notation "G3F4" => Matrix.GeneralLinearGroup (Fin 3) OmegaField
local notation "GL3F4" => coordinateSemilinearGroup 3 OmegaField

private noncomputable def s16h_e3_Z3MatrixCoreAA1_conjSet
    (N : Subgroup GL3F4) (u : G3F4) : Set G3F4 :=
  {x | ∃ n : GL3F4, n ∈ N ∧ x = n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹}

private noncomputable def s16h_e3_Z3MatrixCoreAA1_Dp
    (N : Subgroup GL3F4) (u : G3F4) : Subgroup G3F4 :=
  Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_conjSet N u)

private noncomputable def s16h_e3_Z3MatrixCoreAA1_D
    (N : Subgroup GL3F4) (u : G3F4) : Subgroup GL3F4 :=
  (s16h_e3_Z3MatrixCoreAA1_Dp N u).map
    (SemidirectProduct.inl :
      G3F4 →* GL3F4)

private noncomputable def s16h_e3_Z3MatrixCoreAA1_iInl : G3F4 →* GL3F4 :=
  SemidirectProduct.inl

private noncomputable def s16h_e3_Z3MatrixCoreAA1_Zs : Subgroup G3F4 :=
  MonoidHom.range (Matrix.GeneralLinearGroup.scalar (Fin 3) : OmegaFieldˣ →* G3F4)

private noncomputable def s16h_e3_Z3MatrixCoreAA1_K' (K : Subgroup GL3F4) : Subgroup G3F4 :=
  K.comap s16h_e3_Z3MatrixCoreAA1_iInl

private noncomputable def s16h_e3_Z3MatrixCoreAA1_T
    (N : Subgroup GL3F4) (u : G3F4) : Set GL3F4 :=
  {y | ∃ n : GL3F4, n ∈ N ∧ y = n * SemidirectProduct.inl u * n⁻¹}

private lemma s16h_e3_Z3MatrixCoreAA1_inl_conj (n : GL3F4) (u : G3F4) :
    n * SemidirectProduct.inl u * n⁻¹ =
      SemidirectProduct.inl
        (n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹) := by
  calc n * SemidirectProduct.inl u * n⁻¹
      = (SemidirectProduct.inl n.left * SemidirectProduct.inr n.right) *
          SemidirectProduct.inl u *
          (SemidirectProduct.inl n.left * SemidirectProduct.inr n.right)⁻¹ := by
        rw [SemidirectProduct.inl_left_mul_inr_right]
    _ = SemidirectProduct.inl n.left *
          (SemidirectProduct.inr n.right * SemidirectProduct.inl u *
            (SemidirectProduct.inr n.right)⁻¹) * (SemidirectProduct.inl n.left)⁻¹ := by
        group
    _ = SemidirectProduct.inl n.left *
          SemidirectProduct.inl
            (glFieldAut (Fin 3) OmegaField n.right u) * (SemidirectProduct.inl n.left)⁻¹ := by
        rw [← map_inv (SemidirectProduct.inr) n.right, ← SemidirectProduct.inl_aut]
    _ = SemidirectProduct.inl
          (n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹) := by
        rw [← map_inv, ← map_mul, ← map_mul]

private lemma s16h_e3_Z3MatrixCoreAA1_map_conjSet (N : Subgroup GL3F4) (u : G3F4) :
    SemidirectProduct.inl '' s16h_e3_Z3MatrixCoreAA1_conjSet N u =
      s16h_e3_Z3MatrixCoreAA1_T N u := by
  ext y
  constructor
  · rintro ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, (s16h_e3_Z3MatrixCoreAA1_inl_conj n u).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨_, ⟨n, hn, rfl⟩, (s16h_e3_Z3MatrixCoreAA1_inl_conj n u).symm⟩

private lemma s16h_e3_Z3MatrixCoreAA1_D_eq_closure_T (N : Subgroup GL3F4) (u : G3F4) :
    s16h_e3_Z3MatrixCoreAA1_D N u = Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_T N u) := by
  rw [s16h_e3_Z3MatrixCoreAA1_D, s16h_e3_Z3MatrixCoreAA1_Dp, MonoidHom.map_closure,
    s16h_e3_Z3MatrixCoreAA1_map_conjSet]

private lemma s16h_e3_Z3MatrixCoreAA1_T_sq (N : Subgroup GL3F4) {u : G3F4}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∀ x ∈ s16h_e3_Z3MatrixCoreAA1_T N u, x ^ 2 = 1 ∧ x ≠ 1 := by
  rintro x ⟨n, -, rfl⟩
  have hiu : (SemidirectProduct.inl u : GL3F4) ^ 2 = 1 := by
    rw [← map_pow, hu2, map_one]
  constructor
  · calc (n * SemidirectProduct.inl u * n⁻¹) ^ 2
        = n * (SemidirectProduct.inl u) ^ 2 * n⁻¹ := by
          rw [pow_two, pow_two]; group
      _ = 1 := by rw [hiu]; group
  · intro h
    have h1 : (SemidirectProduct.inl u : GL3F4) = 1 := by
      calc (SemidirectProduct.inl u : GL3F4)
          = n⁻¹ * (n * SemidirectProduct.inl u * n⁻¹) * n := by group
        _ = n⁻¹ * 1 * n := by rw [h]
        _ = 1 := by group
    exact hu1 (SemidirectProduct.inl_injective h1)

private lemma s16h_e3_Z3MatrixCoreAA1_conjSet_sq (N : Subgroup GL3F4) {u : G3F4}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∀ x ∈ s16h_e3_Z3MatrixCoreAA1_conjSet N u, x ^ 2 = 1 ∧ x ≠ 1 := by
  intro x hx
  obtain ⟨n, hn, hxeq⟩ := hx
  have hT : n * SemidirectProduct.inl u * n⁻¹ ∈ s16h_e3_Z3MatrixCoreAA1_T N u := ⟨n, hn, rfl⟩
  have hsqT := s16h_e3_Z3MatrixCoreAA1_T_sq N hu2 hu1 _ hT
  have hinl : SemidirectProduct.inl x = n * SemidirectProduct.inl u * n⁻¹ := by
    rw [hxeq]
    exact (s16h_e3_Z3MatrixCoreAA1_inl_conj n u).symm
  constructor
  · have h2 : (SemidirectProduct.inl x : GL3F4) ^ 2 = 1 := by
      rw [hinl]
      exact hsqT.1
    exact SemidirectProduct.inl_injective (by simpa [map_pow] using h2)
  · intro h
    exact hsqT.2 (by rw [← hinl, h, map_one])

private lemma s16h_e3_Z3MatrixCoreAA1_closure_involutions_eq_top
    {G : Type*} [Group G] (D : Subgroup G) (s : Set G)
    (hD : D = Subgroup.closure s) (hs : ∀ x ∈ s, x ^ 2 = 1 ∧ x ≠ 1) :
    Subgroup.closure {x : ↥D | orderOf x = 2} = ⊤ := by
  have hsD : s ⊆ D := by rw [hD]; exact Subgroup.subset_closure
  have hgen : Subgroup.closure {x : ↥D | (x : G) ∈ s} = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    conv_rhs => rw [hD]
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨⟨y, hsD hy⟩, hy, rfl⟩
  have hsub : {x : ↥D | (x : G) ∈ s} ⊆ {x : ↥D | orderOf x = 2} := by
    rintro x hx
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    change orderOf x = 2
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hs x hx).1 (hs x hx).2
  exact top_le_iff.mp (hgen ▸ Subgroup.closure_mono hsub)

private lemma s16h_e3_Z3MatrixCoreAA1_Dp_le_comap
    (N K : Subgroup GL3F4) (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (u : G3F4) (huK : SemidirectProduct.inl u ∈ K) :
    s16h_e3_Z3MatrixCoreAA1_Dp N u ≤ s16h_e3_Z3MatrixCoreAA1_K' K := by
  rw [s16h_e3_Z3MatrixCoreAA1_Dp]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨n, hn, rfl⟩
  change SemidirectProduct.inl
    (n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹) ∈ K
  rw [← s16h_e3_Z3MatrixCoreAA1_inl_conj n u]
  exact (Subgroup.normal_subgroupOf_iff hKN).mp hKnorm (SemidirectProduct.inl u) n huK hn

private lemma s16h_e3_Z3MatrixCoreAA1_scalar_le_comap (K : Subgroup GL3F4)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : GL3F4) ∈ K) :
    s16h_e3_Z3MatrixCoreAA1_Zs ≤
      s16h_e3_Z3MatrixCoreAA1_K' K := by
  rintro x ⟨c, rfl⟩
  exact hZK c

private lemma s16h_e3_Z3MatrixCoreAA1_Dp_le_SL (N : Subgroup GL3F4) {u : G3F4}
    (hu2 : u ^ 2 = 1) :
    s16h_e3_Z3MatrixCoreAA1_Dp N u ≤
      (Matrix.GeneralLinearGroup.det (n := Fin 3) (R := OmegaField)).ker := by
  have hdet_u : Matrix.GeneralLinearGroup.det u = 1 := by
    ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using s16h_e3_z3_det_eq_one_of_sq hu2
  rw [s16h_e3_Z3MatrixCoreAA1_Dp]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨n, -, rfl⟩
  change Matrix.GeneralLinearGroup.det
    (n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹) = 1
  have hdet_aut : Matrix.GeneralLinearGroup.det
      (glFieldAut (Fin 3) OmegaField n.right u) = 1 := by
    change Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map n.right.toRingHom u) = 1
    rw [Matrix.GeneralLinearGroup.map_det, hdet_u, map_one]
  have hsplit : Matrix.GeneralLinearGroup.det
      (n.left * glFieldAut (Fin 3) OmegaField n.right u * n.left⁻¹) =
      Matrix.GeneralLinearGroup.det n.left * Matrix.GeneralLinearGroup.det
        (glFieldAut (Fin 3) OmegaField n.right u) *
        (Matrix.GeneralLinearGroup.det n.left)⁻¹ := by
    simp only [map_mul, map_inv]
  rw [hsplit, hdet_aut, mul_one, mul_inv_cancel]

private lemma s16h_e3_Z3MatrixCoreAA1_sylow_three_le_scalars
    (N K : Subgroup GL3F4) (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hno : ∀ P : Subgroup GL3F4, P ≤ K → IsElemAbelian 3 P → Nat.card ↥P < 9)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : GL3F4) ∈ K)
    (u : G3F4) (huK : SemidirectProduct.inl u ∈ K) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∀ P : Sylow 3 ↥(s16h_e3_Z3MatrixCoreAA1_Dp N u),
      (P : Subgroup ↥(s16h_e3_Z3MatrixCoreAA1_Dp N u)).map
          (s16h_e3_Z3MatrixCoreAA1_Dp N u).subtype ≤
        s16h_e3_Z3MatrixCoreAA1_Zs := by
  classical
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  set D' := s16h_e3_Z3MatrixCoreAA1_Dp N u with hD'def
  set Zs : Subgroup G3F4 :=
    s16h_e3_Z3MatrixCoreAA1_Zs with hZsdef
  have hD'K : D' ≤ s16h_e3_Z3MatrixCoreAA1_K' K :=
    s16h_e3_Z3MatrixCoreAA1_Dp_le_comap N K hKN hKnorm u huK
  have hZsK : Zs ≤ s16h_e3_Z3MatrixCoreAA1_K' K :=
    s16h_e3_Z3MatrixCoreAA1_scalar_le_comap K hZK
  have hno' : ∀ R : Subgroup G3F4,
      R ≤ s16h_e3_Z3MatrixCoreAA1_K' K →
      IsElemAbelian 3 R → Nat.card ↥R < 9 := by
    intro R hRK hR
    have hmap : IsElemAbelian 3 (R.map s16h_e3_Z3MatrixCoreAA1_iInl) :=
      hR.map _
    have hcard : Nat.card ↥(R.map s16h_e3_Z3MatrixCoreAA1_iInl) = Nat.card ↥R :=
      Subgroup.card_map_of_injective SemidirectProduct.inl_injective
    have hlt := hno _ ((Subgroup.map_le_iff_le_comap).mpr hRK) hmap
    rwa [hcard] at hlt
  intro P
  set R : Subgroup G3F4 := (P : Subgroup ↥D').map D'.subtype with hRdef
  have hR3 : IsPGroup 3 R := P.isPGroup'.map D'.subtype
  have hRK : R ≤ s16h_e3_Z3MatrixCoreAA1_K' K :=
    (Subgroup.map_subtype_le _).trans hD'K
  have hRZ3 : IsPGroup 3 ↥(R ⊔ Zs) := by
    have hZs3 : IsPGroup 3 Zs :=
      IsPGroup.of_card (G := ↥Zs) (n := 1) (by
        rw [hZsdef, show Nat.card ↥s16h_e3_Z3MatrixCoreAA1_Zs = 3 from
          s16h_e3_Z3MatrixCoreAA1A_scalar_card]
        norm_num)
    haveI : Zs.Normal :=
      ⟨fun z hz g => by
        have hcomm := (Subgroup.mem_center_iff.mp
          (s16h_e3_Z3MatrixCoreAA1A_scalar_le_center hz)) g
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hz⟩
    exact IsPGroup.to_sup_of_normal_right (G := G3F4) (p := 3) hR3 hZs3
  have hRZK : R ⊔ Zs ≤ s16h_e3_Z3MatrixCoreAA1_K' K :=
    sup_le hRK hZsK
  have hcyc : IsCyclic ↥(R ⊔ Zs) :=
    s16h_e3_Z3MatrixCoreAA1A_three_subgroup_cyclic hno' hRZK hRZ3
  have hRSL : R ≤ (Matrix.GeneralLinearGroup.det (n := Fin 3) (R := OmegaField)).ker :=
    (Subgroup.map_subtype_le _).trans (s16h_e3_Z3MatrixCoreAA1_Dp_le_SL N hu2)
  have hcard_dvd : Nat.card ↥R ∣ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥(R ⊔ Zs) := hcyc
    haveI : IsCyclic ↥R := Subgroup.isCyclic_of_le (le_sup_left : R ≤ R ⊔ Zs)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR3) x
    by_cases hk1 : k ≤ 1
    · rw [← orderOf_dvd_iff_pow_eq_one, hk]
      exact (pow_dvd_pow 3 hk1).trans (by norm_num)
    · exfalso
      have hk2 : 2 ≤ k := by omega
      have hord_y : orderOf (x ^ (3 ^ (k - 2))) = 9 := by
        have h1 : orderOf (x ^ (3 ^ (k - 2))) = orderOf x / 3 ^ (k - 2) :=
          orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 3 (by omega))
        have hk_sub : k - (k - 2) = 2 := by omega
        rw [h1, hk, Nat.pow_div (by omega) (by norm_num : 0 < 3), hk_sub]
      have hdet : (((R.subtype (x ^ (3 ^ (k - 2))) : G3F4)) :
          Matrix (Fin 3) (Fin 3) OmegaField).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det (R.subtype (x ^ (3 ^ (k - 2)))) = 1 :=
          hRSL (x ^ (3 ^ (k - 2))).2
        simpa using congrArg (fun z : OmegaFieldˣ => (z : OmegaField)) h1
      have hord_coe : orderOf (R.subtype (x ^ (3 ^ (k - 2)))) = 9 := by
        rw [orderOf_injective R.subtype R.subtype_injective]
        exact hord_y
      exact (s16h_e3_z3_no_order_nine hdet) hord_coe
  have hle : R.subgroupOf (R ⊔ Zs) ≤ Zs.subgroupOf (R ⊔ Zs) := by
    haveI : IsCyclic ↥(R ⊔ Zs) := hcyc
    refine (IsCyclic.subgroup_le_iff_card_dvd
      (H := R.subgroupOf (R ⊔ Zs)) (K := Zs.subgroupOf (R ⊔ Zs))).mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : R ≤ R ⊔ Zs)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Zs ≤ R ⊔ Zs)).toEquiv,
      hZsdef, show Nat.card ↥s16h_e3_Z3MatrixCoreAA1_Zs = 3 from
        s16h_e3_Z3MatrixCoreAA1A_scalar_card]
    exact hcard_dvd
  calc R = (R.subgroupOf (R ⊔ Zs)).map (R ⊔ Zs).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_left : R ≤ R ⊔ Zs)).symm
    _ ≤ (Zs.subgroupOf (R ⊔ Zs)).map (R ⊔ Zs).subtype := Subgroup.map_mono hle
    _ = Zs := Subgroup.map_subgroupOf_eq_of_le (le_sup_right : Zs ≤ R ⊔ Zs)

private lemma s16h_e3_Z3MatrixCoreAA1_sylow_three_central
    (N K : Subgroup GL3F4) (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hno : ∀ P : Subgroup GL3F4, P ≤ K → IsElemAbelian 3 P → Nat.card ↥P < 9)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : GL3F4) ∈ K)
    (u : G3F4) (huK : SemidirectProduct.inl u ∈ K) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∀ P : Sylow 3 ↥(s16h_e3_Z3MatrixCoreAA1_Dp N u),
      normalizer (P : Set ↥(s16h_e3_Z3MatrixCoreAA1_Dp N u)) ≤
        centralizer (P : Set ↥(s16h_e3_Z3MatrixCoreAA1_Dp N u)) := by
  classical
  set D' := s16h_e3_Z3MatrixCoreAA1_Dp N u with hD'def
  intro P
  have hPZ :=
    s16h_e3_Z3MatrixCoreAA1_sylow_three_le_scalars N K hKN hKnorm hno hZK u huK hu2 hu1 P
  have hPcenter : (P : Subgroup ↥D') ≤ Subgroup.center ↥D' := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have hpZ : D'.subtype p ∈ MonoidHom.range
        (Matrix.GeneralLinearGroup.scalar (Fin 3) : OmegaFieldˣ →* G3F4) :=
      hPZ (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)
    have hpc : D'.subtype p ∈ Subgroup.center G3F4 :=
      s16h_e3_Z3MatrixCoreAA1A_scalar_le_center hpZ
    exact (Subgroup.mem_center_iff.mp hpc) (D'.subtype q)
  have htop : Subgroup.centralizer (P : Set ↥D') = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (fun x hx => hPcenter hx)
  exact htop.symm ▸ le_top

private lemma s16h_e3_Z3MatrixCoreAA1_sylow_centralizer_transfer
    {G G' : Type*} [Group G] [Group G'] [Finite G'] (e : G ≃* G')
    (p : ℕ) [Fact p.Prime]
    (h : ∀ P : Sylow p G, normalizer (P : Set G) ≤ centralizer (P : Set G)) :
    ∀ P : Sylow p G', normalizer (P : Set G') ≤ centralizer (P : Set G') := by
  intro P
  let Q : Sylow p G :=
    Sylow.mapSurjective (f := e.symm.toMonoidHom) (fun x => e.symm.surjective x) P
  have hQmap : (Q : Subgroup G).map e.toMonoidHom = (P : Subgroup G') := by
    change ((P : Subgroup G').map e.symm.toMonoidHom).map e.toMonoidHom = (P : Subgroup G')
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G' := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hN : (Subgroup.normalizer (Q : Set G)).map e.toMonoidHom =
      Subgroup.normalizer (P : Set G') := by
    have := Subgroup.map_normalizer_eq_of_bijective (f := e.toMonoidHom)
      (Q : Subgroup G) e.bijective
    rw [hQmap] at this
    simpa using this
  calc Subgroup.normalizer (P : Set G')
      = (Subgroup.normalizer (Q : Set G)).map e.toMonoidHom := hN.symm
    _ ≤ (Subgroup.centralizer (Q : Set G)).map e.toMonoidHom := Subgroup.map_mono (h Q)
    _ ≤ Subgroup.centralizer (P : Set G') := by
        rintro g ⟨c, hc, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hp' : p ∈ (Q : Subgroup G).map e.toMonoidHom := by
          rw [hQmap]; exact hp
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp'
        have hcq : q * c = c * q := (Subgroup.mem_centralizer_iff.mp hc) q hq
        rw [← map_mul, ← map_mul, hcq]

theorem s16h_e3_z3_transvection_closure_hypotheses
    (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hO2 : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      (P.subgroupOf K).Normal → IsPGroup 2 P → P = ⊥)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    (hno : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      IsElemAbelian 3 P → Nat.card ↥P < 9)
    {u : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
    (huK : (SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    ∃ D : Subgroup (coordinateSemilinearGroup 3 OmegaField),
      D ≤ K ∧
      (D.subgroupOf N).Normal ∧
      D ≤ MonoidHom.range (SemidirectProduct.inl :
        Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
          coordinateSemilinearGroup 3 OmegaField) ∧
      Nontrivial ↥D ∧
      Subgroup.closure {x : ↥D | orderOf x = 2} = ⊤ ∧
      (∀ P : Subgroup ↥D, P.Normal → IsPGroup 2 P → P = ⊥) ∧
      Nat.card ↥D ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 ∧
      (∀ P : Sylow 3 ↥D, normalizer (P : Set ↥D) ≤ centralizer (P : Set ↥D)) ∧
      (∀ P : Sylow 7 ↥D, normalizer (P : Set ↥D) ≤ centralizer (P : Set ↥D)) := by
  classical
  haveI : Finite OmegaField := by
    haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
    exact Module.finite_of_finite (ZMod 2)
  haveI : Finite (OmegaField ≃+* OmegaField) :=
    Finite.of_injective (fun σ : OmegaField ≃+* OmegaField => (σ : OmegaField → OmegaField))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  haveI : Finite GL3F4 :=
    Finite.of_injective (fun g : GL3F4 => (g.left, g.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  set D' := s16h_e3_Z3MatrixCoreAA1_Dp N u with hD'def
  set D : Subgroup GL3F4 := s16h_e3_Z3MatrixCoreAA1_D N u with hDdef
  have hD'_eq : D' = Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_conjSet N u) := rfl
  have hD_eq : D = Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_T N u) :=
    s16h_e3_Z3MatrixCoreAA1_D_eq_closure_T N u
  have hDpK : D' ≤ K.comap (SemidirectProduct.inl : G3F4 →* GL3F4) :=
    s16h_e3_Z3MatrixCoreAA1_Dp_le_comap N K hKN hKnorm u huK
  have hDK : D ≤ K := by
    rw [hDdef, s16h_e3_Z3MatrixCoreAA1_D]
    exact (Subgroup.map_le_iff_le_comap).mpr hDpK
  have hDleN : D ≤ N := hDK.trans hKN
  have hDnorm : (D.subgroupOf N).Normal := by
    have hclN : Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_T N u) ≤ N := by
      apply (Subgroup.closure_le _).mpr
      rintro y ⟨m, hm, rfl⟩
      exact N.mul_mem (N.mul_mem hm (hKN huK)) (N.inv_mem hm)
    rw [hD_eq, Subgroup.normal_subgroupOf_iff hclN]
    intro x n hx hn
    have hTin : ∀ y ∈ s16h_e3_Z3MatrixCoreAA1_T N u, n * y * n⁻¹ ∈
        s16h_e3_Z3MatrixCoreAA1_T N u := by
      rintro y ⟨m, hm, rfl⟩
      exact ⟨n * m, N.mul_mem hn hm, by group⟩
    have hmap : (Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_T N u)).map
        (MulAut.conj n).toMonoidHom ≤ Subgroup.closure (s16h_e3_Z3MatrixCoreAA1_T N u) := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro z ⟨y, hy, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hTin y hy
    have hmem : MulAut.conj n x ∈ (Subgroup.closure
        (s16h_e3_Z3MatrixCoreAA1_T N u)).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have := hmap hmem
    rwa [MulAut.conj_apply] at this
  have huDp : u ∈ D' := by
    rw [hD'def, s16h_e3_Z3MatrixCoreAA1_Dp]
    exact Subgroup.subset_closure ⟨1, N.one_mem, by simp [s16h_e3_Z3MatrixCoreAA1_conjSet]⟩
  have huD : SemidirectProduct.inl u ∈ D := by
    rw [hDdef, s16h_e3_Z3MatrixCoreAA1_D]
    exact Subgroup.mem_map.mpr ⟨u, huDp, rfl⟩
  have hDnt : Nontrivial ↥D :=
    ⟨⟨SemidirectProduct.inl u, huD⟩, 1, fun h =>
      hu1 (SemidirectProduct.inl_injective (Subtype.ext_iff.mp h))⟩
  have hgen : Subgroup.closure {x : ↥D | orderOf x = 2} = ⊤ :=
    s16h_e3_Z3MatrixCoreAA1_closure_involutions_eq_top D
      (s16h_e3_Z3MatrixCoreAA1_T N u) hD_eq (s16h_e3_Z3MatrixCoreAA1_T_sq N hu2 hu1)
  have hDnormalK : (D.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDK]
    intro x k hx hk
    exact (Subgroup.normal_subgroupOf_iff hDleN).mp hDnorm x k hx (hKN hk)
  refine ⟨D, hDK, hDnorm, ?_, hDnt, hgen, ?_, ?_, ?_, ?_⟩
  · rw [hDdef, s16h_e3_Z3MatrixCoreAA1_D]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, rfl⟩
  · exact s16h_e3_Z3MatrixCoreAA1A_normal_two_eq_bot_of_le_normal hDK hDnormalK hO2
  · have hcard : Nat.card ↥D = Nat.card ↥D' := by
      rw [hDdef, s16h_e3_Z3MatrixCoreAA1_D]
      exact Subgroup.card_map_of_injective SemidirectProduct.inl_injective
    rw [hcard]
    exact s16h_e3_Z3MatrixCoreAA1A_card_SL ▸
      Subgroup.card_dvd_of_le (s16h_e3_Z3MatrixCoreAA1_Dp_le_SL N hu2)
  · have h3' :=
      s16h_e3_Z3MatrixCoreAA1_sylow_three_central N K hKN hKnorm hno hZK u huK hu2 hu1
    exact s16h_e3_Z3MatrixCoreAA1_sylow_centralizer_transfer
      (Subgroup.equivMapOfInjective D' (SemidirectProduct.inl : G3F4 →* GL3F4)
        SemidirectProduct.inl_injective) 3 h3'
  · have hgen' : Subgroup.closure {x : ↥D' | orderOf x = 2} = ⊤ := by
      rw [hD'_eq]
      exact s16h_e3_Z3MatrixCoreAA1_closure_involutions_eq_top D'
        (s16h_e3_Z3MatrixCoreAA1_conjSet N u) rfl
        (s16h_e3_Z3MatrixCoreAA1_conjSet_sq N hu2 hu1)
    have h3' :=
      s16h_e3_Z3MatrixCoreAA1_sylow_three_central N K hKN hKnorm hno hZK u huK hu2 hu1
    have hnot3 : ¬ 3 ∣ Nat.card ↥D' :=
      s16h_e3_not_dvd_card_of_closure_involutions (p := 3) (by norm_num) hgen' h3'
    have h7' : ∀ P : Sylow 7 ↥D', normalizer (P : Set ↥D') ≤ centralizer (P : Set ↥D') :=
      fun P => s16h_e3_z3_normalizer_seven hnot3 P
    exact s16h_e3_Z3MatrixCoreAA1_sylow_centralizer_transfer
      (Subgroup.equivMapOfInjective D' (SemidirectProduct.inl : G3F4 →* GL3F4)
        SemidirectProduct.inl_injective) 7 h7'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
