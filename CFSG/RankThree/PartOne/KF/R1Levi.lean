module

public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PartOne.KF.LayerCover

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.RankThree.CALinearPlane

variable {K : Type} [Field K]

@[expose] noncomputable def diagSL (d : Fin 3 → Kˣ) (h : ∏ i, d i = 1) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal fun i => (d i : K), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, h, Units.val_one]⟩

theorem coe_diagSL (d : Fin 3 → Kˣ) (h : ∏ i, d i = 1) :
    ((diagSL d h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => (d i : K) := rfl

@[expose] def bVec (u : Kˣ) : Fin 3 → Kˣ := ![u, u, u⁻¹ * u⁻¹]

theorem prod_bVec (u : Kˣ) : ∏ i, bVec u i = 1 := by
  rw [Fin.prod_univ_three]
  have h0 : bVec u 0 = u := rfl
  have h1 : bVec u 1 = u := rfl
  have h2 : bVec u 2 = u⁻¹ * u⁻¹ := rfl
  rw [h0, h1, h2]
  group

@[expose] noncomputable def bSL (u : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  diagSL (bVec u) (prod_bVec u)

theorem coe_bSL (u : Kˣ) :
    ((bSL u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => (bVec u i : K) := rfl

theorem commute_diagSL_apply {d : Fin 3 → Kˣ} {h : ∏ i, d i = 1}
    {g : SpecialLinearGroup (Fin 3) K} (hg : g * diagSL d h = diagSL d h * g) (i j : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) K) i j * (d j : K) = (d i : K) * (g : Matrix (Fin 3) (Fin 3) K) i j := by
  have := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j) hg
  simpa [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, Matrix.mul_diagonal,
    Matrix.diagonal_mul] using this

theorem apply_eq_zero_of_commute_diagSL {d : Fin 3 → Kˣ} {h : ∏ i, d i = 1}
    {g : SpecialLinearGroup (Fin 3) K} (hg : g * diagSL d h = diagSL d h * g) {i j : Fin 3}
    (hij : d i ≠ d j) : (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have h1 := commute_diagSL_apply hg i j
  have h2 : (g : Matrix (Fin 3) (Fin 3) K) i j * ((d j : K) - (d i : K)) = 0 := by
    rw [mul_sub, h1]
    ring
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hij

theorem bVec_zero_ne_two {u : Kˣ} (hu : u ^ 3 ≠ 1) : bVec u 0 ≠ bVec u 2 := by
  intro h
  apply hu
  have h' : u = u⁻¹ * u⁻¹ := by simpa [bVec] using h
  calc u ^ 3 = u * u * u := by rw [pow_succ, pow_succ, pow_one]
    _ = (u⁻¹ * u⁻¹) * u * u := by rw [← h']
    _ = 1 := by group

theorem centralizer_bSL_block {u : Kˣ} (hu : u ^ 3 ≠ 1) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K))) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  have hg' : g * bSL u = bSL u * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have h02 : bVec u 0 ≠ bVec u 2 := bVec_zero_ne_two hu
  have h12 : bVec u 1 ≠ bVec u 2 := by simpa [bVec] using h02
  exact ⟨apply_eq_zero_of_commute_diagSL hg' h02, apply_eq_zero_of_commute_diagSL hg' h12,
    apply_eq_zero_of_commute_diagSL hg' h02.symm, apply_eq_zero_of_commute_diagSL hg' h12.symm⟩

@[expose] def jTwo : Finset (Fin 3) := {0, 1}

theorem card_jTwo : jTwo.card = 2 := by decide

theorem mem_blockJ_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ coordBlockSL K jTwo ↔ (g : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  rw [mem_coordBlockSL_iff]
  constructor
  · intro h
    have h02 := h 0 2 (Or.inr (by simp [jTwo]))
    have h12 := h 1 2 (Or.inr (by simp [jTwo]))
    have h20 := h 2 0 (Or.inl (by simp [jTwo]))
    have h21 := h 2 1 (Or.inl (by simp [jTwo]))
    have h22 := h 2 2 (Or.inl (by simp [jTwo]))
    simp at h02 h12 h20 h21 h22
    exact ⟨h02, h12, h20, h21, h22⟩
  · rintro ⟨h02, h12, h20, h21, h22⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [jTwo]

theorem blockJ_le_centralizer (u : Kˣ) :
    coordBlockSL K jTwo ≤ Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K)) := by
  intro g hg
  obtain ⟨h02, h12, h20, h21, h22⟩ := mem_blockJ_iff.1 hg
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_bSL, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp_all [bVec] <;> ring

theorem apply_two_two_ne_zero {u : Kˣ} (hu : u ^ 3 ≠ 1) {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K))) :
    (g : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
  obtain ⟨h02, h12, h20, h21⟩ := centralizer_bSL_block hu hg
  intro h22
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  simp [h02, h12, h20, h21, h22] at hdet

@[expose] noncomputable def phiB {u : Kˣ} (hu : u ^ 3 ≠ 1) :
    ↥(Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K))) →* Kˣ where
  toFun g := Units.mk0 (((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2)
    (apply_two_two_ne_zero hu g.2)
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    obtain ⟨-, -, h20, h21⟩ := centralizer_bSL_block hu g.2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21]

theorem phiB_apply {u : Kˣ} (hu : u ^ 3 ≠ 1)
    (g : ↥(Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K)))) :
    ((phiB hu g : Kˣ) : K) = ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 :=
  rfl

theorem ker_phiB {u : Kˣ} (hu : u ^ 3 ≠ 1) :
    (phiB (K := K) hu).ker =
      (coordBlockSL K jTwo).subgroupOf
        (Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_blockJ_iff]
  obtain ⟨h02, h12, h20, h21⟩ := centralizer_bSL_block hu g.2
  constructor
  · intro h
    have h22 : ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h
      rw [phiB_apply] at this
      simpa using this
    exact ⟨h02, h12, h20, h21, h22⟩
  · rintro ⟨-, -, -, -, h22⟩
    apply Units.ext
    rw [phiB_apply]
    simpa using h22

theorem perfectResidual_centralizer_bSL [Finite K] (hK : 4 ≤ Nat.card K) {u : Kˣ}
    (hu : u ^ 3 ≠ 1) :
    inSubgroup perfectResidual
        (Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K))) =
      coordBlockSL K jTwo := by
  set C := Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K)) with hC
  have hKJC := blockJ_le_centralizer (K := K) u
  have hker := ker_phiB (K := K) hu
  have : ((coordBlockSL K jTwo).subgroupOf C).Normal := hker ▸ MonoidHom.normal_ker _
  have hsolv : Group.IsSolvable (↥C ⧸ (coordBlockSL K jTwo).subgroupOf C) := by
    have h1 : Group.IsSolvable (↥C ⧸ (phiB (K := K) hu).ker) :=
      Group.isSolvable_of_isSolvable_injective
        (QuotientGroup.kerLift_injective (phiB (K := K) hu))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hker.symm).injective
  apply le_antisymm
  · have h1 := ((perfect_residual_characterization (G := ↥C)).2.2.2.2.1
      ((coordBlockSL K jTwo).subgroupOf C)).1 hsolv
    calc inSubgroup perfectResidual C = (perfectResidual ↥C).map C.subtype := rfl
      _ ≤ ((coordBlockSL K jTwo).subgroupOf C).map C.subtype := Subgroup.map_mono h1
      _ = coordBlockSL K jTwo := Subgroup.map_subgroupOf_eq_of_le hKJC
  · have hq : IsQuasisimple ↥(coordBlockSL K jTwo) :=
      isQuasisimple_coordBlockSL (by rw [card_jTwo]) hK
    have hperf : Group.IsPerfect ↥((coordBlockSL K jTwo).subgroupOf C) := by
      have := hq.1
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hKJC).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKJC).symm.surjective
    have h2 := (perfect_residual_transport (MonoidHom.id ↥C)).2.2 _ hperf
    calc coordBlockSL K jTwo = ((coordBlockSL K jTwo).subgroupOf C).map C.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hKJC).symm
      _ ≤ (perfectResidual ↥C).map C.subtype := Subgroup.map_mono h2

theorem isQuasisimple_perfectResidual_centralizer_bSL [Finite K] (hK : 4 ≤ Nat.card K) {u : Kˣ}
    (hu : u ^ 3 ≠ 1) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({bSL u} : Set (SpecialLinearGroup (Fin 3) K)))) := by
  rw [perfectResidual_centralizer_bSL hK hu]
  exact isQuasisimple_coordBlockSL (by rw [card_jTwo]) hK

theorem card_center_blockJ [CharP K 2] :
    Nat.card (Subgroup.center ↥(coordBlockSL K jTwo)) = 1 := by
  let e : SpecialLinearGroup (Fin jTwo.card) K ≃* ↥(coordBlockSL K jTwo) :=
    (MonoidHom.ofInjective (blockSLOn_injective (k := K) jTwo)).trans
      (MulEquiv.subgroupCongr (range_blockSLOn jTwo))
  rw [← card_center_mulEquiv e, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  have hbot : ∀ z : ↥(Subgroup.center (SpecialLinearGroup (Fin jTwo.card) K)), z = 1 := by
    intro z
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 z.2
    rw [Fintype.card_fin, card_jTwo] at hr
    have hr1 : r = 1 := by
      have h2 : (r - 1) ^ 2 = 0 := by
        have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        rw [this, hr, CharTwo.two_eq_zero, zero_mul, sub_zero]
        exact CharTwo.add_self_eq_zero 1
      exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hrz, hr1]
    simp
  exact (hbot a).trans (hbot b).symm

@[expose] def torusSL (p : ℕ) (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (torusSU p 3 K).comap SpecialLinearGroup.toGL

theorem mem_torusSL_iff {p : ℕ} {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ torusSL p K ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun i => (d i : K) := by
  rw [torusSL, Subgroup.mem_comap, mem_torusSU_iff]
  constructor
  · rintro ⟨d, h1, h2, h3⟩
    refine ⟨d, h1, h2, ?_⟩
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h3
    simpa [diagU_val] using this.symm
  · rintro ⟨d, h1, h2, h3⟩
    refine ⟨d, h1, h2, Units.ext ?_⟩
    simpa [diagU_val] using h3.symm

@[expose] def rhoVec (a : Kˣ) : Fin 3 → Kˣ := ![a, a⁻¹, 1]

theorem prod_rhoVec (a : Kˣ) : ∏ i, rhoVec a i = 1 := by
  rw [Fin.prod_univ_three]
  have h0 : rhoVec a 0 = a := rfl
  have h1 : rhoVec a 1 = a⁻¹ := rfl
  have h2 : rhoVec a 2 = 1 := rfl
  rw [h0, h1, h2]
  group

@[expose] noncomputable def rhoSL : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun a := diagSL (rhoVec a) (prod_rhoVec a)
  map_one' := by
    apply Subtype.ext
    rw [coe_diagSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rhoVec]
  map_mul' a b := by
    apply Subtype.ext
    simp only [coe_diagSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [rhoVec, mul_comm]

theorem coe_rhoSL (a : Kˣ) :
    ((rhoSL a : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => (rhoVec a i : K) := rfl

theorem rhoSL_injective : Function.Injective (rhoSL : Kˣ →* SpecialLinearGroup (Fin 3) K) := by
  intro a b h
  have := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_rhoSL, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem rhoSL_mem_blockJ (a : Kˣ) : (rhoSL a : SpecialLinearGroup (Fin 3) K) ∈ coordBlockSL K jTwo := by
  rw [mem_blockJ_iff, coe_rhoSL]
  simp [rhoVec]

theorem torusSL_inf_blockJ_eq (p : ℕ) :
    torusSL p K ⊓ coordBlockSL K jTwo = (rootsOfUnity p K).map rhoSL := by
  ext g
  constructor
  · rintro ⟨hgT, hgJ⟩
    obtain ⟨d, hd1, hd2, hd3⟩ := mem_torusSL_iff.1 hgT
    obtain ⟨-, -, -, -, h22⟩ := mem_blockJ_iff.1 hgJ
    rw [hd3, Matrix.diagonal_apply_eq] at h22
    have hd2' : d 2 = 1 := Units.ext h22
    have hprod := hd2
    rw [Fin.prod_univ_three, hd2', mul_one] at hprod
    have hd1' : d 1 = (d 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    refine ⟨d 0, (mem_rootsOfUnity p _).2 (hd1 0), ?_⟩
    apply Subtype.ext
    rw [coe_rhoSL, hd3]
    congr 1
    funext i
    fin_cases i
    · rfl
    · simp [rhoVec, hd1']
    · simp [rhoVec, hd2']
  · rintro ⟨a, ha, rfl⟩
    have ha' : a ^ p = 1 := (mem_rootsOfUnity p _).1 ha
    refine ⟨(mem_torusSL_iff (p := p)).2 ⟨rhoVec a, fun i => ?_, prod_rhoVec a, rfl⟩,
      rhoSL_mem_blockJ a⟩
    fin_cases i
    · exact ha'
    · simp [rhoVec, inv_pow, ha']
    · simp [rhoVec]

theorem card_torusSL_inf_blockJ {p : ℕ} (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(torusSL p K ⊓ coordBlockSL K jTwo) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [torusSL_inf_blockJ_eq, Subgroup.card_map_of_injective rhoSL_injective]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

@[expose] noncomputable def trSL (c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection 0 1 c, Matrix.det_transvection_of_ne 0 1 (by decide) c⟩

theorem coe_trSL (c : K) :
    ((trSL c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection 0 1 c := rfl

theorem trSL_zero : (trSL (0 : K) : SpecialLinearGroup (Fin 3) K) = 1 := by
  apply Subtype.ext
  simp [coe_trSL]

theorem trSL_mul (c d : K) :
    (trSL c : SpecialLinearGroup (Fin 3) K) * trSL d = trSL (c + d) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_trSL]
  exact Matrix.transvection_mul_transvection_same 0 1 (by decide) c d

@[expose] noncomputable def rootU (K : Type) [Field K] : Subgroup (SpecialLinearGroup (Fin 3) K) :=
  (({ toFun := fun c : Multiplicative K => trSL (Multiplicative.toAdd c)
      map_one' := trSL_zero
      map_mul' := fun _ _ => (trSL_mul _ _).symm } :
    Multiplicative K →* SpecialLinearGroup (Fin 3) K)).range

theorem trSL_mem_rootU (c : K) : (trSL c : SpecialLinearGroup (Fin 3) K) ∈ rootU K :=
  ⟨Multiplicative.ofAdd c, rfl⟩

theorem mem_rootU_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ rootU K ↔ ∃ c : K, g = trSL c :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => hc ▸ trSL_mem_rootU c⟩

theorem rootU_le_blockJ : rootU K ≤ coordBlockSL K jTwo := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootU_iff.1 hg
  rw [mem_blockJ_iff, coe_trSL]
  simp [Matrix.transvection]

theorem isPGroup_rootU [CharP K 2] : IsPGroup 2 ↥(rootU K) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := mem_rootU_iff.1 hg
  have hsq : (trSL c : SpecialLinearGroup (Fin 3) K) ^ 2 = 1 := by
    rw [pow_two, trSL_mul, CharTwo.add_self_eq_zero, trSL_zero]
  have hdvd : orderOf (⟨trSL c, hg⟩ : ↥(rootU K)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem torusSL_conj_rootU {p : ℕ} {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ torusSL p K) :
    ∀ x ∈ rootU K, g * x * g⁻¹ ∈ rootU K := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_rootU_iff.1 hx
  obtain ⟨d, -, -, hd⟩ := mem_torusSL_iff.1 hg
  have h : g * trSL c = trSL ((d 0 : K) * c * ((d 1)⁻¹ : Kˣ)) * g := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_trSL, hd]
    ext i j
    have h1 : ((d 1 : Kˣ) : K) ≠ 0 := (d 1).ne_zero
    fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]
  have : g * trSL c * g⁻¹ = trSL ((d 0 : K) * c * ((d 1)⁻¹ : Kˣ)) := by
    rw [h, mul_inv_cancel_right]
  rw [this]
  exact trSL_mem_rootU _

theorem trSL_one_not_commute_rhoSL [CharP K 2] {a : Kˣ} (ha : a ≠ 1) :
    (trSL (1 : K) : SpecialLinearGroup (Fin 3) K) * rhoSL a ≠
      rhoSL a * (trSL (1 : K) : SpecialLinearGroup (Fin 3) K) := by
  intro h
  have h1 := congrArg (fun x : SpecialLinearGroup (Fin 3) K =>
    (x : Matrix (Fin 3) (Fin 3) K) 0 1) h
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_trSL, coe_rhoSL, Matrix.transvection,
    Matrix.single_apply, Matrix.mul_apply, Fin.sum_univ_three, rhoVec] at h1
  have h2 : (a⁻¹ : Kˣ) = a := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h1)
  apply ha
  have h3 : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel a
  have h4 : ((a : K) - 1) ^ 2 = 0 := by
    have : ((a : K) - 1) ^ 2 = (a : K) * a - 2 * a + 1 := by ring
    rw [this, ← Units.val_mul, h3, CharTwo.two_eq_zero, zero_mul, sub_zero, Units.val_one]
    exact CharTwo.add_self_eq_zero 1
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4))

theorem torusSL_pow_eq_one {p : ℕ} {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ torusSL p K) :
    g ^ p = 1 := by
  obtain ⟨d, hd1, -, hd⟩ := mem_torusSL_iff.1 hg
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hd, Matrix.diagonal_pow]
  have : (fun i => (d i : K)) ^ p = 1 := funext fun i => by
    simp [← Units.val_pow_eq_pow_val, hd1 i]
  rw [this]
  rfl

theorem bSL_mem_torusSL {p : ℕ} {u : Kˣ} (hu : u ^ p = 1) : (bSL u : SpecialLinearGroup (Fin 3) K) ∈ torusSL p K := by
  refine (mem_torusSL_iff (p := p)).2 ⟨bVec u, fun i => ?_, prod_bVec u, rfl⟩
  fin_cases i
  · exact hu
  · exact hu
  · simp [bVec, mul_pow, inv_pow, hu]

theorem rhoSL_mem_torusSL {p : ℕ} {a : Kˣ} (ha : a ^ p = 1) : (rhoSL a : SpecialLinearGroup (Fin 3) K) ∈ torusSL p K := by
  refine (mem_torusSL_iff (p := p)).2 ⟨rhoVec a, fun i => ?_, prod_rhoVec a, rfl⟩
  fin_cases i
  · exact ha
  · simp [rhoVec, inv_pow, ha]
  · simp [rhoVec]

theorem torusSL_le_normalizer_rootU {p : ℕ} : torusSL p K ≤ Subgroup.normalizer (rootU K : Set (SpecialLinearGroup (Fin 3) K)) := fun g hg =>
  mem_normalizer_of_conj_mem (torusSL_conj_rootU hg) (fun y hy => by
    have := torusSL_conj_rootU ((torusSL p K).inv_mem hg) y hy
    simpa using this)

end CFSG.RankThree.PartOne.KFU
