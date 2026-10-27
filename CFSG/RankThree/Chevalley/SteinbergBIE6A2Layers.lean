module

public import CFSG.RankThree.Chevalley.SteinbergBIE6A2Cert
public import CFSG.RankThree.Chevalley.SteinbergBIE6Commutant
public import CFSG.RankThree.Chevalley.SteinbergBIE6SU2Lang
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

variable {Ω : Type} [Field Ω]

structure IsA2Layer (ψ : SL(3, Ω) →* ModGL Tag.E6 Ω) (J : Set (Fin Tag.E6.rank))
    (i j : Fin Tag.E6.rank) : Prop where
  injective : Function.Injective ψ
  range_eq : ψ.range = subsystemGroup Tag.E6 Ω J
  mem_iff : ∀ l, l ∈ J ↔ l = i ∨ l = j
  x_i : ∀ t : Ω, ψ (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t) =
    xUnit Tag.E6 Ω i t
  x_j : ∀ t : Ω, ψ (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t) =
    xUnit Tag.E6 Ω j t
  y_i : ∀ t : Ω, ψ (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t) =
    yUnit Tag.E6 Ω i t
  y_j : ∀ t : Ω, ψ (SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t) =
    yUnit Tag.E6 Ω j t

@[expose] def splitLayer (ψ : SL(3, Ω) →* ModGL Tag.E6 Ω) {k : Type} [Field k] (ι : k →+* Ω) :
    Subgroup (ModGL Tag.E6 Ω) :=
  (ψ.comp (SpecialLinearGroup.map ι)).range

@[expose] def unitaryLayer (ψ : SL(3, Ω) →* ModGL Tag.E6 Ω) (q : ℕ) (A : GL (Fin 3) Ω) :
    Set (ModGL Tag.E6 Ω) :=
  ψ '' {X | SpecialLinearGroup.toGL X ∈ (fun Y => A * Y * A⁻¹) '' unitarySet q 3}

theorem map_transvection {k : Type} [Field k] (ι : k →+* Ω) {a b : Fin 3} (hab : a ≠ b) (c : k) :
    SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection hab (ι c) := by
  ext p r
  simp

theorem sl3Emb₁₂_uSL_eq (t : Ω) :
    sl3Emb₁₂ (uSL t) = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t :=
  Subtype.ext (sl3Emb₁₂_uSL t)

theorem sl3Emb₁₂_vSL_eq (t : Ω) :
    sl3Emb₁₂ (vSL t) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t :=
  Subtype.ext (sl3Emb₁₂_vSL t)

theorem sl3Emb₂₃_uSL_eq (t : Ω) :
    sl3Emb₂₃ (uSL t) = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t :=
  Subtype.ext (sl3Emb₂₃_uSL t)

theorem sl3Emb₂₃_vSL_eq (t : Ω) :
    sl3Emb₂₃ (vSL t) = SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t :=
  Subtype.ext (sl3Emb₂₃_vSL t)

section Layer

variable {ψ : SL(3, Ω) →* ModGL Tag.E6 Ω} {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}

theorem IsA2Layer.mem_i (h : IsA2Layer ψ J i j) : i ∈ J := (h.mem_iff i).2 (Or.inl rfl)

theorem IsA2Layer.mem_j (h : IsA2Layer ψ J i j) : j ∈ J := (h.mem_iff j).2 (Or.inr rfl)

theorem IsA2Layer.mem (h : IsA2Layer ψ J i j) (X : SL(3, Ω)) :
    ψ X ∈ subsystemGroup Tag.E6 Ω J := by
  rw [← h.range_eq]
  exact ⟨X, rfl⟩

theorem IsA2Layer.comp_sl3Emb₁₂ (h : IsA2Layer ψ J i j) :
    ψ.comp sl3Emb₁₂ = simpleRootSL2 Tag.E6 Ω i :=
  eq_simpleRootSL2 i (fun t => by rw [MonoidHom.comp_apply, sl3Emb₁₂_uSL_eq, h.x_i])
    (fun t => by rw [MonoidHom.comp_apply, sl3Emb₁₂_vSL_eq, h.y_i])

theorem IsA2Layer.comp_sl3Emb₂₃ (h : IsA2Layer ψ J i j) :
    ψ.comp sl3Emb₂₃ = simpleRootSL2 Tag.E6 Ω j :=
  eq_simpleRootSL2 j (fun t => by rw [MonoidHom.comp_apply, sl3Emb₂₃_uSL_eq, h.x_j])
    (fun t => by rw [MonoidHom.comp_apply, sl3Emb₂₃_vSL_eq, h.y_j])

theorem IsA2Layer.mem_e6Commutant (h : IsA2Layer ψ J i j) {X : Module.End Ω (RootModule Tag.E6 Ω)}
    (hx : ∀ c, Commute X (xOp Tag.E6 Ω i c) ∧ Commute X (yOp Tag.E6 Ω i c) ∧
      Commute X (xOp Tag.E6 Ω j c) ∧ Commute X (yOp Tag.E6 Ω j c)) :
    X ∈ e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
  refine mem_e6Commutant_subsystemGroup (fun l hl c => ?_) (fun l hl c => ?_)
  · rcases (h.mem_iff l).1 hl with rfl | rfl
    exacts [(hx c).1, (hx c).2.2.1]
  · rcases (h.mem_iff l).1 hl with rfl | rfl
    exacts [(hx c).2.1, (hx c).2.2.2]

end Layer

theorem commute_conj_iff' (g : ModGL Tag.E6 Ω) (X Y : Module.End Ω (RootModule Tag.E6 Ω)) :
    Commute X ((g : Module.End Ω (RootModule Tag.E6 Ω)) * Y * ↑g⁻¹) ↔
      Commute ((↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑g) Y := by
  have e : (g : Module.End Ω (RootModule Tag.E6 Ω)) *
      ((↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * X * (g : Module.End Ω (RootModule Tag.E6 Ω))) *
        (↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) = X := by
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    simp only [mul_assoc, Units.mul_inv, mul_one]
  conv_lhs => rw [← e]
  exact commute_conj_iff g _ _

theorem commute_simpleRootSL2 {X : Module.End Ω (RootModule Tag.E6 Ω)} {i : Fin Tag.E6.rank}
    (hx : ∀ c, Commute X (xOp Tag.E6 Ω i c)) (hy : ∀ c, Commute X (yOp Tag.E6 Ω i c))
    (B : SL(2, Ω)) :
    Commute X (simpleRootSL2 Tag.E6 Ω i B : Module.End Ω (RootModule Tag.E6 Ω)) := by
  have hT : (commuteSubgroup X).comap (simpleRootSL2 Tag.E6 Ω i) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← (sl2_closure_upper_lower : Subgroup.closure (Set.range (uSL (K := Ω)) ∪
      Set.range vSL) = ⊤), Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change Commute X (simpleRootSL2 Tag.E6 Ω i (uSL c) : Module.End Ω (RootModule Tag.E6 Ω))
      rw [simpleRootSL2_uSL, coe_xUnit]
      exact hx c
    · change Commute X (simpleRootSL2 Tag.E6 Ω i (vSL c) : Module.End Ω (RootModule Tag.E6 Ω))
      rw [simpleRootSL2_vSL, coe_yUnit]
      exact hy c
  have hB : B ∈ (commuteSubgroup X).comap (simpleRootSL2 Tag.E6 Ω i) := hT ▸ Subgroup.mem_top B
  exact hB

theorem commute_of_conj_rootSL2 {k : Type} [Field k] [Fintype k] (ι : k →+* Ω)
    (hk : 3 ≤ Fintype.card k) {X : Module.End Ω (RootModule Tag.E6 Ω)} {i : Fin Tag.E6.rank}
    (C : SL(2, Ω))
    (h : ∀ A : SL(2, k), Commute X (simpleRootSL2 Tag.E6 Ω i
      (C * SpecialLinearGroup.map ι A * C⁻¹) : Module.End Ω (RootModule Tag.E6 Ω))) (c : Ω) :
    Commute X (xOp Tag.E6 Ω i c) ∧ Commute X (yOp Tag.E6 Ω i c) := by
  classical
  set g := simpleRootSL2 Tag.E6 Ω i C with hg
  set X' := (↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑g with hX'
  have hconj : ∀ B : SL(2, Ω), (simpleRootSL2 Tag.E6 Ω i (C * B * C⁻¹) :
      Module.End Ω (RootModule Tag.E6 Ω)) =
      ↑g * ↑(simpleRootSL2 Tag.E6 Ω i B) * ↑g⁻¹ := fun B => by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  have hF : 3 ≤ (Finset.univ.image ι).card := by
    rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ]
    exact hk
  have hx' : ∀ c ∈ Finset.univ.image ι, Commute X' (xOp Tag.E6 Ω i c) := by
    intro c hc
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hc
    have h1 := h (uSL b)
    rw [map_uSL, hconj, simpleRootSL2_uSL, coe_xUnit, commute_conj_iff'] at h1
    exact h1
  have hy' : ∀ c ∈ Finset.univ.image ι, Commute X' (yOp Tag.E6 Ω i c) := by
    intro c hc
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hc
    have h1 := h (vSL b)
    rw [map_vSL, hconj, simpleRootSL2_vSL, coe_yUnit, commute_conj_iff'] at h1
    exact h1
  have hall := commute_simpleRootSL2 (commute_xOp_of_three_le_card hF hx')
    (commute_yOp_of_three_le_card hF hy')
  have back : ∀ Y : Module.End Ω (RootModule Tag.E6 Ω),
      Commute X' ((↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * Y * ↑g) → Commute X Y := by
    intro Y hY
    have e : (g : Module.End Ω (RootModule Tag.E6 Ω)) *
        ((↑g⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * Y * ↑g) * ↑g⁻¹ = Y := by
      simp only [← mul_assoc, Units.mul_inv, one_mul]
      simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← e, commute_conj_iff']
    exact hY
  refine ⟨back _ ?_, back _ ?_⟩
  · have := hall (C⁻¹ * uSL c * C)
    rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL, Units.val_mul, Units.val_mul,
      coe_xUnit] at this
    exact this
  · have := hall (C⁻¹ * vSL c * C)
    rw [map_mul, map_mul, map_inv, simpleRootSL2_vSL, Units.val_mul, Units.val_mul,
      coe_yUnit] at this
    exact this

theorem two_of_prime_pow_eq_two {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (h : ℓ ^ d = 2) :
    ℓ = 2 := by
  have hdvd : ℓ ∣ 2 := h ▸ dvd_pow_self ℓ (by omega)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact absurd h1 hℓ.one_lt.ne'
  · exact h2

theorem charP_of_card {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ d) (ι : k →+* Ω) : CharP Ω ℓ := by
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ hd hk
  exact charP_of_injective_ringHom ι.injective ℓ

theorem fintype_card_of_natCard {ℓ d : ℕ} (hℓ : ℓ.Prime) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ d) : ∃ _ : Fintype k, Fintype.card k = ℓ ^ d := by
  have : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero _ hℓ.ne_zero)
  let _ := Fintype.ofFinite k
  exact ⟨inferInstance, by rw [← Nat.card_eq_fintype_card, hk]⟩

section Split

variable {ψ : SL(3, Ω) →* ModGL Tag.E6 Ω} {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}

theorem IsA2Layer.splitLayer_le (h : IsA2Layer ψ J i j) {k : Type} [Field k] (ι : k →+* Ω) :
    splitLayer ψ ι ≤ subsystemGroup Tag.E6 Ω J := by
  rintro _ ⟨A, rfl⟩
  exact h.mem _

theorem IsA2Layer.commute_of_mem_e6Commutant_splitLayer (h : IsA2Layer ψ J i j) {k : Type}
    [Field k] (ι : k →+* Ω) {X : Module.End Ω (RootModule Tag.E6 Ω)}
    (hX : X ∈ e6Commutant (splitLayer ψ ι : Set (ModGL Tag.E6 Ω))) (b : k) :
    Commute X (xOp Tag.E6 Ω i (ι b)) ∧ Commute X (yOp Tag.E6 Ω i (ι b)) ∧
      Commute X (xOp Tag.E6 Ω j (ι b)) ∧ Commute X (yOp Tag.E6 Ω j (ι b)) := by
  have hmem : ∀ {a c : Fin 3} (hac : a ≠ c),
      ψ (SpecialLinearGroup.transvection hac (ι b)) ∈ splitLayer ψ ι := fun hac =>
    ⟨SpecialLinearGroup.transvection hac b, by
      rw [MonoidHom.comp_apply, map_transvection]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hX _ (hmem (show (0 : Fin 3) ≠ 1 by decide))
    rwa [h.x_i, coe_xUnit] at this
  · have := hX _ (hmem (show (1 : Fin 3) ≠ 0 by decide))
    rwa [h.y_i, coe_yUnit] at this
  · have := hX _ (hmem (show (1 : Fin 3) ≠ 2 by decide))
    rwa [h.x_j, coe_xUnit] at this
  · have := hX _ (hmem (show (2 : Fin 3) ≠ 1 by decide))
    rwa [h.y_j, coe_yUnit] at this

theorem IsA2Layer.e6Commutant_splitLayer (h : IsA2Layer ψ J i j) (hcert : a2CertOK i j = true)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ d)
    (ι : k →+* Ω) :
    e6Commutant (splitLayer ψ ι : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
  classical
  refine Set.Subset.antisymm (fun X hX => ?_) (e6Commutant_anti (h.splitLayer_le ι))
  have hc := h.commute_of_mem_e6Commutant_splitLayer ι hX
  refine h.mem_e6Commutant fun c => ?_
  obtain ⟨_, hcard⟩ := fintype_card_of_natCard hℓ hk
  by_cases hq : 3 ≤ ℓ ^ d
  · have hF : 3 ≤ (Finset.univ.image ι).card := by
      rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, hcard]
      exact hq
    have hsub : ∀ c ∈ Finset.univ.image ι, ∃ b, c = ι b := fun c hc' => by
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hc'
      exact ⟨b, rfl⟩
    refine ⟨commute_xOp_of_three_le_card hF (fun c hc' => ?_) c,
      commute_yOp_of_three_le_card hF (fun c hc' => ?_) c,
      commute_xOp_of_three_le_card hF (fun c hc' => ?_) c,
      commute_yOp_of_three_le_card hF (fun c hc' => ?_) c⟩ <;>
    · obtain ⟨b, rfl⟩ := hsub c hc'
      first
      | exact (hc b).1
      | exact (hc b).2.1
      | exact (hc b).2.2.1
      | exact (hc b).2.2.2
  · have h2 : ℓ ^ d = 2 := by
      have h1 : 2 ≤ ℓ ^ d := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
      omega
    have hℓ2 := two_of_prime_pow_eq_two hℓ hd h2
    have : CharP Ω 2 := hℓ2 ▸ charP_of_card hℓ hd hk ι
    obtain ⟨h1, h2', h3, h4⟩ := hc 1
    rw [map_one] at h1 h2' h3 h4
    exact commute_of_a2CertOK hcert h1 h2' h3 h4 c

theorem sl3Emb₁₂_map {k : Type} [Field k] (ι : k →+* Ω) (A : SL(2, k)) :
    sl3Emb₁₂ (SpecialLinearGroup.map ι A) = SpecialLinearGroup.map ι (sl3Emb₁₂ A) := by
  ext p r
  fin_cases p <;> fin_cases r <;> simp [coe_sl3Emb₁₂, emb12Mat]

theorem IsA2Layer.simpleRootSL2_mem_splitLayer (h : IsA2Layer ψ J i j) {k : Type} [Field k]
    (ι : k →+* Ω) (A : SL(2, k)) :
    simpleRootSL2 Tag.E6 Ω i (SpecialLinearGroup.map ι A) ∈ splitLayer ψ ι := by
  rw [← h.comp_sl3Emb₁₂, MonoidHom.comp_apply, sl3Emb₁₂_map]
  exact ⟨sl3Emb₁₂ A, rfl⟩

end Split

section Unitary

variable {ψ : SL(3, Ω) →* ModGL Tag.E6 Ω} {J : Set (Fin Tag.E6.rank)} {i j : Fin Tag.E6.rank}

theorem exists_sl3_conj_eq [IsAlgClosed Ω] (A : GL (Fin 3) Ω) :
    ∃ B : SL(3, Ω), ∀ Y : GL (Fin 3) Ω,
      A * Y * A⁻¹ = SpecialLinearGroup.toGL B * Y * (SpecialLinearGroup.toGL B)⁻¹ := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) Ω).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((A : Matrix (Fin 3) (Fin 3) Ω).det)⁻¹
    (n := 3) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact inv_ne_zero hdet hz.symm
  have hBdet : (z • (A : Matrix (Fin 3) (Fin 3) Ω)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hz, inv_mul_cancel₀ hdet]
  refine ⟨⟨z • (A : Matrix (Fin 3) (Fin 3) Ω), hBdet⟩, fun Y => ?_⟩
  set u : Ωˣ := Units.mk0 z hz0
  have hB : SpecialLinearGroup.toGL (⟨z • (A : Matrix (Fin 3) (Fin 3) Ω), hBdet⟩ : SL(3, Ω)) =
      GeneralLinearGroup.scalar (Fin 3) u * A := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change z • (A : Matrix (Fin 3) (Fin 3) Ω) = _
    rw [Matrix.smul_eq_diagonal_mul]
    rfl
  have hcomm : ∀ g : GL (Fin 3) Ω, GeneralLinearGroup.scalar (Fin 3) u * g =
      g * GeneralLinearGroup.scalar (Fin 3) u := fun g => by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (u : Ω) (fun r => Commute.all _ r) _).eq
  rw [hB]
  calc A * Y * A⁻¹ = A * Y * A⁻¹ * GeneralLinearGroup.scalar (Fin 3) u *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) u * (A * Y * A⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem IsA2Layer.unitaryLayer_subset (h : IsA2Layer ψ J i j) (q : ℕ) (A : GL (Fin 3) Ω) :
    unitaryLayer ψ q A ⊆ subsystemGroup Tag.E6 Ω J := by
  rintro _ ⟨X, -, rfl⟩
  exact h.mem X

theorem unitaryLayer_eq_conj (ψ : SL(3, Ω) →* ModGL Tag.E6 Ω) (q : ℕ) (A : GL (Fin 3) Ω)
    (B : SL(3, Ω)) (hB : ∀ Y : GL (Fin 3) Ω,
      A * Y * A⁻¹ = SpecialLinearGroup.toGL B * Y * (SpecialLinearGroup.toGL B)⁻¹) :
    unitaryLayer ψ q A = (fun g => ψ B * g * (ψ B)⁻¹) '' unitaryLayer ψ q 1 := by
  ext g
  constructor
  · rintro ⟨X, ⟨Y, hY, hXY⟩, rfl⟩
    dsimp only at hXY
    refine ⟨ψ (B⁻¹ * X * B), ⟨B⁻¹ * X * B, ⟨Y, hY, ?_⟩, rfl⟩, ?_⟩
    · change 1 * Y * 1⁻¹ = _
      rw [one_mul, inv_one, mul_one, map_mul, map_mul, map_inv, ← hXY, hB]
      group
    · dsimp only
      rw [map_mul, map_mul, map_inv]
      group
  · rintro ⟨_, ⟨X, ⟨Y, hY, hXY⟩, rfl⟩, rfl⟩
    dsimp only at hXY
    rw [one_mul, inv_one, mul_one] at hXY
    refine ⟨B * X * B⁻¹, ⟨Y, hY, ?_⟩, ?_⟩
    · change A * Y * A⁻¹ = _
      rw [map_mul, map_mul, map_inv, ← hXY, hB]
    · dsimp only
      rw [map_mul, map_mul, map_inv]

theorem IsA2Layer.e6Commutant_unitaryLayer_one (h : IsA2Layer ψ J i j) {ℓ d : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k] [CharP k ℓ] (hk : Nat.card k = ℓ ^ d)
    [Algebra k Ω] [IsAlgClosure k Ω] (hq : 3 ≤ ℓ ^ d) :
    e6Commutant (unitaryLayer ψ (ℓ ^ d) 1) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
  refine Set.Subset.antisymm (fun X hX => ?_) (e6Commutant_anti (h.unitaryLayer_subset _ 1))
  obtain ⟨C, hC⟩ := exists_sl2_conj_unitary (Ω := Ω) hℓ hd hk
  obtain ⟨_, hcard⟩ := fintype_card_of_natCard hℓ hk
  have hk3 : 3 ≤ Fintype.card k := hcard ▸ hq
  have hmem₁ : ∀ A : SL(2, k), simpleRootSL2 Tag.E6 Ω i
      (C * SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹) ∈ unitaryLayer ψ (ℓ ^ d) 1 :=
    fun A => by
      rw [← h.comp_sl3Emb₁₂, MonoidHom.comp_apply]
      refine ⟨_, ⟨_, sl3Emb₁₂_mem_unitarySet (by omega) (hC A).1 (hC A).2, ?_⟩, rfl⟩
      dsimp only
      rw [one_mul, inv_one, mul_one]
  have hmem₂ : ∀ A : SL(2, k), simpleRootSL2 Tag.E6 Ω j
      (C * SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹) ∈ unitaryLayer ψ (ℓ ^ d) 1 :=
    fun A => by
      rw [← h.comp_sl3Emb₂₃, MonoidHom.comp_apply]
      refine ⟨_, ⟨_, sl3Emb₂₃_mem_unitarySet (by omega) (hC A).1 (hC A).2, ?_⟩, rfl⟩
      dsimp only
      rw [one_mul, inv_one, mul_one]
  have hi := commute_of_conj_rootSL2 (algebraMap k Ω) hk3 C fun A => hX _ (hmem₁ A)
  have hj := commute_of_conj_rootSL2 (algebraMap k Ω) hk3 C fun A => hX _ (hmem₂ A)
  exact h.mem_e6Commutant fun c => ⟨(hi c).1, (hi c).2, (hj c).1, (hj c).2⟩

theorem IsA2Layer.e6Commutant_unitaryLayer (h : IsA2Layer ψ J i j) {ℓ d : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ d)
    [Algebra k Ω] [IsAlgClosure k Ω] (hq : 3 ≤ ℓ ^ d) (A : GL (Fin 3) Ω) :
    e6Commutant (unitaryLayer ψ (ℓ ^ d) A) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ hd hk
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨B, hB⟩ := exists_sl3_conj_eq A
  rw [unitaryLayer_eq_conj ψ _ A B hB, e6Commutant_conj, h.e6Commutant_unitaryLayer_one hℓ hd hk hq,
    ← e6Commutant_conj]
  congr 1
  have hBQ := h.mem B
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact mul_mem (mul_mem hBQ hg') (inv_mem hBQ)
  · intro hg
    exact ⟨(ψ B)⁻¹ * g * ψ B, mul_mem (mul_mem (inv_mem hBQ) hg) hBQ, by group⟩

theorem IsA2Layer.exists_conj_simpleRootSL2_mem_unitaryLayer (h : IsA2Layer ψ J i j) {ℓ d : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k] (hk : Nat.card k = ℓ ^ d)
    [Algebra k Ω] [IsAlgClosure k Ω] (A : GL (Fin 3) Ω) :
    ∃ g ∈ subsystemGroup Tag.E6 Ω J, ∀ B : SL(2, k),
      g * simpleRootSL2 Tag.E6 Ω i (SpecialLinearGroup.map (algebraMap k Ω) B) * g⁻¹ ∈
        unitaryLayer ψ (ℓ ^ d) A := by
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ hd hk
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  obtain ⟨B₀, hB₀⟩ := exists_sl3_conj_eq A
  obtain ⟨C, hC⟩ := exists_sl2_conj_unitary (Ω := Ω) hℓ hd hk
  refine ⟨ψ B₀ * simpleRootSL2 Tag.E6 Ω i C, mul_mem (h.mem B₀) ?_, fun B => ?_⟩
  · rw [← h.comp_sl3Emb₁₂, MonoidHom.comp_apply]
    exact h.mem _
  rw [unitaryLayer_eq_conj ψ _ A B₀ hB₀]
  refine ⟨simpleRootSL2 Tag.E6 Ω i (C * SpecialLinearGroup.map (algebraMap k Ω) B * C⁻¹), ?_, ?_⟩
  · rw [← h.comp_sl3Emb₁₂, MonoidHom.comp_apply]
    refine ⟨_, ⟨_, sl3Emb₁₂_mem_unitarySet (Nat.one_le_iff_ne_zero.2
      (pow_ne_zero _ hℓ.ne_zero)) (hC B).1 (hC B).2, ?_⟩, rfl⟩
    dsimp only
    rw [one_mul, inv_one, mul_one]
  · simp only [map_mul, map_inv]
    group

end Unitary

end CFSG.RankThree.Chevalley
