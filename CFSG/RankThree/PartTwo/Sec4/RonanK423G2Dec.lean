module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
open scoped MatrixGroups

section SL2

variable {L : Type} [Field L]

theorem eq_one_of_mem_center_sl2 (hL : ringChar L = 2) {A : SL2 L}
    (hA : A ∈ Subgroup.center (SL2 L)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h2 : (2 : L) = 0 := by
    have : CharP L 2 := ringChar.of_eq hL
    exact CharP.cast_eq_zero L 2
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem commute_of_commute_nonscalar {B X Y : Matrix (Fin 2) (Fin 2) L}
    (hB : B 0 1 ≠ 0 ∨ B 1 0 ≠ 0 ∨ B 0 0 ≠ B 1 1) (hX : X * B = B * X) (hY : Y * B = B * Y) :
    X * Y = Y * X := by
  have eX : ∀ i j, (X * B) i j = (B * X) i j := fun i j => by rw [hX]
  have eY : ∀ i j, (Y * B) i j = (B * Y) i j := fun i j => by rw [hY]
  have x00 := eX 0 0
  have x01 := eX 0 1
  have x10 := eX 1 0
  have y00 := eY 0 0
  have y01 := eY 0 1
  have y10 := eY 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at x00 x01 x10 y00 y01 y10
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    rcases hB with hb | hc | had <;> grind

theorem commute_of_commute_order_three {X A B : SL2 L} (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1)
    (hAX : A * X = X * A) (hBX : B * X = X * B) : A * B = B * A := by
  have hns : (X : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 ∨ (X : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0 ∨
      (X : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ (X : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    by_contra h
    push Not at h
    obtain ⟨h01, h10, h00⟩ := h
    have hdet := X.2
    rw [Matrix.det_fin_two, h01, h10, h00] at hdet
    have h3' : ((X ^ 3 : SL(2, L)) : Matrix (Fin 2) (Fin 2) L) = 1 := by rw [hX3]; rfl
    rw [Matrix.SpecialLinearGroup.coe_pow] at h3'
    have h3 := congrFun (congrFun h3' 0) 0
    simp only [pow_three, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h00,
      Matrix.one_apply_eq] at h3
    have hl : (X : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by grind
    apply hX1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, hl]
  exact Subtype.ext (commute_of_commute_nonscalar hns (congrArg Subtype.val hAX)
    (congrArg Subtype.val hBX))

end SL2

section MS

variable {L : Type} [Field L]

theorem eq_one_of_rhoA_eq_rhoV
    (hL : ringChar L = 2) {C₁ C₂ : SL2 L}
    (h : simpleRootSL2 .G2 L g2ia C₁ = rhoV L C₂) : C₁ = 1 := by
  apply eq_one_of_mem_center_sl2 hL
  rw [Subgroup.mem_center_iff]
  intro B
  apply simpleRootSL2_injective_g2 (K := L) g2ia
  have hx : simpleRootSL2 .G2 L g2ia B ∈
      rootSubgroup .G2 L g2e0 ⊔ rootSubgroup .G2 L (-g2e0) := by
    have : simpleRootSL2 .G2 L g2ia B ∈ (simpleRootSL2 .G2 L g2ia).range := ⟨B, rfl⟩
    rwa [range_simpleRootSL2_g2] at this
  have hy : rhoV L C₂ ∈ rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ) := by
    rw [← range_rhoV]
    exact ⟨C₂, rfl⟩
  have hc := (KS11Lie2Proof.g2_commute' hx hy).eq
  rw [map_mul, map_mul, h]
  exact hc

end MS

section Split

variable {L : Type} [Field L]

theorem exists_rhoA_mul_rhoV_of_mem_torusGroup
    [Finite L] (hL : ringChar L = 2)
    {h : ModGL .G2 L} (hh : h ∈ torusGroup .G2 L) :
    ∃ r w : Lˣ, h = simpleRootSL2 .G2 L g2ia (HSL r) * rhoV L (HSL w) := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨r₀, hr₀⟩ := FiniteField.isSquare_of_char_two hL ((l g2ia : Lˣ) : L)
  have hr0 : r₀ ≠ 0 := by
    rintro rfl
    exact (l g2ia).ne_zero (by rw [hr₀]; simp)
  set r : Lˣ := Units.mk0 r₀ hr0 with hr
  have hrr : r ^ 2 = l g2ia := Units.ext (by rw [sq, Units.val_mul, hr₀]; rfl)
  refine ⟨r, l g2ir * r, ?_⟩
  rw [rhoA_HSL, rhoV_HSL, ← rootDiagUnit_mul]
  congr 1
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · have hc : Tag.G2.cartan g2ia g2ia = 2 := by decide
    simp [hc, hrr, Pi.mulSingle_eq_of_ne (show g2ia ≠ g2ir by decide)]
  · have hc : Tag.G2.cartan g2ia g2ir = -1 := by decide
    simp [hc]

variable [Finite L]

theorem exists_long_mul_short_split
    (hL : ringChar L = 2) (h31 : 3 ∣ Nat.card L - 1)
    {m : adjointGroup .G2 L} (hmM : m ∈ g2LongSL2 L) (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1)
    {x : adjointGroup .G2 L}
    (hx : x ∈ Subgroup.centralizer ({m} : Set (adjointGroup .G2 L))) :
    ∃ μ ∈ g2LongSL2 L, ∃ s ∈ g2ShortSL2 L, x = μ * s := by
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp hmM
  have hinj := simpleRootSL2_injective_g2 (K := L) g2ia
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hm3)
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := L)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hm1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom L))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m₀ : adjointGroup .G2 L := ⟨simpleRootSL2 .G2 L g2ia P, simpleRootSL2_mem_adjointGroup _ P⟩
    with hm₀
  have hm₀M : m₀ ∈ g2LongSL2 L := mem_g2LongSL2_iff.mpr ⟨P, rfl⟩
  have hmz : ((m₀ * m * m₀⁻¹ : adjointGroup .G2 L) : ModGL .G2 L) =
      rootDiagUnit .G2 (fun j => t ^ Tag.G2.cartan g2ia j) := by
    rw [coe_conj, ← hA, ← rhoA_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  have hcen : ((m₀ * x * m₀⁻¹ : adjointGroup .G2 L) : ModGL .G2 L) ∈
      torusGroup .G2 L ⊔ (rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ)) := by
    rw [← toralCentralizer_torusA ht3, ← mem_centralizer_iff_toral hmz]
    exact conj_mem_centralizer hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_rootPair (K := L) isRoot_g2δ)
  have hcen' : ((m₀ * x * m₀⁻¹ : adjointGroup .G2 L) : ModGL .G2 L) ∈
      ((torusGroup .G2 L ⊔ (rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ)) :
        Subgroup (ModGL .G2 L)) : Set (ModGL .G2 L)) := hcen
  rw [hset] at hcen'
  obtain ⟨h, hh, u, hu, hhu⟩ := hcen'
  obtain ⟨r, w, hrw⟩ := exists_rhoA_mul_rhoV_of_mem_torusGroup hL hh
  have hQv : rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ) ≤ adjointGroup .G2 L :=
    sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
  have hρv : rhoV L (HSL w) ∈ rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ) := by
    rw [← range_rhoV]
    exact ⟨HSL w, rfl⟩
  have hs' : rhoV L (HSL w) * u ∈ rootSubgroup .G2 L g2δ ⊔ rootSubgroup .G2 L (-g2δ) :=
    mul_mem hρv hu
  set s : adjointGroup .G2 L := ⟨rhoV L (HSL w) * u, hQv hs'⟩ with hsdef
  have hsS : s ∈ g2ShortSL2 L := hs'
  set μ₁ : adjointGroup .G2 L :=
    ⟨simpleRootSL2 .G2 L g2ia (HSL r), simpleRootSL2_mem_adjointGroup _ _⟩ with hμ₁
  have hμ₁M : μ₁ ∈ g2LongSL2 L := mem_g2LongSL2_iff.mpr ⟨HSL r, rfl⟩
  have e1 : m₀ * x * m₀⁻¹ = μ₁ * s := by
    apply Subtype.ext
    rw [← hhu, hrw, Subgroup.coe_mul]
    simp only [hμ₁, hsdef, mul_assoc]
  have hcomm : s * m₀ = m₀ * s := g2Short_commute_g2Long hsS hm₀M
  refine ⟨m₀⁻¹ * μ₁ * m₀, mul_mem (mul_mem (inv_mem hm₀M) hμ₁M) hm₀M, s, hsS, ?_⟩
  calc x = m₀⁻¹ * (m₀ * x * m₀⁻¹) * m₀ := by group
    _ = m₀⁻¹ * (μ₁ * s) * m₀ := by rw [e1]
    _ = m₀⁻¹ * μ₁ * (s * m₀) := by group
    _ = m₀⁻¹ * μ₁ * (m₀ * s) := by rw [hcomm]
    _ = m₀⁻¹ * μ₁ * m₀ * s := by group

end Split

section Twisted

theorem three_dvd_sq_sub_one' {q : ℕ} (h : 3 ∣ q + 1) : 3 ∣ q ^ 2 - 1 := by
  have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by rw [← Nat.sq_sub_sq, one_pow]
  rw [e]
  exact Dvd.dvd.mul_right h _

theorem rhoV_mem_adjointGroup
    {K : Type} [Field K] (A : SL2 K) :
    rhoV K A ∈ adjointGroup .G2 K := by
  rw [rhoV_apply]
  exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _) (simpleRootSL2_mem_adjointGroup _ _))
    (inv_mem (canonicalRep_mem_adjointGroup _ K _))

theorem exists_long_mul_short_twisted
    {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (h3 : 3 ∣ Nat.card K + 1) {m : adjointGroup .G2 K}
    (hmM : m ∈ g2LongSL2 K) (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1) {x : adjointGroup .G2 K}
    (hx : x ∈ Subgroup.centralizer ({m} : Set (adjointGroup .G2 K))) :
    ∃ μ ∈ g2LongSL2 K, ∃ s ∈ g2ShortSL2 K, x = μ * s := by
  obtain ⟨K₂, _, _, _, σ, hdeg, hσ⟩ := exists_quadratic_ext' K
  obtain ⟨hfin, -, hfix⟩ := CFSG.RankThree.QuadraticSL2.quadratic_frobenius hdeg σ hσ
  haveI : Finite K₂ := hfin
  have hcard := natCard_quadratic (K := K) (K₂ := K₂) hdeg
  have h31 : 3 ∣ Nat.card K₂ - 1 := by rw [hcard]; exact three_dvd_sq_sub_one' h3
  have hK₂2 : ringChar K₂ = 2 := by
    have : CharP K 2 := ringChar.of_eq hK2
    have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
    exact ringChar.eq K₂ 2
  have hσ' : (σ : K₂ →+* K₂).comp (algebraMap K K₂) = algebraMap K K₂ := by
    ext c
    exact (hfix _).mpr ⟨c, rfl⟩
  set ι := bcG2 K K₂
  have hιm3 : ι m ^ 3 = 1 := by rw [← map_pow, hm3, map_one]
  have hιm1 : ι m ≠ 1 := fun h => hm1 (bcG2_injective (h.trans (map_one ι).symm))
  obtain ⟨μ, hμ, s, hs, hxμs⟩ := exists_long_mul_short_split hK₂2 h31 (bcG2_mem_g2LongSL2 hmM)
    hιm3 hιm1 (map_mem_centralizer ι hx)
  obtain ⟨B₁, hB₁⟩ := mem_g2LongSL2_iff.mp hμ
  obtain ⟨B₂, hB₂⟩ := mem_g2ShortSL2_iff.mp hs
  have h1 : (ι x : ModGL .G2 K₂) = simpleRootSL2 .G2 K₂ g2ia B₁ * rhoV K₂ B₂ := by
    have := congrArg Subtype.val hxμs
    rw [Subgroup.coe_mul, ← hB₁, ← hB₂] at this
    exact this
  have h2 : baseChangeGL (σ : K₂ →+* K₂) (ι x : ModGL .G2 K₂) = (ι x : ModGL .G2 K₂) :=
    baseChangeGL_bcG2 (σ : K₂ →+* K₂) hσ' x
  have h3' : (ι x : ModGL .G2 K₂) =
      simpleRootSL2 .G2 K₂ g2ia (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₁) *
        rhoV K₂ (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₂) := by
    rw [← h2, h1, map_mul, baseChangeGL_simpleRootSL2_of_field, baseChangeGL_rhoV]
  have h4 := h1.symm.trans h3'
  have key : simpleRootSL2 .G2 K₂ g2ia
      ((Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₁)⁻¹ * B₁) =
      rhoV K₂ (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₂ * B₂⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc _ = (simpleRootSL2 .G2 K₂ g2ia (Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₁))⁻¹ *
          (simpleRootSL2 .G2 K₂ g2ia B₁ * rhoV K₂ B₂) * (rhoV K₂ B₂)⁻¹ := by group
      _ = _ := by rw [h4]; group
  have hB₁σ : Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₁ = B₁ :=
    inv_mul_eq_one.mp (eq_one_of_rhoA_eq_rhoV hK₂2 key)
  have hB₂σ : Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₂ = B₂ := by
    have h5 := eq_one_of_rhoA_eq_rhoV hK₂2 key
    rw [h5, map_one] at key
    have h6 : Matrix.SpecialLinearGroup.map (σ : K₂ →+* K₂) B₂ * B₂⁻¹ = 1 :=
      rhoV_injective (K := K₂) (by rw [← key, map_one])
    exact mul_inv_eq_one.mp h6
  obtain ⟨B₁', hB₁'⟩ := exists_sl2_eq_map_of_fixed σ hfix B₁ hB₁σ
  obtain ⟨B₂', hB₂'⟩ := exists_sl2_eq_map_of_fixed σ hfix B₂ hB₂σ
  set μ₀ : adjointGroup .G2 K :=
    ⟨simpleRootSL2 .G2 K g2ia B₁', simpleRootSL2_mem_adjointGroup _ _⟩ with hμ₀
  set s₀ : adjointGroup .G2 K := ⟨rhoV K B₂', rhoV_mem_adjointGroup _⟩ with hs₀
  refine ⟨μ₀, mem_g2LongSL2_iff.mpr ⟨B₁', rfl⟩, s₀, mem_g2ShortSL2_iff.mpr ⟨B₂', rfl⟩, ?_⟩
  have h5 : (ι x : ModGL .G2 K₂) = (ι (μ₀ * s₀) : ModGL .G2 K₂) := by
    rw [h1, map_mul, Subgroup.coe_mul]
    show _ = baseChangeGL (algebraMap K K₂) (simpleRootSL2 .G2 K g2ia B₁') *
      baseChangeGL (algebraMap K K₂) (rhoV K B₂')
    rw [baseChangeGL_simpleRootSL2_of_field, baseChangeGL_rhoV, hB₁', hB₂']
  exact bcG2_injective (Subtype.ext h5)

end Twisted

section Layer

open scoped commutatorElement

variable {X : Type} [Group X]

@[expose] def LayerData (b : X) : Prop :=
  CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ∧
    (∀ z ∈ Subgroup.center ↥⁅Subgroup.centralizer ({b} : Set X),
        Subgroup.centralizer ({b} : Set X)⁆, ∃ k : ℕ, z ^ 3 ^ k = 1) ∧
    ∃ A : Subgroup X, (∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) ∧
      (∀ a ∈ A, ∀ r ∈ ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆,
        a * r = r * a) ∧
      Subgroup.centralizer ({b} : Set X) ≤
        ⁅Subgroup.centralizer ({b} : Set X), Subgroup.centralizer ({b} : Set X)⁆ ⊔ A

theorem map_centralizer_singleton_equiv (e : X ≃* X) (b : X) :
    (Subgroup.centralizer ({b} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e b} : Set X) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa [map_mul] using this
  · intro h
    have := congrArg e.symm h
    simpa [map_mul] using this

theorem LayerData.of_mulEquiv (e : X ≃* X) {b : X} (h : LayerData (e b)) : LayerData b := by
  obtain ⟨hq, hz, A', hA'c, hA'R, hA'C⟩ := h
  set C : Subgroup X := Subgroup.centralizer ({b} : Set X) with hC
  have hmap : C.map e.toMonoidHom = Subgroup.centralizer ({e b} : Set X) :=
    map_centralizer_singleton_equiv e b
  have hR : (⁅C, C⁆).map e.toMonoidHom = ⁅Subgroup.centralizer ({e b} : Set X),
      Subgroup.centralizer ({e b} : Set X)⁆ := by
    rw [Subgroup.map_commutator, hmap]
  let φ : ↥⁅C, C⁆ ≃* ↥⁅Subgroup.centralizer ({e b} : Set X),
      Subgroup.centralizer ({e b} : Set X)⁆ :=
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hR)
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq, fun z hz' => ?_, ?_⟩
  · have hφz : φ z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz' ⊢
      intro y
      obtain ⟨y', rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz' y']
    obtain ⟨k, hk⟩ := hz _ hφz
    refine ⟨k, φ.injective ?_⟩
    rw [map_pow, hk, map_one]
  · set A : Subgroup X := A'.comap e.toMonoidHom with hA
    have hAmap : A.map e.toMonoidHom = A' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective _
    refine ⟨A, fun a ha a' ha' => e.injective ?_, fun a ha r hr => e.injective ?_, ?_⟩
    · rw [map_mul, map_mul]
      exact hA'c _ ha _ ha'
    · rw [map_mul, map_mul]
      exact hA'R _ ha _ (by rw [← hR]; exact ⟨r, hr, rfl⟩)
    · intro c hc
      have h1 : e c ∈ Subgroup.centralizer ({e b} : Set X) := by
        rw [← hmap]; exact ⟨c, hc, rfl⟩
      have h2 := hA'C h1
      rw [← hR, ← hAmap, ← Subgroup.map_sup] at h2
      obtain ⟨c', hc', hcc'⟩ := h2
      have : c' = c := e.injective hcc'
      rwa [this] at hc'

end Layer

section Long

open scoped commutatorElement

variable {K : Type} [Field K]

theorem exists_long_mul_short
    [Finite K] (hK2 : ringChar K = 2)
    {m : adjointGroup .G2 K} (hmM : m ∈ g2LongSL2 K) (hm3 : m ^ 3 = 1) (hm1 : m ≠ 1)
    {x : adjointGroup .G2 K} (hx : x ∈ Subgroup.centralizer ({m} : Set (adjointGroup .G2 K))) :
    ∃ μ ∈ g2LongSL2 K, ∃ s ∈ g2ShortSL2 K, x = μ * s := by
  rcases three_dvd_card_sub_one_or_add_one (K := K) (by rw [hK2]; norm_num) with h31 | h31
  · exact exists_long_mul_short_split hK2 h31 hmM hm3 hm1 hx
  · exact exists_long_mul_short_twisted hK2 h31 hmM hm3 hm1 hx

theorem commute_of_mem_long
    {x a b : adjointGroup .G2 K} (hx : x ∈ g2LongSL2 K)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (ha : a ∈ g2LongSL2 K) (hb : b ∈ g2LongSL2 K)
    (hax : a * x = x * a) (hbx : b * x = x * b) : a * b = b * a := by
  obtain ⟨X, hX⟩ := mem_g2LongSL2_iff.mp hx
  obtain ⟨A, hA⟩ := mem_g2LongSL2_iff.mp ha
  obtain ⟨B, hB⟩ := mem_g2LongSL2_iff.mp hb
  have hinj := simpleRootSL2_injective_g2 (K := K) g2ia
  have hAX : A * X = X * A := hinj (by
    rw [map_mul, map_mul, hA, hX]
    exact congrArg Subtype.val hax)
  have hBX : B * X = X * B := hinj (by
    rw [map_mul, map_mul, hB, hX]
    exact congrArg Subtype.val hbx)
  have hX3 : X ^ 3 = 1 := hinj (by
    rw [map_pow, hX, map_one]
    exact congrArg Subtype.val hx3)
  have hX1 : X ≠ 1 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    rw [← hX, map_one]
    rfl
  have hAB := commute_of_commute_order_three hX3 hX1 hAX hBX
  apply Subtype.ext
  change (a : ModGL .G2 K) * b = b * a
  rw [← hA, ← hB, ← map_mul, ← map_mul, hAB]

theorem layerData_of_long
    [Finite K] (hK2 : ringChar K = 2)
    (hK4 : 4 ≤ Nat.card K) {m : adjointGroup .G2 K} (hmM : m ∈ g2LongSL2 K) (hm3 : m ^ 3 = 1)
    (hm1 : m ≠ 1) : LayerData m := by
  set S : Subgroup (adjointGroup .G2 K) := g2ShortSL2 K with hSdef
  set M : Subgroup (adjointGroup .G2 K) := g2LongSL2 K with hMdef
  set C : Subgroup (adjointGroup .G2 K) := Subgroup.centralizer ({m} : Set (adjointGroup .G2 K))
    with hCdef
  set A : Subgroup (adjointGroup .G2 K) := M ⊓ C with hAdef
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
    (g2Short_commute_g2Long hs hmM)
  have hAc : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    commute_of_mem_long hmM hm3 hm1 ha.1 ha'.1
      (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
      (Subgroup.mem_centralizer_singleton_iff.mp ha'.2)
  have hAS : ∀ a ∈ A, ∀ r ∈ S, a * r = r * a := fun a ha r hr =>
    (g2Short_commute_g2Long hr ha.1).symm
  have hAnorm : A ≤ Subgroup.normalizer (S : Set (adjointGroup .G2 K)) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hAS a ha h hh).symm)
  have hCAS : C ≤ A ⊔ S := by
    intro x hx
    obtain ⟨μ, hμ, s, hs, rfl⟩ := exists_long_mul_short hK2 hmM hm3 hm1 hx
    have hμC : μ ∈ C := by
      have : μ = (μ * s) * s⁻¹ := by group
      rw [this]
      exact mul_mem hx (inv_mem (hSC hs))
    exact mul_mem (Subgroup.mem_sup_left ⟨hμ, hμC⟩) (Subgroup.mem_sup_right hs)
  have hperf : Group.IsPerfect ↥S := (isQuasisimple_g2ShortSL2 hK4).1
  have hR : ⁅C, C⁆ = S := by
    apply le_antisymm
    · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      rw [commutatorElement_def]
      exact commutator_mem_of_mem_sup hAc hAnorm (hCAS hx) (hCAS hy)
    · calc S = ⁅S, S⁆ := Subgroup.commutator_eq_self.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hSC hSC
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hR.symm)
    (isQuasisimple_g2ShortSL2 hK4), fun z hz => ?_, A, hAc, fun a ha r hr => ?_, ?_⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
    set ψ : ↥⁅C, C⁆ ≃* SL2 K := (MulEquiv.subgroupCongr hR).trans e.symm with hψ
    have hψz : ψ z ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul, hz y']
    have h1 : ψ z = 1 := eq_one_of_mem_center_sl2 hK2 hψz
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one]
    exact ψ.injective (by rw [h1, map_one])
  · rw [hR] at hr
    exact hAS a ha r hr
  · rw [hR, sup_comm]
    exact hCAS

end Long

end CFSG.RankThree.PartTwo.Sec4.RonanK423.G2
