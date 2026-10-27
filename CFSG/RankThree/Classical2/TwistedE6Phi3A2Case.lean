module

public import CFSG.RankThree.Classical2.TwistedE6Phi3A2

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical
open Matrix
open scoped Matrix commutatorElement MatrixGroups Pointwise

theorem commutator_sup_le_of_comm {G : Type*} [Group G] {H Q : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (Q : Set G)) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    ⁅H ⊔ Q, H ⊔ Q⁆ ≤ Q := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right H Q hHN
  have hc : ∀ h ∈ H, ∀ z ∈ Q, h * z * h⁻¹ ∈ Q := fun h hh z hz =>
    (Subgroup.mem_normalizer_iff.1 (hHN hh) z).1 hz
  have hc' : ∀ h ∈ H, ∀ z ∈ Q, h⁻¹ * z * h ∈ Q := fun h hh z hz => by
    have := hc h⁻¹ (inv_mem hh) z hz
    rwa [inv_inv] at this
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ (H : Set G) * (Q : Set G) := by rw [← hmul]; exact ha
  have hb' : b ∈ (H : Set G) * (Q : Set G) := by rw [← hmul]; exact hb
  obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := ha'
  obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := hb'
  have hv : h₂⁻¹ * z₁ * h₂ * z₂ * z₁⁻¹ ∈ Q :=
    mul_mem (mul_mem (hc' h₂ hh₂ z₁ hz₁) hz₂) (inv_mem hz₁)
  have hw : h₁ * (h₂⁻¹ * z₁ * h₂ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹ ∈ Q :=
    mul_mem (hc h₁ hh₁ _ hv) (inv_mem hz₂)
  have e2 : h₂ * h₁ * h₂⁻¹ = h₁ := by rw [← hH h₁ hh₁ h₂ hh₂, mul_inv_cancel_right]
  have e : ⁅h₁ * z₁, h₂ * z₂⁆ =
      h₂ * (h₁ * (h₂⁻¹ * z₁ * h₂ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹) * h₂⁻¹ := by
    rw [commutatorElement_def]
    calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹ =
        (h₂ * h₁ * h₂⁻¹) * z₁ * h₂ * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by rw [e2]; group
      _ = h₂ * (h₁ * (h₂⁻¹ * z₁ * h₂ * z₂ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹) * h₂⁻¹ := by group
  rw [e]
  exact hc h₂ hh₂ _ hw

variable {Ω : Type} [Field Ω]

theorem torusGroup_le_normalizer_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) :
    torusGroup Tag.E6 Ω ≤ Subgroup.normalizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
  intro h hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hmap := map_rootSpan_of_forall (f := (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom)
    (S := S) fun α hα => map_conj_rootDiagUnit_rootSubgroup a (hS α hα)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hmap] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := (MulAut.conj (rootDiagUnit Tag.E6 a)).injective hzy
    rw [← this]
    exact hz

theorem exists_eq_scalar_of_commute_conj {n : ℕ} (A B : GL (Fin n) Ω)
    (h : ∀ (i j : Fin n) (hij : i ≠ j),
      A * (B * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1) *
        B⁻¹) =
      (B * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1) * B⁻¹) *
        A) :
    ∃ c : Ω, (A : Matrix (Fin n) (Fin n) Ω) = scalar (Fin n) c := by
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_elementary (B⁻¹ * A * B) fun i j hij => by
    set E := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (1 : Ω))
    have hG : E * (B⁻¹ * A * B) = (B⁻¹ * A * B) * E := by
      calc E * (B⁻¹ * A * B) = B⁻¹ * ((B * E * B⁻¹) * A) * B := by group
        _ = B⁻¹ * (A * (B * E * B⁻¹)) * B := by rw [h i j hij]
        _ = (B⁻¹ * A * B) * E := by group
    have h2 := congrArg (fun M : GL (Fin n) Ω => (M : Matrix (Fin n) (Fin n) Ω)) hG
    simp only [Units.val_mul] at h2
    exact h2
  refine ⟨c, ?_⟩
  have hA : A = B * (B⁻¹ * A * B) * B⁻¹ := by group
  have hcomm : B * Matrix.GeneralLinearGroup.scalar (Fin n) c =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * B := Units.ext (by
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact ((Matrix.scalar_commute (c : Ω) (fun r => Commute.all _ r) _).eq).symm)
  rw [hA, ← hc, hcomm, mul_inv_cancel_right, Matrix.GeneralLinearGroup.coe_scalar]

theorem mem_torusGroup_of_diagonal_mul_eq_scalar {z : ModGL Tag.E6 Ω}
    (hz : z ∈ subsystemGroup Tag.E6 Ω support13) (s t : Ωˣ) {c : Ω}
    (h : diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₁ z = scalar (Fin 3) c) :
    z ∈ torusGroup Tag.E6 Ω := by
  have hinv : diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] *
      diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  have hz' : a2Mat₁ z = diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω) * c, ((t⁻¹ : Ωˣ) : Ω) * c, c] := by
    calc a2Mat₁ z = diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1] *
        (diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₁ z) := by
          rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = _ := by
          rw [h, Matrix.scalar_apply, diagonal_mul_diagonal]
          congr 1
          funext k
          fin_cases k <;> simp
  have hdet := det_a2Mat₁ hz
  rw [hz', det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hdet
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hdet
  set u₀ : Ωˣ := (s * t)⁻¹ * Units.mk0 c hc
  set u₁ : Ωˣ := t⁻¹ * Units.mk0 c hc
  have hu : ((u₀ * u₁)⁻¹ : Ωˣ) = Units.mk0 c hc := by
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    simp only [u₀, u₁, Units.val_mul, Units.val_mk0, Units.val_one]
    linear_combination hdet
  have hmat : a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) u₀ (u₀ * u₁)) = a2Mat₁ z := by
    rw [a2Mat₁_torus, hz', hu, inv_mul_cancel_left]
    simp only [u₀, u₁, Units.val_mul, Units.val_mk0]
  have hmem : e6TorusPair (e6Index 0) (e6Index 2) u₀ (u₀ * u₁) ∈
      subsystemGroup Tag.E6 Ω support13 := e6TorusPair_mem_subsystemGroup _ _ u₀ (u₀ * u₁)
  have heq : (⟨_, hmem⟩ : subsystemGroup Tag.E6 Ω support13) = ⟨z, hz⟩ :=
    a2Rep₁_injective (Subtype.ext (by rw [coe_a2Rep₁, coe_a2Rep₁]; exact hmat))
  have hz2 : e6TorusPair (e6Index 0) (e6Index 2) u₀ (u₀ * u₁) = z := congrArg Subtype.val heq
  rw [← hz2]
  exact e6TorusPair_mem_torusGroup _ _ _ _

theorem rootSpan_torusRootKernel_le_centralizer {x : ModGL Tag.E6 Ω}
    (hx : x ∈ torusGroup Tag.E6 Ω) :
    rootSpan Tag.E6 Ω (torusRootKernel x) ≤ Subgroup.centralizer {x} := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [torusRootKernel_rootDiagUnit]
  exact rootSpan_le_centralizer b le_rfl

theorem diagonal_mul_a2Mat₁_comm {h z p : ModGL Tag.E6 Ω} (hh : h ∈ torusGroup Tag.E6 Ω)
    {s t : Ωˣ}
    (hs : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 0) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 0) (s * c))
    (ht : ∀ c : Ω, h * xUnit Tag.E6 Ω (e6Index 2) c * h⁻¹ = xUnit Tag.E6 Ω (e6Index 2) (t * c))
    (hz : z ∈ subsystemGroup Tag.E6 Ω support13) (hp : p ∈ subsystemGroup Tag.E6 Ω support13)
    (hc : h * z * p = p * (h * z)) :
    diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₁ z * a2Mat₁ p =
      a2Mat₁ p * (diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1] * a2Mat₁ z) := by
  set D := diagonal ![((s * t : Ωˣ) : Ω), (t : Ω), 1]
  set D' := diagonal ![(((s * t)⁻¹ : Ωˣ) : Ω), ((t⁻¹ : Ωˣ) : Ω), 1]
  have hDD : D' * D = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> first | (simp; done) | (simp; field_simp)
  have hzi : z⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := inv_mem hz
  have hZZ : a2Mat₁ z⁻¹ * a2Mat₁ z = 1 := by
    rw [← a2Mat₁_mul hzi hz, inv_mul_cancel, a2Mat₁_one]
  have hzpz : z * p * z⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := mul_mem (mul_mem hz hp) hzi
  have e1 : h * (z * p * z⁻¹) * h⁻¹ = p := by
    calc h * (z * p * z⁻¹) * h⁻¹ = (h * z * p) * (h * z)⁻¹ := by group
      _ = (p * (h * z)) * (h * z)⁻¹ := by rw [hc]
      _ = p := by group
  have e2 := (a2Mat₁_conj_torus hh hs ht hzpz).2
  rw [e1, a2Mat₁_mul (mul_mem hz hp) hzi, a2Mat₁_mul hz hp] at e2
  calc D * a2Mat₁ z * a2Mat₁ p = D * a2Mat₁ z * a2Mat₁ p * (a2Mat₁ z⁻¹ * a2Mat₁ z) := by
        rw [hZZ, Matrix.mul_one]
    _ = (D * (a2Mat₁ z * a2Mat₁ p * a2Mat₁ z⁻¹) * D') * (D * a2Mat₁ z) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc D' D, hDD, Matrix.one_mul]
    _ = a2Mat₁ p * (D * a2Mat₁ z) := by rw [← e2]

section A2Case

variable {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω] {Fr : Ω →+* Ω}

theorem phi3_A2_case [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3TStar K σ Ω Fr g) (hxp : orderOf x = p)
    (hA2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 support13) :
    (∃ k : Subfield K, (∀ c, c ∈ k ↔ σ c = c) ∧
      Nonempty (↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) ≃* SL(3, k))) ∧
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) ∧
    Nat.card (Subgroup.center
        ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr)) =
      Nat.gcd 3 (ℓ ^ f - 1) ∧
    rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr ≤ phi3CStar K σ Ω g ∧
    ⁅phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x},
        phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}⁆ =
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr ∧
    (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
        Subgroup.centralizer
          (↑(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :
            Set (ModGL Tag.E6 Ω)) ≤ torusGroup Tag.E6 Ω ∧
    (phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}) ⊓
        Subgroup.centralizer
          (↑(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :
            Set (ModGL Tag.E6 Ω)) ≤ phi3Torus Ω Fr := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, hr⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  obtain ⟨-, hder, hCR, -, -, -, -, -⟩ := phi3_rational_layer hℓ hf hK hσ hFr hg hgn
  have hRG : phi3FixedGroup Ω Fr ≤ adjointGroup Tag.E6 Ω := fun y hy =>
    (mem_phi3FixedGroup_iff.1 hy).1
  have hxT0 : x ∈ phi3Torus Ω Fr := hx.1
  have hxH : x ∈ torusGroup Tag.E6 Ω := hxT0.1
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hxT : x ∈ phi3TorusTorsion Ω Fr p := ⟨hxT0, hxp'⟩
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, hQ₁, π, hθ⟩ := phi3_A2_transport hp3 hFr hζ hr hxT hx1 hA2
  obtain ⟨hmaps, Φ, hΦ₀, b, hΦt⟩ := exists_sl3_root_permuting_of_theta hFrs
    (phi3ThetaConj Ω Fr w) (phi3ThetaConj_injective w) π hθ
  obtain ⟨e, he⟩ := exists_mulEquiv_fixSubgroup hQ₁ hmaps Φ hΦ₀
  set k₀ := RingHom.eqLocusField σ (RingHom.id K) with hk₀
  have : Module.Finite k₀ K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k₀ K := Algebra.IsAlgebraic.of_finite k₀ K
  have : IsAlgClosure k₀ Ω := IsAlgClosure.ofAlgebraic k₀ K Ω
  have hk₀card : Nat.card k₀ = ℓ ^ f := natCard_eqLocusField hℓ hf hK hσ
  obtain ⟨-, ⟨H', hH'⟩, -, hqsΦ, -, hcardΦ⟩ := sln_root_permuting_frobenius_fixed_split hℓ hf
    hk₀card (le_refl 3) π Φ b (fun i j hij t => by rw [hΦt, hFr])
  let e₂₀ : SL(3, k₀) →* fixSubgroup Φ :=
    { toFun := fun Y => ⟨H' * Matrix.SpecialLinearGroup.map (algebraMap k₀ Ω) Y * H'⁻¹,
        (hH' _).2 ⟨Y, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun Y Z => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }
  have he₂ : Function.Bijective e₂₀ := by
    constructor
    · intro Y Z hYZ
      have h1 := congrArg Subtype.val hYZ
      change H' * _ * H'⁻¹ = H' * _ * H'⁻¹ at h1
      exact specialLinearGroup_map_injective (algebraMap k₀ Ω).injective
        (mul_left_cancel (mul_right_cancel h1))
    · rintro ⟨X, hX⟩
      obtain ⟨Y, hY⟩ := (hH' X).1 hX
      exact ⟨Y, Subtype.ext hY.symm⟩
  set e₂ := MulEquiv.ofBijective e₂₀ he₂
  have hqsP : CFSG.IsQuasisimple
      ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hqsΦ
  have : Group.IsPerfect ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :=
    hqsP.1
  have hPP : ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ =
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr := Subgroup.commutator_eq_self
  have hPC : rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr ≤ phi3CStar K σ Ω g := by
    rw [← hPP, ← hder]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hp7 := (phi3_prime_facts hp hp3 hpq).2.2
  have hCG := centralizer_eq_sup_of_pow_eq_one (by omega : 5 < p) hpΩ hxH hxp'
  have hDle : phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x} ≤
      torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x) := by
    rw [← hCG]
    exact le_inf (inf_le_left.trans (hCR.trans hRG)) inf_le_right
  have hHN : torusGroup Tag.E6 Ω ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) :=
    torusGroup_le_normalizer_rootSpan fun α hα => hα.1
  have hPD : rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr ≤
      phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x} :=
    le_inf hPC (inf_le_left.trans (rootSpan_torusRootKernel_le_centralizer hxH))
  have hDD : ⁅phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x},
      phi3CStar K σ Ω g ⊓ Subgroup.centralizer {x}⁆ =
      rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr := by
    refine le_antisymm (le_inf ?_ ?_) ?_
    · exact (Subgroup.commutator_mono hDle hDle).trans
        (commutator_sup_le_of_comm hHN fun a ha b hb => torusGroup_E6_comm ha hb)
    · refine (Subgroup.commutator_mono (inf_le_left.trans hCR) (inf_le_left.trans hCR)).trans ?_
      rw [hder]
      exact hCR
    · calc rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr =
          ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
            rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆ := hPP.symm
        _ ≤ _ := Subgroup.commutator_mono hPD hPD
  have hC6 : (torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω (torusRootKernel x)) ⊓
      Subgroup.centralizer
        (↑(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr) :
          Set (ModGL Tag.E6 Ω)) ≤ torusGroup Tag.E6 Ω := by
    rintro y ⟨hyHQ, hyc⟩
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHN
    have hy' : y ∈ (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) *
        (rootSpan Tag.E6 Ω (torusRootKernel x) : Set (ModGL Tag.E6 Ω)) := by
      rw [← hmul]
      exact hyHQ
    obtain ⟨h, hh, z, hz, rfl⟩ := hy'
    have hnN := canonicalRep_mem_normalizer (R := Ω) w
    set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
    have hh' : n * h * n⁻¹ ∈ torusGroup Tag.E6 Ω := (Subgroup.mem_normalizer_iff.1 hnN h).1 hh
    have hz' : n * z * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
      rw [← hQ₁]
      exact ⟨z, hz, rfl⟩
    obtain ⟨χ, hχ, -⟩ := exists_simple_root_characters hh'
    set s₀ := χ (e6Index 0)
    set t₀ := χ (e6Index 2)
    have hkey : ∀ (i j : Fin 3) (hij : i ≠ j),
        diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹) *
          ((H' * Matrix.SpecialLinearGroup.transvection hij 1 * H'⁻¹ : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) =
        ((H' * Matrix.SpecialLinearGroup.transvection hij 1 * H'⁻¹ : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) *
          (diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹)) := by
      intro i j hij
      have hmapT : Matrix.SpecialLinearGroup.map (algebraMap k₀ Ω)
          (Matrix.SpecialLinearGroup.transvection hij (1 : k₀)) =
          Matrix.SpecialLinearGroup.transvection hij 1 := by
        apply Subtype.ext
        change (1 + Matrix.single i j (1 : k₀)).map (algebraMap k₀ Ω) =
          1 + Matrix.single i j (1 : Ω)
        rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.map_single, map_one]
      have hX : H' * Matrix.SpecialLinearGroup.transvection hij 1 * H'⁻¹ ∈ fixSubgroup Φ :=
        (hH' _).2 ⟨Matrix.SpecialLinearGroup.transvection hij 1, by rw [hmapT]⟩
      set pp := e.symm ⟨_, hX⟩
      have hpp : a2Mat₁ (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) =
          ((H' * Matrix.SpecialLinearGroup.transvection hij 1 * H'⁻¹ : SL(3, Ω)) :
            Matrix (Fin 3) (Fin 3) Ω) := by
        rw [← he pp, MulEquiv.apply_symm_apply]
      have hppQ : n * (pp : ModGL Tag.E6 Ω) * n⁻¹ ∈ subsystemGroup Tag.E6 Ω support13 := by
        rw [← hQ₁]
        exact ⟨_, pp.2.1, rfl⟩
      have hc0 : h * z * (pp : ModGL Tag.E6 Ω) = pp * (h * z) :=
        ((Subgroup.mem_centralizer_iff.1 hyc) pp pp.2).symm
      have hc1 : (n * h * n⁻¹) * (n * z * n⁻¹) * (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) =
          (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by
        calc (n * h * n⁻¹) * (n * z * n⁻¹) * (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) =
            n * (h * z * (pp : ModGL Tag.E6 Ω)) * n⁻¹ := by group
          _ = n * ((pp : ModGL Tag.E6 Ω) * (h * z)) * n⁻¹ := by rw [hc0]
          _ = (n * (pp : ModGL Tag.E6 Ω) * n⁻¹) * ((n * h * n⁻¹) * (n * z * n⁻¹)) := by group
      have h2 := diagonal_mul_a2Mat₁_comm hh' (hχ (e6Index 0)) (hχ (e6Index 2)) hz' hppQ hc1
      rwa [hpp] at h2
    have hD₁ : diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] *
        diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      fin_cases k <;> first | (simp; done) | (simp; field_simp)
    have hD₂ : diagonal ![(((s₀ * t₀)⁻¹ : Ωˣ) : Ω), ((t₀⁻¹ : Ωˣ) : Ω), 1] *
        diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      fin_cases k <;> first | (simp; done) | (simp; field_simp)
    let Dg : GL (Fin 3) Ω := ⟨_, _, hD₁, hD₂⟩
    obtain ⟨A, hAdef⟩ : ∃ A : GL (Fin 3) Ω,
        A = Dg * Matrix.SpecialLinearGroup.toGL (a2Rep₁ Ω ⟨_, hz'⟩) := ⟨_, rfl⟩
    have hA : (A : Matrix (Fin 3) (Fin 3) Ω) =
        diagonal ![((s₀ * t₀ : Ωˣ) : Ω), (t₀ : Ω), 1] * a2Mat₁ (n * z * n⁻¹) := by
      rw [hAdef, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_a2Rep₁]
    obtain ⟨c, hc⟩ := exists_eq_scalar_of_commute_conj A (Matrix.SpecialLinearGroup.toGL H')
      fun i j hij => by
        rw [← map_inv, ← map_mul, ← map_mul]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hA]
        exact hkey i j hij
    rw [hA] at hc
    have hz'H := mem_torusGroup_of_diagonal_mul_eq_scalar hz' s₀ t₀ hc
    have hzH : z ∈ torusGroup Tag.E6 Ω := by
      have h3 := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) (n * z * n⁻¹)).1 hz'H
      rwa [show n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z by group] at h3
    exact mul_mem hh hzH
  refine ⟨⟨k₀, fun c => by rw [RingHom.mem_eqLocusField, RingHom.id_apply],
      ⟨e.trans e₂.symm⟩⟩, hqsP, (natCard_center_eq_of_mulEquiv e).trans hcardΦ, hPC, hDD, hC6,
    fun y hy => ⟨hC6 ⟨hDle hy.1, hy.2⟩, hCR hy.1.1⟩⟩

end A2Case

end CFSG.RankThree.Classical2
