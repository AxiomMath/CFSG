module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClBlocks
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.HardMathSupport.C14Cl

open Matrix CFSG CFSG.Open CFSG.Assembly CFSG.StandardType

theorem ntCore_of_conj (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R))
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y⁻¹ ∈ I) (h1 : (1 : MulAut R) ∈ I)
    (h : IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (Ebar : Subgroup (MulAut R)) (f : MulAut R),
      IsElemAbelian p Ebar → p ^ 2 ≤ Nat.card Ebar → (∀ e ∈ Ebar, e ∈ I) →
      f ∈ F → orderOf f = p → (∀ e ∈ Ebar, e * f = f * e) →
      (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) →
      ∃ s : ℕ, 2 ≤ s ∧ ∃ (c : ℤ) (k : ℕ), ¬ p ∣ k ∧
        c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
        (∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u) ∧
        (∀ u : MulAut R, GGL45NtCIp p I Ebar u → u ^ p ^ s = 1 ∧ f * u * f⁻¹ = u ^ c) ∧
        (∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
          w * u = u * w) ∧
        ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I Ebar a₁ ∧ GGL45NtCIp p I Ebar a₂ ∧
          ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j) :
    GGL45NtCore p R I F := by
  intro hsimp hnab Ebar f' hEab hcard hEI _ ⟨f, hfF, u, huI, hfo, hf'⟩ hcomm hSat
  have hIinv : ∀ x ∈ I, x⁻¹ ∈ I := fun x hx => by simpa using hI 1 h1 x hx
  have hImul : ∀ x ∈ I, ∀ y ∈ I, x * y ∈ I := fun x hx y hy => by
    simpa using hI x hx y⁻¹ (hIinv y hy)
  set κ := MulAut.conj u with hκ
  have hκa : ∀ x, κ x = u * x * u⁻¹ := fun x => MulAut.conj_apply u x
  obtain ⟨ι, hιdef⟩ : ∃ ι : MulAut R → MulAut R, ∀ x, ι x = u⁻¹ * x * u := ⟨_, fun _ => rfl⟩
  have hκι : ∀ x, κ (ι x) = x := fun x => by rw [hκa, hιdef]; group
  have hικ : ∀ x, ι (κ x) = x := fun x => by rw [hκa, hιdef]; group
  have hιI : ∀ x ∈ I, ι x ∈ I := fun x hx => by
    rw [hιdef]; exact hImul _ (hImul _ (hIinv u huI) x hx) u huI
  have hκI : ∀ x ∈ I, κ x ∈ I := fun x hx => by
    rw [hκa]; exact hImul _ (hImul u huI x hx) _ (hIinv u huI)
  let Ebar' : Subgroup (MulAut R) := Ebar.comap κ.toMonoidHom
  have hmem : ∀ x, x ∈ Ebar' ↔ κ x ∈ Ebar := fun x => Iff.rfl
  have hκf : κ f = f' := by rw [hκa, hf']
  have hEab' : IsElemAbelian p Ebar' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (κ.injective ?_)⟩⟩, fun x hx => κ.injective ?_⟩
    · have := hEab.1.is_comm.comm ⟨κ a, a.2⟩ ⟨κ b, b.2⟩
      simpa [map_mul] using congrArg Subtype.val this
    · rw [map_pow, map_one]; exact hEab.2 _ hx
  have hcard' : Nat.card Ebar' = Nat.card Ebar :=
    Nat.card_congr (Equiv.subtypeEquiv κ.toEquiv fun x => hmem x)
  have hEI' : ∀ e ∈ Ebar', e ∈ I := fun e he => by
    rw [← hικ e]; exact hιI _ (hEI _ he)
  have hcomm' : ∀ e ∈ Ebar', e * f = f * e := fun e he => κ.injective (by
    rw [map_mul, map_mul, hκf]; exact hcomm _ he)
  have hconj : ∀ r : R, κ (MulAut.conj r) = MulAut.conj (u r) := fun r => by
    rw [hκa]; ext x; simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hSat' : ∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar', e r = r) → f r = r →
      MulAut.conj r ∈ Ebar' := by
    intro r hr hEr hfr
    rw [hmem, hconj]
    refine hSat (u r) (by rw [← map_pow, hr, map_one]) (fun e he => ?_) ?_
    · have h' := hEr (ι e) (by rw [hmem, hκι]; exact he)
      have : u (ι e r) = u r := by rw [h']
      simpa [hιdef, MulAut.mul_apply] using this
    · rw [hf']; simp [MulAut.mul_apply, hfr]
  obtain ⟨s, hs2, c, k, hk, hc, H1, H2, H3, a₁, a₂, ha₁, ha₂, hind⟩ :=
    h hsimp hnab Ebar' f hEab' (hcard'.symm ▸ hcard) hEI' hfF hfo hcomm' hSat'
  have toP : ∀ v, GGL45NtCIp p I Ebar v → GGL45NtCIp p I Ebar' (ι v) := by
    rintro v ⟨hvI, hvE, n, hn⟩
    refine ⟨hιI v hvI, fun e he => κ.injective ?_, n, κ.injective ?_⟩
    · rw [map_mul, map_mul, hκι]; exact hvE _ he
    · rw [map_pow, hκι, hn, map_one]
  have ofP : ∀ v, GGL45NtCIp p I Ebar' v → GGL45NtCIp p I Ebar (κ v) := by
    rintro v ⟨hvI, hvE, n, hn⟩
    refine ⟨hκI v hvI, fun e he => ?_, n, by rw [← map_pow, hn, map_one]⟩
    have := hvE (ι e) (by rw [hmem, hκι]; exact he)
    have := congrArg κ this
    rwa [map_mul, map_mul, hκι] at this
  refine ⟨s, hs2, c, k, hk, hc, fun v w hv hw => ?_, fun v hv => ?_, fun v hv w hw hwE => ?_,
    κ a₁, κ a₂, ofP _ ha₁, ofP _ ha₂, fun i j hij => hind i j (κ.injective ?_)⟩
  · have := congrArg κ (H1 _ _ (toP v hv) (toP w hw))
    rwa [map_mul, map_mul, hκι, hκι] at this
  · obtain ⟨h2a, h2b⟩ := H2 _ (toP v hv)
    refine ⟨by rw [← hκι v, ← map_pow, h2a, map_one], ?_⟩
    have := congrArg κ h2b
    rwa [map_mul, map_mul, map_inv, map_zpow, hκf, hκι] at this
  · have := congrArg κ (H3 _ (toP v hv) (ι w) (hιI w hw) fun e he => κ.injective (by
      rw [map_mul, map_mul, hκι]; exact hwE _ he))
    rwa [map_mul, map_mul, hκι, hκι] at this
  · rw [map_mul, map_pow, map_pow, map_pow, map_pow, map_one]; exact hij

theorem sp_mem_iff_adj {K : Type} [Field K] [Fintype K] [CharP K 2] {m : ℕ} (g : GL (Fin m ⊕ Fin m) K) :
    g ∈ LargeEvenSpGroup K m ↔
      formAdj (RingEquiv.refl K) (LargeEvenSpForm K m) (g : Matrix _ _ K) * g = 1 := by
  set J := LargeEvenSpForm K m with hJdef
  have hJJ : J * (-J) = 1 := by
    rw [hJdef, largeEvenSpForm_def, Matrix.mul_neg, Matrix.fromBlocks_multiply]
    simp [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  have hJJ' : (-J) * J = 1 := by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact hJJ
  have hJinv : J⁻¹ = -J := Matrix.inv_eq_right_inv hJJ
  have hmap : ∀ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K, M.map (RingEquiv.refl K) = M :=
    fun M => by ext i j; rfl
  have key : ∀ h : GL (Fin m ⊕ Fin m) K, formAdj (RingEquiv.refl K) J (h : Matrix _ _ K) * (h : Matrix _ _ K) = 1 ↔
      (h : Matrix _ _ K)ᵀ * J * (h : Matrix _ _ K) = J := by
    intro h
    simp only [formAdj, hmap, hJinv]
    constructor
    · intro hh
      calc (h : Matrix _ _ K)ᵀ * J * (h : Matrix _ _ K)
          = J * ((-J) * (h : Matrix _ _ K)ᵀ * J * (h : Matrix _ _ K)) := by
            simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
        _ = J := by rw [hh, Matrix.mul_one]
    · intro hh
      calc (-J) * (h : Matrix _ _ K)ᵀ * J * (h : Matrix _ _ K)
          = (-J) * ((h : Matrix _ _ K)ᵀ * J * (h : Matrix _ _ K)) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hh, hJJ']
  rw [key, largeEvenSpGroup_def]
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      rw [Units.val_mul, Matrix.transpose_mul]
      calc (y : Matrix _ _ K)ᵀ * (x : Matrix _ _ K)ᵀ * J * ((x : Matrix _ _ K) * (y : Matrix _ _ K))
          = (y : Matrix _ _ K)ᵀ * ((x : Matrix _ _ K)ᵀ * J * (x : Matrix _ _ K)) * (y : Matrix _ _ K) := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hx, hy]
    | inv x _ hx =>
      have hxi : (x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hxt : ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * (x : Matrix _ _ K)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hxi, Matrix.transpose_one]
      calc ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * J * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
          = ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * ((x : Matrix _ _ K)ᵀ * J * (x : Matrix _ _ K)) *
              ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by rw [hx]
        _ = J := by
            simp only [← Matrix.mul_assoc, hxt, Matrix.one_mul]
            rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
  · exact fun hg => Subgroup.subset_closure hg

theorem sp_proj_bijective {K : Type} [Field K] [Fintype K] [CharP K 2] (m : ℕ) :
    Function.Bijective (LargeEvenProjMk (LargeEvenSpGroup K m)) := by
  refine ⟨?_, QuotientGroup.mk_surjective⟩
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgs
  rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hgs
  obtain ⟨c, rfl⟩ := hgs
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show Matrix.GeneralLinearGroup.scalar _ c = 1
  rcases isEmpty_or_nonempty (Fin m ⊕ Fin m) with hι | hι
  · exact Units.ext (Subsingleton.elim _ _)
  have h := (sp_mem_iff_adj (K := K) _).1 hg
  have hc : (c : K) ^ 2 = 1 := by
    have hJJ : -(LargeEvenSpForm K m) * LargeEvenSpForm K m = 1 := by
      rw [largeEvenSpForm_def, Matrix.neg_mul, Matrix.fromBlocks_multiply]
      simp [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    have hJinv : (LargeEvenSpForm K m)⁻¹ = -(LargeEvenSpForm K m) := Matrix.inv_eq_left_inv hJJ
    have hm : ∀ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K, M.map (RingEquiv.refl K) = M :=
      fun M => by ext i j; rfl
    have hs : ((Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) c : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (c : K) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      ext i j; by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
    simp only [formAdj, hm, hJinv] at h
    rw [hs] at h
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at h
    rw [hJJ] at h
    obtain ⟨i⟩ := hι
    have := congrFun (congrFun h i) i
    simpa [pow_two] using this
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one]
  have hc1 : (c : K) = 1 := by
    have h2 : ((c : K) - 1) ^ 2 = 0 := by
      rw [sub_sq, hc, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, sub_zero, CharTwo.add_self_eq_zero]
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  rw [hc1]; simp

theorem sp_fieldAut_orderOf {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ} (hm : 1 ≤ m) {f : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) (hfp : orderOf f = p) :
    ∃ σ₀ : K ≃+* K, orderOf σ₀ = p ∧ ∀ g : LargeEvenSpGroup K m,
      f (LargeEvenProjMk _ g) = LargeEvenProjMk _
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀ g) := by
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  refine ⟨σ, ?_, fun g => CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj σ g⟩
  rw [← hfp]
  exact (orderOf_injective _ (RecipeFieldSpU.fieldAut_injective hm) σ).symm


private def cSpC_I (K : Type) [Field K] (m : ℕ) :
    Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :=
  LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)

private def cSpC_F (K : Type) [Field K] (m : ℕ) :
    Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m))) :=
  LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))

private abbrev cSpC_G (K : Type) [Field K] (m : ℕ) : Subgroup (GL (Fin m ⊕ Fin m) K) :=
  LargeEvenSpGroup K m

private theorem cSpC_conj_injective {R : Type} [Group R] (hsimp : IsSimpleGroup R)
    (hnab : ∃ a b : R, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  obtain ⟨a, b, hab⟩ := hnab
  have hZ : Subgroup.center R = ⊥ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hcentral : x ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hconj := congrArg (fun f : MulAut R => f y) hx
    change x * y * x⁻¹ = y at hconj
    calc y * x = (x * y * x⁻¹) * x := by rw [hconj]
      _ = x * y := by group
  rwa [hZ, Subgroup.mem_bot] at hcentral

private theorem cSpC_sigmaGL_coe {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ClSetting K ι) (g : GL ι K) :
    ((S.σGL g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map S.σ₀ := by
  ext i j
  rfl

private theorem cSpC_transfer {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ}
    (S : ClSetting K (Fin m ⊕ Fin m))
    (κ : ↥(cSpC_G K m) →* MulAut (LargeEvenProj (cSpC_G K m)))
    (Ebar : Subgroup (MulAut (LargeEvenProj (cSpC_G K m))))
    (f : MulAut (LargeEvenProj (cSpC_G K m)))
    (hinjκ : Function.Injective κ) (hEbar_le : Ebar ≤ κ.range)
    (hI_mem : ∀ w ∈ cSpC_I K m, ∃ h : ↥(cSpC_G K m), κ h = w)
    (hE₀ : S.E₀ = (Ebar.comap κ).map (cSpC_G K m).subtype)
    (hSadj : ∀ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K,
      S.adj M = formAdj (RingEquiv.refl K) (LargeEvenSpForm K m) M)
    (hκ : ∀ g : ↥(cSpC_G K m), κ g = MulAut.conj (LargeEvenProjMk (cSpC_G K m) g))
    (hκfield : ∀ g : ↥(cSpC_G K m), f * κ g * f⁻¹ =
      κ ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K S.σ₀) g))
    (s : ℕ) (hs2 : 2 ≤ s) (k : ℕ) (hk : ¬ S.p ∣ k)
    (H1 : ∀ x y : GL (Fin m ⊕ Fin m) K, S.CentP (cSpC_G K m) x →
      S.CentP (cSpC_G K m) y → x * y = y * x)
    (H2 : ∀ x : GL (Fin m ⊕ Fin m) K, S.CentP (cSpC_G K m) x →
      x ^ S.p ^ s = 1 ∧ S.σGL x = x ^ (1 + (S.p : ℤ) ^ (s - 1) * k))
    (H3 : ∀ x : GL (Fin m ⊕ Fin m) K, S.CentP (cSpC_G K m) x →
      ∀ w ∈ (cSpC_G K m), S.adj (w : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * w = 1 →
        (∀ e ∈ S.E₀, w * e = e * w) → w * x = x * w)
    (a₁ a₂ : GL (Fin m ⊕ Fin m) K) (ha₁ : S.CentP (cSpC_G K m) a₁)
    (ha₂ : S.CentP (cSpC_G K m) a₂)
    (hind : ∀ i j : ℕ, (a₁ ^ S.p ^ (s - 1)) ^ i * (a₂ ^ S.p ^ (s - 1)) ^ j = 1 →
      S.p ∣ i ∧ S.p ∣ j) :
    ∃ s' : ℕ, 2 ≤ s' ∧ ∃ (c : ℤ) (k' : ℕ), ¬ S.p ∣ k' ∧
      c ≡ 1 + (S.p : ℤ) ^ (s' - 1) * k' [ZMOD (S.p : ℤ) ^ s'] ∧
      (∀ u v : MulAut (LargeEvenProj (cSpC_G K m)), GGL45NtCIp S.p (cSpC_I K m) Ebar u →
        GGL45NtCIp S.p (cSpC_I K m) Ebar v → u * v = v * u) ∧
      (∀ u : MulAut (LargeEvenProj (cSpC_G K m)), GGL45NtCIp S.p (cSpC_I K m) Ebar u →
        u ^ S.p ^ s' = 1 ∧ f * u * f⁻¹ = u ^ c) ∧
      (∀ u : MulAut (LargeEvenProj (cSpC_G K m)), GGL45NtCIp S.p (cSpC_I K m) Ebar u →
        ∀ w ∈ cSpC_I K m, (∀ e ∈ Ebar, w * e = e * w) → w * u = u * w) ∧
      ∃ a₁' a₂' : MulAut (LargeEvenProj (cSpC_G K m)),
        GGL45NtCIp S.p (cSpC_I K m) Ebar a₁' ∧
        GGL45NtCIp S.p (cSpC_I K m) Ebar a₂' ∧
        ∀ i j : ℕ, (a₁' ^ S.p ^ (s' - 1)) ^ i * (a₂' ^ S.p ^ (s' - 1)) ^ j = 1 →
          S.p ∣ i ∧ S.p ∣ j := by
  have hE0le : S.E₀ ≤ (cSpC_G K m) := by rw [hE₀]; exact Subgroup.map_subtype_le _
  have ofP : ∀ u : MulAut (LargeEvenProj (cSpC_G K m)), GGL45NtCIp S.p (cSpC_I K m) Ebar u →
      ∃ g : ↥(cSpC_G K m), S.CentP (cSpC_G K m) (g : GL (Fin m ⊕ Fin m) K) ∧ κ g = u := by
    intro u hu
    obtain ⟨huI, hucomm, huP⟩ := hu
    obtain ⟨g, hg⟩ := hI_mem u huI
    refine ⟨g, ⟨g.2, ⟨?_, ?_⟩, ?_⟩, hg⟩
    · rw [hSadj]
      exact (sp_mem_iff_adj (g : GL (Fin m ⊕ Fin m) K)).1 g.2
    · intro e he
      have heΓ : e ∈ (cSpC_G K m) := hE0le he
      have hmemK : (⟨e, heΓ⟩ : ↥(cSpC_G K m)) ∈ Ebar.comap κ := by
        change e ∈ S.E₀ at he
        rw [hE₀, Subgroup.mem_map] at he
        obtain ⟨x, hxK, hxe⟩ := he
        have hxe' : (⟨e, heΓ⟩ : ↥(cSpC_G K m)) = x := Subtype.ext hxe.symm
        rwa [hxe']
      have hmem : κ (⟨e, heΓ⟩ : ↥(cSpC_G K m)) ∈ Ebar := hmemK
      have hc := hucomm (κ (⟨e, heΓ⟩ : ↥(cSpC_G K m))) hmem
      have hge : g * (⟨e, heΓ⟩ : ↥(cSpC_G K m)) = (⟨e, heΓ⟩ : ↥(cSpC_G K m)) * g := by
        apply hinjκ
        rw [map_mul, map_mul, hg]
        exact hc
      exact congrArg Subtype.val hge
    · obtain ⟨n, hn⟩ := huP
      refine ⟨n, ?_⟩
      have h1 : g ^ S.p ^ n = 1 := by
        apply hinjκ
        rw [map_pow, hg, hn, map_one]
      simpa using congrArg Subtype.val h1
  have toP : ∀ (x : GL (Fin m ⊕ Fin m) K) (hx : S.CentP (cSpC_G K m) x),
      GGL45NtCIp S.p (cSpC_I K m) Ebar (κ ⟨x, hx.1⟩) := by
    intro x hx
    refine ⟨?_, ?_, ?_⟩
    · change κ ⟨x, hx.1⟩ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
        (LargeEvenGSpSet K m)
      rw [RecipeFieldSp.mem_conjImage_iff_inn]
      exact ⟨LargeEvenProjMk (cSpC_G K m) ⟨x, hx.1⟩, (hκ ⟨x, hx.1⟩).symm⟩
    · intro e he
      obtain ⟨g, hg⟩ := hEbar_le he
      have hgE0 : (g : GL (Fin m ⊕ Fin m) K) ∈ S.E₀ := by
        rw [hE₀, Subgroup.mem_map]
        exact ⟨g, by rwa [Subgroup.mem_comap, hg], rfl⟩
      have hc : (⟨x, hx.1⟩ : ↥(cSpC_G K m)) * g = g * ⟨x, hx.1⟩ := by
        apply Subtype.ext
        exact hx.2.1.2 _ hgE0
      rw [← hg]
      rw [← map_mul, ← map_mul, hc]
    · obtain ⟨n, hn⟩ := hx.2.2
      refine ⟨n, ?_⟩
      have hn' : (⟨x, hx.1⟩ : ↥(cSpC_G K m)) ^ S.p ^ n = 1 := by
        apply Subtype.ext
        simpa using hn
      rw [← map_pow, hn', map_one]
  refine ⟨s, hs2, 1 + (S.p : ℤ) ^ (s - 1) * k, k, hk, Int.ModEq.refl _, ?_, ?_, ?_,
    κ ⟨a₁, ha₁.1⟩, κ ⟨a₂, ha₂.1⟩, toP a₁ ha₁, toP a₂ ha₂, ?_⟩
  · intro u v hu hv
    obtain ⟨x, hxP, hxu⟩ := ofP u hu
    obtain ⟨y, hyP, hyv⟩ := ofP v hv
    calc u * v = κ x * κ y := by rw [hxu, hyv]
      _ = κ (x * y) := (map_mul κ x y).symm
      _ = κ (y * x) := by
            have hxy : x * y = y * x :=
              Subtype.ext (H1 (x : GL _ K) (y : GL _ K) hxP hyP)
            rw [hxy]
      _ = κ y * κ x := map_mul κ y x
      _ = v * u := by rw [hyv, hxu]
  · intro u hu
    obtain ⟨x, hxP, hxu⟩ := ofP u hu
    obtain ⟨hxs, hxσ⟩ := H2 (x : GL _ K) hxP
    constructor
    · calc u ^ S.p ^ s = (κ x) ^ S.p ^ s := by rw [hxu]
        _ = κ (x ^ S.p ^ s) := (map_pow κ x (S.p ^ s)).symm
        _ = 1 := by
            have hxs' : (x : ↥(cSpC_G K m)) ^ S.p ^ s = 1 := by
              apply Subtype.ext
              simpa using hxs
            rw [hxs', map_one]
    · have hfield : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K S.σ₀) x =
          x ^ (1 + (S.p : ℤ) ^ (s - 1) * k) := by
        have hgl : (((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K S.σ₀) x :
            ↥(cSpC_G K m)) : GL (Fin m ⊕ Fin m) K) =
            ((x : ↥(cSpC_G K m)) : GL (Fin m ⊕ Fin m) K) ^ (1 + (S.p : ℤ) ^ (s - 1) * k) := by
          have h1 : (((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K S.σ₀) x :
              ↥(cSpC_G K m)) : GL (Fin m ⊕ Fin m) K) =
              S.σGL ((x : ↥(cSpC_G K m)) : GL (Fin m ⊕ Fin m) K) := by
            apply Units.ext
            rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp,
              cSpC_sigmaGL_coe S ((x : ↥(cSpC_G K m)) : GL (Fin m ⊕ Fin m) K)]
          rw [h1]
          exact hxσ
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hgl
      calc f * u * f⁻¹ = f * κ x * f⁻¹ := by rw [hxu]
        _ = κ ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K S.σ₀) x) :=
            hκfield x
        _ = κ (x ^ (1 + (S.p : ℤ) ^ (s - 1) * k)) := by rw [hfield]
        _ = (κ x) ^ (1 + (S.p : ℤ) ^ (s - 1) * k) := map_zpow κ x _
        _ = u ^ (1 + (S.p : ℤ) ^ (s - 1) * k) := by rw [hxu]
  · intro u hu w hw hwE
    obtain ⟨x, hxP, hxu⟩ := ofP u hu
    obtain ⟨h, hhκ⟩ := hI_mem w hw
    have hhCent : S.Cent (h : GL (Fin m ⊕ Fin m) K) := by
      refine ⟨by rw [hSadj]; exact (sp_mem_iff_adj (h : GL (Fin m ⊕ Fin m) K)).1 h.2, ?_⟩
      intro e he
      have heΓ : e ∈ (cSpC_G K m) := hE0le he
      have hmemK : (⟨e, heΓ⟩ : ↥(cSpC_G K m)) ∈ Ebar.comap κ := by
        change e ∈ S.E₀ at he
        rw [hE₀, Subgroup.mem_map] at he
        obtain ⟨x', hx'K, hx'e⟩ := he
        have hxe' : (⟨e, heΓ⟩ : ↥(cSpC_G K m)) = x' := Subtype.ext hx'e.symm
        rwa [hxe']
      have hmem : κ (⟨e, heΓ⟩ : ↥(cSpC_G K m)) ∈ Ebar := hmemK
      have hc := hwE (κ (⟨e, heΓ⟩ : ↥(cSpC_G K m))) hmem
      have hhe : h * (⟨e, heΓ⟩ : ↥(cSpC_G K m)) = (⟨e, heΓ⟩ : ↥(cSpC_G K m)) * h := by
        apply hinjκ
        rw [map_mul, map_mul, hhκ]
        exact hc
      exact congrArg Subtype.val hhe
    calc w * u = κ h * κ x := by rw [hhκ, hxu]
      _ = κ (h * x) := (map_mul κ h x).symm
      _ = κ (x * h) := by
            have h3 : h.1 * x.1 = x.1 * h.1 :=
              H3 x.1 hxP h.1 h.2
                (by rw [hSadj]; exact (sp_mem_iff_adj h.1).1 h.2)
                hhCent.2
            have hxh : h * x = x * h := Subtype.ext h3
            rw [hxh]
      _ = κ x * κ h := map_mul κ x h
      _ = u * w := by rw [hxu, hhκ]
  · intro i j hij
    have h1 : κ (((⟨a₁, ha₁.1⟩ : ↥(cSpC_G K m)) ^ S.p ^ (s - 1)) ^ i *
        ((⟨a₂, ha₂.1⟩ : ↥(cSpC_G K m)) ^ S.p ^ (s - 1)) ^ j) = 1 := by
      simp only [map_mul, map_pow, map_one]
      exact hij
    have h2 : ((⟨a₁, ha₁.1⟩ : ↥(cSpC_G K m)) ^ S.p ^ (s - 1)) ^ i *
        ((⟨a₂, ha₂.1⟩ : ↥(cSpC_G K m)) ^ S.p ^ (s - 1)) ^ j = 1 :=
      hinjκ (by rw [h1, map_one])
    apply hind i j
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val h2

private theorem cSpC_field_case {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ}
    (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hsimp : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)))
    (hnab : ∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a)
    (Ebar : Subgroup (MulAut (LargeEvenProj (LargeEvenSpGroup K m))))
    (f : MulAut (LargeEvenProj (LargeEvenSpGroup K m)))
    (hEab : IsElemAbelian p Ebar) (hcard : p ^ 2 ≤ Nat.card Ebar)
    (hEI : ∀ e ∈ Ebar, e ∈ cSpC_I K m)
    (hfF : f ∈ cSpC_F K m) (hfo : orderOf f = p)
    (hcomm : ∀ e ∈ Ebar, e * f = f * e)
    (hSat : ∀ r : LargeEvenProj (LargeEvenSpGroup K m), r ^ p = 1 →
      (∀ e ∈ Ebar, e r = r) → f r = r → MulAut.conj r ∈ Ebar) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ (c : ℤ) (k : ℕ), ¬ p ∣ k ∧
      c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
      (∀ u v : MulAut _, GGL45NtCIp p (cSpC_I K m) Ebar u →
        GGL45NtCIp p (cSpC_I K m) Ebar v → u * v = v * u) ∧
      (∀ u : MulAut _, GGL45NtCIp p (cSpC_I K m) Ebar u → u ^ p ^ s = 1 ∧ f * u * f⁻¹ = u ^ c) ∧
      (∀ u : MulAut _, GGL45NtCIp p (cSpC_I K m) Ebar u → ∀ w ∈ cSpC_I K m,
        (∀ e ∈ Ebar, w * e = e * w) → w * u = u * w) ∧
      ∃ a₁ a₂ : MulAut _, GGL45NtCIp p (cSpC_I K m) Ebar a₁ ∧
        GGL45NtCIp p (cSpC_I K m) Ebar a₂ ∧
        ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j := by
  let Γ : Subgroup (GL (Fin m ⊕ Fin m) K) := LargeEvenSpGroup K m
  let R := LargeEvenProj Γ
  let π : ↥Γ →* R := LargeEvenProjMk Γ
  let I : Set (MulAut R) := cSpC_I K m
  let κ : ↥Γ →* MulAut R := MulAut.conj.comp π
  have hinjπ : Function.Injective π := (sp_proj_bijective (K := K) m).1
  have hinjconj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    cSpC_conj_injective hsimp hnab
  have hinjκ : Function.Injective κ := hinjconj.comp hinjπ
  obtain ⟨σ₀, hσ₀, hfact⟩ := sp_fieldAut_orderOf (K := K) (m := m) (p := p) hm hfF hfo
  have hrange : κ.range = (MulAut.conj : R →* MulAut R).range := by
    ext φ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨π g, rfl⟩
    · rintro ⟨r, rfl⟩
      obtain ⟨g, hg⟩ := (sp_proj_bijective (K := K) m).2 r
      exact ⟨g, by change MulAut.conj (π g) = MulAut.conj r; rw [hg]⟩
  have hEbar_le : Ebar ≤ κ.range := fun e he => by
    rw [hrange]
    exact RecipeFieldSp.mem_conjImage_iff_inn.mp (hEI e he)
  let Kbar : Subgroup ↥Γ := Ebar.comap κ
  let E₀ : Subgroup (GL (Fin m ⊕ Fin m) K) := Kbar.map Γ.subtype
  have hE0le : E₀ ≤ Γ := Subgroup.map_subtype_le Kbar
  let κK : Kbar →* Ebar :=
    { toFun := fun g => ⟨κ g.1, show κ g.1 ∈ Ebar from g.2⟩
      map_one' := Subtype.ext (map_one κ)
      map_mul' := fun a b => Subtype.ext (map_mul κ a.1 b.1) }
  have hκKbij : Function.Bijective κK := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply Subtype.ext
      apply hinjκ
      exact congrArg Subtype.val hab
    · intro e
      obtain ⟨g, hg⟩ := hEbar_le e.2
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      rw [Subgroup.mem_comap, hg]
      exact e.2
  let κKe : Kbar ≃* Ebar := MulEquiv.ofBijective κK hκKbij
  let E0eq : E₀ ≃* Ebar :=
    (Subgroup.equivMapOfInjective Kbar Γ.subtype (Subgroup.subtype_injective Γ)).symm.trans κKe
  have hE0 : IsElemAbelian p E₀ := by
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply E0eq.injective
      rw [map_mul, map_mul]
      exact hEab.1.is_comm.comm (E0eq a) (E0eq b)
    · intro x hx
      have h1 : (⟨x, hx⟩ : E₀) ^ p = 1 := by
        apply E0eq.injective
        rw [map_pow, map_one]
        exact Subtype.ext (hEab.2 (E0eq ⟨x, hx⟩) (E0eq ⟨x, hx⟩).2)
      exact congrArg Subtype.val h1
  have hE0card : Nat.card E₀ = Nat.card Ebar := Nat.card_congr E0eq.toEquiv
  have hconjform : ∀ r : R, f * MulAut.conj r * f⁻¹ = MulAut.conj (f r) := by
    intro r
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have hκfield : ∀ g : ↥Γ, f * κ g * f⁻¹ =
      κ ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀) g) := by
    intro g
    calc f * κ g * f⁻¹ = MulAut.conj (f (π g)) := hconjform (π g)
      _ = MulAut.conj (π ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀) g)) := by
          rw [hfact g]
      _ = κ ((CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀) g) := rfl
  have hEfix : ∀ e ∈ E₀, (e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ₀ = e := by
    intro e he
    obtain ⟨g, hgK, hge⟩ := (Subgroup.mem_map.mp he : ∃ x ∈ Kbar, Γ.subtype x = e)
    have hkg : κ g ∈ Ebar := hgK
    have h2 : f * κ g * f⁻¹ = κ g := by
      calc f * κ g * f⁻¹ = (κ g * f) * f⁻¹ := by rw [hcomm (κ g) hkg]
        _ = κ g := by group
    have hconj : MulAut.conj (f (π g)) = MulAut.conj (π g) := by
      rw [← hconjform (π g)]
      exact h2
    have hfπ : f (π g) = π g := hinjconj hconj
    have hπeq : π (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀ g) = π g := by
      rw [← hfact g]
      exact hfπ
    have hSp : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀ g = g :=
      hinjπ hπeq
    have hmat : ((g : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K).map σ₀ =
        ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      have hh := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp (r := m) (K := K) σ₀ g
      rw [hSp] at hh
      exact hh.symm
    subst hge
    exact hmat
  have hEU : ∀ e ∈ E₀,
      formAdj (RingEquiv.refl K) (LargeEvenSpForm K m) (e : Matrix _ _ K) * e = 1 := by
    intro e he
    exact (sp_mem_iff_adj (K := K) e).1 (hE0le he)
  have hJJ : LargeEvenSpForm K m * (-(LargeEvenSpForm K m)) = 1 := by
    rw [largeEvenSpForm_def, Matrix.mul_neg, Matrix.fromBlocks_multiply]
    simp [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  have hG : IsUnit (LargeEvenSpForm K m).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hdet := congrArg Matrix.det hJJ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hdet
    exact one_ne_zero hdet.symm
  have hmaprefl : (LargeEvenSpForm K m).map (RingEquiv.refl K) = LargeEvenSpForm K m := by
    ext i j; rfl
  have hJt : (LargeEvenSpForm K m)ᵀ = -(LargeEvenSpForm K m) := by
    rw [largeEvenSpForm_def, fromBlocks_transpose]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.neg_apply]
  have hJneg : -(LargeEvenSpForm K m) = LargeEvenSpForm K m := by
    ext i j
    rw [Matrix.neg_apply]
    exact CharTwo.neg_eq _
  have hGs : ((LargeEvenSpForm K m).map (RingEquiv.refl K))ᵀ = LargeEvenSpForm K m := by
    rw [hmaprefl, hJt, hJneg]
  have hGσ : (LargeEvenSpForm K m).map σ₀ = LargeEvenSpForm K m := by
    rw [largeEvenSpForm_def]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [Matrix.map_apply, Matrix.fromBlocks, Matrix.neg_apply, Matrix.one_apply,
        Matrix.zero_apply]
    all_goals (by_cases hij : i = j <;> simp [hij, map_zero, map_one, map_neg])
  let S : ClSetting K (Fin m ⊕ Fin m) :=
    { p := p
      hp := hp
      hp2 := hp2
      τ := RingEquiv.refl K
      hτ := fun c => rfl
      G := LargeEvenSpForm K m
      hG := hG
      hGs := hGs
      σ₀ := σ₀
      hσ₀ := hσ₀
      hGσ := hGσ
      E₀ := E₀
      hE := hE0
      hEU := hEU
      hEfix := hEfix }
  have hH : S.GoodGroup Γ := ClSetting.goodGroup_U S Γ (fun g => sp_mem_iff_adj g)
  have hSatS : S.Sat Γ := by
    intro y hyΓ hyCent hyp hyσ
    let yΓ : ↥Γ := ⟨y, hyΓ⟩
    have hyΓp : yΓ ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hyp, Subgroup.coe_one]
    let r : R := π yΓ
    have hrp : r ^ p = 1 := by
      change (π yΓ) ^ p = 1
      rw [← map_pow, hyΓp, map_one]
    have hEr : ∀ e ∈ Ebar, e r = r := by
      intro e he
      obtain ⟨g, hg⟩ := hEbar_le he
      have hgE0 : (g : GL (Fin m ⊕ Fin m) K) ∈ E₀ := by
        rw [show E₀ = Kbar.map Γ.subtype from rfl, Subgroup.mem_map]
        exact ⟨g, by rwa [Subgroup.mem_comap, hg], rfl⟩
      have hgy : y * (g : GL (Fin m ⊕ Fin m) K) = (g : GL (Fin m ⊕ Fin m) K) * y :=
        hyCent.2 _ hgE0
      have hgy' : g * yΓ = yΓ * g := Subtype.ext hgy.symm
      rw [← hg]
      change MulAut.conj (π g) (π yΓ) = π yΓ
      calc MulAut.conj (π g) (π yΓ) = π (g * yΓ * g⁻¹) := by
            rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
        _ = π yΓ := by rw [hgy', mul_assoc, mul_inv_cancel, mul_one]
    have hfr : f r = r := by
      change f (π yΓ) = π yΓ
      rw [hfact yΓ]
      have hσy : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp m K σ₀) yΓ = yΓ := by
        apply Subtype.ext
        apply Units.ext
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.coe_fieldSp]
        have hmat : (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ₀ =
            (y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
          have h1 : ((S.σGL y : GL (Fin m ⊕ Fin m) K) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
              ((y : GL (Fin m ⊕ Fin m) K) :
                Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ₀ := by
            simpa using cSpC_sigmaGL_coe S y
          have h2 := congrArg (fun z : GL (Fin m ⊕ Fin m) K =>
            (z : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hyσ
          rw [h1] at h2
          exact h2
        exact hmat
      rw [hσy]
    have hconjr : MulAut.conj r ∈ Ebar := hSat r hrp hEr hfr
    have hyK : yΓ ∈ Kbar := by
      rw [Subgroup.mem_comap]
      exact hconjr
    have hyE0 : y ∈ E₀ := by
      rw [show E₀ = Kbar.map Γ.subtype from rfl, Subgroup.mem_map]
      exact ⟨yΓ, hyK, rfl⟩
    exact S.mem_A_of_mem hyE0
  have hcardS : S.p ^ 2 ≤ Nat.card S.E₀ := by
    show p ^ 2 ≤ Nat.card E₀
    rw [hE0card]
    exact hcard
  obtain ⟨s, hs2, k, hk, H1, H2, H3, a₁, a₂, ha₁, ha₂, hind⟩ :=
    S.matrix_core (H := Γ) hH hSatS hE0le hcardS
  have hI_mem : ∀ w ∈ I, ∃ h : ↥Γ, κ h = w := fun w hw => by
    have h1 : w ∈ κ.range := by
      rw [hrange]
      exact RecipeFieldSp.mem_conjImage_iff_inn.mp hw
    exact h1
  have hE₀ : S.E₀ = (Ebar.comap κ).map Γ.subtype := rfl
  have hSadj : ∀ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K,
      S.adj M = formAdj (RingEquiv.refl K) (LargeEvenSpForm K m) M := fun M => rfl
  have hκ : ∀ g : ↥Γ, κ g = MulAut.conj (LargeEvenProjMk Γ g) := fun g => rfl
  have H3' : ∀ x : GL (Fin m ⊕ Fin m) K, S.CentP Γ x → ∀ w ∈ Γ,
      S.adj (w : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * w = 1 →
        (∀ e ∈ S.E₀, w * e = e * w) → w * x = x * w :=
    fun x hx w hw ha hb => H3 x hx w hw ⟨ha, hb⟩
  exact cSpC_transfer (p := p) S κ Ebar f hinjκ hEbar_le hI_mem hE₀ hSadj hκ hκfield s hs2 k hk
    H1 H2 H3' a₁ a₂ ha₁ ha₂ hind.2.2

theorem ntCore_sp {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ} (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) :
    GGL45NtCore p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  apply ntCore_of_conj p
    (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
    (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) ?_ ?_ ?_
  · intro x hx y hy
    rw [RecipeFieldSp.mem_conjImage_iff_inn] at hx hy ⊢
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
  · rw [RecipeFieldSp.mem_conjImage_iff_inn]
    exact Subgroup.one_mem _
  · intro hsimp hnab Ebar f hEab hcard hEI hfF hfo hcomm hSat
    exact cSpC_field_case (m := m) (p := p) (by omega) hp hp2 hsimp hnab Ebar f hEab hcard
      hEI hfF hfo hcomm hSat

theorem partialNorm_succ {L : Type} [Field L] (σ₀ : L ≃+* L) (lam : L) (i : ℕ) :
    σ₀ (∏ j ∈ Finset.range i, (σ₀ ^ j) lam) * lam = ∏ j ∈ Finset.range (i + 1), (σ₀ ^ j) lam := by
  rw [map_prod, Finset.prod_range_succ', pow_zero]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pow_succ']; rfl

theorem hilbert90 {L : Type} [Field L] [Finite L] (σ₀ : L ≃+* L) (lam : L)
    (hN : ∏ j ∈ Finset.range (orderOf σ₀), (σ₀ ^ j) lam = 1) :
    ∃ b : L, b ≠ 0 ∧ σ₀ b * lam = b := by
  classical
  haveI : Finite (L ≃+* L) := Finite.of_injective (fun e : L ≃+* L => (e : L → L))
    (fun a b h => RingEquiv.ext (congrFun h))
  set n := orderOf σ₀ with hn
  have hn0 : 0 < n := orderOf_pos σ₀
  let lamI : ℕ → L := fun i => ∏ j ∈ Finset.range i, (σ₀ ^ j) lam
  let φ : Fin n → (L →* L) := fun i => ((σ₀ ^ (i : ℕ) : L ≃+* L) : L →+* L).toMonoidHom
  have hφ : Function.Injective φ := by
    intro i j h
    have h' : σ₀ ^ (i : ℕ) = σ₀ ^ (j : ℕ) := RingEquiv.ext fun c => DFunLike.congr_fun h c
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 h')
  have hli := (linearIndependent_monoidHom L L).comp φ hφ
  obtain ⟨θ, hθ⟩ : ∃ θ : L, ∑ i : Fin n, lamI i * (σ₀ ^ (i : ℕ)) θ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Fintype.linearIndependent_iff.1 hli (fun i => lamI i) (funext fun θ => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply]
      exact hcon θ)
    have h0 := this ⟨0, hn0⟩
    simp [lamI] at h0
  let F : ℕ → L := fun i => lamI i * (σ₀ ^ i) θ
  refine ⟨∑ i ∈ Finset.range n, F i, ?_, ?_⟩
  · rwa [← Fin.sum_univ_eq_sum_range F]
  · have hstep : ∀ i, σ₀ (F i) * lam = F (i + 1) := fun i => by
      simp only [F, map_mul]
      rw [mul_right_comm, partialNorm_succ, pow_succ']; rfl
    have hF : F n = F 0 := by
      simp only [F, lamI]
      rw [hN, hn, pow_orderOf_eq_one]; simp
    rw [map_sum, Finset.sum_mul]
    simp_rw [hstep]
    have e1 := Finset.sum_range_succ' F n
    have e2 := Finset.sum_range_succ F n
    rw [hF] at e2
    exact add_right_cancel (e1.symm.trans e2)

theorem lin_descent {K : Type} [Field K] [Fintype K] [CharP K 2] {d : ℕ} (σ₀ : K ≃+* K) (x : GL (Fin d) K) (lam : Kˣ)
    (hx : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (lam : K) • (x : Matrix (Fin d) (Fin d) K)) :
    ∃ μ : Kˣ, ((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map σ₀ = (μ : K) • (x : Matrix (Fin d) (Fin d) K) := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨1, Subsingleton.elim _ _⟩
  have hsm : ∀ (c : K) (M : Matrix (Fin d) (Fin d) K), (c • M).map σ₀ = σ₀ c • M.map σ₀ :=
    fun c M => by ext i j; simp [Matrix.map_apply]
  have hiter : ∀ i : ℕ, (x : Matrix (Fin d) (Fin d) K).map ⇑(σ₀ ^ i) =
      (∏ j ∈ Finset.range i, (σ₀ ^ j) (lam : K)) • (x : Matrix (Fin d) (Fin d) K) := by
    intro i
    induction i with
    | zero => ext a b; simp
    | succ i ih =>
      have : (x : Matrix (Fin d) (Fin d) K).map ⇑(σ₀ ^ (i + 1)) =
          ((x : Matrix (Fin d) (Fin d) K).map ⇑(σ₀ ^ i)).map σ₀ := by
        ext a b; simp only [Matrix.map_apply]; rw [pow_succ']; rfl
      rw [this, ih, hsm, hx, smul_smul, partialNorm_succ]
  have hx0 : ∃ a b, (x : Matrix (Fin d) (Fin d) K) a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : (x : Matrix (Fin d) (Fin d) K) = 0 := by ext a b; exact hcon a b
    have h1 := congrArg (· ⟨0, hd⟩ ⟨0, hd⟩)
      (show (x : Matrix (Fin d) (Fin d) K) * ((x⁻¹ : GL _ K) : Matrix _ _ K) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simp [h0] at h1
  obtain ⟨a, b, hab⟩ := hx0
  have hN : ∏ j ∈ Finset.range (orderOf σ₀), (σ₀ ^ j) (lam : K) = 1 := by
    haveI : Finite (K ≃+* K) := Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun a b h => RingEquiv.ext (congrFun h))
    have h := congrFun (congrFun (hiter (orderOf σ₀)) a) b
    rw [pow_orderOf_eq_one] at h
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h
    exact (mul_eq_right₀ hab).1 h.symm
  obtain ⟨c, hc0, hc⟩ := hilbert90 σ₀ (lam : K) hN
  refine ⟨Units.mk0 c hc0, ?_⟩
  rw [Units.val_mk0, hsm, hx, smul_smul, hc]

private theorem lin_order_p_of_not_dvd {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (σ₀ : K ≃+* K) (x : GL (Fin d) K)
    (hfix : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (x : Matrix (Fin d) (Fin d) K)) (ν : Kˣ) (hxp : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1) :
    ∃ μ : Kˣ, σ₀ μ = μ ∧ ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) ^ p = 1 := by
  have hd : d ≠ 0 := by rintro rfl; exact hpd (dvd_zero p)
  have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
  set δ := (x : Matrix (Fin d) (Fin d) K).det with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by
    have h1 : δ * ((x⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K).det = 1 := by
      rw [hδ, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [h0, zero_mul] at h1; exact zero_ne_one h1
  have hσδ : σ₀ δ = δ := by
    have := RingHom.map_det (σ₀ : K →+* K) (x : Matrix (Fin d) (Fin d) K)
    rw [hδ]; exact this.trans (congrArg Matrix.det hfix)
  have hxp' : (x : Matrix (Fin d) (Fin d) K) ^ p = (ν : K) • 1 := by
    rw [← hxp, Units.val_pow_eq_pow_val]
  have hνd : (ν : K) ^ d = δ ^ p := by
    have := congrArg Matrix.det hxp'
    rw [Matrix.det_pow, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at this
    exact this.symm
  have hσν : σ₀ (ν : K) = ν := by
    have h1 : ((x : Matrix (Fin d) (Fin d) K) ^ p).map σ₀ = (x : Matrix (Fin d) (Fin d) K) ^ p := by
      rw [show ((x : Matrix (Fin d) (Fin d) K) ^ p).map σ₀ =
        ((x : Matrix (Fin d) (Fin d) K).map σ₀) ^ p from
        (map_pow (σ₀.mapMatrix : Matrix (Fin d) (Fin d) K ≃+* _) _ p), hfix]
    rw [hxp'] at h1
    have h2 := congrFun (congrFun h1 i0) i0
    simpa [Matrix.map_apply] using h2
  have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have h := Nat.div_add_mod (d * m) p
  rw [hm] at h
  set t := d * m / p
  have hν0 : (ν : K) ≠ 0 := ν.ne_zero
  set μK : K := (δ⁻¹) ^ m * (ν : K) ^ t
  have hμ0 : μK ≠ 0 := mul_ne_zero (pow_ne_zero _ (inv_ne_zero hδ0)) (pow_ne_zero _ hν0)
  refine ⟨Units.mk0 μK hμ0, ?_, ?_⟩
  · simp only [Units.val_mk0, μK, map_mul, map_pow, map_inv₀, hσδ, hσν]
  · rw [Units.val_mk0, smul_pow, hxp', smul_smul, mul_comm (μK ^ p)]
    have : (ν : K) * μK ^ p = 1 := by
      simp only [μK, mul_pow, ← pow_mul, inv_pow]
      calc (ν : K) * ((δ ^ (m * p))⁻¹ * (ν : K) ^ (t * p))
          = (δ ^ (m * p))⁻¹ * (ν : K) ^ (p * t + 1) := by ring
        _ = (δ ^ (m * p))⁻¹ * ((ν : K) ^ d) ^ m := by rw [h, pow_mul (ν : K) d m]
        _ = 1 := by rw [hνd, ← pow_mul, mul_comm p m, inv_mul_cancel₀ (pow_ne_zero _ hδ0)]
    rw [this, one_smul]

private theorem cW1_pow_eq_one {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Fintype.card K - 1) {z : Kˣ} (hz : z ^ p = 1) : z = 1 := by
  classical
  have hcard : Fintype.card Kˣ = Fintype.card K - 1 := Fintype.card_units K
  have hcop' : Nat.Coprime p (Fintype.card K - 1) := (hp.coprime_iff_not_dvd).mpr h
  have hcop : Nat.Coprime (Fintype.card Kˣ) p := by
    rw [hcard]
    exact Nat.coprime_comm.mp hcop'
  have h1 : orderOf z ∣ Fintype.card Kˣ := orderOf_dvd_card (x := z)
  have h2 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hz
  have h3 : orderOf z ∣ 1 := by
    have h4 : orderOf z ∣ Nat.gcd (Fintype.card Kˣ) p := Nat.dvd_gcd h1 h2
    rwa [hcop] at h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem cW1_pow_injective {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Fintype.card K - 1) : Function.Injective (fun z : Kˣ => z ^ p) := by
  intro a b hab
  change a ^ p = b ^ p at hab
  have hz : (a * b⁻¹) ^ p = 1 := by
    rw [mul_pow, inv_pow, hab, mul_inv_cancel]
  have h1 : a * b⁻¹ = 1 := cW1_pow_eq_one hp h hz
  calc a = a * b⁻¹ * b := by group
    _ = 1 * b := by rw [h1]
    _ = b := by simp

private theorem cW1_pow_surjective {K : Type} [Field K] [Fintype K] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Fintype.card K - 1) : Function.Surjective (fun z : Kˣ => z ^ p) :=
  (Finite.injective_iff_surjective).mp (cW1_pow_injective hp h)

theorem lin_order_p {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (σ₀ : K ≃+* K) (x : GL (Fin d) K)
    (hfix : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (x : Matrix (Fin d) (Fin d) K)) (ν : Kˣ) (hxp : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1) :
    ∃ μ : Kˣ, σ₀ μ = μ ∧ ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) ^ p = 1 := by
  rcases hpd with h | h
  · exact lin_order_p_of_not_dvd hp h σ₀ x hfix ν hxp
  · have hxp' : (x : Matrix (Fin d) (Fin d) K) ^ p = (ν : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact hxp
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      exact ⟨1, by simp, Subsingleton.elim _ _⟩
    have i0 : Fin d := ⟨0, hdpos⟩
    have hσν : σ₀ (ν : K) = (ν : K) := by
      have h1 : ((x : Matrix (Fin d) (Fin d) K) ^ p).map σ₀ =
          (x : Matrix (Fin d) (Fin d) K) ^ p := by
        rw [show ((x : Matrix (Fin d) (Fin d) K) ^ p).map σ₀ =
          ((x : Matrix (Fin d) (Fin d) K).map σ₀) ^ p from
          (map_pow (σ₀.mapMatrix : Matrix (Fin d) (Fin d) K ≃+* _) _ p), hfix]
      rw [hxp'] at h1
      have h2 := congrFun (congrFun h1 i0) i0
      simpa [Matrix.map_apply] using h2
    obtain ⟨μ₀, hμ₀p⟩ := cW1_pow_surjective hp h ν
    change μ₀ ^ p = ν at hμ₀p
    have hσμ₀u : Units.map σ₀.toMonoidHom μ₀ = μ₀ := by
      apply cW1_pow_injective hp h
      apply Units.ext
      rw [Units.val_pow_eq_pow_val (Units.map σ₀.toMonoidHom μ₀) p,
        Units.val_pow_eq_pow_val μ₀ p, Units.coe_map, ← map_pow]
      rw [show (μ₀ : K) ^ p = (ν : K) from by rw [← Units.val_pow_eq_pow_val, hμ₀p]]
      simpa using hσν
    have hσμ₀ : σ₀ (μ₀ : K) = (μ₀ : K) := by
      have hh := congrArg (fun u : Kˣ => (u : K)) hσμ₀u
      simpa [Units.coe_map] using hh
    refine ⟨μ₀⁻¹, ?_, ?_⟩
    · show σ₀ ((μ₀⁻¹ : Kˣ) : K) = ((μ₀⁻¹ : Kˣ) : K)
      rw [Units.val_inv_eq_inv_val, map_inv₀, hσμ₀]
    · rw [smul_pow, hxp', smul_smul]
      have hc : ((μ₀⁻¹ : Kˣ) : K) ^ p * (ν : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, inv_pow,
          show (μ₀ : K) ^ p = (ν : K) from by rw [← Units.val_pow_eq_pow_val, hμ₀p],
          inv_mul_cancel₀ ν.ne_zero]
      rw [hc, one_smul]

private theorem lin_kappa_of_not_dvd {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (g x : GL (Fin d) K) (κ : Kˣ)
    (h : ((g * x * g⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K) = (κ : K) • (x : Matrix (Fin d) (Fin d) K)) (hx : x ^ p = 1) :
    κ = 1 := by
  have hd : d ≠ 0 := by rintro rfl; exact hpd (dvd_zero p)
  have hdetu : ∀ y : GL (Fin d) K, (y : Matrix (Fin d) (Fin d) K).det *
      ((y⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K).det = 1 := fun y => by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hx0 : (x : Matrix (Fin d) (Fin d) K).det ≠ 0 := fun h0 => by
    have := hdetu x; rw [h0, zero_mul] at this; exact zero_ne_one this
  have hκd : (κ : K) ^ d = 1 := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_smul, Fintype.card_fin, Units.val_mul, Units.val_mul, Matrix.det_mul,
      Matrix.det_mul, mul_right_comm, hdetu, one_mul] at h1
    exact (mul_eq_right₀ hx0).1 h1.symm
  have hκp : (κ : K) ^ p = 1 := by
    have h1 : ((g * x * g⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, conj_pow, hx, mul_one, mul_inv_cancel, Units.val_one]
    rw [h, smul_pow, ← Units.val_pow_eq_pow_val x, hx, Units.val_one] at h1
    have h2 := congrFun (congrFun h1 ⟨0, Nat.pos_of_ne_zero hd⟩) ⟨0, Nat.pos_of_ne_zero hd⟩
    simpa using h2
  have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
  have hu1 : κ ^ d = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκd, Units.val_one])
  have hu2 : κ ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
  have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

theorem lin_kappa {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime)
    (hd : 0 < d) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (g x : GL (Fin d) K) (κ : Kˣ)
    (h : ((g * x * g⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K) = (κ : K) • (x : Matrix (Fin d) (Fin d) K)) (hx : x ^ p = 1) :
    κ = 1 := by
  rcases hpd with h' | h'
  · exact lin_kappa_of_not_dvd hp h' g x κ h hx
  · have hκp : (κ : K) ^ p = 1 := by
      have h1 : ((g * x * g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, conj_pow, hx, mul_one, mul_inv_cancel, Units.val_one]
      rw [h, smul_pow, ← Units.val_pow_eq_pow_val x, hx, Units.val_one] at h1
      have h2 := congrFun (congrFun h1 ⟨0, hd⟩) ⟨0, hd⟩
      simpa using h2
    have hu : κ ^ p = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hκp, Units.val_one])
    exact cW1_pow_eq_one hp h' hu

private theorem lin_sl_adjust_of_not_dvd {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (σ₀ : K ≃+* K) (y : GL (Fin d) K)
    (hfix : (y : Matrix (Fin d) (Fin d) K).map σ₀ = (y : Matrix (Fin d) (Fin d) K)) (hy : y ^ p = 1) :
    ∃ μ : Kˣ, σ₀ μ = μ ∧ μ ^ p = 1 ∧ ((μ : K) • (y : Matrix (Fin d) (Fin d) K)).det = 1 := by
  have hd : d ≠ 0 := by rintro rfl; exact hpd (dvd_zero p)
  set δ := (y : Matrix (Fin d) (Fin d) K).det with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by
    have h1 : δ * ((y⁻¹ : GL _ K) : Matrix (Fin d) (Fin d) K).det = 1 := by
      rw [hδ, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [h0, zero_mul] at h1; exact zero_ne_one h1
  have hδp : δ ^ p = 1 := by
    rw [hδ, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hy, Units.val_one, Matrix.det_one]
  have hσδ : σ₀ δ = δ := by
    have := RingHom.map_det (σ₀ : K →+* K) (y : Matrix (Fin d) (Fin d) K)
    rw [hδ]; exact this.trans (congrArg Matrix.det hfix)
  have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set c := m * (p - 1)
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcd : c * d + 1 = p * (d * m / p * (p - 1) + 1) := by
    have h := Nat.div_add_mod (d * m) p
    rw [hm] at h
    set t := d * m / p
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    have e1 : c * d = (d * m) * p' := by simp only [c, hp', Nat.add_sub_cancel]; ring
    rw [e1, ← h, hp', Nat.add_sub_cancel]; ring
  refine ⟨Units.mk0 δ hδ0 ^ c, ?_, ?_, ?_⟩
  · simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hσδ]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul,
      mul_comm, pow_mul, hδp, one_pow, Units.val_one]
  · rw [Matrix.det_smul, Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul,
      ← hδ, ← pow_succ, hcd, pow_mul, hδp, one_pow]

theorem lin_sl_adjust {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) (σ₀ : K ≃+* K) (y : GL (Fin d) K)
    (hfix : (y : Matrix (Fin d) (Fin d) K).map σ₀ = (y : Matrix (Fin d) (Fin d) K)) (hy : y ^ p = 1) :
    ∃ μ : Kˣ, σ₀ μ = μ ∧ μ ^ p = 1 ∧ ((μ : K) • (y : Matrix (Fin d) (Fin d) K)).det = 1 := by
  rcases hpd with h | h
  · exact lin_sl_adjust_of_not_dvd hp h σ₀ y hfix hy
  · have hδp : (y : Matrix (Fin d) (Fin d) K).det ^ p = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hy, Units.val_one, Matrix.det_one]
    have hδ0 : (y : Matrix (Fin d) (Fin d) K).det ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hδp
      exact zero_ne_one hδp
    have hu : Units.mk0 (y : Matrix (Fin d) (Fin d) K).det hδ0 ^ p = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hδp, Units.val_one])
    have hδ1 : (y : Matrix (Fin d) (Fin d) K).det = 1 := by
      have hh := congrArg (fun u : Kˣ => (u : K)) (cW1_pow_eq_one hp h hu)
      simpa [Units.val_mk0] using hh
    refine ⟨1, by simp, by simp, ?_⟩
    rw [Matrix.det_smul, Fintype.card_fin]
    simpa using hδ1

private theorem cUni_exists_eta {K : Type} [Field K]
    (p q : ℕ) (hp : p.Prime) (h2q : 2 ∣ q) (σ₀ : K ≃+* K)
    {θ : K} (hσθ : σ₀ θ = θ) (hθp : θ ^ p = 1) (hθq : θ ^ q = θ) :
    ∃ η : K, σ₀ η = η ∧ η ^ p = 1 ∧ η ^ (q + 1) = θ⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hθp
    exact zero_ne_one hθp
  by_cases hpq : p ∣ q + 1
  · refine ⟨1, by simp, by simp, ?_⟩
    have hθ1 : θ = 1 := by
      rcases Nat.eq_zero_or_pos q with hq0 | hqpos
      · rw [hq0, pow_zero] at hθq
        exact hθq.symm
      · have hθqm1 : θ ^ (q - 1) = 1 := by
          have h1 : θ ^ (q - 1) * θ = 1 * θ := by
            rw [← pow_succ, Nat.sub_add_cancel hqpos, hθq, one_mul]
          exact mul_right_cancel₀ hθ0 h1
        have hordp : orderOf θ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hθp
        have hordqm : orderOf θ ∣ q - 1 := orderOf_dvd_iff_pow_eq_one.mpr hθqm1
        have hord2 : orderOf θ ∣ 2 := by
          have hg : Nat.gcd p (q - 1) ∣ 2 := by
            have h1 : Nat.gcd p (q - 1) ∣ q + 1 :=
              dvd_trans (Nat.gcd_dvd_left p (q - 1)) hpq
            have h2 : Nat.gcd p (q - 1) ∣ q - 1 := Nat.gcd_dvd_right p (q - 1)
            have h3 : Nat.gcd p (q - 1) ∣ (q + 1) - (q - 1) := Nat.dvd_sub h1 h2
            rwa [show (q + 1) - (q - 1) = 2 from by omega] at h3
          exact dvd_trans (Nat.dvd_gcd hordp hordqm) hg
        have hpne2 : p ≠ 2 := by
          intro h; subst h
          obtain ⟨c, hc⟩ := h2q
          obtain ⟨d, hd⟩ := hpq
          omega
        have hg1 : Nat.gcd p 2 = 1 :=
          Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hpne2))
        have hdvd : orderOf θ ∣ 1 := by
          rw [← hg1]
          exact Nat.dvd_gcd hordp hord2
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    rw [hθ1, inv_one]
    simp
  · have hcop : (q + 1).Coprime p := (hp.coprime_iff_not_dvd.mpr hpq).symm
    let u : (ZMod p)ˣ := ZMod.unitOfCoprime (q + 1) hcop
    let a : ℕ := ZMod.val (-((u⁻¹ : (ZMod p)ˣ) : ZMod p))
    refine ⟨θ ^ a, ?_, ?_, ?_⟩
    · rw [map_pow, hσθ]
    · rw [← pow_mul, mul_comm a p, pow_mul, hθp, one_pow]
    · have hcoe : (a : ZMod p) = -((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        exact ZMod.natCast_zmod_val (-((u⁻¹ : (ZMod p)ˣ) : ZMod p))
      have hcoe_u : ((u : ZMod p)) = (q + 1 : ZMod p) := by
        have := ZMod.coe_unitOfCoprime (q + 1) hcop
        simpa [u] using this
      have ha : (a : ZMod p) * (q + 1 : ZMod p) = -1 := by
        rw [hcoe, ← hcoe_u, neg_mul, Units.inv_mul]
      have ha1 : ((a * (q + 1) + 1 : ℕ) : ZMod p) = 0 := by
        push_cast
        rw [ha]
        ring
      have hpdvd : p ∣ a * (q + 1) + 1 := by
        have := (ZMod.natCast_eq_natCast_iff (a * (q + 1) + 1) 0 p).mp (by simpa using ha1)
        exact Nat.modEq_zero_iff_dvd.mp this
      have hordp : orderOf θ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hθp
      have hpow1 : θ ^ (a * (q + 1) + 1) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (dvd_trans hordp hpdvd)
      have hmul : θ * θ ^ (a * (q + 1)) = 1 := by
        rw [← pow_succ']; exact hpow1
      rw [← pow_mul]
      exact eq_inv_of_mul_eq_one_right hmul

private theorem cUni_map_smul {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Mul K]
    (f : K → K) (hf : ∀ a b, f (a * b) = f a * f b) (c : K) (M : Matrix n n K) :
    (c • M).map f = (f c) • M.map f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply]
  exact hf c (M i j)

private theorem cUni_smul_pow {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (c : K) (M : Matrix n n K) (k : ℕ) : (c • M) ^ k = c ^ k • M ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

private theorem cUni_map_transpose {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Semiring K]
    {K' : Type} [Semiring K'] (f : K → K') (M : Matrix n n K) :
    (Mᵀ).map f = (M.map f)ᵀ := by
  ext i j
  simp [Matrix.map_apply, Matrix.transpose_apply]

private theorem cUni_transpose_pow {n : Type} [Fintype n] [DecidableEq n] {K : Type} [CommSemiring K]
    (M : Matrix n n K) (k : ℕ) : (Mᵀ) ^ k = (M ^ k)ᵀ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← Matrix.transpose_mul M (M ^ k), pow_succ']

private theorem uni_descent_of_not_dvd {K : Type} [Field K] [Fintype K] [CharP K 2] {d p q : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d) (hK : Fintype.card K = q ^ 2)
    (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p) (x : GL (Fin d) K) (hxU : x ∈ LargeEvenGUSet (Fin d) K q)
    (lam : Kˣ) (hx : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (lam : K) • (x : Matrix (Fin d) (Fin d) K))
    (ν : Kˣ) (hxp : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1) :
    ∃ μ : Kˣ, ((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map σ₀ = (μ : K) • (x : Matrix (Fin d) (Fin d) K) ∧
      ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) ^ p = 1 ∧
      (((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map (· ^ q))ᵀ *
        ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) = 1 := by
  classical
  have hmul (a b : K) : σ₀ (a * b) = σ₀ a * σ₀ b := map_mul σ₀ a b
  have hqq (a b : K) : (a * b) ^ q = a ^ q * b ^ q := mul_pow a b q
  have hcard2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq2le : 2 ≤ q := by
    by_contra h
    interval_cases q <;> omega
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  let i0 : Fin d := ⟨0, hdpos⟩
  let Mx : Matrix (Fin d) (Fin d) K := (x : Matrix (Fin d) (Fin d) K)
  have hx' : Mx.map σ₀ = (lam : K) • Mx := hx
  have hxp' : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1 := hxp
  obtain ⟨μx, hμx0, hμxq, hμxU⟩ := hxU
  obtain ⟨μ₁, hμ₁⟩ := lin_descent σ₀ x lam hx
  let y₁ : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ₁ * x
  have hy1 : (y₁ : Matrix (Fin d) (Fin d) K) = (μ₁ : K) • Mx := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hfix₁ : (y₁ : Matrix (Fin d) (Fin d) K).map σ₀ = (y₁ : Matrix (Fin d) (Fin d) K) := by
    rw [hy1]; exact hμ₁
  have hν₁ : ∃ ν₁ : Kˣ, ((y₁ ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (ν₁ : K) • 1 := by
    refine ⟨μ₁ ^ p * ν, ?_⟩
    rw [Units.val_pow_eq_pow_val, hy1, cUni_smul_pow, ← Units.val_pow_eq_pow_val x p, hxp,
      smul_smul, Units.val_mul, Units.val_pow_eq_pow_val]
  obtain ⟨ν₁, hν₁⟩ := hν₁
  obtain ⟨μ₂, hμ₂fix, hμ₂pow⟩ := lin_order_p hp (Or.inl hpd) σ₀ y₁ hfix₁ ν₁ hν₁
  let μ : Kˣ := μ₂ * μ₁
  have hμval : (μ : K) = (μ₂ : K) * (μ₁ : K) := Units.val_mul μ₂ μ₁
  have hyfix : ((μ : K) • Mx).map σ₀ = (μ : K) • Mx := by
    rw [hμval, mul_smul,
      cUni_map_smul (n := Fin d) (K := K) σ₀ hmul (μ₂ : K) ((μ₁ : K) • Mx), hμ₂fix, hμ₁]
  have hypow : ((μ : K) • Mx) ^ p = 1 := by
    rw [hμval, mul_smul, ← hy1]
    exact hμ₂pow
  let θ : K := (μ : K) ^ q * (μ : K) * μx
  have hyU : (((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx) = θ • 1 := by
    rw [cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq (μ : K) Mx, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, hμxU, smul_smul, smul_smul]
  have hyfixq : (((μ : K) • Mx).map (· ^ q)).map σ₀ = ((μ : K) • Mx).map (· ^ q) := by
    ext i j
    have ha : σ₀ (((μ : K) • Mx) i j) = ((μ : K) • Mx) i j := by
      have h1 := congrFun (congrFun hyfix i) j
      simpa [Matrix.map_apply] using h1
    simp only [Matrix.map_apply]
    rw [map_pow, ha]
  have hθσ : σ₀ θ = θ := by
    have hA : ((((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx)).map σ₀ =
        (((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx) := by
      rw [Matrix.map_mul, cUni_map_transpose σ₀, hyfixq, hyfix]
    have hB : ((((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx)).map σ₀ = σ₀ θ • 1 := by
      rw [hyU, cUni_map_smul (n := Fin d) (K := K) σ₀ hmul θ 1]
      congr 1
      ext i j
      simp [Matrix.map_apply, Matrix.one_apply]
    have hC : θ • (1 : Matrix (Fin d) (Fin d) K) = σ₀ θ • (1 : Matrix (Fin d) (Fin d) K) :=
      by rw [← hyU, ← hA, hB]
    have h := congrFun (congrFun hC i0) i0
    simpa using h.symm
  have hθq : θ ^ q = θ := by
    have hcard : (μ : K) ^ (q ^ 2 - 1) = 1 := by
      have h1 : (μ ^ (q ^ 2 - 1) : Kˣ) = 1 := by
        have h2 := pow_card_eq_one' (x := μ)
        rw [Nat.card_units, Nat.card_eq_fintype_card, hK] at h2
        exact h2
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have hμqq : (μ : K) ^ (q * q) = (μ : K) := by
      rw [show q * q = q ^ 2 from by ring,
        ← Nat.sub_add_cancel (by nlinarith [hq2le] : 1 ≤ q ^ 2), pow_add, hcard, one_mul,
        pow_one]
    rw [show θ = (μ : K) ^ q * (μ : K) * μx from rfl, mul_pow, mul_pow, ← pow_mul, hμqq,
      hμxq]
    ring
  obtain ⟨N, hNprime, hN⟩ := FiniteField.card K 2
  have hm : ∃ m, q = 2 ^ m := by
    have hq2 : q ^ 2 = 2 ^ (N : ℕ) := by rw [← hK, hN]
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd q with ⟨m, hm⟩ | ⟨r, hrprime, hrq, hrodd⟩
    · exact ⟨m, hm⟩
    · exfalso
      have hr2N : r ∣ 2 ^ (N : ℕ) := by
        rw [← hq2]
        simpa [pow_two] using dvd_mul_of_dvd_left hrq q
      have hr2 : r ∣ 2 := hrprime.dvd_of_dvd_pow hr2N
      have h2r : 2 = r := (Nat.Prime.dvd_iff_eq Nat.prime_two hrprime.ne_one).mp hr2
      rw [← h2r] at hrodd
      rw [Nat.odd_iff] at hrodd
      omega
  obtain ⟨m, hm⟩ := hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hm; omega
    · exact h0
  have h2q : 2 ∣ q := by
    rw [hm]
    exact ⟨2 ^ (m - 1), by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]⟩
  let φ : K →+* K := iterateFrobenius K 2 m
  have hφ : ∀ a : K, φ a = a ^ q := by
    intro a
    rw [show φ a = a ^ 2 ^ m from iterateFrobenius_def 2 m a, hm]
  have hmapφ : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ q) = M.map φ := by
    intro M
    ext i j
    show M i j ^ q = φ (M i j)
    rw [hφ]
  let Y : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ * x
  have hYcoe : (Y : Matrix (Fin d) (Fin d) K) = (μ : K) • Mx := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hYp : Y ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hYcoe]
    exact hypow
  have hAp : (((μ : K) • Mx).map (· ^ q)) ^ p = 1 := by
    rw [hmapφ ((μ : K) • Mx), ← hYcoe, ← Matrix.map_pow, ← Units.val_pow_eq_pow_val Y p,
      hYp, Units.val_one]
    ext i j
    simp [Matrix.map_apply, Matrix.one_apply]
  have hθp : θ ^ p = 1 := by
    have hAt : (((μ : K) • Mx).map (· ^ q))ᵀ =
        θ • ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have hYinv : (Y : Matrix (Fin d) (Fin d) K) *
          ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
        rw [← Units.val_mul]
        simp
      calc (((μ : K) • Mx).map (· ^ q))ᵀ
          = (((μ : K) • Mx).map (· ^ q))ᵀ * (Y : Matrix (Fin d) (Fin d) K) *
              ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc, hYinv, Matrix.mul_one]
        _ = (((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx) *
              ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hYcoe]
        _ = (θ • 1) * ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hyU]
        _ = θ • ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
    have hAeq : ((μ : K) • Mx).map (· ^ q) =
        θ • (((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ := by
      calc ((μ : K) • Mx).map (· ^ q)
          = ((((μ : K) • Mx).map (· ^ q))ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
        _ = (θ • ((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ := by rw [hAt]
        _ = θ • (((Y⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))ᵀ :=
            Matrix.transpose_smul _ _
    have h1 : (((μ : K) • Mx).map (· ^ q)) ^ p = θ ^ p • 1 := by
      rw [hAeq, cUni_smul_pow]
      congr 1
      rw [cUni_transpose_pow, ← Units.val_pow_eq_pow_val (Y⁻¹) p, inv_pow, hYp, inv_one,
        Units.val_one, Matrix.transpose_one]
    have h2 : θ ^ p • (1 : Matrix (Fin d) (Fin d) K) = 1 := by rw [← h1, hAp]
    have hh := congrFun (congrFun h2 i0) i0
    simpa [Matrix.smul_apply, Matrix.one_apply] using hh
  obtain ⟨η, hση, hηp, hηq⟩ := cUni_exists_eta p q hp h2q σ₀ hθσ hθp hθq
  have hη0 : η ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hηp
    exact zero_ne_one hηp
  let ηu : Kˣ := Units.mk0 η hη0
  have hηuval : (ηu : K) = η := rfl
  refine ⟨ηu * μ, ?_, ?_, ?_⟩
  · rw [Units.val_mul, hηuval, mul_smul,
      cUni_map_smul (n := Fin d) (K := K) σ₀ hmul η ((μ : K) • Mx), hση, hyfix]
  · rw [Units.val_mul, hηuval, mul_smul, cUni_smul_pow, hηp, hypow]
    simp
  · rw [Units.val_mul, hηuval, mul_smul,
      cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq η ((μ : K) • Mx),
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hyU, smul_smul, smul_smul]
    have hc : (η ^ q * η) * θ = 1 := by
      rw [← pow_succ, hηq]
      exact inv_mul_cancel₀ (by
        intro h
        rw [h, zero_pow hp.ne_zero] at hθp
        exact zero_ne_one hθp)
    rw [hc, one_smul]

private theorem cW2_exists_pow_root {K : Type} [Field K] {N k : ℕ} (hN : 0 < N)
    (hkN : Nat.Coprime k N) {z : K} (hzN : z ^ N = 1) : ∃ a : ℕ, (z ^ a) ^ k = z := by
  by_cases hN1 : N = 1
  · refine ⟨1, ?_⟩
    rw [hN1, pow_one] at hzN
    rw [pow_one, hzN, one_pow]
  · have hN2 : 1 < N := by omega
    obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hkN hN2
    refine ⟨a, ?_⟩
    have hmod : k * a = N * (k * a / N) + 1 := by
      have h := Nat.div_add_mod (k * a) N
      rw [ha] at h
      exact h.symm
    rw [← pow_mul, mul_comm a k, hmod, pow_add, pow_mul, hzN, one_pow, one_mul, pow_one]

private theorem cW2_pow_isometry {K : Type} [Field K] [Fintype K] {d p : ℕ}
    (φ : K →+* K) (A : GL (Fin d) K)
    (hA : ((A : Matrix (Fin d) (Fin d) K).map φ)ᵀ * (A : Matrix (Fin d) (Fin d) K) = 1) :
    (((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map φ)ᵀ *
      ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  have hAinv : ((A : Matrix (Fin d) (Fin d) K).map φ)ᵀ =
      ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have hAinv1 : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A : Matrix (Fin d) (Fin d) K).map φ)ᵀ
        = ((A : Matrix (Fin d) (Fin d) K).map φ)ᵀ *
            ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
            rw [hAinv1, Matrix.mul_one]
      _ = (((A : Matrix (Fin d) (Fin d) K).map φ)ᵀ * (A : Matrix (Fin d) (Fin d) K)) *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
      _ = ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [hA, Matrix.one_mul]
  have h1 : (((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map φ)ᵀ =
      ((((A⁻¹ : GL (Fin d) K) ^ p : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) := by
    rw [Units.val_pow_eq_pow_val, Matrix.map_pow, Matrix.transpose_pow, hAinv,
      Units.val_pow_eq_pow_val]
  have h2 : ((A⁻¹ : GL (Fin d) K) ^ p) * (A ^ p : GL (Fin d) K) = 1 := by
    rw [inv_pow, inv_mul_cancel]
  rw [h1, Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val (A⁻¹) p, ← Units.val_mul,
    h2, Units.val_one]

private theorem cW2_theta_fixed {K : Type} [Field K] [Fintype K] [CharP K 2] {d q : ℕ}
    (hK : Fintype.card K = q ^ 2) (σ₀ : K ≃+* K) (Mx : Matrix (Fin d) (Fin d) K)
    (μ : Kˣ) (μx : K) (i0 : Fin d)
    (hfix : (((μ : K) • Mx).map σ₀) = (μ : K) • Mx)
    (hμxq : μx ^ q = μx)
    (hμxU : (Mx.map (· ^ q))ᵀ * Mx = μx • 1) :
    σ₀ ((μ : K) ^ q * (μ : K) * μx) = (μ : K) ^ q * (μ : K) * μx ∧
    ((μ : K) ^ q * (μ : K) * μx) ^ q = (μ : K) ^ q * (μ : K) * μx := by
  have hmul (a b : K) : σ₀ (a * b) = σ₀ a * σ₀ b := map_mul σ₀ a b
  have hqq (a b : K) : (a * b) ^ q = a ^ q * b ^ q := mul_pow a b q
  have hcard2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq2le : 2 ≤ q := by
    by_contra hcon
    push Not at hcon
    interval_cases q <;> omega
  let θ : K := (μ : K) ^ q * (μ : K) * μx
  have hyU : (((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx) = θ • 1 := by
    rw [cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq (μ : K) Mx, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, hμxU, smul_smul, smul_smul]
  have hyfixq : (((μ : K) • Mx).map (· ^ q)).map σ₀ = ((μ : K) • Mx).map (· ^ q) := by
    ext i j
    have ha : σ₀ (((μ : K) • Mx) i j) = ((μ : K) • Mx) i j := by
      have h1 := congrFun (congrFun hfix i) j
      simpa [Matrix.map_apply] using h1
    simp only [Matrix.map_apply]
    rw [map_pow, ha]
  have hθσ : σ₀ θ = θ := by
    have hA : ((((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx)).map σ₀ =
        (((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx) := by
      rw [Matrix.map_mul, cUni_map_transpose σ₀, hyfixq, hfix]
    have hB : ((((μ : K) • Mx).map (· ^ q))ᵀ * ((μ : K) • Mx)).map σ₀ = σ₀ θ • 1 := by
      rw [hyU, cUni_map_smul (n := Fin d) (K := K) σ₀ hmul θ 1]
      congr 1
      ext i j
      simp [Matrix.map_apply, Matrix.one_apply]
    have hC : θ • (1 : Matrix (Fin d) (Fin d) K) = σ₀ θ • (1 : Matrix (Fin d) (Fin d) K) :=
      by rw [← hyU, ← hA, hB]
    have h := congrFun (congrFun hC i0) i0
    simpa using h.symm
  have hθq : θ ^ q = θ := by
    have hcard : (μ : K) ^ (q ^ 2 - 1) = 1 := by
      have h1 : (μ ^ (q ^ 2 - 1) : Kˣ) = 1 := by
        have h2 := pow_card_eq_one' (x := μ)
        rw [Nat.card_units, Nat.card_eq_fintype_card, hK] at h2
        exact h2
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have hμqq : (μ : K) ^ (q * q) = (μ : K) := by
      rw [show q * q = q ^ 2 from by ring,
        ← Nat.sub_add_cancel (by nlinarith [hq2le] : 1 ≤ q ^ 2), pow_add, hcard, one_mul,
        pow_one]
    rw [show θ = (μ : K) ^ q * (μ : K) * μx from rfl, mul_pow, mul_pow, ← pow_mul, hμqq,
      hμxq]
    ring
  exact ⟨hθσ, hθq⟩




private theorem cW2_map_pow_fixed {K : Type} [Field K] [Fintype K] {d p : ℕ}
    (σ₀ : K →+* K) (M : Matrix (Fin d) (Fin d) K) (hM : M.map σ₀ = M) :
    (M ^ p).map σ₀ = M ^ p := by
  rw [← RingHom.mapMatrix_apply] at hM ⊢
  rw [map_pow, hM]

private theorem cW2_uni_descent_not_dvd {K : Type} [Field K] [Fintype K] [CharP K 2] {d p q : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ q + 1) (hK : Fintype.card K = q ^ 2)
    (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p) (x : GL (Fin d) K)
    (hxU : x ∈ LargeEvenGUSet (Fin d) K q)
    (lam : Kˣ) (hx : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (lam : K) • (x : Matrix (Fin d) (Fin d) K))
    (ν : Kˣ) (hxp : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1) :
    ∃ μ : Kˣ, ((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map σ₀ = (μ : K) • (x : Matrix (Fin d) (Fin d) K) ∧
      ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) ^ p = 1 ∧
      (((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map (· ^ q))ᵀ *
        ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) = 1 := by
  classical
  have hmul (a b : K) : σ₀ (a * b) = σ₀ a * σ₀ b := map_mul σ₀ a b
  have hqq (a b : K) : (a * b) ^ q = a ^ q * b ^ q := mul_pow a b q
  have hcard2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq2le : 2 ≤ q := by
    by_contra hcon
    push Not at hcon
    interval_cases q <;> omega
  obtain ⟨N, hNprime, hN⟩ := FiniteField.card K 2
  have hm : ∃ m, q = 2 ^ m := by
    have hq2 : q ^ 2 = 2 ^ (N : ℕ) := by rw [← hK, hN]
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd q with ⟨m, hm⟩ | ⟨r, hrprime, hrq, hrodd⟩
    · exact ⟨m, hm⟩
    · exfalso
      have hr2N : r ∣ 2 ^ (N : ℕ) := by
        rw [← hq2]
        simpa [pow_two] using dvd_mul_of_dvd_left hrq q
      have hr2 : r ∣ 2 := hrprime.dvd_of_dvd_pow hr2N
      have h2r : 2 = r := (Nat.Prime.dvd_iff_eq Nat.prime_two hrprime.ne_one).mp hr2
      rw [← h2r] at hrodd
      rw [Nat.odd_iff] at hrodd
      omega
  obtain ⟨m, hm⟩ := hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hm; omega
    · exact h0
  have h2q : 2 ∣ q := by
    rw [hm]
    exact ⟨2 ^ (m - 1), by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]⟩
  let φ : K →+* K := iterateFrobenius K 2 m
  have hφ : ∀ a : K, φ a = a ^ q := by
    intro a
    rw [show φ a = a ^ 2 ^ m from iterateFrobenius_def 2 m a, hm]
  have hmapφ : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ q) = M.map φ := by
    intro M
    ext i j
    show M i j ^ q = φ (M i j)
    rw [hφ]
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨1, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  let i0 : Fin d := ⟨0, hdpos⟩
  let Mx : Matrix (Fin d) (Fin d) K := (x : Matrix (Fin d) (Fin d) K)
  obtain ⟨μx, hμx0, hμxq, hμxU⟩ := hxU
  obtain ⟨μ₁, hμ₁⟩ := lin_descent σ₀ x lam hx
  let y₁ : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ₁ * x
  have hy1 : (y₁ : Matrix (Fin d) (Fin d) K) = (μ₁ : K) • Mx := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul]
  have hfix₁ : (y₁ : Matrix (Fin d) (Fin d) K).map σ₀ = (y₁ : Matrix (Fin d) (Fin d) K) := by
    rw [hy1]; exact hμ₁
  have hν₁ : ∃ ν₁ : Kˣ, ((y₁ ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (ν₁ : K) • 1 := by
    refine ⟨μ₁ ^ p * ν, ?_⟩
    rw [Units.val_pow_eq_pow_val, hy1, cUni_smul_pow, ← Units.val_pow_eq_pow_val x p, hxp,
      smul_smul, Units.val_mul, Units.val_pow_eq_pow_val]
  obtain ⟨ν₁, hν₁⟩ := hν₁
  obtain ⟨hθ₁σ, hθ₁q⟩ := cW2_theta_fixed hK σ₀ Mx μ₁ μx i0 hμ₁ hμxq hμxU
  have hθ₁0 : (μ₁ : K) ^ q * (μ₁ : K) * μx ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ μ₁.ne_zero) μ₁.ne_zero) hμx0
  have hθ₁qm1 : ((μ₁ : K) ^ q * (μ₁ : K) * μx) ^ (q - 1) = 1 := by
    have h2 : ((μ₁ : K) ^ q * (μ₁ : K) * μx) ^ (q - 1) * ((μ₁ : K) ^ q * (μ₁ : K) * μx) =
        1 * ((μ₁ : K) ^ q * (μ₁ : K) * μx) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), hθ₁q, one_mul]
    exact mul_right_cancel₀ hθ₁0 h2
  have hcop2 : Nat.Coprime (q + 1) (q - 1) := by
    have hodd : Odd (q + 1) := by
      obtain ⟨t, ht⟩ := h2q
      exact ⟨t, by omega⟩
    have hcop : Nat.Coprime (q - 1) (q + 1) := by
      have hc := (Nat.coprime_self_sub_left (m := 2) (n := q + 1) (by omega : 2 ≤ q + 1)).mpr
        hodd.coprime_two_left
      rwa [show q + 1 - 2 = q - 1 from by omega] at hc
    exact hcop.symm
  obtain ⟨aη, haη⟩ := cW2_exists_pow_root (N := q - 1) (k := q + 1) (by omega : 0 < q - 1) hcop2
    (z := ((μ₁ : K) ^ q * (μ₁ : K) * μx)⁻¹) (by rw [inv_pow, hθ₁qm1, inv_one])
  let η : K := ((μ₁ : K) ^ q * (μ₁ : K) * μx)⁻¹ ^ aη
  have hηq : η ^ (q + 1) = ((μ₁ : K) ^ q * (μ₁ : K) * μx)⁻¹ := haη
  have hη0 : η ≠ 0 := pow_ne_zero _ (inv_ne_zero hθ₁0)
  have hση : σ₀ η = η := by
    simp only [η, map_pow, map_inv₀, hθ₁σ]
  let ηu : Kˣ := Units.mk0 η hη0
  let Y₂ : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) ηu * y₁
  have hY₂coe : (Y₂ : Matrix (Fin d) (Fin d) K) = η • ((μ₁ : K) • Mx) := by
    rw [Units.val_mul, hy1, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_eq_diagonal_mul, Units.val_mk0, Matrix.smul_eq_diagonal_mul]
  have hY₂fix : (Y₂ : Matrix (Fin d) (Fin d) K).map σ₀ = (Y₂ : Matrix (Fin d) (Fin d) K) := by
    rw [hY₂coe, cUni_map_smul (n := Fin d) (K := K) σ₀ hmul η ((μ₁ : K) • Mx), hση, hμ₁]
  have hyU₁ : (((μ₁ : K) • Mx).map (· ^ q))ᵀ * ((μ₁ : K) • Mx) =
      ((μ₁ : K) ^ q * (μ₁ : K) * μx) • 1 := by
    rw [cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq (μ₁ : K) Mx, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, hμxU, smul_smul, smul_smul]
  have hY₂iso : ((Y₂ : Matrix (Fin d) (Fin d) K).map (· ^ q))ᵀ * (Y₂ : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hY₂coe, cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq η ((μ₁ : K) • Mx),
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hyU₁, smul_smul, smul_smul]
    have hc : (η ^ q * η) * ((μ₁ : K) ^ q * (μ₁ : K) * μx) = 1 := by
      rw [← pow_succ, hηq]
      exact inv_mul_cancel₀ hθ₁0
    rw [hc, one_smul]
  have hY₂p : ((Y₂ ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (η ^ p * (ν₁ : K)) • 1 := by
    rw [Units.val_pow_eq_pow_val, hY₂coe, cUni_smul_pow, ← hy1, ← Units.val_pow_eq_pow_val y₁ p,
      hν₁, smul_smul]
  have hlam0 : η ^ p * (ν₁ : K) ≠ 0 := mul_ne_zero (pow_ne_zero _ hη0) ν₁.ne_zero
  have hlamq1 : (η ^ p * (ν₁ : K)) ^ (q + 1) = 1 := by
    have hY₂isoφ : ((Y₂ : Matrix (Fin d) (Fin d) K).map φ)ᵀ * (Y₂ : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← hmapφ]; exact hY₂iso
    have hpow := cW2_pow_isometry (p := p) φ Y₂ hY₂isoφ
    have hmap_lam : ((η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K)).map φ =
        φ (η ^ p * (ν₁ : K)) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hij]
    have htrans_lam : (((η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K)).map φ)ᵀ =
        φ (η ^ p * (ν₁ : K)) • 1 := by
      rw [hmap_lam, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hY₂p] at hpow
    rw [htrans_lam, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hpow
    have h2 := congrFun (congrFun hpow i0) i0
    rw [Matrix.smul_apply, Matrix.one_apply, if_pos rfl, smul_eq_mul, mul_one] at h2
    rw [hφ (η ^ p * (ν₁ : K))] at h2
    rwa [← pow_succ] at h2
  have hlamfix : σ₀ (η ^ p * (ν₁ : K)) = η ^ p * (ν₁ : K) := by
    have hm1 : ((η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K)).map σ₀ =
        (η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K) := by
      rw [← hY₂p, Units.val_pow_eq_pow_val]
      exact cW2_map_pow_fixed (d := d) (p := p) (σ₀ : K →+* K)
        ((Y₂ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) hY₂fix
    have hm2 : ((η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K)).map σ₀ =
        σ₀ (η ^ p * (ν₁ : K)) • (1 : Matrix (Fin d) (Fin d) K) := by
      rw [cUni_map_smul (n := Fin d) (K := K) σ₀ hmul (η ^ p * (ν₁ : K)) 1]
      congr 1
      ext i j
      simp [Matrix.map_apply, Matrix.one_apply]
    have h2 := congrFun (congrFun (hm1.symm.trans hm2) i0) i0
    simpa using h2.symm
  have hcop_p : Nat.Coprime p (q + 1) := hp.coprime_iff_not_dvd.mpr h
  obtain ⟨aζ, haζ⟩ := cW2_exists_pow_root (N := q + 1) (k := p) (by omega : 0 < q + 1) hcop_p
    (z := η ^ p * (ν₁ : K)) hlamq1
  let ζ : K := (η ^ p * (ν₁ : K)) ^ aζ
  have hζp : ζ ^ p = η ^ p * (ν₁ : K) := haζ
  have hζ0 : ζ ≠ 0 := pow_ne_zero _ hlam0
  have hσζ : σ₀ ζ = ζ := by simp only [ζ, map_pow, hlamfix]
  have hζq1 : ζ ^ (q + 1) = 1 := by
    rw [show ζ = (η ^ p * (ν₁ : K)) ^ aζ from rfl, ← pow_mul, mul_comm aζ (q + 1), pow_mul,
      hlamq1, one_pow]
  let ζu : Kˣ := Units.mk0 ζ hζ0
  let μf : Kˣ := ζu⁻¹ * ηu * μ₁
  have hμcoe : (μf : K) = ζ⁻¹ * η * (μ₁ : K) := by
    rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rfl
  refine ⟨μf, ?_, ?_, ?_⟩
  · rw [hμcoe, mul_smul, mul_smul, ← hY₂coe]
    rw [cUni_map_smul (n := Fin d) (K := K) σ₀ hmul ζ⁻¹ (Y₂ : Matrix (Fin d) (Fin d) K),
      map_inv₀, hσζ, hY₂fix]
  · rw [hμcoe, mul_smul, mul_smul, ← hY₂coe, cUni_smul_pow, ← Units.val_pow_eq_pow_val Y₂ p,
      hY₂p, smul_smul, inv_pow, hζp, inv_mul_cancel₀ hlam0, one_smul]
  · rw [hμcoe, mul_smul, mul_smul, ← hY₂coe]
    rw [cUni_map_smul (n := Fin d) (K := K) (· ^ q) hqq ζ⁻¹ (Y₂ : Matrix (Fin d) (Fin d) K),
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hY₂iso, smul_smul]
    have hc : ζ⁻¹ ^ q * ζ⁻¹ = 1 := by
      rw [← pow_succ, inv_pow, hζq1, inv_one]
    rw [hc, one_smul]

theorem uni_descent {K : Type} [Field K] [Fintype K] [CharP K 2] {d p q : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ d ∨ ¬ p ∣ q + 1) (hK : Fintype.card K = q ^ 2)
    (σ₀ : K ≃+* K) (hσ₀ : orderOf σ₀ = p) (x : GL (Fin d) K) (hxU : x ∈ LargeEvenGUSet (Fin d) K q)
    (lam : Kˣ) (hx : (x : Matrix (Fin d) (Fin d) K).map σ₀ = (lam : K) • (x : Matrix (Fin d) (Fin d) K))
    (ν : Kˣ) (hxp : ((x ^ p : GL _ K) : Matrix (Fin d) (Fin d) K) = (ν : K) • 1) :
    ∃ μ : Kˣ, ((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map σ₀ = (μ : K) • (x : Matrix (Fin d) (Fin d) K) ∧
      ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) ^ p = 1 ∧
      (((μ : K) • (x : Matrix (Fin d) (Fin d) K)).map (· ^ q))ᵀ *
        ((μ : K) • (x : Matrix (Fin d) (Fin d) K)) = 1 := by
  rcases hpd with h | h
  · exact uni_descent_of_not_dvd hp h hK σ₀ hσ₀ x hxU lam hx ν hxp
  · exact cW2_uni_descent_not_dvd hp h hK σ₀ hσ₀ x hxU lam hx ν hxp

end CFSG.HardMathSupport.C14Cl
