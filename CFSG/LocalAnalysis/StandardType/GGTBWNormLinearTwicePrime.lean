module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLinearCentralCard
public import CFSG.LocalAnalysis.StandardType.GGPGLQuadPhase
public import CFSG.LocalAnalysis.StandardType.GGPGLCommForm
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotMove
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace TypeA

theorem exists_scalar_mul_of_conjAut_eq {d : ℕ} {K : Type} [Field K] [Finite K] (hd : 0 < d)
    {B B' : GL (Fin d) K} (h : conjAut d K B = conjAut d K B') :
    ∃ c : Kˣ, B = GeneralLinearGroup.scalar (Fin d) c * B' := by
  have h1 : conjAut d K (B * B'⁻¹) = 1 := by rw [map_mul, h, map_inv, mul_inv_cancel]
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one h1
  obtain ⟨u, hu⟩ := exists_unit_of_scalar hd hc
  exact ⟨u, by rw [← hu, inv_mul_cancel_right]⟩

section NonToral

variable {K : Type} [Field K] [Finite K] {d p : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* projectiveSL d K} {A : Subgroup (MulAut L')}

theorem false_of_normalizing_move (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hp2 : p ≠ 2)
    (hd0 : 0 < d) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    {x₀ y₀ : GL (Fin d) K} (hx₀ : conjAut d K x₀ ∈ inducedSub ψ A)
    (hy₀ : conjAut d K y₀ ∈ inducedSub ψ A) {u₀ : Kˣ}
    (hu₀ : x₀ * y₀ = GeneralLinearGroup.scalar (Fin d) u₀ * (y₀ * x₀)) (hu₀1 : u₀ ≠ 1)
    (E : SpecialLinearGroup (Fin d) K)
    (hEN : ∀ g : GL (Fin d) K, conjAut d K g ∈ inducedSub ψ A →
      conjAut d K (SpecialLinearGroup.toGL E * g * (SpecialLinearGroup.toGL E)⁻¹) ∈
        inducedSub ψ A)
    {k : ℕ} (hk : ¬ p ∣ k) {cE : Kˣ}
    (hEy : SpecialLinearGroup.toGL E * y₀ * (SpecialLinearGroup.toGL E)⁻¹ =
      GeneralLinearGroup.scalar (Fin d) cE * (y₀ * x₀ ^ k))
    [Fact p.Prime] {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have hc := QuotMove.isScalarQuot_PSL (K := K) hd0
  have hXI : ∀ x ∈ inducedSub ψ A, ∃ g : GL (Fin d) K, conjAut d K g = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  refine QuotMove.false_of_normalizing_move hc hp hpK hp2 hψ hker hperf hA (fun a ha => ?_)
    (x₀ := ⟨x₀, Subgroup.mem_top _⟩) (y₀ := ⟨y₀, Subgroup.mem_top _⟩) hx₀ hy₀ hu₀ hu₀1
    ⟨SpecialLinearGroup.toGL E, E, rfl⟩ (fun x hx => ?_) hk hEy ι φ h α hdiag hlin hgen
  · obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨⟨B, Subgroup.mem_top _⟩, hφa⟩
  · obtain ⟨g, rfl⟩ := hXI x hx
    have := hEN g hx
    rwa [map_mul, map_mul, map_inv] at this

theorem exists_comm_pow_of_mem (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d)
    (hψ : Function.Surjective ψ) (hA : IsElemAbelian p A) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {x g : GL (Fin d) K} (hx : conjAut d K x ∈ inducedSub ψ A)
    (hg : conjAut d K g ∈ inducedSub ψ A) :
    ∃ m : ℕ, x * g = GeneralLinearGroup.scalar (Fin d) (ζ ^ m) * (g * x) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hG := isProjElem_comap (d := d) (K := K) hd0 (isElemAbelian_inducedSub hψ hA)
  have hxG : x ∈ (inducedSub ψ A).comap (conjAut d K) := hx
  have hgG : g ∈ (inducedSub ψ A).comap (conjAut d K) := hg
  have hu := PGLTor.commChar_pow_eq_one hG hxG ⟨g, hgG⟩
  obtain ⟨m, -, hm⟩ := QuotMove.exists_pow_eq_units hζ hu
  exact ⟨m, by rw [hm]; exact PGLTor.commChar_spec hG hxG ⟨g, hgG⟩⟩

theorem false_of_noncomm_lifts (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    (hpd : p ∣ d) (hd0 : 0 < d) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    {x₀ y₀ : GL (Fin d) K} (hx₀ : conjAut d K x₀ ∈ inducedSub ψ A)
    (hy₀ : conjAut d K y₀ ∈ inducedSub ψ A) (hx₀p : x₀ ^ p = 1) {u₀ : Kˣ}
    (hu₀ : x₀ * y₀ = GeneralLinearGroup.scalar (Fin d) u₀ * (y₀ * x₀)) (hu₀1 : u₀ ≠ 1)
    (hu₀p : u₀ ^ p = 1) [Fact p.Prime] {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  set ζ : Kˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
    exact hζ₀
  obtain ⟨D, hdet, hDact⟩ := PGLTor.exists_quadPhase hp hp5 (by rw [Fintype.card_fin]; exact hpd)
    hζ hx₀p hu₀1 hu₀p hu₀
  set Ds : SpecialLinearGroup (Fin d) K := ⟨(D : Matrix (Fin d) (Fin d) K), hdet⟩ with hDs
  have hDsGL : SpecialLinearGroup.toGL Ds = D := Units.ext rfl
  obtain ⟨k, hkp, hk⟩ := QuotMove.exists_pow_eq_units hζ hu₀p
  have hk0 : ¬ p ∣ k := by
    rintro ⟨j, rfl⟩
    have hj : j = 0 := by
      by_contra hj
      have := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hj)
      omega
    apply hu₀1
    rw [← hk, hj, mul_zero, pow_zero]
  obtain ⟨cE, hcE⟩ := hDact y₀ k (by rw [hk]; exact hu₀)
  refine false_of_normalizing_move hp hpK hp2 hd0 hψ hker hperf hA hAI hx₀ hy₀ hu₀ hu₀1 Ds
    ?_ hk0 (by rw [hDsGL]; exact hcE) ι φ h α hdiag hlin hgen
  intro g hg
  obtain ⟨m, hm⟩ := exists_comm_pow_of_mem hp hp2 hd0 hψ hA hζ hx₀ hg
  obtain ⟨c, hc⟩ := hDact g m hm
  rw [hDsGL, hc, map_mul, conjAut_scalar, one_mul, map_mul, map_pow]
  exact Subgroup.mul_mem _ hg (Subgroup.pow_mem _ hx₀ _)

omit [Finite K] in
theorem conj_scalar_mul (D W : GL (Fin d) K) (c : Kˣ) :
    D * (GeneralLinearGroup.scalar (Fin d) c * W) * D⁻¹ =
      GeneralLinearGroup.scalar (Fin d) c * (D * W * D⁻¹) := by
  rw [← mul_assoc D, ← (PGLTor.commute_scalar c D).eq]
  simp only [mul_assoc]

omit [Finite K] in
theorem conj_inv_mem_of_conj_mem {G : Type*} [Group G] {X : Subgroup G} [Finite X] {σ : G}
    (hσ : ∀ x ∈ X, σ * x * σ⁻¹ ∈ X) : ∀ x ∈ X, σ⁻¹ * x * σ ∈ X := by
  have hle : X.map (MulAut.conj σ).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hσ x hx
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj σ).injective).ge
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : x = σ * y * σ⁻¹ := by rw [← hyx]; rfl
  rw [hyx', show σ⁻¹ * (σ * y * σ⁻¹) * σ = y by group]
  exact hy

theorem exists_cube_of_not_cube {l : Kˣ} (hl : ¬ ∃ c : Kˣ, c ^ 3 = l) (z : Kˣ) :
    ∃ j < 3, ∃ μ : Kˣ, μ ^ 3 = z * l ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := TypeA.PGLTor.PowQuot K 3
  set x : Q := (QuotientGroup.mk l : Q) with hx
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hx, TypeA.PGLTor.powQuot_mk_eq_one_iff] at h1
    exact hl h1
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨l, rfl⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hinj : Function.Injective fun j : Fin 3 => x ^ (j : ℕ) := by
    intro i j hij
    have := pow_injOn_Iio_orderOf (x := x) (by rw [hord]; exact i.2) (by rw [hord]; exact j.2) hij
    exact Fin.ext this
  have hbij := hinj.bijective_of_nat_card_le (by
    simpa using TypeA.PGLTor.card_powQuot_le (K := K) (p := 3))
  obtain ⟨j, hj⟩ := hbij.2 (QuotientGroup.mk z⁻¹ : Q)
  have hj' : x ^ (j : ℕ) = (QuotientGroup.mk z⁻¹ : Q) := hj
  refine ⟨j, j.2, ?_⟩
  have h1 : (QuotientGroup.mk (z * l ^ (j : ℕ)) : Q) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, ← hx, hj', ← QuotientGroup.mk_mul,
      mul_inv_cancel, QuotientGroup.mk_one]
  exact (TypeA.PGLTor.powQuot_mk_eq_one_iff).mp h1

theorem false_of_noncomm_lifts_three (hpK : 3 ∣ Nat.card K - 1) (hd3 : 3 ∣ d) (hd0 : 0 < d)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ Set.range (conjAut d K), ∀ l : L', φ (ψ l) = ψ (a l))
    {x₀ y₀ : GL (Fin d) K} (hx₀ : conjAut d K x₀ ∈ inducedSub ψ A)
    (hy₀ : conjAut d K y₀ ∈ inducedSub ψ A) (hx₀p : x₀ ^ 3 = 1) {u₀ : Kˣ}
    (hu₀ : x₀ * y₀ = GeneralLinearGroup.scalar (Fin d) u₀ * (y₀ * x₀)) (hu₀1 : u₀ ≠ 1)
    (hu₀p : u₀ ^ 3 = 1) {l : Kˣ} (hl : y₀ ^ 3 = GeneralLinearGroup.scalar (Fin d) l)
    [Fact (Nat.Prime 3)] {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod 3) V) (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := 3) ι (φ i) v = v - α i v • h i)
    (hgen : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range φ)) : False := by
  classical
  obtain ⟨m, hdm⟩ := hd3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : NeZero 3 := ⟨by norm_num⟩
  have : Finite (MulAut (projectiveSL d K)) :=
    Finite.of_injective (fun f : MulAut (projectiveSL d K) => (f : projectiveSL d K → _))
      DFunLike.coe_injective
  obtain ⟨ζ₀, hζ₀⟩ := PGLTor.exists_isPrimitiveRoot_of_dvd hp hpK
  set ζ : Kˣ := (hζ₀.isUnit (by norm_num)).unit with hζdef
  have hζ : IsPrimitiveRoot ζ 3 := by
    rw [← IsPrimitiveRoot.coe_units_iff, hζdef, IsUnit.unit_spec]
    exact hζ₀
  obtain ⟨k, -, hk⟩ := QuotMove.exists_pow_eq_units hζ hu₀p
  have hk0 : ¬ 3 ∣ k := by
    rintro ⟨j, rfl⟩
    apply hu₀1
    rw [← hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hxy : x₀ * y₀ = GeneralLinearGroup.scalar (Fin d) (ζ ^ k) * (y₀ * x₀) := by
    rw [hk]; exact hu₀
  have hcard : Fintype.card (Fin d) / 3 = m := by
    rw [Fintype.card_fin, hdm, Nat.mul_div_cancel_left _ (by norm_num)]
  set X := inducedSub ψ A with hXdef
  have hphase : ∀ {w D : GL (Fin d) K}, conjAut d K w ∈ X →
      (∀ (x : GL (Fin d) K) (m : ℕ), w * x = GeneralLinearGroup.scalar (Fin d) (ζ ^ m) * (x * w) →
        ∃ c : Kˣ, D * x * D⁻¹ = GeneralLinearGroup.scalar (Fin d) c * (x * w ^ m)) →
      ∀ g, conjAut d K g ∈ X → conjAut d K (D * g * D⁻¹) ∈ X := by
    intro w D hw hD g hg
    obtain ⟨m, hm⟩ := exists_comm_pow_of_mem hp (by norm_num) hd0 hψ hA hζ hw hg
    obtain ⟨c, hc⟩ := hD g m hm
    rw [hc, map_mul, conjAut_scalar, one_mul, map_mul, map_pow]
    exact X.mul_mem hg (X.pow_mem hw _)
  have hXI : ∀ x ∈ X, ∃ g : GL (Fin d) K, conjAut d K g = x := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a ha
    exact ⟨B, induced_unique ψ hψ hφa hxa⟩
  have hinv : ∀ D : GL (Fin d) K, (∀ g, conjAut d K g ∈ X → conjAut d K (D * g * D⁻¹) ∈ X) →
      ∀ g, conjAut d K g ∈ X → conjAut d K (D⁻¹ * g * D) ∈ X := by
    intro D hD g hg
    have h1 : ∀ x ∈ X, conjAut d K D * x * (conjAut d K D)⁻¹ ∈ X := by
      intro x hx
      obtain ⟨g', rfl⟩ := hXI x hx
      have := hD g' hx
      rwa [map_mul, map_mul, map_inv] at this
    have h2 := conj_inv_mem_of_conj_mem h1 _ hg
    rwa [← map_inv, ← map_mul, ← map_mul] at h2
  have hy₀p : ∀ j : ℕ, conjAut d K (y₀ ^ j) ∈ X := fun j => by
    rw [map_pow]; exact X.pow_mem hy₀ _
  obtain ⟨Dx, hDxdet, hDx⟩ := PGLTor.exists_quadPhase_three hζ hx₀p hu₀1 hu₀p hu₀
  rw [hcard] at hDxdet
  have hDxN := hphase hx₀ hDx
  obtain ⟨cx, hcx⟩ := hDx y₀ k hxy
  by_cases hcube : ∃ c : Kˣ, c ^ 3 = l
  ·
    obtain ⟨c, hc⟩ := hcube
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : GL (Fin d) K, y₁ = GeneralLinearGroup.scalar (Fin d) c⁻¹ * y₀ :=
      ⟨_, rfl⟩
    have hy₁X : conjAut d K y₁ ∈ X := by rw [hy₁, map_mul, conjAut_scalar, one_mul]; exact hy₀
    have hy₁p : y₁ ^ 3 = 1 := by
      rw [hy₁, (PGLTor.commute_scalar _ y₀).mul_pow, hl, ← map_pow, ← map_mul, inv_pow, hc,
        inv_mul_cancel, map_one]
    have hyx : y₀ * x₀ = GeneralLinearGroup.scalar (Fin d) u₀⁻¹ * (x₀ * y₀) := by
      rw [hu₀, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    have hy₁x : y₁ * x₀ = GeneralLinearGroup.scalar (Fin d) u₀⁻¹ * (x₀ * y₁) := by
      rw [hy₁, mul_assoc, hyx, ← mul_assoc, ← map_mul, mul_comm c⁻¹ u₀⁻¹, map_mul, mul_assoc,
        ← mul_assoc (GeneralLinearGroup.scalar (Fin d) c⁻¹) x₀ y₀,
        (PGLTor.commute_scalar c⁻¹ x₀).eq, mul_assoc]
    obtain ⟨Dy, hDydet, hDy⟩ := PGLTor.exists_quadPhase_three hζ hy₁p (inv_ne_one.mpr hu₀1)
      (by rw [inv_pow, hu₀p, inv_one]) hy₁x
    rw [hcard] at hDydet
    have hDyN := hphase hy₁X hDy
    obtain ⟨cy, hcy⟩ := hDy y₁ 0 (by rw [pow_zero, map_one, one_mul])
    have hdet : ((Dx * Dy⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
      have h1 : ((Dy * Dy⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
        rw [mul_inv_cancel, Units.val_one, Matrix.det_one]
      rw [Units.val_mul, Matrix.det_mul] at h1 ⊢
      rw [hDxdet]
      rw [hDydet] at h1
      exact h1
    set E : SpecialLinearGroup (Fin d) K := ⟨_, hdet⟩ with hE
    have hEGL : SpecialLinearGroup.toGL E = Dx * Dy⁻¹ := Units.ext rfl
    refine false_of_normalizing_move hp hpK (by norm_num) hd0 hψ hker hperf hA hAI hx₀ hy₀
      hu₀ hu₀1 E ?_ hk0 (cE := cx * cy⁻¹) ?_ ι φ h α hdiag hlin hgen
    · intro g hg
      rw [hEGL, _root_.mul_inv_rev, inv_inv, show Dx * Dy⁻¹ * g * (Dy * Dx⁻¹) =
        Dx * (Dy⁻¹ * g * Dy) * Dx⁻¹ by group]
      exact hDxN _ (hinv Dy hDyN g hg)
    ·
      have e1 : Dy * y₁ * Dy⁻¹ = GeneralLinearGroup.scalar (Fin d) cy * y₁ := by
        simpa using hcy
      have hy₀₁ : y₀ = GeneralLinearGroup.scalar (Fin d) c * y₁ := by
        rw [hy₁, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      have e3 : y₁ = GeneralLinearGroup.scalar (Fin d) cy * (Dy⁻¹ * y₁ * Dy) := by
        have := conj_scalar_mul Dy⁻¹ y₁ cy
        rw [inv_inv, ← e1, show Dy⁻¹ * (Dy * y₁ * Dy⁻¹) * Dy = y₁ by group] at this
        exact this
      have e2 : Dy⁻¹ * y₁ * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y₁ := by
        calc Dy⁻¹ * y₁ * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ *
              (GeneralLinearGroup.scalar (Fin d) cy * (Dy⁻¹ * y₁ * Dy)) := by
              rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
          _ = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y₁ := by rw [← e3]
      have h1 : Dy⁻¹ * y₀ * Dy = GeneralLinearGroup.scalar (Fin d) cy⁻¹ * y₀ := by
        have e4 := conj_scalar_mul Dy⁻¹ y₁ c
        rw [inv_inv, ← hy₀₁, e2] at e4
        rw [e4, hy₀₁, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm c cy⁻¹]
      rw [hEGL, _root_.mul_inv_rev, inv_inv, show Dx * Dy⁻¹ * y₀ * (Dy * Dx⁻¹) =
        Dx * (Dy⁻¹ * y₀ * Dy) * Dx⁻¹ by group, h1, conj_scalar_mul, hcx, ← mul_assoc,
        ← map_mul, mul_comm cy⁻¹ cx]
  ·
    have hdety : (y₀ : Matrix (Fin d) (Fin d) K).det = (l : K) ^ m := by
      have := PGLTor.det_eq_pow_of_pow_eq_scalar (p := 3) (by norm_num) hx₀p hu₀1 hu₀p hu₀ hl
      rwa [hcard] at this
    obtain ⟨j, -, μ, hμ⟩ := exists_cube_of_not_cube hcube ζ
    set E' := GeneralLinearGroup.scalar (Fin d) μ⁻¹ * Dx * y₀ ^ j with hE'
    have hdet : (E' : Matrix (Fin d) (Fin d) K).det = 1 := by
      have hμK : (μ : K) ^ 3 = (ζ : K) * (l : K) ^ j := by
        have := congrArg (fun u : Kˣ => (u : K)) hμ
        simpa using this
      rw [hE', Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hDxdet,
        Units.val_pow_eq_pow_val, Matrix.det_pow, hdety, hdm]
      calc ((μ⁻¹ : Kˣ) : K) ^ (3 * m) * (ζ : K) ^ m * ((l : K) ^ m) ^ j
          = (((μ⁻¹ : Kˣ) : K) ^ 3 * ((ζ : K) * (l : K) ^ j)) ^ m := by ring
        _ = 1 := by
          rw [← hμK, ← mul_pow, Units.val_inv_eq_inv_val, inv_mul_cancel₀ μ.ne_zero, one_pow,
            one_pow]
    set E : SpecialLinearGroup (Fin d) K := ⟨_, hdet⟩ with hE
    have hEGL : SpecialLinearGroup.toGL E = E' := Units.ext rfl
    refine false_of_normalizing_move hp hpK (by norm_num) hd0 hψ hker hperf hA hAI hx₀ hy₀
      hu₀ hu₀1 E ?_ hk0 (cE := cx) ?_ ι φ h α hdiag hlin hgen
    · intro g hg
      rw [hEGL, hE', show GeneralLinearGroup.scalar (Fin d) μ⁻¹ * Dx * y₀ ^ j * g *
          (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * Dx * y₀ ^ j)⁻¹ =
          GeneralLinearGroup.scalar (Fin d) μ⁻¹ * (Dx * (y₀ ^ j * g * (y₀ ^ j)⁻¹) * Dx⁻¹) *
            (GeneralLinearGroup.scalar (Fin d) μ⁻¹)⁻¹ by group,
        map_mul, map_mul, conjAut_scalar, map_inv (conjAut d K), conjAut_scalar, one_mul,
        inv_one, mul_one]
      refine hDxN _ ?_
      rw [map_mul, map_mul, map_inv]
      exact X.mul_mem (X.mul_mem (hy₀p j) hg) (X.inv_mem (hy₀p j))
    · have hY : y₀ ^ j * y₀ * (y₀ ^ j)⁻¹ = y₀ := by
        rw [← pow_succ, pow_succ', mul_assoc, mul_inv_cancel, mul_one]
      rw [hEGL, hE', show GeneralLinearGroup.scalar (Fin d) μ⁻¹ * Dx * y₀ ^ j * y₀ *
          (GeneralLinearGroup.scalar (Fin d) μ⁻¹ * Dx * y₀ ^ j)⁻¹ =
          GeneralLinearGroup.scalar (Fin d) μ⁻¹ * (Dx * (y₀ ^ j * y₀ * (y₀ ^ j)⁻¹) * Dx⁻¹) *
            (GeneralLinearGroup.scalar (Fin d) μ⁻¹)⁻¹ by group, hY, hcx,
        (PGLTor.commute_scalar μ⁻¹ _).eq, mul_assoc, mul_inv_cancel, mul_one]

end NonToral

theorem ggTorusWNormSC_twice_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hdp : d = 2 * p) :
    GGTorusWNormSC p (projectiveSL d K) (Set.range (conjAut d K)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hd : 5 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have : Nonempty (Fin d) := ⟨⟨0, hd0⟩⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _ Λ _ _ M C V _ _ ι φ h α
    hM hC hpair hlin hgen s hs
  classical
  have hXA : IsElemAbelian p (inducedSub ψ A) := isElemAbelian_inducedSub hψ hA
  set G := (inducedSub ψ A).comap (conjAut d K) with hGdef
  have hG : PGLTor.IsProjElem p G := isProjElem_comap hd0 hXA
  by_cases hcent : ∀ x ∈ G, x ^ p = 1 → ∀ y ∈ G, y * x = x * y
  · rcases PGLTor.toral_or_card_le_of_central_sharp hp hp2 hpK hG hcent with ⟨A₀, hA₀⟩ | hle
    · have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
        (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
          (Or.inl (by omega))).commutator_eq_top
      obtain ⟨π, hπs, hπker, hdiag⟩ := TypeANbrDvd.exists_actsDiag_model hperfSL
        (slHasSections_of_five_le hd) hψ hker hperf hAI (A₀ := A₀) fun B hB => hA₀ B hB
      exact ggWNormConcl_of_linear_diagonal hp hp2 hpK hd hπs hπker hA h3 hsc hdiag
        hM hC ι φ h α hpair hlin hgen hs
    · exfalso
      have h1 : Nat.card A ≤ p ^ 2 :=
        card_actor_le_of_scalar_lift_bound hd0 hψ hker hperf hAI (by
          simpa only [G, Fintype.card_fin, hdp, Nat.mul_div_cancel _ hp.pos] using hle)
      have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
  · exfalso
    push Not at hcent
    obtain ⟨x₀, hx₀G, hx₀p, y₀, hy₀G, hne⟩ := hcent
    have hu₀1 : PGLTor.commChar hG hx₀G ⟨y₀, hy₀G⟩ ≠ 1 := fun h1 =>
      hne ((PGLTor.commChar_eq_one_iff hG hx₀G ⟨y₀, hy₀G⟩).mp h1).symm
    have hdiag : ∀ i, α i (h i) = 2 := fun i => by rw [hpair i i, hC.1 i]; simp
    rcases eq_or_ne p 3 with rfl | hp3'
    · obtain ⟨l, hl⟩ := hG.pow_scalar y₀ hy₀G
      exact false_of_noncomm_lifts_three hpK ⟨2, by omega⟩ hd0 hψ hker hperf hA hAI hx₀G hy₀G hx₀p
        (PGLTor.commChar_spec hG hx₀G ⟨y₀, hy₀G⟩) hu₀1
        (PGLTor.commChar_pow_eq_one hG hx₀G ⟨y₀, hy₀G⟩) hl ι φ h α hdiag hlin hgen
    · have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h5 | h5
        · interval_cases p <;> first | omega | exact absurd hp (by norm_num)
        · exact h5
      exact false_of_noncomm_lifts hp hp5 hpK (hdp ▸ dvd_mul_left p 2) hd0 hψ hker hperf hA hAI
        hx₀G hy₀G hx₀p (PGLTor.commChar_spec hG hx₀G ⟨y₀, hy₀G⟩) hu₀1
        (PGLTor.commChar_pow_eq_one hG hx₀G ⟨y₀, hy₀G⟩) ι φ h α hdiag hlin hgen

end TypeA

theorem ggTorusWNormSC_linear_twice_prime {K : Type} [Field K] [Finite K] [CharP K 2]
    {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hdp : d = 2 * p) :
    GGTorusWNormSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk _) Set.univ) :=
  ggTorusWNormSC_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (TypeA.ggTorusWNormSC_twice_prime hp hp2 hpK hdp)

theorem largeEvenLabelAll_wnorm_linear_twice_prime {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : lab.tag = .A)
    (hdp : lab.rank + 1 = 2 * p) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at ht hdp hpq ⊢
  subst tag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) Q at hQ
  change LargeEvenRecipeLinear (r + 1) (2 ^ n) (fun R _ I F => Q R I F ∧ GGTorusWNormSC p R I)
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusWNormSC_linear_twice_prime hp hp2 (by rwa [hK]) hdp

end CFSG.StandardType
