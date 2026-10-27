module

public import CFSG.RankThree.PartOne.NF7J.EvenCore
public import CFSG.RankThree.PartOne.NF7J.Odd

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.HESS

section FtSec

variable {G : Type} [Group G] [Finite G] (p : ℕ) (E : Subgroup G)

@[expose] def Zset (t : MulAut E) : Set G :=
  {x | x ∈ kZero p E t ∧ x ∈ Subgroup.centralizer (E : Set G) ∧ x ^ 3 = 1}

@[expose] def Ft (t : MulAut E) : Subgroup G := Subgroup.closure (Zset p E t)

variable {p E}

theorem conj_Zset_sub {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (t : MulAut E) :
    (MulAut.conj w) '' Zset p E t ⊆ Zset p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  rintro _ ⟨x, ⟨hxK, hxC, hx3⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [kZero_conj p t hw]
    exact ⟨x, hxK, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : w⁻¹ * e * w ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (E : Set G)).inv_mem hw) e).1 he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hxC _ he'
    show e * (w * x * w⁻¹) = w * x * w⁻¹ * e
    calc e * (w * x * w⁻¹) = w * ((w⁻¹ * e * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * e * w)) * w⁻¹ := by rw [h1]
      _ = w * x * w⁻¹ * e := by group
  · show (w * x * w⁻¹) ^ 3 = 1
    rw [conj_pow, hx3]
    group

theorem Ft_conj_le {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (t : MulAut E) :
    conjBy w (Ft p E t) ≤ Ft p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  unfold conjBy Ft
  rw [MonoidHom.map_closure]
  exact Subgroup.closure_mono (conj_Zset_sub hw t)

theorem Ft_conj {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (t : MulAut E) :
    conjBy w (Ft p E t) = Ft p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) := by
  apply le_antisymm (Ft_conj_le hw t)
  have hw' := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have h1 := Ft_conj_le (p := p) hw' (conjAut E w hw * t * (conjAut E w hw)⁻¹)
  have h2 : conjAut E w⁻¹ hw' * (conjAut E w hw * t * (conjAut E w hw)⁻¹) *
      (conjAut E w⁻¹ hw')⁻¹ = t := by
    rw [Equivariance.conjAut_inv hw]
    group
  rw [h2] at h1
  have h3 := Subgroup.map_mono (f := (MulAut.conj w).toMonoidHom) h1
  have h4 : conjBy w (conjBy w⁻¹ (Ft p E (conjAut E w hw * t * (conjAut E w hw)⁻¹))) =
      Ft p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) := Equivariance.conjBy_conjBy_inv w _
  rw [← h4]
  exact h3

end FtSec

section PhiE

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} (D : Datum p E)

@[expose] noncomputable def phiE (g : M32) : Subgroup G := by
  classical
  exact if h : det3 g = 1 then Ft p E (D.ν * ((D.e.symm (matUnit' g h) : ↥D.H) : MulAut E)) else ⊥

theorem phiE_unit (x : GL (Fin 3) (ZMod 2)) :
    phiE D (x : M32) = Ft p E (D.ν * ((D.e.symm x : ↥D.H) : MulAut E)) := by
  classical
  have e : matUnit' (x : M32) (det3_GL x) = x := Units.ext (matUnit'_val _ _)
  unfold phiE
  simp only [det3_GL x, ↓reduceDIte, e]

theorem phiE_conj {h : M32} (hh : det3 h = 1) :
    ∃ σ : MulAut G, ∀ g g₁ : M32, det3 g = 1 → h * g = g₁ * h →
      phiE D g₁ = (phiE D g).map σ.toMonoidHom := by
  obtain ⟨hu, rfl⟩ := exists_unit_of_det hh
  obtain ⟨w, hw, hwe⟩ := D.exists_lift (D.e.symm hu).2
  refine ⟨MulAut.conj w, fun g g₁ hg e1 => ?_⟩
  have d1 : det3 g₁ = 1 := by
    have := det3_mul (hu : M32) g
    rw [e1, det3_mul, det3_GL hu, hg] at this
    simpa using this
  obtain ⟨x, rfl⟩ := exists_unit_of_det hg
  obtain ⟨x₁, rfl⟩ := exists_unit_of_det d1
  have u1 : x₁ = hu * x * hu⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact e1.symm
  rw [phiE_unit, phiE_unit, u1]
  have hν := D.ν_comm ((D.e.symm hu : ↥D.H) : MulAut E)
  have hnode : D.ν * ((D.e.symm (hu * x * hu⁻¹) : ↥D.H) : MulAut E) =
      conjAut E w hw * (D.ν * ((D.e.symm x : ↥D.H) : MulAut E)) * (conjAut E w hw)⁻¹ := by
    rw [hwe]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc D.ν * (((D.e.symm hu : ↥D.H) : MulAut E) * ((D.e.symm x : ↥D.H) : MulAut E) *
          ((D.e.symm hu : ↥D.H) : MulAut E)⁻¹)
        = (D.ν * ((D.e.symm hu : ↥D.H) : MulAut E)) * ((D.e.symm x : ↥D.H) : MulAut E) *
          ((D.e.symm hu : ↥D.H) : MulAut E)⁻¹ := by simp only [mul_assoc]
      _ = (((D.e.symm hu : ↥D.H) : MulAut E) * D.ν) * ((D.e.symm x : ↥D.H) : MulAut E) *
          ((D.e.symm hu : ↥D.H) : MulAut E)⁻¹ := by rw [hν]
      _ = ((D.e.symm hu : ↥D.H) : MulAut E) * (D.ν * ((D.e.symm x : ↥D.H) : MulAut E)) *
          ((D.e.symm hu : ↥D.H) : MulAut E)⁻¹ := by simp only [mul_assoc]
  rw [hnode, ← Ft_conj hw]
  rfl

end PhiE

section Diag

variable {K : Type} [Field K]

theorem hmat_injective {a b : Kˣ} (h : (hmat a : Matrix.SpecialLinearGroup (Fin 2) K) = hmat b) :
    a = b := by
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 0 0) h
  simp only [e2_hmat_00] at this
  exact Units.ext this

theorem diag_of_comm {ζ : Kˣ} (hζ2 : ζ ^ 2 ≠ 1) {X : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : X * hmat ζ = hmat ζ * X) : ∃ u : Kˣ, X = hmat u := by
  have hz : (ζ : K) ≠ 0 := ζ.ne_zero
  have hne : (ζ : K) - (ζ : K)⁻¹ ≠ 0 := by
    intro h0
    apply hζ2
    have : (ζ : K) ^ 2 = 1 := by
      field_simp at h0
      linear_combination h0
    exact Units.ext (by simpa using this)
  have h01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 0 1) h
  have h10 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => e2 M 1 0) h
  simp only [e2_mul, e2_hmat_00, e2_hmat_01, e2_hmat_10, e2_hmat_11, mul_zero, add_zero,
    zero_add] at h01 h10
  have x01 : e2 X 0 1 = 0 := by
    have : e2 X 0 1 * ((ζ : K)⁻¹ - (ζ : K)) = 0 := by linear_combination h01
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd (by linear_combination -h') hne
  have x10 : e2 X 1 0 = 0 := by
    have : e2 X 1 0 * ((ζ : K) - (ζ : K)⁻¹) = 0 := by linear_combination h10
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' hne
  have hdet := e2_det X
  rw [x01, x10, mul_zero, sub_zero] at hdet
  have hu : e2 X 0 0 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨Units.mk0 (e2 X 0 0) hu, ?_⟩
  apply e2_ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [e2_hmat_00]
  · simp [e2_hmat_01, x01]
  · simp [e2_hmat_10, x10]
  · simp only [Fin.mk_one, Fin.isValue, e2_hmat_11, Units.val_mk0]
    field_simp
    linear_combination hdet

end Diag

section Base

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K)

namespace RFrame

@[expose] noncomputable def dg : Kˣ × Kˣ →* G := F.rgHom.comp (spDiag K)

theorem dg_apply (x : Kˣ × Kˣ) : F.dg x = F.rgHom (spDiag K x) := rfl

theorem dg_injective : Function.Injective F.dg := F.rgHom_injective.comp spDiag_injective

theorem dg_central (x : Kˣ × Kˣ) : F.dg x ∈ Subgroup.centralizer (E : Set G) := by
  have hle : E ≤ Subgroup.centralizer ({F.dg x} : Set G) := by
    refine F.hEA.trans (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact F.hcL _ (F.rgHom_mem _)
    · intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨hzE, hzL⟩ := hz
      obtain ⟨a, b, -, -, hab⟩ := mem_torus7_iff.1
        (F.lam_mem_torus7_of_mem_E (x := ⟨z, hzL⟩) hzE)
      have hg : F.lam ⟨z, hzL⟩ = spDiag K (a, b) := Subtype.ext hab
      have hz' : z = F.rgHom (spDiag K (a, b)) := by
        have := F.rgHom_lam ⟨z, hzL⟩
        rw [hg] at this
        exact this.symm
      rw [hz', dg_apply, ← map_mul, ← map_mul]
      congr 1
      rw [← map_mul, ← map_mul, mul_comm]
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have := hle he
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem phi₀_hmat (u : Kˣ) : F.phi₀ (hmat u) = F.dg (u, 1) := by
  rw [phi₀, MonoidHom.comp_apply, hmat_eq_diag2, spBlock_diag2]
  rfl

theorem phi₁_hmat (u : Kˣ) : F.phi₁ (hmat u) = F.dg (u, u⁻¹) := by
  rw [phi₁, MonoidHom.comp_apply, hmat_eq_diag2, spBlock'_diag2]
  rfl

omit [Finite K] [CharP K 2] in
theorem hmat_one' : (hmat (1 : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K) = 1 := by
  simpa using (hmat_pow (K := K) 1 0).symm

theorem Zset_r₀_sub (hp : p.Prime) (h5 : 5 ≤ p) {x : G} (hx : x ∈ Zset p E F.r₀) :
    ∃ u : Kˣ, u ^ 3 = 1 ∧ x = F.dg (u, 1) := by
  obtain ⟨hxK, hxC, hx3⟩ := hx
  have hxK' : x ∈ F.phi₀.range := by rw [F.phi₀_range]; exact hxK
  obtain ⟨M, rfl⟩ := hxK'
  have hbE : F.phi₀ (hmat F.ζ) ∈ E := F.phi₀_hmat_mem_E
  have hcomm := Subgroup.mem_centralizer_iff.1 hxC _ hbE
  have h1 : M * hmat F.ζ = hmat F.ζ * M := by
    apply F.phi₀_injective
    rw [map_mul, map_mul]
    exact hcomm.symm
  obtain ⟨u, rfl⟩ := diag_of_comm (F.hζ2 h5) h1
  refine ⟨u, ?_, F.phi₀_hmat u⟩
  have h3 : (F.phi₀ (hmat u)) ^ 3 = 1 := hx3
  rw [← map_pow, ← map_one F.phi₀] at h3
  have h2 := F.phi₀_injective h3
  rw [hmat_pow, ← hmat_one'] at h2
  exact hmat_injective h2

theorem Zset_r₁_sub (hp : p.Prime) (h5 : 5 ≤ p) {x : G} (hx : x ∈ Zset p E F.r₁) :
    ∃ u : Kˣ, u ^ 3 = 1 ∧ x = F.dg (u, u⁻¹) := by
  obtain ⟨hxK, hxC, hx3⟩ := hx
  have hxK' : x ∈ F.phi₁.range := by rw [F.phi₁_range]; exact hxK
  obtain ⟨M, rfl⟩ := hxK'
  have hbE : F.phi₁ (hmat F.ζ) ∈ E := F.phi₁_hmat_mem_E
  have hcomm := Subgroup.mem_centralizer_iff.1 hxC _ hbE
  have h1 : M * hmat F.ζ = hmat F.ζ * M := by
    apply F.phi₁_injective
    rw [map_mul, map_mul]
    exact hcomm.symm
  obtain ⟨u, rfl⟩ := diag_of_comm (F.hζ2 h5) h1
  refine ⟨u, ?_, F.phi₁_hmat u⟩
  have h3 : (F.phi₁ (hmat u)) ^ 3 = 1 := hx3
  rw [← map_pow, ← map_one F.phi₁] at h3
  have h2 := F.phi₁_injective h3
  rw [hmat_pow, ← hmat_one'] at h2
  exact hmat_injective h2

theorem cube_of_primitive {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) {u : Kˣ} (hu : u ^ 3 = 1) :
    ∃ i : ℕ, ω ^ i = u := by
  have hωK : IsPrimitiveRoot (ω : K) 3 := hω.map_of_injective (f := Units.coeHom K) Units.val_injective
  have hu' : (u : K) ^ 3 = 1 := by
    have := congrArg (fun v : Kˣ => (v : K)) hu
    simpa using this
  obtain ⟨i, -, hi⟩ := hωK.eq_pow_of_pow_eq_one hu'
  exact ⟨i, Units.ext (by simpa using hi)⟩

theorem Ft_r₀ {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) (hp : p.Prime) (h5 : 5 ≤ p) :
    Ft p E F.r₀ = Subgroup.zpowers (F.dg (ω, 1)) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Zset_r₀_sub F hp h5 hx
    obtain ⟨i, rfl⟩ := cube_of_primitive hω hu
    have : (ω ^ i, (1 : Kˣ)) = (ω, (1 : Kˣ)) ^ i := by simp
    rw [SetLike.mem_coe, this, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    apply Subgroup.subset_closure
    refine ⟨?_, F.dg_central _, ?_⟩
    · rw [← F.phi₀_hmat, ← F.phi₀_range]
      exact ⟨_, rfl⟩
    · rw [← map_pow]
      have : (ω, (1 : Kˣ)) ^ 3 = 1 := by simp [hω.pow_eq_one]
      rw [this, map_one]

theorem Ft_r₁ {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) (hp : p.Prime) (h5 : 5 ≤ p) :
    Ft p E F.r₁ = Subgroup.zpowers (F.dg (ω, ω⁻¹)) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Zset_r₁_sub F hp h5 hx
    obtain ⟨i, rfl⟩ := cube_of_primitive hω hu
    have : (ω ^ i, (ω ^ i)⁻¹) = (ω, ω⁻¹) ^ i := by simp
    rw [SetLike.mem_coe, this, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    apply Subgroup.subset_closure
    refine ⟨?_, F.dg_central _, ?_⟩
    · rw [← F.phi₁_hmat, ← F.phi₁_range]
      exact ⟨_, rfl⟩
    · rw [← map_pow]
      have : (ω, ω⁻¹) ^ 3 = 1 := by simp [hω.pow_eq_one]
      rw [this, map_one]

theorem lift_form₀ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₀)
    (hkr : conjAut E k hk = F.r₀) : ∃ u : Kˣ, k = F.rgHom (spDiag K (u, 1) * wEl 1) := by
  obtain ⟨X, hX⟩ : ∃ X, F.phi₀ X = k := by
    rw [← F.phi₀_range] at hkK
    exact hkK
  have hbE : F.b₀ ∈ E := F.phi₀_hmat_mem_E
  have hsq : F.r₀ * F.r₀ = 1 := RFrame.r₀_sq F
  have h1 : ((F.r₀ ⟨F.b₀, hbE⟩ : E) : G) = F.b₀⁻¹ :=
    refl_inv_of_mem_movedInG hsq hc (F.b₀_mem_moved hp) hbE
  have h2 : k * F.b₀ * k⁻¹ = F.b₀⁻¹ := by
    have := Equivariance.coe_conjAut hk ⟨F.b₀, hbE⟩
    rw [hkr, h1] at this
    exact this.symm
  have h3 : X * hmat F.ζ = (hmat F.ζ)⁻¹ * X := by
    apply F.phi₀_injective
    rw [map_mul, map_mul, map_inv, hX]
    show k * F.b₀ = F.b₀⁻¹ * k
    calc k * F.b₀ = (k * F.b₀ * k⁻¹) * k := by group
      _ = F.b₀⁻¹ * k := by rw [h2]
  obtain ⟨h00, h11⟩ := antidiag_of_inv (F.hζ2 h5) h3
  obtain ⟨u, hu⟩ := spBlock_anti h00 h11
  refine ⟨u, ?_⟩
  rw [← hu, ← hX]
  rfl

theorem lift_form₁ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₁)
    (hkr : conjAut E k hk = F.r₁) : ∃ u : Kˣ, k = F.rgHom (spDiag K (u, u⁻¹) * wEl 0) := by
  obtain ⟨X, hX⟩ : ∃ X, F.phi₁ X = k := by
    rw [← F.phi₁_range] at hkK
    exact hkK
  have hbE : F.b₁ ∈ E := F.phi₁_hmat_mem_E
  have hsq : F.r₁ * F.r₁ = 1 := RFrame.r₁_sq F
  have h1 : ((F.r₁ ⟨F.b₁, hbE⟩ : E) : G) = F.b₁⁻¹ :=
    refl_inv_of_mem_movedInG hsq hc (F.b₁_mem_moved hp) hbE
  have h2 : k * F.b₁ * k⁻¹ = F.b₁⁻¹ := by
    have := Equivariance.coe_conjAut hk ⟨F.b₁, hbE⟩
    rw [hkr, h1] at this
    exact this.symm
  have h3 : X * hmat F.ζ = (hmat F.ζ)⁻¹ * X := by
    apply F.phi₁_injective
    rw [map_mul, map_mul, map_inv, hX]
    show k * F.b₁ = F.b₁⁻¹ * k
    calc k * F.b₁ = (k * F.b₁ * k⁻¹) * k := by group
      _ = F.b₁⁻¹ * k := by rw [h2]
  obtain ⟨h00, h11⟩ := antidiag_of_inv (F.hζ2 h5) h3
  obtain ⟨u, hu⟩ := spBlock'_anti h00 h11
  refine ⟨u, ?_⟩
  rw [← hu, ← hX]
  rfl

theorem conj_dg_r₀ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₀)
    (hkr : conjAut E k hk = F.r₀) (a b : Kˣ) : k * F.dg (a, b) * k⁻¹ = F.dg (a⁻¹, b) := by
  obtain ⟨u, rfl⟩ := F.lift_form₀ hp h5 hc hk hkK hkr
  rw [dg_apply, dg_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have h1 := wEl_conj_spDiag (K := K) 1 a b
  have hw : wtor 1 a b = (a⁻¹, b) := by simp [wtor]
  rw [hw] at h1
  have hD : spDiag K (u, 1) * spDiag K (a⁻¹, b) = spDiag K (a⁻¹, b) * spDiag K (u, 1) := by
    rw [← map_mul, ← map_mul, mul_comm]
  calc spDiag K (u, 1) * wEl 1 * spDiag K (a, b) * (spDiag K (u, 1) * wEl 1)⁻¹
      = spDiag K (u, 1) * (wEl 1 * spDiag K (a, b) * (wEl 1)⁻¹) * (spDiag K (u, 1))⁻¹ := by group
    _ = spDiag K (u, 1) * spDiag K (a⁻¹, b) * (spDiag K (u, 1))⁻¹ := by rw [h1]
    _ = spDiag K (a⁻¹, b) := by rw [hD]; group

theorem conj_dg_r₁ (hp : p.Prime) (h5 : 5 ≤ p) (hc : ∀ x y : E, x * y = y * x) {k : G}
    (hk : k ∈ Subgroup.normalizer (E : Set G)) (hkK : k ∈ kZero p E F.r₁)
    (hkr : conjAut E k hk = F.r₁) (a b : Kˣ) : k * F.dg (a, b) * k⁻¹ = F.dg (b, a) := by
  obtain ⟨u, rfl⟩ := F.lift_form₁ hp h5 hc hk hkK hkr
  rw [dg_apply, dg_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have h1 := wEl_conj_spDiag (K := K) 0 a b
  have hw : wtor 0 a b = (b, a) := by simp [wtor]
  rw [hw] at h1
  have hD : spDiag K (u, u⁻¹) * spDiag K (b, a) = spDiag K (b, a) * spDiag K (u, u⁻¹) := by
    rw [← map_mul, ← map_mul, mul_comm]
  calc spDiag K (u, u⁻¹) * wEl 0 * spDiag K (a, b) * (spDiag K (u, u⁻¹) * wEl 0)⁻¹
      = spDiag K (u, u⁻¹) * (wEl 0 * spDiag K (a, b) * (wEl 0)⁻¹) * (spDiag K (u, u⁻¹))⁻¹ := by
        group
    _ = spDiag K (u, u⁻¹) * spDiag K (b, a) * (spDiag K (u, u⁻¹))⁻¹ := by rw [h1]
    _ = spDiag K (b, a) := by rw [hD]; group

theorem Ft_n₂ {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) (hp : p.Prime) (h5 : 5 ≤ p)
    (hc : ∀ x y : E, x * y = y * x) :
    Ft p E (F.r₁ * F.r₀ * F.r₁⁻¹) = Subgroup.zpowers (F.dg (1, ω)) := by
  obtain ⟨k, hk, hkK, hkr⟩ := F.kfat₁.2.2.2.2
  have hkr' : conjAut E k hk = F.r₁ := hkr
  have hn : F.r₁ * F.r₀ * F.r₁⁻¹ = conjAut E k hk * F.r₀ * (conjAut E k hk)⁻¹ := by rw [hkr']
  rw [hn, ← Ft_conj hk, Ft_r₀ F hω hp h5]
  unfold conjBy
  rw [MonoidHom.map_zpowers]
  have := conj_dg_r₁ F hp h5 hc hk hkK hkr' ω 1
  show Subgroup.zpowers (k * F.dg (ω, 1) * k⁻¹) = _
  rw [this]

theorem Ft_n₁ {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) (hp : p.Prime) (h5 : 5 ≤ p)
    (hc : ∀ x y : E, x * y = y * x) :
    Ft p E (F.r₀ * F.r₁ * F.r₀⁻¹) = Subgroup.zpowers (F.dg (ω⁻¹, ω⁻¹)) := by
  obtain ⟨k, hk, hkK, hkr⟩ := F.kfat₀.2.2.2.2
  have hkr' : conjAut E k hk = F.r₀ := hkr
  have hn : F.r₀ * F.r₁ * F.r₀⁻¹ = conjAut E k hk * F.r₁ * (conjAut E k hk)⁻¹ := by rw [hkr']
  rw [hn, ← Ft_conj hk, Ft_r₁ F hω hp h5]
  unfold conjBy
  rw [MonoidHom.map_zpowers]
  have := conj_dg_r₀ F hp h5 hc hk hkK hkr' ω ω⁻¹
  show Subgroup.zpowers (k * F.dg (ω, ω⁻¹) * k⁻¹) = _
  rw [this]

end RFrame

end Base

section EvenFinal

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K) (D : Datum p E)

include F in
theorem exists_cube_root (hf : Even f) : ∃ ω : Kˣ, IsPrimitiveRoot ω 3 := by
  obtain ⟨m, hm⟩ := hf
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, F.card]
    have : 2 ^ f = 4 ^ m := by rw [hm, ← two_mul, pow_mul]; norm_num
    rw [this]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 m
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  refine ⟨ω, ?_⟩
  have := IsPrimitiveRoot.orderOf ω
  rwa [hω] at this

theorem dg_indep {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) (a b : ℤ)
    (h : F.dg (ω, 1) ^ a * F.dg (1, ω) ^ b = 1) : (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  rw [← map_zpow, ← map_zpow, ← map_mul, ← map_one F.dg] at h
  have h1 := F.dg_injective h
  have h2 : (ω, (1 : Kˣ)) ^ a * (1, ω) ^ b = (ω ^ a, ω ^ b) := by
    ext <;> simp
  rw [h2] at h1
  have := congrArg Prod.fst h1
  have := congrArg Prod.snd h1
  exact ⟨(hω.zpow_eq_one_iff_dvd a).1 (congrArg Prod.fst h1), (hω.zpow_eq_one_iff_dvd b).1 (congrArg Prod.snd h1)⟩

theorem nf7j_false_even (X : EFacts G p c E) (N : Norm F D) (hf : Even f) : False := by
  have hp := X.prime
  have h5 := X.five_le
  obtain ⟨ω, hω⟩ := exists_cube_root F hf
  have hc := X.comm
  set e : G := F.dg (ω, 1) with he
  set e' : G := F.dg (1, ω) with he'
  have he3 : e ^ 3 = 1 := by
    rw [he, ← map_pow]
    have : (ω, (1 : Kˣ)) ^ 3 = 1 := by simp [hω.pow_eq_one]
    rw [this, map_one]
  have he3' : e' ^ 3 = 1 := by
    rw [he', ← map_pow]
    have : ((1 : Kˣ), ω) ^ 3 = 1 := by simp [hω.pow_eq_one]
    rw [this, map_one]
  have hcomm : Commute e e' := by
    show F.dg (ω, 1) * F.dg (1, ω) = F.dg (1, ω) * F.dg (ω, 1)
    rw [← map_mul, ← map_mul, mul_comm]
  have n84 : phiE D (mk32 84) = Ft p E F.r₀ := by
    rw [← N.h1, phiE_unit, MulEquiv.symm_apply_apply]
    have hn' : D.ν * ((⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H) : MulAut E) = F.r₀ := D.ν_mul_ν_mul _
    rw [hn']
  have n167 : phiE D (mk32 167) = Ft p E F.r₁ := by
    rw [← N.h2, phiE_unit, MulEquiv.symm_apply_apply]
    have hn' : D.ν * ((⟨D.ν * F.r₁, a₂_mem F D⟩ : ↥D.H) : MulAut E) = F.r₁ := D.ν_mul_ν_mul _
    rw [hn']
  have n313 : phiE D (mk32 313) = Ft p E (F.r₁ * F.r₀ * F.r₁⁻¹) := by
    have e313 : ((D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ *
        D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ : GL (Fin 3) (ZMod 2)) : M32) = mk32 313 := by
      rw [Units.val_mul, Units.val_mul, N.h1, N.h2]
      decide +kernel
    rw [← e313, phiE_unit]
    have hsy : ((D.e.symm (D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ * D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ *
        D.e ⟨D.ν * F.r₁, a₂_mem F D⟩) : ↥D.H) : MulAut E) =
        (D.ν * F.r₁) * (D.ν * F.r₀) * (D.ν * F.r₁) := by
      simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
    rw [hsy, ν_triple, r₁_inv]
  have n458 : phiE D (mk32 458) = Ft p E (F.r₀ * F.r₁ * F.r₀⁻¹) := by
    have e458 : ((D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ *
        D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ : GL (Fin 3) (ZMod 2)) : M32) = mk32 458 := by
      rw [Units.val_mul, Units.val_mul, N.h1, N.h2]
      decide +kernel
    rw [← e458, phiE_unit]
    have hsy : ((D.e.symm (D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ * D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ *
        D.e ⟨D.ν * F.r₀, a₁_mem F D⟩) : ↥D.H) : MulAut E) =
        (D.ν * F.r₀) * (D.ν * F.r₁) * (D.ν * F.r₀) := by
      simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
    rw [hsy, ν_triple, r₀_inv]
  have hdg : ∀ a b : Kˣ, F.dg (a, b) = F.dg (a, 1) * F.dg (1, b) := by
    intro a b
    rw [← map_mul]
    simp
  have hinv1 : F.dg (ω⁻¹, 1) = (F.dg (ω, 1))⁻¹ := by
    rw [← map_inv]
    simp
  have hinv2 : F.dg (1, ω⁻¹) = (F.dg (1, ω))⁻¹ := by
    rw [← map_inv]
    simp
  have hbase : ∀ i < 4, phiE D (mk32 (baseNode i)) = Subgroup.zpowers (yEF e e' i) := by
    intro i hi
    interval_cases i
    · show phiE D (mk32 84) = _
      rw [n84, F.Ft_r₀ hω hp h5]
      simp [yEF, aT, bT, he]
    · show phiE D (mk32 167) = _
      rw [n167, F.Ft_r₁ hω hp h5]
      simp only [yEF, aT, bT, he, he']
      rw [hdg ω ω⁻¹, hinv2]
      simp
    · show phiE D (mk32 313) = _
      rw [n313, F.Ft_n₂ hω hp h5 hc]
      simp [yEF, aT, bT, he']
    · show phiE D (mk32 458) = _
      rw [n458, F.Ft_n₁ hω hp h5 hc]
      simp only [yEF, aT, bT, he, he']
      rw [hdg ω⁻¹ ω⁻¹, hinv1, hinv2]
      simp
  exact even_core (EvenHyp.of_indep e e' he3 he3' hcomm (fun a b h => dg_indep F hω a b h)
    (fun h hh => phiE_conj D hh) hbase)

end EvenFinal

end CFSG.RankThree.PartOne.NF7J
