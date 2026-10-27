module

public import CFSG.Quasithin.Background.HSp4A
public import CFSG.Quasithin.Background.HFF

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam
  coe_lam radical mem_unipotent_iff eq_sym2 tau_comm tau_injective lam_mul_tau_mul_inv
  unitri_mul_sym2_mul_transpose unitri)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauSp_bijective)
open CFSG.RankThree.SubgroupLists (spForm spE spForm_spE_left spForm_mulVec spForm_apply
  exists_mem_statedSp_mulVec_eq)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K]

theorem radD_eq_zero_of_comm [CharP K 2] {g g₀ : StatedSp 2 K} (hg : g ∈ radical K)
    (hg₀ : g₀ ∈ unipotent 2 K) (hlev : lev g₀ ≠ 0) (hc : g * g₀ = g₀ * g) : radD g = 0 := by
  obtain ⟨C', hC', rfl⟩ := hg
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hg₀
  have ha : lev (tau hC * lam a) = a := by
    rw [lev, coe_tau_mul_lam]
    simp [unitri]
  rw [ha] at hlev
  have h1 : tau hC' * lam a = lam a * tau hC' := by
    apply mul_left_cancel (a := tau hC)
    rw [← mul_assoc, ← tau_comm hC' hC, mul_assoc, hc, mul_assoc]
  have h2 : lam a * tau hC' * (lam a)⁻¹ = tau hC' := by
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  rw [lam_mul_tau_mul_inv] at h2
  have h3 := tau_injective _ hC' h2
  rw [eq_sym2 hC', unitri_mul_sym2_mul_transpose] at h3
  have h4 := congrFun (congrFun h3 0) 1
  simp only [sym2, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h4
  have h5 : radD (tau hC') = C' 1 1 := by
    rw [radD, coe_tau]
    simp
  rw [h5]
  have h6 : a * C' 1 1 = 0 := by linear_combination h4
  exact (mul_eq_zero.mp h6).resolve_left hlev

theorem card_le_cube [CharP K 2] [Finite K] (E : Subgroup (StatedSp 2 K))
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card K ^ 3 := by
  classical
  have hpg : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hE x x.2)⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
    have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hE _ (E.mul_mem hx hy))
    rw [← hxy, _root_.mul_inv_rev, hx', hy']
  obtain ⟨h, hh⟩ := exists_conj_le_unipotent hpg
  have hconj : ∀ x y : StatedSp 2 K, h⁻¹ * (x * y) * h = (h⁻¹ * x * h) * (h⁻¹ * y * h) :=
    fun x y => by group
  let φ : E →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (lev (h⁻¹ * x * h))
      map_one' := by
        have e : h⁻¹ * ((1 : E) : StatedSp 2 K) * h = 1 := by
          rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
        rw [e]
        simp [lev]
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, hconj, lev_mul (hh x x.2) (hh y y.2), ofAdd_add] }
  have hcard : Nat.card E ≤ Nat.card K * Nat.card φ.ker := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card φ.range ≤ Nat.card K := by
      calc Nat.card φ.range ≤ Nat.card (Multiplicative K) := Finite.card_subtype_le _
        _ = Nat.card K := rfl
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  have hR : ∀ x : E, x ∈ φ.ker → h⁻¹ * (x : StatedSp 2 K) * h ∈ radical K := by
    intro x hx
    have hx0 : lev (h⁻¹ * (x : StatedSp 2 K) * h) = 0 :=
      congrArg Multiplicative.toAdd ((MonoidHom.mem_ker).mp hx)
    exact (unipotent_facts (hh x x.2)).2.2 hx0
  have hinj : ∀ x y : E, x ∈ φ.ker → y ∈ φ.ker →
      radA (h⁻¹ * (x : StatedSp 2 K) * h) = radA (h⁻¹ * (y : StatedSp 2 K) * h) →
      radB (h⁻¹ * (x : StatedSp 2 K) * h) = radB (h⁻¹ * (y : StatedSp 2 K) * h) →
      radD (h⁻¹ * (x : StatedSp 2 K) * h) = radD (h⁻¹ * (y : StatedSp 2 K) * h) → x = y := by
    intro x y hx hy ha hb hd
    have h1 := radB_eq_of_radA_radD (hR x hx) (hR y hy) ha hb hd
    apply Subtype.ext
    have h2 := congrArg (fun z => h * z * h⁻¹) h1
    simpa [mul_assoc] using h2
  by_cases hall : ∀ x : E, x ∈ φ.ker
  · calc Nat.card E ≤ Nat.card (K × K × K) := by
          refine Nat.card_le_card_of_injective (fun x : E => (radA (h⁻¹ * (x : StatedSp 2 K) * h),
            radB (h⁻¹ * (x : StatedSp 2 K) * h), radD (h⁻¹ * (x : StatedSp 2 K) * h)))
            fun x y hxy => ?_
          simp only [Prod.mk.injEq] at hxy
          exact hinj x y (hall x) (hall y) hxy.1 hxy.2.1 hxy.2.2
      _ = Nat.card K ^ 3 := by rw [Nat.card_prod, Nat.card_prod]; ring
  · push Not at hall
    obtain ⟨x₀, hx₀⟩ := hall
    have hlev : lev (h⁻¹ * (x₀ : StatedSp 2 K) * h) ≠ 0 := fun h0 =>
      hx₀ ((MonoidHom.mem_ker).mpr (congrArg Multiplicative.ofAdd h0))
    have hd : ∀ x : E, x ∈ φ.ker → radD (h⁻¹ * (x : StatedSp 2 K) * h) = 0 := by
      intro x hx
      refine radD_eq_zero_of_comm (hR x hx) (hh x₀ x₀.2) hlev ?_
      rw [← hconj, ← hconj, hcomm x x.2 x₀ x₀.2]
    have hker : Nat.card φ.ker ≤ Nat.card K ^ 2 := by
      calc Nat.card φ.ker ≤ Nat.card (K × K) := by
            refine Nat.card_le_card_of_injective (fun x => (radA (h⁻¹ * ((x : E) :
              StatedSp 2 K) * h), radB (h⁻¹ * ((x : E) : StatedSp 2 K) * h))) fun x y hxy => ?_
            simp only [Prod.mk.injEq] at hxy
            exact Subtype.ext (hinj x y x.2 y.2 hxy.1 hxy.2 (by rw [hd x x.2, hd y y.2]))
        _ = Nat.card K ^ 2 := by rw [Nat.card_prod]; ring
    calc Nat.card E ≤ Nat.card K * Nat.card φ.ker := hcard
      _ ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul_left _ hker
      _ = Nat.card K ^ 3 := by ring

theorem exists_conj_upSp_of_three {B : StatedSp 2 K} (hB : B ≠ 1)
    (h3 : 3 ≤ Module.finrank K (fixLin (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))) :
    ∃ (hS : StatedSp 2 K) (l : K), l ≠ 0 ∧ hS⁻¹ * B * hS = upSp (sym2_transpose l 0 0) := by
  classical
  set M := ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  let N : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) := Matrix.toLin' M - LinearMap.id
  have hNv : ∀ v, N v = M *ᵥ v - v := fun v => by simp [N]
  have hker : LinearMap.ker N = fixLin M := by
    ext v
    rw [LinearMap.mem_ker, hNv, sub_eq_zero, mem_fixLin]
  have hrank : Module.finrank K (LinearMap.range N) ≤ 1 := by
    have := LinearMap.finrank_range_add_finrank_ker N
    rw [hker, Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨c₀, hc₀⟩ := finrank_le_one_iff.mp hrank
  set c : Fin 2 ⊕ Fin 2 → K := (c₀ : Fin 2 ⊕ Fin 2 → K) with hc
  have hNc : ∀ v, ∃ t : K, M *ᵥ v - v = t • c := by
    intro v
    obtain ⟨t, ht⟩ := hc₀ ⟨N v, LinearMap.mem_range_self N v⟩
    refine ⟨t, ?_⟩
    have := congrArg Subtype.val ht
    rw [← hNv]
    exact this.symm
  have hc0 : c ≠ 0 := by
    intro h0
    apply hB
    refine eq_one_of_forall_mulVec fun v => ?_
    obtain ⟨t, ht⟩ := hNc v
    rw [h0, smul_zero, sub_eq_zero] at ht
    exact ht
  have hE : (spE : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h ι₀
    simp [spE] at this
  obtain ⟨h, hh, hhc⟩ := exists_mem_statedSp_mulVec_eq hE hc0
  set hS : StatedSp 2 K := ⟨h, hh⟩ with hhS
  set B' := hS⁻¹ * B * hS with hB'
  have hB'M : ((B' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M *
        (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [hB']
    rfl
  have hhinv : ∀ v, ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinvc : ((h⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ c =
      spE := by
    rw [← hhc, hhinv]
  have hB'sub : ∀ v, ∃ t : K, ((B' : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v - v = t • spE := by
    intro v
    obtain ⟨t, ht⟩ := hNc ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
    refine ⟨t, ?_⟩
    rw [hB'M, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have e : M *ᵥ ((h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + t • c :=
      (sub_eq_iff_eq_add'.mp ht)
    rw [e, Matrix.mulVec_add, hhinv, Matrix.mulVec_smul, hinvc, add_sub_cancel_left]
  obtain ⟨l, hl⟩ := eq_upSp_of_sub_mem hB'sub
  refine ⟨hS, l, fun h0 => hB ?_, hl⟩
  have h1 : B' = 1 := by
    rw [hl, h0]
    refine eq_one_of_forall_mulVec fun v => ?_
    rw [coe_upSp, up_mulVec]
    simp
  have hBe : B = hS * B' * hS⁻¹ := by rw [hB']; group
  rw [hBe, h1, mul_one, mul_inv_cancel]

theorem eq_upSp_of_fix {g : StatedSp 2 K}
    (h0 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single ι₀ 1 = Pi.single ι₀ 1)
    (h1 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single ι₁ 1 = Pi.single ι₁ 1)
    (h3 : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single ι₃ 1 = Pi.single ι₃ 1) :
    ∃ l : K, g = upSp (sym2_transpose l 0 0) := by
  set M := ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hf : ∀ u v, spForm 2 K (M *ᵥ u) (M *ᵥ v) = spForm 2 K u v := spForm_mulVec g.2
  have hx2 : M ι₂ ι₂ = 1 := by
    have := hf (Pi.single ι₀ 1) (Pi.single ι₂ 1)
    rw [h0] at this
    simpa [spForm_apply, Pi.single_apply] using this
  have hx3 : M ι₃ ι₂ = 0 := by
    have := hf (Pi.single ι₁ 1) (Pi.single ι₂ 1)
    rw [h1] at this
    simpa [spForm_apply, Pi.single_apply] using this
  have hx1 : M ι₁ ι₂ = 0 := by
    have := hf (Pi.single ι₃ 1) (Pi.single ι₂ 1)
    rw [h3] at this
    simpa [spForm_apply, Pi.single_apply] using this
  apply eq_upSp_of_sub_mem
  intro v
  refine ⟨v ι₂ * M ι₀ ι₂, ?_⟩
  have hv : v = v ι₀ • Pi.single ι₀ 1 + v ι₁ • Pi.single ι₁ 1 + v ι₂ • Pi.single ι₂ 1 +
      v ι₃ • Pi.single ι₃ 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  have hMv : M *ᵥ v = v ι₀ • Pi.single ι₀ 1 + v ι₁ • Pi.single ι₁ 1 +
      v ι₂ • (M *ᵥ Pi.single ι₂ 1) + v ι₃ • Pi.single ι₃ 1 := by
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, h0, h1, h3]
  rw [hMv]
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [spE, hx1, hx2, hx3]

omit [Field K] in
theorem mulVec_conj {K : Type} [Field K] (h g : StatedSp 2 K) (w : Fin 2 ⊕ Fin 2 → K) :
    (((h⁻¹ * g * h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w =
      (((h : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          (((h : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rfl

theorem card_le_of_three [Finite K] {E : Subgroup (StatedSp 2 K)} {t : StatedSp 2 K}
    (ht1 : t ≠ 1) (h3 : 3 ≤ Module.finrank K (fixLin (((t : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))))
    (hE : ∀ g ∈ E, ∀ v, ((t : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      v = v → ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v) :
    Nat.card E ≤ Nat.card K := by
  obtain ⟨hS, l, -, hl⟩ := exists_conj_upSp_of_three ht1 h3
  have hMS : ∀ w, (((hS : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (((hS : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hMS' : ∀ w, ((hS : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((((hS : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hW : ∀ w : Fin 2 ⊕ Fin 2 → K, w ι₂ = 0 →
      ((t : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((hS : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) =
        ((hS : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w := by
    intro w hw
    have e1 : (((hS⁻¹ * t * hS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w = w := by
      rw [hl, coe_upSp, up_mulVec]
      simp [hw]
    rw [mulVec_conj] at e1
    have := congrArg (fun z => ((hS : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ z) e1
    simp only [hMS'] at this
    exact this
  have hfix : ∀ g ∈ E, ∃ c : K, hS⁻¹ * g * hS = upSp (sym2_transpose c 0 0) := by
    intro g hg
    have key : ∀ w : Fin 2 ⊕ Fin 2 → K, w ι₂ = 0 →
        (((hS⁻¹ * g * hS : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w = w := by
      intro w hw
      rw [mulVec_conj, hE g hg _ (hW w hw), hMS]
    exact eq_upSp_of_fix (key _ (by simp)) (key _ (by simp)) (key _ (by simp))
  choose c hc using hfix
  refine Nat.card_le_card_of_injective (fun g : E => c g g.2) fun g g' hgg => ?_
  have h1 : hS⁻¹ * (g : StatedSp 2 K) * hS = hS⁻¹ * g' * hS := by
    rw [hc g g.2, hc g' g'.2]
    simp only at hgg
    rw [hgg]
  apply Subtype.ext
  simpa using h1

theorem card_fix_sq_le [Finite K] {a : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} {σ : K ≃+* K}
    (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K) (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ∈ W ∧ toAddMap a v = v} ^ 2 ≤ Nat.card W := by
  obtain ⟨μ, hμ⟩ : ∃ μ : K, σ μ ≠ μ := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  rw [sq, ← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1 + μ • p.2.1,
    W.add_mem p.1.2.1 (W.smul_mem μ p.2.2.1)⟩) ?_
  rintro ⟨⟨u, hu, hau⟩, ⟨v, hv, hav⟩⟩ ⟨⟨u', hu', hau'⟩, ⟨v', hv', hav'⟩⟩ h
  have h1 : u + μ • v = u' + μ • v' := congrArg Subtype.val h
  have h2 : u + σ μ • v = u' + σ μ • v' := by
    have := congrArg (toAddMap a) h1
    rwa [toAddMap_add, toAddMap_add, ha, ha, hau, hav, hau', hav'] at this
  have hvv : v = v' := by
    funext i
    have e1 := congrFun h1 i
    have e2 := congrFun h2 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : (μ - σ μ) * (v i - v' i) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hμ
    · exact sub_eq_zero.mp h0
  have huu : u = u' := by
    rw [hvv] at h1
    exact add_right_cancel h1
  subst hvv
  subst huu
  rfl

@[expose] def fixSp (E : Subgroup (StatedSp 2 K)) : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
  ⨅ g ∈ E, fixLin (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))

theorem mem_fixSp {E : Subgroup (StatedSp 2 K)} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ fixSp E ↔ ∀ g ∈ E,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v := by
  simp only [fixSp, Submodule.mem_iInf, mem_fixLin]

theorem finrank_fixSp_le {E : Subgroup (StatedSp 2 K)} {t : StatedSp 2 K} (ht : t ∈ E)
    (ht1 : t ≠ 1) : Module.finrank K (fixSp E) ≤ 3 :=
  (Submodule.finrank_mono fun _ hv => mem_fixSp.mp hv t ht).trans (finrank_fixLin_le_three ht1)

variable [CharP K 2] [Finite K]

theorem card_fixV_le_comap (A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
    Nat.card ↥(fixV A) ≤ Nat.card (fixSp (A.comap (pairHom (StatedSp 2 K) tauSp))) *
      Nat.card (fixSp ((A.comap (pairHom (StatedSp 2 K) tauSp)).map tauSp)) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun v =>
    (⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1, mem_fixSp.mpr fun g hg => ?_⟩,
      ⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).2, mem_fixSp.mpr fun g hg => ?_⟩))
    fun v w hvw => ?_
  · have := v.2 _ hg
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.1) this
  · obtain ⟨g₀, hg₀, rfl⟩ := hg
    have := v.2 _ hg₀
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.2) this
  · have h1 := congrArg (fun p => (p.1 : Fin 2 ⊕ Fin 2 → K)) hvw
    have h2 := congrArg (fun p => (p.2 : Fin 2 ⊕ Fin 2 → K)) hvw
    simp only at h1 h2
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h1)
      (Multiplicative.toAdd.injective h2))

omit [Finite K] in
theorem card_comap_pairHom {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))}
    (hA : A ≤ pairSp K) : Nat.card (A.comap (pairHom (StatedSp 2 K) tauSp)) = Nat.card A := by
  have hinj : Function.Injective (pairHom (StatedSp 2 K) tauSp) := by
    rw [injective_iff_map_eq_one]
    intro B hB
    rw [pairHom_apply] at hB
    have := (pairAut_injective (hB.trans pairAut_one.symm)).1
    exact natAut_injective (StatedSp 2 K) (by rw [this, map_one])
  have hmap : (A.comap (pairHom (StatedSp 2 K) tauSp)).map (pairHom (StatedSp 2 K) tauSp) = A :=
    Subgroup.map_comap_eq_self hA
  conv_rhs => rw [← hmap]
  exact (Subgroup.card_map_of_injective hinj).symm

omit [CharP K 2] [Finite K] in
theorem card_fixSp (E : Subgroup (StatedSp 2 K)) :
    Nat.card (fixSp E) = Nat.card K ^ Module.finrank K (fixSp E) :=
  Module.natCard_eq_pow_finrank (K := K) (V := fixSp E)

theorem card_mul_le_of_le_pairSp {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hA : A ≤ pairSp K)
    (hsq : ∀ x ∈ A, x * x = 1) (hA1 : A ≠ ⊥) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  set E := A.comap (pairHom (StatedSp 2 K) tauSp) with hE
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    apply natAut_injective (StatedSp 2 K)
    have := hsq _ hx
    rw [pairHom_apply, pairAut_mul] at this
    rw [map_mul, map_one]
    exact (pairAut_injective (this.trans pairAut_one.symm)).1
  have hτinj : Function.Injective (tauSp : StatedSp 2 K →* StatedSp 2 K) := tauSp_bijective.1
  obtain ⟨t, htE, ht1⟩ : ∃ t ∈ E, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hA1
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨B, rfl⟩ := hA hx
    rw [hcon B hx, map_one]
    exact Subgroup.one_mem _
  have hτt1 : tauSp t ≠ 1 := fun h => ht1 (hτinj (by rw [h, map_one]))
  have hd₁ := finrank_fixSp_le htE ht1
  have hd₂ := finrank_fixSp_le (E := E.map tauSp) ⟨t, htE, rfl⟩ hτt1
  have hcardE : Nat.card E = Nat.card A := card_comap_pairHom hA
  have hcardτE : Nat.card (E.map tauSp) = Nat.card E := Subgroup.card_map_of_injective hτinj
  have hfix := card_fixV_le_comap A
  rw [← hE, card_fixSp, card_fixSp] at hfix
  have hEcube := card_le_cube E hEsq
  have hhyp : ∀ (F : Subgroup (StatedSp 2 K)) (s : StatedSp 2 K), s ∈ F → s ≠ 1 →
      Module.finrank K (fixSp F) = 3 → Nat.card F ≤ Nat.card K := by
    intro F s hs hs1 h3
    have hle : fixSp F ≤ fixLin (((s : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := fun v hv => mem_fixSp.mp hv s hs
    have heq : fixSp F = fixLin (((s : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :=
      Submodule.eq_of_le_of_finrank_le hle (by rw [h3]; exact finrank_fixLin_le_three hs1)
    refine card_le_of_three hs1 (by rw [← heq, h3]) fun g hg v hv => ?_
    have hv' : v ∈ fixSp F := by rw [heq]; exact hv
    exact mem_fixSp.mp hv' g hg
  have hq : 0 < Nat.card K := Nat.card_pos
  rw [← hcardE]
  rcases Nat.lt_or_ge (Module.finrank K (fixSp E)) 3 with h1 | h1
  · rcases Nat.lt_or_ge (Module.finrank K (fixSp (E.map tauSp))) 3 with h2 | h2
    ·
      have hC : Nat.card K ^ Module.finrank K (fixSp E) *
          Nat.card K ^ Module.finrank K (fixSp (E.map tauSp)) ≤ Nat.card K ^ 4 := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hq (by omega)
      calc 4 * Nat.card E * Nat.card ↥(fixV A)
          ≤ 4 * Nat.card K ^ 3 * Nat.card K ^ 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 4 hEcube) (hfix.trans hC)
        _ = 4 * Nat.card K ^ 7 := by ring
        _ ≤ Nat.card K * Nat.card K ^ 7 := Nat.mul_le_mul_right _ hq4
        _ = Nat.card K ^ 8 := by ring
    ·
      have hF := hhyp (E.map tauSp) (tauSp t) ⟨t, htE, rfl⟩ hτt1 (by omega)
      rw [hcardτE] at hF
      have hC : Nat.card K ^ Module.finrank K (fixSp E) *
          Nat.card K ^ Module.finrank K (fixSp (E.map tauSp)) ≤ Nat.card K ^ 6 := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hq (by omega)
      calc 4 * Nat.card E * Nat.card ↥(fixV A)
          ≤ 4 * Nat.card K * Nat.card K ^ 6 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 4 hF) (hfix.trans hC)
        _ = 4 * Nat.card K ^ 7 := by ring
        _ ≤ Nat.card K * Nat.card K ^ 7 := Nat.mul_le_mul_right _ hq4
        _ = Nat.card K ^ 8 := by ring
  ·
    have hF := hhyp E t htE ht1 (by omega)
    have hC : Nat.card K ^ Module.finrank K (fixSp E) *
        Nat.card K ^ Module.finrank K (fixSp (E.map tauSp)) ≤ Nat.card K ^ 6 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hq (by omega)
    calc 4 * Nat.card E * Nat.card ↥(fixV A)
        ≤ 4 * Nat.card K * Nat.card K ^ 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hF) (hfix.trans hC)
      _ = 4 * Nat.card K ^ 7 := by ring
      _ ≤ Nat.card K * Nat.card K ^ 7 := Nat.mul_le_mul_right _ hq4
      _ = Nat.card K ^ 8 := by ring

theorem exists_isSemilinear_pair {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hx : pairAut a b ∈ pairNormSp K) : ∃ σ : K ≃+* K, IsSemilinear a σ ∧ IsSemilinear b σ := by
  obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp hx
  refine ⟨σ, fun c v => ?_, fun c v => ?_⟩
  · rw [ha, ha]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
      smul_comm]
  · rw [hb, hb]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
      smul_comm]

omit [CharP K 2] in
theorem card_fixV_le_of_mem {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))}
    {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (hab : pairAut a b ∈ A)
    (W₁ W₂ : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hW₁ : ∀ v ∈ fixV A, Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1 ∈ W₁)
    (hW₂ : ∀ v ∈ fixV A, Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).2 ∈ W₂) :
    Nat.card ↥(fixV A) ≤ Nat.card {v : Fin 2 ⊕ Fin 2 → K // v ∈ W₁ ∧ toAddMap a v = v} *
      Nat.card {w : Fin 2 ⊕ Fin 2 → K // w ∈ W₂ ∧ toAddMap b w = w} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun v =>
    (⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1, hW₁ v v.2, ?_⟩,
      ⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).2, hW₂ v v.2, ?_⟩)) fun v w hvw => ?_
  · have := v.2 _ hab
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.1) this
  · have := v.2 _ hab
    exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.2) this
  · have h1 := congrArg (fun p => (p.1 : Fin 2 ⊕ Fin 2 → K)) hvw
    have h2 := congrArg (fun p => (p.2 : Fin 2 ⊕ Fin 2 → K)) hvw
    simp only at h1 h2
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h1)
      (Multiplicative.toAdd.injective h2))

omit [CharP K 2] in
theorem two_mul_le_of_mul_le {n c : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hc : c * Nat.card K ≤ 2 ^ (2 * n - 1)) : 2 * c ≤ Nat.card K := by
  have hq : 0 < Nat.card K := Nat.card_pos
  have hqq : Nat.card K * Nat.card K = 2 * 2 ^ (2 * n - 1) := by
    rw [hK, ← pow_add, ← pow_succ']
    congr 1
    omega
  have : 2 * c * Nat.card K ≤ Nat.card K * Nat.card K := by
    rw [hqq, mul_assoc]
    exact Nat.mul_le_mul_left 2 hc
  exact Nat.le_of_mul_le_mul_right this hq

omit [Finite K] in
theorem comap_sq {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hsq : ∀ x ∈ A, x * x = 1) :
    ∀ x ∈ A.comap (pairHom (StatedSp 2 K) tauSp), x * x = 1 := by
  intro x hx
  apply natAut_injective (StatedSp 2 K)
  have := hsq _ hx
  rw [pairHom_apply, pairAut_mul] at this
  rw [map_mul, map_one]
  exact (pairAut_injective (this.trans pairAut_one.symm)).1

theorem card_mul_le_of_field {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hsq : ∀ x ∈ A, x * x = 1)
    (hAsub : ∀ x ∈ A, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K)
    {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (hab : pairAut a b ∈ A)
    (hlin : ¬ IsSemilinear a (RingEquiv.refl K)) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  obtain ⟨c, hcA, hc1, -⟩ := exists_card_le (by omega) hK hAN hsq hAsub
  obtain ⟨σ, hsla, hslb⟩ := exists_isSemilinear_pair (hAN hab)
  have hσ : σ ≠ RingEquiv.refl K := fun h => hlin (h ▸ hsla)
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2c := two_mul_le_of_mul_le (by omega) hK hc1
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hsqrt : ∀ {x k : ℕ}, x ^ 2 ≤ Nat.card K ^ (2 * k) → x ≤ Nat.card K ^ k := by
    intro x k hx
    have e : Nat.card K ^ (2 * k) = (Nat.card K ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e] at hx
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp hx
  by_cases hH1 : A ⊓ pairSp K = ⊥
  ·
    have hA : Nat.card A ≤ c := by
      have := hcA
      rwa [hH1, Subgroup.card_bot, mul_one] at this
    have htop : Nat.card (⊤ : Submodule K (Fin 2 ⊕ Fin 2 → K)) = Nat.card K ^ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := K), finrank_top, Module.finrank_fintype_fun_eq_card]
      simp
    have hfix := card_fixV_le_of_mem hab ⊤ ⊤ (fun _ _ => Submodule.mem_top)
      (fun _ _ => Submodule.mem_top)
    have h1 := hsqrt (k := 2) ((card_fix_sq_le hsla hσ ⊤).trans htop.le)
    have h2 := hsqrt (k := 2) ((card_fix_sq_le hslb hσ ⊤).trans htop.le)
    calc 4 * Nat.card A * Nat.card ↥(fixV A)
        ≤ 4 * c * (Nat.card K ^ 2 * Nat.card K ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 hA) (hfix.trans (Nat.mul_le_mul h1 h2))
      _ = 2 * (2 * c) * Nat.card K ^ 4 := by ring
      _ ≤ 2 * Nat.card K * Nat.card K ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2c)
      _ ≤ Nat.card K ^ 3 * Nat.card K * Nat.card K ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (le_trans (by norm_num) (le_trans hq4 (Nat.le_self_pow (by norm_num) _))))
      _ = Nat.card K ^ 8 := by ring
  ·
    obtain ⟨t, htH, ht1⟩ : ∃ t ∈ A ⊓ pairSp K, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hH1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨B, hB⟩ := htH.2
    have hB1 : B ≠ 1 := fun h => ht1 (by rw [← hB, h, map_one])
    have hτB1 : tauSp B ≠ 1 := fun h => hB1 (tauSp_bijective.1 (by rw [h, map_one]))
    have hBA : pairHom (StatedSp 2 K) tauSp B ∈ A := hB ▸ htH.1
    have hfix := card_fixV_le_of_mem hab
      (fixLin (((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))
      (fixLin ((((tauSp B : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))
      (fun v hv => congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.1)
        (hv _ hBA))
      (fun v hv => congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.2)
        (hv _ hBA))
    have hW₁ : Nat.card (fixLin (((B : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) ≤ Nat.card K ^ 3 := by
      rw [Module.natCard_eq_pow_finrank (K := K)]
      exact Nat.pow_le_pow_right hq (finrank_fixLin_le_three hB1)
    have hW₂ : Nat.card (fixLin ((((tauSp B : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) ≤ Nat.card K ^ 3 := by
      rw [Module.natCard_eq_pow_finrank (K := K)]
      exact Nat.pow_le_pow_right hq (finrank_fixLin_le_three hτB1)
    have hC : Nat.card ↥(fixV A) ≤ Nat.card K ^ 3 := by
      refine hfix.trans (hsqrt (k := 3) ?_)
      rw [mul_pow]
      calc _ ≤ Nat.card K ^ 3 * Nat.card K ^ 3 :=
            Nat.mul_le_mul ((card_fix_sq_le hsla hσ _).trans hW₁)
              ((card_fix_sq_le hslb hσ _).trans hW₂)
        _ = Nat.card K ^ (2 * 3) := by ring
    have hH : Nat.card ↥(A ⊓ pairSp K) ≤ Nat.card K ^ 3 := by
      rw [← card_comap_pairHom (inf_le_right : A ⊓ pairSp K ≤ pairSp K)]
      exact card_le_cube _ (comap_sq fun x hx => hsq x hx.1)
    calc 4 * Nat.card A * Nat.card ↥(fixV A)
        ≤ 4 * (c * Nat.card K ^ 3) * Nat.card K ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 (hcA.trans (Nat.mul_le_mul_left c hH))) hC
      _ = 2 * (2 * c) * Nat.card K ^ 6 := by ring
      _ ≤ 2 * Nat.card K * Nat.card K ^ 6 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h2c)
      _ ≤ Nat.card K * Nat.card K * Nat.card K ^ 6 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = Nat.card K ^ 8 := by ring

theorem card_mul_le_of_swap {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hsq : ∀ x ∈ A, x * x = 1) {y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (hyA : y ∈ A)
    (hy : (V₁ (Fin 2 ⊕ Fin 2) K).map y.toMonoidHom ≠ V₁ (Fin 2 ⊕ Fin 2) K) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  have hy2 := (map_V₁_eq_or (hAN hyA)).resolve_left hy
  set A₀ := A ⊓ pairSub (Fin 2 ⊕ Fin 2) K with hA₀
  have hmem : ∀ x ∈ A, x ∈ pairSub (Fin 2 ⊕ Fin 2) K ↔
      (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
    intro x hx
    constructor
    · intro hxs
      obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hxs
      exact map_V₁_pairAut a b
    · intro h1
      obtain ⟨a, b, rfl⟩ := exists_pairAut (hAN hx) h1
      exact pairAut_mem_pairSub a b
  have hidx : Nat.card A ≤ 2 * Nat.card A₀ := by
    refine card_le_two_mul_of_mul_mem inf_le_left fun x hx z hz hx' hz' => ⟨A.mul_mem hx hz, ?_⟩
    have hx1 : x ∉ pairSub (Fin 2 ⊕ Fin 2) K := fun h => hx' ⟨hx, h⟩
    have hz1 : z ∉ pairSub (Fin 2 ⊕ Fin 2) K := fun h => hz' ⟨hz, h⟩
    have hxV := (map_V₁_eq_or (hAN hx)).resolve_left fun h => hx1 ((hmem x hx).mpr h)
    have hzV := (map_V₁_eq_or (hAN hz)).resolve_left fun h => hz1 ((hmem z hz).mpr h)
    have hxV2 : (V₂ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
      rw [← hxV, Subgroup.map_map]
      have : x.toMonoidHom.comp x.toMonoidHom = MonoidHom.id _ := by
        refine MonoidHom.ext fun v => ?_
        change (x * x) v = v
        rw [hsq x hx]
        rfl
      rw [this, Subgroup.map_id]
    refine (hmem _ (A.mul_mem hx hz)).mpr ?_
    have : (x * z).toMonoidHom = x.toMonoidHom.comp z.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map, hzV, hxV2]
  have hA₀N : A₀ ≤ pairNormSp K := inf_le_left.trans hAN
  have hA₀sq : ∀ x ∈ A₀, x * x = 1 := fun x hx => hsq x hx.1
  have hA₀sub : ∀ x ∈ A₀, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K :=
    fun x hx => (hmem x hx.1).mp hx.2
  obtain ⟨c, hcA, hc1, -⟩ := exists_card_le (by omega) hK hA₀N hA₀sq hA₀sub
  set E := (A₀ ⊓ pairSp K).comap (pairHom (StatedSp 2 K) tauSp) with hE
  have hfix : Nat.card ↥(fixV A) ≤ Nat.card (fixSp E) := by
    refine Nat.card_le_card_of_injective (fun v =>
      ⟨Multiplicative.toAdd (v : PairMod (Fin 2 ⊕ Fin 2) K).1, mem_fixSp.mpr fun g hg => ?_⟩)
      fun v w hvw => ?_
    · have := v.2 _ hg.1.1
      exact congrArg (fun p : PairMod (Fin 2 ⊕ Fin 2) K => Multiplicative.toAdd p.1) this
    · have h1 : (v : PairMod (Fin 2 ⊕ Fin 2) K).1 = (w : PairMod (Fin 2 ⊕ Fin 2) K).1 :=
        Multiplicative.toAdd.injective (congrArg Subtype.val hvw)
      set z := (v : PairMod (Fin 2 ⊕ Fin 2) K) * (w : PairMod (Fin 2 ⊕ Fin 2) K)⁻¹ with hz
      have hzV : z ∈ V₂ (Fin 2 ⊕ Fin 2) K := by
        rw [mem_V₂]
        change (v : PairMod (Fin 2 ⊕ Fin 2) K).1 * ((w : PairMod (Fin 2 ⊕ Fin 2) K).1)⁻¹ = 1
        rw [h1, mul_inv_cancel]
      have hzy : y z = z := by
        rw [hz, map_mul, map_inv, v.2 y hyA, w.2 y hyA]
      have hz1 : z = 1 := by
        obtain ⟨u, hu, hyu⟩ : z ∈ (V₁ (Fin 2 ⊕ Fin 2) K).map y.toMonoidHom := by
          rw [hy2]
          exact hzV
        have hyy : y (y u) = u := by
          change (y * y) u = u
          rw [hsq y hyA]
          rfl
        have hzu : z = u := by
          have h2 : y z = u := by rw [← hyu]; exact hyy
          rw [← h2, hzy]
        exact eq_one_of_fix_of_map_V₂ hy2 (hzu ▸ hu) hzy
      exact Subtype.ext (by rw [← mul_inv_eq_one, ← hz, hz1])
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2c := two_mul_le_of_mul_le (by omega) hK hc1
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hHc : Nat.card ↥(A₀ ⊓ pairSp K) = Nat.card E :=
    (card_comap_pairHom (inf_le_right : A₀ ⊓ pairSp K ≤ pairSp K)).symm
  have hEc : Nat.card E ≤ Nat.card K ^ 3 := card_le_cube E (comap_sq fun x hx => hA₀sq x hx.1)
  have hbound : 4 * Nat.card A * Nat.card ↥(fixV A) ≤
      4 * ((2 * c) * Nat.card E) * Nat.card (fixSp E) := by
    calc 4 * Nat.card A * Nat.card ↥(fixV A)
        ≤ 4 * (2 * (c * Nat.card ↥(A₀ ⊓ pairSp K))) * Nat.card (fixSp E) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 (hidx.trans (Nat.mul_le_mul_left 2 hcA))) hfix
      _ = 4 * ((2 * c) * Nat.card E) * Nat.card (fixSp E) := by rw [hHc]; ring
  by_cases hE1 : ∃ t ∈ E, t ≠ 1
  · obtain ⟨t, htE, ht1⟩ := hE1
    have hC : Nat.card (fixSp E) ≤ Nat.card K ^ 3 := by
      rw [card_fixSp]
      exact Nat.pow_le_pow_right hq (finrank_fixSp_le htE ht1)
    calc 4 * Nat.card A * Nat.card ↥(fixV A)
        ≤ 4 * ((2 * c) * Nat.card E) * Nat.card (fixSp E) := hbound
      _ ≤ 4 * (Nat.card K * Nat.card K ^ 3) * Nat.card K ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.mul_le_mul h2c hEc)) hC
      _ = 4 * Nat.card K ^ 7 := by ring
      _ ≤ Nat.card K * Nat.card K ^ 7 := Nat.mul_le_mul_right _ hq4
      _ = Nat.card K ^ 8 := by ring
  · push Not at hE1
    have hE1' : Nat.card E = 1 := by
      rw [(Subgroup.eq_bot_iff_forall E).mpr hE1, Subgroup.card_bot]
    have hC : Nat.card (fixSp E) ≤ Nat.card K ^ 4 := by
      rw [card_fixSp]
      refine Nat.pow_le_pow_right hq ((Submodule.finrank_le _).trans ?_)
      rw [Module.finrank_fintype_fun_eq_card]
      simp
    calc 4 * Nat.card A * Nat.card ↥(fixV A)
        ≤ 4 * ((2 * c) * Nat.card E) * Nat.card (fixSp E) := hbound
      _ ≤ 4 * (Nat.card K * 1) * Nat.card K ^ 4 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.mul_le_mul h2c hE1'.le)) hC
      _ = 4 * Nat.card K ^ 5 := by ring
      _ ≤ Nat.card K ^ 3 * Nat.card K ^ 5 :=
          Nat.mul_le_mul_right _ (le_trans hq4 (Nat.le_self_pow (by norm_num) _))
      _ = Nat.card K ^ 8 := by ring

theorem four_mul_card_mul_card_fixV_le_two {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA2.2 x hx
  by_cases hsw : ∃ y ∈ A, (V₁ (Fin 2 ⊕ Fin 2) K).map y.toMonoidHom ≠ V₁ (Fin 2 ⊕ Fin 2) K
  · obtain ⟨y, hyA, hy⟩ := hsw
    exact card_mul_le_of_swap hn hK hAN hsq hyA hy
  · push Not at hsw
    by_cases hl : ∃ a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), pairAut a b ∈ A ∧
        ¬ IsSemilinear a (RingEquiv.refl K)
    · obtain ⟨a, b, hab, hlin⟩ := hl
      exact card_mul_le_of_field hn hK hAN hsq hsw hab hlin
    · push Not at hl
      have hA : A ≤ pairSp K := by
        intro x hx
        obtain ⟨a, b, rfl⟩ := exists_pairAut (hAN hx) (hsw x hx)
        obtain ⟨B, -, hB⟩ := eq_pairHom_of_linear (hAN hx) (hsq _ hx) (hl a b hx)
        rw [hB]
        exact pairHom_mem_pairImg _ _ B
      exact card_mul_le_of_le_pairSp hn hK hA hsq hA1

theorem two_mul_card_fixV_le {V : Type*} [CommGroup V] [Finite V] {A B : Subgroup (MulAut V)}
    (hBA : B ≤ A) (hne : fixV B ≠ fixV A) : 2 * Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV B) := by
  have hle : fixV A ≤ fixV B := fun _ hv x hx => hv x (hBA hx)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne (Subgroup.eq_of_le_of_card_ge hle hk.le).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact Nat.card_pos.ne' hk
  rw [hk, mul_comm 2]
  exact Nat.mul_le_mul_left _ (by omega)

theorem four_mul_card_mul_card_fixV_le_one (hK : Nat.card K = 2 ^ 1)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ 8 := by
    rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      ← pow_add]
  suffices H : ∀ k : ℕ, ∀ A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), Nat.card A ≤ k →
      A ≤ pairNormSp K → IsElemAbelian2 A → A ≠ ⊥ →
        4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 from
    H _ A le_rfl hAN hA2 hA1
  intro k
  induction k with
  | zero =>
    intro A hk _ _ _
    have := Nat.card_pos (α := A)
    omega
  | succ k ih =>
    intro A hk hAN hA2 hA1
    have hpg := E3.isPGroup_of_isElemAbelian2 hA2
    obtain ⟨t, htA, ht1⟩ : ∃ t ∈ A, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hA1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    by_cases h2 : Nat.card A ≤ 2
    ·
      have ht2 : orderOf t = 2 := orderOf_eq_prime (hA2.2 t htA) ht1
      have hm := le_rkIdx_fixV_of_involution le_rfl hK (hAN htA) ht2
      have hle : fixV A ≤ fixV (Subgroup.zpowers t) :=
        fun _ hv x hx => hv x ((Subgroup.zpowers_le).mpr htA hx)
      have hC : Nat.card ↥(fixV A) ≤ 2 ^ 5 :=
        (Subgroup.card_le_of_le hle).trans
          ((SL3Pair.card_le_of_le_rkIdx hV _ hm).trans (Nat.pow_le_pow_right (by norm_num)
            (by omega)))
      rw [hK]
      calc 4 * Nat.card A * Nat.card ↥(fixV A) ≤ 4 * 2 * 2 ^ 5 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 4 h2) hC
        _ = (2 ^ 1) ^ 8 := by norm_num
    ·
      have hnot := not_mem_aSet le_rfl hK (le_refl (pairNormSp K)) A
      have hex : ∃ B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), B ≤ A ∧
          E3.mQuot A B < 2 ∧ fixV B ≠ fixV A := by
        by_contra hcon
        push Not at hcon
        exact hnot ⟨hAN, hA1, hA2, fun B hBA hm => hcon B hBA (by omega)⟩
      obtain ⟨B, hBA, hmB, hne⟩ := hex
      have hm0 : E3.mQuot A B ≠ 0 := fun h0 =>
        hne (by rw [(E3.mQuot_eq_zero_iff hpg hBA).mp h0])
      have hm1 : E3.mQuot A B = 1 := by omega
      have hAB : Nat.card A = 2 * Nat.card B := by
        rw [E3.card_eq_two_pow_mul hpg hBA, hm1, pow_one]
      have hB1 : B ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.card_bot] at hAB
        omega
      have hB2 : IsElemAbelian2 B :=
        ⟨fun a ha b hb => hA2.1 a (hBA ha) b (hBA hb), fun a ha => hA2.2 a (hBA ha)⟩
      have hBk : Nat.card B ≤ k := by
        have := Nat.card_pos (α := B)
        omega
      have hIH := ih B hBk (hBA.trans hAN) hB2 hB1
      have hfix := two_mul_card_fixV_le hBA hne
      calc 4 * Nat.card A * Nat.card ↥(fixV A)
          = 4 * Nat.card B * (2 * Nat.card ↥(fixV A)) := by rw [hAB]; ring
        _ ≤ 4 * Nat.card B * Nat.card ↥(fixV B) := Nat.mul_le_mul_left _ hfix
        _ ≤ Nat.card K ^ 8 := hIH

theorem four_mul_card_mul_card_fixV_le {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) :
    4 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 8 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    exact four_mul_card_mul_card_fixV_le_one hK hAN hA2 hA1
  · exact four_mul_card_mul_card_fixV_le_two h hK hAN hA2 hA1

theorem rk_add_two_le_rkIdx_fixV {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hA2 : IsElemAbelian2 A) (hA1 : A ≠ ⊥) : rk ↥A + 2 ≤ rkIdx (fixV A) := by
  have hmain := four_mul_card_mul_card_fixV_le hn hK hAN hA2 hA1
  have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (8 * n) := by
    rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      ← pow_add]
    congr 1
    ring
  have hAcard : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA2)
  refine SL3Pair.le_rkIdx_of_card_mul_le hV _ ?_
  rw [pow_add, ← hAcard]
  calc Nat.card ↥(fixV A) * (Nat.card A * 2 ^ 2) = 4 * Nat.card A * Nat.card ↥(fixV A) := by
        ring
    _ ≤ Nat.card K ^ 8 := hmain
    _ = 2 ^ (8 * n) := by rw [hK, ← pow_mul, mul_comm]

theorem not_isFOneModule {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K) :
    ¬ IsFOneModule X := by
  rintro ⟨A, ⟨hAX, hA1, hAel⟩, hoff⟩
  have := rk_add_two_le_rkIdx_fixV hn hK (hAX.trans hXN) hAel hA1
  omega

theorem alphaH_eq_one {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K) :
    alphaH X = 1 :=
  alphaH_eq_one_of_not_isFOneModule (not_isFOneModule hn hK hXN)

theorem not_isFFModule {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K) :
    ¬ IsFFModule X := by
  have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = 2 ^ (8 * n) := by
    rw [Nat.card_prod, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      ← pow_add]
    congr 1
    ring
  exact not_isFFModule_of_not_isFOneModule (IsPGroup.of_card hV) (not_isFOneModule hn hK hXN)

end Sp4

end H

end CFSG.Quasithin
