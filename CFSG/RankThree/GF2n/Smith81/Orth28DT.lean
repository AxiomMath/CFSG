module

public import CFSG.RankThree.GF2n.Smith81.Orth28Sim

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open scoped commutatorElement Matrix

namespace CFSG.RankThree.GF2n.Smith81

namespace OrthDT

section Tensor

variable {K : Type} [Field K] {ι : Type}

@[expose] def cTensor (c : Fin 2 → K) : (ι → K) →ₗ[K] (ι → K) × (ι → K) where
  toFun v := (c 0 • v, c 1 • v)
  map_add' v w := Prod.ext (smul_add _ _ _) (smul_add _ _ _)
  map_smul' a v := Prod.ext (smul_comm _ _ _).symm (smul_comm _ _ _).symm

theorem cTensor_apply (c : Fin 2 → K) (v : ι → K) : cTensor c v = (c 0 • v, c 1 • v) := rfl

theorem cTensor_injective {c : Fin 2 → K} (hc : c ≠ 0) :
    Function.Injective (cTensor (ι := ι) c) := by
  intro v w h
  have h1 : c 0 • v = c 0 • w := congrArg Prod.fst h
  have h2 : c 1 • v = c 1 • w := congrArg Prod.snd h
  by_cases h0 : c 0 = 0
  · have h1' : c 1 ≠ 0 := by
      intro h'
      apply hc
      funext i
      fin_cases i <;> simp [h0, h']
    exact smul_right_injective _ h1' h2
  · exact smul_right_injective _ h0 h1

@[expose] def uPerp (qU : QuadraticForm K (ι → K)) (u : ι → K) : Submodule K (ι → K) :=
  LinearMap.ker ((QuadraticMap.polarBilin qU).flip u)

theorem mem_uPerp {qU : QuadraticForm K (ι → K)} {u w : ι → K} :
    w ∈ uPerp qU u ↔ QuadraticMap.polar qU w u = 0 := by
  simp [uPerp, QuadraticMap.polarBilin_apply_apply]

@[expose] def uRange (qU : QuadraticForm K (ι → K)) (o : (ι → K) ≃ₗ[K] (ι → K)) (u : ι → K) :
    Submodule K (ι → K) :=
  (uPerp qU u).map ((o : (ι → K) →ₗ[K] (ι → K)) - 1) ⊔ Submodule.span K {u}

end Tensor

section CharTwo

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_one_of_sq_eq_one {a : K} (h : a ^ 2 = 1) : a = 1 := by
  have h' : a ^ 2 = 1 ^ 2 := by rw [h, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h1 | h1
  · exact h1
  · rwa [CharTwo.neg_eq] at h1

theorem orthG_sub_mem_span {g : Matrix (Fin 2) (Fin 2) K} (hgg : g * g = 1) {c : Fin 2 → K}
    (hc : c ≠ 0) (hgc : g *ᵥ c = c) (m : Fin 2 → K) : ∃ a : K, g *ᵥ m - m = a • c := by
  set n : Fin 2 → K := g *ᵥ m - m with hn
  have hgn : g *ᵥ n = n := by
    have h1 : g *ᵥ (g *ᵥ m) = m := by
      rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
    rw [hn, Matrix.mulVec_sub, h1]
    funext i
    simp only [Pi.sub_apply]
    have : ((g *ᵥ m) i - m i) + ((g *ᵥ m) i - m i) = 0 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination ((g *ᵥ m) i - m i) * h2
    linear_combination -this
  by_cases hdet : n 0 * c 1 - n 1 * c 0 = 0
  ·
    by_cases hc0 : c 0 = 0
    · have hc1 : c 1 ≠ 0 := by
        intro h1
        apply hc
        funext i
        fin_cases i <;> simp [hc0, h1]
      refine ⟨n 1 / c 1, ?_⟩
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
        have : n 0 * c 1 = 0 := by rw [hc0] at hdet; linear_combination hdet
        have := (mul_eq_zero.mp this).resolve_right hc1
        simp [hc0, this]
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        field_simp
    · refine ⟨n 0 / c 0, ?_⟩
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
        field_simp
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination -hdet
  · exfalso
    have hall : ∀ v : Fin 2 → K, g *ᵥ v = v := by
      intro v
      have hv : (n 0 * c 1 - n 1 * c 0) • v =
          (v 0 * c 1 - v 1 * c 0) • n + (n 0 * v 1 - n 1 * v 0) • c := by
        funext i
        fin_cases i <;> simp <;> ring
      have h2 : (n 0 * c 1 - n 1 * c 0) • (g *ᵥ v) = (n 0 * c 1 - n 1 * c 0) • v := by
        rw [← Matrix.mulVec_smul, hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          hgn, hgc]
      exact smul_right_injective _ hdet h2
    apply hdet
    have h0 : n = 0 := by
      rw [hn, hall m]
      exact sub_self _
    rw [h0]
    simp

theorem orthTensor_fix_pure {g : Matrix (Fin 2) (Fin 2) K} (hgg : g * g = 1)
    {o : (ι → K) ≃ₗ[K] (ι → K)} {c : Fin 2 → K} (hc : c ≠ 0) {u : ι → K} (hu : u ≠ 0)
    (hfix : orthTensor g o (c 0 • u, c 1 • u) = (c 0 • u, c 1 • u)) :
    g *ᵥ c = c ∧ o u = u := by
  have h0 : (g *ᵥ c) 0 = g 0 0 * c 0 + g 0 1 * c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (g *ᵥ c) 1 = g 1 0 * c 0 + g 1 1 * c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e0 : (g *ᵥ c) 0 • o u = c 0 • u := by
    have := congrArg Prod.fst hfix
    simp only [orthTensor, map_smul] at this
    rw [h0, ← this]
    module
  have e1 : (g *ᵥ c) 1 • o u = c 1 • u := by
    have := congrArg Prod.snd hfix
    simp only [orthTensor, map_smul] at this
    rw [h1, ← this]
    module
  have eij : ∀ j, (g *ᵥ c) j • o u = c j • u := by
    intro j
    fin_cases j
    · exact e0
    · exact e1
  obtain ⟨μ, hμ0, hμ, hgc⟩ : ∃ μ : K, μ ≠ 0 ∧ o u = μ • u ∧ ∀ i, (g *ᵥ c) i * μ = c i := by
    have key : ∀ i : Fin 2, c i ≠ 0 → ∃ μ : K, μ ≠ 0 ∧ o u = μ • u ∧
        ∀ j, (g *ᵥ c) j * μ = c j := by
      intro i hi
      have hgi : (g *ᵥ c) i ≠ 0 := by
        intro h
        have := eij i
        rw [h, zero_smul] at this
        exact hi (by simpa [hu] using this.symm)
      have hμ : o u = (c i / (g *ᵥ c) i) • u := by
        calc o u = ((g *ᵥ c) i)⁻¹ • ((g *ᵥ c) i • o u) := by
              rw [smul_smul, inv_mul_cancel₀ hgi, one_smul]
          _ = ((g *ᵥ c) i)⁻¹ • (c i • u) := by rw [eij i]
          _ = (c i / (g *ᵥ c) i) • u := by rw [smul_smul, div_eq_inv_mul]
      refine ⟨c i / (g *ᵥ c) i, div_ne_zero hi hgi, hμ, fun j => ?_⟩
      have h := eij j
      rw [hμ, smul_smul] at h
      exact smul_left_injective K hu h
    by_cases h0' : c 0 = 0
    · have hc1 : c 1 ≠ 0 := by
        intro h
        apply hc
        funext i
        fin_cases i <;> simp [h0', h]
      exact key 1 hc1
    · exact key 0 h0'
  have hgcμ : g *ᵥ c = μ⁻¹ • c := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_eq_div, eq_div_iff hμ0]
    exact hgc i
  have hsq : (μ⁻¹ * μ⁻¹) • c = c := by
    have h1 : g *ᵥ (g *ᵥ c) = c := by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
    rw [hgcμ, Matrix.mulVec_smul, hgcμ, smul_smul] at h1
    exact h1
  have hμ1 : μ = 1 := by
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    have h2 := congrFun hsq i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : μ⁻¹ * μ⁻¹ = 1 := mul_right_cancel₀ hi (h2.trans (one_mul (c i)).symm)
    have h4 : μ ^ 2 = 1 := by
      have : (μ⁻¹ * μ⁻¹) * (μ * μ) = 1 := by field_simp
      rw [h3, one_mul] at this
      rw [pow_two]
      exact this
    exact eq_one_of_sq_eq_one h4
  refine ⟨?_, ?_⟩
  · rw [hgcμ, hμ1, inv_one, one_smul]
  · rw [hμ, hμ1, one_smul]

theorem orthTensor_sub_core {g : Matrix (Fin 2) (Fin 2) K} (hgg : g * g = 1) {c : Fin 2 → K}
    (hc : c ≠ 0) (hgc : g *ᵥ c = c) {o : (ι → K) →ₗ[K] (ι → K)} {u : ι → K} (hou : o u = u)
    (w : ι → K) (s t : K) :
    ∃ a : K, ((c 0 • w + s • u, c 1 • w + t • u) : (ι → K) × (ι → K)) -
        orthTensor g o (c 0 • w + s • u, c 1 • w + t • u) = cTensor c (w - o w - a • u) := by
  obtain ⟨a, ha⟩ := orthG_sub_mem_span hgg hc hgc ![s, t]
  have hc0 : g 0 0 * c 0 + g 0 1 * c 1 = c 0 := by
    have := congrFun hgc 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hc1 : g 1 0 * c 0 + g 1 1 * c 1 = c 1 := by
    have := congrFun hgc 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have ha0 : g 0 0 * s + g 0 1 * t - s = a * c 0 := by
    have := congrFun ha 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have ha1 : g 1 0 * s + g 1 1 * t - t = a * c 1 := by
    have := congrFun ha 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  refine ⟨a, Prod.ext ?_ ?_⟩
  · simp only [orthTensor, map_add, map_smul, hou, Prod.fst_sub, cTensor_apply]
    linear_combination (norm := module) (-hc0) • o w + (-ha0) • u
  · simp only [orthTensor, map_add, map_smul, hou, Prod.snd_sub, cTensor_apply]
    linear_combination (norm := module) (-hc1) • o w + (-ha1) • u

theorem odd_finrank_commSpace_add_uRange {qU : QuadraticForm K (ι → K)}
    (hnd : qU.polarBilin.Nondegenerate) {o : (ι → K) ≃ₗ[K] (ι → K)}
    (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU) (hoo : o * o = 1) {u : ι → K}
    (hu0 : u ≠ 0) (hqu : qU u = 0) (hou : o u = u) :
    Odd (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace o) +
      Module.finrank K (uRange qU o u)) := by
  classical
  set N : (ι → K) →ₗ[K] (ι → K) := (o : (ι → K) →ₗ[K] (ι → K)) - 1 with hN
  have hNapp : ∀ v, N v = o v - v := fun v => by simp [hN]
  set P := uPerp qU u with hP
  set NP := P.map N with hNP
  have hrange : CFSG.RankThree.OrthogonalInvolutions.commSpace o = LinearMap.range N := rfl
  have hadj : ∀ v w, QuadraticMap.polar qU (N v) w = QuadraticMap.polar qU v (N w) := fun v w => by
    rw [hNapp, hNapp]
    exact CFSG.RankThree.OrthogonalInvolutions.polar_sub_eq_polar_sub hO hoo v w
  have hNu : N u = 0 := by rw [hNapp, hou, sub_self]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, QuadraticMap.polar qU v₀ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hnd.2 u fun v => by simpa [QuadraticMap.polarBilin_apply_apply] using h v)
  have hdecomp : ∀ v, ∃ p ∈ P, ∃ l : K, v = p + l • v₀ := by
    intro v
    refine ⟨v - (QuadraticMap.polar qU v u / QuadraticMap.polar qU v₀ u) • v₀, ?_,
      QuadraticMap.polar qU v u / QuadraticMap.polar qU v₀ u, by abel⟩
    rw [hP, mem_uPerp, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul,
      div_mul_cancel₀ _ hv₀, sub_self]
  have hrange_eq : LinearMap.range N = NP ⊔ Submodule.span K {N v₀} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨p, hp, l, rfl⟩ := hdecomp v
      rw [map_add, map_smul]
      exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hp)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    · refine sup_le ?_ ?_
      · rintro _ ⟨p, -, rfl⟩
        exact ⟨p, rfl⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact ⟨v₀, rfl⟩
  have hNP_range : NP ≤ LinearMap.range N := by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨p, rfl⟩
  rw [hrange]
  by_cases hu : u ∈ LinearMap.range N
  ·
    obtain ⟨v, hv⟩ := hu
    have hvP : v ∈ P := by
      rw [hP, mem_uPerp]
      have h1 : qU (o v) = qU v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hO v
      have h2 : o v = v + u := by rw [← hv, hNapp]; abel
      rw [h2, CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hqu] at h1
      linear_combination h1
    have hA1 : u ∈ NP := Submodule.mem_map.mpr ⟨v, hvP, hv⟩
    have hA2 : N v₀ ∉ NP := by
      rintro ⟨p, hp, hpe⟩
      have hk : N (v₀ - p) = 0 := by rw [map_sub, ← hpe, sub_self]
      have h3 : QuadraticMap.polar qU (v₀ - p) u = 0 := by
        rw [← hv, ← hadj, hk, QuadraticMap.polar_zero_left]
      have h4 : QuadraticMap.polar qU (v₀ - p) u = QuadraticMap.polar qU v₀ u := by
        rw [QuadraticMap.polar_sub_left, mem_uPerp.mp hp, sub_zero]
      exact hv₀ (h4 ▸ h3)
    have e1 : Module.finrank K (LinearMap.range N) = Module.finrank K NP + 1 := by
      rw [hrange_eq]
      exact Submodule.finrank_sup_span_singleton hA2
    have e2 : uRange qU o u = NP := by
      unfold uRange
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hA1)
    rw [e1, e2]
    exact ⟨Module.finrank K NP, by ring⟩
  · have hB1 : u ∉ NP := fun h => hu (hNP_range h)
    have hB2 : N v₀ ∈ NP := by
      have hfix := CFSG.RankThree.OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace hnd hO hoo
      have hperp : LinearMap.BilinForm.orthogonal qU.polarBilin
          (CFSG.RankThree.OrthogonalInvolutions.fixSpace o) =
          CFSG.RankThree.OrthogonalInvolutions.commSpace o := by
        rw [hfix]
        exact LinearMap.BilinForm.orthogonal_orthogonal hnd
          (QuadraticMap.isSymm_polarBilin qU).isRefl _
      have hu' : u ∉ LinearMap.BilinForm.orthogonal qU.polarBilin
          (CFSG.RankThree.OrthogonalInvolutions.fixSpace o) := by
        rw [hperp]
        exact hu
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu'
      push Not at hu'
      obtain ⟨k, hk, hku⟩ := hu'
      have hNk : N k = 0 := by
        rw [hNapp, CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hk, sub_self]
      have hku' : QuadraticMap.polar qU k u ≠ 0 := by
        intro h
        apply hku
        rw [QuadraticMap.polarBilin_apply_apply]
        exact h
      refine Submodule.mem_map.mpr ⟨v₀ - (QuadraticMap.polar qU v₀ u / QuadraticMap.polar qU k u) •
        k, ?_, ?_⟩
      · rw [hP, mem_uPerp, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul,
          div_mul_cancel₀ _ hku', sub_self]
      · rw [map_sub, map_smul, hNk, smul_zero, sub_zero]
    have e1 : Module.finrank K (LinearMap.range N) = Module.finrank K NP := by
      rw [hrange_eq]
      exact congrArg (fun W : Submodule K (ι → K) => Module.finrank K W)
        (sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hB2))
    have e2 : Module.finrank K (uRange qU o u) = Module.finrank K NP + 1 := by
      unfold uRange
      exact Submodule.finrank_sup_span_singleton hB1
    rw [e1, e2]
    exact ⟨Module.finrank K NP, by ring⟩

end CharTwo

section Group

variable {G : Type} [Group G]

@[expose] def Wgrp (Q Z A : Subgroup G) (y : G) : Subgroup G :=
  ⁅Q ⊓ QB A, Subgroup.zpowers y⁆ ⊔ (Z ⊔ A)

variable [Finite G] {M Q Z : Subgroup G}

theorem conjSubgroup_Wgrp (H : StrothHyp M Q Z) (g x : G) :
    conjSubgroup g⁻¹ (Wgrp Q Z (conjSubgroup g Z) x) =
      Wgrp Q Z (conjSubgroup g⁻¹ Z) (g⁻¹ * x * g) := by
  have hQB : QB (conjSubgroup g Z) = conjSubgroup g Q := QB_conj_eq H g
  have hQB' : QB (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
  have e1 : conjSubgroup g⁻¹ (conjSubgroup g Q) = Q := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have e2 : conjSubgroup g⁻¹ (conjSubgroup g Z) = Z := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  unfold Wgrp
  rw [hQB, hQB']
  unfold conjSubgroup at *
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_inf _ _ _
    (MulAut.conj g⁻¹).injective, e1, e2, MonoidHom.map_zpowers, inf_comm, sup_comm (Z.map _)]
  simp [MulAut.conj_apply]

@[expose] def preimSub {K : Type} [Field K] {γ : G → K} {Q Z : Subgroup G}
    (M₀ : Tim79.QuadModel Q Z K γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)) (R : Submodule K ((ι → K) × (ι → K))) : Subgroup G where
  carrier := {x | x ∈ Q ∧ φ (M₀.π x) ∈ R}
  mul_mem' := by
    rintro x y ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
    refine ⟨Q.mul_mem hxQ hyQ, ?_⟩
    rw [M₀.π_mul x hxQ y hyQ, map_add]
    exact R.add_mem hx hy
  one_mem' := by
    refine ⟨Q.one_mem, ?_⟩
    rw [Tim79.QuadModel.pi_one, map_zero]
    exact R.zero_mem
  inv_mem' := by
    rintro x ⟨hxQ, hx⟩
    refine ⟨Q.inv_mem hxQ, ?_⟩
    rw [Tim79.QuadModel.pi_inv M₀ hxQ, map_neg]
    exact R.neg_mem hx

theorem mem_preimSub {K : Type} [Field K] {γ : G → K} {Q Z : Subgroup G}
    {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)} {R : Submodule K ((ι → K) × (ι → K))} {x : G} :
    x ∈ preimSub M₀ φ R ↔ x ∈ Q ∧ φ (M₀.π x) ∈ R := Iff.rfl

theorem exists_root_data {B A : Subgroup G} (C : OrthCtx M Q Z B) (hcA : Ctx M Q Z A) :
    ∃ (c₁ c₂ : C.K) (u : C.ι → C.K) (a : G), (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ u ≠ 0 ∧ C.qU u = 0 ∧
      a ∈ A ∧ a ≠ 1 ∧ C.φ (C.M₀.π a) = (c₁ • u, c₂ • u) := by
  have H := hcA.hyp
  obtain ⟨g₀, hg₀⟩ := hcA.conj
  have hZne : Z ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have haA : g₀ * (z : G) * g₀⁻¹ ∈ A := by
    rw [hg₀, mem_conjSubgroup]
    simpa [mul_assoc] using z.2
  have ha1 : g₀ * (z : G) * g₀⁻¹ ≠ 1 := by
    intro h
    apply hz1'
    have : (z : G) = g₀⁻¹ * (g₀ * (z : G) * g₀⁻¹) * g₀ := by group
    rw [this, h]; group
  have haQ : g₀ * (z : G) * g₀⁻¹ ∈ Q := hcA.le haA
  have haZ : g₀ * (z : G) * g₀⁻¹ ∉ Z := by
    intro h
    have hm : g₀ * (z : G) * g₀⁻¹ ∈ Z ⊓ A := ⟨h, haA⟩
    rw [hcA.inf_eq_bot, Subgroup.mem_bot] at hm
    exact ha1 hm
  obtain ⟨c₁, c₂, u, hc, hu0, hqu, hpa⟩ :=
    (C.hF.root z z.2 hz1' _ haQ haZ).mp (isConj_iff.mpr ⟨g₀, rfl⟩)
  exact ⟨c₁, c₂, u, _, hc, hu0, hqu, haA, ha1, hpa⟩

theorem card_Wgrp_eq {B A : Subgroup G} (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (h52 : Smith52ActStatement) (hcA : Ctx M Q Z A) {y : G} (hyM : y ∈ M) (hy2 : y * y = 1)
    (hyA : ∀ a ∈ A, y * a * y⁻¹ = a) {g : Matrix (Fin 2) (Fin 2) C.K} (hgg : g * g = 1)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ y g o) :
    ∃ u : C.ι → C.K, u ≠ 0 ∧ C.qU u = 0 ∧ o u = u ∧
      Nat.card (Wgrp Q Z A y) = Nat.card Z ^ (1 + Module.finrank C.K (uRange C.qU o u)) := by
  classical
  have H := hcA.hyp
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨c₁, c₂, u, a₀, hc12, hu0, hqu, ha₀A, ha₀1, hpa⟩ := exists_root_data C hcA
  set c : Fin 2 → C.K := ![c₁, c₂] with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    rcases hc12 with h1 | h1
    · exact h1 (by simpa [hcdef] using congrFun h0 0)
    · exact h1 (by simpa [hcdef] using congrFun h0 1)
  have hc0' : c 0 = c₁ := rfl
  have hc1' : c 1 = c₂ := rfl
  have hpa' : C.φ (C.M₀.π a₀) = (c 0 • u, c 1 • u) := by rw [hpa]; simp [hcdef]
  have ha₀Q : a₀ ∈ Q := hcA.le ha₀A
  have hfix : orthTensor g o (c 0 • u, c 1 • u) = (c 0 • u, c 1 • u) := by
    have h1 := hact a₀ ha₀Q
    rw [hyA a₀ ha₀A, hpa'] at h1
    exact h1.symm
  obtain ⟨hgc, hou⟩ := orthTensor_fix_pure hgg hc0 hu0 hfix
  refine ⟨u, hu0, hqu, hou, ?_⟩
  set Rc : Submodule C.K ((C.ι → C.K) × (C.ι → C.K)) :=
    (uRange C.qU o u).map (cTensor c) with hRc
  set P' := preimSub C.M₀ C.φ Rc with hP'
  have hline := isLineGen_pi hcA C.hD ha₀A ha₀1
  have hmemRc : ∀ r ∈ uRange C.qU o u, cTensor c r ∈ Rc := fun r hr => Submodule.mem_map_of_mem hr
  have h52A := h52 G M Q Z B hc C.K C.γ C.M₀ C.hD C.ι C.qU C.φ C.hF C.hA A hcA.conj hcA.le hcA.ne
    c₁ c₂ u hc12 hu0 hqu ⟨a₀, ha₀A, ha₀1, hpa⟩
  have huR : ∀ s : C.K, s • u ∈ uRange C.qU o u := fun s =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have hcommπ : ∀ s ∈ Q, C.φ (C.M₀.π ⁅s, y⁆) =
      C.φ (C.M₀.π s) - orthTensor g o (C.φ (C.M₀.π s)) := by
    intro s hsQ
    have hyQ' : y * s * y⁻¹ ∈ Q := conj_mem_Q H hyM hsQ
    have e : ⁅s, y⁆ = s * (y * s * y⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e, C.M₀.π_mul s hsQ _ (Q.inv_mem hyQ'), Tim79.QuadModel.pi_inv C.M₀ hyQ', map_add,
      map_neg, ← sub_eq_add_neg, hact s hsQ]
  have hrange : ∀ (w : C.ι → C.K) (a : C.K), w ∈ uPerp C.qU u →
      w - o w - a • u ∈ uRange C.qU o u := by
    intro w a hw
    have h1 : -(((o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) - 1) w) ∈
        (uPerp C.qU u).map ((o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) - 1) :=
      Submodule.neg_mem _ (Submodule.mem_map_of_mem hw)
    have h2 : (-a) • u ∈ Submodule.span C.K {u} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have h3 := Submodule.add_mem_sup h1 h2
    have e : w - o w - a • u =
        -(((o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) - 1) w) + (-a) • u := by
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
      module
    rw [e]
    exact h3
  have hWle : Wgrp Q Z A y ≤ P' := by
    refine sup_le (Subgroup.commutator_le.mpr fun s hs t ht => ?_) (sup_le ?_ ?_)
    · rcases mem_zpowers_of_mul_self_eq_one hy2 ht with rfl | rfl
      · simp only [commutatorElement_one_right]
        exact P'.one_mem
      · have hsQ : s ∈ Q := hs.1
        obtain ⟨w, s', t', hw, hs'⟩ := h52A.1 s hs
        refine ⟨comm_mem_Q H hyM hsQ, ?_⟩
        rw [hcommπ s hsQ, hs']
        obtain ⟨a, ha⟩ := orthTensor_sub_core hgg hc0 hgc (o := (o : _ →ₗ[_] _)) hou w s' t'
        have : ((c₁ • w + s' • u, c₂ • w + t' • u) : (C.ι → C.K) × (C.ι → C.K)) -
            orthTensor g o (c₁ • w + s' • u, c₂ • w + t' • u) = cTensor c (w - o w - a • u) := ha
        rw [this]
        exact hmemRc _ (hrange w a (mem_uPerp.mpr hw))
    · intro z hz
      refine ⟨hZQ hz, ?_⟩
      rw [(C.M₀.π_ker z (hZQ hz)).mpr hz, map_zero]
      exact Rc.zero_mem
    · intro a ha
      have haQ : a ∈ Q := hcA.le ha
      refine ⟨haQ, ?_⟩
      obtain ⟨s, hs⟩ := (hline _).mp (C.M₀.pi_mem_img ha haQ)
      rw [hs, map_smul, hpa]
      have : s • ((c₁ • u, c₂ • u) : (C.ι → C.K) × (C.ι → C.K)) = cTensor c (s • u) := by
        simp [cTensor_apply, hcdef, smul_smul, mul_comm]
      rw [this]
      exact hmemRc _ (huR s)
  have hZW : Z ≤ Wgrp Q Z A y := le_sup_left.trans le_sup_right
  have hAW : A ≤ Wgrp Q Z A y := le_sup_right.trans le_sup_right
  have hPle : P' ≤ Wgrp Q Z A y := by
    rintro x ⟨hxQ, hx⟩
    obtain ⟨r, hr, hrx⟩ := Submodule.mem_map.mp hx
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.mp hr
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hr₁
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hr₂
    have hnw : -w ∈ uPerp C.qU u := Submodule.neg_mem _ hw
    obtain ⟨v, hvS, hv⟩ := h52A.2 (-w) 0 0 (mem_uPerp.mp hnw)
    have hvQ : v ∈ Q := hvS.1
    have hcv : ⁅v, y⁆ ∈ Wgrp Q Z A y :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hvS (Subgroup.mem_zpowers y))
    have hcvQ : ⁅v, y⁆ ∈ Q := comm_mem_Q H hyM hvQ
    obtain ⟨a', ha'⟩ := orthTensor_sub_core hgg hc0 hgc (o := (o : _ →ₗ[_] _)) hou (-w) 0 0
    have hv' : C.φ (C.M₀.π v) = (c 0 • (-w) + (0 : C.K) • u, c 1 • (-w) + (0 : C.K) • u) := hv
    have hπcv : C.φ (C.M₀.π ⁅v, y⁆) = cTensor c (-w - o (-w) - a' • u) := by
      rw [hcommπ v hvQ, hv']
      exact ha'
    obtain ⟨a'', ha''A, ha''Q, ha''π⟩ :=
      (hline ((a + a') • C.M₀.π a₀)).mpr ⟨a + a', rfl⟩
    have hx''Q : ⁅v, y⁆ * a'' ∈ Q := Q.mul_mem hcvQ ha''Q
    have hx'' : C.φ (C.M₀.π (⁅v, y⁆ * a'')) = C.φ (C.M₀.π x) := by
      rw [C.M₀.π_mul _ hcvQ _ ha''Q, map_add, hπcv, ha''π, map_smul, hpa', ← hrx]
      simp only [cTensor_apply, map_neg, neg_sub, Prod.mk_add_mk, Prod.smul_mk, smul_add,
        LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, add_smul]
      refine Prod.ext ?_ ?_ <;> dsimp only <;> module
    have hπ : C.M₀.π (⁅v, y⁆ * a'') = C.M₀.π x := C.φ.injective hx''
    have hZx : (⁅v, y⁆ * a'')⁻¹ * x ∈ Z :=
      (Tim79.QuadModel.pi_eq_iff C.M₀ hx''Q hxQ).mp hπ
    have : x = (⁅v, y⁆ * a'') * ((⁅v, y⁆ * a'')⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcv (hAW ha''A)) (hZW hZx)
  have hWP : Wgrp Q Z A y = P' := le_antisymm hWle hPle
  have hWQ : Wgrp Q Z A y ≤ Q := fun x hx => (hWle hx).1
  have hcard := C.M₀.card_eq hWQ hZW
  have hmem : ∀ r : ↥(uRange C.qU o u),
      C.φ.symm (cTensor c (r : C.ι → C.K)) ∈ C.M₀.img (Wgrp Q Z A y) := by
    intro r
    obtain ⟨x, hxQ, hx⟩ := C.M₀.π_surj (C.φ.symm (cTensor c (r : C.ι → C.K)))
    have hxP : x ∈ P' := ⟨hxQ, by rw [hx, LinearEquiv.apply_symm_apply]; exact hmemRc _ r.2⟩
    exact ⟨x, hWP ▸ hxP, hxQ, hx⟩
  have himg : Nat.card ↥(C.M₀.img (Wgrp Q Z A y)) = Nat.card ↥(uRange C.qU o u) := by
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun r => ⟨C.φ.symm (cTensor c (r : C.ι → C.K)),
      hmem r⟩) ⟨?_, ?_⟩)
    · intro r r' h
      have h1 : C.φ.symm (cTensor c (r : C.ι → C.K)) = C.φ.symm (cTensor c (r' : C.ι → C.K)) :=
        congrArg Subtype.val h
      exact Subtype.ext (cTensor_injective hc0 (C.φ.symm.injective h1))
    · rintro ⟨e, x, hxW, hxQ, rfl⟩
      obtain ⟨r, hr, hrx⟩ := Submodule.mem_map.mp (hWP ▸ hxW : x ∈ P').2
      refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
      show C.φ.symm (cTensor c r) = C.M₀.π x
      rw [hrx, LinearEquiv.symm_apply_apply]
  rw [hcard, himg, Module.natCard_eq_pow_finrank (K := C.K) (V := ↥(uRange C.qU o u)), C.hD.card,
    pow_add, pow_one]

end Group

end OrthDT

open OrthDT

section DT

variable {G : Type} [Group G] [Finite G]

theorem orthDT_of_sim (h52 : Smith52ActStatement)
    (hT : OrthTacitStatement) {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) (hsim : OrthSim C) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hxL : x ∈ Lgen M (LB M Q B)) {q' : G} (hq'Q : q' ∈ Q) (hcc : IsConj x ⁅q', x⁆) {g : G}
    (hcC₀ : ⁅q', x⁆ ∈ conjSubgroup g Z) : g⁻¹ * x * g ∈ Lgen M (LB M Q B) := by
  have hcB := hc.ctx
  have H := hcB.hyp
  have hno := noA2_of_tacit hT hc
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hZQ : Z ≤ Q := H.Z_normal.1
  by_cases hgZ : conjSubgroup g Z = Z
  ·
    have hgM : g ∈ M := by
      have := conjSubgroup_eq_self_iff.mp hgZ
      rwa [H.normalizer_Z.1] at this
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (Lgen_normalizes M (LB M Q B) (M.inv_mem hgM)) x).mp hxL
    simpa using hmem
  have hc1 : ⁅q', x⁆ ≠ 1 := ne_one_of_isConj_Z hs.ne_one hcc
  have hcQ : ⁅q', x⁆ ∈ Q := comm_mem_Q H hxM hq'Q
  have hc2 : ⁅q', x⁆ * ⁅q', x⁆ = 1 := by
    have h1 : g⁻¹ * ⁅q', x⁆ * g ∈ Z := mem_conjSubgroup.mp hcC₀
    have h2 := Z_sq H h1
    have e : ⁅q', x⁆ * ⁅q', x⁆ = g * ((g⁻¹ * ⁅q', x⁆ * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    rw [e, h2]; group
  have hxc : x * ⁅q', x⁆ = ⁅q', x⁆ * x := commute_comm_of_sq hx2 hc2
  have hC₀ : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  have hxN : x ∈ Subgroup.normalizer ((conjSubgroup g Z : Subgroup G) : Set G) :=
    hC₀.mem_normalizer_of_commute H hc1 hcC₀ hxc
  have hC₀Q : conjSubgroup g Z ≤ Q := root_le_Q H hC₀ hcC₀ hcQ hc1
  have hcC : Ctx M Q Z (conjSubgroup g Z) := ⟨H, hC₀, hC₀Q, hgZ⟩
  have hxC : ∀ a ∈ conjSubgroup g Z, x * a * x⁻¹ = a := by
    obtain ⟨T, hTπ, -, -⟩ := C.hD.linear_of_centralizes hxM hxZ
    have hline := isLineGen_pi hcC C.hD hcC₀ hc1
    have hTc : T (C.M₀.π ⁅q', x⁆) = C.M₀.π ⁅q', x⁆ := by
      rw [← hTπ _ hcQ]
      congr 1
      have : x * ⁅q', x⁆ * x⁻¹ = ⁅q', x⁆ := by rw [hxc]; group
      rw [this]
    intro a ha
    have haQ : a ∈ Q := hC₀Q ha
    have hxaC : x * a * x⁻¹ ∈ conjSubgroup g Z := by
      have := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
      exact this
    obtain ⟨s, hsa⟩ := (hline _).mp (C.M₀.pi_mem_img ha haQ)
    have hπ : C.M₀.π a = C.M₀.π (x * a * x⁻¹) := by
      rw [hTπ a haQ, hsa, map_smul, hTc]
    have hZ1 : a⁻¹ * (x * a * x⁻¹) ∈ Z := (Tim79.QuadModel.pi_eq_iff C.M₀ haQ
      (conj_mem_Q H hxM haQ)).mp hπ
    have hC1 : a⁻¹ * (x * a * x⁻¹) ∈ conjSubgroup g Z :=
      (conjSubgroup g Z).mul_mem ((conjSubgroup g Z).inv_mem ha) hxaC
    have hbot : a⁻¹ * (x * a * x⁻¹) ∈ Z ⊓ conjSubgroup g Z := ⟨hZ1, hC1⟩
    rw [hcC.inf_eq_bot, Subgroup.mem_bot] at hbot
    have := congrArg (a * ·) hbot
    simpa using this
  set x' : G := g⁻¹ * x * g with hx'def
  set Y : Subgroup G := conjSubgroup g⁻¹ Z with hYdef
  have hx'M : x' ∈ M := by
    have h1 : g⁻¹ * x * g ∈ M := by
      have := hxN
      rw [normalizer_conj_eq H g, mem_conjSubgroup] at this
      exact this
    exact h1
  have hx'Z : ∀ z ∈ Z, x' * z * x'⁻¹ = z := by
    intro z hz
    have hzC : g * z * g⁻¹ ∈ conjSubgroup g Z := by
      rw [mem_conjSubgroup]; simpa [mul_assoc] using hz
    have := hxC _ hzC
    calc x' * z * x'⁻¹ = g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g := by simp only [hx'def]; group
      _ = z := by rw [this]; group
  have hx'2 : x' * x' = 1 := by
    have : x' * x' = g⁻¹ * (x * x) * g := by simp only [hx'def]; group
    rw [this, hx2]; group
  have hx'H0 : x' ∈ H0 M Z := ⟨hx'M, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hx'Z z hz
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm⟩
  have hYQ : Y ≤ Q := by
    have h1 : Z ≤ QB (conjSubgroup g Z) :=
      (IsZConjugate.le_QB_iff H hC₀ (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hC₀Q)
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rw [QB_conj_eq H g] at h2
    have e : conjSubgroup g⁻¹ (conjSubgroup g Q) = Q := by
      rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    exact h2.trans (le_of_eq e)
  have hYZ : Y ≠ Z := by
    intro h
    apply hgZ
    have h1 : g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := conjSubgroup_eq_self_iff.mp h
    have h2 : g ∈ Subgroup.normalizer (Z : Set G) := by simpa using Subgroup.inv_mem _ h1
    exact conjSubgroup_eq_self_iff.mpr h2
  have hcY : Ctx M Q Z Y := ⟨H, ⟨g⁻¹, rfl⟩, hYQ, hYZ⟩
  have hx'Y : ∀ a ∈ Y, x' * a * x'⁻¹ = a := by
    intro a ha
    have haZ : g * a * g⁻¹ ∈ Z := by
      have := mem_conjSubgroup.mp ha
      simpa using this
    have := hxZ _ haZ
    calc x' * a * x'⁻¹ = g⁻¹ * (x * (g * a * g⁻¹) * x⁻¹) * g := by simp only [hx'def]; group
      _ = a := by rw [this]; group
  obtain ⟨g₁, o₁, hact₁, hgg₁, hoo₁, hiso₁, hev₁⟩ := lgen_involution_normalized hc hno C hxL hx2
  obtain ⟨g₂, o₂, hact₂, hgg₂, hoo₂, hiso₂⟩ :=
    exists_normalized_involution_of_sim hc C hsim hx'H0 hx'2
  obtain ⟨u₁, hu₁0, hqu₁, hou₁, hcard₁⟩ :=
    card_Wgrp_eq hc C h52 hcC hxM hx2 hxC hgg₁ hact₁
  obtain ⟨u₂, hu₂0, hqu₂, hou₂, hcard₂⟩ :=
    card_Wgrp_eq hc C h52 hcY hx'M hx'2 hx'Y hgg₂ hact₂
  have hcard : Nat.card ↥(Wgrp Q Z (conjSubgroup g Z) x) = Nat.card ↥(Wgrp Q Z Y x') := by
    rw [← card_conjSubgroup g⁻¹, conjSubgroup_Wgrp H g x]
  have hq2 : 2 ≤ Nat.card ↥Z := by have := H.q4; omega
  have hexp : Module.finrank C.K (uRange C.qU o₁ u₁) = Module.finrank C.K (uRange C.qU o₂ u₂) := by
    have h := hcard₁.symm.trans (hcard.trans hcard₂)
    have := Nat.pow_right_injective hq2 h
    omega
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hodd₁ := odd_finrank_commSpace_add_uRange hnd
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso₁)
    (LinearEquiv.ext fun v => hoo₁ v) hu₁0 hqu₁ hou₁
  have hodd₂ := odd_finrank_commSpace_add_uRange hnd
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso₂)
    (LinearEquiv.ext fun v => hoo₂ v) hu₂0 hqu₂ hou₂
  have heven₂ : Even (Module.finrank C.K (CFSG.RankThree.OrthogonalInvolutions.commSpace o₂)) := by
    rw [Nat.even_iff] at hev₁ ⊢
    rw [Nat.odd_iff] at hodd₁ hodd₂
    omega
  exact (mem_Lgen_iff_normalized_even hc hno C hx'M hx'2 hgg₂ hoo₂ hiso₂ hact₂).mpr heven₂

end DT

@[expose] def OrthDTHypFourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ C : OrthCtx M Q Z B, Fintype.card C.ι = 4 → ¬ NoTotallySingularPlane C.qU →
      ∀ (X : Subgroup G) (x : G), Sit M Q Z X x → x ∈ Lgen M (LB M Q B) →
        ∀ q', OrthValid M Q Z x q' → ∀ g : G, ⁅q', x⁆ ∈ conjSubgroup g Z →
          x ∉ QB (conjSubgroup g Z) → g⁻¹ * x * g ∈ Lgen M (LB M Q B)

theorem orthDT_of_hypFour (h24 : Smith24ActStatement)
    (h52 : Smith52ActStatement) (hT : OrthTacitStatement) (h : OrthDTHypFourStatement) :
    OrthDTStatement := by
  intro G _ _ M Q Z B hc X x hs hxL q' hval g hcC₀ hxQ
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  by_cases hdim : Fintype.card C.ι ≠ 4 ∨ NoTotallySingularPlane C.qU
  · exact orthDT_of_sim h52 hT hc C (orthSim_of_dim hc C hdim) hs hxL hval.1 hval.2.2.1 hcC₀
  · push Not at hdim
    exact h G M Q Z B hc C hdim.1 hdim.2 X x hs hxL q' hval g hcC₀ hxQ

end CFSG.RankThree.GF2n.Smith81
