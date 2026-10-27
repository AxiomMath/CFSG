module

public import Mathlib.GroupTheory.PGroup
public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularVectors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix QuadraticMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem s16g_orth_values_of_singular [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (B : Subgroup (Matrix.GeneralLinearGroup ι K)) (hB : IsPGroup p B)
    (hBQ : ∀ b ∈ B, ∀ v : ι → K, Q ((b : Matrix ι ι K) *ᵥ v) = Q v)
    {u : ι → K} (hu : u ≠ 0) (hQu : Q u = 0) (hfix : ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ u = u)
    (c : K) :
    ∃ w : ι → K, w ≠ 0 ∧ Q w = c ∧ ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ w = w := by
  classical
  haveI : Fintype ↥B := Fintype.ofFinite ↥B
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := ↥B)).mp hB
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hn : (Nat.card ↥B : K) ≠ 0 := by
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ hpK
  let M : ↥B → (ι → K) →ₗ[K] (ι → K) := fun b =>
    Matrix.mulVecLin ((b : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)
  have hpol_self : ∀ x : ι → K, QuadraticMap.polar Q x x = 0 := fun x => by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hfixu : ∀ b : ↥B, M b u = u := fun b => by
    have h := hfix (b : Matrix.GeneralLinearGroup ι K) b.2
    simpa only [M, Matrix.mulVecLin_apply] using h
  have hiso : ∀ b : ↥B, ∀ x y : ι → K,
      QuadraticMap.polar Q (M b x) (M b y) = QuadraticMap.polar Q x y := by
    intro b x y
    have hbx : Q (M b x) = Q x := by
      have h := hBQ (b : Matrix.GeneralLinearGroup ι K) b.2 x
      simpa only [M, Matrix.mulVecLin_apply] using h
    have hby : Q (M b y) = Q y := by
      have h := hBQ (b : Matrix.GeneralLinearGroup ι K) b.2 y
      simpa only [M, Matrix.mulVecLin_apply] using h
    have hbxy : Q (M b x + M b y) = Q (x + y) := by
      rw [← LinearMap.map_add]
      have h := hBQ (b : Matrix.GeneralLinearGroup ι K) b.2 (x + y)
      simpa only [M, Matrix.mulVecLin_apply] using h
    simp only [QuadraticMap.polar]
    rw [hbxy, hbx, hby]
  have hπ_fix : ∀ x, ∀ b₀ : ↥B,
      M b₀ ((Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b x)
        = (Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b x := by
    intro x b₀
    rw [LinearMap.map_smul, map_sum]
    congr 1
    refine Fintype.sum_bijective (fun b : ↥B => b₀ * b) (Group.mulLeft_bijective b₀)
      (fun b => M b₀ (M b x)) (fun b => M b x) (fun b => ?_)
    simp only [M, Matrix.mulVecLin_mul, LinearMap.comp_apply, Subgroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_mul]
  have hπ_id : ∀ x, (∀ b : ↥B, M b x = x) →
      (Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b x = x := by
    intro x hx
    simp only [hx]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hπ_val : ∀ x,
      QuadraticMap.polar Q u ((Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b x)
        = QuadraticMap.polar Q u x := by
    intro x
    have hlin : ∀ y : ι → K,
        QuadraticMap.polar Q u y = (QuadraticMap.polarBilin Q u) y :=
      fun y => (QuadraticMap.polarBilin_apply_apply Q u y).symm
    simp only [hlin]
    rw [LinearMap.map_smul, map_sum]
    have hsum : (∑ b : ↥B, (QuadraticMap.polarBilin Q u) (M b x))
        = ∑ _b : ↥B, (QuadraticMap.polarBilin Q u) x := by
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb : QuadraticMap.polar Q u (M b x) = QuadraticMap.polar Q u x := by
        calc QuadraticMap.polar Q u (M b x)
            = QuadraticMap.polar Q (M b u) (M b x) := by rw [hfixu b]
          _ = QuadraticMap.polar Q u x := hiso b u x
      simpa only [hlin] using hb
    rw [hsum, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hn, one_smul]
  obtain ⟨x₀, hx₀⟩ : ∃ x : ι → K, QuadraticMap.polar Q u x ≠ 0 := by
    by_contra h
    have hzero : ∀ y : ι → K, (QuadraticMap.polarBilin Q u) y = 0 := by
      intro y
      rw [QuadraticMap.polarBilin_apply_apply]
      exact not_not.mp (not_exists.mp h y)
    exact hu (hQ.1 u hzero)
  let a : K := (QuadraticMap.polar Q u x₀)⁻¹
  let x₁ : ι → K := a • x₀
  have hx₁ : QuadraticMap.polar Q u x₁ = 1 := by
    change QuadraticMap.polar Q u (a • x₀) = 1
    rw [QuadraticMap.polar_smul_right]
    change a * QuadraticMap.polar Q u x₀ = 1
    exact inv_mul_cancel₀ hx₀
  set P : ι → K := (Nat.card ↥B : K)⁻¹ • ∑ b : ↥B, M b x₁ with hPdef
  have hPfix : ∀ b : ↥B, M b P = P := by
    intro b
    rw [hPdef]
    exact hπ_fix x₁ b
  have hPval : QuadraticMap.polar Q u P = 1 := by
    rw [hPdef]
    exact (hπ_val x₁).trans hx₁
  set F : ι → K := P + (Q P) • u with hFdef
  have hFfix : ∀ b : ↥B, M b F = F := by
    intro b
    rw [hFdef]
    rw [LinearMap.map_add, hPfix b, LinearMap.map_smul, hfixu b]
  have hFval : QuadraticMap.polar Q u F = 1 := by
    rw [hFdef]
    rw [QuadraticMap.polar_add_right (Q := Q), hPval, QuadraticMap.polar_smul_right (Q := Q),
      hpol_self u, smul_zero, add_zero]
  have hFQ : Q F = 0 := by
    rw [hFdef]
    have h1 : Q ((Q P) • u) = 0 := by rw [QuadraticMap.map_smul Q, hQu, smul_zero]
    have h2 : QuadraticMap.polar Q P ((Q P) • u) = Q P := by
      rw [QuadraticMap.polar_smul_right (Q := Q), QuadraticMap.polar_comm (⇑Q),
        hPval, smul_eq_mul, mul_one]
    rw [QuadraticMap.map_add Q, h1, h2, add_zero]
    exact CharTwo.add_self_eq_zero (Q P)
  set W : ι → K := u + c • F with hWdef
  have hWfix : ∀ b : ↥B, M b W = W := by
    intro b
    rw [hWdef]
    rw [LinearMap.map_add, LinearMap.map_smul, hfixu b, hFfix b]
  have hWQ : Q W = c := by
    rw [hWdef]
    have h1 : Q (c • F) = 0 := by rw [QuadraticMap.map_smul Q, hFQ, smul_zero]
    have h2 : QuadraticMap.polar Q u (c • F) = c := by
      rw [QuadraticMap.polar_smul_right (Q := Q), hFval, smul_eq_mul, mul_one]
    rw [QuadraticMap.map_add Q, hQu, h1, h2]
    simp
  have hWne : W ≠ 0 := by
    intro hw0
    have h0 : QuadraticMap.polar Q u F = 0 := by
      have h1 := QuadraticMap.polar_add_left Q u (c • F) F
      have h2 : QuadraticMap.polar Q (u + c • F) F = 0 := by
        rw [← hWdef, hw0, QuadraticMap.polar_zero_left (Q := Q)]
      have h3 : QuadraticMap.polar Q (c • F) F = 0 := by
        rw [QuadraticMap.polar_smul_left, hpol_self F, smul_zero]
      simpa [h2, h3] using h1.symm
    rw [hFval] at h0
    exact one_ne_zero h0
  exact ⟨W, hWne, hWQ, fun b hb => by
    have h := hWfix ⟨b, hb⟩
    simpa only [M, Matrix.mulVecLin_apply] using h⟩

theorem s16g_exists_singular_of_finrank_ge_three (Q : QuadraticForm K (ι → K))
    (U : Submodule K (ι → K)) (hU : 3 ≤ Module.finrank K U) : ∃ u ∈ U, u ≠ 0 ∧ Q u = 0 := by
  haveI : Module.Finite K U := Module.Finite.of_injective U.subtype Subtype.coe_injective
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U) hU
  let D : Submodule K (ι → K) :=
    Submodule.span K (Set.range (fun i : Fin 3 => (f i : ι → K)))
  have hDle : D ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  have hD : Module.finrank K D = 3 := by
    have hlin : LinearIndependent K (fun i : Fin 3 => (f i : ι → K)) :=
      hf.map' U.subtype (by rw [LinearMap.ker_eq_bot]; exact Subtype.coe_injective)
    have h := finrank_span_eq_card hlin
    simpa [D, Fintype.card_fin] using h
  obtain ⟨p, hpD, hp0, hQp⟩ :=
    CFSG.RankThree.GF2n.Stroth80.sec7_exists_singular_of_finrank_three Q D hD
  exact ⟨p, hDle hpD, hp0, hQp⟩

theorem s16g_exists_singular_of_nofix [CharP K 2] (Q : QuadraticForm K (ι → K)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (g : Matrix.GeneralLinearGroup ι K) (hg : g ^ p = 1) (U : Submodule K (ι → K)) (hU : U ≠ ⊥)
    (hUg : ∀ u ∈ U, (g : Matrix ι ι K) *ᵥ u ∈ U)
    (hnofix : ∀ u ∈ U, (g : Matrix ι ι K) *ᵥ u = u → u = 0) :
    ∃ u ∈ U, u ≠ 0 ∧ Q u = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let f : (ι → K) ≃ₗ[K] (ι → K) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have hf_apply : ∀ v : ι → K, f v = (g : Matrix ι ι K) *ᵥ v := by
    intro v
    change ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv) v
      = (g : Matrix ι ι K) *ᵥ v
    rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
  have hfpow : f ^ p = 1 := by
    change ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K))
        (Matrix.GeneralLinearGroup.toLin g)) ^ p = 1
    rw [← map_pow, ← map_pow, hg, map_one, map_one]
  have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => by rw [hf_apply]; exact hUg u hu
  have hmapU : U.map (f : (ι → K) →ₗ[K] (ι → K)) ≤ U :=
    Submodule.map_le_iff_le_comap.mpr hfU
  have hmapU_eq : U.map (f : (ι → K) →ₗ[K] (ι → K)) = U :=
    Submodule.eq_of_le_of_finrank_le hmapU (by rw [LinearEquiv.finrank_map_eq])
  have hf_inv_U : ∀ u ∈ U, f.symm u ∈ U := by
    intro u hu
    have hcomap : U ≤ U.comap (f.symm : (ι → K) →ₗ[K] (ι → K)) := by
      rw [← Submodule.map_equiv_eq_comap_symm f U]
      exact hmapU_eq.ge
    exact hcomap hu
  let gU : U ≃ₗ[K] U :=
    { toFun := fun u => ⟨f u, hfU u u.2⟩
      invFun := fun u => ⟨f.symm u, hf_inv_U u u.2⟩
      left_inv := fun u => Subtype.ext (f.symm_apply_apply u)
      right_inv := fun u => Subtype.ext (f.apply_symm_apply u)
      map_add' := fun u v => Subtype.ext (by
        change f ((u : ι → K) + (v : ι → K)) = f (u : ι → K) + f (v : ι → K)
        exact map_add f _ _)
      map_smul' := fun r u => Subtype.ext (by
        change f (r • (u : ι → K)) = r • f (u : ι → K)
        exact map_smul f _ _) }
  have hgU_pow : gU ^ p = 1 := by
    ext u
    have hiter : ∀ n : ℕ, ((gU ^ n) u : ι → K) = (f ^ n) u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', LinearEquiv.mul_apply]
          change (f ((gU ^ n) u) : ι → K) = (f ^ (n + 1)) u
          rw [ih, pow_succ']
          rfl
    rw [hiter p, hfpow]
    rfl
  have hgU_ne : gU ≠ 1 := by
    intro h
    obtain ⟨u₀, hu₀U, hu₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have h1 : f u₀ = u₀ := by
      have h2 := congrArg (fun e : U ≃ₗ[K] U => (e ⟨u₀, hu₀U⟩ : ι → K)) h
      simpa [gU] using h2
    have h3 : (g : Matrix ι ι K) *ᵥ u₀ = u₀ := by rwa [hf_apply] at h1
    exact hu₀ (hnofix u₀ hu₀U h3)
  have horder : orderOf gU = p := orderOf_eq_prime hgU_pow hgU_ne
  haveI : Module.Finite K U := Module.Finite.of_injective U.subtype Subtype.coe_injective
  have hcardz : Nat.card ↥(Subgroup.zpowers gU) = p := by
    rw [Nat.card_zpowers, horder]
  haveI hGp : IsPGroup p ↥(Subgroup.zpowers gU) :=
    IsPGroup.of_card (n := 1) (by rw [hcardz, pow_one])
  letI : MulAction ↥(Subgroup.zpowers gU) U :=
    MulAction.compHom U (Subgroup.subtype (Subgroup.zpowers gU))
  have hfixset : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers gU) U) = 1 := by
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨(0 : U), ?_⟩⟩⟩
    · have ha : (a : U) = 0 := by
        have h'mem := a.2 (⟨gU, Subgroup.mem_zpowers gU⟩ : ↥(Subgroup.zpowers gU))
        rw [MulAction.compHom_smul_def] at h'mem
        have h2 : gU (a : U) = (a : U) := by simpa using h'mem
        have h3 : (g : Matrix ι ι K) *ᵥ (a : ι → K) = (a : ι → K) := by
          have h4 := congrArg (fun x : U => (x : ι → K)) h2
          simpa [gU, hf_apply] using h4
        exact Subtype.ext (hnofix (a : ι → K) (a : U).2 h3)
      have hb : (b : U) = 0 := by
        have h'mem := b.2 (⟨gU, Subgroup.mem_zpowers gU⟩ : ↥(Subgroup.zpowers gU))
        rw [MulAction.compHom_smul_def] at h'mem
        have h2 : gU (b : U) = (b : U) := by simpa using h'mem
        have h3 : (g : Matrix ι ι K) *ᵥ (b : ι → K) = (b : ι → K) := by
          have h4 := congrArg (fun x : U => (x : ι → K)) h2
          simpa [gU, hf_apply] using h4
        exact Subtype.ext (hnofix (b : ι → K) (b : U).2 h3)
      rw [ha, hb]
    · intro m
      exact smul_zero m
  have hmod := hGp.card_modEq_card_fixedPoints U
  rw [hfixset] at hmod
  have hdvd : p ∣ Nat.card U - 1 := (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm
  have hcardU : Nat.card U = Nat.card K ^ Module.finrank K U := Module.natCard_eq_pow_finrank
  rw [hcardU] at hdvd
  have hn3 : 3 ≤ Module.finrank K U := by
    by_contra h
    have hnle : Module.finrank K U ≤ 2 := by omega
    have hnge : 1 ≤ Module.finrank K U := by
      obtain ⟨u₀, hu₀U, hu₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      have hpos : 0 < Module.finrank K U :=
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨u₀, hu₀U⟩, fun hh => hu₀ (Subtype.ext_iff.mp hh)⟩
      omega
    set n := Module.finrank K U with hn
    have hdvd' : p ∣ Nat.card K ^ n - 1 := by simpa [hn] using hdvd
    interval_cases n
    · exact hpq (dvd_trans hdvd'
        (by simpa using Nat.sub_one_dvd_pow_sub_one (Nat.card K) 2))
    · exact hpq (by simpa using hdvd')
  exact s16g_exists_singular_of_finrank_ge_three Q U hn3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
