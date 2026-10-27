module

public import CFSG.RankThree.GF2n.Smith81.TiD3Module

public section

namespace CFSG.RankThree.GF2n.Smith81

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

namespace D2

variable {K : Type*} [Field K]

theorem eq_uSL_of_mulVec_single {g : SL(2, K)}
    (h : (g : Mat2 K) *ᵥ (Pi.single 0 1) = Pi.single 0 1) : g = uSL ((g : Mat2 K) 0 1) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, Fin.isValue,
    one_ne_zero, ↓reduceIte, mul_one, mul_zero, add_zero, zero_ne_one] at h0 h1
  have hdet := g.2
  rw [Matrix.det_fin_two, h0, h1] at hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uSL, h0, h1] <;> linear_combination hdet

theorem two_dvd_card [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.pos.ne'

theorem exists_conj_stabilizer [Finite K] [CharP K 2] {R : Subgroup SL(2, K)}
    (hR2 : IsPGroup 2 R) (hRcard : Nat.card K ≤ Nat.card R) :
    ∃ (h : SL(2, K)) (v : Fin 2 → K), v ≠ 0 ∧ (h : Mat2 K) *ᵥ (Pi.single 0 1) = v ∧
      ∀ a : K, h * uSL a * h⁻¹ ∈ R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥R (Fin 2 → K) :=
    { smul := fun r v => ((r : SL(2, K)) : Mat2 K).mulVec v
      one_smul := fun v => by
        show (((1 : ↥R) : SL(2, K)) : Mat2 K).mulVec v = v
        simp
      mul_smul := fun a b v => by
        show (((a : SL(2, K)) * (b : SL(2, K)) : SL(2, K)) : Mat2 K).mulVec v =
          ((a : SL(2, K)) : Mat2 K).mulVec (((b : SL(2, K)) : Mat2 K).mulVec v)
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] }
  have hdvd : 2 ∣ Nat.card (Fin 2 → K) := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact Dvd.dvd.pow two_dvd_card (by norm_num)
  have h0 : (0 : Fin 2 → K) ∈ MulAction.fixedPoints ↥R (Fin 2 → K) := by
    rw [MulAction.mem_fixedPoints]
    intro r
    show ((r : SL(2, K)) : Mat2 K).mulVec 0 = 0
    simp
  obtain ⟨v, hv, hv0⟩ := hR2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 2 → K) hdvd h0
  rw [MulAction.mem_fixedPoints] at hv
  have hvr : ∀ r : ↥R, ((r : SL(2, K)) : Mat2 K).mulVec v = v := hv
  obtain ⟨h, hh⟩ := exists_sl_mulVec_single hv0.symm
  have hstab : ∀ r : ↥R, (((h⁻¹ * (r : SL(2, K)) * h : SL(2, K))) : Mat2 K) *ᵥ (Pi.single 0 1) =
      Pi.single 0 1 := by
    intro r
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh, hvr r, ← hh, Matrix.mulVec_mulVec,
      sl_inv_mul, Matrix.one_mulVec]
  let f : ↥R → K := fun r => ((h⁻¹ * (r : SL(2, K)) * h : SL(2, K)) : Mat2 K) 0 1
  have hf : ∀ r : ↥R, h⁻¹ * (r : SL(2, K)) * h = uSL (f r) := fun r =>
    eq_uSL_of_mulVec_single (hstab r)
  have hfinj : Function.Injective f := by
    intro r r' hrr
    have h1 : h⁻¹ * (r : SL(2, K)) * h = h⁻¹ * (r' : SL(2, K)) * h := by
      rw [hf r, hf r', hrr]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hRcard
  refine ⟨h, v, hv0.symm, hh, fun a => ?_⟩
  obtain ⟨r, hr⟩ := hbij.2 a
  have := hf r
  rw [hr] at this
  have e : h * uSL a * h⁻¹ = (r : SL(2, K)) := by
    rw [← this]
    group
  rw [e]
  exact r.2

end D2

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3Key

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}
  {F : Type} [Field F] [Finite F] [Algebra K F]

namespace D3Data

variable (D : D3Data Q Z M₀ φS F)

theorem fix_U {f : M₀.E} (hf : ∀ a : F, ∃ s : ↥S, D.p s = D2.uSL a ∧ φS s f = f) :
    ∃ c : K, f = c • D.ptv (Pi.single 0 1) := by
  classical
  have hfix : ∀ a : F, D3.act (FiniteField.frobeniusAlgHom K F : F →+* F)
      ((D2.uSL a : SL(2, F)) : Mat2 F) (D.θ f : D3.Hyp F) = (D.θ f : D3.Hyp F) := by
    intro a
    obtain ⟨s, hs, hsf⟩ := hf a
    have := D.act s f
    rw [hsf, hs] at this
    exact this.symm
  haveI : Fintype F := Fintype.ofFinite F
  have hqK : Fintype.card K = Fintype.card K := rfl
  have hq2 : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hF3 : Fintype.card F = Fintype.card K ^ 3 := by
    rw [← Nat.card_eq_fintype_card, D.card_F, ← Nat.card_eq_fintype_card]
  obtain ⟨c, hc⟩ := D3.fix_U_line hqK hq2 hF3 (FiniteField.frobeniusAlgHom K F)
    (fun a => by rw [FiniteField.coe_frobeniusAlgHom]) (D.θ f).2 hfix
  refine ⟨c, D.θ.injective ?_⟩
  apply Subtype.ext
  rw [map_smul, Submodule.coe_smul, D.θ_ptv, ← D3.e0_eq_pt, hc]
  funext i j k
  simp [Algebra.smul_def]

theorem fixed_in_line [CharP F 2] {R : Subgroup SL(2, F)} (hR2 : IsPGroup 2 R)
    (hRcard : Nat.card F ≤ Nat.card R) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ e : M₀.E, (∀ m : ↥S, D.p m ∈ R → φS m e = e) →
      ∃ μ : K, e = μ • D.ptv w := by
  classical
  obtain ⟨h, v, hv0, hhv, hR⟩ := D2.exists_conj_stabilizer hR2 hRcard
  refine ⟨v, hv0, fun e he => ?_⟩
  obtain ⟨mh, hmh⟩ := D.surj h
  set f : M₀.E := φS mh⁻¹ e with hfdef
  have hef : e = φS mh f := by
    rw [hfdef, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  obtain ⟨c, hfc⟩ := D.fix_U (f := f) fun a => by
    obtain ⟨ma, hma⟩ := D.surj (D2.uSL a)
    have h1 : D.p (mh * ma * mh⁻¹) = h * D2.uSL a * h⁻¹ := by
      rw [map_mul, map_mul, map_inv, hmh, hma]
    have h2 : φS (mh * ma * mh⁻¹) e = e := he _ (by rw [h1]; exact hR a)
    have h3 : φS ma f = f := by
      have h4 : φS (mh⁻¹ * (mh * ma * mh⁻¹)) e = f := by
        rw [map_mul, LinearEquiv.mul_apply, h2]
      rw [show mh⁻¹ * (mh * ma * mh⁻¹) = ma * mh⁻¹ by group, map_mul,
        LinearEquiv.mul_apply] at h4
      exact h4
    exact ⟨ma, hma, h3⟩
  refine ⟨c, ?_⟩
  rw [hef, hfc, map_smul, D.φS_ptv, hmh, hhv]

end D3Data

end D3Key

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

namespace D2

@[expose] def diagSL {K : Type*} [Field K] (μ : K) (hμ : μ ≠ 0) : SL(2, K) :=
  ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩

theorem coe_diagSL {K : Type*} [Field K] (μ : K) (hμ : μ ≠ 0) :
    ((diagSL μ hμ : SL(2, K)) : Mat2 K) = !![μ, 0; 0, μ⁻¹] := rfl

end D2

@[expose] def conjS {G : Type} [Group G] {S H : Subgroup G}
    (hnorm : ∀ m ∈ H, ∀ s ∈ S, m * s * m⁻¹ ∈ S) (x : G) (hx : x ∈ H) : ↥S →* ↥S where
  toFun s := ⟨x * s * x⁻¹, hnorm x hx s s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    show x * ((a : G) * (b : G)) * x⁻¹ = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹)
    group)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3R3

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}
  {F : Type} [Field F] [Finite F] [Algebra K F]

namespace D3Data

variable (D : D3Data Q Z M₀ φS F)

include D in
theorem cube_mem [CharP F 2] (hK4 : 4 ≤ Nat.card K)
    {H : Subgroup G} (hSH : S ≤ H) (hQS : Q ≤ S)
    (hnorm : ∀ m ∈ H, ∀ s ∈ S, m * s * m⁻¹ ∈ S)
    (hQnorm : ∀ m ∈ H, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q)
    (hcent : ∀ h ∈ H, (∀ x ∈ S, ⁅h, x⁆ ∈ Q) → h ∈ Q)
    (φ : ↥H →* (M₀.E ≃ₗ[K] M₀.E)) (hφS : ∀ m : ↥S, φS m = φ ⟨m, hSH m.2⟩)
    {m : G} (hm : m ∈ H) : m ^ 3 ∈ S := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hF3 : Fintype.card F = Fintype.card K ^ 3 := by
    rw [← Nat.card_eq_fintype_card, D.card_F, ← Nat.card_eq_fintype_card]
  have hF4 : 4 ≤ Nat.card F := by
    rw [D.card_F]
    calc 4 ≤ Nat.card K := hK4
      _ ≤ Nat.card K ^ 3 := Nat.le_self_pow (by norm_num) _
  let c : ↥S →* ↥S := conjS hnorm m hm
  have hker : D.p.ker ≤ (D.p.comp c).ker := fun s hs => by
    rw [MonoidHom.mem_ker] at hs ⊢
    show D.p (c s) = 1
    exact (D.ker_iff _).mpr (hQnorm m hm s ((D.ker_iff s).mp hs))
  let α : SL(2, F) →* SL(2, F) := D.p.liftOfRightInverse (Function.surjInv D.surj)
    (Function.rightInverse_surjInv D.surj) ⟨D.p.comp c, hker⟩
  have hα : ∀ s, α (D.p s) = D.p (c s) := fun s =>
    D.p.liftOfRightInverse_comp_apply (Function.surjInv D.surj)
      (Function.rightInverse_surjInv D.surj) ⟨D.p.comp c, hker⟩ s
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro A hA
    obtain ⟨s, rfl⟩ := D.surj A
    rw [hα] at hA
    have h1 : (m * s * m⁻¹ : G) ∈ Q := (D.ker_iff _).mp hA
    have h2 := hQnorm m⁻¹ (H.inv_mem hm) _ h1
    rw [show m⁻¹ * (m * (s : G) * m⁻¹) * m⁻¹⁻¹ = s by group] at h2
    exact (D.ker_iff s).mpr h2
  have hαsurj : Function.Surjective α := by
    intro A
    obtain ⟨s', rfl⟩ := D.surj A
    refine ⟨D.p ⟨m⁻¹ * s' * m⁻¹⁻¹, hnorm m⁻¹ (H.inv_mem hm) s' s'.2⟩, ?_⟩
    rw [hα]
    congr 1
    exact Subtype.ext (by show m * (m⁻¹ * (s' : G) * m⁻¹⁻¹) * m⁻¹ = s'; group)
  let αe : MulAut SL(2, F) := MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩
  obtain ⟨g, σ', hg⟩ := autSL2 F hF4 αe
  obtain ⟨s₀, hs₀⟩ := D.surj g
  set m' : G := (s₀ : G)⁻¹ * m with hm'def
  have hs₀H : (s₀ : G) ∈ H := hSH s₀.2
  have hm'H : m' ∈ H := H.mul_mem (H.inv_mem hs₀H) hm
  let c' : ↥S →* ↥S := conjS hnorm m' hm'H
  have hc' : ∀ s : ↥S, D.p (c' s) = D2.slMap σ' (D.p s) := by
    intro s
    have h1 : c' s = s₀⁻¹ * c s * s₀ := Subtype.ext (by
      show m' * (s : G) * m'⁻¹ = (s₀ : G)⁻¹ * (m * s * m⁻¹) * s₀
      rw [hm'def]
      group)
    have h2 : D.p (c s) = g * D2.slMap σ' (D.p s) * g⁻¹ := by
      rw [← hα]
      exact hg (D.p s)
    rw [h1, map_mul, map_mul, map_inv, hs₀, h2]
    group
  let Φ : M₀.E ≃ₗ[K] M₀.E := φ ⟨m', hm'H⟩
  have hΦ : ∀ (s : ↥S) (x : M₀.E), φS (c' s) x = Φ (φS s (Φ⁻¹ x)) := by
    intro s x
    have h1 : φS (c' s) = φ ⟨m', hm'H⟩ * φS s * (φ ⟨m', hm'H⟩)⁻¹ := by
      rw [hφS, hφS, ← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    rfl
  set v₀ : M₀.E := D.ptv (Pi.single 0 1) with hv₀
  have hv₀0 : v₀ ≠ 0 := D.ptv_ne_zero (by
    intro h
    have := congrFun h 0
    simp at this)
  have hfixe : ∀ s : ↥S, ((D.p s : SL(2, F)) : Mat2 F) *ᵥ (Pi.single 0 1) = Pi.single 0 1 →
      φS s v₀ = v₀ := by
    intro s hs
    rw [hv₀, D.φS_ptv, hs]
  have hΦinv : ∀ x : M₀.E, Φ⁻¹ (Φ x) = x := fun x => by
    show (Φ⁻¹ * Φ) x = x
    rw [inv_mul_cancel]
    rfl
  have h7b : ∀ a : F, ∃ s : ↥S, D.p s = D2.uSL a ∧ φS s (Φ v₀) = Φ v₀ := by
    intro a
    obtain ⟨sa, hsa⟩ := D.surj (D2.uSL a)
    let t : ↥S := conjS hnorm m'⁻¹ (H.inv_mem hm'H) sa
    have hct : c' t = sa := Subtype.ext (by
      show m' * (m'⁻¹ * (sa : G) * m'⁻¹⁻¹) * m'⁻¹ = sa
      group)
    have h1 : D2.slMap σ' (D.p t) = D2.uSL a := by rw [← hc' t, hct, hsa]
    have h2 : ((D.p t : SL(2, F)) : Mat2 F) *ᵥ (Pi.single 0 1) = Pi.single 0 1 := by
      have e00 : σ' (((D.p t : SL(2, F)) : Mat2 F) 0 0) = 1 := by
        have := congrArg (fun A : SL(2, F) => (A : Mat2 F) 0 0) h1
        simpa [D2.coe_slMap, D2.uSL] using this
      have e10 : σ' (((D.p t : SL(2, F)) : Mat2 F) 1 0) = 0 := by
        have := congrArg (fun A : SL(2, F) => (A : Mat2 F) 1 0) h1
        simpa [D2.coe_slMap, D2.uSL] using this
      have a00 : ((D.p t : SL(2, F)) : Mat2 F) 0 0 = 1 :=
        σ'.injective (by rw [e00, map_one])
      have a10 : ((D.p t : SL(2, F)) : Mat2 F) 1 0 = 0 :=
        σ'.injective (by rw [e10, map_zero])
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, a00, a10]
    refine ⟨sa, hsa, ?_⟩
    have h3 := hΦ t (Φ v₀)
    rw [hct, hΦinv, hfixe t h2] at h3
    exact h3
  obtain ⟨cc, hcc⟩ := D.fix_U h7b
  have hcc0 : cc ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcc
    exact hv₀0 (Φ.injective (by rw [hcc, map_zero]))
  have hN : ∀ x : F, x * (FiniteField.frobeniusAlgHom K F) x *
      (FiniteField.frobeniusAlgHom K F) ((FiniteField.frobeniusAlgHom K F) x) =
        x ^ (1 + Fintype.card K + Fintype.card K ^ 2) := by
    intro x
    rw [FiniteField.coe_frobeniusAlgHom]
    beta_reduce
    ring
  have htorus : ∀ (μ : F) (hμ : μ ≠ 0), (σ' μ) ^ (1 + Fintype.card K + Fintype.card K ^ 2) =
      μ ^ (1 + Fintype.card K + Fintype.card K ^ 2) := by
    intro μ hμ
    obtain ⟨sμ, hsμ⟩ := D.surj (D2.diagSL μ hμ)
    have hmv : ((D.p sμ : SL(2, F)) : Mat2 F) *ᵥ (Pi.single 0 1) = μ • (Pi.single 0 1) := by
      rw [hsμ]
      ext i
      fin_cases i <;> simp [D2.diagSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Pi.single_apply]
    obtain ⟨κ, hκ, hκv⟩ := D.ptv_smul μ (Pi.single 0 1)
    have hφ1 : φS sμ v₀ = κ • v₀ := by rw [hv₀, D.φS_ptv, hmv, hκv]
    have e00 : ((D.p (c' sμ) : SL(2, F)) : Mat2 F) 0 0 = σ' μ := by
      rw [hc', hsμ, D2.coe_slMap, D2.coe_diagSL]
      simp
    have e10 : ((D.p (c' sμ) : SL(2, F)) : Mat2 F) 1 0 = 0 := by
      rw [hc', hsμ, D2.coe_slMap, D2.coe_diagSL]
      simp
    have hmv' : ((D.p (c' sμ) : SL(2, F)) : Mat2 F) *ᵥ (Pi.single 0 1) =
        σ' μ • (Pi.single 0 1) := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply, e00,
        e10]
    obtain ⟨κ', hκ', hκ'v⟩ := D.ptv_smul (σ' μ) (Pi.single 0 1)
    have hφ2 : φS (c' sμ) v₀ = κ' • v₀ := by rw [hv₀, D.φS_ptv, hmv', hκ'v]
    have e1 : φS (c' sμ) (Φ v₀) = κ • (cc • v₀) := by
      rw [hΦ, hΦinv, hφ1, map_smul, hcc]
    have e2 : φS (c' sμ) (Φ v₀) = cc • (κ' • v₀) := by
      rw [hcc, map_smul, hφ2]
    have e3 : (κ * cc) • v₀ = (cc * κ') • v₀ := by
      rw [mul_smul, mul_smul, ← e1, e2]
    have e4 : κ * cc = cc * κ' := smul_left_injective K hv₀0 e3
    have e5 : κ = κ' := mul_right_cancel₀ hcc0 (by rw [e4, mul_comm])
    rw [← hN, ← hN, ← hκ, ← hκ', e5]
  have hσK : ∀ κ₀ : K, σ' (algebraMap K F κ₀) = algebraMap K F κ₀ := by
    intro κ₀
    by_cases h0 : κ₀ = 0
    · rw [h0, map_zero, map_zero]
    obtain ⟨μ, hμ0, hμ⟩ := D3.exists_nrm_eq hF3 hq2 κ₀ h0
    rw [hμ, map_pow, htorus μ hμ0]
  have hσ3 : σ' ^ 3 = 1 := D3.aut_pow_three D.finrank_F σ' hσK
  have hpow : ∀ n : ℕ, (m' ^ n) ∈ H := fun n => H.pow_mem hm'H n
  have hitero : ∀ (n : ℕ) (s : ↥S),
      D.p (conjS hnorm (m' ^ n) (hpow n) s) = D2.slMap (σ' ^ n) (D.p s) := by
    intro n
    induction n with
    | zero =>
      intro s
      have : conjS hnorm (m' ^ 0) (hpow 0) s = s := Subtype.ext (by
        show m' ^ 0 * (s : G) * (m' ^ 0)⁻¹ = s
        simp)
      rw [this, pow_zero, D2.slMap_one]
    | succ n ih =>
      intro s
      have h1 : conjS hnorm (m' ^ (n + 1)) (hpow (n + 1)) s =
          c' (conjS hnorm (m' ^ n) (hpow n) s) := Subtype.ext (by
        show m' ^ (n + 1) * (s : G) * (m' ^ (n + 1))⁻¹ =
          m' * (m' ^ n * (s : G) * (m' ^ n)⁻¹) * m'⁻¹
        rw [pow_succ']
        group)
      rw [h1, hc', ih, ← D2.slMap_mul, pow_succ']
  have hQ3 : m' ^ 3 ∈ Q := by
    refine hcent _ (hpow 3) fun x hx => ?_
    have h1 : D.p (conjS hnorm (m' ^ 3) (hpow 3) ⟨x, hx⟩) = D.p ⟨x, hx⟩ := by
      rw [hitero, hσ3, D2.slMap_one]
    have h2 : D.p (conjS hnorm (m' ^ 3) (hpow 3) ⟨x, hx⟩ * ⟨x, hx⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (D.ker_iff _).mp h2
    rw [commutatorElement_def]
    exact h3
  have hm3 : m ^ 3 = (s₀ : G) * (m' * s₀ * m'⁻¹) * (m' ^ 2 * s₀ * (m' ^ 2)⁻¹) * m' ^ 3 := by
    have hm : m = (s₀ : G) * m' := by rw [hm'def]; group
    conv_lhs => rw [pow_three, hm]
    group
  rw [hm3]
  refine S.mul_mem (S.mul_mem (S.mul_mem s₀.2 (hnorm m' hm'H s₀ s₀.2))
    (hnorm (m' ^ 2) (hpow 2) s₀ s₀.2)) (hQS hQ3)

end D3Data

end D3R3

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section D3Two

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {S : Subgroup G} {φS : ↥S →* (M₀.E ≃ₗ[K] M₀.E)}
  {F : Type} [Field F] [Finite F] [Algebra K F]

namespace D3Data

variable (D : D3Data Q Z M₀ φS F)

theorem fixed_in_line_of_card [CharP F 2] {T : Subgroup G} (hTS : T ≤ S)
    (hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) ∈ Q)
    (hcard : Nat.card F * Nat.card ↥(T ⊓ Q) ≤ Nat.card T) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧ ∀ e : M₀.E,
      (∀ (t : G) (ht : t ∈ T), φS ⟨t, hTS ht⟩ e = e) → ∃ μ : K, e = μ • D.ptv w := by
  classical
  let f : ↥T →* SL(2, F) := D.p.comp (Subgroup.inclusion hTS)
  have hkerQ : ∀ k : f.ker, ((k : ↥T) : G) ∈ T ⊓ Q := fun k =>
    ⟨k.1.2, (D.ker_iff _).mp (MonoidHom.mem_ker.mp k.2)⟩
  have hker : Nat.card f.ker ≤ Nat.card ↥(T ⊓ Q) :=
    Nat.card_le_card_of_injective
      (fun k : f.ker => (⟨((k : ↥T) : G), hkerQ k⟩ : ↥(T ⊓ Q)))
      (fun a b h => by
        have := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext this))
  have h1 : Nat.card f.ker * f.ker.index = Nat.card T := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have hpos : 0 < Nat.card ↥(T ⊓ Q) := Nat.card_pos
  have hRcard : Nat.card F ≤ Nat.card f.range := by
    have h3 : Nat.card F * Nat.card ↥(T ⊓ Q) ≤ Nat.card ↥(T ⊓ Q) * Nat.card f.range := by
      calc Nat.card F * Nat.card ↥(T ⊓ Q) ≤ Nat.card T := hcard
        _ = Nat.card f.ker * Nat.card f.range := by rw [← h1, h2]
        _ ≤ Nat.card ↥(T ⊓ Q) * Nat.card f.range := Nat.mul_le_mul_right _ hker
    rw [mul_comm] at h3
    exact Nat.le_of_mul_le_mul_left h3 hpos
  have hR2 : IsPGroup 2 f.range := by
    rintro ⟨r, t, rfl⟩
    obtain ⟨k, hk⟩ := hT2 t t.2
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (f t) ^ (2 ^ k) = 1
    rw [← map_pow]
    exact (D.ker_iff (Subgroup.inclusion hTS (t ^ (2 ^ k)))).mpr (by simpa using hk)
  obtain ⟨w, hw0, hw⟩ := D.fixed_in_line hR2 hRcard
  refine ⟨w, hw0, fun e he => hw e fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := hm
  rw [D.φS_eq_of_p_eq ht.symm]
  exact he t t.2

theorem exists_B_ne_zero [CharP F 2] {t : ↥S} (ht1 : D.p t ≠ 1) (ht2 : D.p t * D.p t = 1)
    (hBinv : ∀ (m : ↥S) (e f : M₀.E), M₀.B (φS m e) (φS m f) = M₀.B e f) :
    ∃ v : M₀.E, M₀.B v (φS t v) ≠ 0 := by
  obtain ⟨g, a, ha, hga⟩ := D2.exists_conj_u ht1 ht2
  obtain ⟨mg, hmg⟩ := D.surj g
  obtain ⟨mu, hmu⟩ := D.surj (D2.uSL a)
  set v₀ := D.ptv (Pi.single 1 1) with hv₀
  refine ⟨φS mg v₀, ?_⟩
  have h1 : φS t (φS mg v₀) = φS mg (φS mu v₀) := by
    have : D.p (t * mg) = D.p (mg * mu) := by
      rw [map_mul, map_mul, hmg, hmu, hga]
      group
    rw [← LinearEquiv.mul_apply, ← map_mul, D.φS_eq_of_p_eq this, map_mul,
      LinearEquiv.mul_apply]
  rw [h1, hBinv]
  intro h0
  have hw2 : ((D.p mu : SL(2, F)) : Mat2 F) *ᵥ (Pi.single 1 1) = ![a, 1] := by
    rw [hmu]
    ext i
    fin_cases i <;> simp [D2.uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  have h2 := D.algebraMap_B_ptv (Pi.single 1 1) ((D.p mu : Mat2 F) *ᵥ Pi.single 1 1)
  rw [← D.φS_ptv mu, ← hv₀, h0, map_zero, hw2] at h2
  simp only [Pi.single_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_ne_one, ↓reduceIte, one_ne_zero, zero_mul, one_mul, zero_add] at h2
  have hτ : ∀ x : F, x ≠ 0 → (FiniteField.frobeniusAlgHom K F) x ≠ 0 := fun x hx =>
    (map_ne_zero (FiniteField.frobeniusAlgHom K F)).mpr hx
  exact mul_ne_zero (mul_ne_zero ha (hτ _ ha)) (hτ _ (hτ _ ha)) h2.symm

include D in
theorem card_le_mul [CharP F 2] {T : Subgroup G} (hTS : T ≤ S) (hT2 : IsPGroup 2 T) :
    Nat.card T ≤ Nat.card ↥(T ⊓ Q) * Nat.card F := by
  classical
  let f : ↥T →* SL(2, F) := D.p.comp (Subgroup.inclusion hTS)
  have hkerQ : ∀ k : f.ker, ((k : ↥T) : G) ∈ T ⊓ Q := fun k =>
    ⟨k.1.2, (D.ker_iff _).mp (MonoidHom.mem_ker.mp k.2)⟩
  have hker : Nat.card f.ker ≤ Nat.card ↥(T ⊓ Q) :=
    Nat.card_le_card_of_injective
      (fun k : f.ker => (⟨((k : ↥T) : G), hkerQ k⟩ : ↥(T ⊓ Q)))
      (fun a b h => by
        have := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext this))
  have h1 : Nat.card f.ker * f.ker.index = Nat.card T := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  have h3 : Nat.card f.range ≤ Nat.card F :=
    D2.card_le_of_isPGroup_sl2 (hT2.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  calc Nat.card T = Nat.card f.ker * Nat.card f.range := by rw [← h1, h2]
    _ ≤ Nat.card ↥(T ⊓ Q) * Nat.card F := Nat.mul_le_mul hker h3

end D3Data

end D3Two

end

end CFSG.RankThree.GF2n.Smith81
