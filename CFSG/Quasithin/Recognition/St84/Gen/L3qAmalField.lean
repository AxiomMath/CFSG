module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalLocal
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalCoord

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.ClassicalGroups.PCoreSection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem ActsByMatrix.mul {G : Type*} [Group G] {F : Type*} [Field F] {n : ℕ}
    {Q : Subgroup G} {β : ↥Q ≃* Multiplicative (Fin n → F)} {p q : G}
    (hnormq : ∀ x : ↥Q, ∃ y : ↥Q, (y : G) = q * x * q⁻¹)
    {A B : Matrix (Fin n) (Fin n) F}
    (hA : ActsByMatrix β p A) (hB : ActsByMatrix β q B) :
    ActsByMatrix β (p * q) (A * B) := by
  intro x y hy
  obtain ⟨z, hz⟩ := hnormq x
  have hy' : (y : G) = p * z * p⁻¹ := by
    rw [hy, hz]
    group
  rw [hA z y hy', hB x z hz, Matrix.mulVec_mulVec]

private lemma actsByMatrix_alpha {L S : Subgroup G} {F : Type*} [Field F]
    (c : VertexCoord L S F) (x : ↥L) :
    ActsByMatrix c.β (x : G) (c.α x : Matrix (Fin 2) (Fin 2) F) := by
  intro u v hv
  let w : ↥(pCoreOf 2 L) :=
    ⟨(x : G) * (u : G) * (x : G)⁻¹, PCoreSection.conj_mem_pCoreOf x.2 u.2⟩
  have hw : w = v := Subtype.ext (by simpa [w] using hv.symm)
  rw [← hw]
  exact c.equivariant x u w rfl

private lemma upperTri_mulVec_zero {F : Type*} [Field F] (ν : Fˣ) (r w : F) :
    (!![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) *ᵥ ![w, 0] =
      ![(ν : F) * w, 0] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, Fin.sum_univ_two]

private lemma conj_mem_of_mem_normalizer {Q : Subgroup G} {b x : G}
    (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) :
    b * x * b⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp hb x).mp hx

private theorem exists_gl_of_mem_borel {F : Type*} [Field F] [Finite F]
    (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f)
    (c₁ : VertexCoord L1 S F) (c₂ : VertexCoord L2 S F)
    (ρ : F ≃+* F) (e₁ e₂ : Fˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      Multiplicative.toAdd (c₁.β z₁) 1 = 0 ∧ Multiplicative.toAdd (c₂.β z₂) 1 = 0 ∧
      Multiplicative.toAdd (c₁.β z₁) 0 = e₁ * ρ (Multiplicative.toAdd (c₂.β z₂) 0))
    (h₂ : ∀ (x : ↥(pCoreOf 2 L1)) (x' : ↥L2) (t : F), (x : G) = x' →
      (c₂.α x' : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] →
      Multiplicative.toAdd (c₁.β x) 1 = e₂ * ρ t)
    (hFcard : Nat.card F = 2 ^ f)
    {b : G} (hb : b ∈ borelOf L2 S) {ν : Fˣ} {r : F}
    (hbmat : (c₂.α ⟨b, borelOf_le L2 S hb⟩ : Matrix (Fin 2) (Fin 2) F) =
      !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)]) :
    ∃ (m : F) (M : Matrix.GeneralLinearGroup (Fin 2) F),
      (M : Matrix (Fin 2) (Fin 2) F) =
        !![ρ (ν : F), m; 0, ρ (ν : F) * ρ (ν : F)] ∧
      Matrix.GeneralLinearGroup.det M = (Units.map ρ.toMonoidHom ν) ^ 3 ∧
      ActsByMatrix c₁.β b (M : Matrix (Fin 2) (Fin 2) F) := by
  classical
  have hS2 : S ≤ L2 := hD.le_right hH
  have hbL2 : b ∈ L2 := borelOf_le L2 S hb
  have hbmat' : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) F) =
      !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] := by simpa using hbmat
  have hbS : b ∈ Subgroup.normalizer (S : Set G) := by
    have h := borelOf_le_normalizer L2 S hb
    rwa [inf_eq_left.mpr hS2] at h
  have hbL1 : b ∈ Subgroup.normalizer (L1 : Set G) := hH.h1.borel_le hb
  have hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1 hbL1
  let Q1 := pCoreOf 2 L1
  let ψ : MulAut ↥Q1 := Q1.normalizerMonoidHom ⟨b, hbQ1⟩
  have hψ_apply : ∀ u : ↥Q1, (ψ u : G) = b * (u : G) * b⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q1 ⟨b, hbQ1⟩ u
  let eβ : Additive ↥Q1 ≃+ (Fin 2 → F) :=
    (MulEquiv.toAdditive c₁.β).trans (AddEquiv.additiveMultiplicative (Fin 2 → F))
  let T : (Fin 2 → F) ≃+ (Fin 2 → F) := eβ.symm.trans (ψ.toAdditive.trans eβ)
  have hT_apply : ∀ u : ↥Q1, T (Multiplicative.toAdd (c₁.β u)) =
      Multiplicative.toAdd (c₁.β (ψ u)) := by
    intro u
    have h1 : eβ (Additive.ofMul u) = Multiplicative.toAdd (c₁.β u) := by simp [eβ]
    rw [← h1]
    simp only [T, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
      MulEquiv.toAdditive_apply_apply]
    simp [eβ]
  have hTnorm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
        ∀ v : Fin 2 → F, T ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
          (A' : Matrix (Fin 2) (Fin 2) F) *ᵥ (T v) := by
    intro A
    obtain ⟨x, hx⟩ := c₁.surjective A
    let ψL : MulAut ↥L1 := L1.normalizerMonoidHom ⟨b, hbL1⟩
    let x' : ↥L1 := ψL x
    have hx'coe : (x' : G) = b * (x : G) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L1 ⟨b, hbL1⟩ x
    refine ⟨c₁.α x', fun v => ?_⟩
    obtain ⟨u, hu⟩ := c₁.β.surjective (Multiplicative.ofAdd v)
    have huv : Multiplicative.toAdd (c₁.β u) = v := congrArg Multiplicative.toAdd hu
    rw [← huv]
    let w : ↥Q1 := ⟨(x : G) * (u : G) * (x : G)⁻¹,
      PCoreSection.conj_mem_pCoreOf x.2 u.2⟩
    have hw : Multiplicative.toAdd (c₁.β w) =
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (c₁.β u) := by
      rw [← hx]
      exact c₁.equivariant x u w rfl
    have hx'Q1 : (x' : G) ∈ Subgroup.normalizer (Q1 : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L1 x'.2
    let y : ↥Q1 := ⟨(x' : G) * (ψ u : G) * (x' : G)⁻¹,
      conj_mem_of_mem_normalizer hx'Q1 (ψ u).2⟩
    have hψw : ψ w = y := by
      apply Subtype.ext
      rw [hψ_apply w]
      show b * ((x : G) * (u : G) * (x : G)⁻¹) * b⁻¹ =
        (x' : G) * (ψ u : G) * (x' : G)⁻¹
      rw [hψ_apply u, hx'coe]
      group
    have hy : Multiplicative.toAdd (c₁.β y) =
        (c₁.α x' : Matrix (Fin 2) (Fin 2) F) *ᵥ
          Multiplicative.toAdd (c₁.β (ψ u)) :=
      c₁.equivariant x' (ψ u) y rfl
    rw [← hw, hT_apply w, hψw, hy, ← hT_apply u]
  have hT' : ∀ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
        ∀ v : Fin 2 → F, T ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
          (A' : Matrix (Fin 2) (Fin 2) F) *ᵥ (T v) := by
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) F) := inferInstance
    let α : Matrix.SpecialLinearGroup (Fin 2) F → Matrix.SpecialLinearGroup (Fin 2) F :=
      fun A => Classical.choose (hTnorm A)
    have hα : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
        T ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
          (α A : Matrix (Fin 2) (Fin 2) F) *ᵥ (T v) :=
      fun A => Classical.choose_spec (hTnorm A)
    have hα_inj : Function.Injective α := by
      intro A B hAB
      apply Subtype.ext
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : (α A : Matrix (Fin 2) (Fin 2) F) *ᵥ T (Pi.single j (1 : F)) =
          (α B : Matrix (Fin 2) (Fin 2) F) *ᵥ T (Pi.single j (1 : F)) := by rw [hAB]
      have h2 : T ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single j (1 : F)) =
          T ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single j (1 : F)) := by
        rw [hα A (Pi.single j 1), hα B (Pi.single j 1), h1]
      exact T.injective h2
    have hα_surj : Function.Surjective α := Finite.injective_iff_surjective.mp hα_inj
    intro A'
    obtain ⟨A, hA⟩ := hα_surj A'
    exact ⟨A, fun v => by rw [hα A v, hA]⟩
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_of_normalizes_SL2 T hTnorm hT'
  have hℓ_mem : ∀ z : ↥(Q1 ⊓ pCoreOf 2 L2),
      Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩) 1 = 0 := fun z =>
    (h₁ ⟨z.1, z.2.1⟩ ⟨z.1, z.2.2⟩ rfl).1
  have hℓ_inj : Function.Injective
      (fun z : ↥(Q1 ⊓ pCoreOf 2 L2) =>
        Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩) 0) := by
    intro z w hzw
    have hvec : Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩) =
        Multiplicative.toAdd (c₁.β ⟨w.1, w.2.1⟩) := by
      funext i
      fin_cases i
      · exact hzw
      · simpa using (hℓ_mem z).trans (hℓ_mem w).symm
    have hβ : c₁.β ⟨z.1, z.2.1⟩ = c₁.β ⟨w.1, w.2.1⟩ :=
      Multiplicative.ofAdd.injective hvec
    have hz1 : (⟨z.1, z.2.1⟩ : ↥Q1) = ⟨w.1, w.2.1⟩ := c₁.β.injective hβ
    apply Subtype.ext
    exact congrArg (fun t : ↥Q1 => (t : G)) hz1
  have hℓ_bij : Function.Bijective
      (fun z : ↥(Q1 ⊓ pCoreOf 2 L2) =>
        Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩) 0) :=
    hℓ_inj.bijective_of_nat_card_le (by
      rw [hFcard, show Nat.card ↥(Q1 ⊓ pCoreOf 2 L2) = 2 ^ f by
        simpa [Q1] using hD.card_inf])
  have hline : ∀ z : ↥(Q1 ⊓ pCoreOf 2 L2),
      T (Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩)) =
        ![(ρ (ν : F)) * (Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩)) 0, 0] := by
    intro z
    let z1 : ↥Q1 := ⟨z.1, z.2.1⟩
    let z2 : ↥(pCoreOf 2 L2) := ⟨z.1, z.2.2⟩
    obtain ⟨hz1_2, hz2_2, hz_first⟩ := h₁ z1 z2 rfl
    let y : G := b * (z1 : G) * b⁻¹
    have hyQ1 : y ∈ Q1 := conj_mem_of_mem_normalizer hbQ1 z1.2
    have hyQ2 : y ∈ pCoreOf 2 L2 := PCoreSection.conj_mem_pCoreOf hbL2 z2.2
    let y1 : ↥Q1 := ⟨y, hyQ1⟩
    let y2 : ↥(pCoreOf 2 L2) := ⟨y, hyQ2⟩
    obtain ⟨hy1_2, hy2_2, hy_first⟩ := h₁ y1 y2 rfl
    have hβ2y : Multiplicative.toAdd (c₂.β y2) =
        ![(ν : F) * (Multiplicative.toAdd (c₂.β z2)) 0, 0] := by
      have heq := c₂.equivariant ⟨b, hbL2⟩ z2 y2 rfl
      rw [hbmat'] at heq
      have hz2vec : Multiplicative.toAdd (c₂.β z2) =
          ![(Multiplicative.toAdd (c₂.β z2)) 0, 0] := by
        funext i
        fin_cases i <;> simp [hz2_2]
      rw [heq, hz2vec, upperTri_mulVec_zero]
      simp
    have hy_first' : Multiplicative.toAdd (c₁.β y1) 0 =
        (ρ (ν : F)) * (Multiplicative.toAdd (c₁.β z1) 0) := by
      calc Multiplicative.toAdd (c₁.β y1) 0
          = e₁ * ρ (Multiplicative.toAdd (c₂.β y2) 0) := hy_first
        _ = e₁ * ρ ((ν : F) * (Multiplicative.toAdd (c₂.β z2)) 0) := by
              rw [hβ2y]
              simp
        _ = e₁ * (ρ (ν : F) * ρ (Multiplicative.toAdd (c₂.β z2) 0)) := by
              rw [map_mul]
        _ = (ρ (ν : F)) * (e₁ * ρ (Multiplicative.toAdd (c₂.β z2) 0)) := by ring
        _ = (ρ (ν : F)) * (Multiplicative.toAdd (c₁.β z1) 0) := by rw [← hz_first]
    have hψz : ψ z1 = y1 := Subtype.ext (hψ_apply z1)
    calc T (Multiplicative.toAdd (c₁.β z1))
        = Multiplicative.toAdd (c₁.β (ψ z1)) := hT_apply z1
      _ = Multiplicative.toAdd (c₁.β y1) := by rw [hψz]
      _ = ![(ρ (ν : F)) * (Multiplicative.toAdd (c₁.β z1)) 0, 0] := by
            funext i
            fin_cases i
            · exact hy_first'
            · simpa using hy1_2
  have hρν_ne : ρ (ν : F) ≠ 0 := by
    intro h0
    apply ν.ne_zero
    apply ρ.injective
    simpa using h0
  have hscale : ∀ a : F, T ![a, 0] = ![(ρ (ν : F)) * a, 0] := by
    intro a
    obtain ⟨z, hz⟩ := hℓ_bij.2 a
    have hzvec : Multiplicative.toAdd (c₁.β ⟨z.1, z.2.1⟩) = ![a, 0] := by
      funext i
      fin_cases i
      · exact hz
      · simpa using hℓ_mem z
    simpa [hzvec] using hline z
  have hφid : ∀ a : F, φ a = a := by
    intro a
    have h1 := hφ a (![1, 0] : Fin 2 → F)
    have h2 : a • (![1, 0] : Fin 2 → F) = ![a, 0] := by
      funext i
      fin_cases i <;> simp
    rw [h2, hscale a, hscale 1] at h1
    have hcoord := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at hcoord
    have hcomm : φ a * ρ (ν : F) = a * ρ (ν : F) := by
      rw [← hcoord]
      ring
    exact mul_right_cancel₀ hρν_ne hcomm
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have hTe0 : T e0 = ![(ρ (ν : F)), 0] := by
    simpa [e0] using hscale 1
  let m₂ : F := T e1 0
  let m₃ : F := T e1 1
  have hTe1 : T e1 = ![m₂, m₃] := by
    funext i
    fin_cases i <;> rfl
  have hTlin : ∀ (a : F) (v : Fin 2 → F), T (a • v) = a • T v := by
    intro a v
    rw [hφ a v, hφid a]
  have hTmat : ∀ v : Fin 2 → F, T v = !![ρ (ν : F), m₂; 0, m₃] *ᵥ v := by
    intro v
    have hv : v = v 0 • e0 + v 1 • e1 := by
      funext i
      fin_cases i <;> simp [e0, e1]
    rw [hv, map_add, hTlin, hTlin, hTe0, hTe1]
    funext i
    fin_cases i
    · simp [e0, e1, Matrix.mulVec, Fin.sum_univ_two]
      ring
    · simp [e0, e1, Matrix.mulVec, Fin.sum_univ_two]
      ring
  have hQ1_not_le : ¬ pCoreOf 2 L1 ≤ pCoreOf 2 L2 := by
    intro hle
    have hinf : pCoreOf 2 L1 ⊓ pCoreOf 2 L2 = pCoreOf 2 L1 := inf_eq_left.mpr hle
    have hc : 2 ^ (2 * f) = 2 ^ f := by
      have hcard := hD.card_inf
      rw [hinf, hD.card_left] at hcard
      exact hcard
    have hf : 1 ≤ f := hD.one_le
    have hlt : 2 ^ f < 2 ^ (2 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact (ne_of_lt hlt) hc.symm
  obtain ⟨x, hxQ1, hxQ2⟩ :=
    Set.not_subset.mp (show ¬ (Q1 : Set G) ⊆ (pCoreOf 2 L2 : Set G) from hQ1_not_le)
  have hxS : x ∈ S := hH.pCoreOf_le_left hxQ1
  have hxL2 : x ∈ L2 := hD.le_right hH hxS
  let xL2 : ↥L2 := ⟨x, hxL2⟩
  obtain ⟨t, ht⟩ := (c₂.mem_iff xL2).mp hxS
  have ht_ne : t ≠ 0 := by
    intro ht0
    apply hxQ2
    have hone : c₂.α xL2 = 1 := by
      apply Subtype.ext
      rw [ht, ht0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    exact (c₂.eq_one_iff xL2).mp hone
  have hxβ2 : Multiplicative.toAdd (c₁.β ⟨x, hxQ1⟩) 1 = e₂ * ρ t :=
    h₂ ⟨x, hxQ1⟩ xL2 t rfl ht
  let y : G := b * x * b⁻¹
  have hyQ1 : y ∈ Q1 := conj_mem_of_mem_normalizer hbQ1 hxQ1
  have hyL2 : y ∈ L2 := L2.mul_mem (L2.mul_mem hbL2 hxL2) (L2.inv_mem hbL2)
  let yL2 : ↥L2 := ⟨y, hyL2⟩
  have hb_borel : c₂.α ⟨b, hbL2⟩ ∈ CFSG.GorensteinWalter.sl2Borel F := by
    rw [CFSG.GorensteinWalter.sl2Borel,
      CFSG.GorensteinWalter.sl2_mem_stabilizer_infinity_iff, hbmat']
    simp
  have hx_sl : c₂.α xL2 = CFSG.GorensteinWalter.sl2UpperUnipotent t :=
    Subtype.ext (by simpa [CFSG.GorensteinWalter.sl2UpperUnipotent] using ht)
  have hαy : c₂.α yL2 = CFSG.GorensteinWalter.sl2UpperUnipotent ((ν : F) * (ν : F) * t) := by
    have hy_eq : yL2 = ⟨b, hbL2⟩ * xL2 * ⟨b, hbL2⟩⁻¹ := Subtype.ext rfl
    have h00 : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 = (ν : F) := by
      rw [hbmat']
      simp
    rw [hy_eq, map_mul, map_mul, map_inv, hx_sl,
      CFSG.GorensteinWalter.sl2Borel_conj_upperUnipotent hb_borel t, h00, sq]
  have hyβ2 : Multiplicative.toAdd (c₁.β ⟨y, hyQ1⟩) 1 =
      e₂ * ρ ((ν : F) * (ν : F) * t) := by
    apply h₂ ⟨y, hyQ1⟩ yL2 ((ν : F) * (ν : F) * t) rfl
    rw [hαy]
    rfl
  have hψx : ψ ⟨x, hxQ1⟩ = ⟨y, hyQ1⟩ := Subtype.ext (hψ_apply _)
  have hTy : Multiplicative.toAdd (c₁.β ⟨y, hyQ1⟩) =
      T (Multiplicative.toAdd (c₁.β ⟨x, hxQ1⟩)) := by
    rw [hT_apply ⟨x, hxQ1⟩, hψx]
  have he₂t : e₂ * ρ t ≠ 0 :=
    mul_ne_zero e₂.ne_zero ((map_ne_zero ρ).mpr ht_ne)
  have hm₃ : m₃ = ρ (ν : F) * ρ (ν : F) := by
    have hcoord := congrFun (hTy.trans (hTmat _)) 1
    have hrow : (!![ρ (ν : F), m₂; 0, m₃] *ᵥ
        Multiplicative.toAdd (c₁.β ⟨x, hxQ1⟩)) 1 = m₃ * (e₂ * ρ t) := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hxβ2]
    rw [hyβ2, hrow] at hcoord
    have hρt : ρ ((ν : F) * (ν : F) * t) = (ρ (ν : F) * ρ (ν : F)) * ρ t := by
      rw [map_mul, map_mul]
    rw [hρt] at hcoord
    have h' : (ρ (ν : F) * ρ (ν : F)) * (e₂ * ρ t) = m₃ * (e₂ * ρ t) := by
      rw [← hcoord]
      ring
    exact (mul_right_cancel₀ he₂t h').symm
  have hdet : (!![ρ (ν : F), m₂; 0, m₃] : Matrix (Fin 2) (Fin 2) F).det =
      ρ (ν : F) * ρ (ν : F) * ρ (ν : F) := by
    rw [Matrix.det_fin_two_of, hm₃]
    ring
  have hdet_ne : (!![ρ (ν : F), m₂; 0, m₃] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero hρν_ne hρν_ne) hρν_ne
  let M : Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet_ne
  have hMval : (M : Matrix (Fin 2) (Fin 2) F) = !![ρ (ν : F), m₂; 0, m₃] := by
    simp [M, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hMdet : Matrix.GeneralLinearGroup.det M = (Units.map ρ.toMonoidHom ν) ^ 3 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hMval, hdet]
    simp [Units.coe_map]
    ring
  have hMact : ActsByMatrix c₁.β b (M : Matrix (Fin 2) (Fin 2) F) := by
    intro u v hv
    have hψu : (ψ u : G) = b * (u : G) * b⁻¹ := hψ_apply u
    have hvψ : v = ψ u := Subtype.ext (by rw [hv, hψu])
    rw [hvψ, hMval]
    calc Multiplicative.toAdd (c₁.β (ψ u))
        = T (Multiplicative.toAdd (c₁.β u)) := (hT_apply u).symm
      _ = !![ρ (ν : F), m₂; 0, m₃] *ᵥ Multiplicative.toAdd (c₁.β u) := hTmat _
  exact ⟨m₂, M, by rw [hMval, hm₃], hMdet, hMact⟩

theorem L3qLocalData.linAction_left_of_pairing (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f)
    (c₁ : VertexCoord L1 S (GaloisField 2 f)) (c₂ : VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      Multiplicative.toAdd (c₁.β z₁) 1 = 0 ∧ Multiplicative.toAdd (c₂.β z₂) 1 = 0 ∧
      Multiplicative.toAdd (c₁.β z₁) 0 = e₁ * ρ (Multiplicative.toAdd (c₂.β z₂) 0))
    (h₂ : ∀ (x : ↥(pCoreOf 2 L1)) (x' : ↥L2) (t : GaloisField 2 f), (x : G) = x' →
      (c₂.α x' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
      Multiplicative.toAdd (c₁.β x) 1 = e₂ * ρ t) :
    LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) (cubeDetGL (GaloisField 2 f)) := by
  classical
  have hf0 : f ≠ 0 := by
    have hf : 1 ≤ f := hD.one_le
    omega
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  refine ⟨c₁.β, ?_, ?_⟩
  · intro p hp
    rw [hD.sup_bigB_left hH] at hp
    have hset :=
      Subgroup.coe_mul_of_right_le_normalizer_left L1 (borelOf L2 S) hH.h1.borel_le
    change p ∈ ((L1 ⊔ borelOf L2 S : Subgroup G) : Set G) at hp
    rw [hset, Set.mem_mul] at hp
    obtain ⟨x, hxL1, b, hbB2, hxb⟩ := hp
    rw [← hxb]
    have hbN : b ∈ Subgroup.normalizer (S : Set G) := by
      have h := (show b ∈ L2 ⊓ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G)
        from hbB2).2
      rwa [inf_eq_left.mpr (hD.le_right hH)] at h
    let bL2 : ↥L2 := ⟨b, borelOf_le L2 S hbB2⟩
    have hbN' : (bL2 : G) ∈ Subgroup.normalizer (S : Set G) := hbN
    obtain ⟨ν, r, hbmat⟩ :=
      c₂.exists_of_mem_normalizer (hD.le_right hH) (b := bL2) hbN'
    obtain ⟨m, M, hMval, hMdet, hMact⟩ :=
      exists_gl_of_mem_borel hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hFcard hbB2 hbmat
    let Ax : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 f) :=
      Matrix.SpecialLinearGroup.toGL (c₁.α ⟨x, hxL1⟩)
    refine ⟨Ax * M, ?_, ?_⟩
    · apply Subgroup.mul_mem
      · rw [cubeDetGL, Subgroup.mem_comap]
        refine MonoidHom.mem_range.mpr ⟨1, ?_⟩
        rw [map_one]
        exact (Matrix.SpecialLinearGroup.coeToGL_det _).symm
      · rw [cubeDetGL, Subgroup.mem_comap]
        refine MonoidHom.mem_range.mpr ⟨Units.map ρ.toMonoidHom ν, ?_⟩
        rw [hMdet]
        simp
    · have hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1
          (hH.h1.borel_le hbB2)
      have hnormb : ∀ u : ↥(pCoreOf 2 L1), ∃ y : ↥(pCoreOf 2 L1),
          (y : G) = b * u * b⁻¹ := by
        intro u
        exact ⟨⟨b * (u : G) * b⁻¹, conj_mem_of_mem_normalizer hbQ1 u.2⟩, rfl⟩
      have hcomp := ActsByMatrix.mul hnormb (actsByMatrix_alpha c₁ ⟨x, hxL1⟩) hMact
      simpa [Ax, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hcomp
  · intro A hA
    rw [cubeDetGL, Subgroup.mem_comap] at hA
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hA
    obtain ⟨ν₀, hν₀⟩ := ρ.surjective (μ : GaloisField 2 f)
    have hν₀_ne : ν₀ ≠ 0 := by
      intro h0
      apply μ.ne_zero
      rw [← hν₀, h0, map_zero]
    let ν : (GaloisField 2 f)ˣ := Units.mk0 ν₀ hν₀_ne
    have hρν : ρ (ν : GaloisField 2 f) = (μ : GaloisField 2 f) := by
      simpa [ν] using hν₀
    obtain ⟨bL2, hbN, r, hbmat⟩ := c₂.exists_mem_normalizer (hD.le_right hH) ν
    have hbB2 : (bL2 : G) ∈ borelOf L2 S := by
      refine ⟨bL2.2, ?_⟩
      rwa [inf_eq_left.mpr (hD.le_right hH)]
    obtain ⟨m, M, hMval, hMdet, hMact⟩ :=
      exists_gl_of_mem_borel hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hFcard hbB2 hbmat
    have hμval : (Matrix.GeneralLinearGroup.det A).val =
        (μ : GaloisField 2 f) ^ 3 := by
      have h := congrArg Units.val hμ
      simpa [powMonoidHom] using h.symm
    have hMdetval : (Matrix.GeneralLinearGroup.det M).val =
        (ρ (ν : GaloisField 2 f)) ^ 3 := by
      rw [hMdet]
      simp [Units.coe_map]
    have hρν_ne : ρ (ν : GaloisField 2 f) ≠ 0 := by
      rw [hρν]
      exact μ.ne_zero
    let G' : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 f) := A * M⁻¹
    have hdetG : Matrix.GeneralLinearGroup.det G' = 1 := by
      apply Units.ext
      simp only [G', map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_one]
      rw [hμval, hMdetval, ← hρν]
      exact mul_inv_cancel₀ (pow_ne_zero 3 hρν_ne)
    have hgdet : ((G' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))).det = 1 := by
      have h := congrArg Units.val hdetG
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h
    let g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      ⟨(G' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)), hgdet⟩
    obtain ⟨x, hx⟩ := c₁.surjective g
    have hGM : G' * M = A := by
      simp [G']
    refine ⟨(x : G) * (bL2 : G), ?_, ?_⟩
    · rw [hD.sup_bigB_left hH]
      exact Subgroup.mul_mem_sup x.2 hbB2
    · have hbQ1 : (bL2 : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L1
          (hH.h1.borel_le hbB2)
      have hnormb : ∀ u : ↥(pCoreOf 2 L1), ∃ y : ↥(pCoreOf 2 L1),
          (y : G) = (bL2 : G) * u * (bL2 : G)⁻¹ := by
        intro u
        exact ⟨⟨(bL2 : G) * (u : G) * (bL2 : G)⁻¹,
          conj_mem_of_mem_normalizer hbQ1 u.2⟩, rfl⟩
      have hcomp := ActsByMatrix.mul hnormb (actsByMatrix_alpha c₁ x) hMact
      have hmat : (c₁.α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
            (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := by
        rw [show (c₁.α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
          (G' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) from congrArg Subtype.val hx,
          ← Matrix.GeneralLinearGroup.coe_mul]
        exact congrArg (fun Z : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 f) =>
          (Z : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) hGM
      rw [hmat] at hcomp
      exact hcomp

theorem L3qLocalData.linAction_right_of_pairing (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f)
    (c₁ : VertexCoord L2 S (GaloisField 2 f)) (c₂ : VertexCoord L1 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L2)) (z₂ : ↥(pCoreOf 2 L1)), (z₁ : G) = z₂ →
      Multiplicative.toAdd (c₁.β z₁) 1 = 0 ∧ Multiplicative.toAdd (c₂.β z₂) 1 = 0 ∧
      Multiplicative.toAdd (c₁.β z₁) 0 = e₁ * ρ (Multiplicative.toAdd (c₂.β z₂) 0))
    (h₂ : ∀ (x : ↥(pCoreOf 2 L2)) (x' : ↥L1) (t : GaloisField 2 f), (x : G) = x' →
      (c₂.α x' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
      Multiplicative.toAdd (c₁.β x) 1 = e₂ * ρ t) :
    LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) (cubeDetGL (GaloisField 2 f)) := by
  have h := L3qLocalData.linAction_left_of_pairing (L1 := L2) (L2 := L1) (S := S) (f := f)
    hH.symm hD.symm c₁ c₂ ρ e₁ e₂ h₁ h₂
  rwa [bigB_comm L1 L2 S] at h
