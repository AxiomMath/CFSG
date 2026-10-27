module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalField

import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalRoots

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open scoped MatrixGroups

section Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem sAdm_bar_mul (x y : K) : SAdm h x y (h.bar x * y) := by
  unfold SAdm
  rw [map_mul, h.bar_bar, mul_comm (h.bar y) x]

theorem radPhi_surjective : Function.Surjective (radPhi h) := by
  intro w
  set x := (Multiplicative.toAdd w).1
  set y := (Multiplicative.toAdd w).2
  refine ⟨⟨sElt h (sAdm_bar_mul h x y),
    ⟨x, y, _, sAdm_bar_mul h x y, coe_sElt h (sAdm_bar_mul h x y)⟩⟩, ?_⟩
  rw [radPhi_apply h (coe_sElt h (sAdm_bar_mul h x y))]
  rfl

theorem radPhi_eq_one_iff (g : ↥(radQ h)) : radPhi h g = 1 ↔ (g : hypSU h 2 0) ∈ zRad h := by
  obtain ⟨x, y, c, hc, hg⟩ := g.2
  rw [radPhi_apply h hg]
  constructor
  · intro h1
    have hxy : (x, y) = (0, 0) := Multiplicative.ofAdd.injective h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    exact ⟨c, (sAdm_zero_zero_iff h).mp hc, hg⟩
  · rintro ⟨c', -, hc'⟩
    rw [hg] at hc'
    have hx := congrFun (congrFun hc' ie2) if1
    have hy := congrFun (congrFun hc' if2) if1
    rw [sMat_ie2_if1, sMat_ie2_if1] at hx
    rw [sMat_if2_if1, sMat_if2_if1] at hy
    rw [hx, hy]
    rfl

@[expose] noncomputable def zRadHom : Multiplicative h.fixedField →* ↥(zRad h) where
  toFun c := ⟨sElt h ((sAdm_zero_zero_iff h).mpr ((h.mem_fixedField).mp
      (Multiplicative.toAdd c).2)),
    ⟨_, (h.mem_fixedField).mp (Multiplicative.toAdd c).2,
      coe_sElt h ((sAdm_zero_zero_iff h).mpr ((h.mem_fixedField).mp
        (Multiplicative.toAdd c).2))⟩⟩
  map_one' := by
    apply Subtype.ext
    apply hypSU_ext h
    rw [coe_sElt]
    exact sMat_zero_u4 h
  map_mul' c c' := by
    apply Subtype.ext
    apply hypSU_ext h
    show sMat h 0 0 ((Multiplicative.toAdd (c * c') : h.fixedField) : K) =
      sMat h 0 0 ((Multiplicative.toAdd c : h.fixedField) : K) *
        sMat h 0 0 ((Multiplicative.toAdd c' : h.fixedField) : K)
    rw [sMat_mul]
    simp

theorem coe_zRadHom (c : Multiplicative h.fixedField) :
    ((((zRadHom h c : ↥(zRad h)) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h 0 0 ((Multiplicative.toAdd c : h.fixedField) : K) :=
  coe_sElt h ((sAdm_zero_zero_iff h).mpr ((h.mem_fixedField).mp (Multiplicative.toAdd c).2))

@[expose] noncomputable def zRadEquiv : Multiplicative h.fixedField ≃* ↥(zRad h) :=
  MulEquiv.ofBijective (zRadHom h) (by
    constructor
    · intro c c' hcc
      have e := congrArg (fun g : ↥(zRad h) =>
        (((g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie1 if1) hcc
      simp only [coe_zRadHom, sMat_ie1_if1] at e
      exact Multiplicative.toAdd.injective (Subtype.ext e)
    · rintro ⟨g, c, hc, hg⟩
      refine ⟨Multiplicative.ofAdd ⟨c, (h.mem_fixedField).mpr hc⟩, Subtype.ext ?_⟩
      apply hypSU_ext h
      rw [coe_zRadHom, hg]
      rfl)

theorem coe_zRadEquiv (c : Multiplicative h.fixedField) :
    ((((zRadEquiv h c : ↥(zRad h)) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h 0 0 ((Multiplicative.toAdd c : h.fixedField) : K) :=
  coe_zRadHom h c

end Model

section Algebra

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

theorem twistForm_eq_smul_det (σ : K →+* K) (ρ : F →+* K) (hρ : ∀ a, σ (ρ a) = ρ a)
    (φ : (Fin 2 → F) →+ K) (hφ : ∀ (a : F) (v : Fin 2 → F), φ (a • v) = ρ a * φ v)
    (v w : Fin 2 → F) :
    σ (φ v) * φ w + φ v * σ (φ w) =
      (σ (φ (Pi.single 0 1)) * φ (Pi.single 1 1) + φ (Pi.single 0 1) * σ (φ (Pi.single 1 1))) *
        ρ (v 0 * w 1 + v 1 * w 0) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    funext i; fin_cases i <;> simp
  have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
    funext i; fin_cases i <;> simp
  set a := φ (Pi.single 0 1)
  set b := φ (Pi.single 1 1)
  have hφv : φ v = ρ (v 0) * a + ρ (v 1) * b := by
    rw [hv, map_add, hφ, hφ]; simp [a, b]
  have hφw : φ w = ρ (w 0) * a + ρ (w 1) * b := by
    rw [hw, map_add, hφ, hφ]; simp [a, b]
  rw [hφv, hφw]
  simp only [map_add, map_mul, hρ, map_mul ρ]
  have h2 : ∀ x : K, x + x = 0 := CharTwo.add_self_eq_zero
  linear_combination (ρ (v 0) * ρ (w 0)) * h2 (σ a * a) + (ρ (v 1) * ρ (w 1)) * h2 (σ b * b)

theorem twistForm_basis_ne_zero (σ : K →+* K) (ρ : F →+* K)
    (hfix : ∀ x : K, σ x = x → ∃ a, ρ a = x) (φ : (Fin 2 → F) →+ K)
    (hφ : ∀ (a : F) (v : Fin 2 → F), φ (a • v) = ρ a * φ v) (hinj : Function.Injective φ) :
    σ (φ (Pi.single 0 1)) * φ (Pi.single 1 1) + φ (Pi.single 0 1) * σ (φ (Pi.single 1 1)) ≠ 0 := by
  set a := φ (Pi.single 0 1)
  set b := φ (Pi.single 1 1)
  have ha : a ≠ 0 := by
    intro h0
    have := hinj (h0.trans (map_zero φ).symm)
    simpa using congrFun this 0
  have hσa : σ a ≠ 0 := fun h0 => ha (σ.injective (h0.trans (map_zero σ).symm))
  intro hδ
  have hfixl : σ (b / a) = b / a := by
    rw [map_div₀, div_eq_div_iff hσa ha]
    have e : σ a * b = a * σ b := CharTwo.add_eq_zero.mp hδ
    rw [mul_comm (σ b) a, ← e, mul_comm]
  obtain ⟨c, hc⟩ := hfix _ hfixl
  have hb : b = ρ c * a := by rw [hc, div_mul_cancel₀ _ ha]
  have := hinj (show φ (Pi.single 1 1) = φ (c • Pi.single 0 1) by rw [hφ]; exact hb)
  simpa using congrFun this 1

end Algebra

section Abstract

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem U4qLocalData.exists_phiA {F K : Type} [Field F] [Field K] (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f))
    (c₁ : U4qCoordLeft L1 L2 S f F) (c₂ : U4qCoordRight L1 L2 S f K)
    (hU : UnitaryFieldData 2 f K) :
    ∃ (ρ : F ≃+* hU.fixedField) (φ : (Fin 2 → F) →+ K), Function.Bijective φ ∧
      (∀ (τ : F) (v : Fin 2 → F), φ (τ • v) = (ρ τ : K) * φ v) ∧
      ∀ (a : G) (ha : a ∈ pCoreOf 2 L1) (ha' : a ∈ L2),
        φ (Multiplicative.toAdd (c₁.β ⟨a, ha⟩) 1) =
          (c₂.α ⟨a, ha'⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 := by
  classical
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [c₁.card]; positivity)
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [c₂.card]; positivity)
  obtain ⟨ρ, -, -, hA, -, -⟩ := hD.exists_ringEquiv_fixedField hH hS c₁ c₂ hU
  have hQ1L2 : ∀ {a : G}, a ∈ pCoreOf 2 L1 → a ∈ L2 := fun ha =>
    hD.le_right hH hS (hH.pCoreOf_le_left ha)
  have hsec : ∀ v : Fin 2 → F, ∃ a : ↥(pCoreOf 2 L1), Multiplicative.toAdd (c₁.β a) 1 = v := by
    intro v
    obtain ⟨a, ha⟩ := c₁.surjective_β (Multiplicative.ofAdd (Matrix.of ![0, v]))
    exact ⟨a, by rw [ha]; rfl⟩
  choose sec hsec_spec using hsec
  let ent : ↥(pCoreOf 2 L1) → K := fun a =>
    (c₂.α ⟨a, hQ1L2 a.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1
  have hunit : ∀ a : ↥(pCoreOf 2 L1), (c₂.α ⟨a, hQ1L2 a.2⟩ : Matrix (Fin 2) (Fin 2) K) =
      !![1, ent a; 0, 1] := by
    intro a
    obtain ⟨t, ht⟩ := (c₂.mem_iff ⟨a, hQ1L2 a.2⟩).mp (hH.pCoreOf_le_left a.2)
    have : ent a = t := by
      show (c₂.α ⟨a, hQ1L2 a.2⟩ : Matrix (Fin 2) (Fin 2) K) 0 1 = t
      rw [ht]; rfl
    rw [ht, this]
  have hwd : ∀ a b : ↥(pCoreOf 2 L1), Multiplicative.toAdd (c₁.β b) 1 =
      Multiplicative.toAdd (c₁.β a) 1 → ent b = ent a := by
    intro a b hab
    have h := hA a a.2 (hQ1L2 a.2) b b.2 (hQ1L2 b.2) 1 (by rw [one_smul]; exact hab)
    rw [map_one, Subfield.coe_one, one_mul] at h
    exact h
  have hent_mul : ∀ a b : ↥(pCoreOf 2 L1), ent (a * b) = ent a + ent b := by
    intro a b
    have h := congrFun (congrFun (congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K))
      (map_mul c₂.α ⟨a, hQ1L2 a.2⟩ ⟨b, hQ1L2 b.2⟩)) 0) 1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [hunit a, hunit b] at h
    have e : (c₂.α (⟨a, hQ1L2 a.2⟩ * ⟨b, hQ1L2 b.2⟩) : Matrix (Fin 2) (Fin 2) K) 0 1 =
        ent (a * b) := rfl
    rw [e] at h
    rw [h]
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  let φ : (Fin 2 → F) →+ K := AddMonoidHom.mk' (fun v => ent (sec v)) (by
    intro v w
    have h1 : Multiplicative.toAdd (c₁.β (sec v * sec w)) 1 = v + w := by
      rw [map_mul, toAdd_mul]
      funext j
      have hv := congrFun (hsec_spec v) j
      have hw := congrFun (hsec_spec w) j
      rw [Matrix.add_apply, Pi.add_apply, hv, hw]
    have h2 := hwd (sec v * sec w) (sec (v + w)) (by rw [hsec_spec, h1])
    rw [h2, hent_mul])
  have hφ_spec : ∀ a : ↥(pCoreOf 2 L1), φ (Multiplicative.toAdd (c₁.β a) 1) = ent a :=
    fun a => hwd a _ (hsec_spec _)
  have hφsmul : ∀ (τ : F) (v : Fin 2 → F), φ (τ • v) = (ρ τ : K) * φ v := by
    intro τ v
    have h := hA (sec v) (sec v).2 (hQ1L2 (sec v).2) (sec (τ • v)) (sec (τ • v)).2
      (hQ1L2 (sec (τ • v)).2) τ (by rw [hsec_spec, hsec_spec])
    exact h
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h0 : ent (sec v) = 0 := hv
    have hα : c₂.α ⟨sec v, hQ1L2 (sec v).2⟩ = 1 := by
      apply Subtype.ext
      rw [hunit, h0]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hQ2 : ((sec v : ↥(pCoreOf 2 L1)) : G) ∈ pCoreOf 2 L2 := (c₂.eq_one_iff _).mp hα
    rw [← hsec_spec v]
    exact (c₁.mem_inf_iff (sec v)).mp hQ2
  have hcard : Nat.card K ≤ Nat.card (Fin 2 → F) := by
    rw [Nat.card_fun, Nat.card_fin, c₁.card, c₂.card, ← pow_mul, mul_comm]
  refine ⟨ρ, φ, ⟨hφinj, (hφinj.bijective_of_nat_card_le hcard).2⟩, hφsmul, ?_⟩
  intro a ha ha'
  exact hφ_spec ⟨a, ha⟩

end Abstract

end CFSG.Quasithin.F112R.St84

end
