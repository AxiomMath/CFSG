module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalCoord
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.Quasithin.Background.F1Borel

import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalLocal
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalField
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalSchur
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalPairing
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalVertex
import CFSG.Quasithin.Recognition.St84.Gen.SL2InnerAut
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups
open CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private lemma conj_mem_of_mem_normalizer {Q : Subgroup G} {b x : G}
    (hb : b ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) :
    b * x * b⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp hb x).mp hx

private lemma conj_eq_of_mem_mul {Q : Subgroup G}
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {q x u w : G} (hq : q ∈ Q) (hu : u = q * x)
    (hxN : x ∈ Subgroup.normalizer (Q : Set G)) (hw : w ∈ Q) :
    u * w * u⁻¹ = x * w * x⁻¹ := by
  rw [hu]
  have hxw : x * w * x⁻¹ ∈ Q := conj_mem_of_mem_normalizer hxN hw
  calc (q * x) * w * (q * x)⁻¹ = q * (x * w * x⁻¹) * q⁻¹ := by group
    _ = (x * w * x⁻¹) * q * q⁻¹ := by rw [hQ q hq (x * w * x⁻¹) hxw]
    _ = x * w * x⁻¹ := by group

private lemma exists_kappa_unipotent (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f)
    (e₂ : (GaloisField 2 f)ˣ)
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t)
    {b : G} (hbL2 : b ∈ L2)
    (hbL1 : b ∈ Subgroup.normalizer (L1 : Set G))
    (hbQ2 : b ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    {ν : (GaloisField 2 f)ˣ} {r : GaloisField 2 f}
    (hbmat : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![(ν : GaloisField 2 f), r; 0, ((ν⁻¹ : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)]) :
    ∃ κ : GaloisField 2 f, κ ≠ 0 ∧ ∀ s : GaloisField 2 f, ∃ x y : ↥L1,
      (y : G) = b * (x : G) * b⁻¹ ∧
      (c₁.α x : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, s; 0, 1] ∧
      (c₁.α y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, κ * s; 0, 1] := by
  classical
  let F := GaloisField 2 f
  let Q1 := pCoreOf 2 L1
  let κ : F := ρ.symm (((ν : F))⁻¹ ^ 2)
  have hκ : κ ≠ 0 := by
    apply (map_ne_zero (ρ.symm : F →+* F)).mpr
    exact pow_ne_zero 2 (inv_ne_zero ν.ne_zero)
  have hU : ∀ s : F, ∃ x y : ↥L1,
      (y : G) = b * (x : G) * b⁻¹ ∧
      (c₁.α x : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] ∧
      (c₁.α y : Matrix (Fin 2) (Fin 2) F) = !![1, κ * s; 0, 1] := by
    intro s
    obtain ⟨y, hyα⟩ := Sp4qLocalData.exists_pCoreOf_right_alpha hH hD c₁ s
    have hyα' : (c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) :
        Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] := by
      simpa using hyα
    let y2 : ↥(pCoreOf 2 L2) :=
      ⟨b * (y : G) * b⁻¹, conj_mem_of_mem_normalizer hbQ2 y.2⟩
    have hy2coe : (y2 : G) = b * (y : G) * b⁻¹ := rfl
    have hzL1 : b * (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y : G) * b⁻¹ ∈ L1 :=
      conj_mem_of_mem_normalizer hbL1 (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y).2
    let z : ↥L1 := ⟨b * (y : G) * b⁻¹, hzL1⟩
    have hzcoe : (z : G) = (y2 : G) := rfl
    have hzS : (z : G) ∈ S := by
      have hy2S : (y2 : G) ∈ S := hH.pCoreOf_le_right y2.2
      simpa [hzcoe] using hy2S
    obtain ⟨s', hs'mat⟩ := (c₁.mem_iff z).mp hzS
    have hconj : Multiplicative.toAdd (c₂.γ y2) =
        (sp4RadMat (c₂.α ⟨b, hbL2⟩)).mulVec (Multiplicative.toAdd (c₂.γ y)) :=
      c₂.equivariant ⟨b, hbL2⟩ y y2 (by rfl)
    have hcoord2 : Multiplicative.toAdd (c₂.γ y2) 2 =
        ((ν : F)⁻¹) ^ 2 * Multiplicative.toAdd (c₂.γ y) 2 := by
      rw [hconj, sp4RadMat_mulVec]
      simp [hbmat]
    have hycoord : Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ s :=
      h₂ y (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) s rfl hyα'
    have hzcoord : Multiplicative.toAdd (c₂.γ y2) 2 = e₂ * ρ s' :=
      h₂ y2 z s' hzcoe.symm hs'mat
    have hρeq : ρ s' = ((ν : F)⁻¹) ^ 2 * ρ s := by
      have h : e₂ * ρ s' = ((ν : F)⁻¹) ^ 2 * (e₂ * ρ s) := by
        rw [← hzcoord, hcoord2, hycoord]
      have h' : e₂ * ρ s' = e₂ * (((ν : F)⁻¹) ^ 2 * ρ s) := by
        rw [h]; ring
      exact mul_left_cancel₀ e₂.ne_zero h'
    have hs'eq : s' = κ * s := by
      have h := congrArg (fun t => ρ.symm t) hρeq
      simpa [κ, map_mul] using h
    refine ⟨Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y, z, ?_, hyα', ?_⟩
    · rfl
    · rw [hs'mat, hs'eq]
  exact ⟨κ, hκ, hU⟩

private lemma exists_inner_borelOf (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f)
    (e₂ : (GaloisField 2 f)ˣ)
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t)
    {b : G} (hbL2 : b ∈ L2)
    (hbL1 : b ∈ Subgroup.normalizer (L1 : Set G))
    (hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hbQ2 : b ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    {ν : (GaloisField 2 f)ˣ} {r : GaloisField 2 f}
    (hbmat : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![(ν : GaloisField 2 f), r; 0, ((ν⁻¹ : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)]) :
    ∃ g ∈ L1, ∀ x ∈ L1, b * x * b⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L1 := by
  obtain ⟨κ, hκ, hU⟩ :=
    exists_kappa_unipotent hH hD c₁ c₂ ρ e₂ h₂ hbL2 hbL1 hbQ2 hbmat
  exact exists_inner_of_unitriangular c₁.α c₁.surjective c₁.eq_one_iff hbL1 hbQ1 hκ hU

private lemma addAction_commutes (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {b g : G} (hgL1 : g ∈ L1)
    (hg : ∀ x ∈ L1, b * x * b⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L1)
    (ψ : MulAut ↥(pCoreOf 2 L1))
    (hψ_apply : ∀ u : ↥(pCoreOf 2 L1),
      (ψ u : G) = (g⁻¹ * b) * (u : G) * (g⁻¹ * b)⁻¹)
    (A : (Fin 3 → GaloisField 2 f) →+ (Fin 3 → GaloisField 2 f))
    (hA_apply : ∀ u : ↥(pCoreOf 2 L1),
      A (Multiplicative.toAdd (c₁.γ u)) = Multiplicative.toAdd (c₁.γ (ψ u))) :
    ∀ (M : SL(2, GaloisField 2 f)) (v : Fin 3 → GaloisField 2 f),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v) := by
  classical
  let F := GaloisField 2 f
  let Q1 := pCoreOf 2 L1
  have hcomm : ∀ a ∈ Q1, ∀ c ∈ Q1, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hD.elem_left.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  intro M v
  obtain ⟨x, hx⟩ := c₁.surjective M
  let w : ↥Q1 := c₁.γ.symm (Multiplicative.ofAdd v)
  have hw : Multiplicative.toAdd (c₁.γ w) = v := by simp [w]
  let wx : ↥Q1 := ⟨(x : G) * (w : G) * (x : G)⁻¹,
    PCoreSection.conj_mem_pCoreOf x.2 w.2⟩
  have hwx : Multiplicative.toAdd (c₁.γ wx) = (sp4RadMat M).mulVec v := by
    have h := c₁.equivariant x w wx (by rfl)
    rw [hx, hw] at h
    exact h
  have hA_M : A ((sp4RadMat M).mulVec v) =
      Multiplicative.toAdd (c₁.γ (ψ wx)) := by
    rw [← hwx, hA_apply]
  let q0 : G := b * (x : G) * b⁻¹ * (g * (x : G) * g⁻¹)⁻¹
  have hq0Q : q0 ∈ Q1 := hg (x : G) x.2
  have hgNQ1 : g⁻¹ ∈ Subgroup.normalizer (Q1 : Set G) := by
    simpa [Q1] using le_normalizer_pCoreOf 2 L1 (L1.inv_mem hgL1)
  have hqmem : g⁻¹ * q0 * g ∈ Q1 := by
    simpa using conj_mem_of_mem_normalizer hgNQ1 hq0Q
  let q : ↥Q1 := ⟨g⁻¹ * q0 * g, hqmem⟩
  have hu_eq : g⁻¹ * (b * (x : G) * b⁻¹) * g = (q : G) * (x : G) := by
    have hq0def : q0 * (g * (x : G) * g⁻¹) = b * (x : G) * b⁻¹ := by
      simp [q0]
      group
    calc g⁻¹ * (b * (x : G) * b⁻¹) * g
        = g⁻¹ * (q0 * (g * (x : G) * g⁻¹)) * g := by rw [hq0def]
      _ = (g⁻¹ * q0 * g) * (x : G) := by group
      _ = (q : G) * (x : G) := rfl
  let u : G := g⁻¹ * (b * (x : G) * b⁻¹) * g
  have hxNQ1 : (x : G) ∈ Subgroup.normalizer (Q1 : Set G) := by
    simpa [Q1] using le_normalizer_pCoreOf 2 L1 x.2
  let yw : ↥Q1 := ⟨(x : G) * (ψ w : G) * (x : G)⁻¹,
    PCoreSection.conj_mem_pCoreOf x.2 (ψ w).2⟩
  have hψwx_coe : (ψ wx : G) = u * (ψ w : G) * u⁻¹ := by
    rw [hψ_apply wx, hψ_apply w]
    simp only [wx, u]
    group
  have hconj_eq : u * (ψ w : G) * u⁻¹ =
      (x : G) * (ψ w : G) * (x : G)⁻¹ :=
    conj_eq_of_mem_mul hcomm q.2 hu_eq hxNQ1 (ψ w).2
  have hψwx : ψ wx = yw := by
    apply Subtype.ext
    rw [hψwx_coe, hconj_eq]
  have hyw : Multiplicative.toAdd (c₁.γ yw) = (sp4RadMat M).mulVec (A v) := by
    have h := c₁.equivariant x (ψ w) yw (by rfl)
    rw [hx] at h
    have hwA : A v = Multiplicative.toAdd (c₁.γ (ψ w)) := by
      rw [← hw, hA_apply]
    rw [h, hwA]
  calc A ((sp4RadMat M).mulVec v)
      = Multiplicative.toAdd (c₁.γ (ψ wx)) := hA_M
    _ = Multiplicative.toAdd (c₁.γ yw) := by rw [hψwx]
    _ = (sp4RadMat M).mulVec (A v) := hyw

private lemma exists_addAction_of_inner (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {b g : G} (hgL1 : g ∈ L1)
    (hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hg : ∀ x ∈ L1, b * x * b⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L1) :
    ∃ (A : (Fin 3 → GaloisField 2 f) →+ (Fin 3 → GaloisField 2 f))
      (ψ : MulAut ↥(pCoreOf 2 L1)),
      (∀ u : ↥(pCoreOf 2 L1), (ψ u : G) = (g⁻¹ * b) * (u : G) * (g⁻¹ * b)⁻¹) ∧
      (∀ u : ↥(pCoreOf 2 L1),
        A (Multiplicative.toAdd (c₁.γ u)) = Multiplicative.toAdd (c₁.γ (ψ u))) ∧
      (∀ (M : SL(2, GaloisField 2 f)) (v : Fin 3 → GaloisField 2 f),
        A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v)) ∧
      A (![1, 0, 0] : Fin 3 → GaloisField 2 f) ≠ 0 := by
  classical
  let F := GaloisField 2 f
  let Q1 := pCoreOf 2 L1
  have hgibQ1 : g⁻¹ * b ∈ Subgroup.normalizer (Q1 : Set G) :=
    (Subgroup.normalizer (Q1 : Set G)).mul_mem
      ((Subgroup.normalizer (Q1 : Set G)).inv_mem (le_normalizer_pCoreOf 2 L1 hgL1)) hbQ1
  let ψ : MulAut ↥Q1 := Q1.normalizerMonoidHom ⟨g⁻¹ * b, hgibQ1⟩
  have hψ_apply : ∀ u : ↥Q1, (ψ u : G) = (g⁻¹ * b) * (u : G) * (g⁻¹ * b)⁻¹ := fun u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q1 ⟨g⁻¹ * b, hgibQ1⟩ u
  let A : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => Multiplicative.toAdd
        (c₁.γ (ψ (c₁.γ.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun v w => by
        show Multiplicative.toAdd (c₁.γ (ψ (c₁.γ.symm (Multiplicative.ofAdd (v + w))))) =
          Multiplicative.toAdd (c₁.γ (ψ (c₁.γ.symm (Multiplicative.ofAdd v)))) +
          Multiplicative.toAdd (c₁.γ (ψ (c₁.γ.symm (Multiplicative.ofAdd w))))
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hA_apply : ∀ u : ↥Q1,
      A (Multiplicative.toAdd (c₁.γ u)) = Multiplicative.toAdd (c₁.γ (ψ u)) := by
    intro u
    simp [A]
  have hA_comm : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v) :=
    addAction_commutes hD c₁ hgL1 hg ψ hψ_apply A hA_apply
  have hA_ne : A (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro hzero
    have hγ : c₁.γ (ψ (c₁.γ.symm (Multiplicative.ofAdd ![1, 0, 0]))) = 1 :=
      Multiplicative.toAdd.injective (by simpa [A] using hzero)
    have hψ : ψ (c₁.γ.symm (Multiplicative.ofAdd ![1, 0, 0])) = 1 :=
      c₁.γ.injective (by simpa using hγ)
    have hq : c₁.γ.symm (Multiplicative.ofAdd ![1, 0, 0]) = 1 :=
      ψ.injective (by simpa using hψ)
    have hof : Multiplicative.ofAdd (![1, 0, 0] : Fin 3 → F) = 1 := by
      have h := congrArg c₁.γ hq
      simpa using h
    have hvec : (![1, 0, 0] : Fin 3 → F) = 0 :=
      Multiplicative.ofAdd.injective (by simpa using hof)
    exact one_ne_zero (congrFun hvec 0)
  exact ⟨A, ψ, hψ_apply, hA_apply, hA_comm, hA_ne⟩

private lemma exists_scalar_of_inner (hf : 2 ≤ f) (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {b g : G} (hgL1 : g ∈ L1)
    (hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hg : ∀ x ∈ L1, b * x * b⁻¹ * (g * x * g⁻¹)⁻¹ ∈ pCoreOf 2 L1) :
    ∃ c : GaloisField 2 f, c ≠ 0 ∧
      ActsByMatrix c₁.γ (g⁻¹ * b) (c • 1) := by
  classical
  let F := GaloisField 2 f
  obtain ⟨A, ψ, hψ, hA_apply, hA_comm, hA_ne⟩ :=
    exists_addAction_of_inner hD c₁ hgL1 hbQ1 hg
  have hf0 : f ≠ 0 := by omega
  have hF4 : 4 ≤ Nat.card F := by
    have hcard : Nat.card F = 2 ^ f := GaloisField.card (p := 2) (n := f) hf0
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute_sp4RadMat hF4 A hA_comm
  have hc_ne : c ≠ 0 := by
    intro h0
    have hzero : A (![1, 0, 0] : Fin 3 → F) = 0 := by
      rw [hc]
      simp [h0]
    exact hA_ne hzero
  refine ⟨c, hc_ne, ?_⟩
  intro u v hv
  have hvψ : v = ψ u := Subtype.ext (by rw [hv, hψ u])
  rw [hvψ, ← hA_apply u, hc]
  simp [Matrix.smul_mulVec]

private lemma scalar_eq_of_actsByMatrix (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      (z₁ : G) ∈ blockZ L1 →
        Multiplicative.toAdd (c₂.γ z₂) 1 = e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0))
    {b g : G} (hgL1 : g ∈ L1) (hbL2 : b ∈ L2)
    (hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G))
    (hbQ2 : b ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G))
    {ν : (GaloisField 2 f)ˣ} {r : GaloisField 2 f}
    (hbmat : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![(ν : GaloisField 2 f), r; 0, ((ν⁻¹ : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)])
    (c : GaloisField 2 f)
    (hb_act : ActsByMatrix c₁.γ b (c • sp4RadMat (c₁.α ⟨g, hgL1⟩))) :
    c = ρ.symm ((ν : GaloisField 2 f) ^ 2) := by
  classical
  let F := GaloisField 2 f
  let Q1 := pCoreOf 2 L1
  let z : ↥Q1 := c₁.γ.symm (Multiplicative.ofAdd ![1, 0, 0])
  have hzγ : Multiplicative.toAdd (c₁.γ z) = ![1, 0, 0] := by simp [z]
  have hzZ : (z : G) ∈ blockZ L1 :=
    (c₁.mem_blockZ_iff hD.blockU_left z).mpr (by rw [hzγ]; exact ⟨rfl, rfl⟩)
  have hzQ2 : (z : G) ∈ pCoreOf 2 L2 := (hD.blockZ_left_le hH hzZ).2
  let z2 : ↥(pCoreOf 2 L2) := ⟨z, hzQ2⟩
  let w1 : ↥Q1 := ⟨b * (z : G) * b⁻¹, conj_mem_of_mem_normalizer hbQ1 z.2⟩
  let w2 : ↥(pCoreOf 2 L2) :=
    ⟨b * (z : G) * b⁻¹, conj_mem_of_mem_normalizer hbQ2 z2.2⟩
  have hw1γ : Multiplicative.toAdd (c₁.γ w1) = c • ![1, 0, 0] := by
    have h := hb_act z w1 (by rfl)
    rw [h, hzγ, Matrix.smul_mulVec]
    congr 1
    rw [sp4RadMat_mulVec]
    simp
  have h1z : Multiplicative.toAdd (c₂.γ z2) 1 =
      e₁ * ρ (Multiplicative.toAdd (c₁.γ z) 0) := h₁ z z2 rfl hzZ
  have hw1Z : (w1 : G) ∈ blockZ L1 :=
    (c₁.mem_blockZ_iff hD.blockU_left w1).mpr (by rw [hw1γ]; simp)
  have h1w : Multiplicative.toAdd (c₂.γ w2) 1 =
      e₁ * ρ (Multiplicative.toAdd (c₁.γ w1) 0) := h₁ w1 w2 rfl hw1Z
  have hconj2 : Multiplicative.toAdd (c₂.γ w2) =
      (sp4RadMat (c₂.α ⟨b, hbL2⟩)).mulVec (Multiplicative.toAdd (c₂.γ z2)) :=
    c₂.equivariant ⟨b, hbL2⟩ z2 w2 (by rfl)
  have hz2coord2 : Multiplicative.toAdd (c₂.γ z2) 2 = 0 :=
    Sp4VertexCoord.coord_two_eq_zero_of_mem_inf hH hD c₂ ⟨z.2, hzQ2⟩
  have hw2coord1 : Multiplicative.toAdd (c₂.γ w2) 1 =
      (ν : F) ^ 2 * Multiplicative.toAdd (c₂.γ z2) 1 := by
    rw [hconj2, sp4RadMat_mulVec]
    simp [hbmat, hz2coord2]
  have h1z' : Multiplicative.toAdd (c₂.γ z2) 1 = e₁ := by
    rw [h1z, hzγ]
    simp
  have h1w' : Multiplicative.toAdd (c₂.γ w2) 1 = e₁ * ρ c := by
    rw [h1w, hw1γ]
    simp
  have heq : (ν : F) ^ 2 * e₁ = e₁ * ρ c := by
    rw [← h1z', ← hw2coord1, h1w', h1z']
  have hρc : ρ c = (ν : F) ^ 2 := by
    apply mul_left_cancel₀ e₁.ne_zero
    rw [← heq]
    ring
  have h := congrArg (fun t : F => ρ.symm t) hρc
  simpa using h

private theorem exists_actsByMatrix_borelOf (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      (z₁ : G) ∈ blockZ L1 →
        Multiplicative.toAdd (c₂.γ z₂) 1 = e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0))
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t)
    {b : G} (hb : b ∈ borelOf L2 S) {ν : (GaloisField 2 f)ˣ} {r : GaloisField 2 f}
    (hbmat : (c₂.α ⟨b, borelOf_le L2 S hb⟩ :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![(ν : GaloisField 2 f), r; 0, ((ν⁻¹ : (GaloisField 2 f)ˣ) :
        GaloisField 2 f)]) :
    ∃ (N : SL(2, GaloisField 2 f)) (B : GL (Fin 3) (GaloisField 2 f)),
      B ∈ sp4Gamma (GaloisField 2 f) ∧
      (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)) =
        (ρ.symm ((ν : GaloisField 2 f) ^ 2)) • sp4RadMat N ∧
      ActsByMatrix c₁.γ b (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  let Q1 := pCoreOf 2 L1
  have hbL2 : b ∈ L2 := borelOf_le L2 S hb
  have hbmat' : (c₂.α ⟨b, hbL2⟩ : Matrix (Fin 2) (Fin 2) F) =
      !![(ν : F), r; 0, ((ν⁻¹ : Fˣ) : F)] := by
    simpa using hbmat
  have hbL1 : b ∈ Subgroup.normalizer (L1 : Set G) := hH.h1.borel_le hb
  have hbQ1 : b ∈ Subgroup.normalizer (Q1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 hbL1
  have hbQ2 : b ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    le_normalizer_pCoreOf 2 L2 hbL2
  obtain ⟨g, hgL1, hg⟩ :=
    exists_inner_borelOf hH hD c₁ c₂ ρ e₂ h₂ hbL2 hbL1 hbQ1 hbQ2 hbmat'
  obtain ⟨c, hc_ne, hh_act⟩ :=
    exists_scalar_of_inner hf hD c₁ hgL1 hbQ1 hg
  let N : SL(2, F) := c₁.α ⟨g, hgL1⟩
  have hg_act : ActsByMatrix c₁.γ g (sp4RadMat N) := by
    intro u v hv
    exact c₁.equivariant ⟨g, hgL1⟩ u v hv
  have hnorm : ∀ u : ↥Q1, ∃ y : ↥Q1,
      (y : G) = (g⁻¹ * b) * (u : G) * (g⁻¹ * b)⁻¹ := by
    intro u
    exact ⟨⟨_, conj_mem_of_mem_normalizer
      ((Subgroup.normalizer (Q1 : Set G)).mul_mem
        ((Subgroup.normalizer (Q1 : Set G)).inv_mem
          (le_normalizer_pCoreOf 2 L1 hgL1)) hbQ1) u.2⟩, rfl⟩
  have hcomp := ActsByMatrix.mul hnorm hg_act hh_act
  have hgb : g * (g⁻¹ * b) = b := by group
  have hmat : sp4RadMat N * (c • 1) = c • sp4RadMat N := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [hgb, hmat] at hcomp
  have hb_act : ActsByMatrix c₁.γ b (c • sp4RadMat (c₁.α ⟨g, hgL1⟩)) := hcomp
  have hc_eq : c = ρ.symm ((ν : F) ^ 2) :=
    scalar_eq_of_actsByMatrix hH hD c₁ c₂ ρ e₁ h₁ hgL1 hbL2 hbQ1 hbQ2 hbmat' c hb_act
  let cU : Fˣ := Units.mk0 c hc_ne
  let B : GL (Fin 3) F := sp4RadHom F (c₁.α ⟨g, hgL1⟩) * sp4ScalarHom F cU
  have hBcoe : (B : Matrix (Fin 3) (Fin 3) F) = c • sp4RadMat (c₁.α ⟨g, hgL1⟩) := by
    simp [B, cU, Matrix.mul_smul]
  have hBmem : B ∈ sp4Gamma F := by
    rw [mem_sp4Gamma_iff]
    exact ⟨c₁.α ⟨g, hgL1⟩, cU, by simpa [cU] using hBcoe⟩
  refine ⟨c₁.α ⟨g, hgL1⟩, B, hBmem, ?_, ?_⟩
  · rw [hBcoe, hc_eq]
  · rw [hBcoe]
    exact hb_act

private lemma actsByMatrix_of_mem_sup_bigB (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      (z₁ : G) ∈ blockZ L1 →
        Multiplicative.toAdd (c₂.γ z₂) 1 = e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0))
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t)
    {p : G} (hp : p ∈ L1 ⊔ bigB L1 L2 S) :
    ∃ A ∈ sp4Gamma (GaloisField 2 f),
      ActsByMatrix c₁.γ p (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  have hS1 : S ≤ L1 := hD.le_left hH
  rw [sup_bigB_left_of_le hS1] at hp
  have hset :=
    Subgroup.coe_mul_of_right_le_normalizer_left L1 (borelOf L2 S) hH.h1.borel_le
  change p ∈ ((L1 ⊔ borelOf L2 S : Subgroup G) : Set G) at hp
  rw [hset, Set.mem_mul] at hp
  obtain ⟨x, hxL1, b, hbB2, hxb⟩ := hp
  rw [← hxb]
  have hbL2 : b ∈ L2 := borelOf_le L2 S hbB2
  have hbN : ((⟨b, hbL2⟩ : ↥L2) : G) ∈ Subgroup.normalizer (S : Set G) := by
    have h := borelOf_le_normalizer L2 S hbB2
    rwa [inf_eq_left.mpr (hD.le_right hH)] at h
  obtain ⟨ν, r, hbmat⟩ :=
    c₂.exists_of_mem_normalizer (hD.le_right hH) (b := ⟨b, hbL2⟩) hbN
  obtain ⟨N, B, hBmem, hBcoe, hBact⟩ :=
    exists_actsByMatrix_borelOf hf hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hbB2
      (by simpa using hbmat)
  let Ax : GL (Fin 3) F := sp4RadHom F (c₁.α ⟨x, hxL1⟩)
  have hxmem : Ax ∈ sp4Gamma F := by
    rw [mem_sp4Gamma_iff]
    exact ⟨c₁.α ⟨x, hxL1⟩, 1, by simp [Ax]⟩
  have hxact : ActsByMatrix c₁.γ x (Ax : Matrix (Fin 3) (Fin 3) F) := by
    intro u v hv
    exact c₁.equivariant ⟨x, hxL1⟩ u v hv
  have hnormb : ∀ u : ↥(pCoreOf 2 L1), ∃ y : ↥(pCoreOf 2 L1),
      (y : G) = b * (u : G) * b⁻¹ := by
    intro u
    have hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 L1 (hH.h1.borel_le hbB2)
    exact ⟨⟨_, conj_mem_of_mem_normalizer hbQ1 u.2⟩, rfl⟩
  refine ⟨Ax * B, Subgroup.mul_mem _ hxmem hBmem, ?_⟩
  have hcomp := ActsByMatrix.mul hnormb hxact hBact
  simpa [Ax, Matrix.GeneralLinearGroup.coe_mul] using hcomp

private lemma exists_mem_sup_bigB_of_mem_sp4Gamma (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      (z₁ : G) ∈ blockZ L1 →
        Multiplicative.toAdd (c₂.γ z₂) 1 = e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0))
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t)
    {A : GL (Fin 3) (GaloisField 2 f)} (hA : A ∈ sp4Gamma (GaloisField 2 f)) :
    ∃ p ∈ L1 ⊔ bigB L1 L2 S,
      ActsByMatrix c₁.γ p (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  rw [mem_sp4Gamma_iff] at hA
  obtain ⟨M, c₀, hAmat⟩ := hA
  have hc₀ : (c₀ : F) ≠ 0 := c₀.ne_zero
  have hsq : ∃ ν : F, ν ^ 2 = ρ (c₀ : F) := by
    obtain ⟨ν, hν⟩ := isSquare_of_charTwo' (ρ (c₀ : F))
    exact ⟨ν, by rw [pow_two]; exact hν.symm⟩
  obtain ⟨ν, hν⟩ := hsq
  have hν0 : ν ≠ 0 := by
    intro h0
    have hz : ρ (c₀ : F) = 0 := by rw [← hν, h0]; simp
    exact hc₀ ((map_eq_zero ρ).mp hz)
  let νu : Fˣ := Units.mk0 ν hν0
  obtain ⟨bL2, hbN, r, hbmat⟩ := c₂.exists_mem_normalizer (hD.le_right hH) νu
  have hbB2 : (bL2 : G) ∈ borelOf L2 S := by
    refine ⟨bL2.2, ?_⟩
    rwa [inf_eq_left.mpr (hD.le_right hH)]
  obtain ⟨N, B, hBmem, hBcoe, hBact⟩ :=
    exists_actsByMatrix_borelOf hf hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hbB2
      (by simpa using hbmat)
  have hBcoef : (B : Matrix (Fin 3) (Fin 3) F) = (c₀ : F) • sp4RadMat N := by
    rw [hBcoe]
    show (ρ.symm ((νu : F) ^ 2)) • sp4RadMat N = (c₀ : F) • sp4RadMat N
    rw [show (νu : F) = ν from rfl, hν]
    simp
  obtain ⟨x, hx⟩ := c₁.surjective (M * N⁻¹)
  let Ax : GL (Fin 3) F := sp4RadHom F (c₁.α ⟨x, x.2⟩)
  have hxmem : Ax ∈ sp4Gamma F := by
    rw [mem_sp4Gamma_iff]
    exact ⟨c₁.α ⟨x, x.2⟩, 1, by simp [Ax]⟩
  have hxact : ActsByMatrix c₁.γ x (Ax : Matrix (Fin 3) (Fin 3) F) := by
    intro u v hv
    exact c₁.equivariant ⟨x, x.2⟩ u v hv
  have hnormb : ∀ u : ↥(pCoreOf 2 L1), ∃ y : ↥(pCoreOf 2 L1),
      (y : G) = (bL2 : G) * (u : G) * (bL2 : G)⁻¹ := by
    intro u
    have hbQ1 : (bL2 : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 L1 (hH.h1.borel_le hbB2)
    exact ⟨⟨_, conj_mem_of_mem_normalizer hbQ1 u.2⟩, rfl⟩
  refine ⟨(x : G) * (bL2 : G), ?_, ?_⟩
  · rw [sup_bigB_left_of_le (hD.le_left hH)]
    exact Subgroup.mul_mem_sup x.2 hbB2
  · have hcomp := ActsByMatrix.mul hnormb hxact hBact
    have hmat_eq : ((Ax * B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.coe_mul, hAmat]
      have hAxcoe : (Ax : Matrix (Fin 3) (Fin 3) F) =
          sp4RadMat (c₁.α (⟨(x : G), x.2⟩ : ↥L1)) := rfl
      have hx' : c₁.α (⟨(x : G), x.2⟩ : ↥L1) = M * N⁻¹ := hx
      rw [hAxcoe, hBcoef]
      have hsp : sp4RadMat (c₁.α (⟨(x : G), x.2⟩ : ↥L1)) =
          sp4RadMat (M * N⁻¹) := by rw [hx']
      rw [hsp, Matrix.mul_smul, sp4RadMat_mul]
      rw [← sp4RadMat_mul, ← sp4RadMat_mul]
      rw [show M * N⁻¹ * N = M by group]
    rw [← hmat_eq]
    simpa [Matrix.GeneralLinearGroup.coe_mul] using hcomp

theorem Sp4qLocalData.linAction_left_of_pairing (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f)) (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ)
    (h₁ : ∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
      (z₁ : G) ∈ blockZ L1 →
        Multiplicative.toAdd (c₂.γ z₂) 1 = e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0))
    (h₂ : ∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
      (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
        Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t) :
      LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) (sp4Gamma (GaloisField 2 f)) := by
  classical
  refine ⟨c₁.γ, ?_, ?_⟩
  · intro p hp
    exact actsByMatrix_of_mem_sup_bigB hf hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hp
  · intro A hA
    exact exists_mem_sup_bigB_of_mem_sp4Gamma hf hH hD c₁ c₂ ρ e₁ e₂ h₁ h₂ hA

theorem Sp4qLocalData.linAction_left (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) (sp4Gamma (GaloisField 2 f)) := by
  obtain ⟨c₁⟩ := hD.exists_coord_left hf hH
  obtain ⟨c₂⟩ := hD.exists_coord_right hf hH
  obtain ⟨ρ, e₁, e₂, h₁, h₂⟩ := hD.exists_ringEquiv_pairing hf hH c₁ c₂
  exact hD.linAction_left_of_pairing hf hH c₁ c₂ ρ e₁ e₂ h₁ h₂

theorem Sp4qLocalData.linAction_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) :
    LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) (sp4Gamma (GaloisField 2 f)) := by
  have h := Sp4qLocalData.linAction_left (L1 := L2) (L2 := L1) (S := S) (f := f)
    hf hH.symm hD.symm
  rwa [bigB_comm L1 L2 S] at h

end CFSG.Quasithin.F112R.St84

end
