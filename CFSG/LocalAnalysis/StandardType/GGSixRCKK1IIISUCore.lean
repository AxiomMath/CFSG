module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUAct
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUS5
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISULevi

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.Open

variable {k : ℕ}

private noncomputable abbrev rckSUk_C (hk : 4 ≤ k) : Subgroup (SUG k) :=
  Subgroup.centralizer ({suR hk} : Set (SUG k))

@[simp] private theorem rckSUk_map_refl {n : ℕ} (M : Matrix (Fin n) (Fin n) SUF) :
    M.map (RingEquiv.refl SUF) = M := by
  change M.map id = M
  rw [Matrix.map_id]

private theorem rckSUk_exists_psi (hk : 4 ≤ k) (x : SUG k) (hx : x ∈ rckSUk_C hk) :
    ∃ ψ : GL (Fin 4) (ZMod 2),
      (∀ v : Fin 4 → ZMod 2,
        s5q (((ψ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v) ∧
      (((ψ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R) ∧
      (ψ ≠ s5tau) ∧
      (∀ v : Fin 4 → ZMod 2,
        x * suZ hk v * x⁻¹ =
          suZ hk (((ψ : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)) := by
  have hcomm : x * suR hk = suR hk * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hB : conjTr SUσ (((x : GL (Fin k) SUF)) :
        Matrix (Fin k) (Fin k) SUF) * antidiag k *
      (((x : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) = antidiag k :=
    (mem_SU.mp x.2).2
  have hGL : (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) =
      (suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF) :=
    congrArg (fun g : SUG k => (g : GL (Fin k) SUF)) hcomm
  have hGLconj : (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) *
      (x : GL (Fin k) SUF)⁻¹ = (suR hk : GL (Fin k) SUF) := by
    calc (x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF)⁻¹
        = ((x : GL (Fin k) SUF) * (suR hk : GL (Fin k) SUF)) *
            (x : GL (Fin k) SUF)⁻¹ := rfl
      _ = ((suR hk : GL (Fin k) SUF) * (x : GL (Fin k) SUF)) *
            (x : GL (Fin k) SUF)⁻¹ := by rw [hGL]
      _ = (suR hk : GL (Fin k) SUF) *
            ((x : GL (Fin k) SUF) * (x : GL (Fin k) SUF)⁻¹) := by rw [mul_assoc]
      _ = (suR hk : GL (Fin k) SUF) * 1 := by simp
      _ = (suR hk : GL (Fin k) SUF) := by simp
  have hr : (((x : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) *
      (((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map
        (RingEquiv.refl SUF)) *
        ((((x : GL (Fin k) SUF))⁻¹ : GL (Fin k) SUF) :
          Matrix (Fin k) (Fin k) SUF) =
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
    rw [rckSUk_map_refl]
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using
      congrArg (fun g : GL (Fin k) SUF => (g : Matrix (Fin k) (Fin k) SUF)) hGLconj
  obtain ⟨ψ, hq, hR, hτ, hconj⟩ :=
    rckSU_act hk (RingEquiv.refl SUF) (x : GL (Fin k) SUF) hB hr
  refine ⟨ψ, hq, hR, hτ rfl, ?_⟩
  intro v
  have hconjv : (((x : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF) * suCorner hk v *
      ((((x : GL (Fin k) SUF))⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      suCorner hk (((ψ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
    simpa only [rckSUk_map_refl] using hconj v
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    suZ_val]
  exact hconjv

private noncomputable def rckSUk_psi (hk : 4 ≤ k) (x : rckSUk_C hk) :
    GL (Fin 4) (ZMod 2) :=
  Classical.choose (rckSUk_exists_psi hk x x.2)

private theorem rckSUk_psi_spec (hk : 4 ≤ k) (x : rckSUk_C hk) :
    (∀ v : Fin 4 → ZMod 2,
      s5q (((rckSUk_psi hk x : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v) ∧
    (((rckSUk_psi hk x : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R) ∧
    (rckSUk_psi hk x ≠ s5tau) ∧
    (∀ v : Fin 4 → ZMod 2,
      (x : SUG k) * suZ hk v * (x : SUG k)⁻¹ =
        suZ hk (((rckSUk_psi hk x : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)) :=
  Classical.choose_spec (rckSUk_exists_psi hk x x.2)

private theorem rckSUk_psi_ext {ψ ψ' : GL (Fin 4) (ZMod 2)}
    (h : ∀ v : Fin 4 → ZMod 2,
      ((ψ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v =
        ((ψ' : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) :
    ψ = ψ' := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hv := congrFun (h (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hv

private theorem rckSUk_psi_unique (hk : 4 ≤ k) {x : SUG k} (hx : x ∈ rckSUk_C hk)
    {ψ : GL (Fin 4) (ZMod 2)}
    (h : ∀ v : Fin 4 → ZMod 2,
      x * suZ hk v * x⁻¹ =
        suZ hk (((ψ : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)) :
    rckSUk_psi hk ⟨x, hx⟩ = ψ := by
  apply rckSUk_psi_ext
  intro v
  apply suZ_injective hk
  rw [← (rckSUk_psi_spec hk ⟨x, hx⟩).2.2.2 v, h]

private theorem rckSUk_val_mul (a b : GL (Fin 4) (ZMod 2)) :
    (((a * b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) =
      ((a : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        ((b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  Units.val_mul a b

private theorem rckSUk_Phi_mul (hk : 4 ≤ k) (x y : rckSUk_C hk) :
    rckSUk_psi hk (x * y) = rckSUk_psi hk x * rckSUk_psi hk y := by
  refine rckSUk_psi_unique hk (x := ((x * y : rckSUk_C hk) : SUG k))
    ((rckSUk_C hk).mul_mem x.2 y.2) ?_
  intro v
  rw [rckSUk_val_mul, ← Matrix.mulVec_mulVec]
  rw [← (rckSUk_psi_spec hk x).2.2.2
    (((rckSUk_psi hk y : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)]
  rw [← (rckSUk_psi_spec hk y).2.2.2 v]
  simp only [Subgroup.coe_mul]
  group

private theorem rckSUk_Phi_one (hk : 4 ≤ k) :
    rckSUk_psi hk (1 : rckSUk_C hk) = 1 := by
  refine rckSUk_psi_unique hk (x := (1 : SUG k)) (rckSUk_C hk).one_mem ?_
  intro v
  simp [Units.val_one, Matrix.one_mulVec]

private noncomputable def rckSUk_Phi (hk : 4 ≤ k) :
    rckSUk_C hk →* GL (Fin 4) (ZMod 2) where
  toFun := rckSUk_psi hk
  map_one' := rckSUk_Phi_one hk
  map_mul' := rckSUk_Phi_mul hk

private theorem rckSUk_Phi_apply (hk : 4 ≤ k) (x : rckSUk_C hk) :
    rckSUk_Phi hk x = rckSUk_psi hk x := rfl

private noncomputable def rckSUk_Y (hk : 4 ≤ k) : Subgroup (GL (Fin 4) (ZMod 2)) :=
  ((pCoreOf 2 (rckSUk_C hk)).subgroupOf (rckSUk_C hk)).map (rckSUk_Phi hk)

private theorem rckSUk_mem_Y_iff (hk : 4 ≤ k) {y : GL (Fin 4) (ZMod 2)} :
    y ∈ rckSUk_Y hk ↔
      ∃ q : (pCoreOf 2 (rckSUk_C hk)).subgroupOf (rckSUk_C hk),
        rckSUk_Phi hk (q : rckSUk_C hk) = y := by
  rw [rckSUk_Y, Subgroup.mem_map]
  constructor
  · rintro ⟨q, hq, hqy⟩
    exact ⟨⟨q, hq⟩, hqy⟩
  · rintro ⟨q, hqy⟩
    exact ⟨q, q.2, hqy⟩

private theorem rckSUk_Y_isPGroup (hk : 4 ≤ k) : IsPGroup 2 (rckSUk_Y hk) := by
  rw [rckSUk_Y]
  have hp : IsPGroup 2 (pCoreOf 2 (rckSUk_C hk)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (rckSUk_C hk)
  have hp' : IsPGroup 2 ((pCoreOf 2 (rckSUk_C hk)).subgroupOf (rckSUk_C hk)) := by
    rw [← Subgroup.comap_subtype]
    exact hp.comap_of_injective (rckSUk_C hk).subtype (Subgroup.subtype_injective _)
  exact hp'.map (rckSUk_Phi hk)

private theorem rckSUk_Y_q (hk : 4 ≤ k) :
    ∀ y ∈ rckSUk_Y hk, ∀ v : Fin 4 → ZMod 2,
      s5q (((y : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v := by
  intro y hy v
  rw [rckSUk_mem_Y_iff] at hy
  obtain ⟨q, hq⟩ := hy
  rw [← hq, rckSUk_Phi_apply]
  exact (rckSUk_psi_spec hk (q : rckSUk_C hk)).1 v

private theorem rckSUk_Y_R (hk : 4 ≤ k) :
    ∀ y ∈ rckSUk_Y hk,
      ((y : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R := by
  intro y hy
  rw [rckSUk_mem_Y_iff] at hy
  obtain ⟨q, hq⟩ := hy
  rw [← hq, rckSUk_Phi_apply]
  exact (rckSUk_psi_spec hk (q : rckSUk_C hk)).2.1

private theorem rckSUk_conj_mem_Y (hk : 4 ≤ k) {c : SUG k} (hc : c ∈ rckSUk_C hk)
    {u : GL (Fin 4) (ZMod 2)} (hu : rckSUk_Phi hk ⟨c, hc⟩ = u)
    {y : GL (Fin 4) (ZMod 2)} (hy : y ∈ rckSUk_Y hk) :
    u * y * u⁻¹ ∈ rckSUk_Y hk := by
  rw [rckSUk_mem_Y_iff] at hy ⊢
  obtain ⟨q, hq⟩ := hy
  refine ⟨⟨⟨c, hc⟩ * (q : rckSUk_C hk) * ⟨c, hc⟩⁻¹, ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    have hqQ : (q : SUG k) ∈ pCoreOf 2 (rckSUk_C hk) := Subgroup.mem_subgroupOf.mp q.2
    have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (rckSUk_C hk) hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (Subgroup.mem_normalizer_iff.mp hnorm (q : SUG k)).mp hqQ
  · rw [map_mul, map_mul, map_inv, hu, hq]

private theorem rckSUk_h1_normalizes (hk : 4 ≤ k) :
    s5h1 ∈ Subgroup.normalizer (rckSUk_Y hk : Set (GL (Fin 4) (ZMod 2))) := by
  obtain ⟨c1, -, hc1r, -, hc1z, -⟩ := rckSU_levi hk
  have hc1 : c1 ∈ rckSUk_C hk := Subgroup.mem_centralizer_singleton_iff.mpr hc1r
  have hPhi1 : rckSUk_Phi hk ⟨c1, hc1⟩ = s5h1 := by
    refine rckSUk_psi_unique hk (x := c1) hc1 ?_
    intro v
    simpa using hc1z v
  have hc1inv : c1⁻¹ ∈ rckSUk_C hk := (rckSUk_C hk).inv_mem hc1
  have hPhi1inv : rckSUk_Phi hk ⟨c1⁻¹, hc1inv⟩ = s5h1⁻¹ := by
    have hsub : (⟨c1, hc1⟩ : rckSUk_C hk)⁻¹ = ⟨c1⁻¹, hc1inv⟩ := rfl
    rw [← hsub, map_inv, hPhi1]
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact rckSUk_conj_mem_Y hk hc1 hPhi1 hy
  · intro hy
    have hy' := rckSUk_conj_mem_Y hk hc1inv hPhi1inv hy
    have hgrp : s5h1⁻¹ * (s5h1 * y * s5h1⁻¹) * (s5h1⁻¹)⁻¹ = y := by group
    rwa [hgrp] at hy'

private theorem rckSUk_h2_normalizes (hk : 4 ≤ k) :
    s5h2 ∈ Subgroup.normalizer (rckSUk_Y hk : Set (GL (Fin 4) (ZMod 2))) := by
  obtain ⟨-, c2, -, hc2r, -, hc2z⟩ := rckSU_levi hk
  have hc2 : c2 ∈ rckSUk_C hk := Subgroup.mem_centralizer_singleton_iff.mpr hc2r
  have hPhi2 : rckSUk_Phi hk ⟨c2, hc2⟩ = s5h2 := by
    refine rckSUk_psi_unique hk (x := c2) hc2 ?_
    intro v
    simpa using hc2z v
  have hc2inv : c2⁻¹ ∈ rckSUk_C hk := (rckSUk_C hk).inv_mem hc2
  have hPhi2inv : rckSUk_Phi hk ⟨c2⁻¹, hc2inv⟩ = s5h2⁻¹ := by
    have hsub : (⟨c2, hc2⟩ : rckSUk_C hk)⁻¹ = ⟨c2⁻¹, hc2inv⟩ := rfl
    rw [← hsub, map_inv, hPhi2]
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact rckSUk_conj_mem_Y hk hc2 hPhi2 hy
  · intro hy
    have hy' := rckSUk_conj_mem_Y hk hc2inv hPhi2inv hy
    have hgrp : s5h2⁻¹ * (s5h2 * y * s5h2⁻¹) * (s5h2⁻¹)⁻¹ = y := by group
    rwa [hgrp] at hy'

private theorem rckSUk_mem_suZ0 (hk : 4 ≤ k) {z : SUG k} (hz : z ∈ suZ0 hk) :
    ∃ v : Fin 4 → ZMod 2, suZ hk v = z := by
  rw [suZ0, MonoidHom.mem_range] at hz
  obtain ⟨v, hv⟩ := hz
  exact ⟨v.toAdd, hv⟩

theorem rckSU_core (hk : 4 ≤ k) :
    pCoreOf 2 (Subgroup.centralizer ({suR hk} : Set (SUG k))) ≤
      Subgroup.centralizer ((suZ0 hk : Subgroup (SUG k)) : Set (SUG k)) := by
  have hs5 := rckSU_s5 (rckSUk_Y hk) (rckSUk_Y_isPGroup hk) (rckSUk_Y_q hk)
    (rckSUk_Y_R hk) (rckSUk_h1_normalizes hk) (rckSUk_h2_normalizes hk)
  intro q hqQ
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨v, rfl⟩ := rckSUk_mem_suZ0 hk hz
  have hqC : q ∈ rckSUk_C hk :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (rckSUk_C hk) hqQ
  let qC : rckSUk_C hk := ⟨q, hqC⟩
  have hmemQ : qC ∈ (pCoreOf 2 (rckSUk_C hk)).subgroupOf (rckSUk_C hk) :=
    Subgroup.mem_subgroupOf.mpr hqQ
  have hmemY : rckSUk_Phi hk qC ∈ rckSUk_Y hk :=
    Iff.mpr (rckSUk_mem_Y_iff (hk := hk)) ⟨⟨qC, hmemQ⟩, rfl⟩
  rcases hs5 (rckSUk_Phi hk qC) hmemY with h1 | htau
  · have h1' : rckSUk_psi hk qC = 1 := by
      rw [← rckSUk_Phi_apply hk qC]; exact h1
    have hconj : q * suZ hk v * q⁻¹ = suZ hk v := by
      have h := (rckSUk_psi_spec hk qC).2.2.2 v
      rw [h1'] at h
      simpa [Units.val_one, Matrix.one_mulVec] using h
    have hcomm : q * suZ hk v = suZ hk v * q := by
      calc q * suZ hk v = (q * suZ hk v * q⁻¹) * q := by group
        _ = suZ hk v * q := by rw [hconj]
    exact hcomm.symm
  · exact absurd htau (rckSUk_psi_spec hk qC).2.2.1

end CFSG.StandardType.RCKK1IIISU
