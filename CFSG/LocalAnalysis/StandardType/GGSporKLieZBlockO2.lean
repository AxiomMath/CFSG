module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZReduce
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
import CFSG.ClassicalGroups.Symplectic.InvariantForm
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.LocalCores.Components
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.StandardType.ClassicalBlocks Matrix

private theorem l937z_bo_pCore_eq_bot_of_subsingleton {G : Type} [Group G] [Subsingleton G] :
    pCore 2 G = ⊥ :=
  Subgroup.eq_bot_of_subsingleton _

private theorem l937z_bo_pCore_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : pCore 2 G = ⊥) : pCore 2 H = ⊥ := by
  rw [← pCore_map_iso 2 e, h, Subgroup.map_bot]

private theorem l937z_bo_gl_eq_one_of_fixes {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type}
    [Field E] (A : GL ι E)
    (h : ∀ v : ι → E, (A : Matrix ι ι E) *ᵥ v = v) : A = 1 := by
  apply Units.ext
  ext i j
  have hcol := congrFun (h (Pi.single j (1 : E))) i
  rw [Matrix.mulVec_single] at hcol
  simpa [Pi.single_apply, Matrix.one_apply] using hcol

private def l937z_bo_glOfSqZero {m : ℕ} {E : Type} [Ring E]
    (N : Matrix (Fin m) (Fin m) E) (hN : N * N = 0) : GL (Fin m) E :=
  ⟨1 + N, 1 - N, by
    calc (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero],
  by
    calc (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
      _ = 1 := by rw [hN, sub_zero]⟩

@[simp] private theorem l937z_bo_glOfSqZero_coe {m : ℕ} {E : Type} [Ring E]
    (N : Matrix (Fin m) (Fin m) E) (hN : N * N = 0) :
    ((l937z_bo_glOfSqZero N hN : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = 1 + N := rfl

private theorem l937z_bo_glOfSqZero_mulVec {m : ℕ} {E : Type} [Ring E]
    (N : Matrix (Fin m) (Fin m) E) (hN : N * N = 0) (v : Fin m → E) :
    ((l937z_bo_glOfSqZero N hN : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ v
      = v + N *ᵥ v := by
  rw [l937z_bo_glOfSqZero_coe, Matrix.add_mulVec, Matrix.one_mulVec]

private theorem l937z_bo_irreducible_GL {m : ℕ} {E : Type} [Field E]
    (W : Submodule E (Fin m → E))
    (hW : ∀ g : GL (Fin m) E, ∀ v ∈ W, (g : Matrix (Fin m) (Fin m) E) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  let a : Fin m → E := fun j => if j = i then 0 else -(w j) / (w i)
  let ei : Fin m → E := Pi.single i (1 : E)
  let N₁ : Matrix (Fin m) (Fin m) E := Matrix.vecMulVec a ei
  have hN₁w : N₁ *ᵥ w = (w i) • a := by
    dsimp only [N₁]
    rw [Matrix.vecMulVec_mulVec, single_dotProduct]
    simp
  have hN₁sq : N₁ * N₁ = 0 := by
    dsimp only [N₁]
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec]
    dsimp only [ei]
    rw [single_dotProduct]
    simp [a]
  have hAw : ((l937z_bo_glOfSqZero N₁ hN₁sq : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ w
      = w i • ei := by
    rw [l937z_bo_glOfSqZero_mulVec, hN₁w]
    ext j
    by_cases hji : j = i
    · subst hji; simp [a, ei]
    · simp only [Pi.add_apply, Pi.smul_apply, ei, Pi.single_eq_of_ne hji, mul_zero, add_zero, a,
        hji, if_false]
      rw [smul_eq_mul, smul_zero]
      field_simp [hi]
      ring
  have hmem := hW (l937z_bo_glOfSqZero N₁ hN₁sq) w hwW
  rw [hAw] at hmem
  have hei : ei ∈ W := by
    have := W.smul_mem ((w i)⁻¹) hmem
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  rw [← Finset.univ_sum_single v]
  refine W.sum_mem fun j _ => ?_
  have hsingle : Pi.single j (v j) = v j • Pi.single j (1 : E) := by
    ext k
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [Pi.single_eq_of_ne hkj]
  rw [hsingle]
  by_cases hji : j = i
  · subst hji; exact W.smul_mem (v j) hei
  · let ej : Fin m → E := Pi.single j (1 : E)
    let N₂ : Matrix (Fin m) (Fin m) E := Matrix.vecMulVec ej ei
    have hN₂sq : N₂ * N₂ = 0 := by
      dsimp only [N₂]
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec]
      dsimp only [ei]
      rw [single_dotProduct]
      simp [ej, hji, Ne.symm hji]
    have hN₂ei : N₂ *ᵥ ei = ej := by
      dsimp only [N₂]
      rw [Matrix.vecMulVec_mulVec]
      dsimp only [ei]
      rw [single_dotProduct]
      simp [ej]
    have hAw₂ : ((l937z_bo_glOfSqZero N₂ hN₂sq : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ
        ei = ei + ej := by
      rw [l937z_bo_glOfSqZero_mulVec, hN₂ei]
    have hmem₂ := hW (l937z_bo_glOfSqZero N₂ hN₂sq) _ hei
    rw [hAw₂] at hmem₂
    have hsub : ej = (ei + ej) - ei := by abel
    change v j • ej ∈ W
    rw [hsub]
    exact W.smul_mem (v j) (W.sub_mem hmem₂ hei)

private theorem l937z_bo_irreducible_Sp {n : ℕ} {K : Type} [Field K]
    (W : Submodule K (Fin n ⊕ Fin n → K))
    (hW : ∀ g ∈ StatedSp n K, ∀ v ∈ W,
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  CFSG.ClassicalGroups.Symplectic.eq_bot_or_eq_top_of_invariant_statedSp W hW

private theorem l937z_bo_irreducible_GU {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) (W : Submodule E (Fin m → E))
    (hW : ∀ g ∈ GUFull m Q E, ∀ v ∈ W, (g : Matrix (Fin m) (Fin m) E) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  have hQ2 : 2 ≤ Q := by
    have h1 : 2 ≤ Nat.card E := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    nlinarith [hE]
  have hQne : Q ≠ 0 := by omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show Q + 1 ≠ 1 by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpdvd' : p ∣ Nat.card E - 1 := by
    rw [hE]
    refine hpdvd.trans ⟨Q - 1, ?_⟩
    have hfac : (Q + 1) * (Q - 1) = Q ^ 2 - 1 := by
      have hQ1 : 1 ≤ Q := by omega
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have h2 : (Q + 1) * Q = Q ^ 2 + Q := by ring
      rw [h2]
      omega
    exact hfac.symm
  have hpdvd'' : p ∣ Nat.card Eˣ := by
    rw [Nat.card_units]
    exact hpdvd'
  obtain ⟨μ, hμord⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) p hpdvd''
  have hμne : μ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hμord
    exact hp.ne_one hμord.symm
  have hμpowU : μ ^ (Q + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hμord]
    exact hpdvd
  have hμpow : (μ : E) ^ (Q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hμpowU, Units.val_one]
  let d : Fin m → E := fun k => if k = i then (μ : E) else 1
  have hd : ∀ k, d k ≠ 0 := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [d]
    · simp [d, hki]
  let D : Matrix (Fin m) (Fin m) E := Matrix.diagonal d
  have hD : D * Matrix.diagonal (fun k => (d k)⁻¹) = 1 := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.diagonal_apply, hd]
    · simp [Matrix.diagonal_apply, hab]
  let Dunit : GL (Fin m) E :=
    Units.mkOfMulEqOne D (Matrix.diagonal (fun k => (d k)⁻¹)) hD
  have hDmem : Dunit ∈ GUFull m Q E := by
    apply Subgroup.subset_closure
    change ((D.map (· ^ Q))ᵀ * D = 1)
    have hmap : D.map (· ^ Q) = Matrix.diagonal (fun k => d k ^ Q) := by
      ext a b
      simp [D, Matrix.map_apply, Matrix.diagonal_apply, hQne]
    rw [hmap, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp only [Matrix.diagonal_apply, if_true, d]
        rw [← pow_succ, hμpow]
      · simp [Matrix.diagonal_apply, d, hai]
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
  have hDw : D *ᵥ w ∈ W := hW Dunit hDmem w hwW
  have hDsub : (D - 1) *ᵥ w ∈ W := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact W.sub_mem hDw hwW
  have hDsub_eq : (D - 1) *ᵥ w = (((μ : E) - 1) * w i) • Pi.single i (1 : E) := by
    dsimp only [D]
    ext a
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, Matrix.mulVec_diagonal]
    by_cases hai : a = i
    · subst hai
      simp [d, Pi.single_eq_same]
      ring
    · simp [d, hai, Pi.single_eq_of_ne hai]
  have hmu_ne : ((μ : E) - 1) ≠ 0 := sub_ne_zero.mpr (fun h => hμne (Units.ext h))
  have hei : Pi.single i (1 : E) ∈ W := by
    rw [hDsub_eq] at hDsub
    have hcoef : (((μ : E) - 1) * w i) ≠ 0 := mul_ne_zero hmu_ne hi
    have h1 := W.smul_mem ((((μ : E) - 1) * w i)⁻¹) hDsub
    rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at h1
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  rw [← Finset.univ_sum_single v]
  refine W.sum_mem fun j _ => ?_
  have hsingle : Pi.single j (v j) = v j • Pi.single j (1 : E) := by
    ext k
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [Pi.single_eq_of_ne hkj]
  rw [hsingle]
  by_cases hji : j = i
  · subst hji; exact W.smul_mem (v j) hei
  · let σ : Equiv.Perm (Fin m) := Equiv.swap i j
    let P : Matrix (Fin m) (Fin m) E := Equiv.Perm.permMatrix E σ
    have hP : P * Equiv.Perm.permMatrix E σ⁻¹ = 1 := by
      dsimp only [P]
      rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
    let Punit : GL (Fin m) E := Units.mkOfMulEqOne P (Equiv.Perm.permMatrix E σ⁻¹) hP
    have hPmem : Punit ∈ GUFull m Q E := by
      apply Subgroup.subset_closure
      change ((P.map (· ^ Q))ᵀ * P = 1)
      have hmap : P.map (· ^ Q) = P := by
        ext a b
        simp [P, σ, Equiv.Perm.permMatrix, Matrix.map_apply, hQne]
      rw [hmap, Matrix.transpose_permMatrix]
      rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
    have hPei : P *ᵥ (Pi.single i (1 : E)) = Pi.single j (1 : E) := by
      dsimp only [P]
      rw [Matrix.permMatrix_mulVec]
      ext k
      by_cases hk : k = j
      · subst hk
        simp [σ, Equiv.swap_apply_def, hji]
      · by_cases hk2 : k = i
        · subst hk2
          simp [σ, Equiv.swap_apply_def, hji, hk]
        · simp [σ, Equiv.swap_apply_def, hk, hk2, Pi.single_eq_of_ne hk]
    have hmem := hW Punit hPmem _ hei
    change P *ᵥ Pi.single i (1 : E) ∈ W at hmem
    rw [hPei] at hmem
    exact W.smul_mem (v j) hmem

private noncomputable def l937z_bo_fixedSpace {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (GL ι F)) : Submodule F (ι → F) :=
  ⨅ n : ↥(pCore 2 ↥G),
    LinearMap.ker (Matrix.mulVecLin (((n : ↥G) : GL ι F) : Matrix ι ι F) - 1)

private theorem l937z_bo_mem_fixedSpace {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (GL ι F)) (v : ι → F) :
    v ∈ l937z_bo_fixedSpace G ↔ ∀ n : ↥(pCore 2 ↥G),
      (((n : ↥G) : GL ι F) : Matrix ι ι F) *ᵥ v = v := by
  rw [l937z_bo_fixedSpace, Submodule.mem_iInf]
  constructor
  · intro h n
    have h' := h n
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, sub_eq_zero] at h'
    exact h'
  · intro h n
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, sub_eq_zero]
    exact h n

private theorem l937z_bo_fixedSpace_invariant {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Subgroup (GL ι F)) {g : GL ι F} (hg : g ∈ G) :
    ∀ v ∈ l937z_bo_fixedSpace G,
      (g : Matrix ι ι F) *ᵥ v ∈ l937z_bo_fixedSpace G := by
  intro v hv
  rw [l937z_bo_mem_fixedSpace G] at hv ⊢
  intro n
  let gG : ↥G := ⟨g, hg⟩
  have hmem : gG⁻¹ * (n : ↥G) * gG ∈ pCore 2 ↥G :=
    (inferInstance : (pCore 2 ↥G).Normal).conj_mem (n : ↥G) n.2 gG⁻¹
  let m : ↥(pCore 2 ↥G) := ⟨gG⁻¹ * (n : ↥G) * gG, hmem⟩
  have hmg : ((m : ↥G) : GL ι F)
      = (gG : GL ι F)⁻¹ * ((n : ↥G) : GL ι F) * (gG : GL ι F) := rfl
  have hmat : (((n : ↥G) : GL ι F) : Matrix ι ι F) * ((g : GL ι F) : Matrix ι ι F)
      = ((g : GL ι F) : Matrix ι ι F) * (((m : ↥G) : GL ι F) : Matrix ι ι F) := by
    have h1 : ((n : ↥G) : GL ι F) * (gG : GL ι F)
        = (gG : GL ι F) * ((m : ↥G) : GL ι F) := by
      have h2 : (n : ↥G) * gG = gG * (m : ↥G) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [show ((m : ↥G) : GL ι F)
          = (gG : GL ι F)⁻¹ * ((n : ↥G) : GL ι F) * (gG : GL ι F) from hmg]
        group
      simpa using congrArg (fun x : ↥G => (x : GL ι F)) h2
    simpa using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) h1
  calc (((n : ↥G) : GL ι F) : Matrix ι ι F) *ᵥ (((g : GL ι F) : Matrix ι ι F) *ᵥ v)
      = ((((n : ↥G) : GL ι F) : Matrix ι ι F) * ((g : GL ι F) : Matrix ι ι F)) *ᵥ v := by
        rw [Matrix.mulVec_mulVec]
    _ = (((g : GL ι F) : Matrix ι ι F) * (((m : ↥G) : GL ι F) : Matrix ι ι F)) *ᵥ v := by
        rw [hmat]
    _ = ((g : GL ι F) : Matrix ι ι F) *ᵥ ((((m : ↥G) : GL ι F) : Matrix ι ι F) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec]
    _ = ((g : GL ι F) : Matrix ι ι F) *ᵥ v := by rw [hv m]

private theorem l937z_bo_fixedSpace_card_modEq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (G : Subgroup (GL ι F)) :
    Nat.card (ι → F) ≡ Nat.card ↥(l937z_bo_fixedSpace G) [MOD 2] := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI actG : MulAction ↥G (ι → F) := MulAction.compHom (ι → F) G.subtype
  letI actN : MulAction ↥(pCore 2 ↥G) (ι → F) :=
    MulAction.compHom (ι → F) (pCore 2 ↥G).subtype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcong := IsPGroup.card_modEq_card_fixedPoints (p := 2)
      (pCore_isPGroup (p := 2) (G := ↥G)) (ι → F)
  have hcard : Nat.card ↥(l937z_bo_fixedSpace G)
      = Nat.card ↥(MulAction.fixedPoints (pCore 2 ↥G) (ι → F)) := by
    apply Nat.card_congr
    refine ⟨fun x => ⟨x.1, ?_⟩, fun x => ⟨x.1, ?_⟩, fun x => rfl, fun x => rfl⟩
    · rw [MulAction.mem_fixedPoints]
      intro n
      exact (l937z_bo_mem_fixedSpace G x.1).mp x.2 n
    · rw [l937z_bo_mem_fixedSpace]
      intro n
      exact (MulAction.mem_fixedPoints.mp x.2) n
  rwa [← hcard] at hcong

private theorem l937z_bo_fixedSpace_ne_bot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (G : Subgroup (GL ι F)) (hcard : Even (Nat.card (ι → F))) :
    l937z_bo_fixedSpace G ≠ ⊥ := by
  have hcong := l937z_bo_fixedSpace_card_modEq G
  have hEven : Even (Nat.card ↥(l937z_bo_fixedSpace G)) := by
    rw [Nat.even_iff] at hcard ⊢
    rw [Nat.ModEq] at hcong
    omega
  have hpos : 0 < Nat.card ↥(l937z_bo_fixedSpace G) := Nat.card_pos
  have hne1 : Nat.card ↥(l937z_bo_fixedSpace G) ≠ 1 := by
    intro h1
    rw [h1] at hEven
    norm_num at hEven
  have h2 : 1 < Nat.card ↥(l937z_bo_fixedSpace G) :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hpos.ne', hne1⟩
  haveI : Fintype ↥(l937z_bo_fixedSpace G) := Fintype.ofFinite _
  have h2' : 1 < Fintype.card ↥(l937z_bo_fixedSpace G) := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h2' (0 : ↥(l937z_bo_fixedSpace G))
  exact (Submodule.ne_bot_iff (l937z_bo_fixedSpace G)).mpr
    ⟨x.1, x.2, fun h0 => hx (Subtype.ext h0)⟩

private theorem l937z_bo_pCore_eq_bot_of_irreducible {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] (G : Subgroup (GL ι F))
    (hirr : ∀ W : Submodule F (ι → F),
      (∀ g ∈ G, ∀ v ∈ W, (g : Matrix ι ι F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hcard : Even (Nat.card (ι → F))) :
    pCore 2 ↥G = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hW : l937z_bo_fixedSpace G = ⊤ := by
    rcases hirr (l937z_bo_fixedSpace G)
      (fun g hg v hv => l937z_bo_fixedSpace_invariant G hg v hv) with h | h
    · exact absurd h (l937z_bo_fixedSpace_ne_bot G hcard)
    · exact h
  have hfix : ∀ v : ι → F, (((n : ↥G) : GL ι F) : Matrix ι ι F) *ᵥ v = v := by
    intro v
    have hv : v ∈ l937z_bo_fixedSpace G := by rw [hW]; exact Submodule.mem_top
    exact (l937z_bo_mem_fixedSpace G v).mp hv ⟨n, hn⟩
  exact Subtype.ext (l937z_bo_gl_eq_one_of_fixes (n : GL ι F) hfix)

private noncomputable def l937z_bo_subgroupCongr {G : Type} [Group G] {A B : Subgroup G}
    (h : A = B) : ↥A ≃* ↥B where
  toFun x := ⟨x.1, by rw [← h]; exact x.2⟩
  invFun x := ⟨x.1, by rw [h]; exact x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

private theorem l937z_bo_pCore_eq_bot_of_isQuasisimple {G : Type} [Group G] [Finite G]
    (hQ : CFSG.IsQuasisimple G) (hZ : Subgroup.center G = ⊥) : pCore 2 G = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect G := hQ.1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
      (inferInstance : (pCore 2 G).Normal) with htop | hle
  · exfalso
    have hntq : Nontrivial (G ⧸ Subgroup.center G) := by
      obtain ⟨a, b, hab⟩ := hQ.2.2
      exact ⟨a, 1, fun h1 => hab (by rw [h1, one_mul, mul_one])⟩
    haveI : Nontrivial G := by
      haveI := hntq
      obtain ⟨y, hy⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨x, 1, fun h1 => hy (by simp [h1])⟩
    have e : ↥(pCore 2 G) ≃* G := (l937z_bo_subgroupCongr htop).trans Subgroup.topEquiv
    haveI : Group.IsNilpotent ↥(pCore 2 G) := pCore_isNilpotent (p := 2) (G := G)
    haveI : Group.IsNilpotent G := Group.nilpotent_of_mulEquiv e
    haveI : Group.IsSolvable G := inferInstance
    exact Group.IsPerfect.not_isSolvable G inferInstance
  · have hx' : x ∈ Subgroup.center G := hle hx
    rwa [hZ] at hx'

private noncomputable def l937z_bo_comapMulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (K : Subgroup H) : ↥(K.comap e.toMonoidHom) ≃* ↥K where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by
    rw [Subgroup.mem_comap]
    simpa using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

private noncomputable def l937z_bo_statedOmega_mulEquiv {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) :
    ↥(StatedOmega ⇑Φ) ≃* ↥(CFSG.RankThree.Classical2.orthDerived Φ) :=
  (l937z_bo_subgroupCongr
      (CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl)).trans
    (l937z_bo_comapMulEquiv (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K)
      (CFSG.RankThree.Classical2.orthDerived Φ))

private theorem l937z_bo_even_card_of_charP_two {E : Type} [Field E] [Fintype E] [CharP E 2] :
    Even (Fintype.card E) := by
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  rw [hn]
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero n.ne_zero
  rw [hk]
  refine ⟨2 ^ k, ?_⟩
  rw [pow_succ]
  ring

private theorem l937z_bo_even_pow_of_pos {a m : ℕ} (ha : Even a) (hm : 0 < m) : Even (a ^ m) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨(c + c) ^ k * c, ?_⟩
  rw [pow_succ]
  ring

theorem pCore_two_GL_eq_bot {E : Type} [Field E] [Finite E] [CharP E 2] (m : ℕ) :
    pCore 2 (GL (Fin m) E) = ⊥ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact l937z_bo_pCore_eq_bot_of_subsingleton
  · letI : Fintype E := Fintype.ofFinite E
    have htop := l937z_bo_pCore_eq_bot_of_irreducible (ι := Fin m) (F := E) (G := ⊤) ?_ ?_
    · exact l937z_bo_pCore_eq_bot_of_mulEquiv Subgroup.topEquiv htop
    · intro W hW
      exact l937z_bo_irreducible_GL W (fun g v hv => hW g trivial v hv)
    · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      exact l937z_bo_even_pow_of_pos (l937z_bo_even_card_of_charP_two (E := E)) hm

theorem pCore_two_StatedSp_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    pCore 2 ↥(StatedSp n K) = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact l937z_bo_pCore_eq_bot_of_subsingleton
  · letI : Fintype K := Fintype.ofFinite K
    refine l937z_bo_pCore_eq_bot_of_irreducible (ι := Fin n ⊕ Fin n) (F := K)
      (G := StatedSp n K) ?_ ?_
    · intro W hW
      exact l937z_bo_irreducible_Sp W hW
    · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
      exact l937z_bo_even_pow_of_pos (l937z_bo_even_card_of_charP_two (E := K)) (by omega)

theorem pCore_two_GUFull_eq_bot {E : Type} [Field E] [Finite E] [CharP E 2] (m Q : ℕ)
    (hE : Nat.card E = Q ^ 2) : pCore 2 ↥(GUFull m Q E) = ⊥ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact l937z_bo_pCore_eq_bot_of_subsingleton
  · letI : Fintype E := Fintype.ofFinite E
    refine l937z_bo_pCore_eq_bot_of_irreducible (ι := Fin m) (F := E) (G := GUFull m Q E) ?_ ?_
    · intro W hW
      exact l937z_bo_irreducible_GU hE W hW
    · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      exact l937z_bo_even_pow_of_pos (l937z_bo_even_card_of_charP_two (E := E)) hm

theorem pCore_two_StatedOmega_eq_bot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (hd : Fintype.card ι = 0 ∨ 6 ≤ Fintype.card ι) : pCore 2 ↥(StatedOmega ⇑Φ) = ⊥ := by
  rcases hd with h0 | h6
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    exact l937z_bo_pCore_eq_bot_of_subsingleton
  · letI : Fintype K := Fintype.ofFinite K
    haveI : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
      Finite.of_injective
        (fun e : (ι → K) ≃ₗ[K] (ι → K) => (e : (ι → K) → (ι → K)))
        (fun _ _ h => LinearEquiv.ext (fun v => congrFun h v))
    haveI : Finite ↥(CFSG.RankThree.Classical2.orthDerived Φ) :=
      Finite.of_injective
        (fun x : ↥(CFSG.RankThree.Classical2.orthDerived Φ) =>
          (x : (ι → K) ≃ₗ[K] (ι → K))) (fun a b h => Subtype.ext h)
    have hfin : 6 ≤ Module.finrank K (ι → K) := by
      rwa [Module.finrank_fintype_fun_eq_card]
    obtain ⟨hQ, hZ, -⟩ := CFSG.StandardType.OrthRestOdd.orthDerived_facts Φ hΦ hfin
    exact l937z_bo_pCore_eq_bot_of_mulEquiv (l937z_bo_statedOmega_mulEquiv Φ).symm
      (l937z_bo_pCore_eq_bot_of_isQuasisimple hQ hZ)

end CFSG.StandardType.SporadicShape
