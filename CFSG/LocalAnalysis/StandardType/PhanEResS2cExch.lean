module

public import CFSG.LocalAnalysis.StandardType.PhanEResS2c
public import CFSG.LocalAnalysis.StandardType.PhanEFlagNormalX

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Flag

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

private theorem pls2x_sgv_mulVec {n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (g g' : GL (Fin n) K)
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j)) (v : Fin n → K) :
    sgv K f n (glLin g v) = glLin g' (sgv K f n v) := by
  rw [glLin_apply, glLin_apply]
  ext i
  rw [sgv_apply]
  change ((sg K f : K →+* K) : K → K) ((↑g *ᵥ v) i) =
    ((↑g' : Matrix (Fin n) (Fin n) K) *ᵥ (sgv K f n) v) i
  rw [RingHom.map_mulVec (sg K f : K →+* K)]
  have hmap : ((g : Matrix (Fin n) (Fin n) K).map (sg K f : K →+* K)) =
      (g' : Matrix (Fin n) (Fin n) K) := by
    ext a b
    rw [Matrix.map_apply, hgg']
    rfl
  rw [hmap]
  rfl

private theorem pls2x_sgS_map (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (g g' : GL (Fin n) K)
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j))
    (U : Submodule K (Fin n → K)) :
    sgS K f n (U.map (glLin g).toLinearMap) =
      (sgS K f n U).map (glLin g').toLinearMap := by
  apply le_antisymm
  · intro v hv
    rw [mem_sgS, Submodule.mem_map] at hv
    obtain ⟨u, hu, hueq⟩ := hv
    rw [Submodule.mem_map]
    refine ⟨sgv K f n u, ?_, ?_⟩
    · rw [mem_sgS, sgv_sgv hK]
      exact hu
    · show (glLin g') (sgv K f n u) = v
      rw [← pls2x_sgv_mulVec hK g g' hgg' u]
      have hueq' : (glLin g) u = sgv K f n v := hueq
      change sgv K f n ((glLin g) u) = v
      rw [hueq', sgv_sgv hK]
  · intro v hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, hweq⟩ := hv
    rw [mem_sgS] at hw
    rw [mem_sgS, ← hweq]
    have hweq' : (glLin g') w = v := hweq
    change (sgv K f n ((glLin g') w)) ∈ Submodule.map (glLin g).toLinearMap U
    have hgg'' : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j =
        sg K f ((g' : Matrix (Fin n) (Fin n) K) i j) := by
      intro i j
      rw [hgg', sg_sg hK]
    have hstep : sgv K f n ((glLin g') w) = (glLin g) (sgv K f n w) :=
      pls2x_sgv_mulVec hK g' g hgg'' w
    rw [hstep]
    exact Submodule.mem_map_of_mem hw

theorem flagSg_flagAct (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} (g g' : GL (Fin n) K)
    (hgg' : ∀ i j, (g' : Matrix (Fin n) (Fin n) K) i j =
      sg K f ((g : Matrix (Fin n) (Fin n) K) i j))
    (x : FlagK K n) : flagSg hK (flagAct g x) = flagAct g' (flagSg hK x) := by
  apply FlagK.ext
  intro j
  rw [flagSg_E, flagAct, flagMap_E, flagAct, flagMap_E, flagSg_E]
  exact pls2x_sgS_map hK g g' hgg' (x.E j)

private theorem pls2x_toGL_map_apply {n : ℕ} (B : SpecialLinearGroup (Fin n) K) (i j : Fin n) :
    (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f : K →+* K) B) :
      Matrix (Fin n) (Fin n) K) i j =
      sg K f (((SpecialLinearGroup.toGL B : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j) := by
  rw [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem flagSg_stdFlag (hK : Nat.card K = (2 ^ f) ^ 2) (n : ℕ) :
    flagSg hK (stdFlag K n) = stdFlag K n := by
  apply FlagK.ext
  intro j
  rw [flagSg_E]
  exact sgS_Vsub j

private theorem pls2x_flagSg_toGL_std (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ}
    (B : SpecialLinearGroup (Fin n) K) :
    flagSg hK (flagAct (SpecialLinearGroup.toGL B) (stdFlag K n)) =
      flagAct (SpecialLinearGroup.toGL (SpecialLinearGroup.map (sg K f : K →+* K) B))
        (stdFlag K n) := by
  rw [flagSg_flagAct hK _ _ (pls2x_toGL_map_apply (f := f) B) (stdFlag K n),
    flagSg_stdFlag]

private theorem pls2x_kapMat_false_one {m : ℕ}
    (B P : SpecialLinearGroup (Fin (m + 1)) K) (hP : P = 1) :
    kapMat (sg K f : K →+* K) false P B =
      SpecialLinearGroup.map (sg K f : K →+* K) B := by
  rw [hP]
  simp [kapMat]

private theorem pls2x_isCut_02 : IsCut 2 [0, 2] where
  head := rfl
  last := rfl
  strict := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst i
    decide

private theorem pls2x_mem_refSet_02 (x : FlagK K 2) : x ∈ refSet K 2 [0, 2] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa [List.getD, FlagK.E_zero] using (Vsub_zero (K := K) (n := 2)).symm
  · rw [show ([0, 2].getD 1 0) = 2 from rfl, Vsub_self]
    refine Submodule.eq_top_of_finrank_eq ?_
    simpa using x.dim 2 (le_refl 2)

theorem exists_chart_exchA1A1 {I C : Type} (X : ChamberSystem I C)
    (hK : Nat.card K = (2 ^ f) ^ 2) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X ((flagSys K 1).prod (flagSys K 1))) (N₁ N₂ : GL (Fin 2) K)
    (hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).1 ∈ refSet K 2 [0, 2])
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c)
    (P₁ P₂ : SpecialLinearGroup (Fin 2) K) (hP₁ : P₁ = 1) (hP₂ : P₂ = 1)
    (hψ : ∀ B₁ B₂ : SpecialLinearGroup (Fin 2) K, ∀ c ∈ S,
      Θ₀.Φ c = (flagAct (SpecialLinearGroup.toGL B₁) (stdFlag K 2),
        flagAct (SpecialLinearGroup.toGL B₂) (stdFlag K 2)) →
        Θ₀.Φ (ψ c) =
          (flagAct N₁ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P₂ B₂))
              (stdFlag K 2)),
            flagAct N₂ (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false P₁ B₁))
              (stdFlag K 2)))) :
    ∃ Θ : ChamberIso X ((flagSys K 1).prod (flagSys K 1)),
      (∀ c, c ∈ S ↔ Θ.Φ c ∈ (Set.univ : Set (FlagK K 2 × FlagK K 2))) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) = psiA1A1 hK (Θ.Φ c) := by
  have hd02 : IsCut 2 [0, 2] := pls2x_isCut_02
  have hallS : ∀ c, c ∈ S := fun c => (hS c).mpr (pls2x_mem_refSet_02 (Θ₀.Φ c).1)
  have hkey : ∀ c ∈ S, Θ₀.Φ (ψ c) =
      (flagAct N₁ (flagSg hK (Θ₀.Φ c).2), flagAct N₂ (flagSg hK (Θ₀.Φ c).1)) := by
    intro c hc
    have hx1 : (Θ₀.Φ c).1 ∈ refSet K 2 [0, 2] := (hS c).mp hc
    have hx2 : (Θ₀.Φ c).2 ∈ refSet K 2 [0, 2] := pls2x_mem_refSet_02 _
    obtain ⟨B₁, _, hB1⟩ := exists_blockSL_of_mem_refSet hd02 hx1
    obtain ⟨B₂, _, hB2⟩ := exists_blockSL_of_mem_refSet hd02 hx2
    have hk₂ := pls2x_kapMat_false_one (f := f) (m := 1) B₂ P₂ hP₂
    have hk₁ := pls2x_kapMat_false_one (f := f) (m := 1) B₁ P₁ hP₁
    have hs₂ := pls2x_flagSg_toGL_std (f := f) hK B₂
    have hs₁ := pls2x_flagSg_toGL_std (f := f) hK B₁
    have hpsi := hψ B₁ B₂ c hc (Prod.ext hB1 hB2)
    rw [hk₂, hk₁] at hpsi
    rw [hpsi, hB2, hB1, ← hs₂, ← hs₁]
  have hinv : ∀ x : FlagK K 2 × FlagK K 2,
      (flagAct N₁ (flagSg hK (flagAct N₂ (flagSg hK x.1))),
        flagAct N₂ (flagSg hK (flagAct N₁ (flagSg hK x.2)))) = x := by
    intro x
    let c : C := Θ₀.Φ.symm x
    have hc : c ∈ S := hallS c
    have h1 := hkey c hc
    have h2 := hkey (ψ c) (hallS (ψ c))
    rw [hψψ c hc, h1, Θ₀.Φ.apply_symm_apply x] at h2
    exact h2.symm
  obtain ⟨e₁, e₂, heq⟩ := exists_normalForm_psiA1A1 hK N₁ N₂ hinv
  let Θ₁ : ChamberIso ((flagSys K 1).prod (flagSys K 1))
      ((flagSys K 1).prod (flagSys K 1)) :=
    (flagMapIso (glLin e₁)).prodCongr (flagMapIso (glLin e₂))
  let Θ : ChamberIso X ((flagSys K 1).prod (flagSys K 1)) := Θ₀.trans Θ₁
  have hΘ : ∀ c, Θ.Φ c = (flagAct e₁ (Θ₀.Φ c).1, flagAct e₂ (Θ₀.Φ c).2) := fun c => rfl
  refine ⟨Θ, fun c => by simp [hallS c], fun c hc => ?_⟩
  have h1 : flagAct e₂⁻¹ (Θ.Φ c).2 = (Θ₀.Φ c).2 := by
    rw [hΘ c, flagAct_inv_flagAct]
  have h2 : flagAct e₁⁻¹ (Θ.Φ c).1 = (Θ₀.Φ c).1 := by
    rw [hΘ c, flagAct_inv_flagAct]
  have hgoal := heq (Θ.Φ c)
  rw [h1, h2, hΘ c] at hgoal
  rw [hΘ (ψ c), hkey c hc, hΘ c]
  simpa [psiA1A1] using hgoal

theorem exists_chart_exch3 {I C : Type} (X : ChamberSystem I C)
    (hK : Nat.card K = (2 ^ f) ^ 2) {dz : List ℕ} (hdz : IsCut 2 dz) (S : Set C) (ψ : C → C)
    (Θ₀ : ChamberIso X (((flagSys K 1).prod (flagSys K 1)).prod (flagSys K 1)))
    (Nx Ny Nz : GL (Fin 2) K) (hNz : StabV 2 dz Nz)
    (hS : ∀ c, c ∈ S ↔ (Θ₀.Φ c).2 ∈ refSet K 2 dz)
    (hψS : ∀ c ∈ S, ψ c ∈ S) (hψψ : ∀ c ∈ S, ψ (ψ c) = c)
    (Px Py : SpecialLinearGroup (Fin 2) K) (hPx : Px = 1) (hPy : Py = 1) (polz : Bool)
    (Pz : SpecialLinearGroup (Fin 2) K)
    (hPz : (Pz : Matrix (Fin 2) (Fin 2) K) =
      if polz then (revBlocks K 2 dz : Matrix (Fin 2) (Fin 2) K) else 1)
    (hψ : ∀ Bx By : SpecialLinearGroup (Fin 2) K, ∀ Az ∈ blockSL K 1 dz, ∀ c ∈ S,
      Θ₀.Φ c = ((flagAct (SpecialLinearGroup.toGL Bx) (stdFlag K 2),
        flagAct (SpecialLinearGroup.toGL By) (stdFlag K 2)),
          flagAct (SpecialLinearGroup.toGL Az) (stdFlag K 2)) →
        Θ₀.Φ (ψ c) =
          ((flagAct Nx (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false Py By))
              (stdFlag K 2)),
            flagAct Ny (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) false Px Bx))
              (stdFlag K 2))),
            flagAct Nz (flagAct (SpecialLinearGroup.toGL (kapMat (sg K f : K →+* K) polz Pz Az))
              (stdFlag K 2))))
    (plz : List Bool)
    (hplz : ∀ b, b + 1 < dz.length → 2 ≤ blockSize dz b → plz.getD b false = polz) :
    ∃ Θ : ChamberIso X (((flagSys K 1).prod (flagSys K 1)).prod (flagSys K 1)),
      (∀ c, c ∈ S ↔ Θ.Φ c ∈
        (Set.univ : Set (FlagK K 2 × FlagK K 2)) ×ˢ refSet K 2 dz) ∧
      ∀ c ∈ S, Θ.Φ (ψ c) =
        Prod.map (psiA1A1 hK) (flagPsi' K f hK 2 dz plz) (Θ.Φ c) := by
  have hd02 : IsCut 2 [0, 2] := pls2x_isCut_02
  let M : GL (Fin 2) K := pathMat K 2 dz Nz polz
  let polrep : List Bool := List.replicate (dz.length - 1) polz
  have hM : StabV 2 dz M := stabV_pathMat hdz hNz polz
  have hthirdKey : ∀ c ∈ S, (Θ₀.Φ (ψ c)).2 =
      flagAct M (flagPsi hK hdz polrep (Θ₀.Φ c).2) := by
    intro c hc
    have hx3 : (Θ₀.Φ c).2 ∈ refSet K 2 dz := (hS c).mp hc
    obtain ⟨Az, hAz, hAzEq⟩ := exists_blockSL_of_mem_refSet hdz hx3
    obtain ⟨Bx, _, hBx⟩ :=
      exists_blockSL_of_mem_refSet hd02 (pls2x_mem_refSet_02 (Θ₀.Φ c).1.1)
    obtain ⟨By, _, hBy⟩ :=
      exists_blockSL_of_mem_refSet hd02 (pls2x_mem_refSet_02 (Θ₀.Φ c).1.2)
    have hpsi := hψ Bx By Az hAz c hc (Prod.ext (Prod.ext hBx hBy) hAzEq)
    rw [hpsi, hAzEq]
    exact flagAct_kapMat_stdFlag hK hdz Nz polz Pz hPz hAz
  have hthirdInv : ∀ x ∈ refSet K 2 dz,
      flagAct M (flagPsi hK hdz polrep (flagAct M (flagPsi hK hdz polrep x))) = x := by
    intro x hx
    let c : C := Θ₀.Φ.symm ((stdFlag K 2, stdFlag K 2), x)
    have hc : c ∈ S := (hS c).mpr (by simpa [c] using hx)
    have h1 := hthirdKey c hc
    have h2 := hthirdKey (ψ c) (hψS c hc)
    have hx' : (Θ₀.Φ c).2 = x := by simp [c]
    rw [hψψ c hc, h1, hx'] at h2
    exact h2.symm
  obtain ⟨e₃, he₃, heq₃⟩ := exists_normalForm_flagPsi hK hdz polrep hM hthirdInv
  have hpairKey : ∀ c ∈ S, (Θ₀.Φ (ψ c)).1 =
      (flagAct Nx (flagSg hK ((Θ₀.Φ c).1).2),
        flagAct Ny (flagSg hK ((Θ₀.Φ c).1).1)) := by
    intro c hc
    have hx3 : (Θ₀.Φ c).2 ∈ refSet K 2 dz := (hS c).mp hc
    obtain ⟨Az, hAz, hAzEq⟩ := exists_blockSL_of_mem_refSet hdz hx3
    obtain ⟨Bx, _, hBx⟩ :=
      exists_blockSL_of_mem_refSet hd02 (pls2x_mem_refSet_02 (Θ₀.Φ c).1.1)
    obtain ⟨By, _, hBy⟩ :=
      exists_blockSL_of_mem_refSet hd02 (pls2x_mem_refSet_02 (Θ₀.Φ c).1.2)
    have hk₁ := pls2x_kapMat_false_one (f := f) (m := 1) By Py hPy
    have hk₂ := pls2x_kapMat_false_one (f := f) (m := 1) Bx Px hPx
    have hs₁ := pls2x_flagSg_toGL_std (f := f) hK By
    have hs₂ := pls2x_flagSg_toGL_std (f := f) hK Bx
    have hpsi := hψ Bx By Az hAz c hc (Prod.ext (Prod.ext hBx hBy) hAzEq)
    rw [hk₁, hk₂] at hpsi
    have hfst := congrArg Prod.fst hpsi
    rw [hfst, hBy, hBx, ← hs₁, ← hs₂]
  have hpairInv : ∀ x : FlagK K 2 × FlagK K 2,
      (flagAct Nx (flagSg hK (flagAct Ny (flagSg hK x.1))),
        flagAct Ny (flagSg hK (flagAct Nx (flagSg hK x.2)))) = x := by
    intro x
    let c : C := Θ₀.Φ.symm (x, stdFlag K 2)
    have hc : c ∈ S := (hS c).mpr (by
      simpa [c] using stdFlag_mem_refSet hdz)
    have h1 := hpairKey c hc
    have h2 := hpairKey (ψ c) (hψS c hc)
    have hx' : (Θ₀.Φ c).1 = x := by simp [c]
    rw [hψψ c hc, h1, hx'] at h2
    exact h2.symm
  obtain ⟨e₁, e₂, heq₁₂⟩ := exists_normalForm_psiA1A1 hK Nx Ny hpairInv
  let Θ₁₂ : ChamberIso ((flagSys K 1).prod (flagSys K 1))
      ((flagSys K 1).prod (flagSys K 1)) :=
    (flagMapIso (glLin e₁)).prodCongr (flagMapIso (glLin e₂))
  let Θ' : ChamberIso (((flagSys K 1).prod (flagSys K 1)).prod (flagSys K 1))
      (((flagSys K 1).prod (flagSys K 1)).prod (flagSys K 1)) :=
    Θ₁₂.prodCongr (flagMapIso (glLin e₃))
  let Θ : ChamberIso X (((flagSys K 1).prod (flagSys K 1)).prod (flagSys K 1)) :=
    Θ₀.trans Θ'
  have hΘ : ∀ c, Θ.Φ c =
      ((flagAct e₁ ((Θ₀.Φ c).1).1, flagAct e₂ ((Θ₀.Φ c).1).2),
        flagAct e₃ ((Θ₀.Φ c).2)) := fun c => rfl
  have himg₃ : flagMap (glLin e₃) '' refSet K 2 dz = refSet K 2 dz :=
    flagMap_image_refSet (glLin e₃) he₃
  have hiff₃ : ∀ x : FlagK K 2,
      flagAct e₃ x ∈ refSet K 2 dz ↔ x ∈ refSet K 2 dz := by
    intro x
    constructor
    · intro hx
      have hx' : flagMap (glLin e₃) x ∈
          flagMap (glLin e₃) '' refSet K 2 dz := by
        rw [himg₃]; exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzx' : z = x := flagMap_injective (glLin e₃) hzx
      rwa [hzx'] at hz
    · intro hx
      have hx' : flagMap (glLin e₃) x ∈
          flagMap (glLin e₃) '' refSet K 2 dz := Set.mem_image_of_mem _ hx
      rwa [himg₃] at hx'
  refine ⟨Θ, fun c => ?_, fun c hc => ?_⟩
  · rw [hS c, hΘ c, Set.mem_prod]
    simp only [Set.mem_univ, true_and]
    exact (hiff₃ (Θ₀.Φ c).2).symm
  · have hx3 : (Θ₀.Φ c).2 ∈ refSet K 2 dz := (hS c).mp hc
    have h1 : flagAct e₂⁻¹ (Θ.Φ c).1.2 = (Θ₀.Φ c).1.2 := by
      rw [hΘ c, flagAct_inv_flagAct]
    have h2 : flagAct e₁⁻¹ (Θ.Φ c).1.1 = (Θ₀.Φ c).1.1 := by
      rw [hΘ c, flagAct_inv_flagAct]
    have hpair := heq₁₂ (Θ.Φ c).1
    rw [h1, h2, hΘ c] at hpair
    have hfirst : (Θ.Φ (ψ c)).1 = psiA1A1 hK (Θ.Φ c).1 := by
      rw [hΘ (ψ c), hpairKey c hc, hΘ c]
      simpa [psiA1A1] using hpair
    have hthird : (Θ.Φ (ψ c)).2 =
        flagPsi' K f hK 2 dz plz (Θ.Φ c).2 := by
      rw [hΘ (ψ c), hthirdKey c hc, flagPsi', dif_pos hdz]
      have hmem3 : flagAct e₃ (Θ₀.Φ c).2 ∈ refSet K 2 dz :=
        flagMap_mem_refSet (glLin e₃) he₃ hx3
      have h3eq := heq₃ (flagAct e₃ (Θ₀.Φ c).2) hmem3
      rw [flagAct_inv_flagAct] at h3eq
      rw [h3eq]
      exact flagPsi_eq_of_pol_eq hK hdz polrep plz (fun b hb h2 => by
        simpa [polrep, List.getD_replicate, show b < dz.length - 1 from by omega]
          using (hplz b hb h2).symm) hmem3
    exact Prod.ext hfirst hthird

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
