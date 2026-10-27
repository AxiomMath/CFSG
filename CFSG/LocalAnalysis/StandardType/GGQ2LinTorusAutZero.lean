module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutGens
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm
import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermMem

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open Matrix
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

section

variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)

private theorem one_sub_planeIdem_eq_fromBlocks (S : Finset (Fin t)) :
    (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) - planeIdem t ε S true =
      Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0
        (0 : Matrix (Fin ε.val) (Fin ε.val) K) := by
  ext x y
  rcases x with (i | i) | c <;> rcases y with (j | j) | d <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.diagonal, Matrix.one_apply]

private theorem tau_injective_lin (hζ : Function.Injective ζ) :
    Function.Injective (tau ζ t ε) := by
  intro u v h
  have h' : (SpBlocks.tau ζ t u : ↥(StatedSp t K)) = SpBlocks.tau ζ t v := by
    apply Subtype.ext
    apply planeExt_injective t ε
    rw [← tau_eq_planeExt, ← tau_eq_planeExt]
    exact h
  exact SpBlocks.tau_injective hζ t h'

private theorem tau_mul_planeIdem_of_vanishes {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i ∈ S, u i = 0) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        planeIdem t ε S true = planeIdem t ε S true := by
  rw [coe_tau_eq_fromBlocks_planeMat, planeIdem_true_eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  have hblock : WitSpNs.planeMat (fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) * SpBlocks.planeIdem t S = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · rw [if_pos hj, hu j hj, ofAdd_zero, map_one]
      simp
    · rw [if_neg hj, Matrix.mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hblock]

private theorem planeIdem_mul_tau_of_vanishes {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i ∈ S, u i = 0) :
    planeIdem t ε S true *
        ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      planeIdem t ε S true := by
  rw [coe_tau_eq_fromBlocks_planeMat, planeIdem_true_eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  have hblock : SpBlocks.planeIdem t S * WitSpNs.planeMat (fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · rw [if_pos hj, hu j hj, ofAdd_zero, map_one]
      simp
    · rw [if_neg hj, Matrix.zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hblock]

private theorem commute_tau_of_mem_levi_lin {S : Finset (Fin t)} {u : PlaneRaw.V t}
    (hu : ∀ i ∈ S, u i = 0) {g : GL (LinIdx t ε) K}
    (hg : g ∈ levi (planeIdem t ε S true)) :
    tau ζ t ε u * g = g * tau ζ t ε u := by
  apply Units.ext
  let A : Matrix (LinIdx t ε) (LinIdx t ε) K := (g : Matrix (LinIdx t ε) (LinIdx t ε) K)
  let T : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)
  let P : Matrix (LinIdx t ε) (LinIdx t ε) K := planeIdem t ε S true
  have hQ : A * (1 - P) = 1 - P := hg.1
  have hQA : (1 - P) * A = 1 - P := hg.2
  have hAP : A * P = P * A := by
    have h1 : A - A * P = 1 - P := by simpa [Matrix.mul_sub] using hQ
    have h2 : A - P * A = 1 - P := by simpa [Matrix.sub_mul] using hQA
    have e1 : A * P = A - (1 - P) := by rw [← h1]; abel
    have e2 : P * A = A - (1 - P) := by rw [← h2]; abel
    rw [e1, e2]
  have hTP : T * P = P := tau_mul_planeIdem_of_vanishes ζ t ε hu
  have hPT : P * T = P := planeIdem_mul_tau_of_vanishes ζ t ε hu
  have hQT : (1 - P) * T = T - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPT]
  have hTQ : T * (1 - P) = T - P := by
    rw [Matrix.mul_sub, Matrix.mul_one, hTP]
  have hA' : A = A * P + A * (1 - P) := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  have hA'' : A = P * A + (1 - P) := by
    rw [← hAP, ← hQ, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  have hAT : A * T = P * A + (T - P) := by
    calc A * T = (A * P + A * (1 - P)) * T := by conv_lhs => rw [hA']
      _ = A * P * T + A * (1 - P) * T := by rw [Matrix.add_mul]
      _ = P * A + (T - P) := by
          have h1 : A * P * T = P * A := by rw [Matrix.mul_assoc, hPT, hAP]
          have h2 : A * (1 - P) * T = T - P := by rw [hQ, hQT]
          rw [h1, h2]
  have hTA : T * A = P * A + (T - P) := by
    calc T * A = T * (P * A + (1 - P)) := by conv_lhs => rw [hA'']
      _ = T * (P * A) + T * (1 - P) := by rw [Matrix.mul_add]
      _ = P * A + (T - P) := by
          have h1 : T * (P * A) = P * A := by rw [← Matrix.mul_assoc, hTP]
          rw [h1, hTQ]
  exact (hAT.trans hTA.symm).symm

theorem planeExt_mem_levi_of {S : Finset (Fin t)} {x : GL (Fin t ⊕ Fin t) K}
    (h₁ : (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
        (1 - SpBlocks.planeIdem t S) = 1 - SpBlocks.planeIdem t S)
    (h₂ : (1 - SpBlocks.planeIdem t S) *
        (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = 1 - SpBlocks.planeIdem t S) :
    planeExt t ε x ∈ levi (planeIdem t ε S true) := by
  refine ⟨?_, ?_⟩
  · change planeExtMat t ε (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
        (1 - planeIdem t ε S true) = 1 - planeIdem t ε S true
    rw [one_sub_planeIdem_eq_fromBlocks]
    change Matrix.fromBlocks (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0
        (1 : Matrix (Fin ε.val) (Fin ε.val) K) *
        Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0
          (0 : Matrix (Fin ε.val) (Fin ε.val) K) =
        Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0
          (0 : Matrix (Fin ε.val) (Fin ε.val) K)
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj, h₁]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · change (1 - planeIdem t ε S true) *
        planeExtMat t ε (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) =
      1 - planeIdem t ε S true
    rw [one_sub_planeIdem_eq_fromBlocks]
    change Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0
        (0 : Matrix (Fin ε.val) (Fin ε.val) K) *
        Matrix.fromBlocks (x : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0
          (1 : Matrix (Fin ε.val) (Fin ε.val) K) =
        Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0
          (0 : Matrix (Fin ε.val) (Fin ε.val) K)
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj, h₂]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

private theorem planeExt_mem_levi_of_mem_spLevi {S : Finset (Fin t)} {x : ↥(StatedSp t K)}
    (hx : x ∈ SpBlocks.levi t S) :
    planeExt t ε ((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) ∈
      levi (planeIdem t ε S true) := by
  have h₁ : (((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * (1 - SpBlocks.planeIdem t S) =
      1 - SpBlocks.planeIdem t S := hx
  have hAP : (((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * SpBlocks.planeIdem t S =
      SpBlocks.planeIdem t S * (((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) :=
    SpBlocks.commute_planeIdem_of_mem_levi hx
  have h₂ : (1 - SpBlocks.planeIdem t S) *
      (((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) = 1 - SpBlocks.planeIdem t S := by
    have hmul := h₁
    rw [Matrix.mul_sub, Matrix.mul_one] at hmul
    rw [Matrix.sub_mul, Matrix.one_mul, ← hAP]
    exact hmul
  exact planeExt_mem_levi_of t ε h₁ h₂

private theorem swapEquiv_mem_torusAut_blockGroup [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {S : Finset (Fin t)} {i j : Fin t}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    PlaneRaw.swapEquiv t i j ∈ torusAut ζ t ε (blockGroup ζ t ε (.zero S)) := by
  refine mem_torusAut_of_mem_spTorusAut ζ t ε
    (X := Subgroup.zpowers (rho i j hij sl2W)) ?_
    (SpBlocks.swapEquiv_mem_torusAut (X := Subgroup.zpowers (rho i j hij sl2W))
      hK hζ hij (Subgroup.mem_zpowers _))
  intro x hx
  exact planeExt_mem_levi_of_mem_spLevi t ε
    ((Subgroup.zpowers_le.mpr (SpBlocks.rho_mem_levi hi hj hij sl2W)) hx)

private theorem negEquiv_mem_torusAut_blockGroup [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hζ : Function.Injective ζ) {S : Finset (Fin t)} {i : Fin t}
    (hi : i ∈ S) :
    PlaneRaw.negEquiv t i ∈ torusAut ζ t ε (blockGroup ζ t ε (.zero S)) := by
  refine mem_torusAut_of_mem_spTorusAut ζ t ε
    (X := Subgroup.zpowers (lam i sl2W)) ?_
    (SpBlocks.negEquiv_mem_torusAut (X := Subgroup.zpowers (lam i sl2W))
      hK hζ (Subgroup.mem_zpowers _))
  intro x hx
  exact planeExt_mem_levi_of_mem_spLevi t ε
    ((Subgroup.zpowers_le.mpr (SpBlocks.lam_mem_levi hi sl2W)) hx)

end

theorem torusAut_blockGroup_zero_eq (h : LinTorusAutSubsetSignedPerm) {K : Type} [Field K]
    [Finite K] [CharP K 2] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ}
    {ε : Fin 2} (hK : Nat.card K = 2) (hζ : Function.Injective ζ) (S : Finset (Fin t)) :
    torusAut ζ t ε (blockGroup ζ t ε (PlaneRaw.Code.zero S)) =
      ((PlaneRaw.signedPermGroupOn t S : Subgroup _) : Set _) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    have hsigned : φ ∈ PlaneRaw.signedPermGroup t :=
      h ζ t ε hK hζ (blockGroup ζ t ε (.zero S)) hφ
    obtain ⟨σ, ε', hε', hφform⟩ :=
      PlaneRaw.exists_signedPerm_of_mem_signedPermGroup hsigned
    obtain ⟨y, hy, hyφ⟩ := hφ
    have hfix : ∀ k ∉ S, φ (Pi.single k 1) = Pi.single k 1 := by
      intro k hk
      have hu : ∀ i ∈ S, (Pi.single k 1 : PlaneRaw.V t) i = 0 := by
        intro i hi
        have hik : i ≠ k := fun h => hk (h ▸ hi)
        simp [hik]
      have hcomm : y * tau ζ t ε (Pi.single k 1) * y⁻¹ = tau ζ t ε (Pi.single k 1) := by
        rw [← commute_tau_of_mem_levi_lin ζ t ε hu hy]
        group
      have htau : tau ζ t ε (φ (Pi.single k 1)) = tau ζ t ε (Pi.single k 1) := by
        rw [← hyφ (Pi.single k 1), hcomm]
      exact tau_injective_lin ζ t ε hζ htau
    have hkey : ∀ k ∉ S, σ k = k ∧ ε' k = 1 := by
      intro k hk
      have h := hφform (Pi.single k 1) k
      rw [hfix k hk, Pi.single_eq_same] at h
      by_cases hk' : σ.symm k = k
      · have hσk : σ k = k := by
          have h1 := congrArg σ hk'
          rw [Equiv.apply_symm_apply] at h1
          exact h1.symm
        rw [hk', Pi.single_eq_same] at h
        exact ⟨hσk, by simpa using h.symm⟩
      · have hne : k ≠ σ.symm k := fun h' => hk' h'.symm
        have h0 : (Pi.single k 1 : PlaneRaw.V t) (σ.symm k) = 0 := by
          simp [Ne.symm hne]
        rw [h0, mul_zero] at h
        exact absurd h one_ne_zero
    refine PlaneRaw.mem_signedPermGroupOn_of_apply S φ σ (fun i => ε' (σ i)) ?_ ?_ ?_ ?_
    · intro i
      exact hε' (σ i)
    · intro i hi
      exact (hkey i hi).1
    · intro i hi
      rw [show σ i = i from (hkey i hi).1]
      exact (hkey i hi).2
    · intro u i
      simpa using hφform u (σ i)
  · rw [PlaneRaw.signedPermGroupOn]
    refine closure_subset_torusAut ζ t ε (X := blockGroup ζ t ε (.zero S)) ?_
    intro ψ hψ
    rcases hψ with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · by_cases hab : a = b
      · subst b
        have hswap : PlaneRaw.swapEquiv t a a = 1 := by
          ext u k
          simp [PlaneRaw.swapEquiv]
        rw [hswap]
        exact one_mem_torusAut ζ t ε (blockGroup ζ t ε (.zero S))
      · exact swapEquiv_mem_torusAut_blockGroup ζ t ε hK hζ ha hb hab
    · exact negEquiv_mem_torusAut_blockGroup ζ t ε hK hζ ha

end CFSG.StandardType.GGQ2Frame.LinBlocks
