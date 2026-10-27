module

public import CFSG.Quasithin.Background.RonanH46Oz
public import CFSG.Quasithin.Background.RonanH46ZLev

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem hermBlkZ_twisted (X : HMod 1 K) :
    (hermBlkZ X)ᵀ = (hermBlkZ X).map (barR 1 K) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, hermBlkZ, barR_apply]
  exact (herm_apply X j.succ i.succ).symm

private theorem hermBlkZ_mul (X Y : HMod 1 K) : hermBlkZ (X * Y) = hermBlkZ X + hermBlkZ Y := by
  ext i j
  simp [hermBlkZ, mat_mul]

private theorem hermBlkZ_one : hermBlkZ (1 : HMod 1 K) = 0 := by
  ext i j
  simp [hermBlkZ, mat_one]

private noncomputable def zBlkHom :
    ↥(⊤ : Subgroup (HMod 1 K)) →* Multiplicative (twistedForm (barR 1 K)) where
  toFun u := Multiplicative.ofAdd ⟨hermBlkZ (u : HMod 1 K), hermBlkZ_twisted (u : HMod 1 K)⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hermBlkZ_one
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hermBlkZ_mul (u : HMod 1 K) (v : HMod 1 K)

private theorem zBlkHom_surjective : Function.Surjective (zBlkHom (K := K)) := by
  intro Bm
  obtain ⟨⟨M2, hM2⟩, rfl⟩ : ∃ B : twistedForm (barR 1 K), Multiplicative.ofAdd B = Bm :=
    ⟨Multiplicative.toAdd Bm, rfl⟩
  have h1 : M2ᵀ = M2.map (barR 1 K) := hM2
  have hbar : ∀ a b : Fin 2, bar 1 (M2 a b) = M2 b a := by
    intro a b
    have h := congrFun (congrFun h1 a) b
    simp only [Matrix.transpose_apply, Matrix.map_apply, barR_apply] at h
    exact h.symm
  have hMH : (conjM 1 !![0, 0, 0; 0, M2 0 0, M2 0 1; 0, M2 1 0, M2 1 1])ᵀ =
      !![0, 0, 0; 0, M2 0 0, M2 0 1; 0, M2 1 0, M2 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, hbar]
  refine ⟨⟨mkH _ hMH, Subgroup.mem_top _⟩, ?_⟩
  have hblk : hermBlkZ (mkH _ hMH) = M2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermBlkZ, mat_mkH]
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact hblk

private theorem zBlkHom_eq_one_iff (u : ↥(⊤ : Subgroup (HMod 1 K))) :
    zBlkHom (K := K) u = 1 ↔ (u : HMod 1 K) ∈ V2z 1 K := by
  rw [mem_V2z_iff_hermBlkZ]
  constructor
  · intro h
    exact congrArg (fun z => (Multiplicative.toAdd z : twistedForm (barR 1 K)).1) h
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact h

private noncomputable def zCoordHom (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K}
    (hω : barR 1 K ω ≠ ω) : ↥(⊤ : Subgroup (HMod 1 K)) →* Multiplicative (Fin 4 → Fq 1 K) :=
  (AddEquiv.toMultiplicative (theta hK hω).symm.toAddEquiv).toMonoidHom.comp
    (zBlkHom (K := K))

private theorem zCoordHom_apply (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K} (hω : barR 1 K ω ≠ ω)
    (u : ↥(⊤ : Subgroup (HMod 1 K))) :
    zCoordHom hK hω u =
      Multiplicative.ofAdd ((theta hK hω).symm (Multiplicative.toAdd (zBlkHom (K := K) u))) :=
  rfl

private theorem zCoordHom_surjective (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K}
    (hω : barR 1 K ω ≠ ω) : Function.Surjective (zCoordHom hK hω) := by
  intro y
  obtain ⟨u, hu⟩ := zBlkHom_surjective (K := K)
    (Multiplicative.ofAdd ((theta hK hω) (Multiplicative.toAdd y)))
  refine ⟨u, ?_⟩
  rw [zCoordHom_apply, hu, toAdd_ofAdd, LinearEquiv.symm_apply_apply, ofAdd_toAdd]

private theorem zCoordHom_eq_one_iff (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K}
    (hω : barR 1 K ω ≠ ω) (u : ↥(⊤ : Subgroup (HMod 1 K))) :
    zCoordHom hK hω u = 1 ↔ (u : HMod 1 K) ∈ V2z 1 K := by
  rw [← zBlkHom_eq_one_iff, zCoordHom_apply, ofAdd_eq_one, LinearEquiv.map_eq_zero_iff,
    toAdd_eq_zero]

private theorem zCoordHom_rel (hK : Nat.card K = (2 ^ 1) ^ 2) {ω : K} (hω : barR 1 K ω ≠ ω)
    {g : MulAut (HMod 1 K)} {A : SL(2, K)}
    (hgA : ∀ X : HMod 1 K, hermBlkZ (g X) = (A : Matrix (Fin 2) (Fin 2) K) * hermBlkZ X *
      ((A : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ)
    {φ : MulAut (Multiplicative (Fin 4 → Fq 1 K))}
    (hφ : ∀ x : Fin 4 → Fq 1 K, (theta hK hω).symm (twistRep (barR_inv hK) A (theta hK hω x)) =
      Multiplicative.toAdd (φ (Multiplicative.ofAdd x)))
    (u u' : ↥(⊤ : Subgroup (HMod 1 K))) (huu : (u' : HMod 1 K) = g u) :
    zCoordHom hK hω u' = φ (zCoordHom hK hω u) := by
  rw [zCoordHom_apply, zCoordHom_apply]
  generalize hx : (theta hK hω).symm (Multiplicative.toAdd (zBlkHom (K := K) u)) = x
  have hθx : theta hK hω x = Multiplicative.toAdd (zBlkHom (K := K) u) := by
    rw [← hx, LinearEquiv.apply_symm_apply]
  have h1 : Multiplicative.toAdd (zBlkHom (K := K) u') =
      twistRep (barR_inv hK) A (theta hK hω x) := by
    rw [hθx]
    apply Subtype.ext
    rw [twistRep_apply]
    show hermBlkZ (u' : HMod 1 K) = _
    rw [huu, hgA (u : HMod 1 K)]
    rfl
  rw [h1, hφ x, ofAdd_toAdd]

private theorem part4Orth_fq (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∃ a : Fq 1 K, a ≠ 0 ∧ InducesOnR (LZ hK) ⊤ (V2z 1 K) (Multiplicative (Fin 4 → Fq 1 K))
      (CFSG.Quasithin.H11Proof.omegaFour (Fq 1 K)
        (CFSG.Quasithin.H11Proof.orthMinus (Fq 1 K) a)) := by
  obtain ⟨ω, hω1⟩ := exists_trace_one (le_refl 1) hK
  have hω : barR 1 K ω ≠ ω := barR_ne_of_trace hK hω1
  have hb : CFSG.Quasithin.G11.Harris.L2.coordB (barR_inv hK) ω = 1 := Subtype.ext hω1
  obtain ⟨hA, hB⟩ := herm_omega (le_refl 1) hK hω hb
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  refine ⟨CFSG.Quasithin.G11.Harris.L2.coordC (barR_inv hK) ω, ?_, ?_⟩
  · have h0 := CFSG.Quasithin.G11.Harris.L2.coordB_nonsplit (hinv := barR_inv hK)
      CharTwo.two_eq_zero hω 0
    simpa using h0
  refine ⟨le_top, fun g _ u _ => Subgroup.mem_top _, fun g hg z hz => LZ_mem_V2z hK hg hz,
    zCoordHom hK hω, zCoordHom_surjective hK hω, zCoordHom_eq_one_iff hK hω, ?_, ?_⟩
  · intro g hg
    obtain ⟨A, hgA⟩ := LZ_hermBlkZ hK hg
    obtain ⟨φ, hφ, hφx⟩ := hA A
    exact ⟨φ, hφ, fun u u' huu => zCoordHom_rel hK hω hgA hφx u u' huu⟩
  · intro φ hφ
    obtain ⟨A, hAφ⟩ := hB φ hφ
    obtain ⟨y, hy, hyA⟩ := exists_LZ_hermBlkZ hK h4 A
    exact ⟨y, hy, fun u u' huu => zCoordHom_rel hK hω hyA hAφ u u' huu⟩

theorem part4Orth (hK : Nat.card K = (2 ^ 1) ^ 2) :
    InducesOnR (LZ hK) ⊤ (V2z 1 K) (Multiplicative (Fin 4 → ZMod 2))
      (CFSG.Quasithin.H11Proof.omegaFour (ZMod 2)
        (CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) 1)) := by
  obtain ⟨a, ha0, h⟩ := part4Orth_fq hK
  obtain ⟨ψ⟩ := exists_ringEquiv_zmod2 (F := Fq 1 K) (by rw [card_Fq (le_refl 1) hK, pow_one])
  have hψ0 : ψ a ≠ 0 := fun h0 => ha0 (ψ.injective (by rw [h0, map_zero]))
  have ha : ψ a = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ hψ0
  have hQ : ∀ x : Fin 4 → Fq 1 K,
      CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) (ψ a) (fun i => ψ (x i)) =
        ψ (CFSG.Quasithin.H11Proof.orthMinus (Fq 1 K) a x) := by
    intro x
    simp only [CFSG.Quasithin.H11Proof.orthMinus, map_add, map_mul, map_pow]
  have h' := inducesOn_map_equiv
    (AddEquiv.toMultiplicative (AddEquiv.piCongrRight (fun _ : Fin 4 => ψ.toAddEquiv))) h
  have key := map_omegaFour_ringEquiv ψ (CFSG.Quasithin.H11Proof.orthMinus (Fq 1 K) a)
    (CFSG.Quasithin.H11Proof.orthMinus (ZMod 2) (ψ a)) hQ
  rw [ha] at key
  rw [← key]
  exact h'

end CFSG.Quasithin.RonanH46
