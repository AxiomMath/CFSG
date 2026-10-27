module

public import CFSG.Quasithin.Vol2.Ch3B513NSelfDual
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.Background.JonesParshallSp4H1

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Rep

variable (K : Type) [Field K] [CharP K 2]

noncomputable local instance algZ2S : Algebra (ZMod 2) K := ZMod.algebra K 2

theorem statedSp_eq_sp4 : StatedSp 2 K = Explicit.sp4 K := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    rw [Matrix.neg_apply]
    exact CharTwo.neg_eq _
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      Explicit.spJ K := by
    rw [hneg]
    rfl
  unfold StatedSp
  rw [hJ]
  exact Subgroup.closure_eq (Explicit.sp4 K)

@[expose] noncomputable def natRepSp :
    Representation (ZMod 2) ↥(StatedSp 2 K) (Fin 2 ⊕ Fin 2 → K) where
  toFun γ := (Matrix.mulVecLin ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).restrictScalars (ZMod 2)
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem natRepSp_apply (γ : ↥(StatedSp 2 K)) (x : Fin 2 ⊕ Fin 2 → K) :
    natRepSp K γ x = ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x := rfl

@[expose] noncomputable def bilLin : (Ix → K) →ₗ[K] (Ix → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y => x ⬝ᵥ (Explicit.spJ K *ᵥ y)) (fun x x' y => add_dotProduct x x' _)
    (fun c x y => smul_dotProduct c x _) (fun x y y' => by rw [mulVec_add, dotProduct_add])
    (fun c x y => by rw [mulVec_smul, dotProduct_smul, smul_eq_mul])

omit [CharP K 2] in
theorem bilLin_apply (x y : Ix → K) : bilLin K x y = bil x y := (bil_eq x y).symm

omit [CharP K 2] in
theorem bilLin_nondeg (u : Ix → K) (hu : ∀ x, bilLin K u x = 0) : u = 0 := by
  funext i
  have h := hu (Explicit.spJ K *ᵥ Pi.single i 1)
  simp only [bilLin, LinearMap.mk₂_apply, mulVec_mulVec, spJ_mul_spJ, one_mulVec] at h
  rw [dotProduct_single, mul_one] at h
  exact h

theorem finrank_H1_dual_natRepSp [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (H1 (Representation.dual (natRepSp K))) = n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : Finite ↥(StatedSp 2 K) := Subtype.finite
  have : Finite (Module.Dual (ZMod 2) (Ix → K)) := by
    have : Module.Finite (ZMod 2) (Ix → K) := Module.Finite.of_finite
    exact Module.finite_of_finite (ZMod 2)
  have hinv : ∀ (γ : ↥(StatedSp 2 K)) (u x : Ix → K),
      bilLin K (natRepSp K γ u) (natRepSp K γ x) = bilLin K u x := by
    intro γ u x
    rw [bilLin_apply, bilLin_apply, natRepSp_apply, natRepSp_apply]
    have hγ : (γ : Matrix.GeneralLinearGroup Ix K) ∈ Explicit.sp4 K := by
      rw [← statedSp_eq_sp4 K]
      exact γ.2
    exact bil_smul hγ u x
  apply finrank_H1_of_card
  rw [card_H1_dual_of_selfDual K (natRepSp K) (bilLin K) (bilLin_nondeg K) hinv
    (MulEquiv.subgroupCongr (statedSp_eq_sp4 K)) muSp (fun γ x => rfl)
    (card_Z1A_muSp hF (by omega)), hF]

end Rep

variable {W : Type} [CommGroup W] [Finite W]

theorem card_fixV_le_of_sp4 (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (U : Subgroup W)
    (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U) {n : ℕ} (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes L U (fixV L ⊓ U)) :
    Nat.card ↥(fixV L ⊓ U) ≤ 2 ^ n := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Finite ↥(StatedSp 2 K) := Subtype.finite
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSp 2 K)) hexp L U (fixV L ⊓ U)
    inf_le_right (fun z hz x hx => mem_fixV.1 hz.1 x hx) hinv hcomm π hπ.1 (natRepSp K) β
    hβs hβk (fun γ v hv => hβe γ v hv)
  rwa [finrank_H1_dual_natRepSp K hK hn] at hcard

end CFSG.Quasithin.B513N
