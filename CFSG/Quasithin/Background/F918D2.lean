module

public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.JonesParshallSLn

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace L3Dual

@[expose] def dotDual {n : ℕ} (u : Fin n → ZMod 2) : Module.Dual (ZMod 2) (Fin n → ZMod 2) where
  toFun x := u ⬝ᵥ x
  map_add' x y := dotProduct_add u x y
  map_smul' c x := by simp [dotProduct_smul]

@[expose] def dualVec {n : ℕ} (l : Module.Dual (ZMod 2) (Fin n → ZMod 2)) : Fin n → ZMod 2 :=
  fun i => l (Pi.single i 1)

theorem dotDual_dualVec {n : ℕ} (l : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    dotDual (dualVec l) = l := by
  apply LinearMap.ext
  intro x
  show dualVec l ⬝ᵥ x = l x
  conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ l x]
  have hs : ∀ i : Fin n, (fun j : Fin n => if i = j then (1 : ZMod 2) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [hs, dotProduct, dualVec, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dualVec_dotDual {n : ℕ} (u : Fin n → ZMod 2) : dualVec (dotDual u) = u := by
  funext i
  simp [dualVec, dotDual, dotProduct_single]

@[expose] def dualEquiv (n : ℕ) : Module.Dual (ZMod 2) (Fin n → ZMod 2) ≃+ (Fin n → ZMod 2) where
  toFun := dualVec
  invFun := dotDual
  left_inv := dotDual_dualVec
  right_inv := dualVec_dotDual
  map_add' _ _ := rfl

@[expose] noncomputable def repNat (n : ℕ) :
    Representation (ZMod 2) (SpecialLinearGroup (Fin n) (ZMod 2)) (Fin n → ZMod 2) where
  toFun γ := AddMonoidHom.toZModLinearMap 2 (muF2 n γ)
  map_one' := LinearMap.ext fun x => by
    show muF2 n 1 x = x
    rw [map_one]
    rfl
  map_mul' γ δ := LinearMap.ext fun x => by
    show muF2 n (γ * δ) x = muF2 n γ (muF2 n δ x)
    rw [map_mul]
    rfl

private theorem repNat_apply (n : ℕ) (γ : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    repNat n γ x = (γ : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := rfl

private theorem dualEquiv_equivariant (n : ℕ) (γ : SpecialLinearGroup (Fin n) (ZMod 2))
    (l : Module.Dual (ZMod 2) (Fin n → ZMod 2)) :
    dualEquiv n ((Representation.dual (repNat n)) γ l) =
      muF2 n (invTransposeSL n (ZMod 2) γ) (dualEquiv n l) := by
  funext i
  show l (repNat n γ⁻¹ (Pi.single i 1)) = _
  rw [repNat_apply]
  have hcol : (γ⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)).1 *ᵥ (Pi.single i 1 : Fin n → ZMod 2) =
      fun j => (γ⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)).1 j i := by
    funext j
    simp
  rw [hcol]
  have h1 := LinearMap.pi_apply_eq_sum_univ l (fun j => (γ⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)).1 j i)
  have hs : ∀ j : Fin n, (fun k : Fin n => if j = k then (1 : ZMod 2) else 0) = Pi.single j 1 := by
    intro j
    funext k
    simp [Pi.single_apply, eq_comm]
  simp only [hs, smul_eq_mul] at h1
  rw [h1]
  show _ = ((((invTransposeSL n (ZMod 2) γ : SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ dualVec l) i
  rw [invTransposeSL_coe]
  simp [mulVec, dotProduct, dualVec]

theorem finrank_H1_dual_repNat_three :
    Module.finrank (ZMod 2) (H1 (Representation.dual (repNat 3))) = 1 := by
  have : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
    Finite.of_equiv _ (dualEquiv 3).symm.toEquiv
  have hcard := card_H1_eq_of_card (Representation.dual (repNat 3))
    (θ := invTransposeSL 3 (ZMod 2)) (β := dualEquiv 3) (μ := muF2 3)
    (fun γ l => dualEquiv_equivariant 3 γ l) (k := 2) card_Z1A_three
  exact finrank_H1_of_card _ (by rw [hcard]; norm_num)

end L3Dual

open L3Dual in
theorem card_fixV_le_two_of_natural3 {W : Type} [CommGroup W]
    [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (V : Subgroup W)
    (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V) (hcomm : XMod.commOf ↥L V = V)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1) : Nat.card ↥(V ⊓ fixV L) ≤ 2 := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have hβe : ∀ (γ : L3.Γ) (v : ↥V) (hv : (D.π γ : MulAut W) (v : W) ∈ V),
      D.β ⟨(D.π γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (repNat 3 γ (Multiplicative.toAdd (D.β v))) := by
    intro γ v hv
    rw [D.equi γ v hv]
    rfl
  have hcard := card_le_pow_finrank_H1_dual (Γ := L3.Γ) hexp L V (V ⊓ fixV L) D.Z_le
    (fun z hz x hx => hz.2 x hx) hinv hcomm D.π D.π_surj (repNat 3) D.β D.β_surj D.ker_β hβe
  rw [finrank_H1_dual_repNat_three] at hcard
  simpa using hcard

end CFSG.Quasithin
