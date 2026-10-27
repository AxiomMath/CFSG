module

public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.Quasithin.Background.JonesParshallSLn

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace SLCover

variable (d : ℕ) (F : Type) [Field F] [CharP F 2]

noncomputable local instance algZ2 : Algebra (ZMod 2) F := ZMod.algebra F 2

@[expose] noncomputable def natRepQ : Representation (ZMod 2) ↥(StatedSL d F) (Fin d → F) where
  toFun γ := (Matrix.mulVecLin ((γ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)).restrictScalars
    (ZMod 2)
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem natRepQ_apply (γ : ↥(StatedSL d F)) (x : Fin d → F) :
    natRepQ d F γ x = ((γ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ x := rfl

@[expose] noncomputable def psiFun (u : Fin d → F) : Module.Dual (ZMod 2) (Fin d → F) where
  toFun x := Algebra.trace (ZMod 2) F (u ⬝ᵥ x)
  map_add' x y := by rw [dotProduct_add, map_add]
  map_smul' c x := by
    rw [dotProduct_smul, map_smul]
    rfl

@[expose] noncomputable def psi : (Fin d → F) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin d → F) where
  toFun := psiFun d F
  map_add' u v := by
    ext x
    simp [psiFun, add_dotProduct]
  map_smul' c u := by
    ext x
    simp [psiFun, smul_dotProduct]

theorem psi_injective [Finite F] : Function.Injective (psi d F) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have hnd := traceForm_nondegenerate (ZMod 2) F
  funext i
  have h1 : ∀ c : F, Algebra.trace (ZMod 2) F (u i * c) = 0 := by
    intro c
    have := congrArg (fun l => l (Pi.single i c)) hu
    simpa [psi, psiFun, dotProduct_single] using this
  exact hnd.1 (u i) (fun c => by simpa [Algebra.traceForm_apply] using h1 c)


theorem psi_bijective [Finite F] : Function.Bijective (psi d F) := by
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  refine ⟨psi_injective d F, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin d → F)).symm).mp (psi_injective d F)

@[expose] noncomputable def psiEquiv [Finite F] : (Fin d → F) ≃+ Module.Dual (ZMod 2) (Fin d → F) :=
  (LinearEquiv.ofBijective (psi d F) (psi_bijective d F)).toAddEquiv

theorem psi_apply (u x : Fin d → F) : psi d F u x = Algebra.trace (ZMod 2) F (u ⬝ᵥ x) := rfl

theorem dual_psi (γ : ↥(StatedSL d F)) (u : Fin d → F) :
    Representation.dual (natRepQ d F) γ (psi d F u) =
      psi d F ((((γ⁻¹ : ↥(StatedSL d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *ᵥ u) := by
  refine LinearMap.ext fun x => ?_
  rw [Representation.dual_apply]
  show psi d F u (natRepQ d F γ⁻¹ x) = psi d F _ x
  rw [psi_apply, psi_apply, natRepQ_apply, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem binaryNaturalSL_dual [Finite F] :
    Explicit.BinaryNaturalSL (Representation.dual (natRepQ d F)) d F .dual := by
  show (FFModel.dualNat (StatedSL d F)).IsModel (Representation.dual (natRepQ d F))
  let D := FFModel.dualNat (StatedSL d F)
  let e := secEquivAmb D rfl rfl
  let βa : Module.Dual (ZMod 2) (Fin d → F) ≃+ Additive D.Amb :=
    (psiEquiv d F).symm.trans (additiveVec d F).symm
  have hamb : ∀ (γ : ↥(StatedSL d F)) (w : Module.Dual (ZMod 2) (Fin d → F)),
      βa (Representation.dual (natRepQ d F) γ w) =
        Additive.ofMul (D.act γ (Additive.toMul (βa w))) := by
    intro γ w
    obtain ⟨u, rfl⟩ := (psiEquiv d F).surjective w
    have h2 : Representation.dual (natRepQ d F) γ (psiEquiv d F u) =
        psiEquiv d F ((((γ⁻¹ : ↥(StatedSL d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)ᵀ *ᵥ u) :=
      dual_psi d F γ u
    show (additiveVec d F).symm ((psiEquiv d F).symm
        (Representation.dual (natRepQ d F) γ (psiEquiv d F u))) =
      Additive.ofMul (D.act γ (Additive.toMul ((additiveVec d F).symm
        ((psiEquiv d F).symm (psiEquiv d F u)))))
    rw [h2, (psiEquiv d F).symm_apply_apply, (psiEquiv d F).symm_apply_apply]
    rfl
  refine ⟨MulEquiv.refl _, βa.trans e.symm.toAdditive, ?_, ?_, ?_, ?_⟩
  · exact bot_le
  · intro g m _
    exact Subgroup.mem_top _
  · intro g m hm
    have hm1 : m = 1 := Subgroup.mem_bot.mp hm
    subst hm1
    refine Subgroup.mem_bot.mpr ?_
    show Multiplicative.ofAdd ((((g⁻¹ : ↥(StatedSL d F)) : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F)ᵀ *ᵥ Multiplicative.toAdd (1 : Multiplicative (Fin d → F))) =
        (1 : Multiplicative (Fin d → F))
    simp
  · intro γ w m hm hw
    have key : ∀ y : Additive D.Amb, e.toAdditive (e.symm.toAdditive y) = y := fun y => by
      show Additive.ofMul (e (e.symm (Additive.toMul y))) = y
      rw [e.apply_symm_apply]
      rfl
    have h1 : βa w = Additive.ofMul (m : D.Amb) := by
      have h := congrArg e.toAdditive hw
      rw [show (βa.trans e.symm.toAdditive) w = e.symm.toAdditive (βa w) from rfl, key] at h
      exact h
    have h2 : βa (Representation.dual (natRepQ d F) γ w) =
        Additive.ofMul (D.act γ (m : D.Amb)) := by
      rw [hamb, h1]
      rfl
    apply e.toAdditive.injective
    rw [show (βa.trans e.symm.toAdditive) (Representation.dual (natRepQ d F) γ w) =
      e.symm.toAdditive (βa (Representation.dual (natRepQ d F) γ w)) from rfl, key, h2]
    rfl

theorem fixV_eq_bot_of_dual_h1 [Finite F] {W : Type} [CommGroup W] [Finite W]
    (hexp : ∀ w : W, w ^ 2 = 1) (L : Subgroup (MulAut W)) (U : Subgroup W)
    (hinv : ∀ x ∈ L, ∀ v ∈ U, x v ∈ U) (hcomm : XMod.commOf ↥L U = U)
    (hH1 : Module.finrank (ZMod 2) (H1 (Representation.dual (natRepQ d F))) = 0)
    (hreal : (FFModel.nat (StatedSL d F)).Realizes L U (fixV L ⊓ U)) : fixV L ⊓ U = ⊥ := by
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSL d F)) hexp L U (fixV L ⊓ U)
    inf_le_right (fun z hz x hx => mem_fixV.1 hz.1 x hx) hinv hcomm π hπ.1 (natRepQ d F) β hβs hβk
    (fun γ v hv => hβe γ v hv)
  rw [hH1, pow_zero] at hcard
  exact Subgroup.card_eq_one.mp (le_antisymm hcard Nat.card_pos)

end SLCover

open SLCover in
theorem asI16Cover_of : AsI16Cover := by
  intro V _ _ hexp L hirr hcase
  have hinv : ∀ x ∈ L, ∀ v ∈ commV L, x v ∈ commV L := fun x hx v hv => hirr.2.1 ⟨x, hx⟩ v hv
  have hcomm : XMod.commOf ↥L (commV L) = commV L := hirr.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcase with ⟨n, hn, K, hK, hKfin, hcard, hreal⟩ | ⟨K, hK, hKfin, hcard, hreal⟩ |
    ⟨K, hK, hKfin, hcard, hreal⟩
  · let : Field K := hK
    have : Fintype K := Fintype.ofFinite K
    have hF : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hcard
    have : CharP K 2 := charP_of_card_eq_prime_pow hF
    refine fixV_eq_bot_of_dual_h1 3 K hexp L (commV L) hinv hcomm ?_ hreal
    rw [finrank_H1_SL3 hF (by omega) (binaryNaturalSL_dual 3 K)]
    simp [show n ≠ 1 by omega]
  · let : Field K := hK
    have : Fintype K := Fintype.ofFinite K
    have hF : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by simpa using hF)
    refine fixV_eq_bot_of_dual_h1 4 K hexp L (commV L) hinv hcomm ?_ hreal
    exact finrank_H1_SL45 (Or.inl rfl) hF (binaryNaturalSL_dual 4 K)
  · let : Field K := hK
    have : Fintype K := Fintype.ofFinite K
    have hF : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by simpa using hF)
    refine fixV_eq_bot_of_dual_h1 5 K hexp L (commV L) hinv hcomm ?_ hreal
    exact finrank_H1_SL45 (Or.inr rfl) hF (binaryNaturalSL_dual 5 K)

end CFSG.Quasithin
