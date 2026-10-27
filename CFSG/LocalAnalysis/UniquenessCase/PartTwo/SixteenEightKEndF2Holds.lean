module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
public import CFSG.LinearAlgebra.SLFiveRankTenCentralizer
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case1M22Rep
import CFSG.Quasithin.Background.G116IIModule
import CFSG.LargeExtraspecial.D73IdentPSL
public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.G11
open CFSG.Quasithin.JonesParshall.Curtis
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.LocalAnalysis.UniquenessCase.UC22

private noncomputable def s16kEndF2_autLin {X : Type*} [CommGroup X] (hX : ∀ x : X, x ^ 2 = 1)
    [Module (ZMod 2) (Additive X)] :
    MulAut X ≃* (Additive X ≃ₗ[ZMod 2] Additive X) where
  toFun g :=
    let e : Additive X ≃+ Additive X :=
      { toFun := fun x => Additive.ofMul (g (Additive.toMul x))
        invFun := fun x => Additive.ofMul (g.symm (Additive.toMul x))
        left_inv := fun x => by
          simp only [toMul_ofMul, MulEquiv.symm_apply_apply, ofMul_toMul]
        right_inv := fun x => by
          simp only [toMul_ofMul, MulEquiv.apply_symm_apply, ofMul_toMul]
        map_add' := fun x y => by
          rw [toMul_add, map_mul, ofMul_mul] }
    e.toLinearEquiv (fun c x => ZMod.map_smul e.toAddMonoidHom c x)
  invFun f :=
    { toFun := fun x => Additive.toMul (f (Additive.ofMul x))
      invFun := fun x => Additive.toMul (f.symm (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul, LinearEquiv.symm_apply_apply, toMul_ofMul]
      right_inv := fun x => by
        simp only [ofMul_toMul, LinearEquiv.apply_symm_apply, toMul_ofMul]
      map_mul' := fun x y => by
        rw [ofMul_mul, map_add, toMul_add] }
  left_inv g := MulEquiv.ext fun x => rfl
  right_inv f := LinearEquiv.ext fun x => rfl
  map_mul' g h := LinearEquiv.ext fun x => rfl

private theorem s16kEndF2_autLin_apply {X : Type*} [CommGroup X] (hX : ∀ x : X, x ^ 2 = 1)
    [Module (ZMod 2) (Additive X)] (g : MulAut X) (x : Additive X) :
    s16kEndF2_autLin hX g x = Additive.ofMul (g (Additive.toMul x)) := rfl

private theorem s16kEndF2_centralizer_eq_bot_of_map
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : Type} [CommGroup Q]
    (Φ : MulAut Q ≃* (V ≃ₗ[ZMod 2] V)) (L : Subgroup (MulAut Q))
    (h : Subgroup.centralizer (L.map Φ.toMonoidHom : Set (V ≃ₗ[ZMod 2] V)) = ⊥) :
    Subgroup.centralizer (L : Set (MulAut Q)) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  intro γ hγ
  have hmem : Φ γ ∈ Subgroup.centralizer
      (L.map Φ.toMonoidHom : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [Subgroup.mem_centralizer_iff] at hγ ⊢
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    change Φ l * Φ γ = Φ γ * Φ l
    rw [← map_mul, hγ l hl, map_mul]
  have h1 : Φ γ = 1 := by
    have h2 := hmem
    rw [h] at h2
    simpa using h2
  exact Φ.injective (by rw [h1, map_one])

theorem s16kEndF2Rank10_holds :
    S16kEndF2Rank10 := by
  intro Q _ _ hQ2 hcard L hirr hLie
  haveI : Module (ZMod 2) (Additive Q) :=
    AddCommGroup.zmodModule (G := Additive Q) (fun x => by
      have hx := hQ2 (Additive.toMul x)
      rw [two_nsmul]
      apply Additive.toMul.injective
      rw [toMul_add, ← pow_two]
      exact hx)
  haveI : Nontrivial Q := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  haveI : Nontrivial (Additive Q) := inferInstance
  have hcardV : Nat.card (Additive Q) = 2 ^ 10 :=
    (Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)).symm.trans hcard
  have hdim : Module.finrank (ZMod 2) (Additive Q) = 10 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [Nat.card_zmod, hcardV] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1).symm
  let e : Q ≃* Multiplicative (Additive Q) :=
    { toFun := fun q => Multiplicative.ofAdd (Additive.ofMul q)
      invFun := fun m => Additive.toMul (Multiplicative.toAdd m)
      left_inv := fun q => by simp
      right_inv := fun m => by simp
      map_mul' := fun x y => by
        rw [ofMul_mul, ofAdd_add] }
  let Φ := s16kEndF2_autLin (X := Q) hQ2
  let L' : Subgroup (Additive Q ≃ₗ[ZMod 2] Additive Q) := L.map Φ.toMonoidHom
  have hIrr' : IsIrr L' ⊤ := by
    refine ⟨fun _ _ _ _ => Submodule.mem_top, bot_lt_top, ?_⟩
    intro U hU _ _
    have hU' : XMod.IsInv ↥L' (subToSubgroup U) := invariant_iff_isInv.mp hU
    let B : Subgroup Q := (subToSubgroup U).map e.symm.toMonoidHom
    have hstab : ∀ l ∈ L, ∀ b ∈ B, l b ∈ B := by
      intro l hl b hb
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hb
      rw [Subgroup.mem_map]
      have hk : Φ l ∈ L' := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      have hmem : (Φ l) • u ∈ subToSubgroup U := hU' ⟨Φ l, hk⟩ u hu
      refine ⟨(Φ l) • u, hmem, ?_⟩
      show e.symm ((Φ l) • u) = l (e.symm u)
      rw [linMulAct_smul]
      have hto : Multiplicative.toAdd u = Additive.ofMul (e.symm u) := by
        rw [← MulEquiv.apply_symm_apply e u]
        rfl
      rw [hto, s16kEndF2_autLin_apply]
      exact e.symm_apply_apply (l (e.symm u))
    rcases hirr B hstab with h | h
    · left
      have hsub : subToSubgroup U = ⊥ :=
        Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective (by simpa [B] using h)
      exact subToSubgroup.injective (by simpa [OrderIso.map_bot] using hsub)
    · right
      have hsub : subToSubgroup U = ⊤ :=
        Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective (by simpa [B] using h)
      exact subToSubgroup.injective (by simpa [OrderIso.map_top] using hsub)
  have emap : ↥L ≃* ↥L' := Subgroup.equivMapOfInjective L Φ.toMonoidHom Φ.injective
  rcases hLie with hL5 | hM22
  · have hL5' : CFSG.Blueprint.LieModel ↥L .PSL 5 2 1 := hL5
    have hSC := hL5'.statedClassicalModel_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hSC
    have hK2 : Nat.card K = 2 := by simpa using hK
    obtain ⟨eK2⟩ :=
      CFSG.LargeExtraspecial.DW.D73.nonempty_mulEquiv_SL_of_card_two hK2 5
    have eLie : ↥L ≃* G5 := eK.trans eK2
    have e' : ↥L' ≃* G5 := emap.symm.trans eLie
    have hc := CFSG.LinearAlgebra.SLFiveRankTen.centralizer_eq_bot_of_finrank_ten e' hIrr' hdim
    exact s16kEndF2_centralizer_eq_bot_of_map Φ L hc
  · have hM22' : Nonempty (↥L ≃* CFSG.Quasithin.B45Mat.M22.G22) := hM22
    obtain ⟨θ⟩ := hM22'
    have θ' : ↥L' ≃* CFSG.Quasithin.B45Mat.M22.G22 := emap.symm.trans θ
    have hd : Module.finrank (ZMod 2) (Additive Q) ≤ 33 := by omega
    have hEnd : EndIsField L' 1 := (m22_repData θ' hIrr' hd).2.1
    have hc : Subgroup.centralizer (L' : Set (Additive Q ≃ₗ[ZMod 2] Additive Q)) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 ?_
      intro γ hγ
      have hmem : (γ : Additive Q →ₗ[ZMod 2] Additive Q) ∈ endCommutant L' := by
        rw [endCommutant, Subalgebra.mem_centralizer_iff]
        intro g hg
        obtain ⟨h, hh, rfl⟩ := hg
        ext v
        have hcomm := (Subgroup.mem_centralizer_iff.mp hγ) h hh
        have h1 := congrArg (fun g' : Additive Q ≃ₗ[ZMod 2] Additive Q => g' v) hcomm
        simpa [LinearEquiv.mul_apply] using h1
      let T : ↥(endCommutant L') := ⟨(γ : Additive Q →ₗ[ZMod 2] Additive Q), hmem⟩
      have hTne : T ≠ 0 := by
        intro h0
        have h0' : (γ : Additive Q →ₗ[ZMod 2] Additive Q) = 0 :=
          congrArg (fun T : ↥(endCommutant L') => (T : Additive Q →ₗ[ZMod 2] Additive Q)) h0
        obtain ⟨v, hv⟩ := exists_ne (0 : Additive Q)
        have h1 : (γ : Additive Q →ₗ[ZMod 2] Additive Q) (γ.symm v) = 0 := by
          rw [h0']; simp
        have h2 : (γ : Additive Q →ₗ[ZMod 2] Additive Q) (γ.symm v) = v := by
          simpa using γ.apply_symm_apply v
        exact hv (h2.symm.trans h1)
      rcases eq_zero_or_eq_one_of_endIsField_one hEnd T with h0 | h1
      · exact absurd h0 hTne
      · apply LinearEquiv.ext
        intro v
        have h1' : (γ : Additive Q →ₗ[ZMod 2] Additive Q) = 1 := by
          simpa [T] using congrArg (fun T : ↥(endCommutant L') =>
            (T : Additive Q →ₗ[ZMod 2] Additive Q)) h1
        have h2 := congrArg (fun f : Additive Q →ₗ[ZMod 2] Additive Q => f v) h1'
        simpa using h2
    exact s16kEndF2_centralizer_eq_bot_of_map Φ L hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
