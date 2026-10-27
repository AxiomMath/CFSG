module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
import CFSG.Quasithin.Background.Harris.G2.U33End
import CFSG.Quasithin.Background.F918E1
import CFSG.Quasithin.Background.G116IIModule
import CFSG.Adapters.LieModelSimple
public import CFSG.Quasithin.Background.JonesParshallCurtisGroupInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.G11
open CFSG.Quasithin.JonesParshall.Curtis
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem gapEndU33_holds :
    GapEndU33 := by
  intro Q _ _ hQ2 L hLie hirrOn hcard
  have hirr : ∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤ :=
    fun B hB => hirrOn.2.2.2 B hB bot_le le_top
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
  have hcardV : Nat.card (Additive Q) = 2 ^ 6 :=
    (Nat.card_congr (Additive.ofMul : Q ≃ Additive Q)).symm.trans hcard
  have hdim : Module.finrank (ZMod 2) (Additive Q) = 6 := by
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
  let Φ := mulAutLin Q
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
      rw [hto, mulAutLin_apply]
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
  have hLie' : CFSG.Blueprint.LieModel ↥L' .PSU 3 3 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv emap hLie
  have hsimp : IsSimpleGroup ↥L' :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie'
  have hmodel : StatedClassicalModel ↥L' .PSU 3 3 1 :=
    hLie'.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  have hEnd : EndIsField L' 1 := CFSG.Quasithin.G11.Harris.G2.endIsField_u33 hsimp hmodel hIrr' hdim
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
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  intro γ hγ
  have hmem : Φ γ ∈ Subgroup.centralizer (L' : Set (Additive Q ≃ₗ[ZMod 2] Additive Q)) := by
    rw [Subgroup.mem_centralizer_iff] at hγ ⊢
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
    change Φ l * Φ γ = Φ γ * Φ l
    rw [← map_mul, hγ l hl, map_mul]
  have h1 : Φ γ = 1 := by
    have h2 := hmem
    rw [hc] at h2
    simpa using h2
  exact Φ.injective (by rw [h1, map_one])

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
