module

public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneWeyl
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.StandardType.SpCoord
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix Multiplicative
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot

theorem sympMinus_lam_eq_longBlock {K : Type} [Field K] {m : ℕ} (i : Fin m)
    (g : SpecialLinearGroup (Fin 2) K) :
    lam i g = longBlock K m i g := by
  apply statedSp_ext
  rfl

theorem sympMinus_lam_sl2W_conj_spPlaneTorus {K : Type} [Field K] [CharP K 2] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) :
    lam i (sl2W : SpecialLinearGroup (Fin 2) K) * spPlaneTorus m ζ f *
        (lam i (sl2W : SpecialLinearGroup (Fin 2) K))⁻¹ =
      spPlaneTorus m ζ (sgnAut i f) := by
  let A : (Fin m → Multiplicative (ZMod p)) →* StatedSp m K :=
    (MulAut.conj (lam i (sl2W : SpecialLinearGroup (Fin 2) K))).toMonoidHom.comp
      (spPlaneTorus m ζ)
  let B : (Fin m → Multiplicative (ZMod p)) →* StatedSp m K :=
    (spPlaneTorus m ζ).comp (sgnAut i).toMonoidHom
  have haux : ∀ (j : Fin m) (a : Multiplicative (ZMod p)), A (Pi.mulSingle j a) =
      B (Pi.mulSingle j a) := by
    intro j a
    simp only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [spPlaneTorus_mulSingle]
    by_cases hji : j = i
    · subst hji
      rw [sgnAut_mulSingle_self, ← Pi.mulSingle_inv, spPlaneTorus_mulSingle]
      have h1 : ((lam j (sl2W : SpecialLinearGroup (Fin 2) K)) * lam j (ζ a) *
          (lam j (sl2W : SpecialLinearGroup (Fin 2) K))⁻¹) =
          lam j (sl2W * ζ a * sl2W⁻¹) := by
        rw [← map_mul, ← map_inv, ← map_mul]
      rw [h1, hζ a]
    · rw [sgnAut_mulSingle_of_ne hji, spPlaneTorus_mulSingle]
      have hcomm := commute_lam_lam (k := K) (Ne.symm hji)
        (sl2W : SpecialLinearGroup (Fin 2) K) (ζ a)
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hAB : A = B := MonoidHom.pi_ext haux
  have h := congrArg (fun φ => φ f) hAB
  simpa only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem sympMinus_permSp_conj_spPlaneTorus {K : Type} [Field K] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (π : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) :
    permSp K π * spPlaneTorus m ζ f * (permSp K π)⁻¹ =
      spPlaneTorus m ζ (permAut π f) := by
  let A : (Fin m → Multiplicative (ZMod p)) →* StatedSp m K :=
    (MulAut.conj (permSp K π)).toMonoidHom.comp (spPlaneTorus m ζ)
  let B : (Fin m → Multiplicative (ZMod p)) →* StatedSp m K :=
    (spPlaneTorus m ζ).comp (permAut π).toMonoidHom
  have haux : ∀ (j : Fin m) (a : Multiplicative (ZMod p)), A (Pi.mulSingle j a) =
      B (Pi.mulSingle j a) := by
    intro j a
    simp only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [spPlaneTorus_mulSingle, permAut_mulSingle, spPlaneTorus_mulSingle,
      sympMinus_lam_eq_longBlock j (ζ a), sympMinus_lam_eq_longBlock (π j) (ζ a),
      conj_permSp_longBlock]
  have hAB : A = B := MonoidHom.pi_ext haux
  have h := congrArg (fun φ => φ f) hAB
  simpa only [A, B, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem sympMinus_signedAut_le_sectionFrameAut {K : Type} [Field K] [CharP K 2] {p m : ℕ}
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) :
    TypeBDatum.signedAut m p ≤ FrameBs.sectionFrameAut (spPlaneTorus m ζ) ⊤ := by
  rw [TypeBDatum.signedAut]
  refine TypeBDatum.signedSupportedAut_le Finset.univ (fun i _ => ?_)
    (fun a _ b _ _ => ?_)
  · exact ⟨lam i (sl2W : SpecialLinearGroup (Fin 2) K), Subgroup.mem_top _,
      sympMinus_lam_sl2W_conj_spPlaneTorus ζ hζ i⟩
  · exact ⟨permSp K (Equiv.swap a b), Subgroup.mem_top _,
      sympMinus_permSp_conj_spPlaneTorus ζ (Equiv.swap a b)⟩

theorem sympMinus_sectionFrameAut_le_signedAut {K : Type} [Field K] [CharP K 2] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) K)
    (hζ : Function.Injective ζ) :
    FrameBs.sectionFrameAut (spPlaneTorus m ζ) ⊤ ≤ TypeBDatum.signedAut m p := by
  intro τ hτ
  obtain ⟨n, -, hn⟩ := hτ
  obtain ⟨π, ε, hε, hπ⟩ :=
    exists_signedPerm_of_normalizes (F := K) hp hp2 hζ n (fun f => ⟨τ f, hn f⟩)
  exact TypeBDatum.mem_signedAut_of_isSignedPerm
    (σ := τ) ⟨π, ε, hε, fun f i => hπ f (τ f) (hn f) i⟩

end CFSG.StandardType.SympMinus

end
