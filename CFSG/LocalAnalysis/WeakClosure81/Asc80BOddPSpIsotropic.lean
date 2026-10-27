module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

import CFSG.LieType.SeitzGeneration.SymplecticOpposition
import CFSG.LieType.SeitzGeneration.LinearOuterLocal
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpAniso
import CFSG.LieType.SeitzGeneration.RootPairSpConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.GroupTheory CFSG.LieType.SeitzGeneration
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm)
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull

private lemma isPGroup_spRad_ringChar {r : ℕ} {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) {W : Submodule F (Fin r ⊕ Fin r → F)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) :
    IsPGroup (ringChar F) (spRad W hW) := by
  classical
  let ℓ := ringChar F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have hfact : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP F ℓ := ringChar.charP F
  have hℓ2 : ℓ ≠ 2 := hF
  rw [IsPGroup.iff_orderOf]
  intro g
  have hgℓ : ((g : spRad W hW) : StatedSp r F) ^ ℓ = 1 := by
    obtain ⟨hg1, hg2, hg3⟩ := g.2
    set N : Module.End F (Fin r ⊕ Fin r → F) := spEnd (g : StatedSp r F) - 1 with hNdef
    have hNx : ∀ x, N x = spEnd (g : StatedSp r F) x - x := fun x => by simp [hNdef]
    have hN3 : N * N * N = 0 := by
      refine LinearMap.ext fun x => ?_
      have h1 : N x ∈ spPerp W := by rw [hNx]; exact hg1 x
      have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2 _ h1
      have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
      simpa using h3
    have hg1' : spEnd (g : StatedSp r F) = 1 + N := by rw [hNdef]; abel
    have hchoose : (ℓ.choose 2 : F) = (ℓ : F) * (((ℓ - 1) / 2 : ℕ) : F) := by
      rw [Nat.choose_two_right, Nat.mul_div_assoc _ (even_iff_two_dvd.1 (hℓ.even_sub_one hℓ2))]
      push_cast
      rfl
    have hℓ0 : (ℓ : F) = 0 := CharP.cast_eq_zero F ℓ
    have hchoose0 : (ℓ.choose 2 : F) = 0 := by rw [hchoose, hℓ0, zero_mul]
    have hpow : spEnd (((g : spRad W hW) : StatedSp r F) ^ ℓ) = 1 := by
      rw [CFSG.LieType.SeitzGeneration.spEnd_pow, hg1',
        one_add_pow_of_cube_eq_zero (K := F) hN3 ℓ, hℓ0, hchoose0]
      simp
    apply spLin_injective
    rw [map_one]
    exact Units.ext hpow
  have hpow : (g : spRad W hW) ^ ℓ = 1 := Subtype.ext hgℓ
  have hdvd : orderOf g ∣ ℓ := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime hℓ).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private lemma map_conjSp_spRad_le {r : ℕ} {F : Type} [Field F] [NeZero r]
    {W : Submodule F (Fin r ⊕ Fin r → F)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) (A : gsp r F)
    (hAW : ∀ w ∈ W,
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W)
    (hAinvW : ∀ w ∈ W,
      (((A⁻¹ : gsp r F) : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W) :
    (spRad W hW).map (conjSp r F A) ≤ spRad W hW := by
  classical
  set a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with ha
  set B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F :=
    (((A⁻¹ : gsp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) with hB
  have hAB : a * B = 1 := by
    rw [ha, hB, Subgroup.coe_inv]
    simp
  have hfix : ∀ y, a *ᵥ (B *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  have hμ : (multiplier r F A : F) ≠ 0 := Units.ne_zero _
  have hAperp : ∀ y ∈ spPerp W, a *ᵥ y ∈ spPerp W := by
    intro y hy w hw
    have hcoef : spForm r F w (a *ᵥ y) =
        (multiplier r F A : F) * spForm r F (B *ᵥ w) y := by
      conv_lhs => rw [← hfix w]
      simpa [ha] using RootPair.spForm_gsp A (B *ᵥ w) y
    rw [hcoef, hy _ (by simpa [hB] using hAinvW w hw), mul_zero]
  have hAinvperp : ∀ y ∈ spPerp W, B *ᵥ y ∈ spPerp W := by
    intro y hy w hw
    have hcoef : spForm r F (a *ᵥ w) y =
        (multiplier r F A : F) * spForm r F w (B *ᵥ y) := by
      conv_lhs => rw [← hfix y]
      simpa [ha] using RootPair.spForm_gsp A w (B *ᵥ y)
    have h0 : spForm r F (a *ᵥ w) y = 0 := hy _ (by simpa [ha] using hAW w hw)
    rw [hcoef] at h0
    exact (mul_eq_zero.mp h0).resolve_left hμ
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hsp : ∀ x, spEnd (conjSp r F A g) x = a *ᵥ (spEnd g (B *ᵥ x)) := by
    intro x
    rw [spEnd_apply, coe_conjSp, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, spEnd_apply g]
    rfl
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · change spEnd (conjSp r F A g) x - x ∈ spPerp W
    rw [hsp x]
    have hx0 : a *ᵥ (spEnd g (B *ᵥ x)) - x =
        a *ᵥ (spEnd g (B *ᵥ x) - B *ᵥ x) := by rw [Matrix.mulVec_sub, hfix x]
    rw [hx0]
    exact hAperp _ (hg1 _)
  · change spEnd (conjSp r F A g) x - x ∈ W
    rw [hsp x]
    have hx0 : a *ᵥ (spEnd g (B *ᵥ x)) - x =
        a *ᵥ (spEnd g (B *ᵥ x) - B *ᵥ x) := by rw [Matrix.mulVec_sub, hfix x]
    rw [hx0]
    exact hAW _ (by simpa [ha] using hg2 _ (hAinvperp x hx))
  · change spEnd (conjSp r F A g) x = x
    rw [hsp x, hg3 _ (by simpa [hB] using hAinvW x hx), hfix x]

theorem planeGen_of_isotropic_sp {F : Type} [Field F] [Finite F] {r : ℕ}
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hlin : E ≤ spLinearAutGroup r F)
    (W : Submodule F (Fin r ⊕ Fin r → F)) (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0)
    (hst : ∀ A : gsp r F, conjAut r F A ∈ E →
      ∀ w ∈ W, ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W) :
    PlaneGen E := by
  classical
  let ℓ := ringChar F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have hfact : Fact ℓ.Prime := ⟨hℓ⟩
  have hchar : CharP F ℓ := ringChar.charP F
  have hℓ2 : ℓ ≠ 2 := hF
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    subst hr0
    apply hW0
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    rcases i with i | i <;> exact i.elim0
  have hne : NeZero r := ⟨by omega⟩
  obtain ⟨w, hwW, hwne⟩ : ∃ w ∈ W, w ≠ 0 := by
    by_contra h
    push Not at h
    apply hW0
    rw [Submodule.eq_bot_iff]
    exact fun x hx => h x hx
  let T : StatedSp r F := spTransvection w 1
  have hT : T ∈ spRad W hW := spTransvection_mem_spRad hwW 1
  have h2F : (2 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F) (p := ringChar F) Nat.prime_two hF
  have hprojT : proj r F T ≠ 1 := by
    intro hproj
    have hker : T ∈ (proj r F).ker := MonoidHom.mem_ker.mpr hproj
    rw [ker_proj] at hker
    rcases SpSeitz.spEnd_eq_of_mem_spScalars hr hker with hsp | hsp
    · obtain ⟨x, hx⟩ : ∃ x, spForm r F x w ≠ 0 := by
        by_contra h
        push Not at h
        exact hwne (spForm_nondegenerate.2 w h)
      have hfixx : spEnd T x = x := by rw [hsp]; simp
      rw [spEnd_spTransvection, one_mul] at hfixx
      have hzw : (spForm r F x w) • w = 0 := by simpa using hfixx
      exact hx ((smul_eq_zero.mp hzw).resolve_right hwne)
    · have hfixw : spEnd T w = w := by
        rw [spEnd_spTransvection, spForm_isAlt.self_eq_zero, mul_zero, zero_smul, add_zero]
      have hneg : spEnd T w = -w := by rw [hsp]; simp
      have hw : w = -w := hfixw.symm.trans hneg
      have htwo : (2 : F) • w = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr hw
      exact hwne ((smul_eq_zero.mp htwo).resolve_left h2F)
  let R : Subgroup (StatedProj (StatedSp r F)) := (spRad W hW).map (proj r F)
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hmem : proj r F T ∈ R := Subgroup.mem_map_of_mem _ hT
    rw [hbot] at hmem
    exact hprojT (Subgroup.mem_bot.mp hmem)
  have hRr : IsPGroup ℓ R := (isPGroup_spRad_ringChar hF hW).map (proj r F)
  have hER : ∀ e ∈ E, R.map e.toMonoidHom = R := by
    intro e he
    have hrange : spLinearAutGroup r F = (conjAut r F).range := by
      rw [spLinearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    have he_range : e ∈ (conjAut r F).range := by
      rw [← hrange]
      exact hlin he
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp he_range
    have hAW : ∀ w ∈ W,
        ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W :=
      fun w hw => hst A he w hw
    have hAinvW : ∀ w ∈ W,
        (((A⁻¹ : gsp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
      intro w hw
      exact hst A⁻¹ (by rw [map_inv]; exact E.inv_mem he) w hw
    have hle : (spRad W hW).map (conjSp r F A).toMonoidHom ≤ spRad W hW :=
      map_conjSp_spRad_le hW A hAW hAinvW
    have hle' : (spRad W hW).map (conjSp r F A⁻¹).toMonoidHom ≤ spRad W hW :=
      map_conjSp_spRad_le hW A⁻¹ hAinvW (by simpa using hAW)
    have hconj : (spRad W hW).map (conjSp r F A).toMonoidHom = spRad W hW := by
      refine le_antisymm hle ?_
      intro g hg
      have h1 : conjSp r F A (conjSp r F A⁻¹ g) = g := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ (hle' (Subgroup.mem_map_of_mem _ hg))
    have hRdef : R = (spRad W hW).map (proj r F) := rfl
    rw [hRdef, Subgroup.map_map,
      show (conjAut r F A).toMonoidHom.comp (proj r F) =
        (proj r F).comp (conjSp r F A).toMonoidHom from rfl,
      ← Subgroup.map_map, hconj, ← hRdef]
  have hgood : ∀ Q : Subgroup (StatedProj (StatedSp r F)), Q ≠ ⊥ →
      IsRadicalPGroup ℓ ⊤ Q → HasGoodOppositePRadicals ℓ ⊤ Q := by
    intro Q hQne hQ
    have htop : (proj r F).range = ⊤ := MonoidHom.range_eq_top.mpr proj_surjective
    rw [← htop] at hQ ⊢
    exact hasGoodOppositePRadicals_of_statedSp (proj r F)
      (by rw [ker_proj]; exact spScalars_le_center) hQne hQ
  exact planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals hℓ2 hgood E hE h4 R hRne hRr
    hER

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
