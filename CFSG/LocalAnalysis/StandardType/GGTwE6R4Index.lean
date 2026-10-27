module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport

public section

namespace CFSG.StandardType.TwE6R4

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent


theorem three_pow_five_le_inf_conj {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) (hY6 : Nat.card Y = 3 ^ 6) :
    3 ^ 5 ≤ Nat.card ↥(Y ⊓ (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)).range) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  set Ψ : ↥(TwistedDiag.Rgrp Ω Fr) →* MulAut (TwE6Delta.RecipeR K n) :=
    (TwE6Transport.recipeConj σ ε).comp
      (NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm.toMonoidHom with hΨdef
  have hΨrange : Ψ.range = (TwE6Transport.recipeConj σ ε).range := by
    rw [hΨdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      Subgroup.map_top]
  have hΨinj : Function.Injective Ψ := by
    rw [hΨdef]
    exact (TwE6Transport.recipeConj_injective σ ε hn hK hσ).comp
      (MulEquiv.injective (NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm)
  have hYle : Y ≤ Ψ.range := by
    intro φ hφ
    rw [hΨrange, hε]
    exact hYI φ hφ
  set Y' : Subgroup ↥(TwistedDiag.Rgrp Ω Fr) := Y.comap Ψ with hY'def
  have hY'map : Y'.map Ψ = Y := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.2 le_rfl
    · intro y hy
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hYle hy)
      exact ⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact hy), hx⟩
  have hY'card : Nat.card Y' = 3 ^ 6 := by
    rw [← hY6, ← Subgroup.card_map_of_injective (K := Y') hΨinj, hY'map]
  set X : Subgroup (ModGL Tag.E6 Ω) := Y'.map (TwistedDiag.Rgrp Ω Fr).subtype with hXdef
  have hXle : X ≤ TwistedDiag.Rgrp Ω Fr :=
    Subgroup.map_subtype_le _
  have hXcard : Nat.card X = 3 ^ 6 := by
    rw [hXdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hY'card]
  have hdvd : (TwistedDiag.Cgrp K σ.toRingHom Ω).relIndex X ∣ 3 :=
    LieType.SeitzGeneration.twisted_E6_relIndex_dvd_three Nat.prime_two hn K hK σ.toRingHom
      (fun c => hσ c) Ω Fr hFr hXle
  have hrel : (TwistedDiag.Cgrp K σ.toRingHom Ω).relIndex X ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hdvd
  have hprod : Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) *
      (TwistedDiag.Cgrp K σ.toRingHom Ω).relIndex X = Nat.card X := by
    rw [mul_comm, inf_comm]
    exact Subgroup.relIndex_mul_card _ _
  have h35 : 3 ^ 5 ≤ Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) := by
    have h1 : 3 ^ 5 * 3 ≤
        Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) * 3 := by
      calc 3 ^ 5 * 3 = Nat.card X := by rw [hXcard]; norm_num
        _ = Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) *
              (TwistedDiag.Cgrp K σ.toRingHom Ω).relIndex X := hprod.symm
        _ ≤ Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) * 3 :=
              Nat.mul_le_mul_left _ hrel
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  set Z : Subgroup ↥(TwistedDiag.Rgrp Ω Fr) :=
    Y' ⊓ (TwistedDiag.Cgrp K σ.toRingHom Ω).comap (TwistedDiag.Rgrp Ω Fr).subtype with hZdef
  have hZmap : Z.map (TwistedDiag.Rgrp Ω Fr).subtype =
      X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    rw [hZdef, Subgroup.map_inf_eq _ _ _ (Subgroup.subtype_injective _), ← hXdef,
      Subgroup.map_comap_eq, Subgroup.range_subtype, ← inf_assoc, inf_eq_left.2 hXle]
  have hZcard : Nat.card Z =
      Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) := by
    rw [← Subgroup.card_map_of_injective (K := Z) (Subgroup.subtype_injective _), hZmap]
  have hconj : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε (MulAut.conj c) = MulAut.conj (ε c) := by
    intro c
    ext x
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hZle : Z.map Ψ ≤ Y ⊓ (MulAut.conj : TwE6Delta.RecipeR K n →*
      MulAut (TwE6Delta.RecipeR K n)).range := by
    apply le_inf
    · rw [← hY'map]
      exact Subgroup.map_mono inf_le_left
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨hzY', hzC⟩ := Subgroup.mem_inf.1 hz
      have hzC' : (z : ModGL Tag.E6 Ω) ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
        Subgroup.mem_comap.1 hzC
      obtain ⟨c, hc⟩ := TwE6DD2.rgrpConjAut_mem_range_conj hn hK σ hσ Fr hFr z.2 hzC'
      refine ⟨ε c, ?_⟩
      show MulAut.conj (ε c) = MulAut.congr ε
        ((NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr) z)
      rw [show (NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr) z = MulAut.conj c
          from hc.symm, hconj]
  haveI : Finite (MulAut (TwE6Delta.RecipeR K n)) := TwE6Delta.finite_mulAut_recipeR hK
  calc 3 ^ 5 ≤ Nat.card ↥(X ⊓ TwistedDiag.Cgrp K σ.toRingHom Ω) := h35
    _ = Nat.card Z := hZcard.symm
    _ = Nat.card (Z.map Ψ) := (Subgroup.card_map_of_injective (K := Z) hΨinj).symm
    _ ≤ Nat.card ↥(Y ⊓ (MulAut.conj : TwE6Delta.RecipeR K n →*
          MulAut (TwE6Delta.RecipeR K n)).range) := Subgroup.card_le_of_le hZle

end CFSG.StandardType.TwE6R4

