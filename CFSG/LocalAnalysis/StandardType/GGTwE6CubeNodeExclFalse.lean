module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeCoords

public section

namespace CFSG.StandardType.TwE6Cube

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType
  CFSG.StandardType.TwE6EndNode3


theorem cube_killer_false {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) {v : Fin Tag.E6.rank → ZMod 3}
    (hd : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    (hfix : ∀ y ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g,
      (∀ j ∈ LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)), y j = j) ↔
        y ∈ Subgroup.zpowers (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩))
    {u : Fin Tag.E6.rank → ZMod 3} (hu0 : u ≠ 0) (huv : u ≠ v) (hun : u ≠ -v)
    (hcomm : ∀ c ∈ LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)),
      (g⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
          (c : ModGL TwistTag.E6.tag K) * g) * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * (g⁻¹ * baseChangeGL (τ := Tag.E6)
          (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g)) :
    False := by
  have hζo : orderOf ζ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hζ hζ1
  obtain ⟨Ψ, hΨinj, -, hΨ⟩ := exists_cubeHom hn hK σ hσ Fr hFr h3 hg hgn hζ hζo
  obtain ⟨_, hΨv⟩ := hΨ (Multiplicative.ofAdd v)
  obtain ⟨hxu, hΨu⟩ := hΨ (Multiplicative.ofAdd u)
  have hX : rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩ = Ψ (Multiplicative.ofAdd v) := hΨv.symm
  have hxu' : g * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr := hxu
  have hΨu' : Ψ (Multiplicative.ofAdd u) = rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hxu'⟩ := hΨu
  have hb : ∀ i, zetaVec ζ hζ u i ^ 3 = 1 := fun i => by
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hy : Ψ (Multiplicative.ofAdd u) ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g :=
    (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).2 ⟨zetaVec ζ hζ u, hb, hxu', hΨu'.symm⟩
  obtain ⟨w, -, hwb, hwΦ⟩ := exists_matrix_of_cube hn hK σ hσ Fr hFr hxu'
  have hwb' : baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (w : ModGL TwistTag.E6.tag K) = g * rootDiagUnit Tag.E6 (zetaVec ζ hζ u) * g⁻¹ := hwb
  have hconj : ∀ {G H : Type} [Group G] [Group H] (φ : G →* H) (w j : G) (g d : H),
      φ w = g * d * g⁻¹ → (g⁻¹ * φ j * g) * d = d * (g⁻¹ * φ j * g) → φ (w * j * w⁻¹) = φ j := by
    intro _ _ _ _ φ w j g d hw hc
    rw [map_mul, map_mul, map_inv, hw]
    have h1 : d * (g⁻¹ * φ j * g) * d⁻¹ = g⁻¹ * φ j * g := mul_inv_eq_iff_eq_mul.2 hc.symm
    calc g * d * g⁻¹ * φ j * (g * d * g⁻¹)⁻¹ = g * (d * (g⁻¹ * φ j * g) * d⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * φ j * g) * g⁻¹ := by rw [h1]
      _ = φ j := by group
  have hyfix : ∀ j ∈ LargeEvenLayer (ggFix (rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hd⟩)),
      Ψ (Multiplicative.ofAdd u) j = j := fun j hj => by
    rw [hΨu', hwΦ]
    exact Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (hconj _ _ _ _ _ hwb' (hcomm j hj)))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((hfix _ hy).1 hyfix)
  rw [hX, ← map_zpow] at hk
  have hku : k • v = u := Multiplicative.ofAdd.injective (by rw [ofAdd_zsmul]; exact hΨinj hk)
  have hcases : ∀ m : ZMod 3, m = 0 ∨ m = 1 ∨ m = -1 := by decide
  rcases hcases (k : ZMod 3) with h | h | h
  · exact hu0 (by rw [← hku, ← Int.cast_smul_eq_zsmul (ZMod 3), h, zero_smul])
  · exact huv (by rw [← hku, ← Int.cast_smul_eq_zsmul (ZMod 3), h, one_smul])
  · exact hun (by rw [← hku, ← Int.cast_smul_eq_zsmul (ZMod 3), h, neg_one_smul])

end CFSG.StandardType.TwE6Cube

end
