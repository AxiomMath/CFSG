module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactL3Alg
import CFSG.CGT.T75N.L29Overgroup
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

private theorem r920kl3e_irreducible_map_conj {K : Type} [Field K]
    {W : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    (hirr : ∀ Z : Submodule K (Fin 3 → K),
      (∀ s ∈ W, ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∀ X : Submodule K (Fin 3 → K),
      (∀ s ∈ W.map (MulAut.conj g).toMonoidHom, ∀ v ∈ X,
        (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ X) → X = ⊥ ∨ X = ⊤ := by
  intro X hX
  let eφ : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) := SpecialLinearGroup.toLin' g
  let φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := eφ.toLinearMap
  have hφ_surj : Function.Surjective φ := eφ.surjective
  have hZ : ∀ s ∈ W, ∀ v ∈ X.comap φ,
      (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ X.comap φ := by
    intro s hs v hv
    have hL : φ ((s : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (SpecialLinearGroup.toLin' (g * s)) v := by
      change (SpecialLinearGroup.toLin' g) ((SpecialLinearGroup.toLin' s) v) = _
      rw [map_mul]
      rfl
    have hcomp : (MulAut.conj g) s * g = g * s := by
      rw [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one]
    have hcomp' : SpecialLinearGroup.toLin' ((MulAut.conj g) s) *
        SpecialLinearGroup.toLin' g = SpecialLinearGroup.toLin' (g * s) := by
      rw [← map_mul, hcomp]
    have hR : ((MulAut.conj g) s : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v =
        (SpecialLinearGroup.toLin' (g * s)) v := by
      change (SpecialLinearGroup.toLin' ((MulAut.conj g) s))
          ((SpecialLinearGroup.toLin' g) v) = _
      rw [← hcomp']
      rfl
    have key : φ ((s : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ((MulAut.conj g) s : Matrix (Fin 3) (Fin 3) K) *ᵥ φ v := hL.trans hR.symm
    have hv' : φ v ∈ X := Submodule.mem_comap.mp hv
    rw [Submodule.mem_comap, key]
    exact hX _ (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hs) _ hv'
  rcases hirr (X.comap φ) hZ with h | h
  · left
    rw [← Submodule.map_comap_eq_of_surjective hφ_surj X, h, Submodule.map_bot]
  · right
    rw [← Submodule.map_comap_eq_of_surjective hφ_surj X, h, Submodule.map_top]
    exact LinearMap.range_eq_top_of_surjective φ hφ_surj

theorem kFactL28_L3_even {Q : Type} [Group Q] [Finite Q] {f : ℕ} (hpf : 2 ^ f % 3 = 2)
    (hQ : LieModel Q .PSL 3 2 f) {X W T : Subgroup Q} (c : KCfgL28 X W T) : W = ⊤ := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hQ.statedClassicalModel (by decide)
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hpf
  let e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    (eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (pslEquivSL3 hqK)
  let W' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := W.map e.toMonoidHom
  have hcard504 : Nat.card (Bar2 X) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hdvd : Nat.card (Bar2 X) ∣ Nat.card ↥X :=
    Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)
  have h7X : 7 ∣ Nat.card ↥X := dvd_trans (by rw [hcard504]; norm_num) hdvd
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 7 h7X
  let A : Subgroup Q := (Subgroup.zpowers x).map X.subtype
  have hAX : A ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA7 : Nat.card A = 7 := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]
  let B' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := A.map e.toMonoidHom
  have hN' : ∀ P' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), IsPGroup 7 ↥P' →
      B' ≤ P' → normalizer (P' : Set (Matrix.SpecialLinearGroup (Fin 3) K)) ≤ W' := by
    intro P' hP' hB'P'
    let P : Subgroup Q := P'.map e.symm.toMonoidHom
    have hPe : P.map e.toMonoidHom = P' := by
      have hP : P = P'.comap e.toMonoidHom := by
        dsimp [P]
        rw [Subgroup.map_equiv_eq_comap_symm]
        rfl
      rw [hP, Subgroup.map_comap_eq_self_of_surjective e.surjective P']
    have hP : IsPGroup 7 ↥P := by
      dsimp [P]
      exact hP'.of_equiv (Subgroup.equivMapOfInjective P' e.symm.toMonoidHom e.symm.injective)
    have hAP : A ≤ P := by
      intro a ha
      refine Subgroup.mem_map.mpr ⟨e a, hB'P' (Subgroup.mem_map_of_mem e.toMonoidHom ha), ?_⟩
      exact e.symm_apply_apply a
    have hNP : normalizer P ≤ W := c.N7 A hAX hA7 P hP hAP
    have hNPe : (normalizer P).map e.toMonoidHom = normalizer P' := by
      rw [Subgroup.map_equiv_normalizer_eq P e, hPe]
    rw [← hNPe]
    exact Subgroup.map_mono hNP
  have hB'W' : B' ≤ W' := by
    dsimp [B', W']
    exact Subgroup.map_mono (hAX.trans c.X_le)
  have hB7' : Nat.card B' = 7 := by
    dsimp [B']
    rw [Subgroup.card_map_of_injective e.injective, hA7]
  have hirr : ∀ Z : Submodule K (Fin 3 → K),
      (∀ s ∈ W', ∀ v ∈ Z, (s : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ Z) → Z = ⊥ ∨ Z = ⊤ := by
    by_cases h7 : 7 ∣ Nat.card K - 1
    · exact sl3_irreducible_of_seven_dvd hK h7 hB'W' hB7' hN'
    · intro Z hZ
      exact sl3_irreducible_of_not_seven_dvd hK h7 hB7' Z
        (fun s hs v hv => hZ s (hB'W' hs) v hv)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTindex : ¬ 2 ∣ T.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp c.T_sylow).2.2
    rwa [Subgroup.relIndex_top_right] at h
  have hWodd : ¬ 2 ∣ W'.index := by
    dsimp [W']
    rw [Subgroup.index_map_equiv W e]
    exact fun h => hTindex (dvd_trans h (Subgroup.index_dvd_of_le c.T_le))
  haveI : Fintype K := Fintype.ofFinite K
  haveI hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  obtain ⟨g, hg⟩ := CFSG.CGT.T75N.exists_conj_unitriangular_le_gen W' hWodd
  let S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := W'.map (MulAut.conj g).toMonoidHom
  have hU : unitriangular 3 K ≤ S := by
    intro u hu
    exact Subgroup.mem_map_equiv.mpr (show (MulAut.conj g).symm u ∈ W' from hg u hu)
  have hirrS := r920kl3e_irreducible_map_conj (W := W') hirr g
  have hStop : S = ⊤ := CFSG.CGT.T75N.eq_top_of_unitriangular_le_gen S hU hirrS
  have hW'top : W' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g) y ∈ S := by rw [hStop]; exact Subgroup.mem_top _
    change (MulAut.conj g) y ∈ W'.map (MulAut.conj g).toMonoidHom at hy
    have hy' : (MulAut.conj g).symm ((MulAut.conj g) y) ∈ W' := Subgroup.mem_map_equiv.mp hy
    simpa only [MulEquiv.symm_apply_apply] using hy'
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ W' := by
    rw [hW'top]
    exact Subgroup.mem_top _
  change e x ∈ W.map e.toMonoidHom at hx
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hx
  rw [e.injective hwe] at hw
  exact hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
