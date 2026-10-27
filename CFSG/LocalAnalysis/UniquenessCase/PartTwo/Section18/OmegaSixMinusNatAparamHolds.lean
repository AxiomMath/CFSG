module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusOrbit
public import CFSG.Quasithin.Background.E3Restrict
public import CFSG.HardMathSupport.U4FF.BOSemi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.E3
open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.HardMathSupport.U4FF
open scoped Matrix

theorem le_two_mul_of_mem_aSet_natNorm_omegaMinus {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {Y A : Subgroup (MulAut (StdMod (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))}
    (hY : Y ≤ natNorm (StatedOmega (StatedQuadMinus 3 F b c))) {k : ℕ}
    (hA : A ∈ E3.aSet k Y) : k ≤ 2 * n := by
  classical
  have h2F : 1 < Nat.card F := Finite.one_lt_card
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, pow_zero] at hF
      omega
    · exact hnpos
  by_cases hk : k ≤ 2
  · omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have hA1 : A ≠ ⊥ := hA.2.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hsc : HasScalarCommutant (StatedOmega (StatedQuadMinus 3 F b c)) :=
    fun f hf => omega_commutant hirr f hf
  have hsemi : ∀ a ∈ A, ∃ σ : F ≃+* F, IsSemilinear a σ := fun a ha =>
    exists_semilinear hsc (hY (hA.1 ha))
  have hlin : ∀ a ∈ A, IsSemilinear a (RingEquiv.refl F) :=
    forall_linear_of_mem_aSet (κ := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) hn hF hk2 hA hsemi
  have hiso : ∀ a ∈ A, ∀ v, StatedQuadMinus 3 F b c (toAddMap a v) =
      StatedQuadMinus 3 F b c v := by
    intro a ha v
    obtain ⟨M, hM⟩ := exists_matAut_of_mem_linSub (mem_linSub.mpr (hlin a ha))
    have hM2gl : M * M = 1 := by
      have h := hAel.2 a ha
      refine matHom_injective ?_
      rw [map_mul, map_one, matHom_apply, ← hM]
      simpa [pow_two] using h
    have hM2 : ((M : GL OIdx F) : Matrix OIdx OIdx F) *
        ((M : GL OIdx F) : Matrix OIdx OIdx F) = 1 := by
      rw [← Units.val_mul, hM2gl, Units.val_one]
    have hMnorm : matAut M ∈ natNorm (StatedOmega (StatedQuadMinus 3 F b c)) := by
      rw [← hM]
      exact hY (hA.1 ha)
    have hN : ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
        ∃ g₁ ∈ StatedOmega (StatedQuadMinus 3 F b c),
          ∀ x, ((M : Matrix OIdx OIdx F) *ᵥ
              (((g : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x)) =
            ((g₁ : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ
              ((M : Matrix OIdx OIdx F) *ᵥ x) := by
      intro g hg
      have hmem : matAut M * matAut g * (matAut M)⁻¹ ∈
          natImage (StatedOmega (StatedQuadMinus 3 F b c)) :=
        (Subgroup.mem_normalizer_iff.mp hMnorm (matAut g)).mp ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp hmem
      refine ⟨g'.1, g'.2, ?_⟩
      intro x
      have h2 := congrArg (fun t : MulAut (StdMod OIdx F) =>
        toAddMap t ((M : Matrix OIdx OIdx F) *ᵥ x)) hg'
      have hinv : toAddMap ((matAut M)⁻¹) ((M : Matrix OIdx OIdx F) *ᵥ x) = x := by
        rw [← toAddMap_matAut M x]
        exact toAddMap_apply_inv (matAut M) x
      simpa [toAddMap_mul, toAddMap_natAut, toAddMap_matAut, hinv] using h2.symm
    have hisoM := omega_isometry_of_normalizes hirr M hM2 hN
    simpa [hM, toAddMap_matAut] using hisoM v
  obtain ⟨w, hw, U, hUcard, hU⟩ :=
    exists_small_orbit_omegaMinus hirr hAel hA1 hlin hiso
  have hle : k ≤ E3.mQuot A (stabAt A w) := le_mQuot_stabAt_of_mem_aSet hA hw
  have hpow : 2 ^ E3.mQuot A (stabAt A w) ≤ Nat.card U :=
    two_pow_mQuot_stabAt_le hAel hU
  have hcard : Nat.card U ≤ 2 ^ (2 * n) := by
    calc Nat.card U ≤ Nat.card F ^ 2 := hUcard
      _ = 2 ^ (2 * n) := by rw [hF, ← pow_mul]; congr 1; omega
  have hbound : 2 ^ k ≤ 2 ^ (2 * n) := by
    calc 2 ^ k ≤ 2 ^ E3.mQuot A (stabAt A w) :=
          Nat.pow_le_pow_right (by norm_num) hle
      _ ≤ Nat.card U := hpow
      _ ≤ 2 ^ (2 * n) := hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbound

theorem le_two_mul_of_mem_aSet_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hN : NatOmegaMinus H ⊤ ⊥ 6 n)
    {N A : Subgroup (MulAut W)} (hNH : N ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {k : ℕ} (hA : A ∈ E3.aSet k N) : k ≤ 2 * n := by
  classical
  obtain ⟨F, hFfield, hFfinite, b, c, hFcard, hbc, ε, ψ, hcoords⟩ :=
    exists_natCoords_of_natOmegaMinus (H := H) (n := n) hN
  have main : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F),
      Nat.card F = 2 ^ n →
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
      (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c))) →
      (ψ : ↥(⊤ : Subgroup W) ≃* StdMod OIdx F) →
      NatCoordsOmegaMinusOn H ⊤ (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ →
      k ≤ 2 * n := by
    intro F _ _ _ b c hFcard hbc ε ψ hcoords
    let eM : W ≃* StdMod OIdx F := (Subgroup.topEquiv (G := W)).symm.trans ψ
    have eM_apply : ∀ w : W, eM w = ψ ⟨w, Subgroup.mem_top w⟩ := fun w => rfl
    have he : ∀ (l : ↥H) (w : W), eM ((l : MulAut W) w) =
        Multiplicative.ofAdd (((ε l : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ
          Multiplicative.toAdd (eM w)) := by
      intro l w
      simpa [eM_apply] using hcoords l ⟨w, Subgroup.mem_top w⟩
    have hγ : ∀ γ : ↥(StatedOmega (StatedQuadMinus 3 F b c)),
        congrHom eM ((ε.symm γ : ↥H) : MulAut W) =
          natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ := by
      intro γ
      refine toAddMap_injective fun x => ?_
      have hx : eM (eM.symm (Multiplicative.ofAdd x)) = Multiplicative.ofAdd x :=
        eM.apply_symm_apply _
      calc toAddMap (congrHom eM ((ε.symm γ : ↥H) : MulAut W)) x
          = Multiplicative.toAdd (eM (((ε.symm γ : ↥H) : MulAut W)
              (eM.symm (Multiplicative.ofAdd x)))) := rfl
        _ = Multiplicative.toAdd (Multiplicative.ofAdd
              (((ε ((ε.symm γ : ↥H)) : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ
                Multiplicative.toAdd (eM (eM.symm (Multiplicative.ofAdd x))))) := by
            rw [he]
        _ = (((ε ((ε.symm γ : ↥H)) : GL OIdx F) : Matrix OIdx OIdx F) *ᵥ x) := by
            rw [hx]
            rfl
        _ = Multiplicative.toAdd (natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ
              (Multiplicative.ofAdd x)) := by
            rw [MulEquiv.apply_symm_apply]
            rfl
        _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ) x := rfl
    have key : ∀ n₀ ∈ N, ∀ γ : ↥(StatedOmega (StatedQuadMinus 3 F b c)),
        congrHom eM n₀ * natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ *
          (congrHom eM n₀)⁻¹ ∈ natImage (StatedOmega (StatedQuadMinus 3 F b c)) := by
      intro n₀ hn₀ γ
      let l : ↥H := ε.symm γ
      have hnorm : n₀ * (l : MulAut W) * n₀⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp (hNH hn₀) (l : MulAut W)).mp l.2
      let l' : ↥H := ⟨n₀ * (l : MulAut W) * n₀⁻¹, hnorm⟩
      refine ⟨ε l', ?_⟩
      rw [← hγ (ε l'), MulEquiv.symm_apply_apply]
      change congrHom eM (n₀ * (l : MulAut W) * n₀⁻¹) =
        congrHom eM n₀ * natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ * (congrHom eM n₀)⁻¹
      rw [map_mul, map_mul, map_inv, hγ γ]
    have hmapN : N.map (congrHom eM) ≤ natNorm (StatedOmega (StatedQuadMinus 3 F b c)) := by
      rintro x hx
      obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro hy
        obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hy
        exact key n₀ hn₀ γ
      · rintro hy
        obtain ⟨γ, hγy⟩ := MonoidHom.mem_range.mp hy
        have h1 : y = congrHom eM n₀⁻¹ * natAut (StatedOmega (StatedQuadMinus 3 F b c)) γ *
            (congrHom eM n₀⁻¹)⁻¹ := by
          rw [hγy, map_inv, inv_inv]
          group
        rw [h1]
        exact key n₀⁻¹ (N.inv_mem hn₀) γ
    have hmapA : A.map (congrHom eM) ∈ E3.aSet k (N.map (congrHom eM)) :=
      (map_mem_aSet_iff eM).mpr hA
    exact le_two_mul_of_mem_aSet_natNorm_omegaMinus hbc hFcard hmapN hmapA
  exact @main F hFfield hFfinite
    (@CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow F hFfield hFfinite 2 n
      Nat.prime_two hFcard)
    b c hFcard hbc ε ψ hcoords

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
