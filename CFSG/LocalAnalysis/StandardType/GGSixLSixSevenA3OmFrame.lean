module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmPair
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmSingle
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmClass
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3ProofFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMoves
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {E J : Subgroup (V ≃ₗ[K] V)}

theorem GGOmA3Hyp.exists_pair_mem_centralizer (H : GGOmA3Hyp F E J) :
    ∃ a b : Fin r, a ≠ b ∧
      F.ι (ofAdd (Pi.single a 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) ∧
      F.ι (ofAdd (Pi.single b 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := by
  obtain ⟨a, ha⟩ := H.exists_single_mem_centralizer
  by_cases hb : ∃ b : Fin r, b ≠ a ∧
      F.ι (ofAdd (Pi.single b 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V))
  · obtain ⟨b, hba, hb⟩ := hb
    exact ⟨a, b, hba.symm, ha, hb⟩
  · exfalso
    have hY : ∀ m : Fin r,
        F.ι (ofAdd (Pi.single m 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) → m = a :=
      fun m hm => by_contra fun hma => hb ⟨m, hma, hm⟩
    obtain ⟨t, h, ht, hta, hfull, hh, -, hJB, hUa⟩ := H.exists_full_support_of_single hY
    have haE : F.ι (ofAdd (Pi.single a 1)) ∈ E := H.mem_E_of_mem_centralizer (F.mem _) ha
    exact H.false_of_class ht hta hfull (H.isComponentOf_single haE ht hta hfull hh hJB hUa)

theorem GGOmA3Hyp.exists_shape (H : GGOmA3Hyp F E J) :
    ∃ i j k l : Fin r, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      (∀ s : Fin r → ZMod p, F.ι (ofAdd s) ∈ E → ∀ m, m ≠ i → m ≠ j → s m = 0) ∧
      F.ι (ofAdd (Pi.single k 1)) ∈ J ∧ F.ι (ofAdd (Pi.single l 1)) ∈ J := by
  obtain ⟨a, b, hab, ha, hb⟩ := H.exists_pair_mem_centralizer
  obtain ⟨k, l, hkl, hka, hkb, hla, hlb, hk, hl⟩ := H.exists_pair_mem_of_pair hab ha hb
  exact ⟨a, b, k, l, hab, hka.symm, hla.symm, hkb.symm, hlb.symm, hkl,
    fun s hs m hma hmb => H.apply_eq_zero_of_pair hab ha hb hs hma hmb, hk, hl⟩

theorem GGOmA3Hyp.exists_mem_normalizer_conj_le (H : GGOmA3Hyp F E J) :
    ∃ w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)),
      ∀ e ∈ E, w⁻¹ * e * w ∈ J := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, hE0, hk, hl⟩ := H.exists_shape
  set π : Equiv.Perm (Fin r) := Equiv.swap i k * Equiv.swap j l with hπ
  obtain ⟨h1, h2⟩ := ggA3_swap_symm hij hjk hkl
  have hπk : π k = i := by rw [← h1]; exact π.apply_symm_apply i
  have hπl : π l = j := by rw [← h2]; exact π.apply_symm_apply j
  obtain ⟨w, hw, hws⟩ := H.moves π (fun _ => 1) (fun _ => Subgroup.one_mem _) (by simp)
  refine ⟨w, hw, fun e he => ?_⟩
  obtain ⟨s, rfl⟩ := F.exists_eq (H.le_A he)
  have hs0 : ∀ m, m ≠ i → m ≠ j → toAdd s m = 0 := by
    intro m hmi hmj
    exact hE0 (toAdd s) (by simpa using he) m hmi hmj
  have hs : s = ofAdd (toAdd s) := (ofAdd_toAdd s).symm
  rw [hs, hws]
  have hvec : (fun m => ((1 : (ZMod p)ˣ) : ZMod p) * toAdd s (π m)) =
      toAdd s i • (Pi.single k 1 : Fin r → ZMod p) +
        toAdd s j • (Pi.single l 1 : Fin r → ZMod p) := by
    funext m
    simp only [Units.val_one, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hmk : m = k
    · subst hmk
      rw [hπk, Pi.single_eq_same, Pi.single_eq_of_ne hkl, mul_one, mul_zero, add_zero]
    · by_cases hml : m = l
      · subst hml
        rw [hπl, Pi.single_eq_same, Pi.single_eq_of_ne hkl.symm, mul_one, mul_zero, zero_add]
      · rw [Pi.single_eq_of_ne hmk, Pi.single_eq_of_ne hml, mul_zero, mul_zero, add_zero]
        refine hs0 (π m) (fun h => hmk (π.injective (h.trans hπk.symm)))
          (fun h => hml (π.injective (h.trans hπl.symm)))
  rw [hvec, ofAdd_add, map_mul]
  exact J.mul_mem (StepTwoToral.ofAdd_smul_mem hk _) (StepTwoToral.ofAdd_smul_mem hl _)

end Frame

section OmLevel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_conj_le_of_a3 (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (A : Subgroup (V ≃ₗ[K] V)) (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (h4 : p ^ 4 ≤ Nat.card A) {E J : Subgroup (V ≃ₗ[K] V)} (hEA : E ≤ A)
    (hE : Nat.card E = p ^ 2)
    (hJ : IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer (E : Set (V ≃ₗ[K] V))))
    (hCJ : A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) ≤ E)
    (hJcard : Nat.card J ∣ 40320)
    (hJZ : ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z ^ p = 1 → z = 1) :
    ∃ w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)),
      ∀ e ∈ E, w⁻¹ * e * w ∈ J := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨r, F, hF⟩ := ggOmFrameMoveInput_of_elem ggOmFrameElemMoveInput_holds K V p hp2 Q hQ hT A
    hAΩ hApow hAcomm hmax
  have hcA : Nat.card A = p ^ r := by
    rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hr4 : 4 ≤ r := by
    by_contra h
    have hlt : p ^ r < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by omega)
    exact absurd (hcA ▸ h4) (not_le.mpr hlt)
  exact
    (GGOmA3Hyp.mk hQ hT hp2 hAΩ hmax hr4 hF hEA hE hJ hCJ hJcard hJZ).exists_mem_normalizer_conj_le

end OmLevel

end CoordOm

end CFSG.StandardType
