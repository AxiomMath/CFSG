module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerDerived
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.StandardType

namespace LayerCyc

open Matrix Module

section FixedCount

variable {K : Type} [Field K] [Finite K] {n : Type} [Fintype n] [DecidableEq n]

theorem pow_finrank_modEq {X : Matrix n n K} {p : ℕ} [hp : Fact p.Prime] (hXp : X ^ p = 1)
    (U : Submodule K (n → K)) (hU : ∀ v ∈ U, X *ᵥ v ∈ U) :
    Nat.card K ^ finrank K U ≡
      Nat.card K ^ finrank K ↥(U ⊓ LinearMap.ker (Matrix.toLin' (X - 1))) [MOD p] := by
  classical
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun v => ⟨X *ᵥ (v : n → K), hU _ v.2⟩
  have hpow : ∀ (m : ℕ) (v : U), ((f ^ m) v : n → K) = (X ^ m) *ᵥ (v : n → K) := by
    intro m
    induction m with
    | zero => intro v; simp; rfl
    | succ m ih =>
      intro v
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec]
      exact ih (f v)
  have hfp : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext v
    apply Subtype.ext
    rw [hpow, hXp, Matrix.one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hfp
  have hmem : ∀ v : n → K, v ∈ LinearMap.ker (Matrix.toLin' (X - 1)) ↔ X *ᵥ v = v := by
    intro v
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  let e : Function.fixedPoints f ≃ ↥(U ⊓ LinearMap.ker (Matrix.toLin' (X - 1))) :=
    { toFun := fun v => ⟨((v : U) : n → K), Submodule.mem_inf.mpr ⟨(v : U).2,
        (hmem _).mpr (congrArg Subtype.val v.2)⟩⟩
      invFun := fun w => ⟨⟨w, (Submodule.mem_inf.mp w.2).1⟩,
        Subtype.ext ((hmem _).mp (Submodule.mem_inf.mp w.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcardU : Fintype.card U = Nat.card K ^ finrank K U := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K) (V := U)]
  have hcardF : Fintype.card (Function.fixedPoints f) =
      Nat.card K ^ finrank K ↥(U ⊓ LinearMap.ker (Matrix.toLin' (X - 1))) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K)]
  convert hmod using 1
  · exact hcardU.symm
  · convert hcardF.symm

end FixedCount

theorem nine_pow_mod_seven {k : ℕ} (hk : k ≤ 3) (h : 9 ^ k ≡ 1 [MOD 7]) : k = 0 ∨ k = 3 := by
  interval_cases k
  · exact Or.inl rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inr rfl

theorem eq_one_of_pow_seven_of_commute {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    {X G : Matrix (Fin 3) (Fin 3) K} (hX7 : X ^ 7 = 1) (hG3 : G ^ 3 = 1) (hG1 : G ≠ 1)
    (hXG : X * G = G * X) : X = 1 := by
  have hV : finrank K (Fin 3 → K) = 3 := by simp
  have memK : ∀ (M : Matrix (Fin 3) (Fin 3) K) (v : Fin 3 → K),
      v ∈ LinearMap.ker (Matrix.toLin' (M - 1)) ↔ M *ᵥ v = v := by
    intro M v
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hle : ∀ U : Submodule K (Fin 3 → K), finrank K U ≤ 3 := fun U =>
    (Submodule.finrank_le U).trans hV.le
  set W := LinearMap.ker (Matrix.toLin' (G - 1)) with hW
  set F := LinearMap.ker (Matrix.toLin' (X - 1)) with hF
  have hFt : F = ⊥ ∨ F = ⊤ := by
    have h := pow_finrank_modEq (hp := ⟨by norm_num⟩) hX7 ⊤ fun v _ => Submodule.mem_top
    rw [top_inf_eq, finrank_top, hV, hK] at h
    rcases nine_pow_mod_seven (hle F) (by
      have h' : 9 ^ 3 ≡ 1 [MOD 7] := by decide
      exact h.symm.trans h') with h0 | h3
    · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
    · exact Or.inr (Submodule.eq_top_of_finrank_eq (h3.trans hV.symm))
  rcases hFt with hF0 | hF1
  · exfalso
    have hW0 : finrank K W ≠ 0 := by
      intro h0
      have h := pow_finrank_modEq (hp := ⟨Nat.prime_three⟩) hG3 ⊤ fun v _ => Submodule.mem_top
      rw [top_inf_eq, finrank_top, hV, hK, ← hW, h0] at h
      exact absurd h (by decide)
    have hW3 : finrank K W ≠ 3 := by
      intro h3
      apply hG1
      have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (h3.trans hV.symm)
      have h1 : Matrix.toLin' (G - 1) = 0 := LinearMap.ker_eq_top.mp htop
      have h2 : G - 1 = 0 := Matrix.toLin'.injective (by rw [h1, map_zero])
      exact sub_eq_zero.mp h2
    have hXW : ∀ v ∈ W, X *ᵥ v ∈ W := by
      intro v hv
      rw [memK] at hv ⊢
      rw [Matrix.mulVec_mulVec, ← hXG, ← Matrix.mulVec_mulVec, hv]
    have h := pow_finrank_modEq (hp := ⟨by norm_num⟩) hX7 W hXW
    rw [← hF, hF0, inf_bot_eq, finrank_bot, hK] at h
    rcases nine_pow_mod_seven (hle W) h with h0 | h3
    · exact hW0 h0
    · exact hW3 h3
  · have h1 : Matrix.toLin' (X - 1) = 0 := LinearMap.ker_eq_top.mp hF1
    have h2 : X - 1 = 0 := Matrix.toLin'.injective (by rw [h1, map_zero])
    exact sub_eq_zero.mp h2

end LayerCyc

open LayerCyc CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U

theorem ggSU33ThreeCentInput_holds : GGSU33ThreeCentInput := by
  intro g x hg hxp hx3 hgx
  have hdvd : orderOf x ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
    have := orderOf_dvd_natCard x
    rwa [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9] at this
  have h7 : orderOf x = 7 := by
    rcases (Nat.Prime.dvd_mul hxp).mp hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hxp).mp h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hxp Nat.prime_two).mp (hxp.dvd_of_dvd_pow h)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hxp Nat.prime_three).mp (hxp.dvd_of_dvd_pow h)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hxp (by norm_num)).mp h
  have hval : ∀ (y : StatedSU 3 3 F9) (k : ℕ), y ^ k = 1 →
      ((y : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) ^ k = 1 := fun y k hy => by
    have h := congrArg (fun z : StatedSU 3 3 F9 => ((z : GL (Fin 3) F9) :
      Matrix (Fin 3) (Fin 3) F9)) hy
    simpa using h
  have hX7 := hval x 7 (by have := pow_orderOf_eq_one x; rwa [h7] at this)
  have hG3 := hval g 3 (by have := pow_orderOf_eq_one g; rwa [hg] at this)
  have hG1 : ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext (Units.ext h)
    rw [this, orderOf_one] at hg
    omega
  have hXG : ((x : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *
      ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) =
      ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) *
      ((x : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) := by
    have h := congrArg (fun z : StatedSU 3 3 F9 => ((z : GL (Fin 3) F9) :
      Matrix (Fin 3) (Fin 3) F9)) hgx
    simp only [Subgroup.coe_mul, Units.val_mul] at h
    exact h.symm
  have hX1 := eq_one_of_pow_seven_of_commute card_F9 hX7 hG3 hG1 hXG
  have : x = 1 := Subtype.ext (Units.ext hX1)
  rw [this, orderOf_one] at h7
  omega

section Wiring


theorem ggLayerDerivedFixSolvableInput_of_tits (hT : GGTitsThreeCentInput) :
    GGLayerDerivedFixSolvableInput :=
  ggLayerDerivedFixSolvableInput_of ggSU33ThreeCentInput_holds hT

theorem ggLayerCenterCyclicInput_of_tits_exc
    (hT : GGTitsThreeCentInput) (hexc : GGLayerCenterCyclicExcInput) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_su33_tits_exc ggSU33ThreeCentInput_holds hT hexc

end Wiring

end CFSG.StandardType

end
