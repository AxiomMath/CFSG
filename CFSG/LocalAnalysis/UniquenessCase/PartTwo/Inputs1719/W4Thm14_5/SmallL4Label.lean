module

public import CFSG.LieType.SpecialLinear.SLModel.Basic
public import CFSG.LieType.SpecialLinear.ExteriorModel.Weights
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.SpecialLinear.SLModel CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.HardMathSupport.GuralnickMalle
open scoped TensorProduct

theorem orbitSize_sub_movedOrbit_singleton_four {j : Fin 4} (hj : 1 ≤ (j : ℕ)) :
    orbitSize ({j} : Finset (Fin 4)) - movedOrbit (n := 4) (by norm_num) {j} = 2 := by
  rw [orbitSize_singleton, movedOrbit_singleton _ hj]
  have hj4 := j.isLt
  obtain ⟨v, hv⟩ := j
  simp only at hj hj4 ⊢
  interval_cases v <;> decide

theorem exists_single_of_movedTop_le {f s e : ℕ} (he : 3 ≤ e) (ε : Fin f → Finset (Fin 4))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin 4) ∉ ε r) (ht : ∃ r, ε r ≠ ∅)
    (hs : e ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hm : s * movedTop (n := 4) (by norm_num) ε ≤ 4 * e + 4) :
    ∃ r₀ : Fin f, ∃ j : Fin 4, 1 ≤ (j : ℕ) ∧ ε r₀ = {j} ∧ ∀ r, r ≠ r₀ → ε r = ∅ := by
  classical
  set T := univ.filter fun r => ε r ≠ ∅ with hT
  have hmemT : ∀ r, r ∈ T ↔ ε r ≠ ∅ := fun r => by simp [hT]
  have hTpos : 0 < T.card := by
    obtain ⟨r, hr⟩ := ht
    exact Finset.card_pos.mpr ⟨r, (hmemT r).mpr hr⟩
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, zero_mul] at hs
      omega
    · exact h
  by_cases h3 : 3 ≤ T.card
  · exfalso
    have hlow := two_mul_pow_le_movedTop_of_three (n := 4) (by norm_num) ε h0 h3
    have hpow : ∀ t, 3 ≤ t → 4 * t + 5 ≤ 2 * 4 ^ (t - 1) := by
      intro t ht3
      induction t, ht3 using Nat.le_induction with
      | base => norm_num
      | succ t ht3 ih =>
        have h4 : 4 ^ (t + 1 - 1) = 4 * 4 ^ (t - 1) := by
          rw [show t + 1 - 1 = (t - 1) + 1 by omega, pow_succ]
          ring
        rw [h4]
        omega
    have h1 := hpow T.card h3
    have h2 : s * (4 * T.card + 5) ≤ s * movedTop (n := 4) (by norm_num) ε :=
      Nat.mul_le_mul_left s (h1.trans hlow)
    nlinarith
  by_cases h2 : T.card = 2
  · exfalso
    obtain ⟨i₁, i₂, hne, hT2⟩ := Finset.card_eq_two.mp h2
    have hrest : ∀ i, i ≠ i₁ → i ≠ i₂ → ε i = ∅ := by
      intro i hi1 hi2
      by_contra hi
      have hiT : i ∈ T := (hmemT i).mpr hi
      rw [hT2] at hiT
      rcases Finset.mem_insert.mp hiT with h | h
      · exact hi1 h
      · exact hi2 (Finset.mem_singleton.mp h)
    have hε₁ : ε i₁ ≠ ∅ := (hmemT i₁).mp (by rw [hT2]; exact Finset.mem_insert_self _ _)
    have hε₂ : ε i₂ ≠ ∅ :=
      (hmemT i₂).mp (by rw [hT2]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hformula := movedTop_of_two (n := 4) (by norm_num) ε hne hrest
    have hN₂ := n_le_orbitSize (n := 4) (by norm_num) (h0 i₂) hε₂
    have hM₁ := two_le_movedOrbit (n := 4) (by norm_num) (h0 i₁) hε₁
    have hM₂ := two_le_movedOrbit (n := 4) (by norm_num) (h0 i₂) hε₂
    have h12 : 12 ≤ movedTop (n := 4) (by norm_num) ε := by
      rw [hformula]
      by_cases hc : 2 ≤ (ε i₁).card
      · have hM := two_mul_two_mul_sub_three_le_movedOrbit (n := 4) (by norm_num) (h0 i₁)
          (by omega : 3 ≤ (ε i₁).card + 1)
        nlinarith
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hε₁)
          omega : (ε i₁).card = 1)
        have hj1 : 1 ≤ (j : ℕ) := by
          rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
          · exact absurd (by rw [hj]; exact Finset.mem_singleton.mpr (Fin.ext h.symm))
              (h0 i₁)
          · exact h
        have hF := orbitSize_sub_movedOrbit_singleton_four hj1
        rw [← hj] at hF
        rw [hF]
        nlinarith
    have hs2 : e ≤ s * 2 := by rwa [h2] at hs
    have h4 : s * 12 ≤ 4 * e + 4 :=
      (Nat.mul_le_mul_left s h12).trans hm
    omega
  have h1 : T.card = 1 := by omega
  obtain ⟨r₀, hT1⟩ := Finset.card_eq_one.mp h1
  have hr₀ : ε r₀ ≠ ∅ := (hmemT r₀).mp (by rw [hT1]; exact Finset.mem_singleton_self _)
  have hrest : ∀ r, r ≠ r₀ → ε r = ∅ := by
    intro r hr
    by_contra hne
    have hrT : r ∈ T := (hmemT r).mpr hne
    rw [hT1] at hrT
    exact hr (Finset.mem_singleton.mp hrT)
  have hmt := movedTop_of_one (n := 4) (by norm_num) ε r₀ hrest
  have hs1 : e ≤ s := by rw [h1, mul_one] at hs; exact hs
  by_cases hc : 2 ≤ (ε r₀).card
  · exfalso
    have hM := two_mul_two_mul_sub_three_le_movedOrbit (n := 4) (by norm_num) (h0 r₀)
      (by omega : 3 ≤ (ε r₀).card + 1)
    rw [← hmt] at hM
    have h10 : s * 10 ≤ 4 * e + 4 := (Nat.mul_le_mul_left s (by omega)).trans hm
    omega
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (by
      have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr₀)
      omega : (ε r₀).card = 1)
    refine ⟨r₀, j, ?_, hj, hrest⟩
    rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
    · exact absurd (by rw [hj]; exact Finset.mem_singleton.mpr (Fin.ext h.symm)) (h0 r₀)
    · exact h

theorem finrank_range_sub_one_eq_mul {G W : Type} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) = 2 ^ s) (k : Type)
    [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] (g : G) :
    finrank (ZMod 2) (LinearMap.range (ρ g - 1)) =
      s * finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g - 1)) := by
  classical
  set R := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) with hR
  have h1 := card_eq_pow_finrank_extendScalars ρ k
  have h2 := card_fixSubGen_eq_pow_finrank_extendScalars ρ k (Subgroup.zpowers g)
  rw [hE, ← pow_mul] at h1 h2
  have hfixW : fixSubGen ρ (Subgroup.zpowers g) = LinearMap.ker (ρ g - 1) := by
    ext v
    rw [mem_fixSubGen, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · exact fun h => h g (Subgroup.mem_zpowers g)
    · intro h a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hfix : ∀ m : ℕ, ρ (g ^ m) v = v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · simpa using hfix m
      · have h' := hfix m
        rw [_root_.zpow_neg, zpow_natCast]
        calc ρ (g ^ m)⁻¹ v = ρ (g ^ m)⁻¹ (ρ (g ^ m) v) := by rw [h']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hfixR : fixSubGen R (Subgroup.zpowers g) = LinearMap.ker (R g - 1) := by
    ext v
    rw [mem_fixSubGen, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · exact fun h => h g (Subgroup.mem_zpowers g)
    · intro h a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hfix : ∀ m : ℕ, R (g ^ m) v = v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, h, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · simpa using hfix m
      · have h' := hfix m
        rw [_root_.zpow_neg, zpow_natCast]
        calc R (g ^ m)⁻¹ v = R (g ^ m)⁻¹ (R (g ^ m) v) := by rw [h']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hW : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rwa [Nat.card_zmod] at this
  have hC : Nat.card (fixSubGen ρ (Subgroup.zpowers g)) =
      2 ^ finrank (ZMod 2) (fixSubGen ρ (Subgroup.zpowers g)) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixSubGen ρ (Subgroup.zpowers g))
    rwa [Nat.card_zmod] at this
  have hd1 : finrank (ZMod 2) W = s * finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G)
      ρ.asModule] ρ.asModule) :=
    Nat.pow_right_injective le_rfl (hW.symm.trans h1)
  have hd2 : finrank (ZMod 2) (fixSubGen ρ (Subgroup.zpowers g)) =
      s * finrank k (fixSubGen R (Subgroup.zpowers g)) :=
    Nat.pow_right_injective le_rfl (hC.symm.trans h2)
  rw [hfixW] at hd2
  rw [hfixR] at hd2
  haveI : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) ρ.asModule :=
    finiteDimensional_endField ρ
  have hrn1 := LinearMap.finrank_range_add_finrank_ker (ρ g - 1)
  have hrn2 := LinearMap.finrank_range_add_finrank_ker (R g - 1)
  have hrn2' : finrank k (LinearMap.range (R g - 1)) +
      finrank k (LinearMap.ker (R g - 1)) =
      finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) := hrn2
  have hs2 : s * finrank k (LinearMap.range (R g - 1)) + s * finrank k (LinearMap.ker (R g - 1)) =
      s * finrank k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) := by
    rw [← mul_add, hrn2']
  omega

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k]

theorem exists_perm_finrank_range_slModelRep_sub_one {m f : ℕ}
    (ε : Fin f → Finset (Fin (m + 2))) {x : SpecialLinearGroup (Fin (m + 2)) F}
    (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ π : Equiv.Perm (Fin (m + 2)), π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
      finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) =
        finrank k (LinearMap.range (slModelRep (F := F) (k := k) (m := m + 1) ε x - 1)) := by
  obtain ⟨π, g, hπ, hπ0, hconj⟩ := exists_conj_eq_permMatrix_of_ne_one hx hx1
  refine ⟨π, hπ, by simpa using hπ0, ?_⟩
  let G := twistHom (frobTwist F k f) g
  have hG : G * twistHom (frobTwist F k f) x * G⁻¹ = fun _ => permSL (k := k) π := by
    rw [← map_inv, ← map_mul, ← map_mul]
    funext r
    refine Subtype.ext ?_
    change ((SpecialLinearGroup.map (frobTwist F k f r) (g * x * g⁻¹) :
      SpecialLinearGroup (Fin (m + 2)) k) : Matrix (Fin (m + 2)) (Fin (m + 2)) k) =
        π.permMatrix k
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hconj, permMatrix_map]
  have h := finrank_range_rep_conj_sub_one (bRep (k := k) ε) G (twistHom (frobTwist F k f) x)
  rw [hG] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
