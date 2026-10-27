module

public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.KF.FlagSplit
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (localRank)

section Core

variable {K : Type} [Field K]

theorem finrank_totallyIsotropic_fin_three (F : ReflForm K (Fin 3 → K))
    {W : Submodule K (Fin 3 → K)} (hW : F.IsTotallyIsotropic W) (hW0 : W ≠ ⊥) :
    Module.finrank K W = 1 ∧ Module.finrank K (F.perp W) = 2 := by
  have h1 := F.finrank_perp W
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K W ≤ Module.finrank K (F.perp W) := Submodule.finrank_mono hW
  have h3 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  exact ⟨by omega, by omega⟩

theorem sub_mem_of_fixes_totallyIsotropic_fin_three (F : ReflForm K (Fin 3 → K))
    (T : Module.End K (Fin 3 → K)) {W : Submodule K (Fin 3 → K)}
    (hW : F.IsTotallyIsotropic W) (hW0 : W ≠ ⊥) (hTW : ∀ w ∈ W, T w = w)
    (hTP : ∀ v ∈ F.perp W, T v ∈ F.perp W) (hT : ∀ u v, F.β (T u) (T v) = F.β u v)
    (hdet : LinearMap.det T = 1) : ∀ v ∈ F.perp W, T v - v ∈ W := by
  obtain ⟨hW1, hP2⟩ := finrank_totallyIsotropic_fin_three F hW hW0
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hww : F.β w w = 0 := hW hwW w hwW
  obtain ⟨m, hmP, hmW⟩ := IsConcreteLE.exists_of_lt
    (Submodule.lt_of_le_of_finrank_lt_finrank hW (by omega) : W < F.perp W)
  have hwm : F.β w m = 0 := hmP w hwW
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, F.β w v₀ ≠ 0 := by
    by_contra! h
    exact hw0 (F.nondeg w h)
  have hβ : ∀ a b c : K, F.β w (a • w + b • m + c • v₀) = c * F.β w v₀ := by
    intro a b c
    rw [F.add_right, F.add_right, F.smul_right, F.smul_right, F.smul_right, hww, hwm]
    ring
  have hli : LinearIndependent K ![w, m, v₀] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • w + c 1 • m + c 2 • v₀ = 0 := by
      simpa [Fin.sum_univ_three] using hc
    have h2 : c 2 = 0 := by
      have h := hβ (c 0) (c 1) (c 2)
      rw [hc', F.β_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hv₀
    rw [h2, zero_smul, add_zero] at hc'
    have h1 : c 1 = 0 := by
      by_contra h1
      refine hmW ((Submodule.smul_mem_iff W h1).mp ?_)
      rw [eq_neg_of_add_eq_zero_right hc']
      exact W.neg_mem (W.smul_mem _ hwW)
    rw [h1, zero_smul, add_zero] at hc'
    have h0 : c 0 = 0 := (smul_eq_zero.mp hc').resolve_right hw0
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 3) K (Fin 3 → K), ∀ i, b i = ![w, m, v₀] i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp),
      fun i => by simp [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  have hb0 : b 0 = w := by simpa using hb 0
  have hb1 : b 1 = m := by simpa using hb 1
  have hb2 : b 2 = v₀ := by simpa using hb 2
  have hcoord : ∀ x, x = b.repr x 0 • w + b.repr x 1 • m + b.repr x 2 • v₀ := by
    intro x
    have h := b.sum_repr x
    rw [Fin.sum_univ_three, hb0, hb1, hb2] at h
    exact h.symm
  have hrep : ∀ x, F.β w x = b.repr x 2 * F.β w v₀ := by
    intro x
    conv_lhs => rw [hcoord x]
    exact hβ _ _ _
  have hperp : ∀ x ∈ F.perp W, b.repr x 2 = 0 := by
    intro x hx
    have h := hrep x
    rw [hx w hwW] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hv₀
  have hA : ∀ i j, LinearMap.toMatrix b b T i j = b.repr (T (b j)) i := fun i j => by
    rw [LinearMap.toMatrix_apply]
  have hTw : T (b 0) = b 0 := by
    rw [hb0]
    exact hTW w hwW
  have hA00 : LinearMap.toMatrix b b T 0 0 = 1 := by simp [hA, hTw]
  have hA10 : LinearMap.toMatrix b b T 1 0 = 0 := by simp [hA, hTw]
  have hA20 : LinearMap.toMatrix b b T 2 0 = 0 := by simp [hA, hTw]
  have hA21 : LinearMap.toMatrix b b T 2 1 = 0 := by
    rw [hA]
    exact hperp _ (by rw [hb1]; exact hTP m hmP)
  have hA22 : LinearMap.toMatrix b b T 2 2 = 1 := by
    rw [hA, hb2]
    have h1 : F.β w (T v₀) = F.β w v₀ := by
      have h := hT w v₀
      rwa [hTW w hwW] at h
    have h2 := hrep (T v₀)
    rw [h1] at h2
    exact mul_right_cancel₀ hv₀ (h2.symm.trans (one_mul _).symm)
  have hdetA : (LinearMap.toMatrix b b T).det = 1 := by
    rw [LinearMap.det_toMatrix]
    exact hdet
  rw [Matrix.det_fin_three, hA00, hA10, hA20, hA21, hA22] at hdetA
  have hA11 : LinearMap.toMatrix b b T 1 1 = 1 := by linear_combination hdetA
  intro v hv
  have hv2 : b.repr v 2 = 0 := hperp v hv
  have hTm2 : b.repr (T m) 2 = 0 := by
    have h := hA21
    rwa [hA, hb1] at h
  have hTm1 : b.repr (T m) 1 = 1 := by
    have h := hA11
    rwa [hA, hb1] at h
  obtain ⟨a, ha⟩ : ∃ a : K, T m = a • w + m := by
    refine ⟨b.repr (T m) 0, ?_⟩
    conv_lhs => rw [hcoord (T m)]
    rw [hTm1, hTm2, zero_smul, add_zero, one_smul]
  obtain ⟨r0, r1, hvr⟩ : ∃ r0 r1 : K, v = r0 • w + r1 • m := by
    refine ⟨b.repr v 0, b.repr v 1, ?_⟩
    conv_lhs => rw [hcoord v]
    rw [hv2, zero_smul, add_zero]
  have e : T v - v = (r1 * a) • w := by
    rw [hvr, map_add, map_smul, map_smul, hTW w hwW, ha]
    module
  rw [e]
  exact W.smul_mem _ hwW

end Core

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem eq_one_of_fixes_isotropic_su_three (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {g : StatedSU 3 (2 ^ f) K} (hgp : g ^ p = 1) {W : Submodule K (Fin 3 → K)}
    (hW : (unitaryForm 2 f hK 3).IsTotallyIsotropic W) (hW0 : W ≠ ⊥)
    (hfix : ∀ w ∈ W, natRep (StatedSU 3 (2 ^ f) K) g w = w) : g = 1 := by
  have hρ : IsIsometric (unitaryForm 2 f hK 3) (natRep (StatedSU 3 (2 ^ f) K)) :=
    isIsometric_natRep_statedSU hK 3
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    have h1 : Nat.card K = 1 := by simp [hK, h0]
    exact absurd h1 (Finite.one_lt_card (α := K)).ne'
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine FlagSplit.eq_one_of_fixes_flag _ _ hρ (natRep_injective _) hp hp2 hgp hfix ?_
  refine sub_mem_of_fixes_totallyIsotropic_fin_three _ _ hW hW0 hfix ?_ (hρ g)
    (CFSG.RankThree.PartTwo.Census.det_natRep_statedSU hU g)
  intro v hv
  refine hρ.apply_mem_perp_of_forall (fun w hw => ?_) hv
  have hinv : natRep (StatedSU 3 (2 ^ f) K) g⁻¹ w = w := by
    calc natRep (StatedSU 3 (2 ^ f) K) g⁻¹ w
        = natRep (StatedSU 3 (2 ^ f) K) g⁻¹ (natRep (StatedSU 3 (2 ^ f) K) g w) := by
          rw [hfix w hw]
      _ = w := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hinv]
  exact hw

theorem card_le_of_invariant_isotropic_su_three (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (E : Subgroup (StatedSU 3 (2 ^ f) K))
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1)
    {W : Submodule K (Fin 3 → K)} (hW : (unitaryForm 2 f hK 3).IsTotallyIsotropic W)
    (hW0 : W ≠ ⊥)
    (hWE : ∀ g ∈ E, ∀ w ∈ W, natRep (StatedSU 3 (2 ^ f) K) g w ∈ W) : Nat.card E ≤ p := by
  let ρE : E →* Module.End K (Fin 3 → K) := (natRep (StatedSU 3 (2 ^ f) K)).comp E.subtype
  have hW' : ∀ g : E, ∀ w ∈ W, ρE g w ∈ W := fun g w hw => hWE g g.2 w hw
  let ρW : E →* (W ≃ₗ[K] W) := LIT.restrictAction (FlagSplit.repAut ρE) W hW'
  have hinj : Function.Injective ρW := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    refine Subgroup.mem_bot.2 (Subtype.ext (eq_one_of_fixes_isotropic_su_three hK hp hp2
      (hexp g g.2) hW hW0 fun w hw => ?_))
    exact congrArg Subtype.val (LinearEquiv.congr_fun hg ⟨w, hw⟩)
  have hfin : Finite (W ≃ₗ[K] W) := FlagSplit.finite_linearEquiv (K := K)
  have hcommE : ∀ g h : E, g * h = h * g := fun g h => Subtype.ext (hcomm g g.2 h h.2)
  have hexpE : ∀ g : E, g ^ p = 1 := fun g => Subtype.ext (hexp g g.2)
  have hdim := (finrank_totallyIsotropic_fin_three _ hW hW0).1
  calc Nat.card E ≤ Nat.card ρW.range :=
        Nat.card_le_card_of_injective ρW.rangeRestrict
          (MonoidHom.rangeRestrict_injective_iff.mpr hinj)
    _ ≤ p ^ (Module.finrank K W / 1) :=
        FlagSplit.card_range_le_pow_div ρW hp (LIT.natCast_ne_zero_of_charTwo hp hp2) one_pos
          (fun i hi hi1 => absurd hi1 (by omega)) hcommE hexpE
    _ = p := by simp [hdim]

theorem localRank_statedSU_three_le_one (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : localRank p ↥(StatedSU 3 (2 ^ f) K) ≤ 1 := by
  by_contra hlt
  have hrk : 2 ≤ localRank p ↥(StatedSU 3 (2 ^ f) K) := by omega
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hrk
  have hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : E) ⟨h, hh⟩)
  have hexp : ∀ g ∈ E, g ^ p = 1 := fun g hg =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian g hg
  obtain ⟨W, hW0, hWiso, hWE⟩ := exists_invariant_isotropic (unitaryForm 2 f hK 3)
    (natRep (StatedSU 3 (2 ^ f) K)) (isIsometric_natRep_statedSU hK 3) (natRep_injective _)
    hU2 hU0 hEU
  have hle := card_le_of_invariant_isotropic_su_three hK hp hp2 E hcomm hexp hWiso hW0 hWE
  rw [hEc] at hle
  nlinarith [hp.two_le]

end Main

end CFSG.RankThree.PartOne.KFU
