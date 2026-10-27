module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth

import CFSG.Walter.PSL2Facts.EvenAutOddPow
public import CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GroupTheory
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem bigB_le_normalizer_u3H {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) := by
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have h' := bigB_le_normalizer_of_hyp111 h.symm
    rwa [bigB_comm] at h'
  have hBQ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  simpa [u3H] using D14.le_normalizer_sup hBL2 hBQ2

private theorem exists_sylow_u3H_image_invariant
    {L1 L2 S : Subgroup G} {m : ℕ} (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) {w : G} (hwB : w ∈ bigB L1 L2 S)
    (hM : Subgroup.zpowers w ≤ Subgroup.normalizer (u3H L1 L2 S : Set G)) :
    ∃ T : Sylow 2 (oTwoQuot ↥(u3H L1 L2 S)),
      (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) = imageOTwoQuot (u3H L1 L2 S) S ∧
      ∀ y ∈ (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))),
        CFSG.GroupTheory.conjModPCore 2 (u3H L1 L2 S) (Subgroup.zpowers w) hM
          ⟨w, Subgroup.mem_zpowers w⟩ y ∈ (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) := by
  classical
  have hSyl : IsSylowTwoOf S (u3H L1 L2 S) :=
    F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW)
      (str86_s_le_u3H hF.toW hSB hm hL2) (u3H_le_p2 L1 L2 S)
  obtain ⟨S₀, hS₀⟩ := F7.isSylowTwoOf_exists_sylow hSyl
  let T : Sylow 2 (oTwoQuot ↥(u3H L1 L2 S)) := S₀.mapSurjective
    (f := QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)))
    (QuotientGroup.mk'_surjective _)
  have hTcoe : (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) =
      imageOTwoQuot (u3H L1 L2 S) S := by
    have h1 : (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) =
        (S₀ : Subgroup ↥(u3H L1 L2 S)).map
          (QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S))) :=
      Sylow.coe_mapSurjective (f := QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)))
        (QuotientGroup.mk'_surjective _) S₀
    rw [h1, hS₀]
    rfl
  refine ⟨T, hTcoe, ?_⟩
  intro y hy
  rw [hTcoe] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
  have hx'S : w * (x : G) * w⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (hSB hwB) (x : G)).mp hxS
  let x' : ↥(u3H L1 L2 S) := ⟨w * (x : G) * w⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hM (Subgroup.mem_zpowers w)) (x : G)).mp x.2⟩
  refine Subgroup.mem_map.mpr ⟨x', Subgroup.mem_subgroupOf.mpr hx'S, ?_⟩
  change QuotientGroup.mk (s := pCore 2 ↥(u3H L1 L2 S)) x' =
    (CFSG.GroupTheory.conjModPCore 2 (u3H L1 L2 S) (Subgroup.zpowers w) hM
      ⟨w, Subgroup.mem_zpowers w⟩) (QuotientGroup.mk (s := pCore 2 ↥(u3H L1 L2 S)) x)
  rw [CFSG.GroupTheory.conjModPCore_mk]

theorem Str86AbHyp.commutator_mem_q2_of_pow_eq_one
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {w : G} (hwB : w ∈ bigB L1 L2 S) {N : ℕ} (hN : Odd N)
    (hw : w ^ N = 1) :
    ∀ x ∈ u3H L1 L2 S, w ^ (Nat.gcd N m * Nat.gcd N (2 ^ m - 1)) * x *
      (w ^ (Nat.gcd N m * Nat.gcd N (2 ^ m - 1)))⁻¹ * x⁻¹ ∈ Q2 L1 L2 S := by
  classical
  have hBH := bigB_le_normalizer_u3H hI.hF.1
  have hM : Subgroup.zpowers w ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) :=
    Subgroup.zpowers_le.mpr (hBH hwB)
  obtain ⟨T, hTcoe, hψT⟩ :=
    exists_sylow_u3H_image_invariant hI.hF hI.hSB hI.hm hI.hL2 hwB hM
  let mw : ↥(Subgroup.zpowers w) := ⟨w, Subgroup.mem_zpowers w⟩
  let ψ : ↥(Subgroup.zpowers w) →* MulAut (oTwoQuot ↥(u3H L1 L2 S)) :=
    CFSG.GroupTheory.conjModPCore 2 (u3H L1 L2 S) (Subgroup.zpowers w) hM
  have hψN : (ψ mw) ^ N = 1 := by
    have hmwN : mw ^ N = 1 := by
      apply Subtype.ext
      simpa using hw
    rw [← map_pow, hmwN, map_one]
  have hL2H : IsL2Quot m (oTwoQuot ↥(u3H L1 L2 S)) :=
    str86_isL2Quot_u3H hI.hF.toW hI.hL2
  obtain ⟨e⟩ := hL2H
  have hm0 : m ≠ 0 := by have := hI.hm; omega
  have hψd : (ψ mw) ^ (Nat.gcd N m * Nat.gcd N (2 ^ m - 1)) = 1 :=
    CFSG.Walter.psl2_mulAut_pow_gcd_mul_gcd_eq_one_of_mulEquiv hm0 e (ψ mw) T hψT hN hψN
  intro x hx
  set d : ℕ := Nat.gcd N m * Nat.gcd N (2 ^ m - 1) with hd
  have hmemM : w ^ d ∈ Subgroup.zpowers w :=
    (Subgroup.zpowers w).pow_mem (Subgroup.mem_zpowers w) d
  have hψwd : ψ ⟨w ^ d, hmemM⟩ = 1 := by
    have h1 : (⟨w ^ d, hmemM⟩ : ↥(Subgroup.zpowers w)) = mw ^ d := by
      apply Subtype.ext
      simp [mw]
    rw [h1, map_pow, hψd]
  have hker : w ^ d ∈ (CFSG.GroupTheory.conjModPCore 2 (u3H L1 L2 S)
      (Subgroup.zpowers w) hM).ker.map (Subgroup.zpowers w).subtype := by
    simpa using Subgroup.mem_map_of_mem (Subgroup.zpowers w).subtype
      (MonoidHom.mem_ker.mpr hψwd)
  have hcomm := ((CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 (u3H L1 L2 S)
    (Subgroup.zpowers w) hM).mp hker).2
  rw [str86_pCoreOf_u3H hI.hF.toW] at hcomm
  exact hcomm x hx

end CFSG.Quasithin.Stroth

end
