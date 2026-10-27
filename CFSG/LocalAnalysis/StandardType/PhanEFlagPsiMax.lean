module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsiOpp
public import CFSG.LocalAnalysis.StandardType.PhanEFlagGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {m : ℕ} {d : List ℕ}

private lemma q2cFPm_blockU_le_Vsub {n : ℕ} {d : List ℕ} (hd : IsCut n d)
    (E : ℕ → Submodule K (Fin n → K)) {i r : ℕ} (hi : i + 1 < d.length) :
    blockU K n d E i r ≤ Vsub n (d.getD (i + 1) 0) :=
  sup_le inf_le_right (Vsub_mono (le_of_lt (hd.strict i hi)))

private lemma q2cFPm_inf_inf_eq_inf_of_le {n : ℕ} {A B C : Submodule K (Fin n → K)}
    (hAC : A ≤ C) : A ⊓ (B ⊓ C) = A ⊓ B := by
  rw [← inf_assoc, inf_eq_left.mpr (le_trans inf_le_left hAC)]

@[expose] def flagPsiMax (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut (m + 1) d)
    (pol : List Bool) : Set (FlagK K (m + 1)) :=
  {x | x ∈ refSet K (m + 1) d ∧ ∀ y ∈ refSet K (m + 1) d,
    (symCox m).length (flagδ m y (flagPsi hK hd pol y)) ≤
      (symCox m).length (flagδ m x (flagPsi hK hd pol x))}

theorem mem_flagPsiMax_iff (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (hn : m + 1 ≤ 4)
    (hd : IsCut (m + 1) d) (pol : List Bool) {x : FlagK K (m + 1)} :
    x ∈ flagPsiMax hK hd pol ↔
      x ∈ refSet K (m + 1) d ∧
        flagδ m x (flagPsi hK hd pol x) = longest (symCox m) (cutTypes m d) := by
  haveI : Finite ((symCox m).parabolic (cutTypes m d)) := Subtype.finite
  constructor
  · rintro ⟨hxR, hxmax⟩
    obtain ⟨z, hzR, hzlong⟩ := exists_opp_flagPsi hK hq hn hd pol
    have hlen := hxmax z hzR
    rw [hzlong] at hlen
    have hxmem := flagδ_mem_parabolic_of_mem_refSet hd hxR (flagPsi_mem hK hd pol hxR)
    exact ⟨hxR, IsLongest.eq_longest ⟨hxmem, fun v hv =>
      le_trans ((isLongest_longest (cs := symCox m) (cutTypes m d)).2 v hv) hlen⟩⟩
  · rintro ⟨hxR, hxlong⟩
    refine ⟨hxR, fun y hy => ?_⟩
    rw [hxlong]
    exact (isLongest_longest (cs := symCox m) (cutTypes m d)).2 _
      (flagδ_mem_parabolic_of_mem_refSet hd hy (flagPsi_mem hK hd pol hy))

theorem blockOK_iff_flagδ (hK : Nat.card K = (2 ^ f) ^ 2) (hd : IsCut (m + 1) d)
    (pol : List Bool) {E : FlagK K (m + 1)} (hE : E ∈ farSet (m + 1) d) :
    (∀ b, b + 1 < d.length → blockOK K f (m + 1) d pol E.E b) ↔
      flagδ m (gateFlag hd hE) (flagPsi hK hd pol (gateFlag hd hE)) =
        longest (symCox m) (cutTypes m d) := by
  have hgate := gateFlag_mem_refSet hd hE
  rw [flagδ_eq_longest_cutTypes_iff hd hgate (flagPsi_mem hK hd pol hgate)]
  constructor
  · intro hOK b r hb hr
    have hr' : r ≤ d.getD (b + 1) 0 - d.getD b 0 := by simpa [blockSize] using hr
    have h := hOK b hb r hr'
    rw [gateFlag_E hd hE hb hr,
      flagPsi_E hK hd pol hgate (b := b) (s := blockSize d b - r) hb
        (Nat.sub_le _ _),
      psiSub]
    by_cases hp : pol.getD b false = true
    · rw [if_pos hp] at h ⊢
      rw [show blockSize d b - (blockSize d b - r) = r by omega,
        gateFlag_E hd hE hb hr]
      have hAC : blockU K (m + 1) d E.E b r ≤ Vsub (m + 1) (d.getD (b + 1) 0) :=
        q2cFPm_blockU_le_Vsub hd E.E hb
      exact (q2cFPm_inf_inf_eq_inf_of_le
        (B := perpB K f (m + 1) (d.getD b 0) (d.getD (b + 1) 0)
          (blockU K (m + 1) d E.E b r)) hAC).trans h
    · rw [if_neg hp] at h ⊢
      rw [gateFlag_E hd hE hb (Nat.sub_le _ _)]
      exact h
  · intro hflag b hb r hr
    have hr' : r ≤ blockSize d b := by simpa [blockSize] using hr
    have h := hflag b r hb hr'
    rw [gateFlag_E hd hE hb hr',
      flagPsi_E hK hd pol hgate (b := b) (s := blockSize d b - r) hb
        (Nat.sub_le _ _)] at h
    rw [psiSub] at h
    by_cases hp : pol.getD b false = true
    · rw [if_pos hp] at h
      rw [show blockSize d b - (blockSize d b - r) = r by omega,
        gateFlag_E hd hE hb hr'] at h
      rw [if_pos hp]
      have hAC : blockU K (m + 1) d E.E b r ≤ Vsub (m + 1) (d.getD (b + 1) 0) :=
        q2cFPm_blockU_le_Vsub hd E.E hb
      exact ((q2cFPm_inf_inf_eq_inf_of_le
        (B := perpB K f (m + 1) (d.getD b 0) (d.getD (b + 1) 0)
          (blockU K (m + 1) d E.E b r)) hAC).symm).trans h
    · rw [if_neg hp] at h
      rw [gateFlag_E hd hE hb (Nat.sub_le _ _)] at h
      rw [if_neg hp]
      exact h

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
