module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagExchCalc
public import CFSG.LocalAnalysis.StandardType.PhanEFlagProj

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem isCut_22 : IsCut 4 [0, 2, 4] where
  head := rfl
  last := rfl
  strict := by
    intro i hi
    rw [show ([0, 2, 4] : List ℕ).length = 3 from rfl] at hi
    have hi2 : i < 2 := by omega
    interval_cases i <;> decide

theorem exists_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    ∃ y : FlagK K 4, y ∈ refSet K 4 [0, 2, 4] ∧
      y.E 1 = Submodule.span K (jShiftInv K f '' (x.E 3 : Set (Fin 4 → K))) ∧
      y.E 3 = Vsub 4 2 ⊔ Submodule.span K (jShift K f '' (x.E 1 : Set (Fin 4 → K))) := by
  have hx2 : x.E 2 = Vsub (K := K) 4 2 := by simpa using hx 1 (by decide)
  have hL : x.E 1 ≤ Vsub (K := K) 4 2 := by rw [← hx2]; exact x.mono (by norm_num)
  have hH : Vsub (K := K) 4 2 ≤ x.E 3 := by rw [← hx2]; exact x.mono (by norm_num)
  have hL1 : finrank K (x.E 1) = 1 := x.dim 1 (by norm_num)
  have hH3 : finrank K (x.E 3) = 3 := x.dim 3 (by norm_num)
  have hp1 : finrank K (q2cFX_JInv f (x.E 3)) = 1 := q2cFX_finrank_JInv hK hH hH3
  have hpL : q2cFX_JInv f (x.E 3) ≤ Vsub (K := K) 4 2 :=
    q2cFX_span_jShiftInv_le_Vsub _
  have hP3 : finrank K (q2cFX_Phi f (x.E 1)) = 3 := q2cFX_finrank_Phi hK hL hL1
  have hV2 : finrank K (Vsub (K := K) 4 2) = 2 := finrank_Vsub (K := K) (n := 4) (by norm_num)
  have hle : Vsub (K := K) 4 2 ≤ q2cFX_Phi f (x.E 1) := le_sup_left
  refine ⟨FlagK.ofChain4 _ (Vsub (K := K) 4 2) _ hp1 hV2 hP3 hpL hle, ?_, ?_, ?_⟩
  · intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i
    · change (FlagK.ofChain4 _ (Vsub (K := K) 4 2) _ hp1 hV2 hP3 hpL hle).E 0 =
        Vsub (K := K) 4 0
      rw [FlagK.E_zero, Vsub_zero]
    · change (FlagK.ofChain4 _ (Vsub (K := K) 4 2) _ hp1 hV2 hP3 hpL hle).E 2 =
        Vsub (K := K) 4 2
      exact FlagK.ofChain4_E_two _ _ _ _ _ _ _ _
    · change (FlagK.ofChain4 _ (Vsub (K := K) 4 2) _ hp1 hV2 hP3 hpL hle).E 4 =
        Vsub (K := K) 4 4
      rw [FlagK.top _ 4 (by norm_num), Vsub_self]
  · exact FlagK.ofChain4_E_one _ _ _ _ _ _ _ _
  · exact FlagK.ofChain4_E_three _ _ _ _ _ _ _ _

@[expose] noncomputable def flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) (x : FlagK K 4) :
    FlagK K 4 :=
  open Classical in
  if h : x ∈ refSet K 4 [0, 2, 4] then Classical.choose (exists_flagPsiX hK h) else x

theorem flagPsiX_mem (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) : flagPsiX hK x ∈ refSet K 4 [0, 2, 4] := by
  rw [flagPsiX, dif_pos hx]
  exact (Classical.choose_spec (exists_flagPsiX hK hx)).1

theorem flagPsiX_E_one (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagPsiX hK x).E 1 = Submodule.span K (jShiftInv K f '' (x.E 3 : Set (Fin 4 → K))) := by
  rw [flagPsiX, dif_pos hx]
  exact (Classical.choose_spec (exists_flagPsiX hK hx)).2.1

theorem flagPsiX_E_three (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (flagPsiX hK x).E 3 =
      Vsub 4 2 ⊔ Submodule.span K (jShift K f '' (x.E 1 : Set (Fin 4 → K))) := by
  rw [flagPsiX, dif_pos hx]
  exact (Classical.choose_spec (exists_flagPsiX hK hx)).2.2

theorem flagPsiX_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) : flagPsiX hK (flagPsiX hK x) = x := by
  have hψ := flagPsiX_mem hK hx
  have hx2 : x.E 2 = Vsub (K := K) 4 2 := by simpa using hx 1 (by decide)
  have hL : x.E 1 ≤ Vsub (K := K) 4 2 := by rw [← hx2]; exact x.mono (by norm_num)
  have hH : Vsub (K := K) 4 2 ≤ x.E 3 := by rw [← hx2]; exact x.mono (by norm_num)
  have h1 : (flagPsiX hK (flagPsiX hK x)).E 1 = x.E 1 := by
    rw [flagPsiX_E_one hK hψ, flagPsiX_E_three hK hx]
    exact q2cFX_jInv_image_phi hK hL
  have h3 : (flagPsiX hK (flagPsiX hK x)).E 3 = x.E 3 := by
    rw [flagPsiX_E_three hK hψ, flagPsiX_E_one hK hx]
    exact q2cFX_phi_jInv_image hK hH
  have h2 : (flagPsiX hK (flagPsiX hK x)).E 2 = x.E 2 := by
    have hψψ := flagPsiX_mem hK hψ
    rw [show (flagPsiX hK (flagPsiX hK x)).E 2 = Vsub (K := K) 4 2 from by
          simpa using hψψ 1 (by decide),
      show x.E 2 = Vsub (K := K) 4 2 from by simpa using hx 1 (by decide)]
  refine FlagK.ext_of_mid ?_
  intro j hj1 hj4
  interval_cases j
  exacts [h1, h2, h3]

@[expose] def flagPsiXMax (hK : Nat.card K = (2 ^ f) ^ 2) : Set (FlagK K 4) :=
  {x | x ∈ refSet K 4 [0, 2, 4] ∧ ∀ y ∈ refSet K 4 [0, 2, 4],
    (symCox 3).length (flagδ 3 y (flagPsiX hK y)) ≤ (symCox 3).length (flagδ 3 x (flagPsiX hK x))}

private theorem q2cFX_blocks_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (∀ b r, b + 1 < ([0, 2, 4] : List ℕ).length → r ≤ blockSize [0, 2, 4] b →
      x.E ([0, 2, 4].getD b 0 + r) ⊓ (flagPsiX hK x).E
          ([0, 2, 4].getD b 0 + (blockSize [0, 2, 4] b - r)) =
        Vsub 4 ([0, 2, 4].getD b 0)) ↔
      x.E 1 ⊓ q2cFX_JInv f (x.E 3) = ⊥ ∧ x.E 3 ⊓ q2cFX_Phi f (x.E 1) = Vsub (K := K) 4 2 := by
  have hψ := flagPsiX_mem hK hx
  have hx0 : x.E 0 = Vsub (K := K) 4 0 := by simpa using hx 0 (by decide)
  have hx2 : x.E 2 = Vsub (K := K) 4 2 := by simpa using hx 1 (by decide)
  have hx4 : x.E 4 = Vsub (K := K) 4 4 := by simpa using hx 2 (by decide)
  have hψ0 : (flagPsiX hK x).E 0 = Vsub (K := K) 4 0 := by simpa using hψ 0 (by decide)
  have hψ2 : (flagPsiX hK x).E 2 = Vsub (K := K) 4 2 := by simpa using hψ 1 (by decide)
  have hψ4 : (flagPsiX hK x).E 4 = Vsub (K := K) 4 4 := by simpa using hψ 2 (by decide)
  have hJ : (flagPsiX hK x).E 1 = q2cFX_JInv f (x.E 3) := flagPsiX_E_one hK hx
  have hP : (flagPsiX hK x).E 3 = q2cFX_Phi f (x.E 1) := flagPsiX_E_three hK hx
  constructor
  · intro h
    constructor
    · have hh := h 0 1 (by decide) (by decide)
      change x.E 1 ⊓ (flagPsiX hK x).E 1 = Vsub 4 0 at hh
      rw [hJ] at hh
      simpa [Vsub_zero] using hh
    · have hh := h 1 1 (by decide) (by decide)
      change x.E 3 ⊓ (flagPsiX hK x).E 3 = Vsub 4 2 at hh
      rw [hP] at hh
      simpa using hh
  · rintro ⟨hA, hB⟩ b r hb hr
    have hb' : b = 0 ∨ b = 1 := by
      have hb3 : b + 1 < 3 := by simpa using hb
      omega
    have hr2 : r ≤ 2 := by
      rcases hb' with rfl | rfl <;> simpa [blockSize] using hr
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hb' with rfl | rfl <;> rcases hr' with rfl | rfl | rfl <;>
      simp [blockSize, hx0, hx2, hx4, hψ0, hψ2, hψ4, hJ, hP, hA, hB, Vsub_zero, Vsub_self]

private theorem q2cFX_core (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    (x.E 1 ⊓ q2cFX_JInv f (x.E 3) = ⊥ ∧
      x.E 3 ⊓ q2cFX_Phi f (x.E 1) = Vsub (K := K) 4 2) ↔
      x.E 3 ≠ q2cFX_Phi f (x.E 1) := by
  have hx2 : x.E 2 = Vsub (K := K) 4 2 := by simpa using hx 1 (by decide)
  have hL : x.E 1 ≤ Vsub (K := K) 4 2 := by rw [← hx2]; exact x.mono (by norm_num)
  have hH : Vsub (K := K) 4 2 ≤ x.E 3 := by rw [← hx2]; exact x.mono (by norm_num)
  have hL1 : finrank K (x.E 1) = 1 := x.dim 1 (by norm_num)
  have hH3 : finrank K (x.E 3) = 3 := x.dim 3 (by norm_num)
  have hJ1 : finrank K (q2cFX_JInv f (x.E 3)) = 1 := q2cFX_finrank_JInv hK hH hH3
  have hP3 : finrank K (q2cFX_Phi f (x.E 1)) = 3 := q2cFX_finrank_Phi hK hL hL1
  have hAB : x.E 3 ≤ q2cFX_Phi f (x.E 1) ↔ q2cFX_JInv f (x.E 3) ≤ x.E 1 := by
    constructor
    · intro hle
      rw [q2cFX_JInv, Submodule.span_le]
      rintro v ⟨h, hh, rfl⟩
      exact (q2cFX_mem_sup_jShift_iff hK hL h).mp (hle hh)
    · intro hle h hh
      exact (q2cFX_mem_sup_jShift_iff hK hL h).mpr
        (hle (Submodule.subset_span ⟨h, hh, rfl⟩))
  constructor
  · rintro ⟨-, hB⟩ hHP
    have hHV2 : x.E 3 = Vsub (K := K) 4 2 := by
      rw [← hHP, inf_idem] at hB
      exact hB
    have := hH3
    rw [hHV2, finrank_Vsub (K := K) (n := 4) (by norm_num)] at this
    omega
  · intro hHP
    have hnotHP : ¬ x.E 3 ≤ q2cFX_Phi f (x.E 1) := fun hle =>
      hHP (Submodule.eq_of_le_of_finrank_eq hle (by rw [hH3, hP3]))
    have hnotJL : ¬ q2cFX_JInv f (x.E 3) ≤ x.E 1 := fun hle => hnotHP (hAB.mpr hle)
    constructor
    · rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨hvL, hvJ⟩ := Submodule.mem_inf.mp hv
      by_contra hv0
      apply hnotJL
      have hJspan : q2cFX_JInv f (x.E 3) = Submodule.span K {v} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hJ1 hvJ hv0
      rw [hJspan]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
    · have hleV : Vsub (K := K) 4 2 ≤ x.E 3 ⊓ q2cFX_Phi f (x.E 1) := le_inf hH le_sup_left
      let X : Submodule K (Fin 4 → K) := x.E 3 ⊓ q2cFX_Phi f (x.E 1)
      have hlt : finrank K X < finrank K (x.E 3) := by
        by_contra h
        rw [not_lt] at h
        have heq : X = x.E 3 := Submodule.eq_of_le_of_finrank_le inf_le_left h
        exact hnotHP (le_trans (le_of_eq heq.symm) inf_le_right)
      have hfin2 : finrank K X = 2 := by
        have h1 : 2 ≤ finrank K X := by
          have hmono := Submodule.finrank_mono hleV
          rwa [finrank_Vsub (K := K) (n := 4) (by norm_num)] at hmono
        have h2 := hlt
        rw [hH3] at h2
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hleV (by
        rw [finrank_Vsub (K := K) (n := 4) (by norm_num), hfin2])).symm

private theorem q2cFX_longest_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4}
    (hx : x ∈ refSet K 4 [0, 2, 4]) :
    flagδ 3 x (flagPsiX hK x) = longest (symCox 3) (cutTypes 3 [0, 2, 4]) ↔
      x.E 3 ≠ q2cFX_Phi f (x.E 1) := by
  rw [flagδ_eq_longest_cutTypes_iff isCut_22 hx (flagPsiX_mem hK hx),
    q2cFX_blocks_iff hK hx]
  exact q2cFX_core hK hx

theorem exists_opp_flagPsiX (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ z ∈ refSet K 4 [0, 2, 4],
      flagδ 3 z (flagPsiX hK z) = longest (symCox 3) (cutTypes 3 [0, 2, 4]) := by
  have hp1 : finrank K (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K))) = 1 :=
    finrank_span_singleton (v := q2cFX_e0 (K := K)) (by
      intro h; have := congrFun h 0; simp [q2cFX_e0] at this)
  have hp1' : finrank K (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K))) = 1 :=
    finrank_span_singleton (by
      intro h; have := congrFun h 1; simp [q2cFX_e1] at this)
  have hV2 : finrank K (Vsub (K := K) 4 2) = 2 := finrank_Vsub (K := K) (n := 4) (by norm_num)
  have hH3 : finrank K (q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)))) = 3 :=
    q2cFX_finrank_Phi hK (by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      intro j hj; fin_cases j <;> simp_all [q2cFX_e1]) hp1'
  have hle1 : (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) :
      Submodule K (Fin 4 → K)) ≤ Vsub (K := K) 4 2 :=
    q2cFX_e0_le_Vsub
  have hle2 : Vsub (K := K) 4 2 ≤
      q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K))) := le_sup_left
  set z : FlagK K 4 := FlagK.ofChain4 (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)))
    (Vsub (K := K) 4 2) (q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K))))
    hp1 hV2 hH3 hle1 hle2 with hz
  have hz1 : z.E 1 = Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K)) := by
    rw [hz]; exact FlagK.ofChain4_E_one _ _ _ _ _ _ _ _
  have hz2 : z.E 2 = Vsub (K := K) 4 2 := by
    rw [hz]; exact FlagK.ofChain4_E_two _ _ _ _ _ _ _ _
  have hz3 : z.E 3 = q2cFX_Phi f (Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K))) := by
    rw [hz]; exact FlagK.ofChain4_E_three _ _ _ _ _ _ _ _
  have hzR : z ∈ refSet K 4 [0, 2, 4] := by
    intro i hi
    have hi3 : i < 3 := by simpa using hi
    interval_cases i
    · change z.E 0 = Vsub (K := K) 4 0
      rw [FlagK.E_zero z, Vsub_zero]
    · exact hz2
    · change z.E 4 = Vsub (K := K) 4 4
      rw [z.top 4 (by norm_num), Vsub_self]
  have hψR := flagPsiX_mem hK hzR
  have hψ1 : (flagPsiX hK z).E 1 = Submodule.span K ({q2cFX_e1} : Set (Fin 4 → K)) := by
    rw [flagPsiX_E_one hK hzR, hz3]
    exact q2cFX_JInv_Phi_e1 hK
  have hψ2 : (flagPsiX hK z).E 2 = Vsub (K := K) 4 2 := by simpa using hψR 1 (by decide)
  have hψ3 : (flagPsiX hK z).E 3 =
      q2cFX_Phi f (Submodule.span K ({q2cFX_e0} : Set (Fin 4 → K))) := by
    rw [flagPsiX_E_three hK hzR, hz1]
    rfl
  refine ⟨z, hzR, ?_⟩
  rw [flagδ_eq_longest_cutTypes_iff isCut_22 hzR hψR]
  intro b r hb hr
  have hb' : b = 0 ∨ b = 1 := by
    have hb3 : b + 1 < 3 := by simpa using hb
    omega
  have hr2 : r ≤ 2 := by
    rcases hb' with rfl | rfl <;> simpa [blockSize] using hr
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hb' with rfl | rfl <;> rcases hr' with rfl | rfl | rfl <;>
    simp [blockSize, FlagK.E_zero z, z.top 4 (by norm_num),
      FlagK.E_zero (flagPsiX hK z), (flagPsiX hK z).top 4 (by norm_num),
      hz1, hz2, hz3, hψ1, hψ2, hψ3, q2cFX_inf_e0_e1, q2cFX_Phi_e1_inf_Phi_e0, Vsub_zero]

theorem mem_flagPsiXMax_iff (hK : Nat.card K = (2 ^ f) ^ 2) {x : FlagK K 4} :
    x ∈ flagPsiXMax hK ↔ x ∈ refSet K 4 [0, 2, 4] ∧
      x.E 3 ≠ Vsub 4 2 ⊔ Submodule.span K (jShift K f '' (x.E 1 : Set (Fin 4 → K))) := by
  haveI : Finite ((symCox 3).parabolic (cutTypes 3 [0, 2, 4])) := Subtype.finite
  have hmax : flagPsiXMax hK = {x | x ∈ refSet K 4 [0, 2, 4] ∧
      flagδ 3 x (flagPsiX hK x) = longest (symCox 3) (cutTypes 3 [0, 2, 4])} := by
    ext x
    constructor
    · rintro ⟨hxR, hxmax⟩
      obtain ⟨w, hwR, hwlong⟩ := exists_opp_flagPsiX hK
      have hpar : flagδ 3 x (flagPsiX hK x) ∈
          (symCox 3).parabolic (cutTypes 3 [0, 2, 4]) :=
        flagδ_mem_parabolic_of_mem_refSet isCut_22 hxR (flagPsiX_mem hK hxR)
      have hge : (symCox 3).length (longest (symCox 3) (cutTypes 3 [0, 2, 4])) ≤
          (symCox 3).length (flagδ 3 x (flagPsiX hK x)) := by
        have h := hxmax w hwR
        rwa [hwlong] at h
      have hle : (symCox 3).length (flagδ 3 x (flagPsiX hK x)) ≤
          (symCox 3).length (longest (symCox 3) (cutTypes 3 [0, 2, 4])) :=
        (isLongest_longest (cs := symCox 3) (cutTypes 3 [0, 2, 4])).2 _ hpar
      have hlen : (symCox 3).length (flagδ 3 x (flagPsiX hK x)) =
          (symCox 3).length (longest (symCox 3) (cutTypes 3 [0, 2, 4])) :=
        le_antisymm hle hge
      have hisLong : IsLongest (symCox 3) (cutTypes 3 [0, 2, 4])
          (flagδ 3 x (flagPsiX hK x)) :=
        ⟨hpar, fun v hv => by rw [hlen]; exact (isLongest_longest (cs := symCox 3) _).2 v hv⟩
      exact ⟨hxR, hisLong.unique (isLongest_longest (cs := symCox 3) _)⟩
    · rintro ⟨hxR, hxlong⟩
      refine ⟨hxR, fun y hy => ?_⟩
      rw [hxlong]
      exact (isLongest_longest (cs := symCox 3) (cutTypes 3 [0, 2, 4])).2 _
        (flagδ_mem_parabolic_of_mem_refSet isCut_22 hy (flagPsiX_mem hK hy))
  rw [hmax]
  exact ⟨fun h => ⟨h.1, (q2cFX_longest_iff hK h.1).mp h.2⟩,
    fun h => ⟨h.1, (q2cFX_longest_iff hK h.1).mpr h.2⟩⟩

theorem set22x_eq_flipSet (hK : Nat.card K = (2 ^ f) ^ 2) :
    set22x K f =
      {E | Gate.IsFar (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) Set.univ
          (stdFlag K 4) E ∧
        resProj (symCox 3) (flagδ (K := K) 3) (cutTypes 3 [0, 2, 4]) (stdFlag K 4) E ∈
          flagPsiXMax hK} := by
  have hstd : stdFlag K 4 ∈ refSet K 4 [0, 2, 4] := stdFlag_mem_refSet isCut_22
  ext E
  constructor
  · intro hE
    simp only [set22x, Set.mem_setOf_eq] at hE
    obtain ⟨hEfar, hEcond⟩ := hE
    refine ⟨(isFar_iff_mem_farSet isCut_22 hstd).mpr hEfar, ?_⟩
    rw [resProj_eq_gateFlag isCut_22 hEfar hstd, mem_flagPsiXMax_iff hK]
    refine ⟨gateFlag_mem_refSet isCut_22 hEfar, ?_⟩
    have hg1 : (gateFlag isCut_22 hEfar).E 1 = blockU K 4 [0, 2, 4] E.E 0 1 := by
      simpa using gateFlag_E isCut_22 hEfar (b := 0) (r := 1) (by decide) (by decide)
    have hg3 : (gateFlag isCut_22 hEfar).E 3 = blockU K 4 [0, 2, 4] E.E 1 1 := by
      simpa using gateFlag_E isCut_22 hEfar (b := 1) (r := 1) (by decide) (by decide)
    rw [hg3, hg1]
    exact hEcond
  · intro hE
    obtain ⟨hEfar, hEmax⟩ := hE
    have hfar : E ∈ farSet 4 [0, 2, 4] := (isFar_iff_mem_farSet isCut_22 hstd).mp hEfar
    simp only [set22x, Set.mem_setOf_eq]
    rw [resProj_eq_gateFlag isCut_22 hfar hstd, mem_flagPsiXMax_iff hK] at hEmax
    refine ⟨hfar, ?_⟩
    have hg1 : (gateFlag isCut_22 hfar).E 1 = blockU K 4 [0, 2, 4] E.E 0 1 := by
      simpa using gateFlag_E isCut_22 hfar (b := 0) (r := 1) (by decide) (by decide)
    have hg3 : (gateFlag isCut_22 hfar).E 3 = blockU K 4 [0, 2, 4] E.E 1 1 := by
      simpa using gateFlag_E isCut_22 hfar (b := 1) (r := 1) (by decide) (by decide)
    rw [hg3, hg1] at hEmax
    exact hEmax.2

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
