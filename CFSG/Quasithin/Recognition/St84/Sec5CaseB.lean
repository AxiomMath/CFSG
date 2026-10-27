module

public import CFSG.Quasithin.Recognition.St84.Sec5Step11
public import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2A
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Walter.Bender1970.S38.AbelianNormal

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem card_S_seven (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) : Nat.card Y.S = 2 ^ (3 * n₀ + 3) :=
  card_S_of_isMaxRegLen_six_sub Y H (isMaxRegLen_six Y H hZ) h7

private theorem card_Q1_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) : Nat.card (Y.Q 1) = 2 ^ (3 * n₀ + 2) := by
  have hS := card_S_seven Y H hZ h7
  have hQ1S : Y.Q 1 ≤ Y.S := by
    rw [← Y.edgeSylow_zero]
    exact Y.Q_le_edgeSylow_right 1
  have hrel := Y.relIndex_Q_succ_edgeSylow 0
  rw [Y.edgeSylow_zero] at hrel
  simp only [zero_add] at hrel
  rw [H.n_one] at hrel
  have hcard := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.S)
  rw [inf_eq_left.mpr hQ1S, hrel, hS] at hcard
  have hpow : 2 ^ (3 * n₀ + 3) = 2 * 2 ^ (3 * n₀ + 2) := by
    rw [show 3 * n₀ + 3 = (3 * n₀ + 2) + 1 by ring, pow_succ]
    ring
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hcard

private theorem card_Z_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Nat.card (Y.Z 0) = 2 :=
  (s52_step8 Y H hZ).2.2.2.2.2.2.1

private theorem card_Z1_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Nat.card (Y.Z 1) = 4 :=
  (s52_step8_Z Y H hZ 1 (by norm_num)).2

private theorem relIndex_Z_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) : (Y.Z 0).relIndex (Y.Q 0) = 2 ^ (2 * n₀ + 2) := by
  have hS := card_S_seven Y H hZ h7
  have hQ0S : Y.Q 0 ≤ Y.S := by
    rw [← Y.edgeSylow_zero]
    exact Y.Q_le_edgeSylow_left 0
  have hrelQ := Y.relIndex_Q_edgeSylow 0
  rw [Y.edgeSylow_zero] at hrelQ
  rw [H.n_zero] at hrelQ
  have hcardQ := Subgroup.relIndex_mul_card (H := Y.Q 0) (K := Y.S)
  rw [inf_eq_left.mpr hQ0S, hrelQ, hS] at hcardQ
  have hcardQ0 : Nat.card (Y.Q 0) = 2 ^ (2 * n₀ + 3) := by
    have h : 2 ^ n₀ * Nat.card (Y.Q 0) = 2 ^ n₀ * 2 ^ (2 * n₀ + 3) := by
      rw [hcardQ, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) n₀) h
  have hZleQ : Y.Z 0 ≤ Y.Q 0 := Y.Z_le_Q 0
  have hcard := Subgroup.relIndex_mul_card (H := Y.Z 0) (K := Y.Q 0)
  rw [inf_eq_left.mpr hZleQ, card_Z_eq Y H hZ, hcardQ0] at hcard
  have hpow : 2 ^ (2 * n₀ + 3) = 2 ^ (2 * n₀ + 2) * 2 := by
    rw [show 2 * n₀ + 3 = (2 * n₀ + 2) + 1 by ring, pow_succ]
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcard

private theorem card_A_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) : Nat.card ↥(Y.Q 0 ⊓ Y.Q 2) = 4 * 2 ^ n₀ := by
  have hQ1 := card_Q1_eq Y H hZ h7
  have hAleQ1 : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Q 1 := by
    simpa using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero
  have hrel := Y.relIndex_inf_Q H 1
  rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at hrel
  have hn2 : Y.n 2 = n₀ := by
    have h := Y.n_add 1 0
    rw [show (0 : ℤ) + 2 * 1 = 2 by ring] at h
    rw [h, H.n_zero]
  rw [hn2] at hrel
  have hcard := Subgroup.relIndex_mul_card (H := Y.Q 0 ⊓ Y.Q 2) (K := Y.Q 1)
  rw [inf_eq_left.mpr hAleQ1, hrel, hQ1] at hcard
  have hgoal : 2 ^ (2 * n₀) * (4 * 2 ^ n₀) = 2 ^ (3 * n₀ + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [← hgoal] at hcard
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) (2 * n₀)) hcard

private theorem card_D_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    Nat.card ↥(Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)) = 2 ^ n₀ := by
  let A := Y.Q 0 ⊓ Y.Q 2
  let D := A ⊓ Subgroup.centralizer ({d} : Set G)
  have hEq : A = D ⊔ Y.Z 1 := (s52_A_eq Y H hZ hd hd3).1
  have hinf : D ⊓ Y.Z 1 = ⊥ := (s52_A_eq Y H hZ hd hd3).2
  have hZ1le : Y.Z 1 ≤ A := by rw [hEq]; exact le_sup_right
  have hDle : D ≤ A := inf_le_left
  have habel : IsMulCommutative ↥A := (isElemAbelian_Q_zero_inf_Q_two Y H hZ).1
  haveI : IsMulCommutative ↥A := habel
  have hZ1normD : Y.Z 1 ≤ Subgroup.normalizer (D : Set G) :=
    hZ1le.trans (Subgroup.le_normalizer_of_normal_subgroupOf hDle)
  have hdisj : Disjoint D (Y.Z 1) := disjoint_iff.mpr hinf
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    D (Y.Z 1) hZ1normD hdisj
  rw [card_Z1_eq Y H hZ] at hcard
  have hcardA : Nat.card ↥(D ⊔ Y.Z 1) = 4 * 2 ^ n₀ := by
    rw [← hEq]
    exact card_A_eq Y H hZ h7
  rw [hcardA] at hcard
  change Nat.card ↥D = 2 ^ n₀
  have h' : Nat.card ↥D * 4 = 4 * 2 ^ n₀ := hcard.symm
  have h'' : Nat.card ↥D * 4 = 2 ^ n₀ * 4 := by rw [h']; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h''

private def cubicCore (Y : Setup Γ G) : Subgroup G :=
  pCoreOf 2 (Y.arcStab (-2) 4)

private theorem cubicCore_le_Q (Y : Setup Γ G) (i : ℤ) (h1 : -2 ≤ i - 1) (h2 : i + 1 ≤ 4) :
    cubicCore Y ≤ Y.Q i := by
  have hU2 : IsPGroup 2 (cubicCore Y) := pCoreOf_isPGroup' (Y.arcStab (-2) 4)
  have hUleArc : cubicCore Y ≤ Y.arcStab (-2) 4 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.arcStab (-2) 4)
  have hUG : cubicCore Y ≤ Y.Gi i :=
    hUleArc.trans (Y.arcStab_le_Gi_of_between (by omega) (by omega))
  have hfixL : ∀ y ∈ cubicCore Y, y • Y.vert (i - 1) = Y.vert (i - 1) := by
    intro y hy
    exact MulAction.mem_stabilizer_iff.mp
      (Y.arcStab_le_Gi_of_between h1 (by omega) (hUleArc hy))
  have hfixR : ∀ y ∈ cubicCore Y, y • Y.vert (i + 1) = Y.vert (i + 1) := by
    intro y hy
    exact MulAction.mem_stabilizer_iff.mp
      (Y.arcStab_le_Gi_of_between (by omega) h2 (hUleArc hy))
  have h := le_pCoreOf_of_isPGroup_fixes_two Y.hyp hU2 hUG
    (by simpa using (Y.adj (i - 1)).symm) (Y.adj i) (Y.vert_injective.ne (by omega))
    hfixL hfixR
  simpa [Setup.Q, Setup.Gi] using h

private theorem K_le_normalizer_cubicCore (Y : Setup Γ G) :
    Y.K ≤ Subgroup.normalizer (cubicCore Y : Set G) :=
  (Y.K_le_GT.trans (Y.GT_le_arcStab (-2) 4)).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.arcStab (-2) 4))

private theorem finite_cubicCore (Y : Setup Γ G) : Finite ↥(cubicCore Y) :=
  finite_of_le_stabilizer Y.hyp (H := cubicCore Y)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.arcStab (-2) 4)).trans
      (Y.arcStab_le_Gi_left (by norm_num)))

private theorem four_le_two_pow_n₀ (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    4 ≤ 2 ^ n₀ := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) H.two_le

private theorem card_cubicCore (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) : Nat.card (cubicCore Y) = 2 ^ n₀ := by
  have hreg : Y.RightTransAt (-2) 4 := by
    have h := (Y.trans_of_lt H.sing (-2) (k := 6) (by norm_num) (by omega)).2
    have h4 : (-2 : ℤ) + ((6 : ℕ) : ℤ) = 4 := by norm_num
    rwa [h4] at h
  have hn4 : Y.n 4 = n₀ := by
    have h := Y.n_add 2 0
    rw [show (0 : ℤ) + 2 * 2 = 4 by norm_num] at h
    rw [h, H.n_zero]
  have hGT : Y.arcStab (-2) 5 = Y.GT := by
    have h := hr.2 (-2) 7 (by norm_num)
    simpa using h
  have hrel := Y.relIndex_arcStab_succ (-2) 4 (by norm_num) hreg
  rw [show (4 : ℤ) + 1 = 5 by norm_num, hn4] at hrel
  have hcardA : Nat.card ↥(Y.arcStab (-2) 4) = 2 ^ n₀ * Nat.card Y.GT := by
    have h := Subgroup.relIndex_mul_card (H := Y.arcStab (-2) 5) (K := Y.arcStab (-2) 4)
    have hinf : Y.arcStab (-2) 5 ⊓ Y.arcStab (-2) 4 = Y.arcStab (-2) 5 :=
      inf_eq_left.mpr (Y.arcStab_anti le_rfl (by norm_num))
    rw [hinf, hrel, hGT] at h
    exact h.symm
  have hU2 : IsPGroup 2 (cubicCore Y) := pCoreOf_isPGroup' (Y.arcStab (-2) 4)
  have hKA : Y.K ≤ Y.arcStab (-2) 4 := Y.K_le_GT.trans (Y.GT_le_arcStab _ _)
  have hA : Y.arcStab (-2) 4 ≤ Y.Gi (-2) ⊓ Y.Gi (-1) := by
    refine le_inf ?_ ?_
    · exact Y.arcStab_le_Gi_left (by norm_num)
    · exact Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num)
  obtain ⟨-, hsup⟩ := Y.pCoreOf_eq_inf_edgeSylow (-2) hKA hA
  have hKU := K_le_normalizer_cubicCore Y
  have hdisj : Disjoint (cubicCore Y) Y.K := by
    rw [disjoint_iff, inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup (A := Y.K) (B := cubicCore Y) Y.odd_card_K hU2
  haveI hfinK : Finite ↥Y.K := finite_of_le_stabilizer Y.hyp (H := Y.K) (Y.K_le_Gi 0)
  haveI := finite_cubicCore Y
  have hcardUK := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (cubicCore Y) Y.K hKU hdisj
  have hsup' : Y.K ⊔ cubicCore Y = Y.arcStab (-2) 4 := hsup
  rw [sup_comm] at hcardUK
  rw [hsup'] at hcardUK
  rw [hcardA, Y.GT_eq_K_of_sec5Hyp H] at hcardUK
  have hpos : 0 < Nat.card Y.K := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos hcardUK).symm

private theorem cubicCore_inf_Gi_neg_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) : cubicCore Y ⊓ Y.Gi (-3) = ⊥ := by
  have hU2 : IsPGroup 2 (cubicCore Y) := pCoreOf_isPGroup' (Y.arcStab (-2) 4)
  have hGT : Y.arcStab (-3) 4 = Y.GT := by
    have h := hr.2 (-3) 7 (by norm_num)
    simpa using h
  have hle : cubicCore Y ⊓ Y.Gi (-3) ≤ Y.arcStab (-3) 4 := by
    rw [Y.arcStab_eq_inf (show (-3 : ℤ) ≤ 4 by norm_num)]
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.arcStab (-2) 4)).trans
        (Y.arcStab_le_Gi_right (by norm_num)))
  rw [hGT] at hle
  rw [Y.GT_eq_K_of_sec5Hyp H] at hle
  have h2 : IsPGroup 2 ↥(cubicCore Y ⊓ Y.Gi (-3)) := hU2.to_le inf_le_left
  have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.K)
    (B := cubicCore Y ⊓ Y.Gi (-3)) Y.odd_card_K h2
  rw [inf_comm] at hbot
  rwa [inf_eq_left.mpr hle] at hbot

private theorem cubicCore_inf_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) : cubicCore Y ⊓ Y.Q (-2) = ⊥ := by
  have hG3 := cubicCore_inf_Gi_neg_three Y H hr
  have hQle : Y.Q (-2) ≤ Y.Gi (-3) := fun x hx => (Y.Q_le_Gi_adj (-2) hx).1
  exact le_bot_iff.mp (le_trans (inf_le_inf le_rfl hQle) (le_of_eq hG3))

private theorem cubicCore_not_le_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) : ¬ cubicCore Y ≤ Y.Q (-2) := by
  intro h
  have hUbot : cubicCore Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxinf : x ∈ cubicCore Y ⊓ Y.Q (-2) := ⟨hx, h hx⟩
    rw [cubicCore_inf_Q Y H hr] at hxinf
    simpa using hxinf
  have hcard := card_cubicCore Y H hr h7
  rw [hUbot] at hcard
  simp only [Subgroup.card_bot] at hcard
  have h4 := four_le_two_pow_n₀ Y H
  omega

private theorem cubicCore_sup_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) :
    cubicCore Y ⊔ Y.Q (-2) = Y.edgeSylow (-2) := by
  have hU2 : IsPGroup 2 (cubicCore Y) := pCoreOf_isPGroup' (Y.arcStab (-2) 4)
  have hUleArc : cubicCore Y ≤ Y.arcStab (-2) 4 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.arcStab (-2) 4)
  have hUle : cubicCore Y ≤ Y.Gi (-2) := hUleArc.trans (Y.arcStab_le_Gi_left (by norm_num))
  have hKU := K_le_normalizer_cubicCore Y
  have hω : cubicCore Y ≤ Y.Gi (-1) :=
    hUleArc.trans (Y.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have h := (Y.gen_of_K_invariant H (j := -2) (by norm_num) hU2 hUle hKU
    (cubicCore_not_le_Q Y H hr h7) (by simpa using hω)).1
  simpa [Setup.edgeSylow] using h

private theorem cubicCore_orbit (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {u v : G}
    (hu : u ∈ cubicCore Y) (hv : v ∈ cubicCore Y) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ k ∈ Y.K, k * u * k⁻¹ = v := by
  have hU2 : IsPGroup 2 (cubicCore Y) := pCoreOf_isPGroup' (Y.arcStab (-2) 4)
  have hUleArc : cubicCore Y ≤ Y.arcStab (-2) 4 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.arcStab (-2) 4)
  have hKU := K_le_normalizer_cubicCore Y
  have hsupQ := cubicCore_sup_Q Y H hr h7
  have hinfQ := cubicCore_inf_Q Y H hr
  have huE : u ∈ Y.edgeSylow (-2) := by rw [← hsupQ]; exact Subgroup.mem_sup_left hu
  have hvE : v ∈ Y.edgeSylow (-2) := by rw [← hsupQ]; exact Subgroup.mem_sup_left hv
  have huQ : u ∉ Y.Q (-2) := by
    intro hmem
    have : u ∈ cubicCore Y ⊓ Y.Q (-2) := ⟨hu, hmem⟩
    rw [hinfQ] at this
    exact hu1 (by simpa using this)
  have hvQ : v ∉ Y.Q (-2) := by
    intro hmem
    have : v ∈ cubicCore Y ⊓ Y.Q (-2) := ⟨hv, hmem⟩
    rw [hinfQ] at this
    exact hv1 (by simpa using this)
  obtain ⟨k, hk, hkq⟩ := exists_conj_mem_Q_left Y (-2) huE hvE huQ hvQ
  refine ⟨k, hk.1, ?_⟩
  have hku : k * u * k⁻¹ ∈ cubicCore Y :=
    (Subgroup.mem_normalizer_iff.mp (hKU hk.1) u).mp hu
  have hmemU : k * u * k⁻¹ * v⁻¹ ∈ cubicCore Y :=
    (cubicCore Y).mul_mem hku ((cubicCore Y).inv_mem hv)
  have hmemQ : k * u * k⁻¹ * v⁻¹ ∈ Y.Q (-2) := hkq
  have hone : k * u * k⁻¹ * v⁻¹ = 1 := by
    have := Subgroup.mem_inf.mpr ⟨hmemU, hmemQ⟩
    rw [hinfQ] at this
    simpa using this
  calc k * u * k⁻¹ = (k * u * k⁻¹ * v⁻¹) * v := by group
    _ = v := by rw [hone, one_mul]

private theorem exists_ne_one_ne (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hUcard : Nat.card (cubicCore Y) = 2 ^ n₀) {x : G}
    (hx : x ∈ cubicCore Y) (hx1 : x ≠ 1) :
    ∃ w ∈ cubicCore Y, w ≠ 1 ∧ w ≠ x := by
  haveI := finite_cubicCore Y
  have h3 : 3 ≤ Nat.card (cubicCore Y) := by
    rw [hUcard]
    have := four_le_two_pow_n₀ Y H
    omega
  exact CFSG.Walter.exists_mem_ne_one_ne h3 x
private theorem cubicCore_inf_Z1 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hr : Y.IsMaxRegLen 6) (h7 : s = 7) :
    cubicCore Y ⊓ Y.Z 1 = ⊥ := by
  have hZt : Y.Zt 1 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.2.2
  have hZ1C : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) := by
    rw [Setup.Zt, Subgroup.commutator_eq_bot_iff_le_centralizer] at hZt
    exact hZt
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxU : x ∈ cubicCore Y := hx.1
  have hfix : ∀ k ∈ Y.K, k * x * k⁻¹ = x := by
    intro k hk
    have hcomm : x * k = k * x := (Subgroup.mem_centralizer_iff.mp (hZ1C hx.2) k hk).symm
    calc k * x * k⁻¹ = x * k * k⁻¹ := by rw [hcomm]
      _ = x := by group
  obtain ⟨w, hwU, hw1, hwx⟩ := exists_ne_one_ne Y H (card_cubicCore Y H hr h7) hxU hx1
  obtain ⟨k, hk, hkx⟩ := cubicCore_orbit Y H hr h7 hxU hwU hx1 hw1
  exact hwx (by rw [← hkx, hfix k hk])

private theorem A_eq_U_sup_Z1 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) :
    Y.Q 0 ⊓ Y.Q 2 = cubicCore Y ⊔ Y.Z 1 := by
  have hUcard := card_cubicCore Y H hr h7
  have hUleA : cubicCore Y ≤ Y.Q 0 ⊓ Y.Q 2 :=
    le_inf (cubicCore_le_Q Y 0 (by norm_num) (by norm_num))
      (cubicCore_le_Q Y 2 (by norm_num) (by norm_num))
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hd := Y.J_le_L 1 hdJ
  have hD := s52_A_eq Y H hZ hd hd3
  have hZ1leA : Y.Z 1 ≤ Y.Q 0 ⊓ Y.Q 2 := by
    rw [hD.1]
    exact le_sup_right
  have hinf : cubicCore Y ⊓ Y.Z 1 = ⊥ := cubicCore_inf_Z1 Y H hZ hr h7
  have habel : IsMulCommutative ↥(Y.Q 0 ⊓ Y.Q 2) := (isElemAbelian_Q_zero_inf_Q_two Y H hZ).1
  haveI : IsMulCommutative ↥(Y.Q 0 ⊓ Y.Q 2) := habel
  have hZ1normU : Y.Z 1 ≤ Subgroup.normalizer (cubicCore Y : Set G) :=
    hZ1leA.trans (Subgroup.le_normalizer_of_normal_subgroupOf hUleA)
  have hdisj : Disjoint (cubicCore Y) (Y.Z 1) := disjoint_iff.mpr hinf
  haveI := finite_cubicCore Y
  haveI hfinZ : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Z 1) (Y.Z_le_Gi 1)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (cubicCore Y) (Y.Z 1) hZ1normU hdisj
  have hcardA : Nat.card ↥(cubicCore Y ⊔ Y.Z 1) = 4 * 2 ^ n₀ := by
    rw [hcard, hUcard, card_Z1_eq Y H hZ]
    ring
  haveI hfinA : Finite ↥(Y.Q 0 ⊓ Y.Q 2) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0 ⊓ Y.Q 2)
      (inf_le_left.trans (Y.Q_le_Gi 0))
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hUleA hZ1leA) (by
    rw [hcardA, card_A_eq Y H hZ h7])).symm

private theorem K_le_normalizer_A (Y : Setup Γ G) :
    Y.K ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 2 : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub k (Y.Q 0 ⊓ Y.Q 2) = Y.Q 0 ⊓ Y.Q 2
  have h0 : conjSub k (Y.Q 0) = Y.Q 0 := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Y.K_le_Gi 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0)) hk)
  have h2 : conjSub k (Y.Q 2) = Y.Q 2 := by
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Y.K_le_Gi 2).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2)) hk)
  rw [conjSub_inf, h0, h2]

private theorem conj_mem_D_of_mem_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hdJ : d ∈ Y.J 1) : ∀ k ∈ Y.K,
      ∀ x ∈ Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G),
      k * x * k⁻¹ ∈ Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G) := by
  intro k hk x hx
  have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hkd : k * d = d * k := Subgroup.mem_centralizer_iff.mp (J_le_centralizer Y H hdJ) k hk
  have hkd' : k⁻¹ * d = d * k⁻¹ := by
    have h := congrArg (fun y => k⁻¹ * y * k⁻¹) hkd
    have h' : d * k⁻¹ = k⁻¹ * d := by simpa [mul_assoc] using h
    exact h'.symm
  refine ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (K_le_normalizer_A Y hk) x).mp hx.1
  · show k * x * k⁻¹ ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k * x * k⁻¹) * d = k * x * (k⁻¹ * d) := by group
      _ = k * x * (d * k⁻¹) := by rw [hkd']
      _ = k * (x * d) * k⁻¹ := by group
      _ = k * (d * x) * k⁻¹ := by rw [hxd]
      _ = (k * d) * x * k⁻¹ := by group
      _ = (d * k) * x * k⁻¹ := by rw [hkd]
      _ = d * (k * x * k⁻¹) := by group

private theorem D_le_cubicCore (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) :
    Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G) ≤ cubicCore Y := by
  set A : Subgroup G := Y.Q 0 ⊓ Y.Q 2 with hAdef
  set D : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hDdef
  set U : Subgroup G := cubicCore Y with hUdef
  have hAsupD : A = D ⊔ Y.Z 1 := (s52_A_eq Y H hZ hd hd3).1
  have hDinf : D ⊓ Y.Z 1 = ⊥ := (s52_A_eq Y H hZ hd hd3).2
  have hAsupU : A = U ⊔ Y.Z 1 := A_eq_U_sup_Z1 Y H hZ hr h7
  have hUleA : U ≤ A := by rw [hAsupU]; exact le_sup_left
  have hDleA : D ≤ A := by rw [hAsupD]; exact le_sup_left
  have hZ1leA : Y.Z 1 ≤ A := by rw [hAsupU]; exact le_sup_right
  have hUcard := card_cubicCore Y H hr h7
  have hZ1C : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) := by
    have hZt : Y.Zt 1 = ⊥ := (s52_step8 Y H hZ).2.2.2.2.2.2.2
    rw [Setup.Zt, Subgroup.commutator_eq_bot_iff_le_centralizer] at hZt
    exact hZt
  have hzsq : ∀ z ∈ Y.Z 1, z * z = 1 := by
    intro z hz
    have h2 : IsElemAbelian 2 (Y.Z 1) := (s52_step8_Z Y H hZ 1 (by norm_num)).1
    have := h2.2 z hz
    simpa [pow_two] using this
  show D ≤ U
  intro x hxD
  have hxA : x ∈ A := hDleA hxD
  rw [hAsupU] at hxA
  haveI : IsMulCommutative ↥A := (isElemAbelian_Q_zero_inf_Q_two Y H hZ).1
  have hcommA : ∀ a ∈ U, ∀ b ∈ Y.Z 1, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, hUleA ha⟩ : ↥A)
      (⟨b, hZ1leA hb⟩ : ↥A))
  obtain ⟨u, hu, z, hz, hxuz⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommA hxA
  by_cases hu1 : u = 1
  · have hxZ : x ∈ Y.Z 1 := by
      rw [← hxuz, hu1, one_mul]
      exact hz
    have hxbot : x ∈ D ⊓ Y.Z 1 := ⟨hxD, hxZ⟩
    rw [hDinf] at hxbot
    rw [Subgroup.mem_bot] at hxbot
    rw [hxbot]
    exact U.one_mem
  · have hkz : ∀ k ∈ Y.K, k * z * k⁻¹ = z := by
      intro k hk
      have hcomm : z * k = k * z := (Subgroup.mem_centralizer_iff.mp (hZ1C hz) k hk).symm
      calc k * z * k⁻¹ = z * k * k⁻¹ := by rw [hcomm]
        _ = z := by group
    obtain ⟨w, hwU, hw1, hwx⟩ := exists_ne_one_ne Y H hUcard (x := u) hu hu1
    have hzu : ∀ y ∈ U, y ≠ 1 → y * z ∈ D := by
      intro y hy hy1
      obtain ⟨k, hk, hky⟩ := cubicCore_orbit Y H hr h7 hu hy hu1 hy1
      have hxDk : k * x * k⁻¹ ∈ D := conj_mem_D_of_mem_K Y H hdJ k hk x hxD
      have hkx : k * x * k⁻¹ = y * z := by
        rw [← hxuz]
        calc k * (u * z) * k⁻¹ = (k * u * k⁻¹) * (k * z * k⁻¹) := by group
          _ = y * z := by rw [hky, hkz k hk]
      rwa [hkx] at hxDk
    have hzw : z * w = w * z :=
      congrArg Subtype.val (mul_comm' (⟨z, hZ1leA hz⟩ : ↥A)
        (⟨w, hUleA hwU⟩ : ↥A))
    have hu2 : u * u = 1 := by
      have h2 : IsElemAbelian 2 (Y.Q 0 ⊓ Y.Q 2) := isElemAbelian_Q_zero_inf_Q_two Y H hZ
      simpa [pow_two] using h2.2 u (hUleA hu)
    have huw1 : u * w ≠ 1 := by
      intro h
      apply hwx
      calc w = 1 * w := by rw [one_mul]
        _ = (u * u) * w := by rw [hu2, one_mul]
        _ = u * (u * w) := by group
        _ = u * 1 := by rw [h]
        _ = u := mul_one u
    have hzsq' : z * z = 1 := hzsq z hz
    have hwzD : w * z ∈ D := hzu w hwU hw1
    have huwD : u * w ∈ D := by
      have h1 : x * (w * z) ∈ D := D.mul_mem hxD hwzD
      have h2 : x * (w * z) = u * w := by
        rw [← hxuz]
        calc (u * z) * (w * z) = u * (z * w) * z := by group
          _ = u * (w * z) * z := by rw [hzw]
          _ = u * w * (z * z) := by group
          _ = u * w := by rw [hzsq', mul_one]
      rwa [h2] at h1
    have huwzD : (u * w) * z ∈ D := hzu (u * w) (U.mul_mem hu hwU) huw1
    have hzD : z ∈ D := by
      have hmem : (u * w)⁻¹ * ((u * w) * z) ∈ D :=
        D.mul_mem (D.inv_mem huwD) huwzD
      simpa [mul_assoc] using hmem
    have hzbot : z ∈ D ⊓ Y.Z 1 := ⟨hzD, hz⟩
    rw [hDinf] at hzbot
    have hz1 : z = 1 := by simpa using hzbot
    rw [← hxuz, hz1, mul_one]
    exact hu

private theorem D_eq_cubicCore (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) :
    Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G) = cubicCore Y := by
  haveI := finite_cubicCore Y
  exact Subgroup.eq_of_le_of_card_ge (D_le_cubicCore Y H hZ hr h7 hd hdJ hd3)
    (by rw [card_cubicCore Y H hr h7, card_D_eq Y H hZ h7 hd hd3])

private theorem Q_one_le_L_zero (Y : Setup Γ G) : Y.Q 1 ≤ Y.L 0 := by
  have hQS : Y.Q 1 ≤ Y.S := by
    rw [← Y.edgeSylow_zero]
    exact Y.Q_le_edgeSylow_right 1
  exact hQS.trans (by simpa [Y.edgeSylow_zero] using Y.edgeSylow_le_L 0)

private theorem L_one_le_normalizer_comm_A (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    Y.L 1 ≤ Subgroup.normalizer
      ((⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), (Y.Q 1 : Subgroup G)⁆ : Subgroup G) : Set G) := by
  have hA := (s52_A_normal Y H hZ).1
  have hQ : Y.L 1 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (Y.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  intro l hl
  exact CFSG.Quasithin.H13.Sec526.commutator_mem_normalizer (hA hl) (hQ hl)

private theorem Z1_irreducible (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {W : Subgroup G} (hW : W ≤ Y.Z 1)
    (hWinv : Y.L 1 ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = Y.Z 1 := by
  rcases eq_or_ne W ⊥ with hbot | hne
  · exact Or.inl hbot
  by_cases htop : W = Y.Z 1
  · exact Or.inr htop
  exfalso
  have hcardZ : Nat.card (Y.Z 1) = 4 := card_Z1_eq Y H hZ
  haveI hfinZ : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Z 1) (Y.Z_le_Gi 1)
  haveI hfinW : Finite ↥W :=
    Finite.of_injective (Subgroup.inclusion hW) (Subgroup.inclusion_injective hW)
  have hdvdW : Nat.card ↥W ∣ 4 := by
    rw [← hcardZ]
    exact Subgroup.card_dvd_of_le hW
  have hne4 : Nat.card ↥W ≠ 4 := by
    intro h4
    refine htop (Subgroup.eq_of_le_of_card_ge hW ?_)
    rw [hcardZ, h4]
  have hWltcard : Nat.card ↥W < 4 := by
    rcases Nat.lt_or_ge (Nat.card ↥W) 4 with h | h
    · exact h
    · exact absurd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvdW) h) hne4
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcardW : Nat.card ↥W = 2 := by
    have hgt : 1 < Nat.card ↥W := by
      haveI : Nontrivial ↥W := W.nontrivial_iff_ne_bot.mpr hne
      exact Finite.one_lt_card
    have hcases : Nat.card ↥W = 2 ∨ Nat.card ↥W = 3 := by omega
    rcases hcases with h2 | h3
    · exact h2
    · exfalso
      have h34 : 3 ∣ 4 := by rw [← h3]; exact hdvdW
      omega
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hd := Y.J_le_L 1 hdJ
  have hcent := Z_one_inf_centralizer_eq_bot Y H hZ hd hd3
  have hdW : d ∈ Subgroup.normalizer (W : Set G) := hWinv hd
  have hwWd : d * (w : G) * d⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hdW (w : G)).mp w.2
  obtain ⟨u, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp hcardW
  have h1 : (w : ↥W) ≠ 1 := hw1
  have h2 : (⟨d * (w : G) * d⁻¹, hwWd⟩ : ↥W) ≠ 1 := by
    intro h
    apply hw1
    have hcoe : d * (w : G) * d⁻¹ = 1 := congrArg Subtype.val h
    have h3 := congrArg (fun y => d⁻¹ * y * d) hcoe
    simpa [mul_assoc] using h3
  have heq : w = (⟨d * (w : G) * d⁻¹, hwWd⟩ : ↥W) :=
    (huniq _ h1).trans (huniq _ h2).symm
  have hfix : d * (w : G) * d⁻¹ = (w : G) := (congrArg Subtype.val heq).symm
  have hdw : d * (w : G) = (w : G) * d := by
    have h := congrArg (fun y => y * d) hfix
    simpa [mul_assoc] using h
  have hcen : (w : G) ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hdw.symm
  have hmem : (w : G) ∈ Y.Z 1 ⊓ Subgroup.centralizer ({d} : Set G) := ⟨hW w.2, hcen⟩
  rw [hcent] at hmem
  exact hw1 (by simpa using hmem)

private theorem comm_A_Q_one_eq_Z1 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h7 : s = 7) :
    ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), (Y.Q 1 : Subgroup G)⁆ = Y.Z 1 := by
  have hle : ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), (Y.Q 1 : Subgroup G)⁆ ≤ Y.Z 1 := by
    rw [Subgroup.commutator_comm]
    exact commutator_Q_one_inf_le_Z_one Y H hZ
  have hAleQ1 : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Q 1 := by
    simpa using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero
  have hne : ⁅(Y.Q 0 ⊓ Y.Q 2 : Subgroup G), (Y.Q 1 : Subgroup G)⁆ ≠ ⊥ := by
    intro hbot
    have hAcomm : Y.Q 0 ⊓ Y.Q 2 ≤ Subgroup.centralizer (Y.Q 1 : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := Y.Q 0 ⊓ Y.Q 2) (H₂ := Y.Q 1)).mp hbot
    have hcenA := centerOf_Q_one_inf_eq_Z_one Y H hZ
    have hAleZ : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Z 1 := by
      intro x hx
      have hxQ : x ∈ Y.Q 1 := hAleQ1 hx
      have hxC : x ∈ Subgroup.centralizer (Y.Q 1 : Set G) := hAcomm hx
      have hxcen : x ∈ centerOf (Y.Q 1) := Subgroup.mem_inf.mpr ⟨hxQ, hxC⟩
      rw [← hcenA]
      exact ⟨hxcen, hx⟩
    haveI : Finite ↥(Y.Z 1) :=
      finite_of_le_stabilizer Y.hyp (H := Y.Z 1) (Y.Z_le_Gi 1)
    have hAZ : Nat.card ↥(Y.Q 0 ⊓ Y.Q 2) ≤ Nat.card ↥(Y.Z 1) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hAleZ)
        (Subgroup.inclusion_injective hAleZ)
    rw [card_A_eq Y H hZ h7, card_Z1_eq Y H hZ] at hAZ
    have h4 := four_le_two_pow_n₀ Y H
    omega
  rcases Z1_irreducible Y H hZ hle (L_one_le_normalizer_comm_A Y H hZ) with hbot | htop
  · exact absurd hbot hne
  · exact htop

private theorem comm_D_Q_one_eq_Z1 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ⁅(Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)), (Y.Q 1 : Subgroup G)⁆ =
      Y.Z 1 := by
  set A : Subgroup G := Y.Q 0 ⊓ Y.Q 2 with hAdef
  set D : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hDdef
  have hAsup : A = D ⊔ Y.Z 1 := (s52_A_eq Y H hZ hd hd3).1
  have hDleA : D ≤ A := by rw [hAsup]; exact le_sup_left
  have hZ1leA : Y.Z 1 ≤ A := by rw [hAsup]; exact le_sup_right
  have hAZ := comm_A_Q_one_eq_Z1 Y H hZ h7
  have habel : IsMulCommutative ↥A := (isElemAbelian_Q_zero_inf_Q_two Y H hZ).1
  haveI : IsMulCommutative ↥A := habel
  have hcommA : ∀ x ∈ D, ∀ z ∈ Y.Z 1, x * z = z * x := by
    intro x hx z hz
    exact congrArg Subtype.val (mul_comm' (⟨x, hDleA hx⟩ : ↥A) (⟨z, hZ1leA hz⟩ : ↥A))
  have hge : ⁅A, (Y.Q 1 : Subgroup G)⁆ ≤ ⁅D, (Y.Q 1 : Subgroup G)⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha q hq
    obtain ⟨x, hx, z, hz, hxz⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommA (hAsup ▸ ha)
    have hzq : ⁅z, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      have hzc : z ∈ Subgroup.centralizer (Y.Q 1 : Set G) :=
        (Subgroup.mem_inf.mp ((Y.Z_le_center 1) hz)).2
      exact (Subgroup.mem_centralizer_iff.mp hzc q hq).symm
    have hEq : ⁅a, q⁆ = ⁅x, q⁆ := by
      rw [← hxz, commutatorElement_mul_left_eq_conj_mul, hzq, mul_one]
      group
    rw [hEq]
    exact Subgroup.commutator_mem_commutator hx hq
  have hle : ⁅D, (Y.Q 1 : Subgroup G)⁆ ≤ ⁅A, (Y.Q 1 : Subgroup G)⁆ :=
    Subgroup.commutator_mono hDleA le_rfl
  have hEq : ⁅D, (Y.Q 1 : Subgroup G)⁆ = ⁅A, (Y.Q 1 : Subgroup G)⁆ :=
    le_antisymm hle hge
  rw [hEq, hAZ]

private theorem cubicCore_comm_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) :
    ⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ = cubicCore Y := by
  have hKU := K_le_normalizer_cubicCore Y
  have hle : ⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ ≤ cubicCore Y :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKU
  have hKinv : Y.K ≤
      Subgroup.normalizer
        ((⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right (cubicCore Y) Y.K
  have hirr : ∀ W : Subgroup G, W ≤ cubicCore Y →
      Y.K ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = cubicCore Y := by
    intro W hW hWinv
    rcases eq_or_ne W ⊥ with hbot | hne
    · exact Or.inl hbot
    right
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hyU : (y : G) ∈ cubicCore Y := hW y.2
    refine le_antisymm hW ?_
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact W.one_mem
    · have hzU : z ∈ cubicCore Y := hz
      obtain ⟨k, hk, hky⟩ := cubicCore_orbit Y H hr h7 hyU hzU
        (fun h => hy1 (Subtype.ext h)) hz1
      rw [← hky]
      exact (Subgroup.mem_normalizer_iff.mp (hWinv hk) (y : G)).mp y.2
  have hne : ⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ ≠ ⊥ := by
    intro hbot
    have hcent : cubicCore Y ≤ Subgroup.centralizer (Y.K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := cubicCore Y) (H₂ := Y.K)).mp hbot
    have hUcard := card_cubicCore Y H hr h7
    have hUne : cubicCore Y ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hUcard
      have h4 := four_le_two_pow_n₀ Y H
      omega
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hxU : (x : G) ∈ cubicCore Y := x.2
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨v, hvU, hv1, hvx⟩ := exists_ne_one_ne Y H hUcard hxU hx1'
    obtain ⟨k, hk, hkx⟩ := cubicCore_orbit Y H hr h7 hxU hvU hx1' hv1
    have hfix : k * (x : G) * k⁻¹ = (x : G) := by
      have hc : (x : G) * k = k * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp (hcent hxU) k hk).symm
      calc k * (x : G) * k⁻¹ = (x : G) * k * k⁻¹ := by rw [hc]
        _ = (x : G) := by group
    rw [hfix] at hkx
    exact hvx hkx.symm
  rcases hirr ⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ hle hKinv with hbot | htop
  · exact absurd hbot hne
  · exact htop

private theorem eq_Q_zero_of_D_inf_ne_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) {N : Subgroup G}
    (hNinv : Y.L 0 ≤ Subgroup.normalizer (N : Set G)) (hNQ : N ≤ Y.Q 0)
    (hDne : (Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ N ≠ ⊥) :
    N = Y.Q 0 := by
  set A : Subgroup G := Y.Q 0 ⊓ Y.Q 2 with hAdef
  set D : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hDdef
  have hD_eq : D = cubicCore Y := D_eq_cubicCore Y H hZ hr h7 hd hdJ hd3
  have hDleN : D ≤ N := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have hxDN : (x : G) ∈ D ⊓ N := x.2
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxD : (x : G) ∈ D := hxDN.1
    have hxN : (x : G) ∈ N := hxDN.2
    have hxU : (x : G) ∈ cubicCore Y := by rw [← hD_eq]; exact hxD
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact N.one_mem
    · have hyU : y ∈ cubicCore Y := by rw [← hD_eq]; exact hy
      obtain ⟨k, hk, hkx⟩ := cubicCore_orbit Y H hr h7 hxU hyU hx1' hy1
      rw [← hkx]
      exact (Subgroup.mem_normalizer_iff.mp (hNinv (Y.K_le_L_zero H hk)) x).mp hxN
  have hZ1leN : Y.Z 1 ≤ N := by
    rw [← comm_D_Q_one_eq_Z1 Y H hZ h7 hd hd3]
    exact (Subgroup.commutator_mono hDleN le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Q_one_le_L_zero Y).trans hNinv))
  have hVleN : Y.VNbr0 ≤ N := by
    rw [Setup.VNbr0]
    refine iSup_le fun g => ?_
    refine iSup_le fun hg => ?_
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]
    exact (Subgroup.mem_normalizer_iff.mp (hNinv hg) z).mp (hZ1leN hz)
  have hQeq : Y.Q 0 = D ⊔ Y.VNbr0 :=
    (s52_step10 Y H hZ (Y.J_le_L 1 hdJ) hd3).2.2.2.2.1
  refine le_antisymm hNQ ?_
  rw [hQeq]
  exact sup_le hDleN hVleN

private theorem L_zero_le_normalizer_Q_zero (Y : Setup Γ G) :
    Y.L 0 ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
  (Y.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))

private theorem comm_Q_zero_L_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G}
    (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ = Y.Q 0 := by
  set A : Subgroup G := Y.Q 0 ⊓ Y.Q 2 with hAdef
  set D : Subgroup G := A ⊓ Subgroup.centralizer ({d} : Set G) with hDdef
  have hD_eq : D = cubicCore Y := D_eq_cubicCore Y H hZ hr h7 hd hdJ hd3
  have hDcomm : ⁅(cubicCore Y : Subgroup G), (Y.K : Subgroup G)⁆ = cubicCore Y :=
    cubicCore_comm_K Y H hr h7
  have hDle : D ≤ ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ := by
    rw [hD_eq, ← hDcomm]
    exact Subgroup.commutator_mono (cubicCore_le_Q Y 0 (by norm_num) (by norm_num))
      (Y.K_le_L_zero H)
  have hQnorm := L_zero_le_normalizer_Q_zero Y
  have hQLinv : Y.L 0 ≤
      Subgroup.normalizer
        ((⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right (Y.Q 0) (Y.L 0)
  have hZ0norm : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) :=
    (Y.L_le_Gi 0).trans (Y.Gi_le_normalizer_Z 0)
  have hQLconj : ∀ l ∈ Y.L 0,
      conjSub l ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ =
        ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ := by
    intro l hl
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQLinv hl)
  have hZ0conj : ∀ l ∈ Y.L 0, conjSub l (Y.Z 0) = Y.Z 0 := by
    intro l hl
    simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZ0norm hl)
  have hNinv : Y.L 0 ≤
      Subgroup.normalizer
        ((⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0 : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjSub l (⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0) =
      ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0
    rw [conjSub_sup, hQLconj l hl, hZ0conj l hl]
  have hNleQ : ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0 ≤ Y.Q 0 :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hQnorm) (Y.Z_le_Q 0)
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hc := card_D_eq Y H hZ h7 hd hd3
    change Nat.card ↥D = 2 ^ n₀ at hc
    rw [hbot, Subgroup.card_bot] at hc
    have h4 := four_le_two_pow_n₀ Y H
    omega
  have hDneN : D ⊓ (⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0) ≠ ⊥ := by
    rwa [inf_eq_left.mpr (hDle.trans le_sup_left)]
  have hN := eq_Q_zero_of_D_inf_ne_bot Y H hZ hr h7 hd hdJ hd3 hNinv hNleQ hDneN
  have hZle : Y.Z 0 ≤ ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ := by
    have hQQ : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := commutator_Q_zero_eq_Z_zero Y H hZ
    rw [← hQQ]
    exact Subgroup.commutator_mono le_rfl (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le
  have hsup : ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ⊔ Y.Z 0 =
      ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ := sup_eq_left.mpr hZle
  rw [hsup] at hN
  exact hN

private theorem L_zero_perfect (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) : ⁅Y.L 0, Y.L 0⁆ = Y.L 0 := by
  refine CFSG.Quasithin.F112R.perfect_of_isL2Quot (G := G) (L := Y.L 0) (f := n₀)
    H.two_le (isL2Quot_L_zero Y H) ?_
  have hO2 : pCoreOf 2 (Y.L 0) = Y.Q 0 :=
    (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).pCoreOf_eq
  rw [hO2, ← comm_Q_zero_L_zero Y H hZ hr h7 hd hdJ hd3]
  exact Subgroup.commutator_mono (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le le_rfl

private theorem isL2Quot_oTwoQuot_top {L : Subgroup G} {n : ℕ}
    (h : IsL2Quot n (oTwoQuot ↥L)) : IsL2Quot n (oTwoQuot ↥(⊤ : Subgroup ↥L)) := by
  obtain ⟨e⟩ := h
  exact ⟨(CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv
    (Subgroup.topEquiv (G := ↥L))).trans e⟩

private theorem commutator_le_of_isL2Quot_finite (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1)
    (hdJ : d ∈ Y.J 1) (hd3 : orderOf d = 3) {N W : Subgroup G} (hNL : N ≤ Y.L 0)
    (hWL : W ≤ Y.L 0) (hLN : Y.L 0 ≤ Subgroup.normalizer (N : Set G))
    (hLW : Y.L 0 ≤ Subgroup.normalizer (W : Set G)) (hWN : W ≤ N) (f : ℕ)
    (hfm : f < 2 * n₀) (hcard : Nat.card N = 2 ^ f * Nat.card W) :
    ⁅N, Y.L 0⁆ ≤ W := by
  let Hgrp := ↥(Y.L 0)
  let N' : Subgroup Hgrp := N.subgroupOf (Y.L 0)
  let W' : Subgroup Hgrp := W.subgroupOf (Y.L 0)
  haveI hTop : Group.IsPerfect ↥(⊤ : Subgroup Hgrp) := by
    haveI : Group.IsPerfect Hgrp :=
      Subgroup.isPerfect_iff.mpr (L_zero_perfect Y H hZ hr h7 hd hdJ hd3)
    exact Group.IsPerfect.top_iff.mpr inferInstance
  have hquot' : IsL2Quot n₀ (oTwoQuot ↥(⊤ : Subgroup Hgrp)) :=
    isL2Quot_oTwoQuot_top (L := Y.L 0) (isL2Quot_L_zero Y H)
  have hLN' : (⊤ : Subgroup Hgrp) ≤ Subgroup.normalizer (N' : Set Hgrp) := by
    haveI : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
    exact Subgroup.le_normalizer_of_normal
  have hLW' : (⊤ : Subgroup Hgrp) ≤ Subgroup.normalizer (W' : Set Hgrp) := by
    haveI : W'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLW
    exact Subgroup.le_normalizer_of_normal
  have hWN' : W' ≤ N' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hWN hx
  have hWn' : (W'.subgroupOf N').Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (fun x _ => hLW' (Subgroup.mem_top (x : Hgrp)))
  have hcardN' : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
  have hcardW' : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
  have hcard' : Nat.card N' = 2 ^ f * Nat.card W' := by
    rw [hcardN', hcardW']
    exact hcard
  haveI hfinH : Finite Hgrp :=
    finite_of_le_stabilizer Y.hyp (H := Y.L 0) (Y.L_le_Gi 0)
  haveI := hWn'
  have hle' := CFSG.Quasithin.H13.Sec526.commutator_le_of_isL2Quot
    (G := Hgrp) (L := ⊤) (N := N') (W := W') (n := n₀) (f := f)
    H.two_le hfm hTop hquot' hLN' hLW' hWN' hcard'
  rw [Subgroup.commutator_le]
  intro n hn l hl
  have hm1 : (⟨n, hNL hn⟩ : Hgrp) ∈ N' := by
    rw [Subgroup.mem_subgroupOf]
    exact hn
  have hm2 : (⟨l, hl⟩ : Hgrp) ∈ (⊤ : Subgroup Hgrp) := Subgroup.mem_top _
  have hmem' : ⁅(⟨n, hNL hn⟩ : Hgrp), (⟨l, hl⟩ : Hgrp)⁆ ∈ W' :=
    (Subgroup.commutator_le.mp hle') _ hm1 _ hm2
  rw [Subgroup.mem_subgroupOf] at hmem'
  have hmem'' : ((Y.L 0).subtype ⁅(⟨n, hNL hn⟩ : Hgrp), (⟨l, hl⟩ : Hgrp)⁆ : G) ∈ W := hmem'
  have hEq : ((Y.L 0).subtype ⁅(⟨n, hNL hn⟩ : Hgrp), (⟨l, hl⟩ : Hgrp)⁆ : G) = ⁅n, l⁆ := by
    rw [map_commutatorElement]
    rfl
  rw [hEq] at hmem''
  exact hmem''

private theorem not_commutator_le_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hperf : ⁅Y.L 0, Y.L 0⁆ = Y.L 0) {W : Subgroup G}
    (hZW : Y.Z 0 ≤ W) (hWQ : W ≤ Y.Q 0) (hne : W ≠ Y.Z 0) :
    ¬ ⁅W, Y.L 0⁆ ≤ Y.Z 0 := by
  intro hle
  have hNil : ⁅⁅W, Y.L 0⁆, Y.L 0⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅W, Y.L 0⁆, Y.L 0⁆ ≤ ⁅Y.Z 0, Y.L 0⁆ :=
          Subgroup.commutator_mono hle le_rfl
      _ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          have hZc : Y.Z 0 = centerOf (Y.L 0) := (s52_step8 Y H hZ).1
          rw [hZc]
          exact inf_le_right
  have hbot : ⁅W, Y.L 0⁆ = ⊥ :=
    CFSG.Quasithin.H13.Sec526.commutator_eq_bot_of_perfect hperf hNil
  have hWleC : W ≤ Subgroup.centralizer (Y.L 0 : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := W) (H₂ := Y.L 0)).mp hbot
  have hWleZ : W ≤ Y.Z 0 := by
    have hZc : Y.Z 0 = centerOf (Y.L 0) := (s52_step8 Y H hZ).1
    intro w hw
    rw [hZc]
    exact ⟨(Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le (hWQ hw), hWleC hw⟩
  exact hne (le_antisymm hWleZ hZW)

private theorem irred_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) :
    ∀ W : Subgroup G, Y.Z 0 ≤ W → W ≤ Y.Q 0 →
      Y.L 0 ≤ Subgroup.normalizer (W : Set G) → W = Y.Z 0 ∨ W = Y.Q 0 := by
  intro W hZW hWQ hWinv
  rcases eq_or_ne W (Y.Z 0) with h | hne
  · exact Or.inl h
  right
  have hperf := L_zero_perfect Y H hZ hr h7 hd hdJ hd3
  have hcomm := comm_Q_zero_L_zero Y H hZ hr h7 hd hdJ hd3
  have hquotcard := relIndex_Z_Q Y H hZ h7
  have hLN := L_zero_le_normalizer_Q_zero Y
  have hLZ : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) :=
    (Y.L_le_Gi 0).trans (Y.Gi_le_normalizer_Z 0)
  have hntW := not_commutator_le_Z_zero Y H hZ hperf hZW hWQ hne
  have hW2 : IsPGroup 2 W :=
    (pCoreOf_isPGroup' (Y.Gi 0)).to_le hWQ
  haveI hfinW : Finite ↥W := by
    have hWleGi : W ≤ Y.Gi 0 := hWQ.trans (Y.Q_le_Gi 0)
    exact finite_of_le_stabilizer Y.hyp (H := W) hWleGi
  obtain ⟨f, hf⟩ : ∃ f, (Y.Z 0).relIndex W = 2 ^ f :=
    hW2.index ((Y.Z 0).subgroupOf W)
  have hfge : 2 * n₀ ≤ f := by
    by_contra hflt
    push Not at hflt
    have hcardW : Nat.card W = 2 ^ f * Nat.card (Y.Z 0) := by
      have h := Subgroup.relIndex_mul_card (H := Y.Z 0) (K := W)
      rw [inf_eq_left.mpr hZW, hf] at h
      simpa using h.symm
    have hle := commutator_le_of_isL2Quot_finite Y H hZ hr h7 hd hdJ hd3
      (N := W) (W := Y.Z 0) (hWQ.trans (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le)
      (Y.Z_le_Q 0 |>.trans (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le)
      hWinv hLZ hZW f hflt hcardW
    exact hntW hle
  by_contra hWne
  have hQ2 : IsPGroup 2 (Y.Q 0) := pCoreOf_isPGroup' (Y.Gi 0)
  haveI hfinQ2 : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  obtain ⟨e, he⟩ : ∃ e, W.relIndex (Y.Q 0) = 2 ^ e :=
    hQ2.index (W.subgroupOf (Y.Q 0))
  have hege : 2 * n₀ ≤ e := by
    by_contra helt
    push Not at helt
    have hcardQ : Nat.card (Y.Q 0) = 2 ^ e * Nat.card W := by
      have h := Subgroup.relIndex_mul_card (H := W) (K := Y.Q 0)
      rw [inf_eq_left.mpr hWQ, he] at h
      simpa using h.symm
    have hle := commutator_le_of_isL2Quot_finite Y H hZ hr h7 hd hdJ hd3
      (N := Y.Q 0) (W := W) (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le
      (hWQ.trans (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le)
      hLN hWinv hWQ e helt hcardQ
    rw [hcomm] at hle
    exact hWne (le_antisymm hWQ hle)
  have hrelmul := Subgroup.relIndex_mul_relIndex (Y.Z 0) W (Y.Q 0) hZW hWQ
  rw [hquotcard, hf, he] at hrelmul
  have h1 : 2 ^ (2 * n₀) * 2 ^ (2 * n₀) ≤ 2 ^ (2 * n₀ + 2) := by
    rw [← hrelmul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hfge)
      (Nat.pow_le_pow_right (by norm_num) hege)
  have h2 : 2 ^ (2 * n₀) * 2 ^ (2 * n₀) = 2 ^ (4 * n₀) := by
    rw [← pow_add]
    congr 1
    ring
  rw [h2] at h1
  have h3 : 4 * n₀ ≤ 2 * n₀ + 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h2le : 2 ≤ n₀ := H.two_le
  omega

private theorem nontriv_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hr : Y.IsMaxRegLen 6) (h7 : s = 7) {d : G} (hd : d ∈ Y.L 1) (hdJ : d ∈ Y.J 1)
    (hd3 : orderOf d = 3) :
    ∃ l ∈ Y.L 0, ∃ v ∈ Y.Q 0, ⁅l, v⁆ ∉ Y.Z 0 := by
  by_contra h
  push Not at h
  have hle : ⁅(Y.Q 0 : Subgroup G), (Y.L 0 : Subgroup G)⁆ ≤ Y.Z 0 := by
    rw [Subgroup.commutator_le]
    intro q hq l hl
    have hmem : ⁅l, q⁆ ∈ Y.Z 0 := h l hl q hq
    have hEq : ⁅q, l⁆ = ⁅l, q⁆⁻¹ := (commutatorElement_inv (g₁ := l) (g₂ := q)).symm
    rw [hEq]
    exact (Y.Z 0).inv_mem hmem
  rw [comm_Q_zero_L_zero Y H hZ hr h7 hd hdJ hd3] at hle
  have hcard := relIndex_Z_Q Y H hZ h7
  rw [Subgroup.relIndex_eq_one.mpr hle] at hcard
  have h4 : 4 ≤ 2 ^ (2 * n₀ + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n₀ + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem isElemSec_subgroupOf {H Z V : Subgroup G} (h : IsElemSec Z V) :
    IsElemSec (Z.subgroupOf H) (V.subgroupOf H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact h.1 hx
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy ⊢
    change (H.subtype ⁅x, y⁆ : G) ∈ Z
    rw [map_commutatorElement]
    exact Subgroup.commutator_le.mp h.2.1 (x : G) hx (y : G) hy
  · intro e he
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have hmem : (e : G) ^ 2 ∈ Z := h.2.2 (e : G) he
    change ((e : G) ^ 2) ∈ Z
    exact hmem

private theorem irred_subgroupOf {L V Z : Subgroup G} (hZL : Z ≤ L) (hVL : V ≤ L)
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V) :
    ∀ W' : Subgroup ↥L, Z.subgroupOf L ≤ W' → W' ≤ V.subgroupOf L →
      (⊤ : Subgroup ↥L) ≤ Subgroup.normalizer (W' : Set ↥L) →
      W' = Z.subgroupOf L ∨ W' = V.subgroupOf L := by
  intro W' hZW' hWV' hWinv
  have hinj : Function.Injective (Subgroup.map L.subtype) :=
    Subgroup.map_injective Subtype.coe_injective
  have hZmap : (Z.subgroupOf L).map L.subtype = Z :=
    Subgroup.map_subgroupOf_eq_of_le hZL
  have hVmap : (V.subgroupOf L).map L.subtype = V :=
    Subgroup.map_subgroupOf_eq_of_le hVL
  have hZleW : Z ≤ W'.map L.subtype := by
    rw [← hZmap]
    exact Subgroup.map_mono hZW'
  have hWleV : W'.map L.subtype ≤ V := by
    rw [← hVmap]
    exact Subgroup.map_mono hWV'
  have hWnorm : L ≤ Subgroup.normalizer (W'.map L.subtype : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro l hl y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hy
    have hl' : (⟨l, hl⟩ : ↥L) ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top _
    have hconj : (⟨l, hl⟩ : ↥L) * x' * (⟨l, hl⟩ : ↥L)⁻¹ ∈ W' :=
      (Subgroup.mem_normalizer_iff.mp (hWinv hl') x').mp hx'
    exact Subgroup.mem_map.mpr ⟨_, hconj, rfl⟩
  rcases hirr (W'.map L.subtype) hZleW hWleV hWnorm with h | h
  · left
    apply hinj
    rw [h, hZmap]
  · right
    apply hinj
    rw [h, hVmap]

private theorem nontriv_subgroupOf {L V Z : Subgroup G} (hVL : V ≤ L)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z) :
    ∃ l' ∈ (⊤ : Subgroup ↥L), ∃ v' ∈ V.subgroupOf L, ⁅l', v'⁆ ∉ Z.subgroupOf L := by
  obtain ⟨l, hl, v, hv, hne⟩ := hnt
  have hvL : v ∈ L := hVL hv
  refine ⟨(⟨l, hl⟩ : ↥L), Subgroup.mem_top _, (⟨v, hvL⟩ : ↥L), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hv
  · intro hmem
    apply hne
    rw [Subgroup.mem_subgroupOf] at hmem
    have hEq : ((↑⁅(⟨l, hl⟩ : ↥L), (⟨v, hvL⟩ : ↥L)⁆) : G) = ⁅l, v⁆ := by
      change (L.subtype ⁅(⟨l, hl⟩ : ↥L), (⟨v, hvL⟩ : ↥L)⁆ : G) = ⁅l, v⁆
      rw [map_commutatorElement]
      rfl
    rwa [hEq] at hmem

private theorem n_eq_three_of_fields (Y : Setup Γ G) (h2 : 2 ≤ n₀)
    (hquot : IsL2Quot n₀ (oTwoQuot ↥(Y.L 0))) (hsec : IsElemSec (Y.Z 0) (Y.Q 0))
    (hZ0norm : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G))
    (hcard : (Y.Z 0).relIndex (Y.Q 0) = 2 ^ (2 * n₀ + 2))
    (hirr : ∀ W : Subgroup G, Y.Z 0 ≤ W → W ≤ Y.Q 0 →
      Y.L 0 ≤ Subgroup.normalizer (W : Set G) → W = Y.Z 0 ∨ W = Y.Q 0)
    (hnt : ∃ l ∈ Y.L 0, ∃ v ∈ Y.Q 0, ⁅l, v⁆ ∉ Y.Z 0) : n₀ = 3 := by
  let Lgrp := ↥(Y.L 0)
  let V' : Subgroup Lgrp := (Y.Q 0).subgroupOf (Y.L 0)
  let Z' : Subgroup Lgrp := (Y.Z 0).subgroupOf (Y.L 0)
  have hQL : Y.Q 0 ≤ Y.L 0 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le
  have hZL : Y.Z 0 ≤ Y.L 0 := (Y.Z_le_Q 0).trans hQL
  have hquot' : IsL2Quot n₀ (oTwoQuot ↥(⊤ : Subgroup Lgrp)) :=
    isL2Quot_oTwoQuot_top (L := Y.L 0) hquot
  have hVZ : Z' ≤ V' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Y.Z_le_Q 0 hx
  have hsec' : IsElemSec Z' V' := isElemSec_subgroupOf hsec
  have hL' : (⊤ : Subgroup Lgrp) ≤
      Subgroup.normalizer (V' : Set Lgrp) ⊓ Subgroup.normalizer (Z' : Set Lgrp) := by
    refine le_inf ?_ ?_
    · haveI : V'.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (L_zero_le_normalizer_Q_zero Y)
      exact Subgroup.le_normalizer_of_normal
    · haveI : Z'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hZ0norm
      exact Subgroup.le_normalizer_of_normal
  have hirr' := irred_subgroupOf (L := Y.L 0) (V := Y.Q 0) (Z := Y.Z 0) hZL hQL hirr
  have hnt' := nontriv_subgroupOf (L := Y.L 0) (V := Y.Q 0) (Z := Y.Z 0) hQL hnt
  have hcard' : Z'.relIndex V' = 2 ^ (2 * n₀ + 2) := by
    rw [Subgroup.relIndex_subgroupOf (H := Y.Z 0) (K := Y.Q 0) (L := Y.L 0) hQL]
    exact hcard
  haveI : Finite Lgrp := finite_of_le_stabilizer Y.hyp (H := Y.L 0) (Y.L_le_Gi 0)
  exact CFSG.Quasithin.St84.eq_three_of_irreducible_of_relIndex h2 hquot' hVZ hsec' hL'
    hirr' hnt' hcard'

private theorem natSec_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    NatSec (Y.L 1) ⊥ (Y.Z 1) := by
  intro x hxL hx3 e heZ hcomm
  rw [Subgroup.mem_bot] at hcomm ⊢
  have hmem : e ∈ Y.Z 1 ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨heZ, Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hcomm)⟩
  rw [Z_one_inf_centralizer_eq_bot Y H hZ hxL hx3] at hmem
  simpa using hmem

private theorem Z1_field (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Nat.card (Y.Z 1) = 4 ∧ NatSec (Y.L 1) ⊥ (Y.Z 1) :=
  ⟨card_Z1_eq Y H hZ, natSec_Z_one Y H hZ⟩

theorem treeD4_of_caseB (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (h7 : s = 7) : Y.TreeD4Data n₀ := by
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hdL : d ∈ Y.L 1 := Y.J_le_L 1 hdJ
  have hr : Y.IsMaxRegLen 6 := isMaxRegLen_six Y H hZ
  have hS : Nat.card Y.S = 2 ^ (3 * n₀ + 3) := card_S_seven Y H hZ h7
  have hquot : IsL2Quot n₀ (oTwoQuot ↥(Y.L 0)) := isL2Quot_L_zero Y H
  have hsec : IsElemSec (Y.Z 0) (Y.Q 0) := isElemSec_Z_zero_Q_zero Y H hZ
  have hcardq : (Y.Z 0).relIndex (Y.Q 0) = 2 ^ (2 * n₀ + 2) := relIndex_Z_Q Y H hZ h7
  have hirr := irred_Q Y H hZ hr h7 hdL hdJ hd3
  have hnt := nontriv_Q Y H hZ hr h7 hdL hdJ hd3
  have hcenter : centerOf (Y.Q 0) = Y.Z 0 := by
    rcases n_le_three_of_card_S Y H hZ hS with h2 | ⟨h3, hV⟩
    · subst h2
      have heq := n_eq_three_of_fields Y (by norm_num) hquot hsec
        ((Y.L_le_Gi 0).trans (Y.Gi_le_normalizer_Z 0)) hcardq hirr hnt
      omega
    · subst h3
      exact centerOf_Q_zero_of_VNbr0_eq Y H hZ hV
  exact ⟨hquot, hS, card_Z_eq Y H hZ, hcenter, hsec, hcardq, hirr, hnt,
    card_Q1_eq Y H hZ h7, Z1_field Y H hZ⟩

theorem TreeD4Data.n_eq_three {Y : Setup Γ G} (h2 : 2 ≤ n₀) (d : Y.TreeD4Data n₀) :
    n₀ = 3 := by
  have hZ0norm : Y.L 0 ≤ Subgroup.normalizer (Y.Z 0 : Set G) :=
    (Y.L_le_Gi 0).trans (Y.Gi_le_normalizer_Z 0)
  exact n_eq_three_of_fields Y h2 d.quot d.sec hZ0norm d.card_quot d.irred d.nontriv

theorem TreeD4Data.false_of_two {Y : Setup Γ G} (d : Y.TreeD4Data 2) : False := by
  have h := TreeD4Data.n_eq_three (Y := Y) (n₀ := 2) (by norm_num) d
  omega

end Setup

end CFSG.Quasithin.St84
