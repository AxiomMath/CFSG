module

public import CFSG.Quasithin.H13.L32AC33b
public import CFSG.Quasithin.H13.L32AC32d
public import CFSG.Quasithin.H13.L32AL2Ic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem iI_le_normalizer_vI (T L V : Subgroup G) (z z' : G) :
    iI T L V z z' ≤ Subgroup.normalizer (vI T L V z z' : Set G) :=
  le_normalizer_conjClosure _ _

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem pCoreOf_l1_le_T (h1332 : Stmt13_3_2) : pCoreOf 2 (l1 T L V) ≤ T := by
  have hTN := Setting147.T_le_N_l1 D.S h1332
  have h1 : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 _) (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _)))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo D.S.hyp.fsu.sylow le_sup_right))

theorem isQuotientOfSQTKTC_autOn (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    IsQuotientOfSQTKTC ↥(autOn (iI T L V z z') (vI T L V z z')) := by
  have hS := D.sqtk_iI h1222 h1332 h1334
  exact ⟨↥(iI T L V z z'), inferInstance, inferInstance, fun p hp hp2 => hS.1 p hp hp2, hS.2,
    InternalSec.autOnHom (iI_le_normalizer_vI T L V z z'),
    InternalSec.autOnHom_surjective (iI_le_normalizer_vI T L V z z')⟩

theorem isSylowTwoOf_autOn_T :
    IsSylowTwoOf (autOn T (vI T L V z z')) (autOn (iI T L V z z') (vI T L V z z')) :=
  Setup.isSylowTwoOf_autOn D.isSylowTwoOf_T (iI_le_normalizer_vI T L V z z')

theorem false_of_le_normalizer (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (hN : autOn (iI T L V z z') (vI T L V z z') ≤
      Subgroup.normalizer (autOn (l1 T L V) (vI T L V z z') : Set (MulAut ↥(vI T L V z z')))) :
    False := by
  obtain ⟨-, -, hred⟩ := D.vI_spec h1222 h1332 h1334
  have hIW := iI_le_normalizer_vI T L V z z'
  set W := vI T L V z z' with hW
  set Λ := autOn (l1 T L V) W with hΛ
  set Qp := autOn (pCoreOf 2 (l1 T L V)) W with hQp
  have hΛI : Λ ≤ autOn (iI T L V z z') W := InternalSec.autOn_le_autOn_of_le l1_le_iI
  have hQΛ : Qp ≤ Λ := InternalSec.autOn_le_autOn_of_le (pCoreOf_le 2 _)
  have hΛQ : Λ ≤ Subgroup.normalizer (Qp : Set (MulAut ↥W)) :=
    le_normalizer_of_conj (InternalSec.autOn_normal_of (le_normalizer_pCoreOf 2 _))
  have hQ2 : IsPGroup 2 Qp :=
    D.isSylowTwoOf_autOn_T.2.1.to_le (InternalSec.autOn_le_autOn_of_le (D.pCoreOf_l1_le_T h1332))
  have h1 : Qp ≤ pCoreOf 2 Λ := le_pCoreOf_of_le_normalizer 2 hQΛ hΛQ hQ2
  have h2 : pCoreOf 2 Λ ≤ pCoreOf 2 (autOn (iI T L V z z') W) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Λ).trans hΛI)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 Λ)) (pCoreOf_isPGroup 2 Λ)
  rw [Setup.pCoreOf_autOn_eq_bot hred] at h2
  have hQC : pCoreOf 2 (l1 T L V) ≤ Subgroup.centralizer (W : Set G) := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (W : Set G) := hIW (l1_le_iI (pCoreOf_le 2 _ hq))
    have h3 := (h1.trans h2) (A1b.conjAct_mem_autOn hqN hq)
    rw [Subgroup.mem_bot] at h3
    exact A1b.conjAct_eq_one_iff.mp h3
  exact D.hL1 ((hQC.trans (D.centralizer_vI_le.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _))

omit D [Finite G] in
theorem l1_eq_L₁Of : l1 T L V = L₁Of L (fsuV1 T V) := (oTwoRes_eq_oTwoUpper _).symm

theorem l1_le_sup (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {x' : G}
    (hx'L : x' ∈ l1 T L V) (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) :
    l1 T L V ≤ pCoreOf 2 (l1 T L V) ⊔ Subgroup.zpowers x' := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  have hLp3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 := by
    rw [l1_eq_L₁Of]
    exact S14.Lp3
  set P := pCoreOf 2 (l1 T L V) with hP
  have hle : P ⊔ Subgroup.zpowers x' ≤ l1 T L V :=
    sup_le (pCoreOf_le 2 _) (Subgroup.zpowers_le.mpr hx'L)
  have hmul := Subgroup.relIndex_mul_relIndex P (P ⊔ Subgroup.zpowers x') (l1 T L V)
    le_sup_left hle
  rw [hLp3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h | h
  · exfalso
    have hx : x' ∈ P := Subgroup.relIndex_eq_one.mp h
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (l1 T L V)) ⟨x', hx⟩
    have hk' : x' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact hx'1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hx'3) (orderOf_dvd_of_pow_eq_one hk')))
  · rw [h] at hmul
    have h1 : (P ⊔ Subgroup.zpowers x').relIndex (l1 T L V) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1

theorem l1_le_closure (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    l1 T L V ≤ Subgroup.closure {x | x ∈ l1 T L V ∧ orderOf x = 3} := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14 h1222 h1332 h1334
  rw [l1_eq_L₁Of]
  refine C.l1_le_of_cube S14 fun y hyL hy3 => ?_
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  · exact Subgroup.subset_closure ⟨hyL, orderOf_eq_prime hy3 hy1⟩

theorem pow_three_of_odd {y : G} (hy : y ∈ a114Y z z') (ho : Odd (orderOf y)) : y ^ 3 = 1 := by
  obtain ⟨hYN, -, hker, -⟩ := a114_one D.hA
  have hyN : y ∈ Subgroup.normalizer (vY T V z' : Set G) := hYN hy
  set φ := conjAct (vY T V z') ⟨y, hyN⟩ with hφ
  have h6 : φ ^ 6 = 1 := by
    have h1 := orderOf_dvd_natCard φ
    rw [D.hA.card_mulAut] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hy6 : y ^ 6 ∈ a114Y z z' ⊓ Subgroup.centralizer (vY T V z' : Set G) := by
    refine ⟨pow_mem hy 6, ?_⟩
    have h1 : conjAct (vY T V z') (⟨y, hyN⟩ ^ 6) = 1 := by rw [map_pow, ← hφ, h6]
    simpa using A1b.conjAct_eq_one_iff.mp h1
  rw [hker] at hy6
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (a114Y z z')) ⟨y ^ 6, hy6⟩
  have hk' : y ^ (6 * 2 ^ k) = 1 := by
    rw [pow_mul]
    simpa using congrArg Subtype.val hk
  have hcop2 : Nat.Coprime (orderOf y) 2 := Nat.coprime_two_right.mpr ho
  have h1 : orderOf y ∣ 6 * 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 6 := (Nat.Coprime.pow_right k hcop2).dvd_of_dvd_mul_right h1
  have h3 : orderOf y ∣ 3 := hcop2.dvd_of_dvd_mul_left (by simpa using h2)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem exists_commute (h1332 : Stmt13_3_2) {y : G} (hy : y ∈ a114Y z z') (hy3 : y ^ 3 = 1) :
    ∃ x' ∈ l1 T L V, x' ^ 3 = 1 ∧ x' ≠ 1 ∧ y * x' = x' * y := by
  obtain ⟨x, hxY, -, hx3, -⟩ := D.exists_x
  have h3 : 3 ∣ Nat.card ↥(lY T L V z') := by
    have := orderOf_dvd_natCard (⟨x, hxY⟩ : ↥(lY T L V z'))
    rwa [Subgroup.orderOf_mk, hx3] at this
  obtain ⟨ω, hω, hω3, hω1, hyω⟩ :=
    C.exists_comm_of_normalizes h3 (D.a114Y_le_normalizer_lY h1332 hy) hy3
  exact ⟨ω, lY_le_l1 hω, hω3, hω1, hyω⟩

end IData

end CFSG.Quasithin.H13.L32A.L2
