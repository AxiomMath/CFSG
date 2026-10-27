module

public import CFSG.Quasithin.Vol2.Ch12Sec4Post
public import CFSG.Quasithin.Vol2.Ch12Sec4Orbit
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Quasithin.Vol2.Ch12Sec4Mod
public import CFSG.Quasithin.Vol2.Ch12Sec4Pre

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure CxFacts (G : Type) [Group G] (T L V : Subgroup G) (z : G) : Prop where
  comm : IsMulCommutative ↥V
  sq : ∀ v ∈ V, v ^ 2 = 1
  normalizes : L ≤ Subgroup.normalizer (V : Set G)
  commutator : ⁅V, L⁆ = V
  pCore : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)
  notCent : ¬ L ≤ Subgroup.centralizer (V : Set G)
  le_T : V ≤ T
  T_le : T ≤ Subgroup.normalizer (V : Set G)
  order : orderOf z = 2
  zV : V ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers z
  MC : Subgroup.normalizer (L : Set G) = Subgroup.centralizer ({z} : Set G)
  MN : Subgroup.normalizer (L : Set G) = Subgroup.normalizer (V : Set G)

theorem CxFacts.of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) [Finite G]
    {T L V : Subgroup G} (hcx : Cx1242 G T L V)
    (hq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    ∃ z : G, CxFacts G T L V z := by
  have hyp := hcx.hyp
  obtain ⟨z, hz2, hzeq, hMz, hMV⟩ := post1244_core h331 h1222 hpre hcx hq
  obtain ⟨hc, -⟩ := modules_cases_of_hyp1223 h1222 hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  refine ⟨z, hc, hsq, hyp.irrPlus.2.2.1, hcomm,
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred, fun h => ?_, hVT, hTV,
    hz2, hzeq, hMz, hMV⟩
  apply hV1
  rw [← hcomm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)

namespace CxFacts

variable {T L V : Subgroup G} {z : G}

theorem mem_zV (hf : CxFacts G T L V z) : z ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
  hf.zV ▸ Subgroup.mem_zpowers z

theorem card_zV (hf : CxFacts G T L V z) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  rw [hf.zV, Nat.card_zpowers, hf.order]

theorem ne_one (hf : CxFacts G T L V z) : z ≠ 1 := fun h => by
  have := hf.order
  rw [h, orderOf_one] at this
  norm_num at this

theorem le_centralizer (hf : CxFacts G T L V z) : V ≤ Subgroup.centralizer (V : Set G) := by
  have := hf.comm
  exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)

theorem isElemAbelian (hf : CxFacts G T L V z) : IsElemAbelian 2 V := ⟨hf.comm, hf.sq⟩

theorem eq_of_mem_zV (hf : CxFacts G T L V z) {v : G}
    (hv : v ∈ V ⊓ Subgroup.centralizer (L : Set G)) (hv1 : v ≠ 1) : v = z :=
  eq_of_mem_of_card_eq_two hf.card_zV hv hf.mem_zV hv1 hf.ne_one

theorem T_le_centralizer (hf : CxFacts G T L V z) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.centralizer ({z} : Set G) :=
  hf.MC ▸ hTL

end CxFacts

theorem cx_l3_module (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G} {z : G}
    [IsMulCommutative ↥V] (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (h3 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nat.card V = 2 ^ 4 ∧ IsSimpleGroup (autOn L V) ∧ Nat.card (autOn L V) = 168 ∧
      BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1 := by
  have hyp := hcx.hyp
  obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
  obtain ⟨e⟩ := h3
  have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
    exact e.isSimpleGroup
  have h168 := card_quot_of_sl_three ⟨e⟩
  obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hf.normalizes hf.pCore hs3 hf.notCent
  have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
  have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hf.le_T
  have hZ2 := hf.card_zV
  have hV16 : Nat.card V = 2 ^ 4 := by
    have hle := hcases.1 ⟨e⟩
    have hidx := four_lt_relIndex_of_simple hf.normalizes hf.commutator hf.notCent hf.pCore hs3
      (by rw [h168]; norm_num)
    have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
    rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
    have h2 := E3.relIndex_eq_two_pow hVp (V ⊓ Subgroup.centralizer (L : Set G))
    rw [h2] at hidx h1
    have hm : 3 ≤ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) := by
      by_contra hm
      push Not at hm
      interval_cases (E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G))) <;> norm_num at hidx
    have h8 : 8 ≤ 2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hm
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hle ⊢
    omega
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hf.normalizes, card_subgroupOf_eq_card_inf, hZ2]
  exact ⟨hV16, hGrs, hGr, binaryNaturalSL_of_card_sixteen
    (fun w : ↥V => Subtype.ext (by simpa using hf.sq w w.2)) hV16 hGrs hGr
    (commV_autOn_eq_top hf.normalizes hf.commutator) hfixGr⟩

theorem cx_g2_module
    (h1222 : Stmt12_2_2) [Finite G] {T L V : Subgroup G} {z : G}
    [IsMulCommutative ↥V] (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z)
    (hU : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) :
    IsSimpleGroup (autOn L V) ∧ G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
  obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223 h1222 hcx.hyp
  have hsU : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
  obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hf.normalizes hf.pCore hsU hf.notCent
  refine ⟨eA.isSimpleGroup, ?_⟩
  rw [fixV_autOn_eq hf.normalizes]
  exact hcases.2.1 hU

end CFSG.Quasithin.H13
