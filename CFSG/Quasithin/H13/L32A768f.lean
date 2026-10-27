module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Quasithin.H13.L32A767n
public import CFSG.Quasithin.H13.L32A768b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem hz_eq_centralizer_singleton {z : G} (hzV1 : z ∈ fsuV1 T V)
    (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) :
    hz T V = Subgroup.centralizer ({z} : Set G) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg z hzV1).symm
  · intro hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
    rcases hgen c hc with rfl | rfl
    · simp
    · exact hg.symm

omit [Finite G] in
theorem oTwoUpper_inf_hz_eq {I : Subgroup G} (hKI : kz T V ≤ I) :
    oTwoUpper (I ⊓ hz T V) = kz T V := by
  refine le_antisymm (oTwoUpper_mono inf_le_right) ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hxH, hodd⟩
  exact mem_oTwoUpper_of_odd ⟨hKI (mem_oTwoUpper_of_odd hxH hodd), hxH⟩ hodd

theorem not_le_hz_of_ne {I : Subgroup G} (hKI : kz T V ≤ I) (hne : I ≠ kz T V)
    (hIp : ⁅I, I⁆ = I) : ¬ I ≤ hz T V := fun hle =>
  hne (le_antisymm (B1Red.perfect_le_oTwoUpper' hle (Subgroup.isPerfect_iff.mpr hIp)) hKI)

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem fsuU_le_pCoreOf_kz : fsuU T V ≤ pCoreOf 2 (kz T V) := by
  have hVK := v_le_kz C.hyp C.hMod C.h1222 C.h1332 C.h1334
  have hUK : fsuU T V ≤ kz T V := by
    rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
    exact conjClosure_le fun k hk v hv =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hk) v).mp (hVK hv)
  refine le_pCoreOf_of_le_normalizer 2 hUK
    (fun k hk => C.H_le_normalizer_U (oTwoUpper_le _ hk)) ?_
  exact fun u => ⟨1, Subtype.ext (by simpa using C.hUe u u.2)⟩

theorem inf_centralizer_eq_bot {I : Subgroup G} (hKI : kz T V ≤ I) (hIH : ¬ I ≤ hz T V) :
    V ⊓ Subgroup.centralizer (I : Set G) = ⊥ := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨z, hzV1, -, hgen⟩ := exists_gen_of_card_two hV1
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hvU0 : v ∈ u0 T V := (mem_u0_iff C.hyp C.hMod).mpr ⟨hVU hvV, fun k hk => by
    rw [Subgroup.mem_centralizer_iff.mp hvC k (hKI hk), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _⟩
  have hvV1 : v ∈ fsuV1 T V := by
    rw [← inf_u0_eq C.hyp C.hMod C.h63 C.hF]
    exact Subgroup.mem_inf.mpr ⟨hvV, hvU0⟩
  rcases hgen v hvV1 with rfl | rfl
  · exact one_mem _
  · exfalso
    apply hIH
    rw [hz_eq_centralizer_singleton hzV1 hgen]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hvC x hx

theorem comm_mem_zpowers {z : G} (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) {e w : G}
    (he : e ∈ V) (hw : w ∈ pCoreOf 2 (kz T V)) :
    e * w * e⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
  have h1 := C.comm_Q (pCoreOf_kz_le hw) ((le_conjClosure V _ : V ≤ fsuU T V) he)
  have h2 : e * w * e⁻¹ * w⁻¹ ∈ fsuV1 T V := by
    have := inv_mem h1
    rwa [show (w * e * w⁻¹ * e⁻¹)⁻¹ = e * w * e⁻¹ * w⁻¹ by group] at this
  rcases hgen _ h2 with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers z

theorem exists_three_fpf {z : G} (hzV1 : z ∈ fsuV1 T V) (hgen : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = z) :
    ∃ y ∈ kz T V, orderOf y = 3 ∧ y ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ e ∈ V, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨x, hxL1, hx3, hfix⟩ := exists_l1_fpf C.hyp C.hMod C.h1222 C.h1332 C.h1334
  have hzz : Subgroup.zpowers z = fsuV1 T V := by
    refine le_antisymm (Subgroup.zpowers_le.mpr hzV1) fun c hc => ?_
    rcases hgen c hc with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers c
  have hx1 : x ≠ 1 := by
    rintro rfl
    have hle : V ≤ fsuV1 T V := fun v hv => hfix v hv (by simp)
    have := Subgroup.card_le_of_le hle
    rw [hV8, hV1] at this
    norm_num at this
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  refine ⟨x, l1_le_kz C.hyp C.hMod hxL1, orderOf_eq_prime hx3 hx1,
    hLTV (Subgroup.mem_sup_left hxL), fun e he hxe => ?_⟩
  rw [hzz] at hxe ⊢
  exact hfix e he hxe

theorem nonempty_quot_alt5 :
    Nonempty (↥(kz T V) ⧸ CFSG.pCore 2 ↥(kz T V) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 C.hyp C.hMod C.h63
  have := isSimpleGroup_sl24
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty card_sl24
  have hk : π.ker = CFSG.pCore 2 ↥(kz T V) := by
    rw [hπk, pCoreOf_subgroupOf_self]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective π hπs).trans e)⟩

end Ctx764

end CFSG.Quasithin.H13.L32A
