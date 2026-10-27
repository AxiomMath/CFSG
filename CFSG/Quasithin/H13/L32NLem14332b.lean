module

public import CFSG.Quasithin.H13.L32NLem14332a
public import CFSG.Quasithin.H13.L32NThm144Big
public import CFSG.Quasithin.Vol2.Ch12Sec8OneModel
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G]

theorem sq_mem_and_comm_mem [Finite G] {U V₁ : Subgroup G} (hU : IsPGroup 2 ↥U)
    (hΦ : frattiniOf U ≤ V₁) :
    (∀ u ∈ U, u * u ∈ V₁) ∧ ∀ u ∈ U, ∀ w ∈ U, ⁅u, w⁆ ∈ V₁ := by
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hU
  refine ⟨fun u hu => hΦ ?_, fun u hu w hw => hΦ ?_⟩
  · refine ⟨⟨u, hu⟩ ^ 2, ?_, by simp [pow_two]⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpow _
  · refine ⟨⁅(⟨u, hu⟩ : ↥U), ⟨w, hw⟩⁆, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini ↥U) ⁅(⟨u, hu⟩ : ↥U), ⟨w, hw⟩⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _

structure Ctx14332 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g a : G)
    (D : HatModelU (fsuU T V)) : Prop where
  hyp : Hyp14310One G T L V
  lt : fsuV1 T V < centerOf (fsuU T V)
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  aV₂ : a ∈ V₂
  a1 : a ∉ fsuV1 T V
  aU : a ∈ fsuU T V
  V₂_cases : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c
  H_V1 : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c
  U2 : IsPGroup 2 ↥(fsuU T V)
  card_V1 : Nat.card ↥(fsuV1 T V) = 2
  sq : ∀ u ∈ fsuU T V, u * u ∈ fsuV1 T V
  comm : ∀ u ∈ fsuU T V, ∀ w ∈ fsuU T V, ⁅u, w⁆ ∈ fsuV1 T V
  T_le : T ≤ l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)
  T2 : IsPGroup 2 ↥T
  T_odd : Odd ((D.img T).relIndex (D.img (l32nH T V)))
  card_zU : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) * 2 =
    Nat.card ↥(centerOf (fsuU T V))
  pi_ne : D.π a ≠ 0
  zUg_le : CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V
  Wg_le : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V
  U_le : fsuU T V ≤ l32nH T V
  V_U : V ≤ fsuU T V
  V_comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  q_tilde : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)

theorem exists_ctx14332 [Finite G] (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    (h14331 : Lemma14331One) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) :
    ∃ (V₂ : Subgroup G) (g a : G) (D : HatModelU (fsuU T V)), Ctx14332 G T L V V₂ g a D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have h1283 := lemma12_8_3 h12213
  have h1284 := lemma12_8_4 h1222 h37 h38 h39
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
  obtain ⟨hVe, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by
    rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV₂U : V₂ ≤ fsuU T V := hV₂.1.1.trans hVU
  have haU : a ∈ fsuU T V := hV₂U haV₂
  have hidx : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V₂)
    rw [inf_eq_left.mpr hV₂.2, hV1, hV₂4] at this
    omega
  have hV₂c : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c := by
    intro x hx
    by_cases hx1 : x ∈ fsuV1 T V
    · exact Or.inl hx1
    right
    have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V₂.inv_mem haV₂⟩)
      (b := ⟨x, hx⟩)).mpr (iff_of_false (fun hm => ha1 (by
        have := (fsuV1 T V).inv_mem (Subgroup.mem_subgroupOf.mp hm)
        rwa [inv_inv] at this)) (fun hm => hx1 (Subgroup.mem_subgroupOf.mp hm)))
    exact ⟨a⁻¹ * x, Subgroup.mem_subgroupOf.mp hm, by group⟩
  have hHV1 : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c := by
    intro x hx c hc
    have := Subgroup.mem_centralizer_iff.mp (le_centralizer_normalizer_of_card_eq_two hV1 hc) x hx
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [this]
      _ = c := by group
  have hU2 : IsPGroup 2 ↥(fsuU T V) :=
    (h.fsu.sylow.1).to_le (h.fsuU_le h13322 hV h1283 h1284)
  have hΦ : frattiniOf (fsuU T V) ≤ fsuV1 T V :=
    (display12_8_frattini h1222 h12213 G T L V 3 (fsuV1 T V) V₂ hs).le
  obtain ⟨hsq, hcomm⟩ := sq_mem_and_comm_mem hU2 hΦ
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := hV₂.1.2.2
  have hTodd : Odd ((D.img T).relIndex (D.img (l32nH T V))) := by
    have hdvd := relIndex_img_dvd D hTH (l32nH_le_normalizer_fsuU T V)
    have hsyl := (h.isSylowTwoOf_l32nH hV).2.2
    have hodd : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (T.relIndex (l32nH T V)) with he | ho
      · exact absurd (even_iff_two_dvd.mp he) hsyl
      · exact Nat.odd_iff.mp ho)
    exact Odd.of_dvd_nat hodd hdvd
  have hZ := card_img_conj_zU h12810 h12813 hs hgP hgN (h14331 G T L V h hlt) hlt.le hV1 D
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  have hpi : D.π a ≠ 0 := by
    intro h0
    have haZ := (L128A.HatU.π_eq_zero_iff D haU).mp h0
    apply ha1
    rw [← hVZ]
    exact Subgroup.mem_inf.mpr ⟨hV₂.1.1 haV₂, haZ⟩
  have hgN₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hgP.2 V₂) ⟨2, le_rfl, hV₂.1⟩
  have hWg : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
    (conj_le_centralizer_of_le inf_le_right hV₂.2 hgN₂).trans
      (Subgroup.centralizer_le_normalizer _)
  exact ⟨V₂, g, a, D, ⟨h, hlt, hV₂, hs, hgP, hgN, haV₂, ha1, haU, hV₂c, hHV1, hU2, hV1, hsq,
    hcomm, le_inf hTH hTV₂, h.fsu.sylow.1, hTodd, hZ, hpi, conj_zU_le h12813 hs hgP hgN, hWg,
    h.fsuU_le_l32nH hV, hVU, fun x hx y hy =>
      congrArg Subtype.val (hVe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    (h1284 G T L V 3 (h.hyp1281One h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1 hV)
      (h.isHzOne_l32nH h13322 hV h1283)).2.2.2⟩⟩

end L14332

end CFSG.Quasithin.H13
