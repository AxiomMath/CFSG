module

public import CFSG.Quasithin.H13.L32A756f
public import CFSG.Quasithin.H13.L32A770b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace M755

theorem w0_qCodes : ∀ c ∈ w0Codes, c ∈ qCodes := by decide +kernel

theorem w0_xor64 : ∀ c ∈ qCodes, (c ^^^ 64) ∈ qCodes ∧ (c ∈ w0Codes ↔ (c ^^^ 64) ∉ w0Codes) := by
  decide +kernel

theorem line_facts : (∀ b ∈ [2, 4, 6], ∃ d ∈ lineB b, d ≠ 0 ∧ d ≠ 8) ∧
    (∀ c ∈ u0Codes, ∃ b ∈ [2, 4, 6], c ∈ lineB b) ∧
    (∀ b ∈ [2, 4, 6], ∀ d ∈ lineB b, d ≠ 0 → d ∈ ptsQ) ∧
    (∀ b ∈ [2, 4, 6], ∀ d ∈ lineB b, d ∈ qCodes) := by
  decide +kernel

theorem mem_w0_of {c : ℕ} (hc : c ∈ qCodes) (h : InW0 (ptQ c)) : c ∈ w0Codes := by
  obtain ⟨c', hc', he⟩ := h
  rw [← ptQ_inj (w0_qCodes c' hc') hc he]
  exact hc'

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem conjSub_D (_C : Ctx753 T L V K) {l x : G} (hl : l ∈ hz T V) :
    conjSub l (centralizerMod (conjSub x (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub x (conjClosure V (hz T V)))) =
      centralizerMod (conjSub (l * x) (fsuV1 T V)) (conjClosure V (hz T V))
        (conjSub (l * x) (conjClosure V (hz T V))) := by
  rw [conjSub_centralizerMod, ← conjSub_mul, ← conjSub_mul,
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V (hz T V) hl)]

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

@[expose] noncomputable def θX (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) (X : Subgroup G) :
    Subgroup ModQ :=
  (X.subgroupOf (conjClosure V (hz T V))).map (C.θ e)

theorem mem_θX (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) {X : Subgroup G}
    (hXU : X ≤ conjClosure V (hz T V)) {q : ModQ} :
    q ∈ C.θX e X ↔ ∃ d ∈ X, C.θG e d = q := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d, Subgroup.mem_subgroupOf.mp hd, C.θG_eq e d.2⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hXU hd⟩, Subgroup.mem_subgroupOf.mpr hd, (C.θG_eq e (hXU hd)).symm⟩

theorem exists_θG (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) (q : ModQ) :
    ∃ u ∈ conjClosure V (hz T V), C.θG e u = q := by
  obtain ⟨u, hu⟩ := C.θ_surjective e q
  exact ⟨u, u.2, by rw [C.θG_eq e u.2]; exact hu⟩

theorem exists_idx (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXH : X ≤ hz T V) (hXS : C.ΦX E X ≤ sSubG) {a : G} (ha : a ∈ X) :
    ∃ i ∈ idx (C.ΦX E X), C.ΦG E a = sEltG i := by
  have hmem : C.ΦG E a ∈ C.ΦX E X := (C.mem_ΦX E hXH).2 ⟨a, ha, rfl⟩
  obtain ⟨i, hi, hie⟩ := mem_sSubG.1 (hXS hmem)
  exact ⟨i, mem_idx.2 ⟨hi, hie ▸ hmem⟩, hie.symm⟩

theorem fix_u0 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXH : X ≤ hz T V) (hXS : C.ΦX E X ≤ sSubG)
    (hidx : ∀ l ∈ idx (C.ΦX E X), l ∈ [0, 2, 4, 6, 8, 10, 12, 14]) {a : G} (ha : a ∈ X)
    {q : ModQ} (hq : M755.InU0 q) : g2QAct (ZMod 2) (C.ΦG E a) q = q := by
  obtain ⟨i, hi, hie⟩ := C.exists_idx E hXH hXS ha
  obtain ⟨c, hc, rfl⟩ := hq
  have hi64 := (mem_idx.1 hi).1
  rw [hie, M755.g2QAct_sEltG_code hi64 (M755.u0_facts.1 c hc),
    M755.u0_facts.2.2.1 i (hidx i hi) c hc]

theorem caseII_p0 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14) (h1222 : Stmt12_2_2) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) {z : G}
    (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1)
    (hZU : conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V))
    (hθ : C.θG e (((k : G) * g) * z * ((k : G) * g)⁻¹) = M755.ptQ 8)
    (hD : ∃ d ∈ centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V))),
      ∃ a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)), d * a * d⁻¹ * a⁻¹ ≠ 1) : False := by
  set x := (k : G) * g with hx
  set zα := x * z * x⁻¹ with hzα
  have h8 : (8 : ℕ) ∈ M755.ptsQ := by decide
  have hθ1 : C.θG e zα ≠ 1 := by rw [hθ]; exact M755.ptQ_ne_one h8
  have hzαU : zα ∈ conjClosure V (hz T V) := hZU (mul_mem_conjSub hz1)
  have hzαV1 : zα ∉ fsuV1 T V := fun h => hθ1 (C.θG_V1 e h)
  have hZV1 : ∀ t ∈ conjSub x (fsuV1 T V), t ∈ fsuV1 T V → t = 1 := by
    intro t ht htV
    rcases C.mem_zα hz1 hzne ht with h | h
    · exact h
    · exact absurd (show zα ∈ fsuV1 T V by rw [hzα, ← h]; exact htV) hzαV1
  have hUαH := N.uα_le_hz C
  have hUαe : IsElemAbelian 2 (conjSub x (conjClosure V (hz T V))) :=
    F7.isElemAbelian_conjSub C.hF98.F911_3
  have hA1 : C.ΦX E (conjSub x (conjClosure V (hz T V))) ≠ ⊥ := by
    intro hA
    have hcard := C.card_ΦX E hUαH
    rw [hA, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (ne_of_gt (N.one_lt_relIndex C))
  have hNα : ∀ h ∈ hz T V, h * zα = zα * h → ∀ u ∈ conjSub x (conjClosure V (hz T V)),
      h * u * h⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := by
    intro h hh hhz u hu
    have hGα := C.mem_Gα_of_comm (x := x) hz1 hzne hhz
    exact (Subgroup.mem_normalizer_iff.mp
      (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hGα) u).mp hu
  obtain ⟨hAS, hcl⟩ := C.class_p0 E hG h13322 hMod h13314 h1222 hzαU hθ hUαH hUαe hA1 hNα
  have hidxA0 : ∀ l ∈ idx (C.ΦX E (conjSub x (conjClosure V (hz T V)))),
      l ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
    intro l hl
    rcases hcl with h | h
    · have := (h l).1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      omega
    · exact (h l).1 hl
  have hfixU0 : ∀ a ∈ conjSub x (conjClosure V (hz T V)), ∀ q, M755.InU0 q →
      g2QAct (ZMod 2) (C.ΦG E a) q = q := fun a ha q hq => C.fix_u0 E hUαH hAS hidxA0 ha hq
  set D := centralizerMod (conjSub x (fsuV1 T V)) (conjClosure V (hz T V))
    (conjSub x (conjClosure V (hz T V))) with hDdef
  have hDU : D ≤ conjClosure V (hz T V) := centralizerMod_le_left _ _ _
  have hDc : ∀ d ∈ D, ∀ a ∈ conjSub x (conjClosure V (hz T V)),
      a * d * a⁻¹ * d⁻¹ ∈ conjSub x (fsuV1 T V) := by
    intro d hd a ha
    have h1 := hd.2.2 a ha
    have e1 : a * d * a⁻¹ * d⁻¹ = (d * a * d⁻¹ * a⁻¹)⁻¹ := by group
    rw [e1]
    exact inv_mem h1
  have hDn : ∀ h ∈ hz T V, h * zα = zα * h → ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    intro h hh hhz d hd
    have hGα := C.mem_Gα_of_comm (x := x) hz1 hzne hhz
    have e1 : conjSub h D = D := by
      rw [hDdef, conjSub_centralizerMod,
        conjSub_eq_self_iff.mpr (conjSub_le_normalizer C.hF98.H_normalizes_V₁ x hGα),
        conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V (hz T V) hh),
        conjSub_eq_self_iff.mpr
          (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hGα)]
    rw [← e1]
    exact mul_mem_conjSub hd
  set Y := C.θX e D ⊔ M755.u0Sub with hY
  have hmemY : ∀ q, q ∈ Y ↔ ∃ d ∈ D, ∃ p, M755.InU0 p ∧ q = C.θG e d * p := by
    intro q
    rw [hY, Subgroup.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨d, hd, rfl⟩ := (C.mem_θX e hDU).1 ha
      exact ⟨d, hd, b, hb, rfl⟩
    · rintro ⟨d, hd, p, hp, rfl⟩
      exact ⟨_, (C.mem_θX e hDU).2 ⟨d, hd, rfl⟩, p, hp, rfl⟩
  have hYinv : ∀ γ₀ ∈ g2Derived (ZMod 2), g2QAct (ZMod 2) γ₀ (M755.ptQ 8) = M755.ptQ 8 →
      (∀ c ∈ M755.u0Codes, M755.InU0 (g2QAct (ZMod 2) γ₀ (M755.ptQ c))) →
      ∀ y ∈ Y, g2QAct (ZMod 2) γ₀ y ∈ Y := by
    intro γ₀ hγD hγp hγu y hy
    obtain ⟨d, hd, p, ⟨c, hc, rfl⟩, rfl⟩ := (hmemY y).1 hy
    obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E hγD
    have hk'H := C.le_hz hk'
    obtain ⟨h', hh', hcomm, hΦ⟩ := C.exists_comm_of_fix E h13322 hMod h13314 h1222 hzαU hθ1
      hk'H (by rw [hke, hθ]; exact hγp)
    rw [map_mul]
    refine (hmemY _).2 ⟨h' * d * h'⁻¹, hDn h' hh' hcomm d hd, _, hγu c hc, ?_⟩
    rw [C.θG_conj E hh' (hDU hd), hΦ, hke]
  have hl3 : ∀ i ∈ [1, 24, 40], i < 64 := by decide
  have hl4 : ∀ i ∈ [1, 24, 40], i ∈ [1, 24, 40, 64] := by decide
  have hcases := M755.inv_cases (Y := Y) (fun c hc => Subgroup.mem_sup_right ⟨c, hc, rfl⟩)
    (fun i hi y hy => hYinv (sEltG i)
      ((hG.inner_iff i (hl3 i hi)).2 (M755.u0_facts.2.2.2.2.2 i hi))
      (M755.sSubG_fix (mem_sSubG.2 ⟨i, hl3 i hi, rfl⟩))
      (fun c hc => ⟨_, M755.u0_facts.2.2.2.1 i (hl4 i hi) c hc,
        (M755.g2QAct_sEltG_code (hl3 i hi) (M755.u0_facts.1 c hc)).symm⟩) y hy)
    (fun y hy => hYinv M755.z1 M755.z1_mem M755.g2QAct_z1
      (fun c hc => ⟨_, M755.u0_facts.2.2.2.1 64 (by decide) c hc,
        (M755.g2QAct_z1_code (M755.u0_facts.1 c hc)).symm⟩) y hy)
  have hθZ : ∀ t ∈ conjSub x (fsuV1 T V), C.θG e t = 1 ∨ C.θG e t = M755.ptQ 8 := by
    intro t ht
    rcases C.mem_zα hz1 hzne ht with h | h
    · left; rw [h]; exact C.θG_V1 e (one_mem _)
    · right; rw [h]; exact hθ
  rcases hcases with hYU | hYW | hYT
  ·
    obtain ⟨d, hd, a, ha, hda⟩ := hD
    apply hda
    have hdθ : M755.InU0 (C.θG e d) :=
      hYU _ (Subgroup.mem_sup_left ((C.mem_θX e hDU).2 ⟨d, hd, rfl⟩))
    have h1 : C.θG e (a * d * a⁻¹ * d⁻¹) = 1 := by
      rw [C.θG_comm E (hUαH ha) (hDU hd), hfixU0 a ha _ hdθ, mul_inv_cancel]
    have h3 := hZV1 _ (hDc d hd a ha) (C.comm_mem_V1 E (hUαH ha) (hDU hd) h1)
    calc d * a * d⁻¹ * a⁻¹ = (a * d * a⁻¹ * d⁻¹)⁻¹ := by group
      _ = 1 := by rw [h3, inv_one]
  rotate_left
  ·
    apply hA1
    rw [eq_bot_iff]
    intro γ₀ hγ
    obtain ⟨a, ha, rfl⟩ := (C.mem_ΦX E hUαH).1 hγ
    rw [Subgroup.mem_bot]
    refine M755.eq_one_of_transv (c := M755.ptQ 8) fun q => ?_
    have hq : q ∈ Y := by rw [hYT]; exact Subgroup.mem_top q
    obtain ⟨d, hd, p, hp, rfl⟩ := (hmemY q).1 hq
    have e1 : g2QAct (ZMod 2) (C.ΦG E a) (C.θG e d) * p * (C.θG e d * p)⁻¹ =
        g2QAct (ZMod 2) (C.ΦG E a) (C.θG e d) * (C.θG e d)⁻¹ := by group
    rw [map_mul, hfixU0 a ha p hp, e1, ← C.θG_comm E (hUαH ha) (hDU hd)]
    exact hθZ _ (hDc d hd a ha)
  obtain ⟨d₀, hd₀, hd₀U⟩ : ∃ d ∈ D, ¬ M755.InU0 (C.θG e d) := by
    by_contra hcon
    push Not at hcon
    have h2 : M755.ptQ 2 ∈ Y := (hYW _).2 ⟨2, by decide, rfl⟩
    obtain ⟨d', hd', p, hp, he⟩ := (hmemY _).1 h2
    have h3 : M755.ptQ 2 ∈ M755.u0Sub := by
      rw [he]
      exact M755.u0Sub.mul_mem (hcon d' hd') hp
    obtain ⟨c, hc, hce⟩ := h3
    have hc2 := M755.ptQ_inj (M755.u0_facts.1 c hc) (by decide) hce
    rw [hc2] at hc
    exact absurd hc (by decide)
  rcases hcl with hB | hA0
  rotate_left
  · exfalso
    obtain ⟨q, hq, hqe⟩ : M755.InW0 (C.θG e d₀) :=
      (hYW _).1 (Subgroup.mem_sup_left ((C.mem_θX e hDU).2 ⟨d₀, hd₀, rfl⟩))
    have hqU : q ∉ M755.u0Codes := fun h => hd₀U ⟨q, h, hqe⟩
    have hqQ := M755.w0_qCodes q hq
    obtain ⟨b, hb, -, honto⟩ := M755.facts_wA0 q hq hqU
    obtain ⟨d', hd', hd'0, hd'8⟩ := M755.line_facts.1 b hb
    obtain ⟨i, hi, hie⟩ := honto d' hd'
    have hiA := (hA0 i).2 hi
    obtain ⟨a, ha, hae⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 hiA).2
    have hi64 := (mem_idx.1 hiA).1
    have hiC : i ∈ [0, 1, 2, 4, 6, 8, 10, 12, 14, 24, 40, 64] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega
    have h1 : C.θG e (a * d₀ * a⁻¹ * d₀⁻¹) = M755.ptQ d' := by
      rw [C.θG_comm E (hUαH ha) (hDU hd₀), hae, ← hqe, M755.g2QAct_sEltG_code hi64 hqQ,
        show ∀ r : ModQ, r⁻¹ = r from fun r => inv_eq_of_mul_eq_one_right (M755.mul_self_Q r),
        ← M755.ptQ_xor (M755.actC_mem _ hiC q hqQ) hqQ, hie]
    have hd'p := M755.line_facts.2.2.1 b hb d' hd' hd'0
    rcases hθZ _ (hDc d₀ hd₀ a ha) with h2 | h2
    · rw [h1] at h2
      exact M755.ptQ_ne_one hd'p h2
    · rw [h1] at h2
      exact hd'8 (M755.ptQ_injective hd'p h8 h2)
  obtain ⟨d, hd, a, ha, hda⟩ := hD
  have hda' : a * d * a⁻¹ * d⁻¹ ≠ 1 := fun h => hda (by
    calc d * a * d⁻¹ * a⁻¹ = (a * d * a⁻¹ * d⁻¹)⁻¹ := by group
      _ = 1 := by rw [h, inv_one])
  have hzαeq : a * d * a⁻¹ * d⁻¹ = zα := by
    rcases C.mem_zα hz1 hzne (hDc d hd a ha) with h | h
    · exact absurd h hda'
    · exact h
  obtain ⟨i, hi, hie⟩ := C.exists_idx E hUαH hAS ha
  have hi' := (hB i).1 hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [sEltG_zero] at hie
    have h1 : C.θG e (a * d * a⁻¹ * d⁻¹) = 1 := by
      rw [C.θG_comm E (hUαH ha) (hDU hd), hie, map_one, MulAut.one_apply, mul_inv_cancel]
    exact hda' (hZV1 _ (hDc d hd a ha) (C.comm_mem_V1 E (hUαH ha) (hDU hd) h1))
  have hb₀ : i ∈ [2, 4, 6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi' ⊢; omega
  obtain ⟨h, hhK, hhV₂, hline, hcover⟩ := C.exists_line E hMod hVL hV₂ hb₀
  have hhH := C.le_hz hhK
  have hcm := C.comm_mem_line E h13322 hMod hVL hV₂ hb₀ hhH hline hcover (hUαH ha) hie (hDU hd)
  have hzαVh : zα ∈ conjSub h V := by
    rw [← hzαeq]
    have e1 : a * d * a⁻¹ * d⁻¹ = (d * a * d⁻¹ * a⁻¹)⁻¹ := by group
    rw [e1]
    exact inv_mem hcm
  obtain ⟨-, -, -, hV1c, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from hcon)
    rw [hV1c, hV₂.2.2.2] at this
    omega
  have hwU := le_conjClosure V (hz T V) (hV₂.2.1 hw)
  have hwVh : w ∈ conjSub h V := by
    have hw' : w ∈ conjSub h V₂ := by rw [hhV₂]; exact hw
    exact conjSub_mono h hV₂.2.1 hw'
  have hzw : zα * w⁻¹ ∈ fsuV1 T V := by
    by_contra hnot
    obtain ⟨d', hd', hd'0, hθ'⟩ := hline _ (mul_mem hzαVh (inv_mem hwVh)) hnot
    rw [C.θG_mul e hzαU (inv_mem hwU), C.θG_inv e hwU, hθ, C.θG_V2 E hMod hVL hV₂ hw hw1,
      mul_inv_cancel] at hθ'
    exact M755.ptQ_ne_one (M755.line_facts.2.2.1 i hb₀ d' hd' hd'0) hθ'.symm
  have hzαV₂ : zα ∈ V₂ := by
    have e1 : zα = (zα * w⁻¹) * w := by group
    rw [e1]
    exact mul_mem (hV₂.1 hzw) hw
  have h1281 := C.hyp.hyp1281One h13322 hMod
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hz1
  have hzαV : zα ∈ V := hV₂.2.1 hzαV₂
  have hzα1 : zα ≠ 1 := fun h => hzαV1 (h ▸ one_mem _)
  have hzzα : z ≠ zα := fun h => hzαV1 (h ▸ hz1)
  obtain ⟨l, -, hl1, hl2⟩ := exists_conj_eq_pair h1281 hzV hzαV hzαV hzV hzne hzα1 hzα1 hzne
    hzzα (Ne.symm hzzα)
  have hlx : l⁻¹ * x ∈ hz T V := C.mem_hz_of_comm hz1 hzne (by
    calc l⁻¹ * x * z * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * z * x⁻¹) * l := by group
      _ = l⁻¹ * zα * l := rfl
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [hl1]
      _ = z := by group)
  have hll : l * l ∈ hz T V := C.mem_hz_of_comm hz1 hzne (by
    calc l * l * z * (l * l)⁻¹ = l * (l * z * l⁻¹) * l⁻¹ := by group
      _ = l * zα * l⁻¹ := by rw [hl1]
      _ = z := hl2)
  have hlxH : l * x ∈ hz T V := C.mem_hz_of_comm hz1 hzne (by
    calc l * x * z * (l * x)⁻¹ = l * (x * z * x⁻¹) * l⁻¹ := by group
      _ = l * zα * l⁻¹ := rfl
      _ = z := hl2)
  have hHU : ∀ c ∈ hz T V, conjSub c (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    fun c hc => conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hc)
  have hlU : conjSub l (conjClosure V (hz T V)) = conjSub x (conjClosure V (hz T V)) := by
    calc conjSub l (conjClosure V (hz T V)) =
        conjSub l (conjSub (l⁻¹ * x) (conjClosure V (hz T V))) := by rw [hHU _ hlx]
      _ = conjSub x (conjClosure V (hz T V)) := by rw [← conjSub_mul, mul_inv_cancel_left]
  have hlUα : conjSub l (conjSub x (conjClosure V (hz T V))) = conjClosure V (hz T V) := by
    rw [← hlU, ← conjSub_mul, hHU _ hll]
  have hlZ : conjSub l (conjSub x (fsuV1 T V)) = fsuV1 T V := by
    rw [← conjSub_mul]
    exact conjSub_eq_self_iff.mpr (C.hF98.H_normalizes_V₁ hlxH)
  have hlinvUα : conjSub l⁻¹ (conjSub x (conjClosure V (hz T V))) = conjClosure V (hz T V) := by
    rw [← hlU, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hlinvU : conjSub l⁻¹ (conjClosure V (hz T V)) = conjSub x (conjClosure V (hz T V)) := by
    calc conjSub l⁻¹ (conjClosure V (hz T V)) =
        conjSub l⁻¹ (conjSub l (conjSub x (conjClosure V (hz T V)))) := by rw [hlUα]
      _ = conjSub x (conjClosure V (hz T V)) := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hlinvZ : conjSub l⁻¹ (fsuV1 T V) = conjSub x (fsuV1 T V) := by
    calc conjSub l⁻¹ (fsuV1 T V) = conjSub l⁻¹ (conjSub l (conjSub x (fsuV1 T V))) := by
          rw [hlZ]
      _ = conjSub x (fsuV1 T V) := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hlD : conjSub l D = centralizerMod (fsuV1 T V) (conjSub x (conjClosure V (hz T V)))
      (conjClosure V (hz T V)) := by
    rw [hDdef, conjSub_centralizerMod, hlZ, hlU, hlUα]
  have hsub : centralizerMod (fsuV1 T V) (conjSub x (conjClosure V (hz T V)))
      (conjClosure V (hz T V)) ≤ conjSub x (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V) := by
    intro a' ha'
    refine ⟨ha'.1, ?_⟩
    have ha'H := hUαH ha'.1
    have key : ∀ q : ModQ, g2QAct (ZMod 2) (C.ΦG E a') q = q := by
      intro q
      obtain ⟨u, huU, rfl⟩ := C.exists_θG e q
      rw [← C.θG_conj E ha'H huU]
      have hv := ha'.2.2 u huU
      have hvU : a' * u * a'⁻¹ * u⁻¹ ∈ conjClosure V (hz T V) :=
        (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _) hv
      rw [show a' * u * a'⁻¹ = (a' * u * a'⁻¹ * u⁻¹) * u by group,
        C.θG_mul e hvU huU, C.θG_V1 e hv, one_mul]
    have h1 : C.ΦG E a' = 1 :=
      g2QAct_injective (MulEquiv.ext fun q => by rw [key q, map_one, MulAut.one_apply])
    rw [C.ΦG_eq E ha'H] at h1
    exact (C.Φ_eq_one_iff E ⟨a', ha'H⟩).1 h1
  have hcardA : (conjSub x (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V)).relIndex
      (conjSub x (conjClosure V (hz T V))) = 4 := by
    rw [← C.card_ΦX E hUαH, card_eq_idx hAS]
    have : idx (C.ΦX E (conjSub x (conjClosure V (hz T V)))) = ({0, 2, 4, 6} : Finset ℕ) := by
      ext l
      rw [hB l]
      simp
    rw [this]
    rfl
  have hDidx : 4 ≤ D.relIndex (conjClosure V (hz T V)) := by
    have h1 : D.relIndex (conjClosure V (hz T V)) =
        (centralizerMod (fsuV1 T V) (conjSub x (conjClosure V (hz T V)))
          (conjClosure V (hz T V))).relIndex (conjSub x (conjClosure V (hz T V))) := by
      rw [← hlD, ← hlU, relIndex_conjSub]
    rw [h1, ← hcardA]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := (centralizerMod (fsuV1 T V) (conjSub x (conjClosure V (hz T V)))
        (conjClosure V (hz T V))).subgroupOf (conjSub x (conjClosure V (hz T V))))))
      (Subgroup.relIndex_dvd_of_le_left _ hsub)
  have hU0D : ∀ c ∈ M755.u0Codes, ∃ d ∈ D, C.θG e d = M755.ptQ c := by
    intro c hc
    obtain ⟨b, hb, hcb⟩ := M755.line_facts.2.1 c hc
    obtain ⟨c', hc', hc'e⟩ := M755.facts_B0_onto b hb c hcb
    have hbA : b ∈ idx (C.ΦX E (conjSub x (conjClosure V (hz T V)))) :=
      (hB b).2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega)
    obtain ⟨a', ha', ha'e⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 hbA).2
    have hb64 := (mem_idx.1 hbA).1
    obtain ⟨u, huU, hu⟩ := C.exists_θG e (M755.ptQ c')
    refine ⟨a' * u * a'⁻¹ * u⁻¹, ?_, ?_⟩
    · have hmem := N.comm_le_D C (Subgroup.commutator_mem_commutator huU ha')
      rw [commutatorElement_def] at hmem
      have e1 : a' * u * a'⁻¹ * u⁻¹ = (u * a' * u⁻¹ * a'⁻¹)⁻¹ := by group
      rw [e1]
      exact inv_mem hmem
    · have hbC : b ∈ [0, 1, 2, 4, 6, 8, 10, 12, 14, 24, 40, 64] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega
      rw [C.θG_comm E (hUαH ha') huU, ha'e, hu,
        M755.g2QAct_sEltG_code hb64 hc',
        show ∀ r : ModQ, r⁻¹ = r from fun r => inv_eq_of_mul_eq_one_right (M755.mul_self_Q r),
        ← M755.ptQ_xor (M755.actC_mem _ hbC c' hc') hc', hc'e]
  obtain ⟨u₀, hu₀U, hu₀θ, hu₀D⟩ :
      ∃ u₀ ∈ conjClosure V (hz T V), C.θG e u₀ = 1 ∧ u₀ ∉ D := by
    by_contra hcon
    push Not at hcon
    have hDW : ∀ u ∈ conjClosure V (hz T V), M755.InW0 (C.θG e u) → u ∈ D := by
      intro u hu hW
      obtain ⟨d', hd', p, ⟨c, hc, rfl⟩, he⟩ := (hmemY _).1 ((hYW _).2 hW)
      obtain ⟨d'', hd'', hd''e⟩ := hU0D c hc
      have hdd := mul_mem (hDU hd') (hDU hd'')
      have h1 : C.θG e (u * (d' * d'')⁻¹) = 1 := by
        rw [C.θG_mul e hu (inv_mem hdd), C.θG_inv e hdd, C.θG_mul e (hDU hd') (hDU hd''), he,
          hd''e, mul_inv_cancel]
      have h2 := hcon _ (mul_mem hu (inv_mem hdd)) h1
      have e1 : u = u * (d' * d'')⁻¹ * (d' * d'') := by group
      rw [e1]
      exact mul_mem h2 (mul_mem hd' hd'')
    have hDiff : ∀ u ∈ conjClosure V (hz T V), ∀ cu ∈ M755.qCodes, C.θG e u = M755.ptQ cu →
        (u ∈ D ↔ cu ∈ M755.w0Codes) := by
      intro u hu cu hcu hθu
      constructor
      · intro huD
        have h1 := (hYW _).1 (Subgroup.mem_sup_left ((C.mem_θX e hDU).2 ⟨u, huD, rfl⟩))
        rw [hθu] at h1
        exact M755.mem_w0_of hcu h1
      · intro hw'
        exact hDW u hu (by rw [hθu]; exact ⟨cu, hw', rfl⟩)
    obtain ⟨u₆₄, hu₆₄U, hu₆₄⟩ := C.exists_θG e (M755.ptQ 64)
    have h64 : (64 : ℕ) ∈ M755.qCodes := by decide
    have hidx2 : (D.subgroupOf (conjClosure V (hz T V))).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨u₆₄, hu₆₄U⟩, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      obtain ⟨cb, hcb, hcbe⟩ := M755.exists_code (C.θG e b)
      obtain ⟨hx64, hiff⟩ := M755.w0_xor64 cb hcb
      have hθbu : C.θG e (b * u₆₄) = M755.ptQ (cb ^^^ 64) := by
        rw [C.θG_mul e b.2 hu₆₄U, ← hcbe, hu₆₄, ← M755.ptQ_xor hcb h64]
      rw [hDiff _ (mul_mem b.2 hu₆₄U) _ hx64 hθbu, hDiff _ b.2 cb hcb hcbe.symm]
      by_cases hcw : cb ∈ M755.w0Codes
      · exact Or.inr ⟨hcw, hiff.1 hcw⟩
      · exact Or.inl ⟨by_contra fun h => hcw (hiff.2 h), hcw⟩
    have : D.relIndex (conjClosure V (hz T V)) = 2 := hidx2
    omega
  have hu₀N : u₀ ∈ Subgroup.normalizer (conjSub x (fsuV1 T V) : Set G) :=
    conjSub_le_normalizer C.hF98.H_normalizes_V₁ x (N.conjClosure_le_Gα C hu₀U)
  obtain ⟨a₀, ha₀, ha₀Z⟩ : ∃ a₀ ∈ conjSub x (conjClosure V (hz T V)),
      u₀ * a₀ * u₀⁻¹ * a₀⁻¹ ∉ conjSub x (fsuV1 T V) := by
    by_contra hcon
    push Not at hcon
    exact hu₀D ⟨hu₀U, hu₀N, hcon⟩
  set u₀' := l⁻¹ * u₀ * l⁻¹⁻¹ with hu₀'
  have hu₀'Uα : u₀' ∈ conjSub x (conjClosure V (hz T V)) := by
    rw [← hlinvU]
    exact mul_mem_conjSub hu₀U
  have hu₀'H := hUαH hu₀'Uα
  have hu₀'c : ∀ u ∈ conjClosure V (hz T V),
      u₀' * u * u₀'⁻¹ * u⁻¹ ∈ conjSub x (fsuV1 T V) := by
    intro u hu
    have haUα : l * u * l⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := by
      rw [← hlU]
      exact mul_mem_conjSub hu
    have h1 : C.θG e ((l * u * l⁻¹) * u₀ * (l * u * l⁻¹)⁻¹ * u₀⁻¹) = 1 := by
      rw [C.θG_comm E (hUαH haUα) hu₀U, hu₀θ, map_one, mul_inv_cancel]
    have h2 := C.comm_mem_V1 E (hUαH haUα) hu₀U h1
    rw [← hlinvZ]
    have e1 : u₀' * u * u₀'⁻¹ * u⁻¹ =
        l⁻¹ * ((l * u * l⁻¹) * u₀ * (l * u * l⁻¹)⁻¹ * u₀⁻¹)⁻¹ * l⁻¹⁻¹ := by
      rw [hu₀']
      group
    rw [e1]
    exact mul_mem_conjSub (inv_mem h2)
  have hΦ1 : C.ΦG E u₀' = 1 := by
    refine M755.eq_one_of_transv (c := M755.ptQ 8) fun q => ?_
    obtain ⟨u, huU, rfl⟩ := C.exists_θG e q
    rw [← C.θG_comm E hu₀'H huU]
    exact hθZ _ (hu₀'c u huU)
  have hu₀'U : ∀ u ∈ conjClosure V (hz T V), u₀' * u * u₀'⁻¹ * u⁻¹ = 1 := by
    intro u hu
    have h1 : C.θG e (u₀' * u * u₀'⁻¹ * u⁻¹) = 1 := by
      rw [C.θG_comm E hu₀'H hu, hΦ1, map_one, MulAut.one_apply, mul_inv_cancel]
    exact hZV1 _ (hu₀'c u hu) (C.comm_mem_V1 E hu₀'H hu h1)
  apply ha₀Z
  have hu : l⁻¹ * a₀ * l⁻¹⁻¹ ∈ conjClosure V (hz T V) := by
    rw [← hlinvUα]
    exact mul_mem_conjSub ha₀
  have h1 := hu₀'U _ hu
  have e1 : u₀ * a₀ * u₀⁻¹ * a₀⁻¹ =
      l * (u₀' * (l⁻¹ * a₀ * l⁻¹⁻¹) * u₀'⁻¹ * (l⁻¹ * a₀ * l⁻¹⁻¹)⁻¹) * l⁻¹ := by
    rw [hu₀']
    group
  rw [e1, h1, mul_one, mul_inv_cancel]
  exact one_mem _

theorem comm_D_eq_bot (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14) (h1222 : Stmt12_2_2) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ⁅centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub ((k : G) * g) (conjClosure V (hz T V))),
      conjSub ((k : G) * g) (conjClosure V (hz T V))⁆ = ⊥ := by
  by_contra hD
  obtain ⟨z, hz1, hzne⟩ := C.exists_V1_ne
  have hZU := N.zα_le_U_of_comm C hD
  obtain ⟨v, hv, hv1, hθv⟩ := C.θ_zα_mem E hG h13322 hMod hVL hV₂ h13314 h1222 N hz1 hzne hZU
  obtain ⟨l, hlL, hlH, hlθ⟩ := C.exists_l_of_V E h13322 hMod hVL hV₂ hv hv1
  have N' := N.mul_left C.hF98 (inv_mem hlL) (inv_mem hlH)
  have hx' : ((⟨l⁻¹, Subgroup.mem_sup_left (Subgroup.mem_sup_left (inv_mem hlL))⟩ * k :
      ↥((L ⊔ T) ⊔ hz T V)) : G) * g = l⁻¹ * ((k : G) * g) := by
    rw [Subgroup.coe_mul, mul_assoc]
  have hHU : conjSub l⁻¹ (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ (inv_mem hlH))
  obtain ⟨d, hd, a, ha, hda⟩ : ∃ d ∈ centralizerMod (conjSub ((k : G) * g) (fsuV1 T V))
      (conjClosure V (hz T V)) (conjSub ((k : G) * g) (conjClosure V (hz T V))),
      ∃ a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)), d * a * d⁻¹ * a⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hD
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd a ha
    rw [commutatorElement_def, Subgroup.mem_bot]
    exact hcon d hd a ha
  refine C.caseII_p0 E hG h13322 hMod hVL hV₂ h13314 h1222 N' hz1 hzne ?_ ?_ ?_
  · rw [hx', conjSub_mul, ← hHU]
    exact conjSub_mono _ hZU
  · rw [hx', show l⁻¹ * ((k : G) * g) * z * (l⁻¹ * ((k : G) * g))⁻¹ =
      l⁻¹ * (((k : G) * g) * z * ((k : G) * g)⁻¹) * l⁻¹⁻¹ by group,
      C.θG_conj E (inv_mem hlH) (hZU (mul_mem_conjSub hz1)), hθv, ← hlθ, C.ΦG_inv E hlH,
      map_inv, MulAut.inv_apply_self]
  · refine ⟨l⁻¹ * d * l⁻¹⁻¹, ?_, l⁻¹ * a * l⁻¹⁻¹, ?_, ?_⟩
    · rw [hx', ← C.conjSub_D (inv_mem hlH)]
      exact mul_mem_conjSub hd
    · rw [hx', conjSub_mul]
      exact mul_mem_conjSub ha
    · intro h1
      apply hda
      have e1 : l⁻¹ * d * l⁻¹⁻¹ * (l⁻¹ * a * l⁻¹⁻¹) * (l⁻¹ * d * l⁻¹⁻¹)⁻¹ *
          (l⁻¹ * a * l⁻¹⁻¹)⁻¹ = l⁻¹ * (d * a * d⁻¹ * a⁻¹) * l := by group
      rw [e1] at h1
      calc d * a * d⁻¹ * a⁻¹ = l * (l⁻¹ * (d * a * d⁻¹ * a⁻¹) * l) * l⁻¹ := by group
        _ = 1 := by rw [h1]; group

end Ctx753

end CFSG.Quasithin.H13.L32A
