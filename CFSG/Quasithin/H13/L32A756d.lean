module

public import CFSG.Quasithin.H13.L32A755i
public import CFSG.Quasithin.H13.L32A756b
public import CFSG.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace M755

theorem g2QAct_yB {b : ℕ} (hb : b ∈ [2, 4, 6]) {c : ℕ} (hc : c ∈ o0Codes) :
    g2QAct (ZMod 2) (yB b) (ptQ c) = ptQ (nq (mact (wMatC (yW b)) c)) := by
  rw [g2QAct_ptQ _ hc, yB, matCode_wordGG' (yW_tok b hb),
    ptQ_nq (by rw [← matCode_wordGG' (yW_tok b hb)]; exact mact_mem_o0Codes (yB b).2 hc)]

theorem facts_yB_sq : ∀ b ∈ [2, 4, 6], ∀ c ∈ lineB b, c ≠ 0 →
    nq (mact (wMatC (yW b)) (nq (mact (wMatC (yW b)) c))) =
      c ^^^ nq (mact (wMatC (yW b)) c) ∧ nq (mact (wMatC (yW b)) c) ∈ o0Codes ∧
      (c ^^^ nq (mact (wMatC (yW b)) c)) ∈ lineB b ∧ c ∈ o0Codes := by
  decide +kernel

theorem facts_z1_lines : (∀ c ∈ [8, 32, 40], actC 64 c ∈ [8, 48, 56]) ∧
    (∀ c ∈ [8, 48, 56], actC 64 c ∈ [8, 16, 24]) ∧ actC 64 8 = 8 ∧
    (∀ d ∈ [8, 48, 56], ∃ c ∈ [8, 32, 40], actC 64 c = d) ∧
    (∀ d ∈ [8, 16, 24], ∃ c ∈ [8, 48, 56], actC 64 c = d) := by
  decide +kernel

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem exists_pt_V (C : Ctx753 T L V K) (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {v : G} (hv : v ∈ V) (hv1 : v ∉ fsuV1 T V) :
    ∃ l ∈ L, l ∈ hz T V ∧ ∃ w ∈ V₂, w ∉ fsuV1 T V ∧ l * w * l⁻¹ = v := by
  have h1281 := C.hyp.hyp1281One h13322 hMod
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨z, hz1, hzne⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra h
    push Not at h
    have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot] at hV1
    omega
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [hV1, hV₂.2.2.2] at this
    omega
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hz1
  have hwz : w ≠ z := fun h => hw1 (h ▸ hz1)
  have hvz : v ≠ z := fun h => hv1 (h ▸ hz1)
  have hw1' : w ≠ 1 := fun h => hw1 (h ▸ one_mem _)
  have hv1' : v ≠ 1 := fun h => hv1 (h ▸ one_mem _)
  obtain ⟨l, hl, h1, h2⟩ := exists_conj_eq_pair h1281 hzV (hV₂.2.1 hw) hzV hv hzne hw1' hzne hv1'
    (Ne.symm hwz) (Ne.symm hvz)
  exact ⟨l, hl, C.mem_hz_of_comm hz1 hzne h1, w, hw, hw1, h2⟩

theorem V1_le_conj (C : Ctx753 T L V K) {h : G} (hh : h ∈ hz T V) :
    fsuV1 T V ≤ conjSub h V := by
  intro z hz
  have := C.conj_V1 hh hz
  rw [← this]
  exact mul_mem_conjSub ((inf_le_left : fsuV1 T V ≤ V) hz)

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem line_le (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {c c' : G} (hc : c ∈ hz T V) (hc' : c' ∈ hz T V)
    (h : ∀ y ∈ conjSub c' V, y ∉ fsuV1 T V →
      ∃ y₀ ∈ conjSub c V, y₀ ∉ fsuV1 T V ∧ C.θG e y₀ = C.θG e y) :
    conjSub c' V ≤ conjSub c V := by
  intro y hy
  by_cases hy1 : y ∈ fsuV1 T V
  · have : fsuV1 T V ≤ conjSub c V := by
      intro z hz
      have := C.conj_V1 hc hz
      rw [← this]
      exact mul_mem_conjSub ((inf_le_left : fsuV1 T V ≤ V) hz)
    exact this hy1
  obtain ⟨y₀, hy₀, hy₀1, hθ⟩ := h y hy hy1
  obtain ⟨v, hv, hv1, rfl⟩ := C.exists_of_mem_conjSub hc' hy hy1
  obtain ⟨v₀, hv₀, hv₀1, rfl⟩ := C.exists_of_mem_conjSub hc hy₀ hy₀1
  obtain ⟨l, hlL, hlH, w, hw, hw1, rfl⟩ := C.exists_pt_V h13322 hMod hV₂ hv hv1
  obtain ⟨l₀, hl₀L, hl₀H, w₀, hw₀, hw₀1, rfl⟩ := C.exists_pt_V h13322 hMod hV₂ hv₀ hv₀1
  have hmem : ∀ {a b u : G}, u ∈ V₂ → a * (b * u * b⁻¹) * a⁻¹ ∈ conjSub (a * b) V₂ :=
    fun {a b u} hu => by
      rw [show a * (b * u * b⁻¹) * a⁻¹ = (a * b) * u * (a * b)⁻¹ by group]
      exact mul_mem_conjSub hu
  have heq := C.eq_of_θG_pt E hMod hVL hV₂ (mul_mem hc hl₀H) (mul_mem hc' hlH) (hmem hw₀) hy₀1
    (hmem hw) hy1 hθ
  have hy' : c' * (l * w * l⁻¹) * c'⁻¹ ∈ conjSub (c * l₀) V₂ := heq ▸ hmem hw
  rw [conjSub_mul] at hy'
  refine conjSub_mono c ?_ hy'
  rintro _ ⟨u, hu, rfl⟩
  change l₀ * u * l₀⁻¹ ∈ V
  obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  exact (Subgroup.mem_normalizer_iff.mp ((le_sup_left : L ≤ L ⊔ T).trans hLTV hl₀L) u).mp
    (hV₂.2.1 hu)

theorem exists_V_θG (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {d : ℕ} (hd : d ∈ [8, 32, 40]) : ∃ v ∈ V, v ∉ fsuV1 T V ∧ C.θG e v = M755.ptQ d := by
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [hV1, hV₂.2.2.2] at this
    omega
  obtain ⟨v, hv, hv2⟩ : ∃ v ∈ V, v ∉ V₂ := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show V ≤ V₂ from h)
    rw [hV8, hV₂.2.2.2] at this
    omega
  have hVU := le_conjClosure V (hz T V)
  have hv1 : v ∉ fsuV1 T V := fun h => hv2 (hV₂.1 h)
  have hwV := hV₂.2.1 hw
  have hw8 := C.θG_V2 E hMod hVL hV₂ hw hw1
  have hvw : v * w ∉ V₂ := fun h => hv2 (by
    have := V₂.mul_mem h (V₂.inv_mem hw)
    rwa [mul_inv_cancel_right] at this)
  have hvw1 : v * w ∉ fsuV1 T V := fun h => hvw (hV₂.1 h)
  have h32 : ∀ u ∈ V, u ∉ V₂ → C.θG e u = M755.ptQ 32 ∨ C.θG e u = M755.ptQ 40 := by
    intro u hu hu2
    rw [C.θG_eq e (hVU hu)]
    exact C.coord_V hMod hVL E.mem_T hV₂ hu hu2
  have hprod : C.θG e (v * w) = C.θG e v * M755.ptQ 8 := by
    rw [C.θG_mul e (hVU hv) (hVU hwV), hw8]
  have h8 : (8 : ℕ) ∈ o0Codes := by decide
  have h32c : (32 : ℕ) ∈ o0Codes := by decide
  have h40c : (40 : ℕ) ∈ o0Codes := by decide
  have e1 : M755.ptQ 32 * M755.ptQ 8 = M755.ptQ 40 := by rw [M755.ptQ_mul h32c h8]; rfl
  have e2 : M755.ptQ 40 * M755.ptQ 8 = M755.ptQ 32 := by rw [M755.ptQ_mul h40c h8]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨w, hwV, hw1, hw8⟩
  · rcases h32 v hv hv2 with h | h
    · exact ⟨v, hv, hv1, h⟩
    · exact ⟨v * w, V.mul_mem hv hwV, hvw1, by rw [hprod, h, e2]⟩
  · rcases h32 v hv hv2 with h | h
    · exact ⟨v * w, V.mul_mem hv hwV, hvw1, by rw [hprod, h, e1]⟩
    · exact ⟨v, hv, hv1, h⟩

theorem exists_line (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {b : ℕ} (hb : b ∈ [2, 4, 6]) :
    ∃ h ∈ K, conjSub h V₂ = V₂ ∧
      (∀ y ∈ conjSub h V, y ∉ fsuV1 T V → ∃ d ∈ M755.lineB b, d ≠ 0 ∧ C.θG e y = M755.ptQ d) ∧
      ∀ d ∈ M755.lineB b, d ≠ 0 → ∃ y ∈ conjSub h V, y ∉ fsuV1 T V ∧ C.θG e y = M755.ptQ d := by
  obtain ⟨hz1a, hz1b, hz88, hz1c, hz1d⟩ := M755.facts_z1_lines
  obtain ⟨h₁, hh₁K, hΦ₁⟩ : ∃ h₁ ∈ K, C.ΦG E h₁ = M755.z1 := by
    have : M755.z1 ∈ (K.subgroupOf (hz T V)).map (C.Φ E) := by
      rw [C.map_Φ_K E]
      exact M755.z1_mem
    obtain ⟨k, hk, hke⟩ := this
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk, by rw [C.ΦG_eq E k.2]; exact hke⟩
  have hh₁H := C.le_hz hh₁K
  have hVU := le_conjClosure V (hz T V)
  have hconj : ∀ {h : G}, h ∈ hz T V → ∀ {y : G}, y ∈ conjSub h V → y ∉ fsuV1 T V →
      ∃ d ∈ [8, 32, 40], C.θG e y = g2QAct (ZMod 2) (C.ΦG E h) (M755.ptQ d) :=
    fun hh y hy hy1 => C.θG_ln E hMod hVL hV₂ hh hy hy1
  have hcode : ∀ c ∈ [8, 32, 40, 48, 56, 16, 24], c ∈ M755.qCodes := by decide
  have hz1 : ∀ c ∈ [8, 32, 40, 48, 56, 16, 24], g2QAct (ZMod 2) M755.z1 (M755.ptQ c) =
      M755.ptQ (M755.actC 64 c) := fun c hc => M755.g2QAct_z1_code (hcode c hc)
  have hV₂fix : ∀ {h : G}, h ∈ hz T V → g2QAct (ZMod 2) (C.ΦG E h) (M755.ptQ 8) = M755.ptQ 8 →
      conjSub h V₂ = V₂ := by
    intro h hh h8
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
      obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
      by_contra hc
      push Not at hc
      have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from hc)
      rw [hV1, hV₂.2.2.2] at this
      omega
    have hhw : h * w * h⁻¹ ∉ fsuV1 T V := fun hc => hw1 (by
      have := C.conj_V1 (inv_mem hh) hc
      rw [show h⁻¹ * (h * w * h⁻¹) * h⁻¹⁻¹ = w by group] at this
      rw [this]; exact hc)
    have := C.eq_of_θG_pt E hMod hVL hV₂ hh (one_mem _) (mul_mem_conjSub hw) hhw
      (by rw [conjSub_one]; exact hw) hw1 (by
        rw [C.θG_pt E hMod hVL hV₂ hh (mul_mem_conjSub hw) hhw, h8,
          C.θG_V2 E hMod hVL hV₂ hw hw1])
    rwa [conjSub_one] at this
  have m1 : ∀ d ∈ [8, 32, 40], d ∈ [8, 32, 40, 48, 56, 16, 24] := by decide
  have m2 : ∀ d ∈ [8, 48, 56], d ∈ [8, 32, 40, 48, 56, 16, 24] := by decide
  have m3 : ∀ d ∈ [8, 16, 24], d ∈ [8, 32, 40, 48, 56, 16, 24] := by decide
  have l2 : ∀ d ∈ [8, 16, 24], d ∈ M755.lineB 2 ∧ d ≠ 0 := by decide
  have l2' : ∀ d ∈ M755.lineB 2, d ≠ 0 → d ∈ [8, 16, 24] := by decide
  have l4 : ∀ d ∈ [8, 32, 40], d ∈ M755.lineB 4 ∧ d ≠ 0 := by decide
  have l4' : ∀ d ∈ M755.lineB 4, d ≠ 0 → d ∈ [8, 32, 40] := by decide
  have l6 : ∀ d ∈ [8, 48, 56], d ∈ M755.lineB 6 ∧ d ≠ 0 := by decide
  have l6' : ∀ d ∈ M755.lineB 6, d ≠ 0 → d ∈ [8, 48, 56] := by decide
  have h8m : (8 : ℕ) ∈ [8, 32, 40, 48, 56, 16, 24] := by decide
  have hnV1 : ∀ {h : G}, h ∈ hz T V → ∀ {v : G}, v ∉ fsuV1 T V → h * v * h⁻¹ ∉ fsuV1 T V :=
    fun {h} hh {v} hv1 hc0 => hv1 (by
      have := C.conj_V1 (inv_mem hh) hc0
      rw [show h⁻¹ * (h * v * h⁻¹) * h⁻¹⁻¹ = v by group] at this
      rw [this]; exact hc0)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  ·
    have hH2 := mul_mem hh₁H hh₁H
    have hΦ2 : ∀ c ∈ [8, 32, 40], g2QAct (ZMod 2) (C.ΦG E (h₁ * h₁)) (M755.ptQ c) =
        M755.ptQ (M755.actC 64 (M755.actC 64 c)) := by
      intro c hc
      rw [C.ΦG_mul E hh₁H hh₁H, hΦ₁, map_mul, MulAut.mul_apply, hz1 c (m1 c hc),
        hz1 _ (m2 _ (hz1a c hc))]
    refine ⟨h₁ * h₁, mul_mem hh₁K hh₁K, hV₂fix hH2 (by
      rw [hΦ2 8 (by decide), hz88, hz88]), ?_, ?_⟩
    · intro y hy hy1
      obtain ⟨d, hd, hθ⟩ := hconj hH2 hy hy1
      rw [hΦ2 d hd] at hθ
      exact ⟨_, (l2 _ (hz1b _ (hz1a d hd))).1, (l2 _ (hz1b _ (hz1a d hd))).2, hθ⟩
    · intro d hd hd0
      obtain ⟨c, hc, rfl⟩ := hz1d d (l2' d hd hd0)
      obtain ⟨c', hc', rfl⟩ := hz1c c hc
      obtain ⟨v, hv, hv1, hθv⟩ := C.exists_V_θG E hMod hVL hV₂ hc'
      refine ⟨(h₁ * h₁) * v * (h₁ * h₁)⁻¹, mul_mem_conjSub hv, hnV1 hH2 hv1, ?_⟩
      rw [C.θG_conj E hH2 (hVU hv), hθv, hΦ2 c' hc']
  ·
    refine ⟨1, one_mem _, by rw [conjSub_one], ?_, ?_⟩
    · intro y hy hy1
      rw [conjSub_one] at hy
      obtain ⟨d, hd, hθ⟩ := C.θG_V E hMod hVL hV₂ hy hy1
      exact ⟨d, (l4 d hd).1, (l4 d hd).2, hθ⟩
    · intro d hd hd0
      obtain ⟨v, hv, hv1, hθv⟩ := C.exists_V_θG E hMod hVL hV₂ (l4' d hd hd0)
      exact ⟨v, by rw [conjSub_one]; exact hv, hv1, hθv⟩
  ·
    refine ⟨h₁, hh₁K, hV₂fix hh₁H (by rw [hΦ₁, hz1 8 h8m, hz88]), ?_, ?_⟩
    · intro y hy hy1
      obtain ⟨d, hd, hθ⟩ := hconj hh₁H hy hy1
      rw [hΦ₁, hz1 d (m1 d hd)] at hθ
      exact ⟨_, (l6 _ (hz1a d hd)).1, (l6 _ (hz1a d hd)).2, hθ⟩
    · intro d hd hd0
      obtain ⟨c, hc, rfl⟩ := hz1c d (l6' d hd hd0)
      obtain ⟨v, hv, hv1, hθv⟩ := C.exists_V_θG E hMod hVL hV₂ hc
      refine ⟨h₁ * v * h₁⁻¹, mul_mem_conjSub hv, hnV1 hh₁H hv1, ?_⟩
      rw [C.θG_conj E hh₁H (hVU hv), hθv, hΦ₁, hz1 c (m1 c hc)]

theorem comm_mem_line (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {b₀ : ℕ} (hb₀ : b₀ ∈ [2, 4, 6]) {h : G}
    (hhH : h ∈ hz T V)
    (hline : ∀ y ∈ conjSub h V, y ∉ fsuV1 T V →
      ∃ d ∈ M755.lineB b₀, d ≠ 0 ∧ C.θG e y = M755.ptQ d)
    (hcover : ∀ d ∈ M755.lineB b₀, d ≠ 0 →
      ∃ y ∈ conjSub h V, y ∉ fsuV1 T V ∧ C.θG e y = M755.ptQ d)
    {b : G} (hb : b ∈ hz T V) (hΦb : C.ΦG E b = sEltG b₀) {u : G}
    (hu : u ∈ conjClosure V (hz T V)) : u * b * u⁻¹ * b⁻¹ ∈ conjSub h V := by
  have hF := C.hF98
  have hb64 : b₀ < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb₀; omega
  have hUeq : conjClosure V (hz T V) = fsuU T V := C.conjClosure_eq
  have hcomm : ∀ a ∈ conjClosure V (hz T V), ∀ c ∈ conjClosure V (hz T V), a * c = c * a :=
    fun a ha c hc => F7.isElemAbelian_comm hF.F911_3 ha hc
  have hsq : ∀ a ∈ conjClosure V (hz T V), a * a = 1 := fun a ha => by
    have := F7.isElemAbelian_pow_eq_one hF.F911_3 ha
    rwa [pow_two] at this
  have hNU : ∀ {g : G}, g ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      g * a * g⁻¹ ∈ conjClosure V (hz T V) := fun {g} hg {a} ha =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hg) a).mp ha
  have hV1U : fsuV1 T V ≤ conjClosure V (hz T V) :=
    (inf_le_left : fsuV1 T V ≤ V).trans (le_conjClosure V _)
  have hV1V' := C.V1_le_conj hhH
  have htU : ∀ {g : G}, g ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      a * g * a⁻¹ * g⁻¹ ∈ conjClosure V (hz T V) := fun {g} hg {a} ha => by
    rw [show a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) by group]
    exact mul_mem ha (hNU hg (inv_mem ha))
  have hθt : ∀ {g : G}, g ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      C.θG e (a * g * a⁻¹ * g⁻¹) =
        C.θG e a * (g2QAct (ZMod 2) (C.ΦG E g) (C.θG e a))⁻¹ := fun {g} hg {a} ha => by
    rw [show a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) by group, C.θG_mul e ha (hNU hg (inv_mem ha)),
      C.θG_conj E hg (inv_mem ha), C.θG_inv e ha, map_inv]
  have hker : ∀ {g : G}, g ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      C.θG e (a * g * a⁻¹ * g⁻¹) = 1 → a * g * a⁻¹ * g⁻¹ ∈ fsuV1 T V := fun {g} hg {a} ha h1 => by
    rw [hθt hg ha, mul_inv_eq_one, ← C.θG_conj E hg ha] at h1
    have h2 := C.mem_V1_of_θG E hg ha h1.symm
    have e : a * g * a⁻¹ * g⁻¹ = (a⁻¹ * (g * a * g⁻¹))⁻¹ := by
      rw [show a * g * a⁻¹ * g⁻¹ = a * (g * a⁻¹ * g⁻¹) by group,
        hcomm a ha _ (hNU hg (inv_mem ha))]
      group
    rw [e]
    exact inv_mem h2
  set P : G → Prop := fun s => ∃ a ∈ conjClosure V (hz T V), ∃ v ∈ fsuV1 T V,
    s = a * b * a⁻¹ * b⁻¹ * v with hP
  have hPU : ∀ {s}, P s → s ∈ conjClosure V (hz T V) := by
    rintro s ⟨a, ha, v, hv, rfl⟩
    exact mul_mem (htU hb ha) (hV1U hv)
  have hPmul : ∀ {s s'}, P s → P s' → P (s * s') := by
    rintro _ _ ⟨a, ha, v, hv, rfl⟩ ⟨a', ha', v', hv', rfl⟩
    refine ⟨a * a', mul_mem ha ha', v * v', mul_mem hv hv', ?_⟩
    rw [← comm_mul_comm C.hyp hMod hb (hUeq ▸ ha) (hUeq ▸ ha')]
    have hc := hcomm _ (hV1U hv) _ (htU hb ha')
    calc a * b * a⁻¹ * b⁻¹ * v * (a' * b * a'⁻¹ * b⁻¹ * v') =
        a * b * a⁻¹ * b⁻¹ * (v * (a' * b * a'⁻¹ * b⁻¹)) * v' := by group
      _ = a * b * a⁻¹ * b⁻¹ * ((a' * b * a'⁻¹ * b⁻¹) * v) * v' := by rw [hc]
      _ = a * b * a⁻¹ * b⁻¹ * (a' * b * a'⁻¹ * b⁻¹) * (v * v') := by group
  have hPinv : ∀ {s}, P s → P s⁻¹ := by
    rintro _ ⟨a, ha, v, hv, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, v⁻¹, inv_mem hv, ?_⟩
    have h1 := comm_mul_comm C.hyp hMod hb (hUeq ▸ ha) (hUeq ▸ inv_mem ha)
    rw [mul_inv_cancel, one_mul, inv_one, mul_one, mul_inv_cancel] at h1
    have h2 : a⁻¹ * b * a⁻¹⁻¹ * b⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, mul_inv_rev, hcomm _ (inv_mem (hV1U hv)) _ (inv_mem (htU hb ha))]
  have hP1 : ∀ {s}, P s → C.θG e s = 1 → s ∈ fsuV1 T V := by
    rintro _ ⟨a, ha, v, hv, rfl⟩ h1
    rw [C.θG_mul e (htU hb ha) (hV1U hv), C.θG_eq e (hV1U hv),
      (C.θ_eq_one_iff e _).2 ((C.modMk_eq_one_iff' (hV1U hv)).2 hv ▸ Subgroup.one_mem _),
      mul_one] at h1
    exact mul_mem (hker hb ha h1) hv
  obtain ⟨y, hyK, hΦy⟩ : ∃ y ∈ K, C.ΦG E y = M755.yB b₀ := by
    have : M755.yB b₀ ∈ (K.subgroupOf (hz T V)).map (C.Φ E) := by
      rw [C.map_Φ_K E]
      exact M755.yB_mem b₀
    obtain ⟨k, hk, hke⟩ := this
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk, by rw [C.ΦG_eq E k.2]; exact hke⟩
  have hyH := C.le_hz hyK
  have hq : b⁻¹ * (y * b * y⁻¹) ∈ pCoreOf 2 (hz T V) := by
    have hm : b⁻¹ * (y * b * y⁻¹) ∈ hz T V := mul_mem (inv_mem hb) (mul_mem (mul_mem hyH hb)
      (inv_mem hyH))
    have := (C.Φ_eq_one_iff E ⟨_, hm⟩).1
    apply this
    rw [← C.ΦG_eq E hm, C.ΦG_mul E (inv_mem hb) (mul_mem (mul_mem hyH hb) (inv_mem hyH)),
      C.ΦG_mul E (mul_mem hyH hb) (inv_mem hyH), C.ΦG_mul E hyH hb, C.ΦG_inv E hyH,
      C.ΦG_inv E hb, hΦy, hΦb, M755.yB_comm hb₀]
    group
  have hQV1 : ∀ {q : G}, q ∈ pCoreOf 2 (hz T V) → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      a⁻¹ * (q * a * q⁻¹) ∈ fsuV1 T V := fun {q} hq' {a} ha => by
    have hqH := pCoreOf_le 2 _ hq'
    refine C.mem_V1_of_θG E hqH ha ?_
    rw [C.θG_conj E hqH ha, C.ΦG_eq E hqH, (C.Φ_eq_one_iff E ⟨_, hqH⟩).2 hq', map_one,
      MulAut.one_apply]
  have hPy : ∀ {s}, P s → P (y * s * y⁻¹) := by
    rintro _ ⟨a, ha, v, hv, rfl⟩
    set q := b⁻¹ * (y * b * y⁻¹) with hqdef
    set a' := y * a * y⁻¹ with ha'
    have ha'U : a' ∈ conjClosure V (hz T V) := hNU hyH ha
    have hcq := hQV1 hq ha'U
    refine ⟨a', ha'U, (b * (a' * (q * a'⁻¹ * q⁻¹)) * b⁻¹) * (y * v * y⁻¹), mul_mem ?_ ?_, ?_⟩
    · have : a' * (q * a'⁻¹ * q⁻¹) ∈ fsuV1 T V := by
        have e : a' * (q * a'⁻¹ * q⁻¹) = (a'⁻¹ * (q * a' * q⁻¹))⁻¹ := by
          rw [hcomm _ ha'U _ (hNU (pCoreOf_le 2 _ hq) (inv_mem ha'U))]
          group
        rw [e]; exact inv_mem hcq
      rw [C.conj_V1 hb this]
      exact this
    · rw [C.conj_V1 hyH hv]; exact hv
    · have hyb : y * b * y⁻¹ = b * q := by rw [hqdef]; group
      calc y * (a * b * a⁻¹ * b⁻¹ * v) * y⁻¹ =
          a' * (y * b * y⁻¹) * a'⁻¹ * (y * b * y⁻¹)⁻¹ * (y * v * y⁻¹) := by rw [ha']; group
        _ = a' * b * a'⁻¹ * b⁻¹ * ((b * (a' * (q * a'⁻¹ * q⁻¹)) * b⁻¹) * (y * v * y⁻¹)) := by
          rw [hyb]; group
  have hyV' : ∀ {x}, x ∈ conjSub h V → y * x * y⁻¹ ∈ conjSub h V := by
    have hle := C.line_le E h13322 hMod hVL hV₂ hhH (mul_mem hyH hhH) fun z hz hz1 => by
      have hz' := mem_conjSub.1 hz
      set v := (y * h)⁻¹ * z * (y * h) with hvdef
      have hv : v ∈ V := hz'
      have hzv : z = y * (h * v * h⁻¹) * y⁻¹ := by rw [hvdef]; group
      rw [hzv] at hz1 ⊢
      have hx1 : h * v * h⁻¹ ∉ fsuV1 T V := fun h' => hz1 (by
        rw [C.conj_V1 hyH h']
        exact h')
      obtain ⟨d, hd, hd0, hθ⟩ := hline _ (mul_mem_conjSub hv) hx1
      have hdc : d ∈ o0Codes := by
        have : ∀ b ∈ [2, 4, 6], ∀ d ∈ M755.lineB b, d ∈ o0Codes := by decide
        exact this b₀ hb₀ d hd
      obtain ⟨d', hd', hd'0, -, hyd⟩ := M755.yB_act hb₀ hd hd0
      obtain ⟨y₀, hy₀, hy₀1, hθ₀⟩ := hcover d' hd' hd'0
      refine ⟨y₀, hy₀, hy₀1, ?_⟩
      rw [hθ₀, C.θG_conj E hyH (hNU hhH (le_conjClosure V _ hv)), hθ, hΦy, hyd]
    intro x hx
    rw [conjSub_mul] at hle
    exact hle (mul_mem_conjSub hx)
  have hV'ker : ∀ {x}, x ∈ conjSub h V → C.θG e x = 1 → x ∈ fsuV1 T V := by
    intro x hx h1
    by_contra hx1
    obtain ⟨d, hd, hd0, hθ⟩ := hline x hx hx1
    have hdp : d ∈ M755.ptsQ := by
      have : ∀ b ∈ [2, 4, 6], ∀ d ∈ M755.lineB b, d ≠ 0 → d ∈ M755.ptsQ := by decide
      exact this b₀ hb₀ d hd hd0
    exact M755.ptQ_ne_one hdp (hθ.symm.trans h1)
  have hV'U : conjSub h V ≤ conjClosure V (hz T V) := by
    rintro _ ⟨v, hv, rfl⟩
    exact hNU hhH (le_conjClosure V _ hv)
  set t := u * b * u⁻¹ * b⁻¹ with ht
  have hPt : P t := ⟨u, hu, 1, one_mem _, by rw [mul_one]⟩
  have htU' := hPU hPt
  obtain ⟨c, hc, hcu⟩ := M755.exists_code (C.θG e u)
  have hθtc : C.θG e t = M755.ptQ (c ^^^ M755.actC b₀ c) := by
    rw [ht, hθt hb hu, ← hcu, hΦb, M755.g2QAct_sEltG_code hb64 hc,
      show ∀ q : ModQ, q⁻¹ = q from fun q => inv_eq_of_mul_eq_one_right (M755.mul_self_Q q),
      ← M755.ptQ_xor hc (M755.actC_mem _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb₀ ⊢; omega) c hc)]
  have hd₁ : (c ^^^ M755.actC b₀ c) ∈ M755.lineB b₀ := by
    rw [Nat.xor_comm]
    exact (M755.facts_B0 b₀ hb₀ c hc).1
  by_cases hd₁0 : (c ^^^ M755.actC b₀ c) = 0
  · exact hV1V' (hP1 hPt (by rw [hθtc, hd₁0, M755.ptQ_zero]))
  set d₁ := c ^^^ M755.actC b₀ c with hd₁def
  obtain ⟨x₂, hx₂, -, hθx₂⟩ := hcover d₁ hd₁ hd₁0
  obtain ⟨hsq₁, hd₂c, hd₁₂, hd₁c⟩ := M755.facts_yB_sq b₀ hb₀ d₁ hd₁ hd₁0
  set d₂ := M755.nq (mact (M755.wMatC (M755.yW b₀)) d₁) with hd₂def
  have hyq : ∀ {x}, x ∈ conjClosure V (hz T V) → C.θG e x = M755.ptQ d₁ →
      C.θG e (y * x * y⁻¹) = M755.ptQ d₂ := fun hx h1 => by
    rw [C.θG_conj E hyH hx, h1, hΦy, M755.g2QAct_yB hb₀ hd₁c]
  have hyq' : ∀ {x}, x ∈ conjClosure V (hz T V) → C.θG e x = M755.ptQ d₂ →
      C.θG e (y * x * y⁻¹) = M755.ptQ (d₁ ^^^ d₂) := fun hx h1 => by
    rw [C.θG_conj E hyH hx, h1, hΦy, M755.g2QAct_yB hb₀ hd₂c, hsq₁]
  set t₁ := y * t * y⁻¹
  set t₂ := y * t₁ * y⁻¹
  set x₂' := y * x₂ * y⁻¹
  set x₂'' := y * x₂' * y⁻¹
  have hPt₁ : P t₁ := hPy hPt
  have hPt₂ : P t₂ := hPy hPt₁
  have hx₂' : x₂' ∈ conjSub h V := hyV' hx₂
  have hx₂'' : x₂'' ∈ conjSub h V := hyV' hx₂'
  have hθt₁ : C.θG e t₁ = M755.ptQ d₂ := hyq htU' (hθtc.trans rfl)
  have hθt₂ : C.θG e t₂ = M755.ptQ (d₁ ^^^ d₂) := hyq' (hPU hPt₁) hθt₁
  have hθx₂' : C.θG e x₂' = M755.ptQ d₂ := hyq (hV'U hx₂) hθx₂
  have hθx₂'' : C.θG e x₂'' = M755.ptQ (d₁ ^^^ d₂) := hyq' (hV'U hx₂') hθx₂'
  have hptQmul : M755.ptQ d₁ * M755.ptQ d₂ = M755.ptQ (d₁ ^^^ d₂) :=
    M755.ptQ_mul hd₁c hd₂c
  have h1 : (t * t₁)⁻¹ * t₂ ∈ fsuV1 T V := by
    refine hP1 (hPmul (hPinv (hPmul hPt hPt₁)) hPt₂) ?_
    rw [C.θG_mul e (inv_mem (mul_mem htU' (hPU hPt₁))) (hPU hPt₂),
      C.θG_inv e (mul_mem htU' (hPU hPt₁)), C.θG_mul e htU' (hPU hPt₁), hθtc, hθt₁, hθt₂]
    rw [hptQmul, inv_mul_cancel]
  have h2 : (x₂ * x₂')⁻¹ * x₂'' ∈ fsuV1 T V := by
    refine hV'ker (mul_mem (inv_mem (mul_mem hx₂ hx₂')) hx₂'') ?_
    rw [C.θG_mul e (inv_mem (mul_mem (hV'U hx₂) (hV'U hx₂'))) (hV'U hx₂''),
      C.θG_inv e (mul_mem (hV'U hx₂) (hV'U hx₂')), C.θG_mul e (hV'U hx₂) (hV'U hx₂'), hθx₂,
      hθx₂', hθx₂'', hptQmul, inv_mul_cancel]
  set δ := t⁻¹ * x₂ with hδ
  have hδU : δ ∈ conjClosure V (hz T V) := mul_mem (inv_mem htU') (hV'U hx₂)
  have hθδ : C.θG e δ = 1 := by
    rw [C.θG_mul e (inv_mem htU') (hV'U hx₂), C.θG_inv e htU', hθtc, hθx₂, inv_mul_cancel]
  have hθδ₁ : C.θG e (y * δ * y⁻¹) = C.θG e δ := by
    rw [C.θG_conj E hyH hδU, hθδ, map_one]
  have hδ₁ := C.mem_V1_of_θG E hyH hδU hθδ₁
  have hδ₁U : y * δ * y⁻¹ ∈ conjClosure V (hz T V) := hNU hyH hδU
  have hθδ₂ : C.θG e (y * (y * δ * y⁻¹) * y⁻¹) = C.θG e (y * δ * y⁻¹) := by
    rw [C.θG_conj E hyH hδ₁U, hθδ₁, hθδ, map_one]
  have hδ₂ := C.mem_V1_of_θG E hyH hδ₁U hθδ₂
  have hrel : (t * t₁)⁻¹ * (x₂ * x₂') = δ * (y * δ * y⁻¹) := by
    have e1 : y * δ * y⁻¹ = t₁⁻¹ * x₂' := by
      show y * (t⁻¹ * x₂) * y⁻¹ = (y * t * y⁻¹)⁻¹ * (y * x₂ * y⁻¹)
      group
    calc (t * t₁)⁻¹ * (x₂ * x₂') = t₁⁻¹ * t⁻¹ * x₂ * x₂' := by group
      _ = t⁻¹ * t₁⁻¹ * x₂ * x₂' := by rw [hcomm _ (inv_mem (hPU hPt₁)) _ (inv_mem htU')]
      _ = t⁻¹ * (t₁⁻¹ * x₂) * x₂' := by group
      _ = t⁻¹ * (x₂ * t₁⁻¹) * x₂' := by rw [hcomm _ (inv_mem (hPU hPt₁)) _ (hV'U hx₂)]
      _ = (t⁻¹ * x₂) * (t₁⁻¹ * x₂') := by group
      _ = δ * (y * δ * y⁻¹) := by rw [e1]
  have hrel2 : t₂⁻¹ * x₂'' = y * (y * δ * y⁻¹) * y⁻¹ := by
    show (y * (y * t * y⁻¹) * y⁻¹)⁻¹ * (y * (y * x₂ * y⁻¹) * y⁻¹) =
      y * (y * (t⁻¹ * x₂) * y⁻¹) * y⁻¹
    group
    rw [zpow_two]
  have hx₂U := hV'U hx₂
  have hx₂'U := hV'U hx₂'
  have hx₂''U := hV'U hx₂''
  have ht₁U := hPU hPt₁
  have ht₂U := hPU hPt₂
  have h3 : (δ * (y * δ * y⁻¹))⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹) ∈ fsuV1 T V := by
    rw [← hrel, ← hrel2]
    have e2 : ((t * t₁)⁻¹ * (x₂ * x₂'))⁻¹ * (t₂⁻¹ * x₂'') =
        ((t * t₁)⁻¹ * t₂)⁻¹ * ((x₂ * x₂')⁻¹ * x₂'') := by
      have hPx := inv_mem (mul_mem hx₂U hx₂'U)
      have hQt := mul_mem (mul_mem htU' ht₁U) (inv_mem ht₂U)
      calc ((t * t₁)⁻¹ * (x₂ * x₂'))⁻¹ * (t₂⁻¹ * x₂'') =
          (x₂ * x₂')⁻¹ * ((t * t₁) * t₂⁻¹) * x₂'' := by group
        _ = ((t * t₁) * t₂⁻¹) * (x₂ * x₂')⁻¹ * x₂'' := by rw [hcomm _ hPx _ hQt]
        _ = (t₂⁻¹ * (t * t₁)) * (x₂ * x₂')⁻¹ * x₂'' := by
          rw [hcomm _ (mul_mem htU' ht₁U) _ (inv_mem ht₂U)]
        _ = ((t * t₁)⁻¹ * t₂)⁻¹ * ((x₂ * x₂')⁻¹ * x₂'') := by group
    rw [e2]
    exact mul_mem (inv_mem h1) h2
  have hδ₂U : y * (y * δ * y⁻¹) * y⁻¹ ∈ conjClosure V (hz T V) := hNU hyH hδ₁U
  have h4 : δ⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹) ∈ fsuV1 T V := by
    have e3 : δ⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹) =
        (δ⁻¹ * (y * δ * y⁻¹)) * ((y * δ * y⁻¹)⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹)) := by group
    rw [e3]
    exact mul_mem hδ₁ hδ₂
  have h7 : (y * δ * y⁻¹)⁻¹ ∈ fsuV1 T V := by
    have e4 : (y * δ * y⁻¹)⁻¹ = (δ⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹))⁻¹ *
        ((δ * (y * δ * y⁻¹))⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹)) := by
      calc (y * δ * y⁻¹)⁻¹ = (y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹) *
            (y * δ * y⁻¹)⁻¹ := by group
        _ = ((y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * (y * δ * y⁻¹)⁻¹) * (y * (y * δ * y⁻¹) * y⁻¹) := by
          rw [mul_assoc, hcomm _ hδ₂U _ (inv_mem hδ₁U), ← mul_assoc]
        _ = (y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * (δ * δ⁻¹) * (y * δ * y⁻¹)⁻¹ *
            (y * (y * δ * y⁻¹) * y⁻¹) := by group
        _ = (y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * δ * ((y * δ * y⁻¹)⁻¹ * δ⁻¹) *
            (y * (y * δ * y⁻¹) * y⁻¹) := by
          rw [show (y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * (δ * δ⁻¹) * (y * δ * y⁻¹)⁻¹ =
            (y * (y * δ * y⁻¹) * y⁻¹)⁻¹ * δ * (δ⁻¹ * (y * δ * y⁻¹)⁻¹) by group,
            hcomm _ (inv_mem hδU) _ (inv_mem hδ₁U)]
        _ = (δ⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹))⁻¹ *
            ((δ * (y * δ * y⁻¹))⁻¹ * (y * (y * δ * y⁻¹) * y⁻¹)) := by group
    rw [e4]
    exact mul_mem (inv_mem h4) h3
  have hkey : δ ∈ fsuV1 T V := by
    have e5 : δ = (y * δ * y⁻¹) * (δ⁻¹ * (y * δ * y⁻¹))⁻¹ := by group
    rw [e5]
    exact mul_mem ((inv_mem_iff).1 h7) (inv_mem hδ₁)
  have : t = x₂ * δ⁻¹ := by simp only [hδ]; group
  rw [this]
  exact mul_mem hx₂ (hV1V' (inv_mem hkey))

end Ctx753

end CFSG.Quasithin.H13.L32A
