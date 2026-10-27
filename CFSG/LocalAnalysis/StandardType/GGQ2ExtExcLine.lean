module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtExc

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open CFSG CFSG.Assembly Module

variable {m : Fin 6} {T : Chk.Tabs}

private theorem nat_all_iff' {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h x _
    exact h x.val x.isLt

private theorem scanN_of_scanLineN {ext q2 : Bool} {S : Chk.Search} {body : ℕ → ℕ → Bool}
    {c₀ : ℕ} (h : Chk.scanLineN T m ext q2 S body c₀ = true) :
    Chk.scanN T m ext q2 S (fun cv cy => !(cv == c₀) || body cv cy) = true := by
  simp only [Chk.scanN]
  rw [nat_all_iff']
  intro cv _
  by_cases hc : cv = c₀
  · subst hc
    simp only [Chk.scanLineN] at h
    simpa only [beq_self_eq_true, Bool.not_true, Bool.false_or] using h
  · rw [Bool.or_eq_true]
    right
    rw [nat_all_iff']
    intro cy _
    simp [beq_false_of_ne hc]

theorem scanLineN_sound (hT : Chk.tabsOK m T = true) {ext q2 : Bool} {S : Chk.Search}
    {body : ℕ → ℕ → Bool} {vx : V m} (h : Chk.scanLineN T m ext q2 S body (code m vx) = true)
    {ℓ : Finset (Root m)} (hℓ : LineHyp m ext q2 vx ℓ) {U : Submodule (ZMod 3) (V m)}
    (hU : finrank (ZMod 3) U = 2) (hxU : vx ∈ U) {j : Finset (Root m)} (hj : PlaneHyp m U j) :
    ∃ cv cy : ℕ, cv < 3 ^ dim m ∧ cy < 3 ^ dim m ∧ vx = vec m cv ∧
      vec m cy ∉ Submodule.span (ZMod 3) {vec m cv} ∧
      U = Submodule.span (ZMod 3) {vec m cv, vec m cy} ∧ ℓ = ofMask m (T.zm[cv]!) ∧
      j = ofMask m (T.zm[cv]! &&& T.zm[cy]!) ∧ body cv cy = true := by
  obtain ⟨cv, cy, hcv, hcy, hvx, hnot, hUeq, hℓeq, hjeq, hb⟩ :=
    scanN_sound hT (scanN_of_scanLineN h) hℓ hU hxU hj
  have hc : cv = code m vx := by
    rw [hvx, code_vec m hcv]
  refine ⟨cv, cy, hcv, hcy, hvx, hnot, hUeq, hℓeq, hjeq, ?_⟩
  simpa [hc] using hb

theorem extCasesVx_of_scanLineN (hT : Chk.tabsOK m T = true) {S : Chk.Search}
    {X : ℕ → ℕ → ℕ → ℕ → Chk.ExtWit} {vx : V m}
    (h : Chk.scanLineN T m true true S (fun cv cy =>
      Chk.candScanN T m S cv cy fun a b =>
        Chk.extWitOK T m cv cy (Chk.combN (dim m) cv cy a b) (X cv cy a b)) (code m vx) = true) :
    ExtCasesVx (excRaw m) vx := by
  intro hvx0 ℓ hadm hq hocc hcent hvxin U hU hvxU j hadmj hjocc hjcent hins hnorm z hzU hzvx k
    hcand hinsk
  have hℓ : LineHyp m true true vx ℓ :=
    ⟨hvx0, hadm, fun _ => hq, hocc, hcent,
      ⟨fun h => absurd h hvxin, fun h => by simp at h⟩⟩
  have hj : PlaneHyp m U j := ⟨hadmj, hjocc, hjcent⟩
  obtain ⟨cv, cy, hcv, hcy, hvx, -, hUeq, hℓeq, hjeq, hbody⟩ :=
    scanLineN_sound hT h hℓ hU hvxU hj
  subst vx
  have hzspan : z ∈ Submodule.span (ZMod 3) {vec m cv, vec m cy} := by
    rw [← hUeq]
    exact hzU
  have hk : CandHyp m (vec m cv) z k := candHyp_of_candidate hcand
  obtain ⟨a, b, -, -, hz, hkeq, hext⟩ :=
    candScanN_sound hT hbody hcv hcy hzspan hzvx hk
  subst z
  subst k
  subst ℓ
  subst j
  exact extOutcome_of_extWitOK hT hext

end CFSG.StandardType.GGQ2Frame.ExcRaw
