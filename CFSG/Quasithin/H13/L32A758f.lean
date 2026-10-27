module

public import CFSG.Quasithin.H13.L32A758e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace M755

theorem line_inter : ∀ c ∈ [2, 4, 6], ∀ c' ∈ [2, 4, 6], c ≠ c' → ∀ d ∈ lineB c, d ∈ lineB c' →
    d = 0 ∨ d = 8 := by
  decide +kernel

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem mem_V2 (C : Ctx753 T L V K) (hMod : StmtL32NModule) {V₂ : Subgroup G}
    (hV₂ : A6.IsV2 T V V₂) {z w₀ : G} (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1) (hw₀ : w₀ ∈ V₂)
    (hw₀1 : w₀ ∉ fsuV1 T V) {v : G} (hv : v ∈ V₂) : v = 1 ∨ v = z ∨ v = w₀ ∨ v = z * w₀ := by
  obtain ⟨hVe, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨hV₁V₂, hV₂V, -, hV₂4⟩ := hV₂
  by_cases hvV1 : v ∈ fsuV1 T V
  · rcases M755.eq_one_or_eq_of_card_two C.card_V1 hz1 hzne hvV1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hwv := inv_mul_mem_of_two hV₁V₂ (by rw [hV1, hV₂4]) hw₀ hv hw₀1 hvV1
    rcases M755.eq_one_or_eq_of_card_two C.card_V1 hz1 hzne hwv with h | h
    · right; right; left
      rw [inv_mul_eq_one] at h
      exact h.symm
    · right; right; right
      have e : v = w₀ * z := by rw [← h]; group
      have : IsMulCommutative ↥V := hVe.1
      rw [e]
      exact setLike_mul_comm (hV₂V hw₀) ((inf_le_left : fsuV1 T V ≤ V) hz1)

theorem exists_pt_of_line (C : Ctx753 T L V K) (h13322 : Stmt13_3_2_two)
    (hMod : StmtL32NModule) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {h f g' : G}
    (hf : f ∈ conjSub h V) (hg : g' ∈ conjSub h V) (hf1 : f ≠ 1) (hg1 : g' ≠ 1) (hfg : f ≠ g') :
    ∃ l ∈ L, (∀ t ∈ conjSub (h * l) V₂, t = 1 ∨ t = f ∨ t = g' ∨ t = f * g') ∧
      f ∈ conjSub (h * l) V₂ ∧ g' ∈ conjSub (h * l) V₂ ∧ conjSub (h * l) V₂ ≤ conjSub h V := by
  have h1281 := C.hyp.hyp1281One h13322 hMod
  obtain ⟨-, -, hLTV, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨z, hz1, hzne⟩ := C.exists_V1_ne
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from hcon)
    rw [hV1, hV₂.2.2.2] at this
    omega
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hz1
  have hw₀V : w₀ ∈ V := hV₂.2.1 hw₀
  have hzw : z ≠ w₀ := fun e => hw₀1 (e ▸ hz1)
  have hw₀ne : w₀ ≠ 1 := fun e => hw₀1 (e ▸ one_mem _)
  have hf' : h⁻¹ * f * h ∈ V := mem_conjSub.1 hf
  have hg' : h⁻¹ * g' * h ∈ V := mem_conjSub.1 hg
  have hf'1 : h⁻¹ * f * h ≠ 1 := fun e => hf1 (by
    have := congrArg (fun t => h * t * h⁻¹) e
    simpa [mul_assoc] using this)
  have hg'1 : h⁻¹ * g' * h ≠ 1 := fun e => hg1 (by
    have := congrArg (fun t => h * t * h⁻¹) e
    simpa [mul_assoc] using this)
  have hfg' : h⁻¹ * f * h ≠ h⁻¹ * g' * h := fun e => hfg (by
    have := congrArg (fun t => h * t * h⁻¹) e
    simpa [mul_assoc] using this)
  obtain ⟨l, hlL, hl1, hl2⟩ := exists_conj_eq_pair h1281 hzV hw₀V hf' hg' hzne hw₀ne hf'1 hg'1
    hzw hfg'
  have hlz : (h * l) * z * (h * l)⁻¹ = f := by
    calc (h * l) * z * (h * l)⁻¹ = h * (l * z * l⁻¹) * h⁻¹ := by group
      _ = f := by rw [hl1]; group
  have hlw : (h * l) * w₀ * (h * l)⁻¹ = g' := by
    calc (h * l) * w₀ * (h * l)⁻¹ = h * (l * w₀ * l⁻¹) * h⁻¹ := by group
      _ = g' := by rw [hl2]; group
  refine ⟨l, hlL, fun t ht => ?_, ?_, ?_, fun t ht => ?_⟩
  · have hv := mem_conjSub.1 ht
    have e : t = (h * l) * ((h * l)⁻¹ * t * (h * l)) * (h * l)⁻¹ := by group
    rcases C.mem_V2 hMod hV₂ hz1 hzne hw₀ hw₀1 hv with hv' | hv' | hv' | hv' <;> rw [e, hv']
    · left; group
    · right; left; exact hlz
    · right; right; left; exact hlw
    · right; right; right
      rw [← hlz, ← hlw]
      group
  · rw [← hlz]
    exact mul_mem_conjSub ((hV₂.1) hz1)
  · rw [← hlw]
    exact mul_mem_conjSub hw₀
  · have hv := mem_conjSub.1 ht
    rw [mem_conjSub]
    have e : h⁻¹ * t * h = l * ((h * l)⁻¹ * t * (h * l)) * l⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp ((le_sup_left : L ≤ L ⊔ T).trans hLTV hlL) _).mp
      (hV₂.2.1 hv)

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem mem_V2_of_line (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {c : ℕ} (hc : c ∈ [2, 4, 6]) {h : G} (hhH : h ∈ hz T V) (hhV₂ : conjSub h V₂ = V₂)
    (hline : ∀ y ∈ conjSub h V, y ∉ fsuV1 T V →
      ∃ d ∈ M755.lineB c, d ≠ 0 ∧ C.θG e y = M755.ptQ d)
    {t : G} (ht : t ∈ conjSub h V) (hθ : C.θG e t = M755.ptQ 8) : t ∈ V₂ := by
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
  have htU : t ∈ conjClosure V (hz T V) := by
    obtain ⟨v, hv, rfl⟩ := ht
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hhH) v).mp
      (le_conjClosure V _ hv)
  have htw : t * w⁻¹ ∈ fsuV1 T V := by
    by_contra hnot
    obtain ⟨d', hd', hd'0, hθ'⟩ := hline _ (mul_mem ht (inv_mem hwVh)) hnot
    rw [C.θG_mul e htU (inv_mem hwU), C.θG_inv e hwU, hθ, C.θG_V2 E hMod hVL hV₂ hw hw1,
      mul_inv_cancel] at hθ'
    exact M755.ptQ_ne_one (M755.line_facts.2.2.1 c hc d' hd' hd'0) hθ'.symm
  have e1 : t = (t * w⁻¹) * w := by group
  rw [e1]
  exact mul_mem (hV₂.1 htw) hw

theorem false_of_data
    (C : Ctx753 T L V K) {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ}
    (E : Coord C e) (hG : M755.G2Facts) (h38 : Lemma14_7_38) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G}
    (hV₂ : A6.IsV2 T V V₂) (h13314 : A6.Stmt13_3_14) (h1222 : Stmt12_2_2)
    {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) : False := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨-, -, -, k₁, -, N₁, hA0₁⟩ := C.exists_A0' E hG h13322 hMod hVL hV₂ h13314 h1222 N
  obtain ⟨δ, δ', k₂, h₀, y, N₂, hyU, hyU₂, -, -, hyV1, hyV1₂⟩ :=
    N₁.exists_sym_of_eq C (C.heq_of E hG h13322 hMod hVL hV₂ h13314 h1222 N₁)
  obtain ⟨l₂, -, hl₂H, h₀', hh₀', N₃, hA0₃⟩ :=
    C.exists_A0' E hG h13322 hMod hVL hV₂ h13314 h1222 N₂
  set x := (k₁ : G) * g with hx
  set x₃ := (h₀' : G) * k₂ with hx₃
  obtain ⟨y', hy'⟩ : ∃ y' : G, y' = y * l₂⁻¹ := ⟨_, rfl⟩
  have hHU : conjSub l₂⁻¹ (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ (inv_mem hl₂H))
  have hHV1 : conjSub l₂⁻¹ (fsuV1 T V) = fsuV1 T V :=
    conjSub_eq_self_iff.mpr (C.hF98.H_normalizes_V₁ (inv_mem hl₂H))
  have hyx : y' * x₃ = y * ((h₀ : G) * k₂) := by rw [hy', hx₃, hh₀']; group
  have hR1 : conjSub y' (conjClosure V (hz T V)) = conjSub x (conjClosure V (hz T V)) := by
    rw [hy', conjSub_mul, hHU, hyU]
  have hR2 : conjSub y' (conjSub x₃ (conjClosure V (hz T V))) = conjClosure V (hz T V) := by
    rw [← conjSub_mul, hyx, conjSub_mul, hyU₂]
  have hR3 : conjSub y' (fsuV1 T V) = conjSub x (fsuV1 T V) := by
    rw [hy', conjSub_mul, hHV1, hyV1]
  have hV1α := C.not_V1_le E hG h1332 h1334 hVL hV₂ h13314 h1222 N₁
  have hZU := C.not_zα_le E hG h1332 h1334 hVL hV₂ h13314 h1222 N₁
  have hV1α₃ := C.not_V1_le E hG h1332 h1334 hVL hV₂ h13314 h1222 N₃
  obtain ⟨z, hz1, hzne⟩ := C.exists_V1_ne
  have hUH : conjClosure V (hz T V) ≤ hz T V :=
    C.hF98.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hZα1 : ∀ t ∈ conjSub x (fsuV1 T V), t ∈ conjClosure V (hz T V) → t = 1 := by
    intro t ht htU
    rcases C.mem_zα hz1 hzne ht with h1 | h1
    · exact h1
    · exfalso
      apply hZU
      intro t' ht'
      rcases C.mem_zα hz1 hzne ht' with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2, ← h1]; exact htU
  obtain ⟨h₁, hh₁H, hh₁V₂, hline₁, f₁, hf₁, hθf₁, g₁, hg₁, hθg₁, hstr₁, c₁, hc₁, h'₁, hh'₁H,
    hh'₁V₂, hline'₁, hcover'₁, hy₁⟩ := C.lineData E h38 h13322 hMod hVL hV₂ N₁ hA0₁ hV1α N₃ hA0₃
      hV1α₃ hR1 hR2 (c := 2) (by decide)
  obtain ⟨h₂, hh₂H, hh₂V₂, hline₂, f₂, hf₂, hθf₂, g₂, hg₂, hθg₂, hstr₂, c₂, hc₂, h'₂, hh'₂H,
    hh'₂V₂, hline'₂, hcover'₂, hy₂⟩ := C.lineData E h38 h13322 hMod hVL hV₂ N₁ hA0₁ hV1α N₃ hA0₃
      hV1α₃ hR1 hR2 (c := 4) (by decide)
  have hV'U : ∀ {h t : G}, h ∈ hz T V → t ∈ conjSub h V → t ∈ conjClosure V (hz T V) :=
    fun {h t} hh ht => by
      obtain ⟨v, hv, rfl⟩ := ht
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hh) v).mp
        (le_conjClosure V _ hv)
  have hf₁V₂ := C.mem_V2_of_line E hMod hVL hV₂ (by decide) hh₁H hh₁V₂ hline₁ hf₁.1 hθf₁
  have hf₂V₂ := C.mem_V2_of_line E hMod hVL hV₂ (by decide) hh₂H hh₂V₂ hline₂ hf₂.1 hθf₂
  have hV1αt : ∀ t ∈ fsuV1 T V, t ∈ conjSub x (conjClosure V (hz T V)) → t = 1 := by
    intro t ht htα
    by_contra ht1
    apply hV1α
    intro v hv
    rcases M755.eq_one_or_eq_of_card_two C.card_V1 ht ht1 hv with rfl | rfl
    · exact one_mem _
    · exact htα
  have hff : f₁ = f₂ := by
    have hm : f₁⁻¹ * f₂ ∈ V₂ := mul_mem (inv_mem hf₁V₂) hf₂V₂
    have hmU := le_conjClosure V (hz T V) (hV₂.2.1 hm)
    have hθm : C.θG e (f₁⁻¹ * f₂) = 1 := by
      rw [C.θG_mul e (inv_mem (hV'U hh₁H hf₁.1)) (hV'U hh₂H hf₂.1),
        C.θG_inv e (hV'U hh₁H hf₁.1), hθf₁, hθf₂, inv_mul_cancel]
    have hm1 : f₁⁻¹ * f₂ ∈ fsuV1 T V := by
      by_contra hnot
      rw [C.θG_V2 E hMod hVL hV₂ hm hnot] at hθm
      exact M755.ptQ_ne_one (by decide) hθm
    have := hV1αt _ hm1 (mul_mem (inv_mem hf₁.2) hf₂.2)
    rwa [inv_mul_eq_one] at this
  subst hff
  set f := f₁ with hfdef
  have h8 : (8 : ℕ) ∈ M755.ptsQ := by decide
  have hf1 : f ≠ 1 := fun h1 => M755.ptQ_ne_one h8 (by rw [← hθf₁, h1, C.θG_V1 e (one_mem _)])
  have hfU : f ∈ conjClosure V (hz T V) := hV'U hh₁H hf₁.1
  have hconjU : ∀ {a}, a ∈ conjSub x (conjClosure V (hz T V)) →
      y'⁻¹ * a * y' ∈ conjClosure V (hz T V) := fun {a} ha => by
    rw [← hR1] at ha
    exact mem_conjSub.1 ha
  have hconjα : ∀ {u}, u ∈ conjClosure V (hz T V) →
      y'⁻¹ * u * y' ∈ conjSub x₃ (conjClosure V (hz T V)) := fun {u} hu => by
    rw [← hR2] at hu
    exact mem_conjSub.1 hu
  have hf'V1 : y'⁻¹ * f * y' ∉ fsuV1 T V := by
    intro h1
    have h2 : f ∈ conjSub x (fsuV1 T V) := by
      rw [← hR3]
      have := mul_mem_conjSub (g := y') h1
      rwa [show y' * (y'⁻¹ * f * y') * y'⁻¹ = f by group] at this
    exact hf1 (hZα1 f h2 hfU)
  obtain ⟨-, hinj₃, -⟩ := C.F_facts E h13322 hMod hVL hV₂ N₃ hA0₃ hV1α₃ hc₁ hh'₁H hline'₁
    hcover'₁
  have hf'V₂ : y'⁻¹ * f * y' ∈ V₂ := by
    obtain ⟨d₁, hd₁, hd₁0, hθd₁⟩ := hline'₁ _ (hy₁ f hf₁) hf'V1
    obtain ⟨d₂, hd₂, hd₂0, hθd₂⟩ := hline'₂ _ (hy₂ f hf₂) hf'V1
    by_cases hcc : c₁ = c₂
    ·
      exfalso
      subst hcc
      have hle := C.line_le E h13322 hMod hVL hV₂ hh'₁H hh'₂H fun t ht ht1 => by
        obtain ⟨d, hd, hd0, hθd⟩ := hline'₂ t ht ht1
        obtain ⟨t₀, ht₀, ht₀1, hθt₀⟩ := hcover'₁ d hd hd0
        exact ⟨t₀, ht₀, ht₀1, hθt₀.trans hθd.symm⟩
      have hg₁' := hy₁ g₁ hg₁
      have hg₂' := hle (hy₂ g₂ hg₂)
      have hf' := hy₁ f hf₁
      have hfα := hconjα hfU
      have hg₁α := hconjα (hV'U hh₁H hg₁.1)
      have hg₂α := hconjα (hV'U hh₂H hg₂.1)
      obtain ⟨hdc, hdc0, hdc8, hdcl, -⟩ := M755.dc_facts c₁ hc₁
      have hdcO : M755.dc c₁ ∈ o0Codes :=
        (M755.qCodes_mem _ (M755.line_facts.2.2.2 c₁ hc₁ _ hdc)).1
      have h8O : (8 : ℕ) ∈ o0Codes := by decide
      have hval : ∀ t ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)), t ∉ fsuV1 T V →
          C.θG e t = M755.ptQ 8 ∨ C.θG e t = M755.ptQ (M755.dc c₁) ∨
            C.θG e t = M755.ptQ 8 * M755.ptQ (M755.dc c₁) := by
        intro t ht ht1
        obtain ⟨d, hd, hd0, hθd⟩ := hline'₁ t ht.1 ht1
        rw [hθd]
        rcases hdcl d hd with rfl | rfl | rfl | rfl
        · exact absurd rfl hd0
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (M755.ptQ_mul h8O hdcO).symm)
      have hnV1 : ∀ {a}, a ∈ conjClosure V (hz T V) → a ≠ 1 →
          y'⁻¹ * a * y' ∉ fsuV1 T V := by
        intro a ha ha1 h1
        apply ha1
        have h3 : y'⁻¹ * a * y' = 1 := by
          by_contra hne
          apply hV1α₃
          intro v hv
          rcases M755.eq_one_or_eq_of_card_two C.card_V1 h1 hne hv with rfl | rfl
          · exact one_mem _
          · exact hconjα ha
        have := congrArg (fun t => y' * t * y'⁻¹) h3
        simpa [mul_assoc] using this
      have hg₁1 : g₁ ≠ 1 := fun h1 => M755.ptQ_ne_one (c := M755.dc 2) (by decide) (by
        rw [← hθg₁, h1, C.θG_V1 e (one_mem _)])
      have hg₂1 : g₂ ≠ 1 := fun h1 => M755.ptQ_ne_one (c := M755.dc 4) (by decide) (by
        rw [← hθg₂, h1, C.θG_V1 e (one_mem _)])
      have hθne : ∀ {a b : G}, C.θG e a ≠ C.θG e b → a ≠ b := fun {a b} h hab => h (hab ▸ rfl)
      have hconj_ne : ∀ {a b : G}, a ≠ b → y'⁻¹ * a * y' ≠ y'⁻¹ * b * y' := fun {a b} h hab =>
        h (by simpa using hab)
      have hfg₁ : f ≠ g₁ := hθne (by
        rw [hθf₁, hθg₁]
        exact fun h => absurd (M755.ptQ_injective h8 (by decide) h) (by decide))
      have hfg₂ : f ≠ g₂ := hθne (by
        rw [hθf₁, hθg₂]
        exact fun h => absurd (M755.ptQ_injective h8 (by decide) h) (by decide))
      have hg₁g₂ : g₁ ≠ g₂ := hθne (by
        rw [hθg₁, hθg₂]
        exact fun h => absurd (M755.ptQ_injective (by decide) (by decide) h) (by decide))
      have hθinj : ∀ {a b : G}, a ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) →
          b ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) → a ≠ b →
          C.θG e a ≠ C.θG e b := fun {a b} ha hb hab hθ => hab (hinj₃ a ha b hb hθ)
      have hm₀ : y'⁻¹ * f * y' ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) :=
        ⟨hf', hfα⟩
      have hm₁ : y'⁻¹ * g₁ * y' ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) :=
        ⟨hg₁', hg₁α⟩
      have hm₂ : y'⁻¹ * g₂ * y' ∈ conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) :=
        ⟨hg₂', hg₂α⟩
      have h3 := M755.three_of_span (hval _ hm₀ (hnV1 hfU hf1))
        (hval _ hm₁ (hnV1 (hV'U hh₁H hg₁.1) hg₁1)) (hval _ hm₂ (hnV1 (hV'U hh₂H hg₂.1) hg₂1))
        (hθinj hm₀ hm₁ (hconj_ne hfg₁))
        (hθinj hm₀ hm₂ (hconj_ne hfg₂)) (hθinj hm₁ hm₂ (hconj_ne hg₁g₂))
      have hm₀₁ : y'⁻¹ * f * y' * (y'⁻¹ * g₁ * y') ∈
          conjSub h'₁ V ⊓ conjSub x₃ (conjClosure V (hz T V)) := mul_mem hm₀ hm₁
      rw [← C.θG_mul e (hV'U hh'₁H hf') (hV'U hh'₁H hg₁')] at h3
      have h4 := hinj₃ _ hm₀₁ _ hm₂ h3
      have h5 : f * g₁ = g₂ := by
        have := congrArg (fun t => y' * t * y'⁻¹) h4
        simpa [mul_assoc] using this
      have h6 := congrArg (C.θG e) h5
      rw [C.θG_mul e hfU (hV'U hh₁H hg₁.1), hθf₁, hθg₁, hθg₂, M755.ptQ_mul h8O (by decide)] at h6
      exact absurd (M755.ptQ_injective (by decide) (by decide) h6) (by decide)
    ·
      have hdd : d₁ = d₂ := M755.ptQ_injective (M755.line_facts.2.2.1 c₁ hc₁ d₁ hd₁ hd₁0)
        (M755.line_facts.2.2.1 c₂ hc₂ d₂ hd₂ hd₂0) (hθd₁.symm.trans hθd₂)
      subst hdd
      rcases M755.line_inter c₁ hc₁ c₂ hc₂ hcc d₁ hd₁ hd₂ with h0 | h0
      · exact absurd h0 hd₁0
      · rw [h0] at hθd₁
        exact C.mem_V2_of_line E hMod hVL hV₂ hc₁ hh'₁H hh'₁V₂ hline'₁ (hy₁ f hf₁) hθd₁
  have hfX₁ : f ∈ conjSub y' V₂ := by
    have := mul_mem_conjSub (g := y') hf'V₂
    rwa [show y' * (y'⁻¹ * f * y') * y'⁻¹ = f by group] at this
  have h1281 := C.hyp.hyp1281One h13322 hMod
  have hfV : f ∈ V := hV₂.2.1 hf₁V₂
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hz1
  have hfV1 : f ∉ fsuV1 T V := fun h1 => M755.ptQ_ne_one h8 (by rw [← hθf₁, C.θG_V1 e h1])
  have hfz : f ≠ z := fun h1 => hfV1 (h1 ▸ hz1)
  obtain ⟨lβ, -, hlβ, -⟩ := exists_conj_eq_pair h1281 hzV hfV hfV hzV hzne hf1 hf1 hzne
    (Ne.symm hfz) hfz
  have hZβ : ∀ {X : Subgroup G}, f ∈ X → conjSub lβ (fsuV1 T V) ≤ X := fun {X} hfX t ht => by
    rcases C.mem_zα hz1 hzne ht with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1, hlβ]; exact hfX
  have hg₁1 : g₁ ≠ 1 := fun h1 => M755.ptQ_ne_one (c := M755.dc 2) (by decide) (by
    rw [← hθg₁, h1, C.θG_V1 e (one_mem _)])
  have hg₂1 : g₂ ≠ 1 := fun h1 => M755.ptQ_ne_one (c := M755.dc 4) (by decide) (by
    rw [← hθg₂, h1, C.θG_V1 e (one_mem _)])
  have hθne : ∀ {a b : G}, C.θG e a ≠ C.θG e b → a ≠ b := fun {a b} h hab => h (hab ▸ rfl)
  have hfg₁ : f ≠ g₁ := hθne (by
    rw [hθf₁, hθg₁]
    exact fun h => absurd (M755.ptQ_injective h8 (by decide) h) (by decide))
  have hfg₂ : f ≠ g₂ := hθne (by
    rw [hθf₁, hθg₂]
    exact fun h => absurd (M755.ptQ_injective h8 (by decide) h) (by decide))
  obtain ⟨l₁, -, hX₂str, hfX₂, hg₁X₂, hX₂le⟩ :=
    C.exists_pt_of_line h13322 hMod hV₂ hf₁.1 hg₁.1 hf1 hg₁1 hfg₁
  obtain ⟨l₄, -, hX₄str, hfX₄, -, hX₄le⟩ :=
    C.exists_pt_of_line h13322 hMod hV₂ hf₂.1 hg₂.1 hf1 hg₂1 hfg₂
  have hV₂h : ∀ {h : G}, conjSub h V₂ = V₂ → V₂ ≤ conjSub h V := fun {h} hh => by
    rw [← hh]
    exact conjSub_mono h hV₂.2.1
  have hX₁Y : ∀ {h' : G}, conjSub h' V₂ = V₂ → conjSub y' V₂ ≤ conjSub (y' * h') V :=
    fun {h'} hh' => by
      rw [conjSub_mul]
      exact conjSub_mono y' (hV₂h hh')
  have hFY : ∀ {h h' t : G}, (∀ t ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)),
      y'⁻¹ * t * y' ∈ conjSub h' V) → t ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)) →
      t ∈ conjSub (y' * h') V := fun {h h' t} hy ht => by
    rw [conjSub_mul]
    have := mul_mem_conjSub (g := y') (hy t ht)
    rwa [show y' * (y'⁻¹ * t * y') * y'⁻¹ = t by group] at this
  have hX₂F : ∀ t ∈ conjSub (h₁ * l₁) V₂,
      t ∈ conjSub h₁ V ⊓ conjSub x (conjClosure V (hz T V)) := fun t ht => by
    rcases hX₂str t ht with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hf₁
    · exact hg₁
    · exact mul_mem hf₁ hg₁
  have hX₄F : ∀ t ∈ conjSub (h₂ * l₄) V₂,
      t ∈ conjSub h₂ V ⊓ conjSub x (conjClosure V (hz T V)) := fun t ht => by
    rcases hX₄str t ht with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hf₂
    · exact hg₂
    · exact mul_mem hf₂ hg₂
  have hZαX₁ : conjSub x (fsuV1 T V) ≤ conjSub y' V₂ := by
    rw [← hR3]
    exact conjSub_mono y' hV₂.1
  have hV₂U : V₂ ≤ conjClosure V (hz T V) := hV₂.2.1.trans (le_conjClosure V _)
  have hX₂U : conjSub (h₁ * l₁) V₂ ≤ conjClosure V (hz T V) := fun t ht => hV'U hh₁H (hX₂le ht)
  have hX₄U : conjSub (h₂ * l₄) V₂ ≤ conjClosure V (hz T V) := fun t ht => hV'U hh₂H (hX₄le ht)
  have hne13 : conjSub y' V₂ ≠ V₂ := fun h1 => hZU (hZαX₁.trans (h1.le.trans hV₂U))
  have hne12 : conjSub y' V₂ ≠ conjSub (h₁ * l₁) V₂ := fun h1 =>
    hZU (hZαX₁.trans (h1.le.trans hX₂U))
  have hne41 : conjSub (h₂ * l₄) V₂ ≠ conjSub y' V₂ := fun h1 =>
    hZU (hZαX₁.trans (h1.symm.le.trans hX₄U))
  have hne23 : conjSub (h₁ * l₁) V₂ ≠ V₂ := fun h1 => hV1α fun t ht =>
    (hX₂F t (by rw [h1]; exact hV₂.1 ht)).2
  have hne34 : V₂ ≠ conjSub (h₂ * l₄) V₂ := fun h1 => hV1α fun t ht =>
    (hX₄F t (by rw [← h1]; exact hV₂.1 ht)).2
  have hdc2 : M755.dc 2 = 16 := rfl
  have hdc4 : M755.dc 4 = 32 := rfl
  rw [hdc2] at hθg₁
  rw [hdc4] at hθg₂
  have hne24 : conjSub (h₁ * l₁) V₂ ≠ conjSub (h₂ * l₄) V₂ := by
    intro h1
    have hg := hX₄str g₁ (h1 ▸ hg₁X₂)
    have h16 : (16 : ℕ) ∈ M755.ptsQ := by decide
    rcases hg with h2 | h2 | h2 | h2
    · exact hg₁1 h2
    · exact hfg₁ h2.symm
    · rw [h2, hθg₂] at hθg₁
      exact absurd (M755.ptQ_injective (by decide) h16 hθg₁) (by decide)
    · rw [h2, C.θG_mul e hfU (hV'U hh₂H hg₂.1), hθf₁, hθg₂, M755.ptQ_mul (by decide) (by decide)]
        at hθg₁
      exact absurd (M755.ptQ_injective (by decide) h16 hθg₁) (by decide)
  exact C.no_four_cycle E h13322 hMod hVL hV₂ lβ (X₁ := conjSub y' V₂)
    (X₂ := conjSub (h₁ * l₁) V₂) (X₃ := V₂) (X₄ := conjSub (h₂ * l₄) V₂)
    (Y₁ := conjSub (y' * h'₁) V) (Y₂ := conjSub h₁ V) (Y₃ := conjSub h₂ V)
    (Y₄ := conjSub (y' * h'₂) V) rfl rfl (by rw [conjSub_one]) rfl rfl rfl rfl rfl
    (hZβ hfX₁) (hZβ hfX₂) (hZβ hf₁V₂) (hZβ hfX₄) (hX₁Y hh'₁V₂)
    (fun t ht => hFY hy₁ (hX₂F t ht)) hX₂le (hV₂h hh₁V₂) (hV₂h hh₂V₂) hX₄le
    (fun t ht => hFY hy₂ (hX₄F t ht)) (hX₁Y hh'₂V₂) hne13 hne24 hne12 hne23 hne34 hne41

end Ctx753

end CFSG.Quasithin.H13.L32A
