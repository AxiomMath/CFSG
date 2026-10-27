module

public import CFSG.RankThree.GF2n.Stroth80.Sec83UpperModule
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sp4ModTrans
public import CFSG.RankThree.GF2n.Stroth80.AddAutDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec83SevenReduce
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec83seven_main (h34 : Stroth34Statement)
    (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin 2 ⊕ Fin 2) K} {u u' : Fin 2 ⊕ Fin 2 → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r 2 K φ u u') (hn7 : n = 7) :
    False := by
  have hTrans := sp4ModTransStatement_holds
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, 2, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hinv := sec8InvStatement_holds G M Q Z B hc n t h8 r hr
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨a, hn, hV1c, hW1c⟩ := sec83_count_A h53 sec8InvStatement_holds hs hr hpts
  have ha : a = 1 := by
    subst hn7
    norm_num at hn
    omega
  subst ha
  have hcardV1 : Nat.card ↥(Sec8V1 M Q Z B t r) = Nat.card Z ^ 6 := by
    rw [hV1c]
  have hcardW1 : Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card Z ^ 10 := by
    rw [hW1c, hcardV1, ← pow_add]
    norm_num
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  obtain ⟨hVA1, hA1W, hVA2, hA2W, hsup, hinf, hcomm, hsq, hA1c, hA2c⟩ := hcd
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hV₁W₁ : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hVA1.trans hA1W
  have hnormW1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx
  have hnormV1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r,
      ρ * x * ρ⁻¹ ∈ Sec8V1 M Q Z B t r := fun ρ hρ x hx =>
    conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx
  have hSecX : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    ⟨hV₁W₁, hcomm, hsq, hnormW1, hnormV1⟩
  obtain ⟨X, _, _, κ, hκ⟩ := exists_sectionModule hSecX
  haveI : Finite X := hκ.finite
  have hXcard : Nat.card X = Nat.card Z ^ 4 := by
    have h1 := natCard_eq_of_isSecMod hV₁W₁ hκ
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 * Nat.card X = Nat.card Z ^ 6 * Nat.card Z ^ 4 := by
      rw [← h1, ← pow_add]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hkerAct : ∀ x ∈ φ.ker, ∀ a : X, x • a = a := by
    intro x hx a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hwa : Multiplicative.toAdd (κ w) = a := by rw [hw]; rfl
    have hxN : (x : G) ∈ hc.CN t := by
      rw [hpts.ker] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hxw : ⁅(x : G), (w : G)⁆ ∈ Sec8V1 M Q Z B t r := hb.2 (x : G) hxN w w.2
    have hxwW : ⁅(x : G), (w : G)⁆ ∈ Sec8W1 M Q Z B t r := hV₁W₁ hxw
    have h1 := smul_toAdd_sub_eq hκ hnormW1 x w hxwW
    have h2 : κ ⟨⁅(x : G), (w : G)⁆, hxwW⟩ = 1 := (hκ.ker _).mpr hxw
    rw [h2, toAdd_one, sub_eq_zero] at h1
    rw [← hwa]
    exact h1
  obtain ⟨π, hπ⟩ := exists_addAut_hom_of_range φ hpts.range hkerAct
  have hnontriv : π ≠ 1 := by
    intro hπ1
    have hall : ∀ (x : ↥(Rt M (LB M Q B) t)) (a : X), x • a = a := by
      intro x a
      have hx : φ x ∈ StatedSp 2 K := by
        rw [← hpts.range]
        exact ⟨x, rfl⟩
      rw [← hπ x hx a, hπ1]
      rfl
    have hW₁V₁ : Sec8W1 M Q Z B t r ≤ Sec8V1 M Q Z B t r := by
      intro w hw
      have hcomm_all : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ, w⁆ ∈ Sec8V1 M Q Z B t r := by
        intro ρ hρ
        have hρw : ⁅ρ, w⁆ ∈ Sec8W1 M Q Z B t r := by
          rw [commutatorElement_def]
          exact (Sec8W1 M Q Z B t r).mul_mem (hnormW1 ρ hρ w hw) ((Sec8W1 M Q Z B t r).inv_mem hw)
        have h1 := smul_toAdd_sub_eq hκ hnormW1 ⟨ρ, hρ⟩ ⟨w, hw⟩ hρw
        rw [hall, sub_self] at h1
        exact (hκ.ker _).mp (Multiplicative.toAdd.injective h1.symm)
      have hwA1 := (hA1c w hw).mpr fun l hl => hcomm_all l (hLR hl)
      have hwA2 := (hA2c w hw).mpr fun l hl => hcomm_all l (hL'R hl)
      rw [← hinf]
      exact ⟨hwA1, hwA2⟩
    have h1 := Subgroup.card_le_of_le hW₁V₁
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have htrans := hTrans K (by have := hc.hyp.q4; rw [hpts.card]; exact this) X hκ.two
    (by rw [hXcard, hpts.card]) π hnontriv
  have h35B := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hV1V : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hQV : Q ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hVQ hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Vt M (LB M Q B) B Z t).mul_mem (sec39_Z_le_Vt hc') hy
  have hcommV1 : ∀ x ∈ Sec8W1 M Q Z B t r, ∀ y ∈ Sec8V1 M Q Z B t r, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hV1sq : ∀ v ∈ Sec8V1 M Q Z B t r, v ^ 2 = 1 := by
    intro v hv
    have hv' : v ∈ (Q ⊓ QB B) ⊔ Vt M (LB M Q B) B Z t := hv.1
    obtain ⟨a, ha, v₀, hv₀, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := Q ⊓ QB B) (K := Vt M (LB M Q B) B Z t) (fun x hx => hQV hx.1) hv'
    have haV₁ : a ∈ Sec8V1 M Q Z B t r := by
      have := (Sec8V1 M Q Z B t r).mul_mem hv ((Sec8V1 M Q Z B t r).inv_mem (hV1V hv₀))
      simpa using this
    have h1 : a ^ 2 = 1 := hc.inf_QB_elemAbelian.2 a ha
    have h2 : v₀ ^ 2 = 1 := (hc.Vt_isElemAbelian h35B hs.mem hs.notQ).2 v₀ hv₀
    have h3 : Commute a v₀ := hcommV1 a (hV₁W₁ haV₁) v₀ (hV1V hv₀)
    rw [h3.mul_pow, h1, h2, one_mul]
  set A₁ := QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r with hA₁
  set A₂ := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r with hA₂
  have hA1sq : ∀ x ∈ A₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB B ⊓ Sec8W1 M Q Z B t r) (K := Sec8V1 M Q Z B t r)
      (sec8_le_normalizer_of_conj (S := QB B ⊓ Sec8W1 M Q Z B t r) fun y hy w hw => by
        rw [hcommV1 y hy.2 w hw, mul_inv_cancel_right]
        exact hw) hx
    have h1 : a ^ 2 = 1 := hc.inf_QB_elemAbelian.2 a ⟨hW₁Q ha.2, ha.1⟩
    have h2 : v ^ 2 = 1 := hV1sq v hv
    have h3 : Commute a v := hcommV1 a ha.2 v hv
    rw [h3.mul_pow, h1, h2, one_mul]
  have hA2sq : ∀ x ∈ A₂, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (H := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) (K := Sec8V1 M Q Z B t r)
      (sec8_le_normalizer_of_conj (S := QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r)
        fun y hy w hw => by
          rw [hcommV1 y hy.2 w hw, mul_inv_cancel_right]
          exact hw) hx
    have h1 : a ^ 2 = 1 := hcC.inf_QB_elemAbelian.2 a ⟨hW₁Q ha.2, ha.1⟩
    have h2 : v ^ 2 = 1 := hV1sq v hv
    have h3 : Commute a v := hcommV1 a ha.2 v hv
    rw [h3.mul_pow, h1, h2, one_mul]
  have hex : (∃ a ∈ A₁, a ∉ Sec8V1 M Q Z B t r) ∨ (∃ a ∈ A₂, a ∉ Sec8V1 M Q Z B t r) := by
    by_contra hcon
    push Not at hcon
    have hle : Sec8W1 M Q Z B t r ≤ Sec8V1 M Q Z B t r := by
      rw [← hsup]
      exact sup_le (fun a ha => hcon.1 a ha) (fun a ha => hcon.2 a ha)
    have h1 := Subgroup.card_le_of_le hle
    rw [hcardW1, hcardV1] at h1
    have h2 : Nat.card Z ^ 6 < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have key : ∀ (Ai : Subgroup G), Ai ≤ Sec8W1 M Q Z B t r → Sec8V1 M Q Z B t r ≤ Ai →
      (∀ x ∈ Ai, x ^ 2 = 1) → (∃ a ∈ Ai, a ∉ Sec8V1 M Q Z B t r) →
      ∀ w ∈ Sec8W1 M Q Z B t r, w ∉ Sec8V1 M Q Z B t r → w ^ 2 = 1 := by
    intro Ai hAiW hVAi hAisq ⟨a, haA, haV⟩ w hw hwV
    have hya : Multiplicative.toAdd (κ ⟨a, hAiW haA⟩) ≠ 0 := fun h =>
      haV ((hκ.ker _).mp (Multiplicative.toAdd.injective h))
    have hyw : Multiplicative.toAdd (κ ⟨w, hw⟩) ≠ 0 := fun h =>
      hwV ((hκ.ker _).mp (Multiplicative.toAdd.injective h))
    obtain ⟨g, hg⟩ := htrans _ _ hya hyw
    have hgφ : (g : GL (Fin 2 ⊕ Fin 2) K) ∈ φ.range := by
      rw [hpts.range]
      exact g.2
    obtain ⟨ρ, hρ⟩ := hgφ
    have hρS : φ ρ ∈ StatedSp 2 K := by
      rw [hρ]
      exact g.2
    have hgeq : g = ⟨φ ρ, hρS⟩ := Subtype.ext hρ.symm
    rw [hgeq, hπ ρ hρS] at hg
    obtain ⟨ρ', hρ'R⟩ := ρ
    have hact := hκ.act ⟨ρ', hρ'R⟩ ⟨a, hAiW haA⟩
      ⟨ρ' * a * ρ'⁻¹, hnormW1 ρ' hρ'R a (hAiW haA)⟩ rfl
    rw [hg] at hact
    have hact' : κ ⟨ρ' * a * ρ'⁻¹, hnormW1 ρ' hρ'R a (hAiW haA)⟩ = κ ⟨w, hw⟩ := by
      rw [hact]
      rfl
    have hv₁ : (ρ' * a * ρ'⁻¹) * w⁻¹ ∈ Sec8V1 M Q Z B t r := (hκ.eq_iff _ _).mp hact'
    have hv'' : ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ' ∈ Sec8V1 M Q Z B t r := by
      simpa using hnormV1 ρ'⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ'R) _
        ((Sec8V1 M Q Z B t r).inv_mem hv₁)
    have hxA : (ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ') * a ∈ Ai :=
      Ai.mul_mem (hVAi hv'') haA
    have hw_eq : w = ρ' * ((ρ'⁻¹ * ((ρ' * a * ρ'⁻¹) * w⁻¹)⁻¹ * ρ') * a) * ρ'⁻¹ := by group
    rw [hw_eq, conj_pow, hAisq _ hxA]
    group
  have hsqW1 : ∀ w ∈ Sec8W1 M Q Z B t r, w ^ 2 = 1 := by
    intro w hw
    by_cases hwV : w ∈ Sec8V1 M Q Z B t r
    · exact hV1sq w hwV
    · rcases hex with ⟨a, haA, haV⟩ | ⟨a, haA, haV⟩
      · exact key A₁ hA1W hVA1 hA1sq ⟨a, haA, haV⟩ w hw hwV
      · exact key A₂ hA2W hVA2 hA2sq ⟨a, haA, haV⟩ w hw hwV
  have habel : ∀ a ∈ Sec8W1 M Q Z B t r, ∀ b ∈ Sec8W1 M Q Z B t r, a * b = b * a := by
    intro a ha b hb
    have h1 := hsqW1 a ha
    have h2 := hsqW1 b hb
    have h3 := hsqW1 (a * b) ((Sec8W1 M Q Z B t r).mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rwa [sq] at h1)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rwa [sq] at h2)
    have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rwa [sq] at h3)
    calc a * b = (a * b)⁻¹ := hab'.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have hZW₁ : Z ≤ Sec8W1 M Q Z B t r := fun z hz => ⟨hZQ hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hV₁W₁.trans hW₁Q hv)).symm⟩
  have hAB := sec83W1_card_le_of_comm hc hs hV₁W₁ hW₁Q hZW₁ habel
  rw [hcardW1, hn7] at hAB
  have h2 : Nat.card Z ^ (7 + 1) < Nat.card Z ^ 10 := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem sec83Seven_of_53 (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    (hA : Sec8AExistsStatement) (hPts : Sec5NatPointsSpStatement) :
    Sec83SevenStatement := by
  intro G _ _ M Q Z B hc n t hs hsp hn
  have h8 : Sec8Hyp hc n t := ⟨hs, 2, le_rfl, hsp⟩
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t h8
  obtain ⟨K, _, _, hK, m', hm', φ, u, u', hrange, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs h8.spNat r hr.mem hr.plane
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hrange, hker, hact, huu', hL, hL'⟩
  obtain rfl : m' = 2 := hpts.spMNat.m_unique hsp
  exact sec83seven_main h34 h53 hs hr hpts hn

end CFSG.RankThree.GF2n.Stroth80
