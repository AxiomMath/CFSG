module

public import CFSG.Quasithin.H13.L32A706g
public import CFSG.Quasithin.H13.L32A706c
public import CFSG.Quasithin.H13.L32ASk9

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem shape_of_hypF98 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hS2 : Input1476S2) (S : Setting147 G T L V H) (h98 : HypF98 T V L (fsuV1 T V) V H)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Subgroup G} (hY2 : oTwoUpper Y = Y) (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hexp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y)
    (hYlt : pCoreOf 2 Y < Y) (hYM : Y ⊓ Subgroup.normalizer (L : Set G) = pCoreOf 2 Y)
    (hHYL : H = Y ⊔ (l1 T L V ⊔ T))
    (hmin : ∀ N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), N.Normal → N ≠ ⊥ → N ≤ modO2Image H Y →
      N = modO2Image H Y) :
    (pCoreOf 2 Y).relIndex Y = p ∧ H ≤ Subgroup.normalizer (l1 T L V : Set G) ∧
      ∀ t ∈ T, t * t ∈ pCoreOf 2 H → ∀ l ∈ l1 T L V, t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have h91 := h98.toHypF91
  have hE := h91.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf (fsuV1 T V) (conjClosure V H)) := commGroupOfElemAbelian hE
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  set ρ := FixR.rho h91 with hρ
  set X := autOn (tildeOf (fsuV1 T V) H) (tildeOf (fsuV1 T V) (conjClosure V H)) with hX
  set E := autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)) with hEdef
  have hV : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hE.2 w w.2)
  have hYQ : pCoreOf 2 Y = Y ⊓ pCoreOf 2 H := S152Y.pCoreOf_eq_inf_of_normalizer hYH hHY
  have hρX : ∀ x : ↥H, ρ x ∈ X := fun x =>
    (FixR.mem_autOn_tilde_iff h91 le_rfl).mpr ⟨x, x.2, rfl⟩
  have hρE : ∀ y : ↥H, (y : G) ∈ Y → ρ y ∈ E := fun y hy =>
    (FixR.mem_autOn_tilde_iff h91 hYH).mpr ⟨y, hy, rfl⟩
  have hXE : ∀ g ∈ X, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨x, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 le_rfl).mp hg
    obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hYH).mp he
    refine (FixR.mem_autOn_tilde_iff h91 hYH).mpr ⟨x * y * x⁻¹, ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHY x.2) _).mp hyY
  have hEX : E ≤ X := fun e he => by
    obtain ⟨y, -, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hYH).mp he
    exact hρX y
  have hEexp : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    obtain ⟨y, hyY, rfl⟩ := (FixR.mem_autOn_tilde_iff h91 hYH).mp he
    rw [← map_pow]
    refine (FixR.rho_eq_one_iff h91 _).mpr ?_
    have := hexp y hyY
    rw [hYQ] at this
    simpa using this.2
  have hEp : IsPGroup p E := fun e => ⟨1, Subtype.ext (by simpa using hEexp e e.2)⟩
  have hEne : E ≠ ⊥ := by
    obtain ⟨y₀, hy₀Y, hy₀O⟩ := IsConcreteLE.exists_of_lt hYlt
    intro hbot
    have h1 : ρ ⟨y₀, hYH hy₀Y⟩ ∈ E := hρE _ hy₀Y
    rw [hbot, Subgroup.mem_bot] at h1
    exact hy₀O (by rw [hYQ]; exact ⟨hy₀Y, (FixR.rho_eq_one_iff h91 _).mp h1⟩)
  have hEc := M76.comm_of_minimal h91 hYH hHY hmin hEp hEne
  obtain ⟨k, hk2', hkcard⟩ := M76.exists_card_img_eq h91 hYH hHY hp hp2 hEc hexp
  have hk2 : k ≤ 2 :=
    hk2'.trans (pRank_le_two_of_pCoreOf_ne_bot S.hyp.hyp.h13.qtke S.hz.1.2 hp hp2)
  have hrel : (pCoreOf 2 Y).relIndex Y = Nat.card E := by
    rw [hEdef, HypF91.card_autOn_tilde h91 hYH, ← hYQ]
  have hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
    (qhatOf_le_qOf X).trans h98.lemma_14_5_18_three.1
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hq)
  by_cases hII : ∃ A ∈ QhatStar X, ∃ a ∈ A, ∃ y : ↥H, (y : G) ∈ Y ∧ a * ρ y ≠ ρ y * a
  swap
  · refine (M76.false_of_caseI S h1222 h1332 h1334 h98 hp hp5 hHY hHYL hexp hYlt
      fun A hA a ha y hy => ?_).elim
    by_contra hne
    exact hII ⟨A, hA, a, ha, y, hy, hne⟩
  obtain ⟨A, hAQ, a, haA, y, hy, hne⟩ := hII
  have hEO : E ≤ pCoreOf p X := le_pCoreOf_of_le_normalizer p hEX
    (fun g hg => Subgroup.mem_normalizer_fintype fun e he => hXE g hg e he) hEp
  have hEA : ⁅E, A⁆ ≤ E := Subgroup.commutator_le.mpr fun e he b hb => by
    rw [commutatorElement_def, show e * b * e⁻¹ * b⁻¹ = e * (b * e⁻¹ * b⁻¹) by group]
    exact E.mul_mem he (hXE b (QhatStar_le hAQ hb) _ (E.inv_mem he))
  have hcomm_ne : ⁅E, A⁆ ≠ ⊥ := by
    intro hbot
    have hmem := Subgroup.commutator_mem_commutator (hρE y hy) haA
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply hne
    calc a * ρ y = (ρ y * a * (ρ y)⁻¹ * a⁻¹)⁻¹ * ρ y * a := by group
      _ = ρ y * a := by rw [hmem, inv_one, one_mul]
  have hEAD : ⁅E, A⁆ ≤ ⁅pCoreOf p X, A⁆ := Subgroup.commutator_mono hEO le_rfl
  have hD : ⁅pCoreOf p X, A⁆ ≠ ⊥ := fun h => hcomm_ne (eq_bot_iff.mpr (h ▸ hEAD))
  obtain ⟨h35, h5, -, -, -⟩ := D2_13 hV hr.symm hAQ hp2 rfl hD
  have hp5' : p = 5 := by rcases h35 with h | h <;> omega
  subst hp5'
  obtain ⟨-, -, hDcard, hDcyc, -, hDrk⟩ := h5 rfl
  have hDE : ⁅E, A⁆ = ⁅pCoreOf 5 X, A⁆ := by
    apply Subgroup.eq_of_le_of_card_ge hEAD
    have hdvd : Nat.card ↥(⁅E, A⁆ : Subgroup _) ∣ Nat.card ↥(⁅pCoreOf 5 X, A⁆ : Subgroup _) :=
      Subgroup.card_dvd_of_le hEAD
    rw [hDcard] at hdvd ⊢
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hcomm_ne
    · exact h.ge
  obtain ⟨⟨d, hdD⟩, hgen⟩ := hDcyc.exists_generator
  have hDz : ⁅pCoreOf 5 X, A⁆ = Subgroup.zpowers d := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hdD)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hd1 : d ≠ 1 := by
    intro h1
    rw [hDz, h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hrk4 : rk ((⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom d)) = 4 := by
    rw [← commV_zpowers_eq_map, ← hDz]; exact hDrk
  have hdE : d ∈ E := hEA (hDE ▸ hdD)
  have hd5 : d ^ 5 = 1 := hEexp d hdE
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hEne (Subgroup.eq_bot_of_card_eq _ (by simpa using hkcard))
  have hlE : ∀ l : ↥H, ∀ e ∈ E, ρ l * e * (ρ l)⁻¹ ∈ E := fun l e he => hXE _ (hρX l) e he
  have hc_of : (∀ l : ↥H, (l : G) ∈ l1 T L V → (l : G) ^ 3 = 1 → ∀ e ∈ E,
      ρ l * e * (ρ l)⁻¹ = e) → H ≤ Subgroup.normalizer (l1 T L V : Set G) := by
    intro hce
    refine M76.H_le_N_l1_of_comm S h1222 h1332 h1334 h91 hHY hHYL fun l hl hl3 y' hy' => ?_
    have := hce l hl hl3 _ (hρE y' hy')
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hl3 : ∀ l : ↥H, (l : G) ^ 3 = 1 → ρ l ^ 3 = 1 := fun l hl3 => by
    rw [← map_pow, show l ^ 3 = 1 from Subtype.ext (by simpa using hl3), map_one]
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  swap
  ·
    exfalso
    have hHL := hc_of fun l hl hl3' e he =>
      M76.commute_of_rank_four hV hEc (fun e he => hEexp e he) (by simpa using hkcard)
        (hl3 l hl3') (hlE l) hdE hd1 hrk4 he
    exact hS2 G T L V H S Y hY2 hYH hHY hexp hYM hHYL hHL hmin (by rw [hrel, hkcard]; norm_num)
  have hEz : E = Subgroup.zpowers d := by
    have hle : Subgroup.zpowers d ≤ E := Subgroup.zpowers_le.mpr hdE
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hkcard, Nat.card_zpowers, orderOf_eq_prime hd5 hd1]; norm_num
  have hcomm : ∀ l : ↥H, (l : G) ∈ l1 T L V → (l : G) ^ 3 = 1 → ∀ e ∈ E,
      ρ l * e * (ρ l)⁻¹ = e := by
    intro l hl hl3' e he
    have hld : ρ l * d * (ρ l)⁻¹ = d :=
      M76.conj_eq_of_mem_zpowers (hl3 l hl3') hd5 hd1 (hEz ▸ hlE l d hdE)
    rw [hEz] at he
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [← conj_zpow, hld]
  have hHL := hc_of hcomm
  refine ⟨by rw [hrel, hkcard]; norm_num, hHL, fun t ht htt l hl => ?_⟩
  obtain ⟨l₀, hl₀, hl₀O, hl₀3⟩ := M76.exists_cube_not_mem S h1222 h1332 h1334
  have hl₀H := Setting147.l1H' S hl₀
  have htH := Setting147.TH' S ht
  set lb := ρ ⟨l₀, hl₀H⟩ with hlb
  set s := ρ ⟨t, htH⟩ with hs
  have hlb3 : lb ^ 3 = 1 := hl3 _ hl₀3
  have hfix : fixV (Subgroup.zpowers lb) = ⊥ := by
    refine eq_bot_iff.mpr fun w hw => ?_
    rw [mem_fixV_zpowers_iff] at hw
    exact M76.rho_fix_eq_one S h1222 h1332 h1334 h91 hHL hl₀ hl₀O w hw
  have hdl : d * lb = lb * d := by
    have := hcomm ⟨l₀, hl₀H⟩ hl₀ hl₀3 d hdE
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hs2 : s ^ 2 = 1 := by
    rw [← map_pow]
    exact (FixR.rho_eq_one_iff h91 _).mpr (by simpa [pow_two] using htt)
  have hsd : s * d * s⁻¹ ∈ Subgroup.zpowers d := hEz ▸ hlE _ d hdE
  have hU : ∀ w ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom d),
      lb w = w → w = 1 := fun w _ hw =>
    M76.rho_fix_eq_one S h1222 h1332 h1334 h91 hHL hl₀ hl₀O w hw
  have hUne : ∃ w ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom d),
      w ≠ 1 := by
    by_contra hcon
    have hbot : (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V H))).map (commHom d) = ⊥ :=
      eq_bot_iff.mpr fun w hw => by
        by_contra h1
        exact hcon ⟨w, hw, h1⟩
    rw [hbot, rk_bot] at hrk4
    norm_num at hrk4
  have hsl0 : s * lb * s⁻¹ ∈ Subgroup.zpowers lb := by
    have e : s * lb * s⁻¹ = ρ (⟨t, htH⟩ * ⟨l₀, hl₀H⟩ * (⟨t, htH⟩ : ↥H)⁻¹) := by
      simp only [hs, hlb, map_mul, map_inv]
    rw [e]
    refine M76.rho_mem_zpowers S h1222 h1332 h1334 h91 hHL (l := ⟨l₀, hl₀H⟩) hl₀ hl₀O ?_
    simpa using (Subgroup.mem_normalizer_iff.mp (Setting147.T_le_N_l1 S h1332 ht) l₀).mp hl₀
  have hinv2 : lb⁻¹ = lb * lb := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hlb3)
  have hsl : s * lb * s⁻¹ = lb ∨ s * lb * s⁻¹ = lb⁻¹ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hsl0
    rw [zpow_eq_zpow_emod' j hlb3] at hj
    have hj' : lb ^ (j % 3) = s * lb * s⁻¹ := by simpa using hj
    clear hj
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj3 with h | h | h <;> rw [h] at hj'
    · exfalso
      simp only [zpow_zero] at hj'
      have hlb1 : lb = 1 := by
        have := congrArg (fun z => s⁻¹ * z * s) hj'
        simpa [mul_assoc] using this.symm
      obtain ⟨w, hw, hw1⟩ := hUne
      exact hw1 (hU w hw (by rw [hlb1]; rfl))
    · left; simpa using hj'.symm
    · right; rw [← hj', hinv2]; simp [pow_two]
  have hagree := M76.conj_eq_on_of_rank_four hV hd5 hd1 hlb3 hdl hrk4
    (by rw [hfix, inf_bot_eq]) hs2 hsd hsl
  have hslb : s * lb * s⁻¹ = lb := by
    rcases hsl with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw, hw1⟩ := hUne
      have h1 := hagree w hw
      rw [h, hinv2, MulAut.mul_apply] at h1
      exact hw1 (hU w hw (lb.injective h1))
  have hlH := Setting147.l1H' S hl
  have hmem := M76.rho_mem_zpowers S h1222 h1332 h1334 h91 hHL (l := ⟨l₀, hl₀H⟩)
    (x := ⟨l, hlH⟩) hl₀ hl₀O hl
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcs : Commute s (ρ ⟨l, hlH⟩) := by
    rw [← hj]
    refine Commute.zpow_right ?_ j
    show s * lb = lb * s
    calc s * lb = s * lb * s⁻¹ * s := by group
      _ = lb * s := by rw [hslb]
  have h1 : ρ (⟨t, htH⟩ * ⟨l, hlH⟩ * (⟨t, htH⟩ : ↥H)⁻¹ * (⟨l, hlH⟩ : ↥H)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hs, hcs.eq]; group
  simpa using (FixR.rho_eq_one_iff h91 _).mp h1

theorem input1476Shape_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hS2 : Input1476S2) :
    Input1476Shape := by
  intro G _ _ T L V H S p hp hp5 Y hY2 hYH hHY hexp hYlt hYM hHYL hmin
  exact shape_of_hypF98 h1222 h1332 h1334 hS2 S
    (S.hypF98 (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334) h1222)
    hp hp5 hY2 hYH hHY hexp hYlt hYM hHYL hmin

theorem lemma14_7_6_of_inputs
    (h520 : Lemma14_5_20) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hS2 : Input1476S2) : Lemma14_7_6 :=
  lemma14_7_6_of h520 h1222 h1332 h1334 (input1476Shape_of h1222 h1332 h1334 hS2)

end CFSG.Quasithin.H13.L32A
