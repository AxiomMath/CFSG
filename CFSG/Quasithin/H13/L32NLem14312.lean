module

public import CFSG.Quasithin.H13.L32NLem14312a
public import CFSG.Quasithin.H13.L32NLem14332e
public import CFSG.Quasithin.Background.G10Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L14312

variable {X : Type*} [Group X]

omit [Group X] in
theorem frattiniOf_eq_bot_of_card_two [Group X] {A : Subgroup X} (hA : Nat.card A = 2) :
    frattiniOf A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hco : IsCoatom (⊥ : Subgroup ↥A) := by
    refine ⟨fun h => ?_, fun B hB => ?_⟩
    · have h1 := Subgroup.card_bot (G := ↥A)
      rw [h, Subgroup.card_top, hA] at h1
      omega
    · have : Fact (Nat.card ↥A).Prime := ⟨by rw [hA]; exact Nat.prime_two⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card B with h | h
      · exact absurd h hB.ne'
      · exact h
  have h := frattini_le_coatom hco
  simp only [frattiniOf, le_bot_iff.mp h, Subgroup.map_bot]

end L14312

open L14332 in
theorem lemma14312One_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1288 : Lemma12_8_8_two) (h12811 : Lemma12_8_11) (h12813 : Lemma12_8_13) :
    Lemma14312One := by
  intro G _ _ T L V h V₂ g hV₂ hgP hgN D hle
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨-, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt12 : fsuV1 T V < V₂ := lt_of_le_of_ne hV₂.2 fun he => by rw [he] at hV1; omega
  obtain ⟨a, haV₂, ha1⟩ := IsConcreteLE.exists_of_lt hlt12
  have H := L14312.g101Hyp h1222 h12213 hs hgP hgN haV₂ ha1 D
  have : Module.Finite (ZMod 2) D.V := Module.Finite.of_finite
  set d := Module.finrank (ZMod 2) D.V with hd
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hX
  set X₀ := D.img (CFSG.conjugate (centerOf (fsuU T V)) g) with hX₀
  set r := X₀.relIndex X with hr
  set e := Module.finrank (ZMod 2) ↥(D.hat (l32nE T V V₂ g)) with he
  have hdim : d ≤ 2 * (Nat.log 2 r + 1) := H.dim_le_two_mul
  have hrank : e + Nat.log 2 r = d - 1 := H.rank
  have hiso : 2 * e ≤ d := H.finrank_isotropic_le
  have he1 : 1 ≤ e := by
    have h0 : (⟨D.π a, H.mem_W⟩ : ↥(D.hat (l32nE T V V₂ g))) ≠ 0 := fun h0 =>
      H.point (congrArg Subtype.val h0)
    exact Nat.one_le_iff_ne_zero.mpr fun h0' =>
      h0 (Module.finrank_zero_iff.mp h0' |>.elim _ _)
  have hmul := Subgroup.relIndex_mul_card X₀ X
  rw [inf_eq_left.mpr H.X₀_le, ← hr] at hmul
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hr0 : r ≠ 0 := fun h0 => by rw [h0, zero_mul] at hmul; omega
  have hrX : r ≤ Nat.card ↥X := by
    calc r = r * 1 := (mul_one r).symm
      _ ≤ r * Nat.card ↥X₀ := Nat.mul_le_mul_left r Nat.card_pos
      _ = Nat.card ↥X := hmul
  have hlogX : Nat.log 2 (Nat.card ↥X) ≤ d / 2 - 1 := by
    calc Nat.log 2 (Nat.card ↥X) ≤ Nat.log 2 (2 ^ (d / 2 - 1)) := Nat.log_mono_right hle
      _ = d / 2 - 1 := Nat.log_pow (by norm_num) _
  have hlogr : Nat.log 2 r ≤ d / 2 - 1 := (Nat.log_mono_right hrX).trans hlogX
  have heven : d = 2 * (d / 2) := by omega
  have hlr : Nat.log 2 r = d / 2 - 1 := by omega
  have hed : 2 * e = d := by omega
  obtain ⟨k, hk⟩ := H.exists_card_X
  have hrpow : r = 2 ^ Nat.log 2 r := by
    have hdvd : r ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card X₀ X
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj, Nat.log_pow (by norm_num)]
  have hXeq : Nat.card ↥X = 2 ^ (d / 2 - 1) := by
    refine le_antisymm hle ?_
    calc 2 ^ (d / 2 - 1) = r := by rw [← hlr, ← hrpow]
      _ ≤ Nat.card ↥X := hrX
  have hX₀1 : Nat.card ↥X₀ = 1 := by
    have h1 : r = Nat.card ↥X := by rw [hXeq, ← hlr, ← hrpow]
    rw [← h1] at hmul
    exact (Nat.mul_eq_left hr0).mp hmul
  refine ⟨hXeq, hed, ?_⟩
  have hZg : CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nCHat T V := by
    intro y hy
    have hyH := conj_zU_le h12813 hs hgP hgN hy
    have hρ : D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ = 1 := by
      have hmem : D.ρ ⟨y, l32nH_le_normalizer_fsuU T V hyH⟩ ∈ X₀ :=
        L128A.HatU.rho_mem_img D hy (l32nH_le_normalizer_fsuU T V hyH)
      rw [(Subgroup.card_eq_one).mp hX₀1, Subgroup.mem_bot] at hmem
      exact hmem
    exact (rho_eq_one_iff_mem hyH _).mp hρ
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := by
    have := lemma12_8_8_three h1222 h12213 hs
    exact this ▸ inf_le_right
  have hZ : centerOf (fsuU T V) = fsuV1 T V := by
    rcases hV1Z.lt_or_eq with hlt | heq
    · exact absurd hZg ((h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.2.1 hlt)
    · exact heq.symm
  obtain ⟨U₀, hU₀U, hext, hΦ, hsup⟩ := lemma12_8_8_one h1222 h12213 hs
  have hU₀ : U₀ = fsuU T V := by
    have hle0 : centerOf (fsuU T V) ≤ U₀ := by
      rw [hZ, ← hΦ]
      exact Subgroup.map_subtype_le _
    have h2 : U₀ ⊔ centerOf (fsuU T V) = fsuU T V := hsup
    rw [← h2, sup_eq_left.mpr hle0]
  have h1283 := lemma12_8_3 h12213
  have h1284 := lemma12_8_4 h1222 h37 h38 h39
  have hQ := (h1284 G T L V 3 (h.hyp1281One h13322 hV) (fsuV1 T V) (l32nH T V)
    (h.isTSub_fsuV1 hV) (h.isHzOne_l32nH h13322 hV h1283)).2.2.2
  refine ⟨⟨hZ, hU₀ ▸ hext, ?_⟩, ?_⟩
  · show centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)
    rw [hZ]
    exact hQ
  obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ hs D
  have hfr : frattiniOf (zU128 V (fsuV1 T V)) = ⊥ := by
    show frattiniOf (centerOf (fsuU T V)) = ⊥
    rw [hZ]
    exact L14312.frattiniOf_eq_bot_of_card_two hV1
  obtain ⟨q, hq1, hq2, hq3⟩ := hq hfr
  refine ⟨q, hq1, hq2, hq3, fun w hw => ?_⟩
  obtain ⟨-, hE, -⟩ := h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  have hq0 : q 0 = 0 := by
    have h0 := hq2 0 0
    rw [add_zero, H.isotropic 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _), add_zero] at h0
    have h00 : q 0 + q 0 = 0 := CharTwo.add_self_eq_zero (q 0)
    rw [← h0] at h00
    exact h00
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, ⟨huE, huU⟩, rfl⟩ := hw
    exact (hq1 u huU).mpr (hE.2 u huE)
  | zero => exact hq0
  | add w w' hw hw' ihw ihw' =>
    rw [hq2, ihw, ihw', H.isotropic w hw w' hw', add_zero, add_zero]
  | smul c w hw ih =>
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · rw [zero_smul, hq0]
    · rw [one_smul, ih]

end CFSG.Quasithin.H13
