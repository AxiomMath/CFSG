module

public import CFSG.Sporadic.Recognition.J3MultiplierCover
import Certificates.Kernel.MatCC.J3.UHatA
import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.PartialFact

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.J3Multiplier CFSG.KC.MiscCoset

namespace Certificates

open CFSG.Certificates CFSG.KC.MiscCoset.Mem CFSG.KC.MiscCoset.Partial

def j3dWord : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
    (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (1, false),
    (1, false), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (0, true)]

noncomputable def j3OrbWords : List (List ℕ) :=
  [[(1, true)].map codeN, (([(1, true)].map codeN).map invC).reverse, j3dWord.map codeN,
    ((j3dWord.map codeN).map invC).reverse]

theorem j3_orb_ok : orbOk CFSG.KBData.F24091o.F 1575686 CFSG.KBData.F24091o.Ob.c0 j3OrbWords =
    true := by
  quickRfl

theorem j3_kill_a2 : memOK CFSG.KBData.F24091k.F 61187 ([(0, true), (0, true)].map codeN)
    [0, 117572] = true := by
  quickRfl

theorem j3_kill_v : memOK CFSG.KBData.F24091k.F 61187 ([(2, true)].map codeN) [122372] = true := by
  quickRfl

theorem j3_orb_len : Nat.beq (lenN CFSG.KBData.F24091o.Ob.c0) 180 = true := by
  quickRfl

public section

theorem mk_pow_of_mem {m : ℕ} (ws : List (List (Fin m × Bool))) (u : List (Fin m × Bool)) (k : ℕ)
    (hpow : (List.replicate k u).flatten ∈ ws) :
    (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u)) ^ k =
      1 := by
  have hrep : ∀ j : ℕ, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk (List.replicate j u).flatten) =
        (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u)) ^ j := by
    intro j
    induction j with
    | zero =>
      rw [List.replicate_zero, List.flatten_nil, pow_zero]
      exact map_one _
    | succ j ih =>
      rw [pow_succ', List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, map_mul, ih]
  rw [← hrep k]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hpow)

theorem card_plain_le : Finite (PG 2 plainWords) ∧ Nat.card (PG 2 plainWords) ≤ 50232960 := by
  set gen := pgGen plainWords
  have hrels : ∀ r ∈ CFSG.KBRoute.F24091o.rels, KB.sword gen r = 1 := sword_rels plainWords rfl
  have hwH : CFSG.KBRoute.F24091o.T1.words = [encW sc] := rfl
  set c := PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ plainWords.map FreeGroup.mk}
    (FreeGroup.mk sc)
  have hc19 : c ^ 19 = 1 := mk_pow_of_mem plainWords sc 19 (by decide)
  set H := KB.wordSub gen CFSG.KBRoute.F24091o.T1.words
  have hH : H = Subgroup.zpowers c := by
    change KB.wordSub gen _ = _
    rw [hwH]
    exact wordSub_single plainWords sc
  have hord : 0 < orderOf c := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨19, by norm_num, hc19⟩)
  have hHfin : Finite H := by
    rw [hH]
    exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hHcard : Nat.card H ≤ 19 := by
    rw [hH, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc19)
  obtain ⟨cnt, hL, hA, hfacts⟩ := factsOk_facts gen (fun r hr _ => hrels r hr) CFSG.KBRoute.F24091o.t1
  set val := KB.letterVal gen CFSG.KBRoute.F24091o.T1.amap _
  set rp := KB.Sound.rep val CFSG.KBData.F24091o.F CFSG.KBData.F24091o.D _
  have hcodes := fun (u : List (ℕ × Bool)) (hu : ∀ l ∈ u, l.1 < 2) =>
    codes_spec gen hL hA (m := 2) (by decide) CFSG.KBRoute.F24091o.top hu
  obtain ⟨hcv, hci⟩ := hcodes [(1, true)] (by decide)
  obtain ⟨hdv, hdi⟩ := hcodes j3dWord (by decide)
  have hinvR : ∀ W : List ℕ, (∀ a ∈ W, val (invC a) = (val a)⁻¹) →
      ∀ a ∈ (W.map invC).reverse, val (invC a) = (val a)⁻¹ := by
    intro W hW a ha
    rw [List.mem_reverse, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [invC_invC, hW b hb, inv_inv]
  have hinv : ∀ w ∈ j3OrbWords, ∀ a ∈ w, val (invC a) = (val a)⁻¹ := by
    intro w hw
    simp only [j3OrbWords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hci
    · exact hinvR _ hci
    · exact hdi
    · exact hinvR _ hdi
  obtain ⟨⟨r0, hr0, hx0⟩, hrow⟩ := orbOk_spec H val rp hfacts hinv j3_orb_ok
  set X := {x | ∃ r ∈ CFSG.KBData.F24091o.Ob.c0, rowF r 0 = x}
  set s := KB.sword gen '' {w | w ∈ [[(1, true)], j3dWord]}
  have hstep : ∀ x ∈ X, ∀ g ∈ s, (∃ y ∈ X, KB.Sound.rel H (rp x * g) (rp y)) ∧
      ∃ y ∈ X, KB.Sound.rel H (rp x * g⁻¹) (rp y) := by
    rintro x ⟨r, hr, rfl⟩ g ⟨w, hw, rfl⟩
    have hmem : ∀ w ∈ j3OrbWords, ∃ y ∈ X, KB.Sound.rel H (rp (rowF r 0) * KB.Sound.lv val w)
        (rp y) := by
      intro w hw
      obtain ⟨r', hr', h'⟩ := hrow r hr w hw
      exact ⟨_, ⟨r', hr', rfl⟩, h'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hw
    rcases hw with rfl | rfl
    · refine ⟨?_, ?_⟩
      · have := hmem _ List.mem_cons_self
        rwa [hcv] at this
      · have := hmem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rwa [lv_rev_invC val _ hci, hcv] at this
    · refine ⟨?_, ?_⟩
      · have := hmem (j3dWord.map codeN)
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        rwa [hdv] at this
      · have := hmem ((j3dWord.map codeN).map invC).reverse
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            List.mem_cons_self)))
        rwa [lv_rev_invC val _ hdi, hdv] at this
  have horb := closure_orbit H rp X s hstep
  set K := KB.wordSub gen CFSG.KBRoute.F24091i.T1.words
  have hK : K = Subgroup.closure s := rfl
  have hreps : ∀ g ∈ K, ∃ y ∈ CFSG.KBData.F24091o.Ob.c0.map (rowF · 0), KB.Sound.rel H g (rp y) := by
    intro g hg
    obtain ⟨y, ⟨r, hr, rfl⟩, hy⟩ := horb g (by rw [← hK]; exact hg) 0 ⟨r0, hr0, hx0⟩
    have h0 : rp 0 = 1 := KB.Sound.rep_zero _ _ _ _
    rw [h0, one_mul] at hy
    exact ⟨_, List.mem_map_of_mem hr, hy⟩
  obtain ⟨hKfin, hKcard⟩ := card_le_of_reps H K rp _ hreps
  have hlen : (CFSG.KBData.F24091o.Ob.c0.map (rowF · 0)).length = 180 := by
    rw [List.length_map, ← lenN_eq]
    exact Nat.eq_of_beq_eq_true j3_orb_len
  rw [hlen] at hKcard
  have hidx := CFSG.KBFact.F24091i
  unfold KB.TableFact at hidx
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hi, htop⟩ := hidx
  obtain ⟨hfi, hidx⟩ := index_le_of_tableOk plainWords rfl hi (by norm_num) htop
  have hG : Finite (PG 2 plainWords) := by
    have : Finite (PG 2 plainWords ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient K
  refine ⟨hG, ?_⟩
  rw [← K.index_mul_card]
  calc K.index * Nat.card K ≤ 14688 * (19 * 180) :=
        Nat.mul_le_mul hidx (hKcard.trans (Nat.mul_le_mul_right _ hHcard))
    _ = 50232960 := by norm_num

theorem card_uhat_le : Finite (PG 3 uhatWords) ∧ Nat.card (PG 3 uhatWords) ≤ 50232960 := by
  set genU := pgGen uhatWords
  have hrelsU : ∀ r ∈ CFSG.KBRoute.F24091k.rels, KB.sword genU r = 1 := sword_rels uhatWords rfl
  have hwk : CFSG.KBRoute.F24091k.T1.words = [encW [((1 : Fin 3), true)]] := rfl
  set c := PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ uhatWords.map FreeGroup.mk}
    (FreeGroup.mk [((1 : Fin 3), true)])
  have hc19 : c ^ 19 = 1 := mk_pow_of_mem uhatWords _ 19 (by decide)
  have hsub : KB.wordSub genU CFSG.KBRoute.F24091k.T1.words = Subgroup.zpowers c := by
    rw [hwk, wordSub_single]
  have hx := factsOk_mem genU hrelsU CFSG.KBRoute.F24091k.t1 (by decide) CFSG.KBRoute.F24091k.top
    (by decide) j3_kill_a2
  have hv := factsOk_mem genU hrelsU CFSG.KBRoute.F24091k.t1 (by decide) CFSG.KBRoute.F24091k.top
    (by decide) j3_kill_v
  rw [hsub] at hx hv
  have hone : ∀ w ∈ uhatWords, KB.sword genU (encW w) = 1 := fun w hw =>
    sword_rels uhatWords rfl _ (List.mem_map_of_mem hw)
  have hg : ∀ i : Fin 3, genU i.val = PresentedGroup.of i := fun i => by simp [genU, pgGen, i.isLt]
  have ha4 := hone [(0, true), (0, true), (0, true), (0, true)] (by decide)
  have hv2 := hone [(2, true), (2, true)] (by decide)
  simp only [encW, KB.sword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ite_true] at ha4 hv2 hx hv
  have h19 : Nat.Prime 19 := by norm_num
  have ha2 : genU 0 * genU 0 = 1 :=
    eq_one_of_mem_zpowers h19 (by norm_num) hc19 hx (by rw [pow_two]; simpa [mul_assoc] using ha4)
  have hv1 : genU 2 = 1 :=
    eq_one_of_mem_zpowers h19 (by norm_num) hc19 hv (by rw [pow_two]; exact hv2)
  set f : Fin 2 → PG 3 uhatWords := fun i => PresentedGroup.of i.castSucc
  have hf : ∀ w : List (Fin 2 × Bool), FreeGroup.lift f (FreeGroup.mk w) =
      PresentedGroup.mk _ (FreeGroup.mk (lift3 w)) := by
    intro w
    rw [← CFSG.CosetTable.lift_of_mk, lift_mk_lift3]
  have hrel : ∀ r ∈ plainWords, FreeGroup.lift f (FreeGroup.mk r) = 1 := by
    intro r hr
    rw [hf]
    unfold plainWords at hr
    rcases List.mem_append.1 hr with hr | hr
    · exact PresentedGroup.one_of_mem (List.mem_map_of_mem (by
        unfold uhatWords
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hr))))
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hr
      have hT1 := hone (lift3 (T 1) ++ [(2, false)]) (by
        unfold uhatWords
        exact List.mem_append_right _ List.mem_cons_self)
      rw [sword_pgGen, ← FreeGroup.mul_mk, map_mul] at hT1
      have h2 : PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ uhatWords.map FreeGroup.mk}
          (FreeGroup.mk [((2 : Fin 3), false)]) = 1 := by
        rw [← sword_pgGen]
        simp only [encW, KB.sword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          mul_one, Bool.false_eq_true, ite_false]
        change (genU 2)⁻¹ = 1
        rw [hv1, inv_one]
      rw [h2, mul_one] at hT1
      fin_cases i
      · rw [← sword_pgGen]
        simp only [T, a2, lift3, encW, KB.sword]
        exact ha2
      · exact hT1
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j => Subgroup.subset_closure ⟨j, rfl⟩) i
    rw [← hg (Fin.last 2)]
    change genU 2 ∈ _
    rw [hv1]
    exact one_mem _
  have hP := card_plain_le
  have : Finite (PG 2 plainWords) := hP.1
  have hq := card_le_of_quot plainWords f hrel hgen
  exact ⟨hq.1, hq.2.trans hP.2⟩

open CFSG.CosetTable CFSG.Monster.Schur CFSG.Sporadic.Recognition.J3Multiplier in
theorem certificate24091 : (Finite (PG 2 plainWords) ∧ Nat.card (PG 2 plainWords) ≤ 50232960) ∧
    ∀ e : Fin 2 → Bool, (∃ i, e i = true) →
      Finite (PG (2 + 1) (epsRels U T e)) ∧ Nat.card (PG (2 + 1) (epsRels U T e)) ≤ 50232960 := by
  obtain ⟨hfin, hle⟩ := card_uhat_le
  refine ⟨⟨(card_plain_le_uhat).1, (card_plain_le_uhat).2.trans hle⟩, fun e he => ?_⟩
  exact ⟨(card_eps_le_uhat e he).1, (card_eps_le_uhat e he).2.trans hle⟩

end

end Certificates
