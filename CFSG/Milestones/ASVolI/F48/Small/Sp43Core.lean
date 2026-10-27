module

public import CFSG.Milestones.ASVolI.F48.Small.Eng
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Base
public import Certificates.Certificate7536
public import Certificates.Certificate7537
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Lat2

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42 CFSG.CosetTable

section Facts


theorem burnsideF48s_sp43_checks : burnsideF48s_sp43CheckGens () = true ∧
    burnsideF48s_sp43CheckRels () = true ∧ burnsideF48s_sp43CheckLetters () = true ∧
    burnsideF48s_sp43CheckClosed () = true ∧ burnsideF48s_sp43CheckCand () = true :=
  Certificates.certificate7537

theorem burnsideF48s_sp43_rep :
    burnsideF48s_eRec burnsideF48s_sp43G burnsideF48s_sp43LS burnsideF48s_sp43LSi := by
  have hg := burnsideF48s_sp43_checks.1
  simp only [burnsideF48s_sp43CheckGens, Bool.and_eq_true, decide_eq_true_eq] at hg
  intro i
  have hi : (i : ℕ) < burnsideF48s_sp43XY.length := by
    have := i.2
    simp only [burnsideF48s_sp43XY, List.length_cons, List.length_nil]
    omega
  constructor
  · rw [hg.1, burnsideF48s_e_getD_map _ _ hi [] []]
    exact repL_wordP _
  · rw [hg.2, burnsideF48s_e_getD_map _ _ hi [] []]
    show RepL _ (wordP _)⁻¹
    rw [← wordP_invW]
    exact repL_wordP _

theorem burnsideF48s_sp43_G_mem1 {i : Fin 4} (h : i ≠ 3) :
    burnsideF48s_sp43G i ∈ burnsideF48s_sp43P1 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · exact absurd rfl h

theorem burnsideF48s_sp43_G_mem2 {i : Fin 4} (h : i ≠ 2) :
    burnsideF48s_sp43G i ∈ burnsideF48s_sp43P2 := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact absurd rfl h
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem burnsideF48s_sp43_G_mem_sup (i : Fin 4) :
    burnsideF48s_sp43G i ∈ burnsideF48s_sp43P1 ⊔ burnsideF48s_sp43P2 := by
  by_cases h : i = 3
  · subst h
    exact Subgroup.mem_sup_right (burnsideF48s_sp43_G_mem2 (by decide))
  · exact Subgroup.mem_sup_left (burnsideF48s_sp43_G_mem1 h)

theorem burnsideF48s_sp43_letters :
    (∀ w ∈ burnsideF48s_sp43P1W ++ burnsideF48s_sp43R1 ++ burnsideF48s_sp43U, ∀ l ∈ w, l.1 ≠ 3) ∧
    (∀ w ∈ burnsideF48s_sp43P2W ++ burnsideF48s_sp43R2 ++ burnsideF48s_sp43V, ∀ l ∈ w, l.1 ≠ 2) ∧
    (∀ w ∈ burnsideF48s_sp43KW ++ burnsideF48s_sp43TW ++ burnsideF48s_sp43W, ∀ l ∈ w,
      l.1 ≠ 2 ∧ l.1 ≠ 3) := by
  have hl := burnsideF48s_sp43_checks.2.2.1
  simp only [burnsideF48s_sp43CheckLetters, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hl
  exact ⟨hl.1.1, hl.1.2, hl.2⟩

theorem burnsideF48s_sp43_closed :
    burnsideF48s_sp43P1W.length = 648 ∧ burnsideF48s_sp43P2W.length = 648 ∧
    burnsideF48s_sp43P1W.getD 0 [(0, true)] = [] ∧ burnsideF48s_sp43P2W.getD 0 [(0, true)] = [] ∧
    burnsideF48s_sp43KW = [[], burnsideF48s_sp43Word "aaa"] ∧ burnsideF48s_sp43U.length = 8 ∧
    burnsideF48s_sp43V.length = 8 ∧ burnsideF48s_sp43W.length = 8 ∧
    burnsideF48s_eClosed (burnsideF48s_sp43P1W.map burnsideF48s_sp43EvL) burnsideF48s_sp43LS
      [0, 1, 2] = true ∧
    burnsideF48s_eClosed (burnsideF48s_sp43P2W.map burnsideF48s_sp43EvL) burnsideF48s_sp43LS
      [0, 1, 3] = true := by
  have hc := burnsideF48s_sp43_checks.2.2.2.1
  simp only [burnsideF48s_sp43CheckClosed, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem burnsideF48s_sp43_rels :
    (∀ w ∈ burnsideF48s_sp43R1 ++ burnsideF48s_sp43R2, burnsideF48s_ev burnsideF48s_sp43G w = 1) ∧
    (∀ k ∈ [0, 2, 4, 6], burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_eCandRel 4
      (burnsideF48s_sp43U.getD k []) (burnsideF48s_sp43V.getD k []) (burnsideF48s_sp43W.getD k [])) =
        1) ∧
    burnsideF48s_sp43G 0 ^ 6 = 1 ∧ burnsideF48s_sp43G 0 ^ 3 ≠ 1 ∧
    burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_sp43Word "pbpBp") = xY ∧
    burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_sp43Word "aQABpBp") = yY := by
  have hr := burnsideF48s_sp43_checks.2.1
  simp only [burnsideF48s_sp43CheckRels, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hr
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hr
  have hrep := burnsideF48s_sp43_rep
  have e6 : burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_sp43Word "aaaaaa") =
      burnsideF48s_sp43G 0 ^ 6 := by
    simp [burnsideF48s_sp43Word, burnsideF48s_sp43Letter, burnsideF48s_ev, pow_succ, mul_assoc]
  have e3 : burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_sp43Word "aaa") =
      burnsideF48s_sp43G 0 ^ 3 := by
    simp [burnsideF48s_sp43Word, burnsideF48s_sp43Letter, burnsideF48s_ev, pow_succ, mul_assoc]
  refine ⟨fun w hw => burnsideF48s_e_one hrep (h1 w hw), fun k hk => burnsideF48s_e_one hrep (h2 k hk),
    e6 ▸ burnsideF48s_e_one hrep h3, fun h => h4 ?_, ?_, ?_⟩
  · rw [← e3] at h
    exact repL_unique (burnsideF48s_e_repL hrep _) (h ▸ repL_one 45)
  · have h5' : burnsideF48s_eEvL 45 burnsideF48s_sp43LS burnsideF48s_sp43LSi
        (burnsideF48s_sp43Word "pbpBp") = U42F431.xL := h5
    apply Subtype.ext
    exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h5']; exact repL_x)
  · have h6' : burnsideF48s_eEvL 45 burnsideF48s_sp43LS burnsideF48s_sp43LSi
        (burnsideF48s_sp43Word "aQABpBp") = U42F431.yL := h6
    apply Subtype.ext
    exact eq_of_repL (burnsideF48s_e_repL hrep _) (by rw [h6']; exact repL_y)

end Facts

section Model


theorem burnsideF48s_sp43_let1 {w : List (Fin 4 × Bool)} (h : ∀ l ∈ w, l.1 ≠ 3) :
    ∀ l ∈ w, burnsideF48s_sp43G l.1 ∈ burnsideF48s_sp43P1 :=
  fun l hl => burnsideF48s_sp43_G_mem1 (h l hl)

theorem burnsideF48s_sp43_let2 {w : List (Fin 4 × Bool)} (h : ∀ l ∈ w, l.1 ≠ 2) :
    ∀ l ∈ w, burnsideF48s_sp43G l.1 ∈ burnsideF48s_sp43P2 :=
  fun l hl => burnsideF48s_sp43_G_mem2 (h l hl)

theorem burnsideF48s_sp43_getD0 {Ws : List (List (Fin 4 × Bool))} (hn : 0 < Ws.length)
    (h : Ws.getD 0 [(0, true)] = []) : Ws.getD 0 [] = [] := by
  rw [List.getD_eq_getElem _ _ hn] at h ⊢
  exact h

theorem burnsideF48s_sp43_model : burnsideF48s_EModel burnsideF48s_sp43G burnsideF48s_sp43LS
    burnsideF48s_sp43LSi burnsideF48s_sp43P1 burnsideF48s_sp43P2 burnsideF48s_sp43K
    burnsideF48s_sp43P1W burnsideF48s_sp43P2W burnsideF48s_sp43KW burnsideF48s_sp43R1
    burnsideF48s_sp43R2 := by
  have hrep := burnsideF48s_sp43_rep
  obtain ⟨hl1, hl2, hl3⟩ := burnsideF48s_sp43_letters
  obtain ⟨c1, c2, c3, c4, c5, -, -, -, c9, c10⟩ := burnsideF48s_sp43_closed
  obtain ⟨r1, -, r6, -, rx, ry⟩ := burnsideF48s_sp43_rels
  have hK : ∀ z ∈ burnsideF48s_sp43K, z = 1 ∨ z = burnsideF48s_sp43G 0 ^ 3 := by
    intro z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h2 : (burnsideF48s_sp43G 0 ^ 3) ^ (2 : ℕ) = 1 := by rw [← pow_mul]; exact r6
    rw [zpow_eq_zpow_emod' j h2]
    rcases Int.emod_two_eq_zero_or_one j with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  have e3 : burnsideF48s_ev burnsideF48s_sp43G (burnsideF48s_sp43Word "aaa") =
      burnsideF48s_sp43G 0 ^ 3 := by
    simp [burnsideF48s_sp43Word, burnsideF48s_sp43Letter, burnsideF48s_ev, pow_succ, mul_assoc]
  refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← closure_xy_top, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← rx]
      exact burnsideF48s_ev_mem _ _ fun l _ => burnsideF48s_sp43_G_mem_sup l.1
    · rw [← ry]
      exact burnsideF48s_ev_mem _ _ fun l _ => burnsideF48s_sp43_G_mem_sup l.1
  · rw [burnsideF48s_sp43K, Subgroup.zpowers_le]
    exact ⟨pow_mem (burnsideF48s_sp43_G_mem1 (by decide)) 3,
      pow_mem (burnsideF48s_sp43_G_mem2 (by decide)) 3⟩
  · refine burnsideF48s_e_cover hrep (by rw [c1]; norm_num) (burnsideF48s_sp43_getD0
      (by rw [c1]; norm_num) c3) (gs := [0, 1, 2]) c9 (S := {burnsideF48s_sp43G 0,
      burnsideF48s_sp43G 1, burnsideF48s_sp43G 2}) ?_
    rintro s (rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨2, by simp, rfl⟩
  · refine burnsideF48s_e_cover hrep (by rw [c2]; norm_num) (burnsideF48s_sp43_getD0
      (by rw [c2]; norm_num) c4) (gs := [0, 1, 3]) c10 (S := {burnsideF48s_sp43G 0,
      burnsideF48s_sp43G 1, burnsideF48s_sp43G 3}) ?_
    rintro s (rfl | rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩
    · exact ⟨3, by simp, rfl⟩
  · intro z hz
    rw [c5]
    rcases hK z hz with rfl | rfl
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, by rw [List.getD_cons_succ, List.getD_cons_zero, e3]⟩
  · intro i hi
    exact burnsideF48s_sp43_let1 (hl1 _ (List.mem_append_left _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hi []))))
  · intro j hj
    exact burnsideF48s_sp43_let2 (hl2 _ (List.mem_append_left _ (List.mem_append_left _
      (burnsideF48s_e_getD_mem _ hj []))))
  · intro l hl
    rw [c5] at hl ⊢
    rcases (show l = 0 ∨ l = 1 by simp at hl; omega) with rfl | rfl
    · exact Subgroup.one_mem _
    · rw [List.getD_cons_succ, List.getD_cons_zero, e3]
      exact Subgroup.mem_zpowers _
  · intro r hr
    exact ⟨burnsideF48s_sp43_let1 (hl1 r (List.mem_append_left _ (List.mem_append_right _ hr))),
      r1 r (List.mem_append_left _ hr)⟩
  · intro r hr
    exact ⟨burnsideF48s_sp43_let2 (hl2 r (List.mem_append_left _ (List.mem_append_right _ hr))),
      r1 r (List.mem_append_right _ hr)⟩

theorem burnsideF48s_sp43_card_K : Nat.card ↥burnsideF48s_sp43K = 2 := by
  obtain ⟨-, -, r6, r3, -, -⟩ := burnsideF48s_sp43_rels
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [burnsideF48s_sp43K, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [← pow_mul]; exact r6) r3

end Model

section TC


theorem burnsideF48s_sp43_tc {k : ℕ} (hk : k < 8) :
    Finite (PG 4 (burnsideF48s_sp43Ws k)) ∧
      Nat.card (PG 4 (burnsideF48s_sp43Ws k)) ≤ (if k % 2 = 0 then 40 else 1) * 648 :=
  Certificates.certificate7536 k hk


theorem burnsideF48s_sp43_cands : burnsideF48s_ECands burnsideF48s_sp43G burnsideF48s_sp43LS
    burnsideF48s_sp43LSi burnsideF48s_sp43P1 burnsideF48s_sp43P2 burnsideF48s_sp43P1W
    burnsideF48s_sp43P2W burnsideF48s_sp43KW burnsideF48s_sp43R1 burnsideF48s_sp43R2
    burnsideF48s_sp43TW burnsideF48s_sp43U burnsideF48s_sp43V burnsideF48s_sp43W 4 := by
  obtain ⟨hl1, hl2, hl3⟩ := burnsideF48s_sp43_letters
  obtain ⟨-, -, -, -, -, c6, c7, c8, -, -⟩ := burnsideF48s_sp43_closed
  obtain ⟨-, r2, -, -, -, -⟩ := burnsideF48s_sp43_rels
  have hB : ∀ {w : List (Fin 4 × Bool)}, (∀ l ∈ w, l.1 ≠ 2 ∧ l.1 ≠ 3) →
      ∀ l ∈ w, burnsideF48s_sp43G l.1 ∈ burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2 :=
    fun h l hl => ⟨burnsideF48s_sp43_G_mem1 (h l hl).2, burnsideF48s_sp43_G_mem2 (h l hl).1⟩
  have hX : Nat.card ↥Xs = 25920 := card_Xs
  refine ⟨by rw [c6, c7], by rw [c6, c8], fun t ht => hB (hl3 _ (List.mem_append_left _
    (List.mem_append_right _ (burnsideF48s_e_getD_mem _ ht [])))), fun k hk =>
    burnsideF48s_sp43_let1 (hl1 _ (List.mem_append_right _ (burnsideF48s_e_getD_mem _ hk []))),
    fun k hk => burnsideF48s_sp43_let2 (hl2 _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (by rw [c7]; rw [c6] at hk; exact hk) []))),
    fun k hk => hB (hl3 _ (List.mem_append_right _
      (burnsideF48s_e_getD_mem _ (by rw [c8]; rw [c6] at hk; exact hk) []))),
    burnsideF48s_sp43_checks.2.2.2.2, fun k hk => ?_⟩
  rw [c6] at hk
  obtain ⟨hfin, hcard⟩ := burnsideF48s_sp43_tc hk
  refine ⟨hfin, ?_⟩
  rw [hX]
  by_cases hev : k % 2 = 0
  · rw [if_pos hev] at hcard
    refine Or.inr ⟨hcard.trans (by norm_num), r2 k ?_⟩
    interval_cases k <;> simp_all
  · rw [if_neg hev] at hcard
    exact Or.inl (lt_of_le_of_lt hcard (by norm_num))

end TC

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF


theorem burnsideF48s_sp43_conj
    (hB : Nat.card ↥(burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2) = 162) :
    ∀ K'' : Subgroup Y, K'' ≤ burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2 →
      Nat.card ↥K'' = Nat.card ↥burnsideF48s_sp43K →
      ∃ t ∈ burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2, ∀ z, z ∈ K'' ↔
        t * z * t⁻¹ ∈ burnsideF48s_sp43K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB := burnsideF48s_sp43_model.K_le
  have hcK := burnsideF48s_sp43_card_K
  refine burnsideF48s_e_sylow_conj (q := 2) hKB (IsPGroup.of_card (n := 1) (by rw [hcK]; norm_num))
    ?_
  have h := Subgroup.relIndex_mul_card (H := burnsideF48s_sp43K)
    (K := burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2)
  rw [inf_eq_left.2 hKB, hcK, hB] at h
  have h81 : burnsideF48s_sp43K.relIndex (burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2) = 81 := by
    omega
  rw [h81]
  decide


theorem burnsideF48s_sp43_qe
    (hB : Nat.card ↥(burnsideF48s_sp43P1 ⊓ burnsideF48s_sp43P2) = 162)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : Y ≃* E)
    {A₁ A₂ : Subgroup Y}
    (hA : (A₁ = burnsideF48s_sp43P1 ∧ A₂ = burnsideF48s_sp43P2) ∨
      (A₁ = burnsideF48s_sp43P2 ∧ A₂ = burnsideF48s_sp43P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Z : Type} [Group Z] (β : ChF.Cpl M₁ M₂ Z) (hβ : β.IsFaithful) (hcard : 25920 ≤ Nat.card Z)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hK'card : Nat.card ↥K' = 2)
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    {c : ↥(M₁ ⊓ M₂)} (hcK : (c : E) ∈ K') (hrel : (β.φ1 a * β.φ2 b) ^ 4 = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion :=
  burnsideF48s_e_qe burnsideF48s_sp43_model burnsideF48s_sp43_cands (burnsideF48s_sp43_conj hB) θ
    hA hM1 hM2 hgen β hβ (by rw [card_Xs]; exact hcard) haM hbM hK'le
    (by rw [hK'card, burnsideF48s_sp43_card_K]) haK hbK ha2 hb2 hcK hrel

end QE

end CFSG.ASVolI
