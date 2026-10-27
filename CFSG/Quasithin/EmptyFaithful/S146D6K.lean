module

public import CFSG.Quasithin.EmptyFaithful.S152QDPack

public section

namespace CFSG.Quasithin.S146D6K

open Equiv Finset CFSG.Permutation.FinPack CFSG.LocalAnalysis.RankThreeTheoremC.KFA6Pack
  CFSG.Quasithin.S152QDPack

@[expose] def x0K : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def c4K : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def c0K : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def c1K : Perm (Fin 6) := swap 0 1 * swap 1 4 * swap 2 3 * swap 3 5

@[expose] def inD0P (σ : Perm (Fin 6)) : Prop := σ * x0K = x0K * σ

@[expose] def inSaP (σ : Perm (Fin 6)) : Prop := (σ 4 = 4 ∨ σ 4 = 5) ∧ (σ 5 = 4 ∨ σ 5 = 5)

@[expose] def mpairP (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨ (a = 4 ∧ b = 5) ∨
    (a = 5 ∧ b = 4)

@[expose] def inSbP (σ : Perm (Fin 6)) : Prop :=
  mpairP (σ 0) (σ 2) ∧ mpairP (σ 1) (σ 3) ∧ mpairP (σ 4) (σ 5)

@[expose] def X0K : ℕ := 5509170

@[expose] def C0K : ℕ := 5517345

@[expose] def C1K : ℕ := 2118465

theorem enc_x0 : enc x0K = X0K := by decide +kernel
theorem enc_c0 : enc c0K = C0K := by decide +kernel
theorem enc_c1 : enc c1K = C1K := by decide +kernel

@[expose] def s45 (a : ℕ) : Bool := Nat.beq a 4 || Nat.beq a 5

@[expose] def mpK (a b : ℕ) : Bool :=
  (Nat.beq a 0 && Nat.beq b 2) || (Nat.beq a 2 && Nat.beq b 0) || (Nat.beq a 1 && Nat.beq b 3) ||
    (Nat.beq a 3 && Nat.beq b 1) || (Nat.beq a 4 && Nat.beq b 5) || (Nat.beq a 5 && Nat.beq b 4)

@[expose] def inSaK (c : ℕ) : Bool := s45 (rd c 4) && s45 (rd c 5)

@[expose] def inSbK (c : ℕ) : Bool := mpK (rd c 0) (rd c 2) && mpK (rd c 1) (rd c 3) && mpK (rd c 4) (rd c 5)

@[expose] noncomputable def inD0K (c : ℕ) : Bool := commLaneK 6 c X0K

theorem s45_iff : ∀ a : Fin 6, s45 a = true ↔ (a = 4 ∨ a = 5) := by decide +kernel

theorem mpK_iff : ∀ a b : Fin 6, mpK a b = true ↔ mpairP a b := by
  unfold mpairP
  decide +kernel

theorem mp_symm : ∀ a b : Fin 6, mpairP a b → mpairP b a := by
  unfold mpairP
  decide +kernel

theorem rd6 (σ : Perm (Fin 6)) (i : Fin 6) : rd (enc σ) i = σ i := rd_enc (by norm_num) σ i

theorem inSaK_iff (σ : Perm (Fin 6)) : inSaK (enc σ) = true ↔ inSaP σ := by
  have h4 : rd (enc σ) 4 = ((σ 4 : Fin 6) : ℕ) := rd6 σ 4
  have h5 : rd (enc σ) 5 = ((σ 5 : Fin 6) : ℕ) := rd6 σ 5
  unfold inSaK inSaP
  rw [h4, h5, Bool.and_eq_true, s45_iff, s45_iff]

theorem inSbK_iff (σ : Perm (Fin 6)) : inSbK (enc σ) = true ↔ inSbP σ := by
  have h0 : rd (enc σ) 0 = ((σ 0 : Fin 6) : ℕ) := rd6 σ 0
  have h1 : rd (enc σ) 1 = ((σ 1 : Fin 6) : ℕ) := rd6 σ 1
  have h2 : rd (enc σ) 2 = ((σ 2 : Fin 6) : ℕ) := rd6 σ 2
  have h3 : rd (enc σ) 3 = ((σ 3 : Fin 6) : ℕ) := rd6 σ 3
  have h4 : rd (enc σ) 4 = ((σ 4 : Fin 6) : ℕ) := rd6 σ 4
  have h5 : rd (enc σ) 5 = ((σ 5 : Fin 6) : ℕ) := rd6 σ 5
  unfold inSbK inSbP
  rw [h0, h1, h2, h3, h4, h5, Bool.and_eq_true, Bool.and_eq_true, mpK_iff, mpK_iff, mpK_iff, and_assoc]

theorem inD0K_iff (σ : Perm (Fin 6)) : inD0K (enc σ) = true ↔ inD0P σ := by
  unfold inD0K
  rw [← enc_x0]
  exact commLaneK_iff (by norm_num) σ x0K

theorem false_of_not {b : Bool} {P : Prop} (hb : b = true ↔ P) (h : ¬ P) : b = false := by
  cases b
  · rfl
  · exact absurd (hb.1 rfl) h

theorem not_of_false {b : Bool} {P : Prop} (hb : b = true ↔ P) (h : b = false) : ¬ P := fun hP => by
  rw [hb.2 hP] at h
  exact Bool.noConfusion h

theorem even_test {f : ℕ → Bool} (h : allK f evenCodes6 = true) (σ : Perm (Fin 6))
    (hσ : Perm.sign σ = 1) : f (pc6 σ) = true :=
  allK_iff.1 h _ (memK_iff.1 (pc6_mem_even σ hσ))

theorem code_even {k : ℕ} (h : memK k evenCodes6 = true) :
    ∃ κ : Perm (Fin 6), Perm.sign κ = 1 ∧ pc6 κ = k := by
  have h1 := List.mem_toFinset.2 (memK_iff.1 h)
  rw [← image_even, Finset.mem_image] at h1
  obtain ⟨κ, hκ, e⟩ := h1
  exact ⟨κ, (Finset.mem_filter.1 hκ).2, e⟩

theorem pick {L : List (Perm (Fin 6))} {C : List ℕ} (hL : L.map pc6 = C) {f : ℕ → Bool}
    (h : anyK f C = true) : ∃ δ ∈ L, f (pc6 δ) = true := by
  obtain ⟨a, ha, hf⟩ := anyK_iff.1 h
  rw [← hL, List.mem_map] at ha
  obtain ⟨δ, hδ, rfl⟩ := ha
  exact ⟨δ, hδ, hf⟩

theorem mem_val {L : List (alternatingGroup (Fin 6))} {L' : List (Perm (Fin 6))}
    (h : L.map Subtype.val = L') {δ : Perm (Fin 6)} (hδ : δ ∈ L') :
    ∃ d ∈ L, (d : Perm (Fin 6)) = δ := by
  subst h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hδ
  exact ⟨d, hd, rfl⟩

theorem inD0_mulK {σ τ : Perm (Fin 6)} (h1 : inD0P σ) (h2 : inD0P τ) : inD0P (σ * τ) :=
  Commute.mul_left h1 h2

theorem inD0_invK {σ : Perm (Fin 6)} (h : inD0P σ) : inD0P σ⁻¹ := Commute.inv_left h

theorem inSa_mulK {σ τ : Perm (Fin 6)} (h1 : inSaP σ) (h2 : inSaP τ) : inSaP (σ * τ) := by
  have k : ∀ y : Fin 6, (y = 4 ∨ y = 5) → (σ y = 4 ∨ σ y = 5) := by
    rintro y (rfl | rfl)
    · exact h1.1
    · exact h1.2
  exact ⟨k _ h2.1, k _ h2.2⟩

theorem inSb_map {σ : Perm (Fin 6)} (h : inSbP σ) {a b : Fin 6} (hab : mpairP a b) :
    mpairP (σ a) (σ b) := by
  obtain ⟨h0, h1, h2⟩ := h
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h0
  · exact mp_symm _ _ h0
  · exact h1
  · exact mp_symm _ _ h1
  · exact h2
  · exact mp_symm _ _ h2

theorem inSb_mulK {σ τ : Perm (Fin 6)} (h1 : inSbP σ) (h2 : inSbP τ) : inSbP (σ * τ) :=
  ⟨inSb_map h1 h2.1, inSb_map h1 h2.2.1, inSb_map h1 h2.2.2⟩

@[expose] def tInv (S : ℕ → Bool) (p : ℕ) : Bool := !S (lo6 p) || S (hi6 p)

theorem check_invA : allK (tInv inSaK) evenCodes6 = true := by decide +kernel
theorem check_invB : allK (tInv inSbK) evenCodes6 = true := by decide +kernel

theorem inv_of_check {S : ℕ → Bool} {P : Perm (Fin 6) → Prop} (hS : ∀ σ, S (enc σ) = true ↔ P σ)
    (hc : allK (tInv S) evenCodes6 = true) {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : P σ) :
    P σ⁻¹ := by
  have h1 := even_test hc σ hσ
  unfold tInv at h1
  rw [lo6_pc6, hi6_pc6, (hS σ).2 h, Bool.not_true, Bool.false_or, hS] at h1
  exact h1

theorem inSa_invK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : inSaP σ) : inSaP σ⁻¹ :=
  inv_of_check inSaK_iff check_invA hσ h

theorem inSb_invK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : inSbP σ) : inSbP σ⁻¹ :=
  inv_of_check inSbK_iff check_invB hσ h

@[expose] noncomputable def tSub (S : ℕ → Bool) (p : ℕ) : Bool := !inD0K (lo6 p) || S (lo6 p)

theorem check_subA : allK (tSub inSaK) evenCodes6 = true := by decide +kernel
theorem check_subB : allK (tSub inSbK) evenCodes6 = true := by decide +kernel

theorem sub_of_check {S : ℕ → Bool} {P : Perm (Fin 6) → Prop} (hS : ∀ σ, S (enc σ) = true ↔ P σ)
    (hc : allK (tSub S) evenCodes6 = true) {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : inD0P σ) :
    P σ := by
  have h1 := even_test hc σ hσ
  unfold tSub at h1
  rw [lo6_pc6, (inD0K_iff σ).2 h, Bool.not_true, Bool.false_or, hS] at h1
  exact h1

theorem inD0_inSaK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : inD0P σ) : inSaP σ :=
  sub_of_check inSaK_iff check_subA hσ h

theorem inD0_inSbK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h : inD0P σ) : inSbP σ :=
  sub_of_check inSbK_iff check_subB hσ h

theorem check_card : Nat.beq (centCnt X0K) 8 = true := by decide +kernel

theorem card_D0K :
    Fintype.card {g : alternatingGroup (Fin 6) // (g : Perm (Fin 6)) * x0K = x0K * (g : Perm (Fin 6))} =
      8 := by
  rw [card_cent_eq, enc_x0]
  exact Nat.eq_of_beq_eq_true check_card

@[expose] def lD0 : List (Perm (Fin 6)) :=
  [1, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2, swap 0 2 * swap 4 5,
    swap 1 3 * swap 4 5, c4K * swap 4 5, c4K⁻¹ * swap 4 5]

@[expose] def D0pc : List ℕ :=
  [92573999051280, 92428540579890, 92509322879745, 92363864408355, 76072767270930, 75944421560880,
    76008091091745, 75879745396995]

theorem pin_D0 : lD0.map pc6 = D0pc := by decide +kernel

theorem all_of {L : List (Perm (Fin 6))} {C : List ℕ} (hL : L.map pc6 = C) {f : ℕ → Bool}
    (h : allK f C = true) {δ : Perm (Fin 6)} (hδ : δ ∈ L) : f (pc6 δ) = true :=
  allK_iff.1 h _ (hL ▸ List.mem_map_of_mem hδ)

theorem val_mem {L : List (alternatingGroup (Fin 6))} {L' : List (Perm (Fin 6))}
    (h : L.map Subtype.val = L') {d : alternatingGroup (Fin 6)} (hd : d ∈ L) : (d : Perm (Fin 6)) ∈ L' :=
  h ▸ List.mem_map_of_mem hd

@[expose] noncomputable def tD0 (p : ℕ) : Bool := inD0K (lo6 p)

theorem check_D0pc : allK tD0 D0pc = true := by decide +kernel

theorem sound_of {L : List (Perm (Fin 6))} {C : List ℕ} (hL : L.map pc6 = C)
    (hc : allK tD0 C = true) {δ : Perm (Fin 6)} (hδ : δ ∈ L) : inD0P δ := by
  have h := all_of hL hc hδ
  unfold tD0 at h
  rw [lo6_pc6, inD0K_iff] at h
  exact h

@[expose] noncomputable def dcIn (S : ℕ → Bool) (gi q : ℕ) : Bool :=
  !S (lo6 q) || inD0K (lo6 q) || anyK (fun d => inD0K (mulK 6 gi (mulK 6 (hi6 d) (lo6 q)))) D0pc

@[expose] noncomputable def tDc (S : ℕ → Bool) (p : ℕ) : Bool :=
  !S (lo6 p) || inD0K (lo6 p) || allK (dcIn S (hi6 p)) evenCodes6

theorem check_dcA : allK (tDc inSaK) evenCodes6 = true := by decide +kernel
theorem check_dcB : allK (tDc inSbK) evenCodes6 = true := by decide +kernel

theorem dc_of_check {S : ℕ → Bool} {P : Perm (Fin 6) → Prop} (hS : ∀ σ, S (enc σ) = true ↔ P σ)
    (hc : allK (tDc S) evenCodes6 = true) {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (hs : P σ)
    (hn : ¬ inD0P σ) {τ : Perm (Fin 6)} (hτ : Perm.sign τ = 1) (ht : P τ) :
    inD0P τ ∨ ∃ δ ∈ lD0, inD0P (σ⁻¹ * (δ⁻¹ * τ)) := by
  have h1 := even_test hc σ hσ
  unfold tDc at h1
  rw [lo6_pc6, hi6_pc6, (hS σ).2 hs, false_of_not (inD0K_iff σ) hn] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h2 := even_test h1 τ hτ
  unfold dcIn at h2
  rw [lo6_pc6, (hS τ).2 ht, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact Or.inl ((inD0K_iff τ).1 h2)
  · right
    obtain ⟨δ, hδ, h3⟩ := pick pin_D0 h2
    rw [hi6_pc6, ← enc_mul6, ← enc_mul6, inD0K_iff] at h3
    exact ⟨δ, hδ, h3⟩

theorem dcAK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (hs : inSaP σ) (hn : ¬ inD0P σ)
    {τ : Perm (Fin 6)} (hτ : Perm.sign τ = 1) (ht : inSaP τ) :
    inD0P τ ∨ ∃ δ ∈ lD0, inD0P (σ⁻¹ * (δ⁻¹ * τ)) :=
  dc_of_check inSaK_iff check_dcA hσ hs hn hτ ht

theorem dcBK {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (hs : inSbP σ) (hn : ¬ inD0P σ)
    {τ : Perm (Fin 6)} (hτ : Perm.sign τ = 1) (ht : inSbP τ) :
    inD0P τ ∨ ∃ δ ∈ lD0, inD0P (σ⁻¹ * (δ⁻¹ * τ)) :=
  dc_of_check inSbK_iff check_dcB hσ hs hn hτ ht

@[expose] def lA1 : List (Perm (Fin 6)) := [swap 0 2 * swap 1 3, swap 0 1 * swap 2 3]

@[expose] def lA2 : List (Perm (Fin 6)) := [swap 0 1 * swap 2 3, swap 0 3 * swap 1 2]

@[expose] def lB1 : List (Perm (Fin 6)) := [swap 0 2 * swap 1 3, swap 0 2 * swap 4 5]

@[expose] def lB2 : List (Perm (Fin 6)) := [swap 0 2 * swap 4 5, swap 1 3 * swap 4 5]

@[expose] def A1pc : List ℕ := [92428540579890, 92509322879745]

@[expose] def A2pc : List ℕ := [92509322879745, 92363864408355]

@[expose] def B1pc : List ℕ := [92428540579890, 76072767270930]

@[expose] def B2pc : List ℕ := [76072767270930, 75944421560880]

theorem pin_A1 : lA1.map pc6 = A1pc := by decide +kernel
theorem pin_A2 : lA2.map pc6 = A2pc := by decide +kernel
theorem pin_B1 : lB1.map pc6 = B1pc := by decide +kernel
theorem pin_B2 : lB2.map pc6 = B2pc := by decide +kernel

theorem check_A1pc : allK tD0 A1pc = true := by decide +kernel
theorem check_A2pc : allK tD0 A2pc = true := by decide +kernel
theorem check_B1pc : allK tD0 B1pc = true := by decide +kernel
theorem check_B2pc : allK tD0 B2pc = true := by decide +kernel

@[expose] noncomputable def wK (c ci e e' : ℕ) : ℕ := mulK 6 (mulK 6 (mulK 6 (mulK 6 c e) ci) e') c

@[expose] noncomputable def okA (w : ℕ) : Bool := inSaK w && !inD0K w

@[expose] noncomputable def okB (w : ℕ) : Bool := inSbK w && !inD0K w

@[expose] noncomputable def wW (c ci : ℕ) : Bool :=
  inSaK c || inSbK c ||
    (anyK (fun d => anyK (fun d' => okA (wK c ci (lo6 d) (lo6 d'))) A2pc) A1pc &&
      anyK (fun d => anyK (fun d' => okB (wK c ci (lo6 d) (lo6 d'))) B2pc) B1pc)

@[expose] noncomputable def tW (p : ℕ) : Bool := wW (lo6 p) (hi6 p)

theorem check_word : allK tW evenCodes6 = true := by decide +kernel

theorem enc_wK (σ δ δ' : Perm (Fin 6)) :
    wK (enc σ) (enc σ⁻¹) (enc δ) (enc δ') = enc (σ * δ * σ⁻¹ * δ' * σ) := by
  unfold wK
  rw [enc_mul6, enc_mul6, enc_mul6, enc_mul6]

theorem word_of {ok : ℕ → Bool} {P : Perm (Fin 6) → Prop} (hok : ∀ ρ, ok (enc ρ) = true → P ρ)
    {L L' : List (Perm (Fin 6))} {C C' : List ℕ} (hL : L.map pc6 = C) (hL' : L'.map pc6 = C')
    {σ : Perm (Fin 6)}
    (h : anyK (fun d => anyK (fun d' => ok (wK (enc σ) (enc σ⁻¹) (lo6 d) (lo6 d'))) C') C = true) :
    ∃ δ ∈ L, ∃ δ' ∈ L', P (σ * δ * σ⁻¹ * δ' * σ) := by
  obtain ⟨δ, hδ, h1⟩ := pick hL h
  obtain ⟨δ', hδ', h2⟩ := pick hL' h1
  rw [lo6_pc6, lo6_pc6, enc_wK] at h2
  exact ⟨δ, hδ, δ', hδ', hok _ h2⟩

theorem okA_iff (ρ : Perm (Fin 6)) (h : okA (enc ρ) = true) : inSaP ρ ∧ ¬ inD0P ρ := by
  unfold okA at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨(inSaK_iff ρ).1 h.1, not_of_false (inD0K_iff ρ) h.2⟩

theorem okB_iff (ρ : Perm (Fin 6)) (h : okB (enc ρ) = true) : inSbP ρ ∧ ¬ inD0P ρ := by
  unfold okB at h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨(inSbK_iff ρ).1 h.1, not_of_false (inD0K_iff ρ) h.2⟩

theorem word6K {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (ha : ¬ inSaP σ) (hb : ¬ inSbP σ) :
    (∃ δ ∈ lA1, ∃ δ' ∈ lA2, inSaP (σ * δ * σ⁻¹ * δ' * σ) ∧ ¬ inD0P (σ * δ * σ⁻¹ * δ' * σ)) ∧
    (∃ δ ∈ lB1, ∃ δ' ∈ lB2, inSbP (σ * δ * σ⁻¹ * δ' * σ) ∧ ¬ inD0P (σ * δ * σ⁻¹ * δ' * σ)) := by
  have h := even_test check_word σ hσ
  unfold tW at h
  rw [lo6_pc6, hi6_pc6] at h
  unfold wW at h
  rw [false_of_not (inSaK_iff σ) ha, false_of_not (inSbK_iff σ) hb, Bool.false_or, Bool.false_or,
    Bool.and_eq_true] at h
  exact ⟨word_of okA_iff pin_A1 pin_A2 h.1, word_of okB_iff pin_B1 pin_B2 h.2⟩

@[expose] noncomputable def ord3 (c : ℕ) : Bool :=
  Nat.beq (mulK 6 (mulK 6 c c) c) ID6 && !Nat.beq c ID6

@[expose] def xf (e : ℕ) : ℕ := Nat.land e 281474976710655

@[expose] def kf (e : ℕ) : ℕ := Nat.shiftRight e 48

@[expose] def T3 : List ℕ := [
    10218233316221538105308824080, 5577091813490842438639768080, 25397431511507147478275343120,
    11161195492409635248445608720, 20155603608649641907721544720, 10310036692497307594215732240,
    6538188430307925303537968400, 5648493736457115315044758800, 21394375669870436157536604960,
    25456366682102062680485475360, 11239398471656964317712233760, 26018517206529999801622470960,
    20451412940351775072557548080, 11475139264740755097383096880, 20215672700535213920863007040,
    25111822805002097870435979840, 10296436018771943397766017600, 6578989713541050395821093200,
    6234445283173872514895188560, 5672295035379545536970437200, 26057264226971421208535642145,
    25730854220006943728329900065, 6195981609108247137174638625, 21396854914575000590703919665,
    20213476801129750701038437425, 16482571424334700099429074225, 25458845926806626082608919105,
    26057264226971382674119217985, 6576793814135618224335627585, 11241877716361511226908619345,
    26016321307124481812406092625, 20834704115540005903002707025, 21413855434926641358983934210,
    20120540039604270057529884930, 16442903509061685907548229890, 26036863601536142452934837010,
    20524161292316422595029251090, 11529753452710005583663871250, 21377445988123484850362537010,
    21413855434926587346073765170, 25765988644946623965861053250, 25149294803580030020946695490,
    6290051445747238878822073170, 16191295582902564650392491090, 26019863083211121517978194435,
    25709320210335262252521034755, 6248116242236766521827398915, 21376454290153031759817875475,
    25402177509421533954116174355, 11167075134981071540500845075, 26055989187881678702421038115,
    26019863083211067638196225315, 20180608837566633149738590275, 20761034903196317678347374915,
    16427036375986340939079688275, 6562060014567866664161919315, 20217018577216334602399986180,
    20755226097202987233991283460, 15264200539726443880469570820, 25148303105609591228868997140,
    20161483251221076146750947860, 10314782690411692004192104980, 20217018577216316936993182500,
    20833429076450316371205752100, 25131302570058266526824419380, 25711445293555461814380470580,
    5963641163162477483296690260, 15248333130017509593760072020, 6580335590222154580656140805,
    6559934931347647504917349125, 15242524324024164705727882245, 6289059747776729859492163605,
    6542934428222276736723976725, 5654373379028516564447015445, 16481296385244960054034043685,
    6580335590222152514543879205, 16118618067516006365923459125, 6253925048230060888711766325,
    5981916998224103677878276165, 15266325622946611500357386565]

@[expose] noncomputable def conjT (k c x : ℕ) : Bool := Nat.beq (mulK 6 (mulK 6 (lo6 k) c) (hi6 k)) (lo6 x)

@[expose] noncomputable def t3 (e : ℕ) : Bool :=
  memK (kf e) evenCodes6 &&
    ((conjT (kf e) C0K (xf e) && !inSbK (lo6 (xf e))) || (conjT (kf e) C1K (xf e) && !inSaK (lo6 (xf e))))

@[expose] noncomputable def cov (p : ℕ) : Bool := !ord3 (lo6 p) || anyK (fun e => Nat.beq (xf e) p) T3

theorem check_T3 : allK t3 T3 = true := by decide +kernel
theorem check_cov : allK cov evenCodes6 = true := by decide +kernel

theorem conj_of {κ σ τ : Perm (Fin 6)} {c : ℕ} (hc : enc τ = c)
    (h : Nat.beq (mulK 6 (mulK 6 (enc κ) c) (enc κ⁻¹)) (enc σ) = true) : κ * τ * κ⁻¹ = σ := by
  rw [← hc, ← enc_mul6, ← enc_mul6, Nat.beq_eq] at h
  exact enc_inj (by norm_num) h

theorem cls3K {σ : Perm (Fin 6)} (hσ : Perm.sign σ = 1) (h3 : σ * σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ κ : Perm (Fin 6), Perm.sign κ = 1 ∧
      ((κ * c0K * κ⁻¹ = σ ∧ ¬ inSbP σ) ∨ (κ * c1K * κ⁻¹ = σ ∧ ¬ inSaP σ)) := by
  have hc := even_test check_cov σ hσ
  unfold cov ord3 at hc
  have e3 : Nat.beq (mulK 6 (mulK 6 (enc σ) (enc σ)) (enc σ)) ID6 = true := by
    rw [← enc_mul6, ← enc_mul6, ← eq_one_iff]
    exact h3
  rw [lo6_pc6, e3, false_of_not (eq_one_iff σ).symm h1] at hc
  simp only [Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or] at hc
  obtain ⟨e, he, hx⟩ := anyK_iff.1 hc
  rw [Nat.beq_eq] at hx
  have ht := allK_iff.1 check_T3 e he
  unfold t3 at ht
  rw [Bool.and_eq_true] at ht
  obtain ⟨κ, hκ, hk⟩ := code_even ht.1
  have h2 := ht.2
  unfold conjT at h2
  rw [hx, ← hk, lo6_pc6, hi6_pc6, lo6_pc6, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Bool.not_eq_true'] at h2
  refine ⟨κ, hκ, ?_⟩
  rcases h2 with ⟨h2, h4⟩ | ⟨h2, h4⟩
  · exact Or.inl ⟨conj_of enc_c0 h2, not_of_false (inSbK_iff σ) h4⟩
  · exact Or.inr ⟨conj_of enc_c1 h2, not_of_false (inSaK_iff σ) h4⟩

@[expose] noncomputable def tNe (p : ℕ) : Bool := !Nat.beq (mulK 6 (mulK 6 (lo6 p) C0K) (hi6 p)) C1K

theorem check_ne : allK tNe evenCodes6 = true := by decide +kernel

theorem c0_ne_c1K {κ : Perm (Fin 6)} (hκ : Perm.sign κ = 1) : κ * c0K * κ⁻¹ ≠ c1K := by
  intro h
  have h1 := even_test check_ne κ hκ
  unfold tNe at h1
  rw [lo6_pc6, hi6_pc6, ← enc_c0, ← enc_c1, ← enc_mul6, ← enc_mul6, h] at h1
  simp at h1

theorem pair45 : ∀ a b : Fin 6, a ≠ b →
    (((a = 4 ∨ a = 5) ∧ (b = 4 ∨ b = 5)) ↔ ∀ y : Fin 6, (y = a ∨ y = b) ↔ (y = 4 ∨ y = 5)) := by
  decide +kernel

end CFSG.Quasithin.S146D6K
