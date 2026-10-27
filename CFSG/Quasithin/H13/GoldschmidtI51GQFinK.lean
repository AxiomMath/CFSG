module

public import CFSG.Quasithin.H13.Sp62S6OverK

public section

namespace CFSG.Quasithin.H13.I51K

open Equiv Equiv.Perm CFSG.Permutation.FinPack CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.A6K

@[expose] noncomputable def rK (b : Bool) (c : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) true (evenK 6 c) b

@[expose] noncomputable def aK (o : Bool) (c : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (p2K c) (p1K c) o

@[expose] noncomputable def bK (o : Bool) (c : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (p1K c) (p2K c) o

theorem rK_iff (b : Bool) (σ : Perm (Fin 6)) : (b = false ∨ sign σ = 1) ↔ rK b (enc σ) = true := by
  cases b
  · exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
  · rw [sign_eq_one_iff_evenK h16]
    exact ⟨fun h => h.resolve_left (by decide), Or.inr⟩

theorem aK_iff (o : Bool) (σ : Perm (Fin 6)) : (if o then InP1 σ else InP2 σ) ↔ aK o (enc σ) = true := by
  cases o
  · rw [if_neg Bool.false_ne_true]
    exact (p2K_iff σ).symm
  · rw [if_pos rfl]
    exact (p1K_iff σ).symm

theorem bK_iff (o : Bool) (σ : Perm (Fin 6)) : (if o then InP2 σ else InP1 σ) ↔ bK o (enc σ) = true := by
  cases o
  · rw [if_neg Bool.false_ne_true]
    exact (p1K_iff σ).symm
  · rw [if_pos rfl]
    exact (p2K_iff σ).symm

@[expose] noncomputable def NC (o : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 4534290 1061460 o

@[expose] noncomputable def FC (o : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 5456160 5456385 o

@[expose] noncomputable def LP1c : List ℕ :=
  [5517840, 4534800, 5514000, 4530960, 5517600, 4534560, 5509920, 4526880, 5513520, 4530480,
    5509680, 4526640, 5517825, 4534785, 5513985, 4530945, 5517345, 4534305, 5505825, 4522785,
    5513265, 4530225, 5505585, 4522545, 5517570, 4534530, 5509890, 4526850, 5517330, 4534290,
    5505810, 4522770, 5509170, 4526130, 5505330, 4522290, 5513475, 4530435, 5509635, 4526595,
    5513235, 4530195, 5505555, 4522515, 5509155, 4526115, 5505315, 4522275]

@[expose] noncomputable def LP2c : List ℕ :=
  [5517840, 4534800, 5514000, 4530960, 3298320, 2315280, 3294480, 2311440, 5517825, 4534785,
    5513985, 4530945, 3298305, 2315265, 3294465, 2311425, 5509170, 4526130, 5505330, 4522290,
    1070130, 87090, 1066290, 83250, 5509155, 4526115, 5505315, 4522275, 1070115, 87075, 1066275,
    83235, 3280980, 2297940, 3277140, 2294100, 1061460, 78420, 1057620, 74580, 3280965, 2297925,
    3277125, 2294085, 1061445, 78405, 1057605, 74565]

@[expose] noncomputable def LP1ac : List ℕ :=
  [5517840, 4530960, 4534560, 5509920, 5513520, 4526640, 4534785, 5513985, 5517345, 4522785,
    4530225, 5505585, 5517570, 4526850, 4534290, 5505810, 5509170, 4522290, 4530435, 5509635,
    5513235, 4522515, 4526115, 5505315]

@[expose] noncomputable def LP2ac : List ℕ :=
  [5517840, 4530960, 3298320, 2311440, 4534785, 5513985, 2315265, 3294465, 5509170, 4522290,
    1070130, 83250, 4526115, 5505315, 87075, 1066275, 3280980, 2294100, 1061460, 74580, 2297925,
    3277125, 78405, 1057605]

@[expose] noncomputable def LAc (b o : Bool) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) LP2c LP2ac b)
    (Bool.rec (motive := fun _ => List ℕ) LP1c LP1ac b) o

@[expose] noncomputable def LSc (o : Bool) : List ℕ :=
  Bool.rec (motive := fun _ => List ℕ)
    [5517840, 3490320, 4411920, 4534560, 5456160, 3428640, 5513520, 2441520, 4346160, 3481920,
      5386560, 2314560, 4399440, 2371920, 3293520]
    [5517840, 3490320, 4411920, 5391120, 2380560, 3298320, 1393440, 4281120, 1266720, 2184240,
      5260065, 283425, 3167265, 152625, 1070130] o

@[expose] noncomputable def all4 (q : Bool → Bool → ℕ → Bool) (c : ℕ) : Bool :=
  q false false c && q false true c && q true false c && q true true c

theorem all4_iff {q : Bool → Bool → ℕ → Bool} {c : ℕ} :
    all4 q c = true → ∀ b o, q b o c = true := by
  intro h b o
  simp only [all4, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases b <;> cases o
  exacts [h1, h2, h3, h4]

theorem enc_ip (a n σ : Perm (Fin 6)) :
    enc ((a * n)⁻¹ * σ) = mulK 6 (invPK 6 (mulK 6 (enc a) (enc n))) (enc σ) := by
  rw [enc_mul h16, enc_inv h16, enc_mul h16]

theorem exists_of_anyK {l : List (Perm (Fin 6))} {L : List ℕ} (hL : l.map enc = L) {f : ℕ → Bool}
    (h : anyK f L = true) : ∃ a ∈ l, f (enc a) = true := by
  obtain ⟨x, hx, hf⟩ := anyK_iff.1 h
  rw [← hL, List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, hf⟩

@[expose] noncomputable def ipA (t : ℕ → Bool) (L : List ℕ) (N c : ℕ) : Bool :=
  anyK (fun a => t (mulK 6 (invPK 6 (mulK 6 a N)) c)) L

variable {A : Perm (Fin 6) → Prop} {l : List (Perm (Fin 6))}

theorem ipA_sound {t : ℕ → Bool} (hA : ∀ σ, A σ ↔ t (enc σ) = true) {L : List ℕ}
    (hL : l.map enc = L) {n : Perm (Fin 6)} {N : ℕ} (hN : enc n = N) (σ : Perm (Fin 6))
    (h : ipA t L N (enc σ) = true) : ∃ a ∈ l, A ((a * n)⁻¹ * σ) := by
  obtain ⟨a, ha, hf⟩ := exists_of_anyK hL h
  rw [← hN, ← enc_ip] at hf
  exact ⟨a, ha, (hA _).2 hf⟩

@[expose] noncomputable def qFF (o : Bool) (c : ℕ) : Bool :=
  !aK o c || !aK o (mulK 6 (invPK 6 (mulK 6 c (NC o))) (FC o))

theorem ff_walk : walkK 6 (fun c => qFF false c && qFF true c) 6 0 0 0 = true := by
  decide +kernel

theorem ff_of (o : Bool) {n f : Perm (Fin 6)} (hA : ∀ σ, A σ ↔ aK o (enc σ) = true)
    (hN : enc n = NC o) (hF : enc f = FC o) : ∀ a, A a → ¬ A ((a * n)⁻¹ * f) := by
  intro a ha hz
  have hw := walkK_sound ff_walk a
  have hq : qFF o (enc a) = true := by
    simp only [Bool.and_eq_true] at hw
    cases o
    exacts [hw.1, hw.2]
  rw [qFF.eq_1, (hA a).1 ha, ← hN, ← hF, ← enc_ip, (hA _).1 hz] at hq
  exact absurd hq (by decide)

@[expose] noncomputable def qCov (b o : Bool) (c : ℕ) : Bool :=
  !rK b c || aK o c || ipA (aK o) (LAc b o) (NC o) c || ipA (aK o) (LAc b o) (FC o) c

theorem cover_walk : walkK 6 (all4 qCov) 6 0 0 0 = true := by decide +kernel

theorem cover_of (b o : Bool) {R : Perm (Fin 6) → Prop} {n f : Perm (Fin 6)}
    (hR : ∀ σ, R σ ↔ rK b (enc σ) = true) (hA : ∀ σ, A σ ↔ aK o (enc σ) = true)
    (hL : l.map enc = LAc b o) (hN : enc n = NC o) (hF : enc f = FC o) :
    ∀ σ, R σ → A σ ∨ (∃ a ∈ l, A ((a * n)⁻¹ * σ)) ∨ (∃ a ∈ l, A ((a * f)⁻¹ * σ)) := by
  intro σ hσ
  have hw := all4_iff (walkK_sound cover_walk σ) b o
  rw [qCov.eq_1, (hR σ).1 hσ] at hw
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hw
  rcases hw with (e | e) | e
  · exact Or.inl ((hA σ).2 e)
  · exact Or.inr (Or.inl (ipA_sound hA hL hN σ e))
  · exact Or.inr (Or.inr (ipA_sound hA hL hF σ e))

@[expose] noncomputable def qBs (b o : Bool) (c : ℕ) : Bool :=
  !rK b c || !bK o c || aK o c || ipA (aK o) (LAc b o) (NC o) c

theorem bsub_walk : walkK 6 (all4 qBs) 6 0 0 0 = true := by decide +kernel

theorem bsub_of (b o : Bool) {R B : Perm (Fin 6) → Prop} {n : Perm (Fin 6)}
    (hR : ∀ σ, R σ ↔ rK b (enc σ) = true) (hA : ∀ σ, A σ ↔ aK o (enc σ) = true)
    (hB : ∀ σ, B σ ↔ bK o (enc σ) = true) (hL : l.map enc = LAc b o) (hN : enc n = NC o) :
    ∀ σ, R σ → B σ → A σ ∨ ∃ a ∈ l, A ((a * n)⁻¹ * σ) := by
  intro σ hσ hb
  have hw := all4_iff (walkK_sound bsub_walk σ) b o
  rw [qBs.eq_1, (hR σ).1 hσ, (hB σ).1 hb] at hw
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hw
  rcases hw with e | e
  · exact Or.inl ((hA σ).2 e)
  · exact Or.inr (ipA_sound hA hL hN σ e)

@[expose] noncomputable def qCore (b o : Bool) (c : ℕ) : Bool :=
  !rK b c || !allK (fun s => aK o (mulK 6 (mulK 6 (invPK 6 s) c) s)) (LSc o) || Nat.beq c 5517840

theorem core_walk : walkK 6 (all4 qCore) 6 0 0 0 = true := by decide +kernel

theorem core_of (b o : Bool) {R : Perm (Fin 6) → Prop} {ls : List (Perm (Fin 6))}
    (hR : ∀ σ, R σ ↔ rK b (enc σ) = true) (hA : ∀ σ, A σ ↔ aK o (enc σ) = true)
    (hS : ls.map enc = LSc o) (hE : enc (1 : Perm (Fin 6)) = 5517840) :
    ∀ n, R n → (∀ s ∈ ls, A (s⁻¹ * n * s)) → n = 1 := by
  intro n hn hs
  have hw := all4_iff (walkK_sound core_walk n) b o
  have hall : allK (fun s => aK o (mulK 6 (mulK 6 (invPK 6 s) (enc n)) s)) (LSc o) = true := by
    rw [allK_iff]
    intro x hx
    rw [← hS, List.mem_map] at hx
    obtain ⟨s, hs', rfl⟩ := hx
    try dsimp only
    rw [← enc_inv h16, ← enc_mul h16, ← enc_mul h16]
    exact (hA _).1 (hs s hs')
  rw [qCore.eq_1, (hR n).1 hn, hall] at hw
  simp only [Bool.not_true, Bool.false_or] at hw
  rw [← hE] at hw
  exact (beq_enc_iff h16).1 hw

@[expose] noncomputable def qMem (t : Bool → ℕ → Bool) (L : Bool → Bool → List ℕ) (b o : Bool)
    (c : ℕ) : Bool :=
  !rK b c || !t o c || memK c (L b o)

theorem memA_walk : walkK 6 (all4 (qMem aK LAc)) 6 0 0 0 = true := by decide +kernel

theorem memB_walk : walkK 6 (all4 (qMem bK fun b o => LAc b !o)) 6 0 0 0 = true := by
  decide +kernel

theorem mem_of {t : Bool → ℕ → Bool} {L : Bool → Bool → List ℕ}
    (hw : walkK 6 (all4 (qMem t L)) 6 0 0 0 = true) (b o : Bool) {R : Perm (Fin 6) → Prop}
    (hR : ∀ σ, R σ ↔ rK b (enc σ) = true) (hA : ∀ σ, A σ ↔ t o (enc σ) = true)
    (hL : l.map enc = L b o) : ∀ σ, R σ → A σ → σ ∈ l := by
  intro σ hσ ha
  have h := all4_iff (walkK_sound hw σ) b o
  rw [qMem.eq_1, (hR σ).1 hσ, (hA σ).1 ha] at h
  simp only [Bool.not_true, Bool.false_or] at h
  rw [memK_iff, ← hL, ← mem_iff_enc h16] at h
  exact h

theorem all_of {t : ℕ → Bool} (hA : ∀ σ, A σ ↔ t (enc σ) = true) {L : List ℕ}
    (hL : l.map enc = L) (h : allK t L = true) : ∀ a ∈ l, A a := by
  intro a ha
  have hm : enc a ∈ L := by
    rw [← hL]
    exact List.mem_map_of_mem ha
  exact (hA a).2 (allK_iff.1 h (enc a) hm)

theorem sound_check : ∀ b o : Bool, allK (fun c => rK b c && aK o c) (LAc b o) = true ∧
    allK (fun c => rK b c && bK o c) (LAc b !o) = true ∧ allK (rK true) (LSc o) = true := by
  intro b o
  cases b <;> cases o <;> decide +kernel

@[expose] noncomputable def gqK (b o : Bool) : Bool :=
  allK (fun a => anyK (fun c =>
      aK o (mulK 6 (mulK 6 (invPK 6 c) a) (FC o)) ||
        ipA (aK o) (LAc b o) (NC o) (mulK 6 (mulK 6 (invPK 6 c) a) (FC o))) (LAc b !o))
    (LAc b o)

theorem gq_check : ∀ b o : Bool, gqK b o = true := by
  intro b o
  cases b <;> cases o <;> decide +kernel

theorem gq3_of (b o : Bool) {la lb : List (Perm (Fin 6))} {n f : Perm (Fin 6)}
    (hA : ∀ σ, A σ ↔ aK o (enc σ) = true) (hLA : la.map enc = LAc b o)
    (hLB : lb.map enc = LAc b !o) (hN : enc n = NC o) (hF : enc f = FC o) :
    ∀ a ∈ la, ∃ c ∈ lb, (A (c⁻¹ * a * f) ∨ ∃ a' ∈ la, A ((a' * n)⁻¹ * (c⁻¹ * a * f))) := by
  intro a ha
  have hm : enc a ∈ LAc b o := by
    rw [← hLA]
    exact List.mem_map_of_mem ha
  have hx := allK_iff.1 (gq_check b o) (enc a) hm
  try dsimp only at hx
  obtain ⟨c, hc, hf⟩ := exists_of_anyK hLB hx
  try dsimp only at hf
  have hz : mulK 6 (mulK 6 (invPK 6 (enc c)) (enc a)) (FC o) = enc (c⁻¹ * a * f) := by
    rw [enc_mul h16, enc_mul h16, enc_inv h16, hF]
  rw [hz, Bool.or_eq_true] at hf
  refine ⟨c, hc, ?_⟩
  rcases hf with e | e
  · exact Or.inl ((hA _).2 e)
  · exact Or.inr (ipA_sound hA hLA hN _ e)

theorem card_eq (P : Perm (Fin 6) → Prop) [DecidablePred P] (q : ℕ → Bool)
    (hP : ∀ σ, P σ ↔ q (enc σ) = true) : Fintype.card {σ // P σ} = cntK 6 q 6 0 0 0 := by
  rw [Fintype.card_subtype, Finset.filter_congr (fun σ _ => hP σ), card_filter_eq_cntK]

theorem and_iff {P Q : Perm (Fin 6) → Prop} {p q : ℕ → Bool} (hP : ∀ σ, P σ ↔ p (enc σ) = true)
    (hQ : ∀ σ, Q σ ↔ q (enc σ) = true) (σ : Perm (Fin 6)) :
    (P σ ∧ Q σ) ↔ (p (enc σ) && q (enc σ)) = true := by
  rw [Bool.and_eq_true, ← hP, ← hQ]

theorem conj_iff {t : ℕ → Bool} (hA : ∀ σ, A σ ↔ t (enc σ) = true) {f : Perm (Fin 6)} {F Fi : ℕ}
    (hF : enc f = F) (hFi : enc f⁻¹ = Fi) (σ : Perm (Fin 6)) :
    A (f⁻¹ * σ * f) ↔ t (mulK 6 (mulK 6 Fi (enc σ)) F) = true := by
  rw [hA, enc_mul h16, enc_mul h16, hF, hFi]

theorem rA_iff (b o : Bool) (σ : Perm (Fin 6)) :
    ((b = false ∨ sign σ = 1) ∧ (if o then InP1 σ else InP2 σ)) ↔
      (rK b (enc σ) && aK o (enc σ)) = true := by
  rw [Bool.and_eq_true, ← rK_iff, ← aK_iff]

theorem rB_iff (b o : Bool) (σ : Perm (Fin 6)) :
    ((b = false ∨ sign σ = 1) ∧ (if o then InP2 σ else InP1 σ)) ↔
      (rK b (enc σ) && bK o (enc σ)) = true := by
  rw [Bool.and_eq_true, ← rK_iff, ← bK_iff]

theorem rAC_iff (b o : Bool) {f : Perm (Fin 6)} {F : ℕ} (hF : enc f = F) (hFi : enc f⁻¹ = F)
    (σ : Perm (Fin 6)) :
    ((b = false ∨ sign σ = 1) ∧ (if o then InP1 σ else InP2 σ) ∧
        (if o then InP1 (f⁻¹ * σ * f) else InP2 (f⁻¹ * σ * f))) ↔
      (rK b (enc σ) && (aK o (enc σ) && aK o (mulK 6 (mulK 6 F (enc σ)) F))) = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true, ← rK_iff, ← aK_iff, aK_iff o (f⁻¹ * σ * f),
    enc_mul h16, enc_mul h16, hF, hFi]

theorem counts : ∀ b o : Bool,
    cntK 6 (rK b) 6 0 0 0 = 15 * cntK 6 (fun c => rK b c && aK o c) 6 0 0 0 ∧
      cntK 6 (rK b) 6 0 0 0 = 15 * cntK 6 (fun c => rK b c && bK o c) 6 0 0 0 ∧
      cntK 6 (fun c => rK b c && (aK o c && aK o (mulK 6 (mulK 6 (FC o) c) (FC o)))) 6 0 0 0 * 8 =
        cntK 6 (fun c => rK b c && aK o c) 6 0 0 0 ∧
      cntK 6 (fun c => rK b c && (aK o c && aK o (mulK 6 (mulK 6 (NC o) c) (NC o)))) 6 0 0 0 * 6 =
        cntK 6 (fun c => rK b c && aK o c) 6 0 0 0 := by
  intro b o
  cases b <;> cases o <;> decide +kernel

end CFSG.Quasithin.H13.I51K
