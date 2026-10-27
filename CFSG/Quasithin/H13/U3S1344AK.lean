module

public import CFSG.Quasithin.H13.Sp62S6OverK
public import CFSG.Quasithin.H13.U3L139M

public section

namespace CFSG.Quasithin.H13.U3K

open Equiv Equiv.Perm CFSG.Permutation.FinPack CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.A6K
open CFSG.Quasithin.H13.U3

@[expose] noncomputable def a4K (c : ℕ) : Bool := Nat.beq (rd c 4) 4 && (Nat.beq (rd c 5) 5 && evenK 6 c)

@[expose] noncomputable def d6K (c : ℕ) : Bool :=
  Nat.beq (Nat.div (rd c 4) 2) 2 &&
    (Nat.beq (Nat.div (rd c 5) 2) 2 && Nat.beq (Nat.div (rd c 0) 2) (Nat.div (rd c 1) 2))

theorem a4K_iff (σ : Perm (Fin 6)) : InA4 σ ↔ a4K (enc σ) = true := by
  have e4 : rd (enc σ) 4 = σ 4 := rd_enc h16 σ 4
  have e5 : rd (enc σ) 5 = σ 5 := rd_enc h16 σ 5
  simp only [a4K, Bool.and_eq_true, Nat.beq_eq]
  rw [e4, e5, ← sign_eq_one_iff_evenK h16, InA4, Fin.ext_iff, Fin.ext_iff]
  exact Iff.rfl

theorem d6K_iff (σ : Perm (Fin 6)) : InD6 σ ↔ d6K (enc σ) = true := by
  have e0 : rd (enc σ) 0 = σ 0 := rd_enc h16 σ 0
  have e1 : rd (enc σ) 1 = σ 1 := rd_enc h16 σ 1
  have e4 : rd (enc σ) 4 = σ 4 := rd_enc h16 σ 4
  have e5 : rd (enc σ) 5 = σ 5 := rd_enc h16 σ 5
  simp only [d6K, Bool.and_eq_true, Nat.beq_eq]
  rw [e0, e1, e4, e5]
  exact Iff.rfl

theorem p1_iff (σ : Perm (Fin 6)) : InP1 σ ↔ p1K (enc σ) = true := (p1K_iff σ).symm

@[expose] noncomputable def LX : List ℕ :=
  [5517840, 5513985, 5509170, 5505315, 4534800, 4530945, 4526130, 4522275]

@[expose] noncomputable def L4 : List ℕ := [5517840, 5513985, 5509170, 5505315]

variable {l : List (Perm (Fin 6))} {L : List ℕ}

theorem memL (hL : l.map enc = L) (u : Perm (Fin 6)) : memK (enc u) L = true ↔ u ∈ l := by
  rw [memK_iff, ← hL, ← mem_iff_enc h16]

theorem pow16_iff (he : enc (1 : Perm (Fin 6)) = 5517840) (σ : Perm (Fin 6)) :
    σ ^ 16 = 1 ↔ Nat.beq (powK 6 5517840 (enc σ) 16) 5517840 = true := by
  rw [← enc_pow h16 he, ← he, beq_enc_iff h16]

theorem enc_conj (g σ : Perm (Fin 6)) :
    enc (g * σ * g⁻¹) = mulK 6 (mulK 6 (enc g) (enc σ)) (invPK 6 (enc g)) := by
  rw [enc_mul h16, enc_mul h16, enc_inv h16]

@[expose] noncomputable def grpK (L : List ℕ) : Bool :=
  allK (fun a => allK (fun b => memK (mulK 6 a b) L) L && memK (invPK 6 a) L &&
    Nat.beq (mulK 6 a a) 5517840) L

theorem grpX_check : grpK LX = true ∧ allK p1K LX = true := by decide +kernel

theorem grp4_check : grpK L4 = true := by decide +kernel

theorem grp_of (he : enc (1 : Perm (Fin 6)) = 5517840) (hL : l.map enc = L)
    (h : grpK L = true) : (∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) ∧ (∀ a ∈ l, a⁻¹ ∈ l) ∧
      ∀ a ∈ l, a * a = 1 := by
  have hm : ∀ {a : Perm (Fin 6)}, a ∈ l → enc a ∈ L := fun h' => by
    rw [← hL]
    exact List.mem_map_of_mem h'
  have H : ∀ a ∈ l, (∀ b ∈ l, a * b ∈ l) ∧ a⁻¹ ∈ l ∧ a * a = 1 := by
    intro a ha
    have h' := allK_iff.1 h (enc a) (hm ha)
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    refine ⟨fun b hb => ?_, ?_, ?_⟩
    · have := allK_iff.1 h1 (enc b) (hm hb)
      rw [← enc_mul h16, memL hL] at this
      exact this
    · rw [← enc_inv h16, memL hL] at h2
      exact h2
    · rw [← enc_mul h16, ← he, beq_enc_iff h16] at h3
      exact h3
  exact ⟨fun a ha => (H a ha).1, fun a ha => (H a ha).2.1, fun a ha => (H a ha).2.2⟩

theorem p1_of (hL : l.map enc = L) (h : allK p1K L = true) : ∀ a ∈ l, InP1 a := by
  intro a ha
  have hm : enc a ∈ L := by
    rw [← hL]
    exact List.mem_map_of_mem ha
  exact (p1_iff a).2 (allK_iff.1 h (enc a) hm)

@[expose] noncomputable def qNorm (t : ℕ → Bool) (L : List ℕ) (c : ℕ) : Bool :=
  !t c || allK (fun k => memK (mulK 6 (mulK 6 c k) (invPK 6 c)) L) L

theorem normX_walk : walkK 6 (qNorm p1K LX) 6 0 0 0 = true := by decide +kernel

theorem norm4_walk : walkK 6 (qNorm a4K L4) 6 0 0 0 = true := by decide +kernel

theorem normal_of {P : Perm (Fin 6) → Prop} {t : ℕ → Bool} (hP : ∀ σ, P σ ↔ t (enc σ) = true)
    (hL : l.map enc = L) (hw : walkK 6 (qNorm t L) 6 0 0 0 = true) :
    ∀ σ, P σ → ∀ κ ∈ l, σ * κ * σ⁻¹ ∈ l := by
  intro σ hσ κ hκ
  have h := walkK_sound hw σ
  rw [qNorm.eq_1, (hP σ).1 hσ] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have hk : enc κ ∈ L := by
    rw [← hL]
    exact List.mem_map_of_mem hκ
  have := allK_iff.1 h (enc κ) hk
  rw [← enc_conj, memL hL] at this
  exact this

@[expose] noncomputable def qTwo (c : ℕ) : Bool :=
  !a4K c || !Nat.beq (powK 6 5517840 c 16) 5517840 || memK c L4

theorem two_walk : walkK 6 qTwo 6 0 0 0 = true := by decide +kernel

theorem two_of (he : enc (1 : Perm (Fin 6)) = 5517840) (hL : l.map enc = L4) :
    ∀ σ, InA4 σ → σ ^ 16 = 1 → σ ∈ l := by
  intro σ h1 h2
  have h := walkK_sound two_walk σ
  rw [qTwo.eq_1, (a4K_iff σ).1 h1, (pow16_iff he σ).1 h2] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (memL hL σ).1 h

@[expose] noncomputable def qDec (c : ℕ) : Bool :=
  !a4K c || memK c L4 || memK (mulK 6 c 5517570) L4 || memK (mulK 6 c 5517345) L4

theorem dec_walk : walkK 6 qDec 6 0 0 0 = true := by decide +kernel

theorem dec_of {c : Perm (Fin 6)} (hc : enc c = 5517345) (hci : enc c⁻¹ = 5517570)
    (hL : l.map enc = L4) : ∀ σ, InA4 σ → σ ∈ l ∨ σ * c⁻¹ ∈ l ∨ σ * c ∈ l := by
  intro σ h1
  have h := walkK_sound dec_walk σ
  rw [qDec.eq_1, (a4K_iff σ).1 h1, ← hc, ← hci, ← enc_mul h16, ← enc_mul h16] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, memL hL] at h
  rcases h with (e | e) | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

@[expose] noncomputable def qComm (c : ℕ) : Bool :=
  !a4K c || allK (fun k => memK (mulK 6 (mulK 6 (mulK 6 k c) (invPK 6 k)) (invPK 6 c)) L4) LX

theorem comm_walk : walkK 6 qComm 6 0 0 0 = true := by decide +kernel

theorem comm_of {lx : List (Perm (Fin 6))} (hX : lx.map enc = LX) (hL : l.map enc = L4) :
    ∀ κ ∈ lx, ∀ σ, InA4 σ → κ * σ * κ⁻¹ * σ⁻¹ ∈ l := by
  intro κ hκ σ h1
  have h := walkK_sound comm_walk σ
  rw [qComm.eq_1, (a4K_iff σ).1 h1] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have hk : enc κ ∈ LX := by
    rw [← hX]
    exact List.mem_map_of_mem hκ
  have := allK_iff.1 h (enc κ) hk
  rw [← enc_conj, ← enc_inv h16, ← enc_mul h16, memL hL] at this
  exact this

@[expose] noncomputable def qCos12 (c : ℕ) : Bool :=
  !memK (mulK 6 c 5517570) L4 ||
    allK (fun k₁ => allK (fun k₂ =>
      memK (mulK 6 (mulK 6 (mulK 6 c k₁) (invPK 6 k₂)) 5517570) L4 &&
        memK (mulK 6 (mulK 6 (mulK 6 (invPK 6 c) k₁) (invPK 6 k₂)) 5517345) L4) L4) L4

theorem cos12_walk : walkK 6 qCos12 6 0 0 0 = true := by decide +kernel

@[expose] noncomputable def qCos3 (c : ℕ) : Bool :=
  !memK (mulK 6 c 5517345) L4 ||
    allK (fun k => memK (mulK 6 (mulK 6 (invPK 6 c) k) 5517570) L4) L4

theorem cos3_walk : walkK 6 qCos3 6 0 0 0 = true := by decide +kernel

theorem memL4 (hL : l.map enc = L4) {κ : Perm (Fin 6)} (h : κ ∈ l) : enc κ ∈ L4 := by
  rw [← hL]
  exact List.mem_map_of_mem h

theorem cos12_of {c : Perm (Fin 6)} (hc : enc c = 5517345) (hci : enc c⁻¹ = 5517570)
    (hL : l.map enc = L4) : ∀ a : Perm (Fin 6), a * c⁻¹ ∈ l → ∀ κ₁ ∈ l, ∀ κ₂ ∈ l,
      a * κ₁ * κ₂⁻¹ * c⁻¹ ∈ l ∧ a⁻¹ * κ₁ * κ₂⁻¹ * c ∈ l := by
  intro a ha κ₁ h₁ κ₂ h₂
  have h := walkK_sound cos12_walk a
  have e : memK (mulK 6 (enc a) 5517570) L4 = true := by
    rw [← hci, ← enc_mul h16, memL hL]
    exact ha
  rw [qCos12.eq_1, e] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have h' := allK_iff.1 (allK_iff.1 h (enc κ₁) (memL4 hL h₁)) (enc κ₂) (memL4 hL h₂)
  rw [← hc, ← hci, ← enc_inv h16, ← enc_inv h16] at h'
  simp only [← enc_mul h16, Bool.and_eq_true, memL hL] at h'
  exact h'

theorem cos3_of {c : Perm (Fin 6)} (hc : enc c = 5517345) (hci : enc c⁻¹ = 5517570)
    (hL : l.map enc = L4) : ∀ a : Perm (Fin 6), a * c ∈ l → ∀ κ ∈ l, a⁻¹ * κ * c⁻¹ ∈ l := by
  intro a ha κ hκ
  have h := walkK_sound cos3_walk a
  have e : memK (mulK 6 (enc a) 5517345) L4 = true := by
    rw [← hc, ← enc_mul h16, memL hL]
    exact ha
  rw [qCos3.eq_1, e] at h
  simp only [Bool.not_true, Bool.false_or] at h
  have h' := allK_iff.1 h (enc κ) (memL4 hL hκ)
  rw [← hci, ← enc_inv h16] at h'
  simp only [← enc_mul h16, memL hL] at h'
  exact h'

@[expose] noncomputable def qCent (c : ℕ) : Bool :=
  !d6K c || !memK (mulK 6 (mulK 6 (mulK 6 c 5517345) (invPK 6 c)) 5517570) L4 || memK c LX

theorem cent_walk : walkK 6 qCent 6 0 0 0 = true := by decide +kernel

theorem cent_of {c : Perm (Fin 6)} (hc : enc c = 5517345) (hci : enc c⁻¹ = 5517570)
    {lx : List (Perm (Fin 6))} (hX : lx.map enc = LX) (hL : l.map enc = L4) :
    ∀ σ, InD6 σ → σ * c * σ⁻¹ * c⁻¹ ∈ l → σ ∈ lx := by
  intro σ h1 h2
  have h := walkK_sound cent_walk σ
  have e2 : memK (mulK 6 (mulK 6 (mulK 6 (enc σ) 5517345) (invPK 6 (enc σ))) 5517570) L4 = true := by
    rw [← hc, ← hci, ← enc_conj, ← enc_mul h16, memL hL]
    exact h2
  rw [qCent.eq_1, (d6K_iff σ).1 h1, e2] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (memL hX σ).1 h

@[expose] noncomputable def qDwit (c : ℕ) : Bool :=
  !d6K c || memK c LX ||
    !Nat.beq (powK 6 5517840 (mulK 6 c (mulK 6 (mulK 6 5517345 c) 5517570)) 16) 5517840 ||
    !Nat.beq (powK 6 5517840 (mulK 6 c (mulK 6 (mulK 6 5509920 c) 5513520)) 16) 5517840

theorem dwit_walk : walkK 6 qDwit 6 0 0 0 = true := by decide +kernel

theorem dwit_of (he : enc (1 : Perm (Fin 6)) = 5517840) {c₁ c₂ : Perm (Fin 6)}
    (h₁ : enc c₁ = 5517345) (h₁i : enc c₁⁻¹ = 5517570) (h₂ : enc c₂ = 5509920)
    (h₂i : enc c₂⁻¹ = 5513520) {lx : List (Perm (Fin 6))} (hX : lx.map enc = LX) :
    ∀ σ, InD6 σ → σ ∉ lx →
      ¬ (σ * (c₁ * σ * c₁⁻¹)) ^ 16 = 1 ∨ ¬ (σ * (c₂ * σ * c₂⁻¹)) ^ 16 = 1 := by
  intro σ h1 h2
  have h := walkK_sound dwit_walk σ
  have e2 : memK (enc σ) LX = false := Bool.eq_false_iff.2 fun e => h2 ((memL hX σ).1 e)
  rw [qDwit.eq_1, (d6K_iff σ).1 h1, e2, ← h₁, ← h₁i, ← h₂, ← h₂i] at h
  simp only [← enc_mul h16, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  rcases h with e | e
  · exact Or.inl fun h => by rw [(pow16_iff he _).1 h] at e; cases e
  · exact Or.inr fun h => by rw [(pow16_iff he _).1 h] at e; cases e

@[expose] noncomputable def wK (c g : ℕ) : Bool :=
  p1K g && (evenK 6 g &&
    !Nat.beq (powK 6 5517840 (mulK 6 c (mulK 6 (mulK 6 g c) (invPK 6 g))) 16) 5517840)

@[expose] noncomputable def qPwit (c : ℕ) : Bool :=
  !p1K c || memK c LX || !Nat.beq (powK 6 5517840 c 16) 5517840 ||
    !walkK 6 (fun g => !wK c g) 6 0 0 0

theorem pwit_walk : walkK 6 qPwit 6 0 0 0 = true := by decide +kernel

theorem pwit_of (he : enc (1 : Perm (Fin 6)) = 5517840) {lx : List (Perm (Fin 6))}
    (hX : lx.map enc = LX) : ∀ σ : Perm (Fin 6), ¬ InP1 σ ∨ σ ∈ lx ∨ ¬ σ ^ 16 = 1 ∨
      ∃ g : Perm (Fin 6), InP1 g ∧ Perm.sign g = 1 ∧ ¬ (σ * (g * σ * g⁻¹)) ^ 16 = 1 := by
  intro σ
  have h := walkK_sound pwit_walk σ
  rw [qPwit.eq_1] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with ((e | e) | e) | e
  · exact Or.inl fun hp => by rw [(p1_iff σ).1 hp] at e; cases e
  · exact Or.inr (Or.inl ((memL hX σ).1 e))
  · exact Or.inr (Or.inr (Or.inl fun hp => by rw [(pow16_iff he σ).1 hp] at e; cases e))
  · obtain ⟨g, hg⟩ := exists_of_walkK (P := wK (enc σ)) e
    rw [wK.eq_1, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', ← enc_conj,
      ← enc_mul h16] at hg
    obtain ⟨g1, g2, g3⟩ := hg
    refine Or.inr (Or.inr (Or.inr ⟨g, (p1_iff g).2 g1, (sign_eq_one_iff_evenK h16 g).2 g2,
      fun hp => ?_⟩))
    rw [(pow16_iff he _).1 hp] at g3
    cases g3

end CFSG.Quasithin.H13.U3K
