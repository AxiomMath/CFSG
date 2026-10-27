module

public import CFSG.Permutation.FinPackAll6

public section

namespace CFSG.Permutation.FinPack

open Equiv

@[expose] noncomputable def mulP6 (p q : ℕ) : ℕ :=
  Nat.add (mulK 6 (lo6 p) (lo6 q)) (Nat.shiftLeft (mulK 6 (hi6 q) (hi6 p)) 24)

@[expose] def invP6 (p : ℕ) : ℕ := Nat.add (hi6 p) (Nat.shiftLeft (lo6 p) 24)

theorem pc6_eq (g : Perm (Fin 6)) : pc6 g = Nat.add (enc g) (Nat.shiftLeft (enc g⁻¹) 24) := rfl

theorem pc6_mul (σ τ : Perm (Fin 6)) : pc6 (σ * τ) = mulP6 (pc6 σ) (pc6 τ) := by
  unfold mulP6
  rw [lo6_pc6, lo6_pc6, hi6_pc6, hi6_pc6, ← enc_mul (by norm_num), ← enc_mul (by norm_num),
    ← mul_inv_rev, pc6_eq]

theorem pc6_inv (σ : Perm (Fin 6)) : pc6 σ⁻¹ = invP6 (pc6 σ) := by
  unfold invP6
  rw [lo6_pc6, hi6_pc6, pc6_eq, inv_inv]

theorem pc6_inj : Function.Injective pc6 := fun σ τ h =>
  enc_inj (by norm_num) (by rw [← lo6_pc6 σ, h, lo6_pc6])

theorem allCodes6_length : allCodes6.length = 720 := by decide +kernel

theorem pc6_surj {p : ℕ} (hp : p ∈ allCodes6) : ∃ σ, pc6 σ = p := by
  have hsub : Finset.univ.image pc6 ⊆ allCodes6.toFinset := fun x hx => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
    exact List.mem_toFinset.2 (memK_iff.1 (pc6_mem_all σ))
  have hcard : allCodes6.toFinset.card ≤ (Finset.univ.image pc6).card := by
    rw [Finset.card_image_of_injective _ pc6_inj, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    exact (List.toFinset_card_le _).trans (le_of_eq (allCodes6_length.trans (by decide)))
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hp' : p ∈ Finset.univ.image pc6 := by
    rw [heq]
    exact List.mem_toFinset.2 hp
  obtain ⟨σ, -, h⟩ := Finset.mem_image.1 hp'
  exact ⟨σ, h⟩

variable {F G H K : Finset (Perm (Fin 6))} {P Q R S : List ℕ}

theorem code_of_image (h : F.image pc6 = P.toFinset) (σ : Perm (Fin 6)) :
    σ ∈ F ↔ memK (pc6 σ) P = true := by
  rw [memK_iff, ← List.mem_toFinset, ← h, pc6_inj.mem_finset_image]

theorem exists_of_image (h : F.image pc6 = P.toFinset) {p : ℕ} (hp : memK p P = true) :
    ∃ σ ∈ F, pc6 σ = p := by
  have hp' : p ∈ F.image pc6 := by
    rw [h]
    exact List.mem_toFinset.2 (memK_iff.1 hp)
  exact Finset.mem_image.1 hp'

theorem card_of_image (h : F.image pc6 = P.toFinset) (hn : P.Nodup) : F.card = P.length := by
  rw [← Finset.card_image_of_injective F pc6_inj, h, List.toFinset_card_of_nodup hn]

theorem image_of_code (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hP : allK (fun p => memK p allCodes6) P = true) : F.image pc6 = P.toFinset := by
  ext p
  rw [List.mem_toFinset, Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact memK_iff.1 ((hF σ).1 hσ)
  · intro hp
    obtain ⟨σ, hσ⟩ := pc6_surj (memK_iff.1 (allK_iff.1 hP p hp))
    refine ⟨σ, (hF σ).2 ?_, hσ⟩
    rw [hσ]
    exact memK_iff.2 hp

theorem code_of_pin {T : Perm (Fin 6) → Prop} {t : ℕ → Bool} (hT : ∀ σ, T σ ↔ t (pc6 σ) = true)
    (hc : allK (fun p => t p == memK p P) allCodes6 = true) (σ : Perm (Fin 6)) :
    T σ ↔ memK (pc6 σ) P = true := by
  have h := allK_iff.1 hc _ (memK_iff.1 (pc6_mem_all σ))
  rw [beq_iff_eq] at h
  rw [hT, h]

theorem norm_iff (hF : F.image pc6 = P.toFinset) (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true)
    (σ : Perm (Fin 6)) : (∀ s ∈ F, σ * s * σ⁻¹ ∈ G) ↔
      allK (fun q => memK (mulP6 (mulP6 (pc6 σ) q) (invP6 (pc6 σ))) Q) P = true := by
  rw [allK_iff]
  constructor
  · intro h q hq
    obtain ⟨s, hs, rfl⟩ := exists_of_image hF (memK_iff.2 hq)
    rw [← pc6_inv, ← pc6_mul, ← pc6_mul, ← hG]
    exact h s hs
  · intro h s hs
    have h1 := h _ (memK_iff.1 ((code_of_image hF s).1 hs))
    rw [← pc6_inv, ← pc6_mul, ← pc6_mul, ← hG] at h1
    exact h1

theorem mul_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hH : ∀ σ, σ ∈ H ↔ memK (pc6 σ) R = true)
    (hc : allK (fun p => allK (fun q => memK (mulP6 p q) R) Q) P = true) :
    ∀ a ∈ F, ∀ b ∈ G, a * b ∈ H := by
  intro a ha b hb
  have h := allK_iff.1 (allK_iff.1 hc _ (memK_iff.1 ((hF a).1 ha))) _ (memK_iff.1 ((hG b).1 hb))
  rw [← pc6_mul, ← hH] at h
  exact h

theorem inv_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hc : allK (fun p => memK (invP6 p) Q) P = true) :
    ∀ a ∈ F, a⁻¹ ∈ G := by
  intro a ha
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF a).1 ha))
  rw [← pc6_inv, ← hG] at h
  exact h

theorem sub_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hc : allK (fun p => memK p Q) P = true) :
    F ⊆ G := fun a ha =>
  (hG a).2 (allK_iff.1 hc _ (memK_iff.1 ((hF a).1 ha)))

theorem sq_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true) {e : ℕ} (he : pc6 1 = e)
    (hc : allK (fun p => Nat.beq (mulP6 p p) e) P = true) : ∀ s ∈ F, s * s = 1 := by
  intro s hs
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [Nat.beq_eq, ← he, ← pc6_mul] at h
  exact pc6_inj h

theorem comm_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true)
    (hc : allK (fun p => allK (fun q => Nat.beq (mulP6 p q) (mulP6 q p)) Q) P = true) :
    ∀ a ∈ F, ∀ b ∈ G, a * b = b * a := by
  intro a ha b hb
  have h := allK_iff.1 (allK_iff.1 hc _ (memK_iff.1 ((hF a).1 ha))) _ (memK_iff.1 ((hG b).1 hb))
  rw [Nat.beq_eq, ← pc6_mul, ← pc6_mul] at h
  exact pc6_inj h

theorem norm_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) {g : Perm (Fin 6)} {c : ℕ} (hg : pc6 g = c)
    (hc : allK (fun p => memK (mulP6 (mulP6 c p) (invP6 c)) Q) P = true) :
    ∀ s ∈ F, g * s * g⁻¹ ∈ G := by
  intro s hs
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [← hg, ← pc6_inv, ← pc6_mul, ← pc6_mul, ← hG] at h
  exact h

theorem conjBy_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) {g : Perm (Fin 6)} {c : ℕ} (hg : pc6 g = c)
    (hc : allK (fun p => memK (mulP6 (mulP6 p c) (invP6 p)) Q) P = true) :
    ∀ σ ∈ F, σ * g * σ⁻¹ ∈ G := by
  intro σ hσ
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF σ).1 hσ))
  rw [← hg, ← pc6_inv, ← pc6_mul, ← pc6_mul, ← hG] at h
  exact h

theorem cen_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true) {g a b : Perm (Fin 6)}
    {c x y : ℕ} (hg : pc6 g = c) (ha : pc6 a = x) (hb : pc6 b = y)
    (hc : allK (fun p => !Nat.beq (mulP6 p c) (mulP6 c p) || Nat.beq p x || Nat.beq p y) P =
      true) :
    ∀ s ∈ F, s * g = g * s → s = a ∨ s = b := by
  intro s hs hsg
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [← hg, ← ha, ← hb, ← pc6_mul, ← pc6_mul, hsg, Nat.beq_refl, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  exact h.imp (fun h => pc6_inj h) (fun h => pc6_inj h)

theorem conj_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hK : K.image pc6 = S.toFinset)
    (hc : allK (fun p => anyK (fun c => memK (mulP6 (mulP6 c p) (invP6 c)) Q) S) P = true) :
    ∀ r ∈ F, ∃ γ ∈ K, γ * r * γ⁻¹ ∈ G := by
  intro r hr
  obtain ⟨c, hcS, h⟩ := anyK_iff.1 (allK_iff.1 hc _ (memK_iff.1 ((hF r).1 hr)))
  obtain ⟨γ, hγ, rfl⟩ := exists_of_image hK (memK_iff.2 hcS)
  rw [← pc6_inv, ← pc6_mul, ← pc6_mul, ← hG] at h
  exact ⟨γ, hγ, h⟩

theorem invol_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hH : ∀ σ, σ ∈ H ↔ memK (pc6 σ) R = true)
    {e : ℕ} (he : pc6 1 = e)
    (hc : allK (fun p => !Nat.beq (mulP6 p p) e || memK p Q || memK p R) P = true) :
    ∀ r ∈ F, r * r = 1 → r ∈ G ∨ r ∈ H := by
  intro r hr hrr
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF r).1 hr))
  rw [← he, ← pc6_mul, hrr, Nat.beq_refl, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    ← hG, ← hH] at h
  exact h

theorem noncomm_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true)
    (hc : allK (fun p => memK p Q || allK (fun q => memK q P || !Nat.beq (mulP6 p q) (mulP6 q p))
      Q) P = true) :
    ∀ x ∈ F, x ∉ G → ∀ y ∈ G, y ∉ F → x * y ≠ y * x := by
  intro x hx hxG y hy hyF hxy
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF x).1 hx))
  rw [Bool.or_eq_true, ← hG] at h
  have h2 := allK_iff.1 (h.resolve_left hxG) _ (memK_iff.1 ((hG y).1 hy))
  rw [← pc6_mul, ← pc6_mul, hxy, Nat.beq_refl, Bool.not_true, Bool.or_false, ← hF] at h2
  exact hyF h2

theorem pick_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) {a b : Perm (Fin 6)} {x y : ℕ} (ha : pc6 a = x)
    (hb : pc6 b = y) (hc : allK (fun p => !memK p Q || Nat.beq p x || Nat.beq p y) P = true) :
    ∀ s ∈ F, s ∈ G → s = a ∨ s = b := by
  intro s hs hsG
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [← ha, ← hb, (hG s).1 hsG, Bool.not_true, Bool.false_or, Bool.or_eq_true, Nat.beq_eq,
    Nat.beq_eq] at h
  exact h.imp (fun h => pc6_inj h) (fun h => pc6_inj h)

theorem notin_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true)
    (hG : ∀ σ, σ ∈ G ↔ memK (pc6 σ) Q = true) (hc : allK (fun p => !memK p Q) P = true) :
    ∀ s ∈ F, s ∉ G := by
  intro s hs hsG
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [(hG s).1 hsG, Bool.not_true] at h
  exact Bool.false_ne_true h

theorem ne_one_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true) {e : ℕ} (he : pc6 1 = e)
    (hc : allK (fun p => !Nat.beq p e) P = true) : ∀ s ∈ F, s ≠ 1 := by
  intro s hs hs1
  have h := allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs))
  rw [hs1, he, Nat.beq_refl, Bool.not_true] at h
  exact Bool.false_ne_true h

theorem gen_of_check (hF : ∀ σ, σ ∈ F ↔ memK (pc6 σ) P = true) (hX : G.image pc6 = Q.toFinset)
    (hY : H.image pc6 = R.toFinset) (hZ : K.image pc6 = S.toFinset)
    (hc : allK (fun s => anyK (fun x => anyK (fun y => anyK (fun z =>
      Nat.beq s (mulP6 (mulP6 x y) z)) S) R) Q) P = true) :
    ∀ s ∈ F, ∃ x ∈ G, ∃ y ∈ H, ∃ z ∈ K, s = x * y * z := by
  intro s hs
  obtain ⟨x, hxQ, h⟩ := anyK_iff.1 (allK_iff.1 hc _ (memK_iff.1 ((hF s).1 hs)))
  obtain ⟨y, hyR, h⟩ := anyK_iff.1 h
  obtain ⟨z, hzS, h⟩ := anyK_iff.1 h
  obtain ⟨σx, hσx, rfl⟩ := exists_of_image hX (memK_iff.2 hxQ)
  obtain ⟨σy, hσy, rfl⟩ := exists_of_image hY (memK_iff.2 hyR)
  obtain ⟨σz, hσz, rfl⟩ := exists_of_image hZ (memK_iff.2 hzS)
  rw [Nat.beq_eq, ← pc6_mul, ← pc6_mul] at h
  exact ⟨σx, hσx, σy, hσy, σz, hσz, pc6_inj h⟩

end CFSG.Permutation.FinPack
