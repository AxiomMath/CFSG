module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen1
public import CFSG.Quasithin.EmptyFaithful.SzF53MTab
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35N9AGen2K

public section

namespace CFSG.Quasithin

open Equiv CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

namespace S35.N9

@[expose] def key (g : Perm (Fin 5)) : ℕ :=
  (g 0).val + 5 * (g 1).val + 25 * (g 2).val + 125 * (g 3).val + 625 * (g 4).val

@[expose] def reps : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun g => ∀ s ∈ S5SylF, key g ≤ key (g * s)

theorem exists_rep : ∀ g : Perm (Fin 5), ∃ r ∈ reps, ∃ s ∈ S5SylF, g = r * s := by
  intro g
  have hS : ∀ s, s ∈ S5SylF ↔ s ∈ S5Syl := fun s => (mem_S5Syl_iff s).symm
  obtain ⟨s, hs, hmin⟩ := S5SylF.exists_min_image (fun s => key (g * s))
    ⟨1, (hS 1).2 (one_mem _)⟩
  refine ⟨g * s, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun t ht => ?_⟩, s⁻¹,
    (hS _).2 (inv_mem ((hS s).1 hs)), by rw [mul_assoc, mul_inv_cancel, mul_one]⟩
  rw [mul_assoc]
  exact hmin _ ((hS _).2 (mul_mem ((hS s).1 hs) ((hS t).1 ht)))

open CFSG.Permutation.FinPack in
theorem key_eq (g : Perm (Fin 5)) : key g = N9K.keyK (enc g) := by
  have e : ∀ i : Fin 5, rd (enc g) i = (g i).val := fun i => rd_enc N9K.h16 g i
  rw [key, N9K.keyK, ← e 0, ← e 1, ← e 2, ← e 3, ← e 4]
  rfl

open CFSG.Permutation.FinPack in
theorem repK_of {g : Perm (Fin 5)} (hg : g ∈ reps) : N9K.repK (enc g) = true := by
  rw [reps, Finset.mem_filter] at hg
  refine allK_iff.2 fun d hd => ?_
  obtain ⟨s, hs, rfl⟩ := N9K.exists_of_mem_SylC hd
  rw [← enc_mul N9K.h16, ← key_eq, ← key_eq, Nat.ble_eq]
  exact hg.2 s hs

open CFSG.Permutation.FinPack in
theorem coreA' : ∀ g ∈ reps, ∀ a ∈ S5SylF, ∀ b ∈ S5SylF,
    (g * a * g⁻¹) 4 = 4 → (g * b * g⁻¹) 4 = 4 → g * a * g⁻¹ ∉ S5SylF →
    g * b * g⁻¹ ∉ S5SylF → (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹) ∉ S5SylF → False := by
  intro g hg a ha b hb
  have h := walkK_sound N9K.core_walk g
  rw [repK_of hg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  replace h := h.1
  rw [N9K.coreAK.eq_1, passK_apply] at h
  have h1 := allK_iff.1 h _ (memK_iff.1 ((N9K.mem_S5SylF_iff a).1 ha))
  rw [passK_apply] at h1
  have h2 := allK_iff.1 h1 _ (memK_iff.1 ((N9K.mem_S5SylF_iff b).1 hb))
  rw [passK_apply, ← N9K.enc_conj, ← N9K.enc_conj] at h2
  exact N9K.false_of_condAK _ _ h2

@[expose] def CondB (g a b c : Perm (Fin 5)) : Prop :=
  g * a * g⁻¹ ∉ S5SylF → g * b * g⁻¹ ∉ S5SylF → (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹) ∉ S5SylF →
    (g * c * g⁻¹) 4 ≠ 4 →
    reach [swap 0 2, swap 1 3, g * a * g⁻¹, g * b * g⁻¹, g * c * g⁻¹] 4 = Finset.univ

instance (g a b c : Perm (Fin 5)) : Decidable (CondB g a b c) := by
  unfold CondB; infer_instance

open CFSG.Permutation.FinPack in
theorem coreB' : ∀ g ∈ reps, ∀ a ∈ S5SylF, ∀ b ∈ S5SylF, ∀ c ∈ S5SylF, CondB g a b c := by
  intro g hg a ha b hb c hc
  have h := walkK_sound N9K.core_walk g
  rw [repK_of hg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  replace h := h.2
  rw [N9K.coreK.eq_1, passK_apply] at h
  have h1 := allK_iff.1 h _ (memK_iff.1 ((N9K.mem_S5SylF_iff a).1 ha))
  rw [passK_apply] at h1
  have h2 := allK_iff.1 h1 _ (memK_iff.1 ((N9K.mem_S5SylF_iff b).1 hb))
  rw [passK_apply] at h2
  have h3 := allK_iff.1 h2 _ (memK_iff.1 ((N9K.mem_S5SylF_iff c).1 hc))
  rw [passK_apply, ← N9K.enc_conj, ← N9K.enc_conj, ← N9K.enc_conj] at h3
  exact N9K.cond_of _ _ _ h3

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
