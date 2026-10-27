module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLMain

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

@[expose] def Y0 : Subgroup orth.W := commW orth S5Syl (commW orth S5Syl ⊤)

@[expose] def qList (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) : List (Perm (Fin 5)) → orth.W
  | [] => 1
  | h :: t => qList c t * (t.map (fun h' => c h h')).prod

structure FormHyp (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) : Prop where
  equi : ∀ k h h', c (k * h) (k * h') = orth.act k (c h h')
  right : ∀ h h' t, t ∈ S5That → c (h * t) h' = c h h'
  symm : ∀ h h', c h h' = c h' h
  diag : ∀ h, c h h = 1
  block : ∀ h d, d ∈ S5Syl → c h (h * d) = 1

@[expose] def PCond (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) : Prop :=
  (∀ h h', (c h 1 ∈ Y0 ∧ c h S5g ∈ Y0) ∨ (c h' 1 ∈ Y0 ∧ c h' S5g ∈ Y0) ∨
      (c h 1 * (c h' 1)⁻¹ ∈ Y0 ∧ c h S5g * (c h' S5g)⁻¹ ∈ Y0)) ∧
  (∀ h, ¬ (c h 1 ∈ Y0 ∧ c h S5g ∈ Y0) →
      c h 1 ∉ Y0 ∧ c h S5g ∉ Y0 ∧ c h 1 * (c h S5g)⁻¹ ∉ Y0)

@[expose] def K2Cond (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) : Prop :=
  ∀ x : List (Perm (Fin 5)), (x.map (fun h => c h 1)).prod = 1 →
    (x.map (fun h => c h S5g)).prod = 1 → qList c x ∈ Y0

namespace FL

theorem qList_eq (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) :
    ∀ x, qList c x = qL c x
  | [] => rfl
  | h :: t => by rw [qList, qL, qList_eq c t]

theorem mem_Y0 (w : orth.W) : w ∈ Y0 ↔ pY (enc w) = 0 := mem_Y0_iff w

theorem mul_inv_mem_Y0 (w w' : orth.W) : w * w'⁻¹ ∈ Y0 ↔ pY (enc w) = pY (enc w') := by
  rw [mem_Y0, enc_mul, inv_eq_of_mul_eq_one_right (orth.sq w'), pY_xor, xor_eq_zero_iff]

end FL

theorem finite_lemma (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) (hf : FormHyp c)
    (hP : PCond c) (hK : K2Cond c) :
    ∀ h h' s : Perm (Fin 5), (s = h' ∨ s = h' * S5g) →
      ∃ y ∈ Y0, c h s * c (h * S5g) s = orth.act h' y := by
  obtain ⟨m, hm, hc⟩ := FL.complete c hf.equi hf.right hf.symm hf.block
  have hkey := FL.key c m hm hc
    (fun i _ j _ => by
      have h := hP.1 (FL.ptRep i) (FL.ptRep j)
      simp only [FL.mul_inv_mem_Y0] at h
      simpa only [FL.mem_Y0] using h)
    (fun i _ => by
      have h := hP.2 (FL.ptRep i)
      simp only [FL.mul_inv_mem_Y0] at h
      simpa only [FL.mem_Y0] using h)
  rcases hkey with hC | ⟨n, -, h1, h2, h3⟩
  · intro h h' s hs
    have ea : c h s = orth.act h (c 1 (h⁻¹ * s)) := by
      rw [← hf.equi, mul_one, mul_inv_cancel_left]
    have eb : c (h * S5g) s = orth.act h (c S5g (h⁻¹ * s)) := by
      rw [← hf.equi, mul_inv_cancel_left]
    have hact : ∀ w, orth.act h' (orth.act (h⁻¹ * h')⁻¹ w) = orth.act h w := by
      intro w
      rw [← act_mul_apply, show h' * (h⁻¹ * h')⁻¹ = h by group]
    rw [ea, eb, ← map_mul]
    rcases hs with hs | hs
    · rw [hs]
      exact ⟨_, (FL.mem_Y0 _).mpr (hC (h⁻¹ * h')).1, (hact _).symm⟩
    · rw [hs, ← mul_assoc]
      exact ⟨_, (FL.mem_Y0 _).mpr (hC (h⁻¹ * h')).2, (hact _).symm⟩
  · exact absurd ((FL.mem_Y0 _).mp (hK (FL.wit n) h1 h2)) (by rwa [FL.qList_eq])

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
