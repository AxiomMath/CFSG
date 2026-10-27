module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffCore

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

@[expose] def InLine (d : Option F) (w : Ix3 → F) : Prop :=
  w ∈ stdF F 3 ∧ OnLine d (w (.inr 1), w (.inr 2))

@[expose] def FixD (d : Option F) (w : Ix3 → F) : Prop := ∀ g ∈ rootD d, g2Act g w = w

@[expose] def lineP (d : Option F) (t : F) : F × F :=
  (Option.elim d 0 fun _ => t, Option.elim d t fun s => s * t)

omit [CharP F 2] in
theorem onLine_lineP (d : Option F) (t : F) : OnLine d (lineP d t) := by
  cases d <;> simp [lineP, OnLine]

omit [CharP F 2] in
theorem lineP_mem_rootD (d : Option F) (t : F) :
    g2A (uSL (lineP d t).1 (lineP d t).2 0) ∈ rootD d :=
  ⟨lineP d t, onLine_lineP d t, rfl⟩

theorem fixD_iff (d : Option F) (w : Ix3 → F) :
    FixD d w ↔ w (.inr 0) = 0 ∧ OnLine d (w (.inl 2), w (.inl 1)) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have h1 := h _ (lineP_mem_rootD d 1)
    rw [g2Act_g2A_uSL] at h1
    cases d with
    | none =>
      have e0 := congrFun h1 (.inl 0)
      have e5 := congrFun h1 (.inr 2)
      simp [lineP, q6] at e0 e5
      exact ⟨e5, e0⟩
    | some s =>
      have e0 := congrFun h1 (.inl 0)
      have e4 := congrFun h1 (.inr 1)
      simp [lineP, q6] at e0 e4
      refine ⟨e4, ?_⟩
      show w (.inl 1) = s * w (.inl 2)
      linear_combination e0 - s * w (.inl 2) * h2
  · rintro ⟨hd, hl⟩ _ ⟨v, hv, rfl⟩
    conv_rhs => rw [q6_eta w]
    rw [g2Act_g2A_uSL]
    refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
    · cases d with
      | none =>
        have hv' : v.1 = 0 := hv
        have hl' : w (.inl 2) = 0 := hl
        rw [hv', hl']
        ring
      | some s =>
        have hv' : v.2 = s * v.1 := hv
        have hl' : w (.inl 1) = s * w (.inl 2) := hl
        rw [hv', hl']
        linear_combination v.1 * s * w (.inl 2) * h2
    · ring
    · rfl
    · rfl
    · rw [hd]
      ring
    · rw [hd]
      ring

theorem fixD_of_mem_F3 (d : Option F) {w : Ix3 → F} (hw : w ∈ stdF F 3) : FixD d w := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  refine (fixD_iff d w).mpr ⟨h3, ?_⟩
  cases d <;> simp [OnLine, h1, h2]

theorem fixD_rootW (d : Option F) : FixD d (rootW d) := fun _ hg => rootD_fix d hg

theorem fixD_smul {d : Option F} {w : Ix3 → F} (hw : FixD d w) (c : F) : FixD d (c • w) :=
  fun g hg => by rw [g2Act_smul, hw g hg]

theorem comm_inLine {d : Option F} {w : Ix3 → F} (hw : FixD d w) {γ : ↥(cayleyGroup F)}
    (hγ : γ ∈ A1 F) : InLine d (g2Act γ w - w) := by
  obtain ⟨hd, hl⟩ := (fixD_iff d w).mp hw
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
  have hγw := g2Act_A1 α p q' (w (.inl 0)) (w (.inl 1)) (w (.inl 2)) (w (.inr 0)) (w (.inr 1))
    (w (.inr 2))
  rw [← q6_eta w] at hγw
  rw [hγw]
  refine ⟨mem_stdF_three.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [Pi.sub_apply, q6_apply_inl1, sub_self]
  · simp only [Pi.sub_apply, q6_apply_inl2, sub_self]
  · simp only [Pi.sub_apply, q6_apply_inr0, sub_self]
  · cases d with
    | none =>
      have hl' : w (.inl 2) = 0 := hl
      show (w (.inr 1) + p * w (.inr 0) + α * w (.inl 2)) - w (.inr 1) = 0
      rw [hd, hl']
      ring
    | some s =>
      have hl' : w (.inl 1) = s * w (.inl 2) := hl
      show (w (.inr 2) + q' * w (.inr 0) + α * w (.inl 1)) - w (.inr 2) =
        s * ((w (.inr 1) + p * w (.inr 0) + α * w (.inl 2)) - w (.inr 1))
      rw [hd, hl']
      ring

theorem exists_comm_eq {d : Option F} {x : Ix3 → F} (hx : InLine d x) :
    ∃ (w₁ w₂ : Ix3 → F) (γ₁ γ₂ : ↥(cayleyGroup F)), FixD d w₁ ∧ FixD d w₂ ∧
      γ₁ ∈ A1 F ∧ γ₂ ∈ A1 F ∧ x = (g2Act γ₁ w₁ - w₁) + (g2Act γ₂ w₂ - w₂) := by
  obtain ⟨hx3, hl⟩ := hx
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hx3
  cases d with
  | none =>
    simp only [OnLine] at hl
    refine ⟨rootW none, rootW none, g2X ![0, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL (x (.inl 0)) 0 0),
      g2X ![x (.inr 2), 0, 0] * g2Y ![0, 0, 0] * g2A (uSL 0 0 0), fixD_rootW _, fixD_rootW _,
      kerElt_mem_A1 _ _ _, kerElt_mem_A1 _ _ _, ?_⟩
    rw [rootW, g2Act_A1, g2Act_A1]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, h1, h2, h3, hl]
  | some s =>
    simp only [OnLine] at hl
    refine ⟨rootW (some s), rootW (some s),
      g2X ![0, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL 0 (x (.inl 0)) 0),
      g2X ![x (.inr 1), 0, 0] * g2Y ![0, 0, 0] * g2A (uSL 0 0 0), fixD_rootW _, fixD_rootW _,
      kerElt_mem_A1 _ _ _, kerElt_mem_A1 _ _ _, ?_⟩
    rw [rootW, g2Act_A1, g2Act_A1]
    funext j
    rcases j with j | j <;> fin_cases j <;> simp [q6, h1, h2, h3, hl]
    ring

theorem mem_rootD_of_fixD {d : Option F} {γ : ↥(cayleyGroup F)} (hγ : γ ∈ A1 F)
    (h : ∀ w, FixD d w → g2Act γ w = w) : γ ∈ rootD d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
  have h1 := h _ (fixD_rootW d)
  cases d with
  | none =>
    rw [rootW, g2Act_A1] at h1
    obtain ⟨e0, -, -, -, -, e5⟩ := q6_inj h1
    have hp : p = 0 := by linear_combination e0
    have hα : α = 0 := by linear_combination e5
    subst hp hα
    exact ⟨(0, q'), rfl, eq_uSL_of_A1⟩
  | some s =>
    rw [rootW, g2Act_A1] at h1
    obtain ⟨e0, -, -, -, e4, -⟩ := q6_inj h1
    have hα : α = 0 := by linear_combination e4
    subst hα
    refine ⟨(p, q'), ?_, eq_uSL_of_A1⟩
    show q' = s * p
    linear_combination e0 - s * p * h2

theorem card_rootD [Finite F] (d : Option F) : Nat.card ↥(rootD d) = Nat.card F := by
  refine le_antisymm (card_rootD_le d) ?_
  have hinj : Function.Injective (fun t : F =>
      (⟨g2A (uSL (lineP d t).1 (lineP d t).2 0), lineP_mem_rootD d t⟩ : ↥(rootD d))) := by
    intro t t' h
    have h1 := g2A_uSL_injective (congrArg Subtype.val h)
    cases d with
    | none => exact (Prod.mk.inj h1).2
    | some s => exact (Prod.mk.inj h1).1
  exact Nat.card_le_card_of_injective _ hinj

theorem card_A1 [Finite F] : Nat.card ↥(A1 F) = Nat.card F ^ 3 := by
  refine le_antisymm card_A1_le ?_
  have hinj : Function.Injective (fun t : Fin 3 → F =>
      (⟨g2X ![t 0, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL (t 1) (t 2) 0), kerElt_mem_A1 _ _ _⟩ :
        ↥(A1 F))) := by
    intro t t' h
    have h1 := congrArg (fun g : ↥(A1 F) => g2Act (g : ↥(cayleyGroup F)) (q6 0 0 0 1 0 0)) h
    simp only [g2Act_A1] at h1
    obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
    have c0 : t 0 = t' 0 := eq_of_mul_self_eq_charTwo (by linear_combination e0)
    have c1 : t 1 = t' 1 := by linear_combination e4
    have c2 : t 2 = t' 2 := by linear_combination e5
    funext i
    fin_cases i
    exacts [c0, c1, c2]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_fin] at h1

theorem relIndex_rootD_A1 [Finite F] (d : Option F) :
    (rootD d).relIndex (A1 F) = Nat.card F ^ 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := rootD d) (K := A1 F)
  rw [inf_of_le_left (rootD_le_A1 d), card_rootD, card_A1] at h1
  have hq : 0 < Nat.card F := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [h1]
  ring

theorem exists_inLine_of_le [Finite F] (y : ↥(cayleyGroup F))
    (h1 : stdF F 1 ≤ gmapG y (stdF F 2)) (h3 : gmapG y (stdF F 2) ≤ stdF F 3) :
    ∃ d : Option F, ∀ w, w ∈ gmapG y (stdF F 2) ↔ InLine d w := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hcard : Nat.card ↥(gmapG y (stdF F 2)) = Nat.card F ^ 2 := by
    rw [card_gmapG, card_stdF (by norm_num)]
  have hu : eu (0 : Fin 3) (1 : F) ∈ gmapG y (stdF F 2) :=
    h1 (mem_stdF_one_iff.mpr ⟨1, by rw [one_smul]⟩)
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ gmapG y (stdF F 2),
      (w (.inr 1), w (.inr 2)) ≠ (0 : F × F) := by
    by_contra hall
    have hle : gmapG y (stdF F 2) ≤ stdF F 1 := by
      intro x hx
      have hx0 : (x (.inr 1), x (.inr 2)) = (0 : F × F) := by
        by_contra hne
        exact hall ⟨x, hx, hne⟩
      obtain ⟨b1, b2, b3⟩ := mem_stdF_three.mp (h3 hx)
      rw [mem_stdF_one_iff]
      refine ⟨x (.inl 0), ?_⟩
      funext j
      rcases j with j | j <;> fin_cases j <;>
        simp [b1, b2, b3, (Prod.mk.inj hx0).1, (Prod.mk.inj hx0).2]
    have h4 := Nat.card_le_card_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
    rw [hcard, card_stdF (by norm_num), pow_one] at h4
    have h5 : Nat.card F < Nat.card F ^ 2 := by
      rw [sq]
      exact lt_mul_self hq
    omega
  refine ⟨dirV (w (.inr 1), w (.inr 2)), fun x => ⟨fun hx => ⟨h3 hx, ?_⟩, fun hx => ?_⟩⟩
  ·
    apply onLine_dirV_of hwne
    by_contra hne
    have hle := card_le_of_three (gmapG y (stdF F 2)).toAddSubgroup (x₁ := eu 0 1) (x₂ := w)
      (x₃ := x) (fun a b c => (gmapG y (stdF F 2)).add_mem
        ((gmapG y (stdF F 2)).add_mem ((gmapG y (stdF F 2)).smul_mem a hu)
          ((gmapG y (stdF F 2)).smul_mem b hw)) ((gmapG y (stdF F 2)).smul_mem c hx))
      (fun a b c habc => by
        have e4 := congrFun habc (.inr 1)
        have e5 := congrFun habc (.inr 2)
        have e0 := congrFun habc (.inl 0)
        simp at e4 e5 e0
        have hdet : x (.inr 1) * w (.inr 2) - x (.inr 2) * w (.inr 1) ≠ 0 := sub_ne_zero.mpr hne
        have hc : c = 0 := (mul_eq_zero.mp (show c *
            (x (.inr 1) * w (.inr 2) - x (.inr 2) * w (.inr 1)) = 0 by
          linear_combination w (.inr 2) * e4 - w (.inr 1) * e5)).resolve_right hdet
        subst hc
        have hb : b = 0 := by
          by_contra hb
          apply hwne
          refine Prod.ext ?_ ?_
          · exact (mul_eq_zero.mp (by linear_combination e4)).resolve_left hb
          · exact (mul_eq_zero.mp (by linear_combination e5)).resolve_left hb
        subst hb
        exact ⟨by linear_combination e0, rfl, rfl⟩)
    have h4 : Nat.card ↥(gmapG y (stdF F 2)).toAddSubgroup = Nat.card F ^ 2 := hcard
    rw [h4] at hle
    have h5 : Nat.card F ^ 2 < Nat.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  ·
    obtain ⟨hx3, hl⟩ := hx
    obtain ⟨b1, b2, b3⟩ := mem_stdF_three.mp hx3
    obtain ⟨c1, c2, c3⟩ := mem_stdF_three.mp (h3 hw)
    obtain ⟨lam, hlam1, hlam2⟩ : ∃ lam : F, x (.inr 1) = lam * w (.inr 1) ∧
        x (.inr 2) = lam * w (.inr 2) := by
      unfold dirV at hl
      split_ifs at hl with hw1
      · have hw1' : w (.inr 1) = 0 := hw1
        have hl' : x (.inr 1) = 0 := hl
        have hw2 : w (.inr 2) ≠ 0 := fun h0 => hwne (Prod.ext hw1 h0)
        exact ⟨x (.inr 2) / w (.inr 2), by rw [hl', hw1', mul_zero], by field_simp⟩
      · have hw1' : w (.inr 1) ≠ 0 := hw1
        have hl' : x (.inr 2) = w (.inr 2) / w (.inr 1) * x (.inr 1) := hl
        refine ⟨x (.inr 1) / w (.inr 1), by field_simp, ?_⟩
        rw [hl']
        field_simp
    have hx' : x = (x (.inl 0) - lam * w (.inl 0)) • eu 0 1 + lam • w := by
      funext j
      rcases j with j | j <;> fin_cases j <;> simp [b1, b2, b3, c1, c2, c3, hlam1, hlam2]
    rw [hx']
    exact (gmapG y (stdF F 2)).add_mem ((gmapG y (stdF F 2)).smul_mem _ hu)
      ((gmapG y (stdF F 2)).smul_mem _ hw)

end CFSG.Quasithin.Vol2.Ch11.G2Q8
