module

import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GF2n.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Exponent
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG

variable {P : Type} [Group P]

@[expose] def restrictHom (K : Subgroup (MulAut P)) (U : Subgroup P)
    (hU : ∀ k ∈ K, ∀ x ∈ U, (k : MulAut P) x ∈ U) : K →* MulAut U where
  toFun k :=
    { toFun := fun x => ⟨(k : MulAut P) x, hU _ k.2 _ x.2⟩
      invFun := fun x => ⟨((k : MulAut P))⁻¹ x, hU _ (K.inv_mem k.2) _ x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  map_one' := by
    ext x
    simp
  map_mul' k k' := by
    ext x
    simp

theorem restrictHom_apply (K : Subgroup (MulAut P)) (U : Subgroup P)
    (hU : ∀ k ∈ K, ∀ x ∈ U, (k : MulAut P) x ∈ U) (k : K) (x : U) :
    ((restrictHom K U hU k x : U) : P) = (k : MulAut P) x := rfl

variable [Finite P]

theorem tim78_2_5 {p : ℕ} [Fact p.Prime] (hPc : ∀ a b : P, a * b = b * a)
    (hPp : ∀ a : P, a ^ p = 1) [Nontrivial P] (K : Subgroup (MulAut P))
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hKp : ¬ p ∣ Nat.card K) :
    Nat.card K < Nat.card P - 1 ∨
      (Nat.card K = Nat.card P - 1 ∧
        ∀ x y : P, x ≠ 1 → y ≠ 1 → ∃! k : K, (k : MulAut P) x = y) := by
  classical
  suffices H : ∀ n : ℕ, ∀ (P : Type) [Group P] [Finite P], Nat.card P = n →
      (∀ a b : P, a * b = b * a) → (∀ a : P, a ^ p = 1) → Nontrivial P →
      ∀ K : Subgroup (MulAut P), (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) → ¬ p ∣ Nat.card K →
      Nat.card K < Nat.card P - 1 ∨
        (Nat.card K = Nat.card P - 1 ∧
          ∀ x y : P, x ≠ 1 → y ≠ 1 → ∃! k : K, (k : MulAut P) x = y) from
    H _ P rfl hPc hPp inferInstance K hK hKp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P _ _ hn hPc hPp hnt K hK hKp
  have hcardP : 1 < Nat.card P := Finite.one_lt_card
  have hcard1 : Nat.card {y : P // y ≠ 1} = Nat.card P - 1 := by
    have h := Nat.card_congr (Equiv.sumCompl (fun y : P => y = 1))
    rw [Nat.card_sum, Nat.card_unique] at h
    show Nat.card {y : P // ¬ y = 1} = Nat.card P - 1
    omega
  have hfree_concl : (∀ k : K, ∀ x : P, (k : MulAut P) x = x → x ≠ 1 → k = 1) →
      Nat.card K < Nat.card P - 1 ∨
        (Nat.card K = Nat.card P - 1 ∧
          ∀ x y : P, x ≠ 1 → y ≠ 1 → ∃! k : K, (k : MulAut P) x = y) := by
    intro hfree
    have horb : ∀ x : P, ∀ hx : x ≠ 1, Function.Injective
        (fun k : K => (⟨(k : MulAut P) x, fun h => hx (by
          simpa using congrArg ((k : MulAut P))⁻¹ h)⟩ : {y : P // y ≠ 1})) := by
      intro x hx k k' hkk'
      have h1 : (k : MulAut P) x = (k' : MulAut P) x := congrArg Subtype.val hkk'
      have h2 : ((k'⁻¹ * k : K) : MulAut P) x = x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, h1, MulAut.inv_apply,
          MulEquiv.symm_apply_apply]
      have := hfree _ x h2 hx
      rw [inv_mul_eq_one] at this
      exact this.symm
    obtain ⟨x₀, hx₀⟩ := exists_ne (1 : P)
    have hle : Nat.card K ≤ Nat.card P - 1 := hcard1 ▸ Nat.card_le_card_of_injective _ (horb x₀ hx₀)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, fun x y hx hy => ?_⟩
      have hbij := (horb x hx).bijective_of_nat_card_le (by rw [hcard1, heq])
      obtain ⟨k, hk⟩ := hbij.2 ⟨y, hy⟩
      refine ⟨k, congrArg Subtype.val hk, fun k' hk' => (horb x hx) ?_⟩
      exact Subtype.ext (hk'.trans (congrArg Subtype.val hk).symm)
  by_cases hirr : ∀ U : Subgroup P, (∀ k ∈ K, ∀ x ∈ U, (k : MulAut P) x ∈ U) → U = ⊥ ∨ U = ⊤
  ·
    refine hfree_concl fun k x hkx hx => ?_
    let F : Subgroup P :=
      { carrier := {y | (k : MulAut P) y = y}
        one_mem' := map_one _
        mul_mem' := fun {a b} ha hb => by
          show (k : MulAut P) (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := fun {a} ha => by
          show (k : MulAut P) a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    have hF : ∀ k' ∈ K, ∀ y ∈ F, (k' : MulAut P) y ∈ F := by
      intro k' hk' y hy
      show (k : MulAut P) ((k' : MulAut P) y) = (k' : MulAut P) y
      have hc := hK _ k.2 _ hk'
      rw [← MulAut.mul_apply, hc, MulAut.mul_apply]
      exact congrArg _ hy
    rcases hirr F hF with hbot | htop
    · exact absurd (hbot ▸ (show x ∈ F from hkx)) (by simpa using hx)
    · apply Subtype.ext
      ext y
      have : y ∈ F := htop ▸ Subgroup.mem_top y
      exact this
  push Not at hirr
  obtain ⟨P₀, hP₀inv, hP₀bot, hP₀top⟩ := hirr
  let _ : MulDistribMulAction K P := MulDistribMulAction.compHom P K.subtype
  have hsmul : ∀ (k : K) (x : P), k • x = (k : MulAut P) x := fun _ _ => rfl
  let _ : Fintype K := Fintype.ofFinite K
  have : IsElementaryAbelian p P :=
    { is_comm := ⟨hPc⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hPp }
  obtain ⟨P₁, hcompl, hP₁inv⟩ :=
    CFSG.RankThree.Coprime.exists_isCompl_invariant_subgroup_of_coprime (p := p) (A := K)
      (G := P) (by rwa [← Nat.card_eq_fintype_card]) P₀ (fun k x hx => hP₀inv _ k.2 _ hx)
  have hP₁inv' : ∀ k ∈ K, ∀ x ∈ P₁, (k : MulAut P) x ∈ P₁ := fun k hk x hx =>
    hP₁inv ⟨k, hk⟩ x hx
  have hinf : P₀ ⊓ P₁ = ⊥ := hcompl.inf_eq_bot
  have hsup : P₀ ⊔ P₁ = ⊤ := hcompl.sup_eq_top
  have hP₁bot : P₁ ≠ ⊥ := fun h => hP₀top (by rw [← sup_bot_eq P₀, ← h, hsup])
  have hP₁top : P₁ ≠ ⊤ := fun h => hP₀bot (by rw [← inf_top_eq P₀, ← h, hinf])
  have hcardP01 : Nat.card P = Nat.card P₀ * Nat.card P₁ := by
    have hN : P₀ ≤ Subgroup.normalizer (P₁ : Set P) := fun a _ =>
      Subgroup.mem_normalizer_iff.mpr fun b => by rw [hPc a b, mul_inv_cancel_right]
    have h := PartTwo.Sec6.card_sup_mul_card_inf hN
    rw [hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top] at h
    exact h
  have hlt₀ : Nat.card P₀ < Nat.card P := by
    rw [← Subgroup.card_top (G := P)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hP₀top)
  have hlt₁ : Nat.card P₁ < Nat.card P := by
    rw [← Subgroup.card_top (G := P)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hP₁top)
  have hnt₀ : Nontrivial P₀ := (Subgroup.nontrivial_iff_ne_bot P₀).mpr hP₀bot
  have hnt₁ : Nontrivial P₁ := (Subgroup.nontrivial_iff_ne_bot P₁).mpr hP₁bot
  have hc₀ : ∀ a b : P₀, a * b = b * a := fun a b => Subtype.ext (hPc a b)
  have hc₁ : ∀ a b : P₁, a * b = b * a := fun a b => Subtype.ext (hPc a b)
  have hp₀ : ∀ a : P₀, a ^ p = 1 := fun a => Subtype.ext (by simpa using hPp a)
  have hp₁ : ∀ a : P₁, a ^ p = 1 := fun a => Subtype.ext (by simpa using hPp a)
  set ρ₀ := restrictHom K P₀ hP₀inv with hρ₀
  set ρ₁ := restrictHom K P₁ hP₁inv' with hρ₁
  set K₁ := ρ₀.ker with hK₁
  have hcardK : Nat.card K = Nat.card K₁ * Nat.card ρ₀.range := by
    rw [← Subgroup.card_mul_index K₁, hK₁, Subgroup.index_ker]
  have hK₀c : ∀ a ∈ ρ₀.range, ∀ b ∈ ρ₀.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hK _ a.2 _ b.2)]
  have hK₀p : ¬ p ∣ Nat.card ρ₀.range := fun h => hKp (h.trans ⟨_, by rw [hcardK, mul_comm]⟩)
  have ih₀ := ih _ (hn ▸ hlt₀) P₀ rfl hc₀ hp₀ hnt₀ ρ₀.range hK₀c hK₀p
  have hle₀ : Nat.card ρ₀.range ≤ Nat.card P₀ - 1 := by
    rcases ih₀ with h | h
    · exact h.le
    · exact h.1.le
  set σ := ρ₁.comp K₁.subtype with hσ
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk₀ : ρ₀ k = 1 := k.2
    apply Subtype.ext
    apply Subtype.ext
    ext x
    have hx : x ∈ P₀ ⊔ P₁ := hsup ▸ Subgroup.mem_top x
    have hN : P₁ ≤ Subgroup.normalizer (P₀ : Set P) := fun a _ =>
      Subgroup.mem_normalizer_iff.mpr fun b => by rw [hPc a b, mul_inv_cancel_right]
    obtain ⟨u, hu, v, hv, rfl⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hN hx
    have h1 : ((k : K) : MulAut P) u = u := by
      have := congrArg (fun f : MulAut P₀ => ((f ⟨u, hu⟩ : P₀) : P)) hk₀
      simpa [hρ₀, restrictHom_apply] using this
    have h2 : ((k : K) : MulAut P) v = v := by
      have := congrArg (fun f : MulAut P₁ => ((f ⟨v, hv⟩ : P₁) : P)) hk
      simpa [hσ, hρ₁, restrictHom_apply] using this
    simp [map_mul, h1, h2]
  have hcardσ : Nat.card σ.range = Nat.card K₁ :=
    (Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv).symm
  have hK₁c : ∀ a ∈ σ.range, ∀ b ∈ σ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (Subtype.ext
      (hK _ a.1.2 _ b.1.2))]
  have hK₁p : ¬ p ∣ Nat.card σ.range := by
    rw [hcardσ]
    exact fun h => hKp (h.trans ⟨_, hcardK⟩)
  have ih₁ := ih _ (hn ▸ hlt₁) P₁ rfl hc₁ hp₁ hnt₁ σ.range hK₁c hK₁p
  have hle₁ : Nat.card K₁ ≤ Nat.card P₁ - 1 := by
    rw [← hcardσ]
    rcases ih₁ with h | h
    · exact h.le
    · exact h.1.le
  left
  have ha : 2 ≤ Nat.card P₀ := Finite.one_lt_card
  have hb : 2 ≤ Nat.card P₁ := Finite.one_lt_card
  rw [hcardK, hcardP01]
  obtain ⟨a, ha'⟩ : ∃ a, Nat.card P₀ = a + 2 := ⟨Nat.card P₀ - 2, by omega⟩
  obtain ⟨b, hb'⟩ : ∃ b, Nat.card P₁ = b + 2 := ⟨Nat.card P₁ - 2, by omega⟩
  rw [ha'] at hle₀
  rw [hb'] at hle₁
  rw [ha', hb']
  calc Nat.card K₁ * Nat.card ρ₀.range ≤ (b + 2 - 1) * (a + 2 - 1) := Nat.mul_le_mul hle₁ hle₀
    _ < (a + 2) * (b + 2) - 1 := by
      rw [show b + 2 - 1 = b + 1 by omega, show a + 2 - 1 = a + 1 by omega]
      have : (a + 2) * (b + 2) = (b + 1) * (a + 1) + (a + b + 3) := by ring
      omega

end CFSG.RankThree.GF2n.Tim78
