module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

namespace StepTwoToral

open Multiplicative

variable {G : Type} [Group G] {p r : ℕ}

structure GGStepTwoCoords (p r : ℕ) (O : Subgroup (ZMod p)ˣ)
    (ι : Multiplicative (Fin r → ZMod p) →* G) (Bs G₀ D : Subgroup G)
    (Pair : G → Subgroup G → Prop) : Prop where
  injective : Function.Injective ι
  range_eq : ι.range = Bs
  move : ∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ), (∀ i, η i ∈ O) → ∏ i, η i = 1 →
    ∃ w ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
      w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i))
  contrary : (r : ZMod p) - 1 = 0 → ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
    (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧ ι (ofAdd s) ∈ D
  comp : ∀ (b : G) (L₁ : Subgroup G), Pair b L₁ → ∀ β : Fin r → ZMod p, ι (ofAdd β) = b →
    (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
      ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → ι (ofAdd s) ∈ L₁) ∨
    (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧ (∀ i, ε i ∈ O) ∧
      (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
      ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 → ι (ofAdd s) ∈ L₁)

theorem exists_ne_one_mem_of_ker [Fact p.Prime] {ι : Multiplicative (Fin r → ZMod p) →* G}
    {D U : Subgroup G} (hD : D ≤ ι.range) (hDcard : Nat.card D = p ^ 2)
    (g : (Fin r → ZMod p) →+ ZMod p) (hU : ∀ s, g s = 0 → ι (ofAdd s) ∈ U) :
    ∃ a ∈ D, a ≠ 1 ∧ a ∈ U := by
  have hp : p.Prime := Fact.out
  have hfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hDcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hcoord : ∀ d : D, ∃ s : Fin r → ZMod p, ι (ofAdd s) = d := fun d => by
    obtain ⟨y, hy⟩ := hD d.2
    exact ⟨toAdd y, by simpa using hy⟩
  choose c hc using hcoord
  have hlt : Nat.card (ZMod p) < Nat.card D := by
    rw [Nat.card_zmod, hDcard]
    exact lt_self_pow₀ hp.one_lt (by norm_num)
  have hni : ¬ Function.Injective (fun d : D => g (c d)) := fun hinj =>
    absurd (Nat.card_le_card_of_injective _ hinj) (not_le.mpr hlt)
  obtain ⟨d₁, d₂, heq, hne⟩ := Function.not_injective_iff.mp hni
  refine ⟨(d₂ : G) * (d₁ : G)⁻¹, D.mul_mem d₂.2 (D.inv_mem d₁.2), ?_, ?_⟩
  · intro h1
    exact hne (Subtype.ext (mul_inv_eq_one.mp h1).symm)
  · have hι : ι (ofAdd (c d₂ - c d₁)) = (d₂ : G) * (d₁ : G)⁻¹ := by
      rw [ofAdd_sub, map_div, hc, hc, div_eq_mul_inv]
    rw [← hι]
    exact hU _ (by rw [map_sub, heq, sub_self])

theorem exists_move_torus {O : Subgroup (ZMod p)ˣ} {ι : Multiplicative (Fin r → ZMod p) →* G}
    {Bs G₀ : Subgroup G}
    (hmove : ∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ), (∀ i, η i ∈ O) → ∏ i, η i = 1 →
      ∃ w ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
        w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i)))
    (k k' : Fin r) {ε o : Fin r → (ZMod p)ˣ} (hε : ∀ i, ε i ∈ O) (ho : ∀ i, o i ∈ O)
    {s : Fin r → ZMod p} (hsk : s k' = 0) (hsum : ∑ i, (o i : ZMod p) * s i = 0) :
    ∃ s' : Fin r → ZMod p, s' k = 0 ∧ ∑ i, (↑(ε i)⁻¹ : ZMod p) * s' i = 0 ∧
      (s ≠ 0 → s' ≠ 0) ∧ ∃ w ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G),
        w⁻¹ * ι (ofAdd s') * w = ι (ofAdd s) := by
  classical
  set π : Equiv.Perm (Fin r) := Equiv.swap k' k with hπ
  set η' : Fin r → (ZMod p)ˣ := fun i => (ε (π i))⁻¹ * (o i)⁻¹ with hη'
  set η : Fin r → (ZMod p)ˣ :=
    Function.update η' k' (∏ i ∈ Finset.univ.erase k', η' i)⁻¹ with hη
  have hη'O : ∀ i, η' i ∈ O := fun i => O.mul_mem (O.inv_mem (hε _)) (O.inv_mem (ho i))
  have hηne : ∀ i, i ≠ k' → η i = η' i := fun i hi => by
    rw [hη, Function.update_of_ne hi]
  have hηO : ∀ i, η i ∈ O := by
    intro i
    by_cases hi : i = k'
    · subst hi
      rw [hη, Function.update_self]
      exact O.inv_mem (O.prod_mem fun j _ => hη'O j)
    · rw [hηne i hi]
      exact hη'O i
  have hηprod : ∏ i, η i = 1 := by
    rw [← Finset.mul_prod_erase Finset.univ η (Finset.mem_univ k'), hη, Function.update_self,
      Finset.prod_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
    exact inv_mul_cancel _
  obtain ⟨w, hw, hws⟩ := hmove π η hηO hηprod
  set s' : Fin r → ZMod p := fun y => (↑(η (π.symm y))⁻¹ : ZMod p) * s (π.symm y) with hs'
  have hcomp : (fun i => (η i : ZMod p) * s' (π i)) = s := by
    funext i
    simp only [hs', Equiv.symm_apply_apply]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  refine ⟨s', ?_, ?_, ?_, w, hw, by rw [hws, hcomp]⟩
  · have hk : π.symm k = k' := by
      rw [hπ, Equiv.symm_swap, Equiv.swap_apply_right]
    simp only [hs', hk, hsk, mul_zero]
  · rw [← Equiv.sum_comp π, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hs', Equiv.symm_apply_apply]
    by_cases hi : i = k'
    · rw [hi, hsk, mul_zero, mul_zero, mul_zero]
    · rw [hηne i hi, ← mul_assoc, ← Units.val_mul, hη']
      congr 2
      rw [mul_inv_rev, inv_inv, inv_inv, mul_comm (o i), inv_mul_cancel_left]
  · intro hs0 hs'0
    apply hs0
    rw [← hcomp, hs'0]
    funext i
    simp

theorem GGStepTwoCoords.exists_witness [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {Bs G₀ D : Subgroup G}
    {Pair : G → Subgroup G → Prop} (h : GGStepTwoCoords p r O ι Bs G₀ D Pair)
    (hD : D ≤ Bs) (hDcard : Nat.card D = p ^ 2) {b : G} {L₁ : Subgroup G} (hpair : Pair b L₁)
    (hb : b ∈ Bs) (hb1 : b ≠ 1) :
    ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
      ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
  classical
  have hDr : D ≤ ι.range := h.range_eq ▸ hD
  obtain ⟨β', hβ'⟩ : b ∈ ι.range := h.range_eq ▸ hb
  set β : Fin r → ZMod p := toAdd β' with hβdef
  have hβ : ι (ofAdd β) = b := by rw [hβdef, ofAdd_toAdd, hβ']
  have hβ0 : β ≠ 0 := fun h0 => hb1 (by rw [← hβ, h0, ofAdd_zero, map_one])
  have hdim : ∀ g : (Fin r → ZMod p) →+ ZMod p,
      (∀ s, g s = 0 → ι (ofAdd s) ∈ Subgroup.zpowers b ⊔ L₁) →
        ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
          ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
    intro g hg
    obtain ⟨a, haD, ha1, haU⟩ := exists_ne_one_mem_of_ker hDr hDcard g hg
    exact ⟨a, Subgroup.mem_inf.mpr ⟨hD haD, haU⟩, ha1, 1,
      Subgroup.mem_inf.mpr ⟨G₀.one_mem, Subgroup.one_mem _⟩, by simpa using haD⟩
  have hcomb : ∀ (t : ZMod p) (s' : Fin r → ZMod p), ι (ofAdd s') ∈ L₁ →
      ι (ofAdd (t • β + s')) ∈ Subgroup.zpowers b ⊔ L₁ := by
    intro t s' hs'
    rw [ofAdd_add, map_mul]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hs')
    have ht : t • β = t.val • β := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
    rw [ht, ofAdd_nsmul, map_pow, hβ]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _
  have hsplit : ∀ (t : ZMod p) (s : Fin r → ZMod p), s = t • β + (s - t • β) := fun t s => by
    abel
  rcases h.comp b L₁ hpair β hβ with ⟨j, j', hβjj, hL⟩ | ⟨k, c, ε, hc, hεO, hβε, hL⟩
  ·
    have hP1 : ∀ j₀ j₁ : Fin r, β j₀ ≠ 0 →
        (∀ s : Fin r → ZMod p, s j₀ = 0 → s j₁ = 0 → ι (ofAdd s) ∈ L₁) →
          ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
            ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
      intro j₀ j₁ hj₀ hL'
      refine hdim (AddMonoidHom.mk' (fun s => β j₁ * s j₀ - β j₀ * s j₁) fun x y => by
        simp only [Pi.add_apply]; ring) fun s hs => ?_
      have hs' : β j₁ * s j₀ - β j₀ * s j₁ = 0 := hs
      rw [hsplit (s j₀ / β j₀) s]
      refine hcomb _ _ (hL' _ ?_ ?_)
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [div_mul_cancel₀ _ hj₀, sub_self]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [sub_eq_zero, div_mul_eq_mul_div, eq_div_iff hj₀]
        linear_combination -hs'
    by_cases hj : β j = 0
    · have hj' : β j' ≠ 0 := by
        intro hj'
        apply hβ0
        funext i
        by_cases hi : i = j
        · rw [hi, hj]
          rfl
        · by_cases hi' : i = j'
          · rw [hi', hj']
            rfl
          · exact hβjj i hi hi'
      exact hP1 j' j hj' fun s h1 h2 => hL s h2 h1
    · exact hP1 j j' hj hL
  ·
    have hr1 : 1 ≤ r := Fin.pos k
    let σ : (Fin r → ZMod p) →+ ZMod p := AddMonoidHom.mk'
      (fun s => ∑ i ∈ Finset.univ.erase k, (↑(ε i)⁻¹ : ZMod p) * s i) fun x y => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hσapp : ∀ s, σ s = ∑ i ∈ Finset.univ.erase k, (↑(ε i)⁻¹ : ZMod p) * s i := fun s => rfl
    have hσsmul : ∀ (t : ZMod p) (s : Fin r → ZMod p), σ (t • s) = t * σ s := fun t s => by
      rw [hσapp, hσapp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    have hσβ : σ β = ((r : ZMod p) - 1) * c := by
      rw [hσapp, Finset.sum_congr rfl fun i hi => by
          rw [hβε i (Finset.ne_of_mem_erase hi), ← mul_assoc, Units.inv_mul, one_mul],
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hr1, Nat.cast_one]
    have hfull : ∀ s : Fin r → ZMod p, s k = 0 →
        ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = σ s := fun s hs => by
      rw [hσapp, ← Finset.add_sum_erase _ _ (Finset.mem_univ k), hs, mul_zero, zero_add]
    have hU : ∀ (t : ZMod p) (s : Fin r → ZMod p), s k = t * β k → σ s = t * σ β →
        ι (ofAdd s) ∈ Subgroup.zpowers b ⊔ L₁ := by
      intro t s hk hσs
      have hk' : (s - t • β) k = 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk, sub_self]
      rw [hsplit t s]
      refine hcomb t _ (hL _ hk' ?_)
      rw [hfull _ hk', map_sub, hσsmul, hσs, sub_self]
    by_cases hr : (r : ZMod p) - 1 = 0
    · by_cases hβk : β k = 0
      ·
        obtain ⟨k₁, o, s, hoO, hs0, hsk, hsum, hsD⟩ := h.contrary hr
        obtain ⟨s', hs'k, hs'sum, hs'0, w, hw, hws⟩ :=
          exists_move_torus h.move k k₁ hεO hoO hsk hsum
        refine ⟨ι (ofAdd s'), Subgroup.mem_inf.mpr ⟨h.range_eq ▸ ⟨ofAdd s', rfl⟩,
          Subgroup.mem_sup_right (hL s' hs'k hs'sum)⟩, fun h1 => hs'0 hs0 ?_, w, hw, ?_⟩
        · exact ofAdd_eq_one.mp (h.injective (h1.trans (map_one ι).symm))
        · rw [hws]
          exact hsD
      ·
        refine hdim σ fun s hs => hU (s k / β k) s ?_ ?_
        · rw [div_mul_cancel₀ _ hβk]
        · rw [hs, hσβ, hr, zero_mul, mul_zero]
    ·
      have hrc : ((r : ZMod p) - 1) * c ≠ 0 := mul_ne_zero hr hc
      refine hdim (AddMonoidHom.mk' (fun s => ((r : ZMod p) - 1) * c * s k - β k * σ s)
        fun x y => by simp only [Pi.add_apply, map_add]; ring) fun s hs => ?_
      have hs' : ((r : ZMod p) - 1) * c * s k - β k * σ s = 0 := hs
      refine hU (σ s / (((r : ZMod p) - 1) * c)) s ?_ ?_
      · rw [div_mul_eq_mul_div, eq_div_iff hrc]
        linear_combination hs'
      · rw [hσβ, div_mul_cancel₀ _ hrc]

theorem contrary_of_sub [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {D : Subgroup G} {i j k : Fin r} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j)
    (hD : ι (ofAdd (Pi.single i 1 - Pi.single j 1 : Fin r → ZMod p)) ∈ D) :
    (r : ZMod p) - 1 = 0 → ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
      (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧
        ι (ofAdd s) ∈ D := by
  intro _
  refine ⟨k, 1, Pi.single i 1 - Pi.single j 1, fun _ => O.one_mem, ?_, ?_, ?_, hD⟩
  · intro h0
    have h := congrFun h0 i
    simp [hij] at h
  · simp [hki, hkj]
  · simp [Finset.sum_sub_distrib]

theorem contrary_of_const [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} {D : Subgroup G} {k i₀ : Fin r} (hi₀ : i₀ ≠ k)
    {ε : Fin r → (ZMod p)ˣ} (hε : ∀ i, ε i ∈ O)
    (hD : ι (ofAdd fun i => if i = k then 0 else (ε i : ZMod p)) ∈ D) :
    (r : ZMod p) - 1 = 0 → ∃ (k : Fin r) (o : Fin r → (ZMod p)ˣ) (s : Fin r → ZMod p),
      (∀ i, o i ∈ O) ∧ s ≠ 0 ∧ s k = 0 ∧ ∑ i, (o i : ZMod p) * s i = 0 ∧
        ι (ofAdd s) ∈ D := by
  classical
  intro hr
  refine ⟨k, fun i => (ε i)⁻¹, fun i => if i = k then 0 else (ε i : ZMod p),
    fun i => O.inv_mem (hε i), ?_, by simp, ?_, hD⟩
  · intro h0
    have h := congrFun h0 i₀
    simp only [hi₀, ite_false, Pi.zero_apply] at h
    exact (ε i₀).ne_zero h
  · have hr1 : 1 ≤ r := Fin.pos k
    calc ∑ i, (↑(ε i)⁻¹ : ZMod p) * (if i = k then 0 else (ε i : ZMod p))
        = ∑ i ∈ Finset.univ.erase k, (1 : ZMod p) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ite_eq_left rfl, mul_zero, zero_add]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [ite_eq_right (Finset.ne_of_mem_erase hi), Units.inv_mul]
      _ = (r : ZMod p) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub hr1, Nat.cast_one]
      _ = 0 := hr

end StepTwoToral

end CFSG.StandardType
