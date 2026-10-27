module

public import CFSG.LieType.Ree.SuzukiBruhatNormalForm
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.SzTorus

open CFSG.Blueprint CFSG.LieType.Ree

section NatSz

variable {a : ℕ} {K : Type} [Field K]

@[expose] def natFix (a : ℕ) (K : Type) [Field K] (Q : Subgroup (suzukiGroup a K)) :
    Subgroup (Multiplicative (Fin 4 → K)) where
  carrier := {x | ∀ g ∈ Q, natAct (suzukiGroup a K) g x = x}
  one_mem' := fun g _ => by simp [natAct]
  mul_mem' := fun {x y} hx hy g hg => by rw [natAct_mul, hx g hg, hy g hg]
  inv_mem' := fun {x} hx g hg => by
    have : natAct (suzukiGroup a K) g x⁻¹ = (natAct (suzukiGroup a K) g x)⁻¹ := by
      simp [natAct, Matrix.mulVec_neg]
    rw [this, hx g hg]

theorem natAct_S_toAdd (u v : K) (x : Multiplicative (Fin 4 → K)) :
    (natAct (suzukiGroup a K) (suzukiSElt a K u v) x).toAdd =
      ![x.toAdd 0, u * x.toAdd 0 + x.toAdd 1,
        v * x.toAdd 0 + u ^ 2 ^ (a + 1) * x.toAdd 1 + x.toAdd 2,
        suzukiN a u v * x.toAdd 0 + (u ^ (2 ^ (a + 1) + 1) + v) * x.toAdd 1 + u * x.toAdd 2 +
          x.toAdd 3] := by
  ext i
  fin_cases i <;>
    simp [natAct, coe_suzukiSElt, suzukiS, dotProduct, Fin.sum_univ_four]

theorem natAct_D_toAdd (l : Kˣ) (x : Multiplicative (Fin 4 → K)) (i : Fin 4) :
    (natAct (suzukiGroup a K) (suzukiDElt a K l) x).toAdd i = suzukiD a l i i * x.toAdd i := by
  simp [natAct, coe_suzukiDElt, suzukiD, Matrix.mulVec_diagonal]

theorem suzukiD_three (l : Kˣ) :
    suzukiD a l 3 3 = ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K) := by
  simp [suzukiD]

@[expose] def InLine (x : Multiplicative (Fin 4 → K)) : Prop :=
  x.toAdd 0 = 0 ∧ x.toAdd 1 = 0 ∧ x.toAdd 2 = 0

theorem natFix_suzukiU_eq [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : Multiplicative (Fin 4 → K)) : x ∈ natFix a K (suzukiU a K) ↔ InLine x := by
  constructor
  · intro hx
    have h1 := congrArg Multiplicative.toAdd (hx _ (suzukiSElt_mem_suzukiU a K 1 0))
    rw [natAct_S_toAdd] at h1
    have e1 := congrFun h1 1
    simp at e1
    have e2 := congrFun h1 2
    simp [e1] at e2
    have e3 := congrFun h1 3
    simp [e1, e2] at e3
    exact ⟨e1, e2, e3⟩
  · rintro ⟨h0, h1, h2⟩ g hg
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hg
    apply Multiplicative.toAdd.injective
    rw [natAct_S_toAdd]
    ext i
    fin_cases i <;> simp [h0, h1, h2]

theorem natFix_suzukiU_card [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card ↥(natFix a K (suzukiU a K)) = 2 ^ (2 * a + 1) := by
  rw [← hK]
  refine Nat.card_congr
    { toFun := fun x => (x.1).toAdd 3
      invFun := fun c => ⟨Multiplicative.ofAdd (Pi.single 3 c),
        (natFix_suzukiU_eq hK _).2 ⟨by simp, by simp, by simp⟩⟩
      left_inv := fun x => ?_
      right_inv := fun c => by simp }
  obtain ⟨h0, h1, h2⟩ := (natFix_suzukiU_eq hK _).1 x.2
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [h0, h1, h2]

omit [Field K] in
theorem card_natModule [Finite K] :
    Nat.card (Multiplicative (Fin 4 → K)) = Nat.card K ^ 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → K) ≃ (Fin 4 → K))]
  simp [Nat.card_pi]

@[expose] def lineScal (a : ℕ) {K : Type} [Field K] (l : Kˣ) : K :=
  ((l ^ (-1 - (2 ^ a : ℤ)) : Kˣ) : K)

theorem natAct_SD_line (u v : K) (l : Kˣ) {x : Multiplicative (Fin 4 → K)} (hx : InLine x)
    (i : Fin 4) :
    (natAct (suzukiGroup a K) (suzukiSElt a K u v * suzukiDElt a K l) x).toAdd i =
      lineScal a l * x.toAdd i := by
  rw [natAct_mul_act]
  have hy0 : (natAct (suzukiGroup a K) (suzukiDElt a K l) x).toAdd 0 = 0 := by
    rw [natAct_D_toAdd, hx.1, mul_zero]
  have hy1 : (natAct (suzukiGroup a K) (suzukiDElt a K l) x).toAdd 1 = 0 := by
    rw [natAct_D_toAdd, hx.2.1, mul_zero]
  have hy2 : (natAct (suzukiGroup a K) (suzukiDElt a K l) x).toAdd 2 = 0 := by
    rw [natAct_D_toAdd, hx.2.2, mul_zero]
  have hy3 : (natAct (suzukiGroup a K) (suzukiDElt a K l) x).toAdd 3 =
      lineScal a l * x.toAdd 3 := by
    rw [natAct_D_toAdd, suzukiD_three]
    rfl
  rw [natAct_S_toAdd]
  fin_cases i
  · simp [hy0, hx.1]
  · simp [hy0, hy1, hx.2.1]
  · simp [hy0, hy1, hy2, hx.2.2]
  · simp [hy0, hy1, hy2, hy3]

theorem inLine_single (c : K) :
    InLine (Multiplicative.ofAdd (Pi.single 3 c) : Multiplicative (Fin 4 → K)) :=
  ⟨by simp, by simp, by simp⟩

theorem mem_suzukiB_of_normalizer [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {s : suzukiGroup a K}
    (hs : s ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K))) : s ∈ suzukiB a K := by
  have hpres : ∀ x, InLine x → InLine (natAct (suzukiGroup a K) s x) := by
    intro x hx
    rw [← natFix_suzukiU_eq hK] at hx ⊢
    intro g hg
    have hg' : s⁻¹ * g * s ∈ suzukiU a K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs) g).1 hg
      simpa using this
    calc natAct (suzukiGroup a K) g (natAct (suzukiGroup a K) s x)
        = natAct (suzukiGroup a K) (g * s) x := (natAct_mul_act _ _ _ _).symm
      _ = natAct (suzukiGroup a K) (s * (s⁻¹ * g * s)) x := by rw [mul_assoc, mul_inv_cancel_left]
      _ = natAct (suzukiGroup a K) s (natAct (suzukiGroup a K) (s⁻¹ * g * s) x) :=
          natAct_mul_act _ _ _ _
      _ = natAct (suzukiGroup a K) s x := by rw [hx _ hg']
  rcases (suzuki_bruhat_normal_form hK s).1 with ⟨u, v, l, h⟩ | ⟨u, v, l, c, d, h⟩
  · exact (mem_suzukiB_iff hK).2 ⟨u, v, l, h⟩
  · exfalso
    have h0 := (hpres _ (inLine_single (1 : K))).1
    have h1 := suzuki_bigCell_row_zero (a := a) u v c d l 3
    rw [← h] at h1
    have h2 : (natAct (suzukiGroup a K) s (Multiplicative.ofAdd (Pi.single 3 1))).toAdd 0 =
        (((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 0 3 := by
      simp [natAct]
    rw [h2, h1] at h0
    have h3 : suzukiS a c d 3 3 = 1 := rfl
    rw [h3, mul_one] at h0
    exact Units.ne_zero _ h0

theorem natAct_pow_line {s : suzukiGroup a K} (u v : K) (l : Kˣ)
    (hs : s = suzukiSElt a K u v * suzukiDElt a K l) (k : ℕ) {x : Multiplicative (Fin 4 → K)}
    (hx : InLine x) (i : Fin 4) :
    (natAct (suzukiGroup a K) (s ^ k) x).toAdd i = lineScal a l ^ k * x.toAdd i := by
  subst hs
  induction k generalizing i with
  | zero => simp [natAct_one]
  | succ k ih =>
    rw [pow_succ', natAct_mul_act]
    have hy : InLine (natAct (suzukiGroup a K) ((suzukiSElt a K u v * suzukiDElt a K l) ^ k) x) :=
      ⟨by rw [ih, hx.1, mul_zero], by rw [ih, hx.2.1, mul_zero], by rw [ih, hx.2.2, mul_zero]⟩
    rw [natAct_SD_line u v l hy, ih]
    ring

theorem eq_one_of_zpow_neg [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ}
    (h : l ^ (-1 - (2 ^ a : ℤ)) = 1) : l = 1 := by
  have hbij := (suzuki_frobenius_exponents a K hK).2.2.2.2.2.2.2.2.2.2.2.2
  have h1 : l ^ (1 + 2 ^ a : ℤ) = 1 := by
    have e : l ^ (-1 - (2 ^ a : ℤ)) = (l ^ (1 + 2 ^ a : ℤ))⁻¹ := by
      rw [← zpow_neg]
      congr 1
      ring
    rw [e, inv_eq_one] at h
    exact h
  exact hbij.1 (by simpa using h1)

theorem natFix_pow_fix [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : suzukiGroup a K}
    (hs : s ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)))
    (hord : orderOf s = 2 ^ (2 * a + 1) - 1) {k : ℕ} (hk : ¬ (2 ^ (2 * a + 1) - 1 ∣ k))
    {x : Multiplicative (Fin 4 → K)} (hx : InLine x)
    (hfix : natAct (suzukiGroup a K) (s ^ k) x = x) : x = 1 := by
  have hB := mem_suzukiB_of_normalizer hK hs
  obtain ⟨u, v, l, hsl⟩ := (mem_suzukiB_iff hK).1 hB
  by_contra hx1
  have hex : ∃ i, x.toAdd i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx1
    apply Multiplicative.toAdd.injective
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hc : lineScal a l ^ k = 1 := by
    have h1 := natAct_pow_line u v l hsl k hx i
    rw [hfix] at h1
    exact mul_right_cancel₀ hi (by rw [one_mul]; exact h1.symm)
  obtain ⟨u', v', l', hsk⟩ := (mem_suzukiB_iff hK).1 (pow_mem hB k)
  have e1 := natAct_pow_line u v l hsl k (inLine_single (1 : K)) 3
  have e2 : (natAct (suzukiGroup a K) (s ^ k) (Multiplicative.ofAdd (Pi.single 3 1))).toAdd 3 =
      lineScal a l' *
        (Multiplicative.ofAdd (Pi.single 3 (1 : K)) : Multiplicative (Fin 4 → K)).toAdd 3 := by
    rw [hsk]
    exact natAct_SD_line u' v' l' (inLine_single (1 : K)) 3
  rw [e1] at e2
  simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one] at e2
  have hl'1 : l' = 1 := by
    apply eq_one_of_zpow_neg hK
    apply Units.ext
    rw [Units.val_one]
    show lineScal a l' = 1
    rw [← e2, hc]
  have hmem : s ^ k ∈ suzukiU a K := by
    rw [hsk, hl'1, suzukiDElt_one, mul_one]
    exact suzukiSElt_mem_suzukiU a K u' v'
  have hU2 : Nat.card ↥(suzukiU a K) = (2 ^ (2 * a + 1)) ^ 2 := (suzuki_unipotent_structure hK).2.1
  have hd1 : orderOf (s ^ k) ∣ Nat.card ↥(suzukiU a K) := Subgroup.orderOf_dvd_natCard _ hmem
  have hd2 : orderOf (s ^ k) ∣ 2 ^ (2 * a + 1) - 1 := hord ▸ orderOf_pow_dvd k
  have hodd : Odd (2 ^ (2 * a + 1) - 1) := by
    have h2 : 0 < 2 ^ (2 * a + 1) := Nat.two_pow_pos _
    obtain ⟨r, hr⟩ : Even (2 ^ (2 * a + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ (2 * a + 1) - 1) (Nat.card ↥(suzukiU a K)) := by
    rw [hU2]
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right (2 * a + 1) (Odd.coprime_two_right hodd))
  have h1 : orderOf (s ^ k) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1
  rw [orderOf_eq_one_iff] at h1
  exact hk (hord ▸ orderOf_dvd_of_pow_eq_one h1)

@[expose] noncomputable def suzukiDHom (a : ℕ) (K : Type) [Field K] :
    Kˣ →* suzukiGroup a K where
  toFun := suzukiDElt a K
  map_one' := suzukiDElt_one
  map_mul' := fun l m => (suzukiDElt_mul l m).symm

theorem exists_suzukiD_order [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ l : Kˣ, orderOf (suzukiDElt a K l) = 2 ^ (2 * a + 1) - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, ?_⟩
  have h1 : orderOf (suzukiDHom a K g) = orderOf g :=
    orderOf_injective _ (fun l m h => (suzukiDElt_inj hK).1 h) g
  show orderOf (suzukiDHom a K g) = _
  rw [h1, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]

end NatSz

end CFSG.Quasithin.SzTorus
