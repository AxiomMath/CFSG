module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

variable {G : Type} [Group G]

open Equiv CFSG.Quasithin.F53Mod CFSG.Quasithin.F7
open scoped commutatorElement

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem natAct_alt_transitive : ∀ v w : Fin 4 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ CFSG.Quasithin.F53Mod.natAct σ v = w := by
  decide +kernel

theorem nat_irred_alt_aux (Y : Subgroup (Multiplicative (Fin 4 → ZMod 2)))
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y,
      Multiplicative.ofAdd (CFSG.Quasithin.F53Mod.natAct σ (Multiplicative.toAdd y)) ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall Y).mpr h)
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 1
  · rw [hw]; exact Y.one_mem
  have hy0 : Multiplicative.toAdd y ≠ 0 := fun h => hy1 (by simpa using h)
  have hw0 : Multiplicative.toAdd w ≠ 0 := fun h => hw (by simpa using h)
  obtain ⟨σ, hs, hσ⟩ := natAct_alt_transitive _ _ hy0 hw0
  have := hY σ (Equiv.Perm.mem_alternatingGroup.mpr hs) y hyY
  rw [hσ] at this
  simpa using this

theorem nat_irred_alt (Y : Subgroup nat.W)
    (hY : ∀ σ ∈ alternatingGroup (Fin 5), ∀ y ∈ Y, nat.act σ y ∈ Y) : Y = ⊥ ∨ Y = ⊤ :=
  nat_irred_alt_aux Y fun σ hσ y hy => hY σ hσ y hy

theorem mem_of_odd_two_step_pow {A J B : Subgroup G} {z : G} {m : ℕ} (hm : Odd m) (hzm : z ^ m = 1)
    (hJB : J ≤ B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) (hJ2 : ∀ x ∈ J, ∃ e : ℕ, x ^ (2 ^ e) ∈ A)
    (h1 : ∀ x ∈ J, z * x * z⁻¹ * x⁻¹ ∈ A) (h2 : ∀ x ∈ B, z * x * z⁻¹ * x⁻¹ ∈ J) :
    ∀ x ∈ B, z * x * z⁻¹ * x⁻¹ ∈ A := by
  intro x hx
  set c := z * x * z⁻¹ * x⁻¹ with hc
  have hcJ : c ∈ J := h2 x hx
  have hcB : c ∈ B := hJB hcJ
  have key : ∀ k : ℕ, (z ^ k * x * (z ^ k)⁻¹) * x⁻¹ * (c ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzc : z * c * z⁻¹ * c⁻¹ ∈ A := h1 c hcJ
      set a := (z ^ k * x * (z ^ k)⁻¹) * x⁻¹ * (c ^ k)⁻¹ with ha
      have hzk : z ^ k * x * (z ^ k)⁻¹ = a * c ^ k * x := by rw [ha]; group
      have hzk1 : z ^ (k + 1) * x * (z ^ (k + 1))⁻¹ = z * (a * c ^ k * x) * z⁻¹ := by
        rw [← hzk]; group
      rw [hzk1]
      have hza : z * a * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hzA a).mp ih
      have hzck : z * c ^ k * z⁻¹ = (z * c * z⁻¹) ^ k := by
        rw [← conj_pow]
      have hpow : ∀ j : ℕ, (z * c * z⁻¹) ^ j * (c ^ j)⁻¹ ∈ A := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hcA : c ^ j ∈ Subgroup.normalizer (A : Set G) :=
            Subgroup.pow_mem _ (hBA hcB) j
          have e : (z * c * z⁻¹) ^ (j + 1) * (c ^ (j + 1))⁻¹ =
              ((z * c * z⁻¹) ^ j * (c ^ j)⁻¹) *
                (c ^ j * ((z * c * z⁻¹ * c⁻¹)) * (c ^ j)⁻¹) := by
            rw [pow_succ, pow_succ]; group
          rw [e]
          exact A.mul_mem ihj ((Subgroup.mem_normalizer_iff.mp hcA _).mp hzc)
      have e2 : z * (a * c ^ k * x) * z⁻¹ * x⁻¹ * (c ^ (k + 1))⁻¹ =
          (z * a * z⁻¹) * ((z * c ^ k * z⁻¹) * (c ^ k)⁻¹) *
            (c ^ k * (z * x * z⁻¹ * x⁻¹ * c⁻¹) * (c ^ k)⁻¹) := by
        rw [pow_succ]; group
      rw [e2]
      have hcc : z * x * z⁻¹ * x⁻¹ * c⁻¹ = 1 := by rw [hc]; group
      rw [hcc, mul_one, mul_inv_cancel, mul_one, hzck]
      exact A.mul_mem hza (hpow k)
  have hm' := key m
  rw [hzm, one_mul, inv_one, mul_one, mul_inv_cancel, one_mul] at hm'
  have hcm : c ^ m ∈ A := by simpa using A.inv_mem hm'
  obtain ⟨e, he⟩ := hJ2 c hcJ
  have hcop : IsCoprime (m : ℤ) ((2 : ℤ) ^ e) := by
    have h2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by
      obtain ⟨r, hr⟩ := hm; omega)
    have := Nat.Coprime.pow_left e h2
    have h3 := Nat.isCoprime_iff_coprime.mpr this.symm
    simpa using h3
  obtain ⟨u, v, huv⟩ := hcop
  have e1 : c = (c ^ m) ^ u * (c ^ (2 ^ e)) ^ v := by
    have h1 : c ^ (u * m + v * 2 ^ e) = (c ^ m) ^ u * (c ^ (2 ^ e)) ^ v := by
      rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul]
      congr 2 <;> norm_cast
    rw [← h1, huv, zpow_one]
  rw [e1]
  exact A.mul_mem (A.zpow_mem hcm u) (A.zpow_mem he v)


theorem normalizer_commutator_of_le {H P Q : Subgroup G}
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh)]

theorem commutator_le_left_of_normalizes {Q L : Subgroup G}
    (h : L ≤ Subgroup.normalizer (Q : Set G)) : ⁅Q, L⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have := (Subgroup.mem_normalizer_iff.mp (h hl) q⁻¹).mp (Q.inv_mem hq)
  have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [e]; exact Q.mul_mem hq this

theorem commutator_oTwoRes_oTwoRes {X Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQX : Q ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅⁅Q, oTwoRes X⁆, oTwoRes X⁆ = ⁅Q, oTwoRes X⁆ := by
  set L := oTwoRes X with hL
  have hLX : L ≤ X := oTwoRes_le X
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_oTwoRes X
  set A : Subgroup G := ⁅Q, L⁆ with hA
  set B : Subgroup G := ⁅A, L⁆ with hB
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := normalizer_commutator_of_le hXQ hXL
  have hXB : X ≤ Subgroup.normalizer (B : Set G) := normalizer_commutator_of_le hXA hXL
  have hAQ : A ≤ Q := commutator_le_left_of_normalizes (hLX.trans hXQ)
  have hBA : B ≤ A := commutator_le_left_of_normalizes (hLX.trans hXA)
  refine le_antisymm hBA ?_
  let S : Subgroup G :=
    { carrier := {l | l ∈ X ∧ ∀ q ∈ Q, l * q * l⁻¹ * q⁻¹ ∈ B}
      one_mem' := ⟨X.one_mem, fun q _ => by simp [B.one_mem]⟩
      mul_mem' := by
        rintro l1 l2 ⟨hl1, h1⟩ ⟨hl2, h2⟩
        refine ⟨X.mul_mem hl1 hl2, fun q hq => ?_⟩
        have e : l1 * l2 * q * (l1 * l2)⁻¹ * q⁻¹ =
            (l1 * (l2 * q * l2⁻¹ * q⁻¹) * l1⁻¹) * (l1 * q * l1⁻¹ * q⁻¹) := by group
        rw [e]
        exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXB hl1) _).mp (h2 q hq)) (h1 q hq)
      inv_mem' := by
        rintro l ⟨hl, h1⟩
        refine ⟨X.inv_mem hl, fun q hq => ?_⟩
        have hq' : l⁻¹ * q * l ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (hXQ (X.inv_mem hl)) q).mp hq
          simpa using this
        have := B.inv_mem (h1 _ hq')
        have e : (l * (l⁻¹ * q * l) * l⁻¹ * (l⁻¹ * q * l)⁻¹)⁻¹ = l⁻¹ * q * (l⁻¹)⁻¹ * q⁻¹ := by group
        rw [e] at this
        exact this }
  have hLS : L ≤ S := by
    rw [hL, oTwoRes, Subgroup.closure_le]
    rintro z ⟨hzX, m, hm, hzm⟩
    have hzL : z ∈ L := Subgroup.subset_closure ⟨hzX, m, hm, hzm⟩
    refine ⟨hzX, ?_⟩
    have := mem_of_odd_two_step_pow (A := B) (J := A) (B := Q) (z := z) hm hzm hAQ
      (hQX.trans hXB) (hXB hzX)
      (fun x hx => by
        obtain ⟨k, hk⟩ := hQ ⟨x, hAQ hx⟩
        refine ⟨k, ?_⟩
        have h := congrArg Subtype.val hk
        simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
        rw [h]; exact B.one_mem)
      (fun x hx => by
        have h := Subgroup.commutator_mem_commutator hzL hx
        rw [Subgroup.commutator_comm] at h
        simpa [commutatorElement_def] using h)
      (fun x hx => by
        have h := Subgroup.commutator_mem_commutator hzL hx
        rw [Subgroup.commutator_comm] at h
        simpa [commutatorElement_def] using h)
    exact this
  rw [hA, Subgroup.commutator_le]
  intro q hq l hl
  have := (hLS hl).2 q hq
  have e : ⁅q, l⁆ = (l * q * l⁻¹ * q⁻¹)⁻¹ := by simp [commutatorElement_def]; group
  rw [e]; exact B.inv_mem this

end CFSG.Quasithin.Kleidman.F53Hss36
