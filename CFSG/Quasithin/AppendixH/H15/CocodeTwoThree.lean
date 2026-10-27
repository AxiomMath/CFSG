module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiRange
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOrth

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem rk_comap_eq_of_injective_le_range {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (I : Subgroup H) (hI : I ≤ f.range) :
    rk ↥I = rk ↥(I.comap f : Subgroup G) := by
  have hmap : (I.comap f).map f = I := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hI]
  have hcard : Nat.card ↥I = Nat.card ↥(I.comap f : Subgroup G) := by
    have h := Subgroup.card_map_of_injective (K := I.comap f) hf
    rwa [hmap] at h
  unfold rk
  rw [hcard]

theorem three_main (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    ∀ I : Subgroup V, I ≤ fixV (rImg ρ (octFix O)) → (∀ x ∈ I, ¬ IsO2Vec d a b Γ β x) →
      rk ↥I ≤ (if d = 24 then 3 else 4) := by
  intro I hIle havoid
  obtain ⟨P⟩ := exists_phiData hM
  have hIrange : I ≤ P.φ.range := by rw [P.range_eq_fixV hM]; exact hIle
  by_cases hd22 : d = 22
  ·
    have hv0notI : P.φ (Multiplicative.ofAdd (evPair 0 2)) ∉ I := fun hmem =>
      havoid _ hmem
        (P.isO2Vec hM (p := 0) (q := 2) (by decide) (Or.inr (Or.inr ⟨hd22, rfl, by decide⟩)))
    have hv0range : P.φ (Multiplicative.ofAdd (evPair 0 2)) ∈ P.φ.range := ⟨_, rfl⟩
    have hne : I ≠ P.φ.range := by
      intro heq
      exact hv0notI (by rw [heq]; exact hv0range)
    have hlt : I < P.φ.range := lt_of_le_of_ne hIrange hne
    obtain ⟨D, c, hD, hn, hdU, hActs⟩ := exists_kFrame hM
    haveI : Finite V := c.finite
    haveI : Finite ↥(P.φ.range) := Subtype.finite
    have hcardlt : Nat.card ↥I < Nat.card ↥(P.φ.range) := Subgroup.card_lt_of_lt hlt
    have hcardI : Nat.card ↥I = 2 ^ rk ↥I := card_eq_two_pow c.sq_eq_one I
    have hcardR : Nat.card ↥(P.φ.range) = 2 ^ 5 := by
      rw [P.range_eq_fixV hM, kLayer_card_fixV hM, if_pos hd22]
    have hpow : 2 ^ rk ↥I < 2 ^ 5 := by
      rw [← hcardI, ← hcardR]
      exact hcardlt
    have hrk : rk ↥I < 5 := (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow
    rw [if_neg (by omega : d ≠ 24)]
    omega
  ·
    let J : Subgroup (Multiplicative (Fin 6 → ZMod 2)) := I.comap P.φ
    have hinj : Function.Injective P.φ :=
      (MonoidHom.ker_eq_bot_iff P.φ).mp (P.ker_ne22 hM hd22)
    have hrk : rk ↥I = rk ↥J := rk_comap_eq_of_injective_le_range P.φ hinj I hIrange
    rcases mctx_cases hM with ⟨h24, _⟩ | ⟨h23, _⟩ | ⟨h22, _⟩
    · have hJavoid : ∀ x ∈ J, ∀ p q : Fin 8, p ≠ q →
          x ≠ Multiplicative.ofAdd (evPair p q) := by
        intro x hx p q hpq hxeq
        have hxI : P.φ x ∈ I := hx
        exact havoid (P.φ x) hxI (by rw [hxeq]; exact P.isO2Vec hM hpq (Or.inl h24))
      have hle : rk ↥J ≤ 3 := rk_le_three_of_avoid hJavoid
      rw [hrk, if_pos h24]
      exact hle
    · have hJavoid : ∀ x ∈ J, ∀ q : Fin 8, q ≠ 0 →
          x ≠ Multiplicative.ofAdd (evPair 0 q) := by
        intro x hx q hq hxeq
        have hxI : P.φ x ∈ I := hx
        exact havoid (P.φ x) hxI
          (by rw [hxeq]
              exact P.isO2Vec hM (p := 0) (q := q) (Ne.symm hq)
                (Or.inr (Or.inl ⟨h23, rfl⟩)))
      have hle : rk ↥J ≤ 4 := rk_le_four_of_avoid_zero hJavoid
      rw [hrk, if_neg (by omega : d ≠ 24)]
      exact hle
    · exact absurd h22 hd22

end CFSG.ASVolI.AppH

