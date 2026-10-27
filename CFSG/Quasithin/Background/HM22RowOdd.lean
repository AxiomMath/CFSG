module

public import CFSG.Quasithin.Background.HM22RowOddData
public import CFSG.Quasithin.Background.HM22RowAbs
public import CFSG.Quasithin.Background.H12OneHatM22PfModel

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert Matrix

section Sub

variable {gW gens : List (List ℕ)} {D : List (List ℕ × List ℕ)}

theorem subCheck_spec (h : subCheck gW gens D = true) :
    gW.map tW = gens ∧ (∀ p ∈ D, evalW 12 gens p.2 = p.1) ∧
      (∀ x ∈ D.map Prod.fst, ∀ g ∈ gens, mulN g x ∈ D.map Prod.fst) ∧
      oneN 12 ∈ D.map Prod.fst ∧ (∀ g ∈ gens, ValidN 12 g) ∧ (D.map Prod.fst).Nodup ∧
      ∀ x ∈ D.map Prod.fst, x = one12 ∨ fixOK x oddMask = true := by
  simp only [subCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.contains_iff_mem,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, fun g hg => validB_iff.mp (h5 g hg), h6, h7⟩

theorem unit_of_subCheck (h : subCheck gW gens D = true) :
    ∀ g ∈ gens, ∃ u ∈ G, (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) = decN 12 g := by
  intro g hg
  rw [← (subCheck_spec h).1] at hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨tU w, tU_mem w, tU_val w⟩

theorem mem_iff_of_subCheck (h : subCheck gW gens D = true) (u : GL (Fin 12) (ZMod 2)) :
    u ∈ genSubN 12 gens ↔ colsN (u : Matrix (Fin 12) (Fin 12) (ZMod 2)) ∈ D.map Prod.fst := by
  obtain ⟨-, h2, h3, h4, h5, -, -⟩ := subCheck_spec h
  refine mem_genSubN_iff gens _ h5 (fun g hg => ?_) (fun x hx => ?_) h4 h3 u
  · obtain ⟨u, -, hu⟩ := unit_of_subCheck h g hg
    exact ⟨u, hu⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact ⟨p.2, (h2 p hp).symm⟩

theorem card_of_subCheck (h : subCheck gW gens D = true) :
    Nat.card (genSubN 12 gens) = D.length := by
  obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := subCheck_spec h
  rw [card_genSubN gens (D.map Prod.fst) h5 (fun g hg => ?_) (fun x hx => ?_) (fun x hx => ?_) h4
    h3 h6, List.length_map]
  · obtain ⟨u, -, hu⟩ := unit_of_subCheck h g hg
    exact ⟨u, hu⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact ⟨p.2, (h2 p hp).symm⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    rw [← h2 p hp]
    exact validN_evalW gens h5 _

theorem le_G_of_subCheck (h : subCheck gW gens D = true) : genSubN 12 gens ≤ G := by
  rw [genSubN, Subgroup.closure_le]
  intro u hu
  obtain ⟨v, hv, hvu⟩ := unit_of_subCheck h _ hu
  have : u = v := by
    apply eq_of_colsN_eq
    rw [hvu, colsN_decN ((subCheck_spec h).2.2.2.2.1 _ hu)]
  rw [this]
  exact hv

theorem card_fix_le_of_subCheck (h : subCheck gW gens D = true) (hm : maskCard oddMask ≤ 16)
    {u : GL (Fin 12) (ZMod 2)} (hu : u ∈ genSubN 12 gens) (hu1 : u ≠ 1) :
    Nat.card {v : Fin 12 → ZMod 2 //
      ((u : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v} ≤ 16 := by
  rcases (subCheck_spec h).2.2.2.2.2.2 _ ((mem_iff_of_subCheck h u).mp hu) with h1 | h1
  · exfalso
    apply hu1
    apply eq_of_colsN_eq
    rw [h1, Units.val_one, colsN_one]
  · have h2 := card_fix_le (validN_colsN _) h1
    rw [decN_colsN] at h2
    exact h2.trans hm

end Sub

theorem oddCheck_parts : subCheck p3W p3G p3D = true ∧ subCheck p5W p5G p5D = true ∧
    subCheck p7W p7G p7D = true ∧ subCheck p11W p11G p11D = true ∧ maskCard oddMask ≤ 16 := by
  have h := oddCheck_eq
  simp only [oddCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem card_fix_le_of_conj {gW gens : List (List ℕ)} {D : List (List ℕ × List ℕ)}
    (h : subCheck gW gens D = true) {p k : ℕ} [Fact p.Prime]
    (hD : D.length = p ^ k) (hk : ¬ p ^ (k + 1) ∣ 1330560) {g : GL (Fin 12) (ZMod 2)}
    (hg : g ∈ G) (hgp : orderOf g = p) :
    Nat.card {v : Fin 12 → ZMod 2 //
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v} ≤ 16 := by
  have hle := le_G_of_subCheck h
  have hP : Nat.card ↥((genSubN 12 gens).subgroupOf G) = p ^ k := by
    rw [← hD, ← card_of_subCheck h]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hE : IsPGroup p ↥(Subgroup.zpowers (⟨g, hg⟩ : ↥G)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, hgp]
  obtain ⟨c, hc⟩ := exists_conj_le hP (by rwa [card_G]) hE
  have h1 := hc _ (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (((c⁻¹ * ⟨g, hg⟩ * c : ↥G) : GL (Fin 12) (ZMod 2))) =
      (c : GL (Fin 12) (ZMod 2))⁻¹ * g * c := rfl
  rw [h2] at h1
  have hne : (c : GL (Fin 12) (ZMod 2))⁻¹ * g * c ≠ 1 := by
    intro h3
    have h4 : g = 1 := by
      calc g = (c : GL (Fin 12) (ZMod 2)) * ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) *
            (c : GL (Fin 12) (ZMod 2))⁻¹ := by group
        _ = 1 := by rw [h3, mul_one, mul_inv_cancel]
    rw [h4, orderOf_one] at hgp
    exact (Fact.out : p.Prime).one_lt.ne hgp
  rw [← card_fix_conj (c : GL (Fin 12) (ZMod 2)) g]
  exact card_fix_le_of_subCheck h oddCheck_parts.2.2.2.2 h1 hne

theorem card_fix_le_of_orderOf {g : GL (Fin 12) (ZMod 2)}
    (hg : g ∈ G) {p : ℕ} (hgp : orderOf g = p) (hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11) :
    Nat.card {v : Fin 12 → ZMod 2 //
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v = v} ≤ 16 := by
  rcases hp with rfl | rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact card_fix_le_of_conj (k := 3) oddCheck_parts.1 (by decide) (by norm_num) hg hgp
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact card_fix_le_of_conj (k := 1) oddCheck_parts.2.1 (by decide) (by norm_num) hg hgp
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact card_fix_le_of_conj (k := 1) oddCheck_parts.2.2.1 (by decide) (by norm_num) hg hgp
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact card_fix_le_of_conj (k := 1) oddCheck_parts.2.2.2.1 (by decide) (by norm_num) hg hgp

end CFSG.Quasithin.H.Mathieu.M22Row
