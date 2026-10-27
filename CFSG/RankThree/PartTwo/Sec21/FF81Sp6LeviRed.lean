module

public import Certificates.Certificate899102
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit

section Cert


private theorem aElt_three : aElt 3 = zH 0 * zH 1 := by
  change zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 0 = _
  rw [pow_one, pow_one, pow_zero, mul_one]

private theorem vecElt_one_one_one : vecElt zH ![1, 1, 1] = zH 0 * zH 1 * zH 2 := by
  change zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 1 = _
  rw [pow_one, pow_one, pow_one]

private theorem card_cen_conj (g x : H6) :
    Nat.card (Subgroup.centralizer {g * x * g⁻¹}) = Nat.card (Subgroup.centralizer {x}) := by
  have e : Subgroup.centralizer {g * x * g⁻¹} =
      (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
    constructor
    · intro h
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
        _ = x * (g⁻¹ * y * g) := by group
    · intro h
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
        _ = g * x * g⁻¹ * y := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem centralizer_one : Subgroup.centralizer ({1} : Set H6) = ⊤ := by
  ext x
  simp [Subgroup.mem_centralizer_iff]

private theorem card_cen_conj_inv (g x : H6) :
    Nat.card (Subgroup.centralizer {g⁻¹ * x * g}) = Nat.card (Subgroup.centralizer {x}) := by
  simpa only [inv_inv] using card_cen_conj g⁻¹ x

private theorem wreathW_le_cen :
    wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ≤ Subgroup.centralizer {vecElt zH ![1, 1, 1]} := by
  have hz : ∀ i, zH i ∈ Subgroup.centralizer {vecElt zH ![1, 1, 1]} := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := vecElt_add wreathFacts_zH (Pi.single i 1) ![1, 1, 1]
    rw [add_comm, vecElt_add wreathFacts_zH, vecElt_single_one] at h
    exact h.symm
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact (Subgroup.zpowers_le).mpr (hz 0)
  · exact (Subgroup.zpowers_le).mpr (hz 1)
  · exact (Subgroup.zpowers_le).mpr (hz 2)
  · refine (Subgroup.zpowers_le).mpr ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := conj_vecElt wreathFacts_zH ![1, 1, 1]
    have e : (![(![1, 1, 1] : Fin 3 → ZMod 3) 2, (![1, 1, 1] : Fin 3 → ZMod 3) 0,
        (![1, 1, 1] : Fin 3 → ZMod 3) 1] : Fin 3 → ZMod 3) = ![1, 1, 1] := by
      ext i; fin_cases i <;> rfl
    rw [e] at h
    calc CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * vecElt zH ![1, 1, 1] = CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * vecElt zH ![1, 1, 1] * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH⁻¹ * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := by group
      _ = vecElt zH ![1, 1, 1] * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := by rw [h]

private theorem single_of_card {y : H6} (hy : y ∈ baseA zH)
    (hc : Nat.card (Subgroup.centralizer {y}) = 2160) :
    ∃ (p : Fin 3) (k : ℕ), (k = 1 ∨ k = 2) ∧ y = zH p ^ k := by
  obtain ⟨v, rfl⟩ := (mem_baseA_iff wreathFacts_zH).mp hy
  have hv : vecElt zH v = zH 0 ^ (v 0).val * zH 1 ^ (v 1).val * zH 2 ^ (v 2).val := rfl
  have hval : ∀ i, (v i).val < 3 := fun i => ZMod.val_lt _
  set a := (v 0).val
  set b := (v 1).val
  set c := (v 2).val
  have h2 : ([a, b, c].filter (· != 0)).length ≠ 2 := by
    intro h2
    obtain ⟨g, hg⟩ :=
      Certificates.certificate899102.2.2.2.1 a (hval 0) b (hval 1) c (hval 2) h2
    rw [hv, hg, card_cen_conj, ← aElt_three, ← centSub_eq, card_centSub] at hc
    exact absurd hc (by decide)
  have h3 : ([a, b, c].filter (· != 0)).length ≠ 3 := by
    intro h3
    obtain ⟨g, hg⟩ :=
      Certificates.certificate899102.2.2.2.2 a (hval 0) b (hval 1) c (hval 2) h3
    rw [hv, hg, card_cen_conj, ← vecElt_one_one_one] at hc
    have hdvd := Subgroup.card_dvd_of_le wreathW_le_cen
    rw [card_wreathW_zH, hc] at hdvd
    exact absurd hdvd (by decide)
  rw [hv] at hc ⊢
  have h0 : ([a, b, c].filter (· != 0)).length ≠ 0 := by
    intro h0
    have ha : a = 0 ∧ b = 0 ∧ c = 0 := by
      simp only [List.filter_cons, List.filter_nil] at h0
      split_ifs at h0 with h1 h2 h3 <;> simp_all
    obtain ⟨ha, hb, hc'⟩ := ha
    rw [ha, hb, hc', pow_zero, pow_zero, pow_zero, one_mul, one_mul,
      centralizer_one, Subgroup.card_top, card_H6] at hc
    exact absurd hc (by decide)
  have key : ∀ a' < 3, ∀ b' < 3, ∀ c' < 3, ([a', b', c'].filter (· != 0)).length ≠ 0 →
      ([a', b', c'].filter (· != 0)).length ≠ 2 → ([a', b', c'].filter (· != 0)).length ≠ 3 →
      (b' = 0 ∧ c' = 0 ∧ (a' = 1 ∨ a' = 2)) ∨ (a' = 0 ∧ c' = 0 ∧ (b' = 1 ∨ b' = 2)) ∨
        (a' = 0 ∧ b' = 0 ∧ (c' = 1 ∨ c' = 2)) := by
    intro a' ha' b' hb' c' hc'
    interval_cases a' <;> interval_cases b' <;> interval_cases c' <;> decide
  rcases key a (hval 0) b (hval 1) c (hval 2) h0 h2 h3 with ⟨hb, hc', ha⟩ | ⟨ha, hc', hb⟩ |
    ⟨ha, hb, hc'⟩
  · exact ⟨0, a, ha, by rw [hb, hc', pow_zero, pow_zero, mul_one, mul_one]⟩
  · exact ⟨1, b, hb, by rw [ha, hc', pow_zero, pow_zero, one_mul, mul_one]⟩
  · exact ⟨2, c, hc', by rw [ha, hb, pow_zero, pow_zero, one_mul, one_mul]⟩

theorem exists_single_of_card {y : H6} (hy : y ∈ baseA zH)
    (hc : Nat.card (Subgroup.centralizer {y}) = 2160) :
    ∃ (p : Fin 3) (a : ZMod 3), a ≠ 0 ∧ y = zH p ^ a.val := by
  obtain ⟨p, k, hk, rfl⟩ := single_of_card hy hc
  rcases hk with rfl | rfl
  · exact ⟨p, 1, one_ne_zero, by rw [ZMod.val_one]⟩
  · exact ⟨p, 2, by decide, by rw [show (2 : ZMod 3).val = 2 from rfl]⟩

private theorem card_closure_le_nine {p q : Fin 3} {S : Set H6}
    (hS : ∀ x ∈ S, x ∈ Subgroup.zpowers (zH p) ⊔ Subgroup.zpowers (zH q)) :
    Nat.card (Subgroup.closure S) ≤ 9 := by
  have hle : Subgroup.closure S ≤ Subgroup.zpowers (zH p) ⊔ Subgroup.zpowers (zH q) :=
    (Subgroup.closure_le _).mpr hS
  refine (Subgroup.card_le_of_le hle).trans ?_
  by_cases hpq : p = q
  · subst hpq
    rw [sup_idem, Nat.card_zpowers, orderOf_z wreathFacts_zH]
    norm_num
  · exact ((isElemAbelian_sup_zpowers wreathFacts_zH hpq).2).le

private theorem pow_mem_zpowers (p : Fin 3) (n : ℕ) : zH p ^ n ∈ Subgroup.zpowers (zH p) :=
  pow_mem (Subgroup.mem_zpowers _) _

theorem exists_conj_torus {c₁ c₂ c₃ : H6}
    (hBe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c₁, c₂, c₃} : Set H6)))
    (hBc : Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27)
    (h₁ : Nat.card (Subgroup.centralizer {c₁}) = 2160)
    (h₂ : Nat.card (Subgroup.centralizer {c₂}) = 2160)
    (h₃ : Nat.card (Subgroup.centralizer {c₃}) = 2160) :
    ∃ (g : H6) (p₁ p₂ p₃ : Fin 3) (a₁ a₂ a₃ : ZMod 3), p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      a₃ ≠ 0 ∧ g * zH p₁ ^ a₁.val * g⁻¹ = c₁ ∧ g * zH p₂ ^ a₂.val * g⁻¹ = c₂ ∧
      g * zH p₃ ^ a₃.val * g⁻¹ = c₃ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := Subgroup.closure ({c₁, c₂, c₃} : Set H6) with hBdef
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by rw [hBc]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hBp
  have hPg : B.map (MulAut.conj g⁻¹).toMonoidHom = baseA zH :=
    eq_baseA_of_le_wreathW wreathFacts_zH card_wreathW_zH
      (CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.map_conj_inv_le hg)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B hBe)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBc])
  have hcl : Subgroup.closure ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6) =
      baseA zH := by
    rw [← hPg, hBdef, MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  have hmem : ∀ x ∈ ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6), x ∈ baseA zH :=
    fun x hx => hcl ▸ Subgroup.subset_closure hx
  obtain ⟨p₁, a₁, ha₁, e₁⟩ := exists_single_of_card
    (hmem (g⁻¹ * c₁ * g) (by simp))
    (by rw [card_cen_conj_inv]; exact h₁)
  obtain ⟨p₂, a₂, ha₂, e₂⟩ := exists_single_of_card
    (hmem (g⁻¹ * c₂ * g) (by simp))
    (by rw [card_cen_conj_inv]; exact h₂)
  obtain ⟨p₃, a₃, ha₃, e₃⟩ := exists_single_of_card
    (hmem (g⁻¹ * c₃ * g) (by simp))
    (by rw [card_cen_conj_inv]; exact h₃)
  have hcard : Nat.card (Subgroup.closure
      ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6)) = 27 := by
    rw [hcl, card_baseA wreathFacts_zH]
  have hsets : ∀ x ∈ ({g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g} : Set H6),
      x = zH p₁ ^ a₁.val ∨ x = zH p₂ ^ a₂.val ∨ x = zH p₃ ^ a₃.val := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl e₁
    · exact Or.inr (Or.inl e₂)
    · exact Or.inr (Or.inr e₃)
  refine ⟨g, p₁, p₂, p₃, a₁, a₂, a₃, ?_, ?_, ha₁, ha₂, ha₃, ?_, ?_, ?_⟩
  · intro h
    subst h
    have := card_closure_le_nine (p := p₁) (q := p₃)
      (S := {g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g}) (fun x hx => by
        rcases hsets x hx with rfl | rfl | rfl
        · exact Subgroup.mem_sup_left (pow_mem_zpowers _ _)
        · exact Subgroup.mem_sup_left (pow_mem_zpowers _ _)
        · exact Subgroup.mem_sup_right (pow_mem_zpowers _ _))
    omega
  · intro h
    subst h
    have := card_closure_le_nine (p := p₂) (q := p₁)
      (S := {g⁻¹ * c₁ * g, g⁻¹ * c₂ * g, g⁻¹ * c₃ * g}) (fun x hx => by
        rcases hsets x hx with rfl | rfl | rfl
        · exact Subgroup.mem_sup_right (pow_mem_zpowers _ _)
        · exact Subgroup.mem_sup_left (pow_mem_zpowers _ _)
        · exact Subgroup.mem_sup_left (pow_mem_zpowers _ _))
    omega
  · rw [← e₁]; group
  · rw [← e₂]; group
  · rw [← e₃]; group

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi
