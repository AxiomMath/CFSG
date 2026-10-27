module

public import CFSG.Quasithin.Background.C124YLH6LiftA5
public import CFSG.Quasithin.Background.C124YLH6Ov
public import CFSG.Sporadic.Schreier.J4SSylowBase

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.H6

open Equiv Subgroup CFSG.Quasithin CFSG.Quasithin.C124.YL.A6

theorem exists_hat_hom {Γ : Type} [Group Γ] (h : IsHat Γ ↥(alternatingGroup (Fin 6))) :
    ∃ q : Γ →* P6, q.range = alternatingGroup (Fin 6) ∧ q.ker = Subgroup.center Γ := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  refine ⟨(alternatingGroup (Fin 6)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Γ))), ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ e.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  · ext x
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]

theorem card_ker_hat {Γ : Type} [Group Γ] [Finite Γ] (h : IsHat Γ ↥(alternatingGroup (Fin 6)))
    {q : Γ →* P6} (hker : q.ker = Subgroup.center Γ) : Nat.card q.ker = 3 := by
  rw [hker]
  exact h.2.1

theorem card_hat {Γ : Type*} [Group Γ] [Finite Γ] {q : Γ →* P6}
    (hq : q.range = alternatingGroup (Fin 6)) (hker3 : Nat.card q.ker = 3) :
    Nat.card Γ = 1080 := by
  have h := Subgroup.card_ker_mul_card_range q
  rw [hq, hker3] at h
  have h2 : Nat.card (alternatingGroup (Fin 6)) = 360 := card_Gam
  rw [h2] at h
  omega

theorem card_map_of_elem {Γ : Type*} [Group Γ] [Finite Γ] {q : Γ →* P6}
    (hker3 : Nat.card q.ker = 3) {B : Subgroup Γ} (hsq : ∀ a ∈ B, a * a = 1) :
    Nat.card (B.map q) = Nat.card B := by
  have hinj : Function.Injective (q.comp B.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (a : Γ) ∈ q.ker := ha
    exact Subgroup.mem_bot.2 (Subtype.ext (eq_one_of_ker_sq hker3 h1 (hsq a a.2)))
  have h : (q.comp B.subtype).range = B.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem Pg_not_comm : ¬ ∀ a ∈ Pg, ∀ b ∈ Pg, a * b = b * a := by
  intro h
  have h1 : (swap 4 5 * swap 2 3 : P6) ∈ Pg := nu_mem_Pg
  have h2 : (swap 3 4 * swap 0 1 : P6) ∈ Pg := memP_iff.1 (by decide +kernel :
    memP (swap 3 4 * swap 0 1) plist = true)
  have := h _ h1 _ h2
  revert this
  decide +kernel

theorem card_le_four_of_elem {Γ : Type*} [Group Γ] [Finite Γ] {q : Γ →* P6}
    (hq : q.range = alternatingGroup (Fin 6)) (hker3 : Nat.card q.ker = 3) {B : Subgroup Γ}
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hsq : ∀ a ∈ B, a * a = 1) :
    Nat.card B ≤ 4 := by
  have hB2 : IsPGroup 2 B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa [pow_two] using hsq x x.2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hB2
  have hdvd : Nat.card B ∣ 1080 := by
    rw [← card_hat hq hker3]
    exact Subgroup.card_subgroup_dvd_card B
  rw [hn] at hdvd
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    omega
  by_contra hgt
  have hB8 : Nat.card B = 8 := by
    rw [hn]
    interval_cases n <;> simp_all
  have hKbA : B.map q ≤ alternatingGroup (Fin 6) := hq ▸ Subgroup.map_le_range q B
  have hKb8 : Nat.card (B.map q) = 8 := by rw [card_map_of_elem hker3 hsq, hB8]
  have hKb2 : IsPGroup 2 (B.map q) := IsPGroup.of_card (n := 3) (by rw [hKb8]; norm_num)
  obtain ⟨c, -, hcle⟩ := exists_conj_le_of_isSylowTwoOf isSylowTwoOf_Pg hKbA hKb2
  have hPg : cjSub c (B.map q) = Pg := by
    refine Subgroup.eq_of_le_of_card_ge hcle ?_
    rw [card_cjSub, hKb8, card_Pg]
  apply Pg_not_comm
  intro a ha b hb
  rw [← hPg] at ha hb
  have ha' := mem_cjSub.1 ha
  have hb' := mem_cjSub.1 hb
  obtain ⟨x, hx, hxa⟩ := ha'
  obtain ⟨y, hy, hyb⟩ := hb'
  have hxy := hcomm x hx y hy
  have : c⁻¹ * (a * b) * c = c⁻¹ * (b * a) * c := by
    calc c⁻¹ * (a * b) * c = (c⁻¹ * a * c) * (c⁻¹ * b * c) := by group
      _ = q x * q y := by rw [← hxa, ← hyb]
      _ = q (x * y) := (map_mul q x y).symm
      _ = q (y * x) := by rw [hxy]
      _ = q y * q x := map_mul q y x
      _ = (c⁻¹ * b * c) * (c⁻¹ * a * c) := by rw [← hxa, ← hyb]
      _ = c⁻¹ * (b * a) * c := by group
  simpa using this

end CFSG.Quasithin.C124.YL.H6
