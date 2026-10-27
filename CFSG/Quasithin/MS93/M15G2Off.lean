module

public import CFSG.Quasithin.MS93.M15G2
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)

section Basic

variable {F : Type} [Field F]

theorem zmk_R (c : F) : zmk c 0 0 0 0 0 0 c = ((c, 0, 0, c) : quasithinZorn F) :=
  Prod.ext rfl (Prod.ext (funext fun i => by fin_cases i <;> rfl)
    (Prod.ext (funext fun i => by fin_cases i <;> rfl) rfl))

theorem cgE_R (g : ↥(cayleyGroup F)) (c : F) :
    cgE g (zmk c 0 0 0 0 0 0 c) = zmk c 0 0 0 0 0 0 c := by
  have h : zmk c 0 0 0 0 0 0 c = c • cayleyOne F := by
    rw [cayleyOne_eq, zmk_smul]
    apply zmk_congr <;> ring
  rw [h, map_smul, cg_one]

theorem comm_eq_zero_of_mem_R (γ : ↥(cayleyGroup F)) {x : quasithinZorn F}
    (hx : cayleyTr x = 0) {c : F} (h : cgE γ x - x = zmk c 0 0 0 0 0 0 c) : c = 0 := by
  have h1 : cgE γ x = x + zmk c 0 0 0 0 0 0 c := by rw [← h]; abel
  have hn := cg_norm γ x
  rw [h1, zorn_eta x, zmk_add, cayleyNorm_zmk, cayleyNorm_zmk] at hn
  rw [zorn_eta x, cayleyTr_zmk] at hx
  have h2 : c * c = 0 := by linear_combination hn - c * hx
  exact mul_self_eq_zero.mp h2

theorem cgE_conj_comm (g γ : ↥(cayleyGroup F)) (y : quasithinZorn F) :
    cgE (g * γ * g⁻¹) y - y = cgE g (cgE γ (cgE g⁻¹ y) - cgE g⁻¹ y) := by
  have h1 : cgE g (cgE g⁻¹ y) = y := by
    rw [← cg_mul_apply, mul_inv_cancel]
    rfl
  rw [map_sub, h1]
  rfl

@[expose] def o0Comm (Γ : Subgroup ↥(cayleyGroup F)) : Set (quasithinZorn F) :=
  {t | ∃ γ ∈ Γ, ∃ x : quasithinZorn F, cayleyTr x = 0 ∧ cgE γ x - x = t}

@[expose] def tA1 (F : Type) [Field F] : AddSubgroup (quasithinZorn F) where
  carrier := {t | ∃ ρ τ σ₁ σ₂ : F, t = zmk ρ τ 0 0 0 σ₁ σ₂ ρ}
  add_mem' := by
    rintro _ _ ⟨a, b, c, d, rfl⟩ ⟨a', b', c', d', rfl⟩
    exact ⟨a + a', b + b', c + c', d + d', by rw [zmk_add]; simp⟩
  zero_mem' := ⟨0, 0, 0, 0, by rw [zmk_zero]⟩
  neg_mem' := by
    rintro _ ⟨a, b, c, d, rfl⟩
    refine ⟨-a, -b, -c, -d, ?_⟩
    rw [← zero_sub, ← zmk_zero, zmk_sub']
    simp

theorem mem_o0Comm_conj_iff (g : ↥(cayleyGroup F)) {Γ : Subgroup ↥(cayleyGroup F)}
    {t : quasithinZorn F} :
    t ∈ o0Comm (Γ.map (MulAut.conj g).toMonoidHom) ↔ ∃ s ∈ o0Comm Γ, t = cgE g s := by
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, y, hy, rfl⟩
    exact ⟨cgE γ (cgE g⁻¹ y) - cgE g⁻¹ y, ⟨γ, hγ, cgE g⁻¹ y, (cg_tr _ _).trans hy, rfl⟩,
      cgE_conj_comm g γ y⟩
  · rintro ⟨_, ⟨γ, hγ, x, hx, rfl⟩, rfl⟩
    refine ⟨g * γ * g⁻¹, ⟨γ, hγ, rfl⟩, cgE g x, (cg_tr _ _).trans hx, ?_⟩
    rw [cgE_conj_comm, cg_inv_apply]

end Basic

section Char2

variable {F : Type} [Field F] [CharP F 2]

theorem cayleyTr_R (c : F) : cayleyTr (zmk c 0 0 0 0 0 0 c) = 0 := CharTwo.add_self_eq_zero c

abbrev a1E (α p q' : F) : ↥(cayleyGroup F) :=
  g2X ![α, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0)

theorem a1E_comm (α p q' r u₀ u₁ u₂ v₀ v₁ v₂ : F) :
    cgE (a1E α p q') (zmk r u₀ u₁ u₂ v₀ v₁ v₂ r) - zmk r u₀ u₁ u₂ v₀ v₁ v₂ r =
      zmk (α * v₀) (p * u₁ + q' * u₂ + α * α * v₀) 0 0 0 (p * v₀ + α * u₂) (q' * v₀ + α * u₁)
        (α * v₀) := by
  have hy : (![0, 0, 0] : Fin 3 → F) = 0 := funext fun i => by fin_cases i <;> rfl
  rw [cg_mul_apply, cg_mul_apply, hy, g2Y_zero]
  change xaFun ![α, 0, 0] (gAFun (CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat p q' 0)
    (zmk r u₀ u₁ u₂ v₀ v₁ v₂ r)) - _ = _
  rw [gAFun_zmk, xaFun_zmk, zmk_sub']
  simp only [CFSG.ClassicalInvolution.ModelFacts.OddCover.uMat, Matrix.adjugate_fin_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.tail_cons, Matrix.head_fin_const]
  refine zmk_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp only [CharTwo.sub_eq_add, CharTwo.neg_eq])
  all_goals ring_nf
  all_goals (try simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add])

theorem mem_o0Comm_A1_iff {t : quasithinZorn F} :
    t ∈ o0Comm (A1 F) ↔ ∃ α p q' u₁ u₂ v₀ : F,
      t = zmk (α * v₀) (p * u₁ + q' * u₂ + α * α * v₀) 0 0 0 (p * v₀ + α * u₂)
        (q' * v₀ + α * u₁) (α * v₀) := by
  constructor
  · rintro ⟨γ, hγ, x, hx, rfl⟩
    obtain ⟨α, p, q', rfl⟩ := exists_eq_of_mem_A1 hγ
    rw [zorn_eta x] at hx ⊢
    rw [cayleyTr_zmk] at hx
    have hs : x.2.2.2 = x.1 := (CharTwo.add_eq_zero.1 hx).symm
    rw [hs]
    exact ⟨α, p, q', x.2.1 1, x.2.1 2, x.2.2.1 0, a1E_comm α p q' _ _ _ _ _ _ _⟩
  · rintro ⟨α, p, q', u₁, u₂, v₀, rfl⟩
    exact ⟨_, kerElt_mem_A1 α p q', zmk 0 0 u₁ u₂ v₀ 0 0 0, by rw [cayleyTr_zmk, add_zero],
      a1E_comm α p q' 0 0 u₁ u₂ v₀ 0 0⟩

theorem mem_tA1_of_mem_o0Comm {t : quasithinZorn F} (ht : t ∈ o0Comm (A1 F)) : t ∈ tA1 F := by
  obtain ⟨α, p, q', u₁, u₂, v₀, rfl⟩ := mem_o0Comm_A1_iff.1 ht
  exact ⟨_, _, _, _, rfl⟩

theorem mem_o0Comm_A1 {t : quasithinZorn F} (ht : t ∈ tA1 F)
    (hR : ∀ c : F, t ≠ zmk c 0 0 0 0 0 0 c) : t ∈ o0Comm (A1 F) := by
  obtain ⟨ρ, τ, σ₁, σ₂, rfl⟩ := ht
  rw [mem_o0Comm_A1_iff]
  by_cases hσ : σ₁ = 0 ∧ σ₂ = 0
  · obtain ⟨rfl, rfl⟩ := hσ
    have hτ : τ ≠ 0 := by
      rintro rfl
      exact hR ρ rfl
    by_cases hρ : ρ = 0
    · subst hρ
      refine ⟨0, τ, 0, 1, 0, 0, ?_⟩
      apply zmk_congr <;> ring
    · refine ⟨τ / ρ, 0, 0, 0, 0, ρ * ρ / τ, ?_⟩
      apply zmk_congr <;> field_simp <;> ring
  ·
    obtain ⟨u₁, u₂, hu⟩ : ∃ u₁ u₂ : F, σ₁ * u₁ + σ₂ * u₂ = τ + ρ * ρ := by
      by_cases h1 : σ₁ = 0
      · have h2 : σ₂ ≠ 0 := fun h2 => hσ ⟨h1, h2⟩
        exact ⟨0, (τ + ρ * ρ) / σ₂, by rw [h1]; field_simp; ring⟩
      · exact ⟨(τ + ρ * ρ) / σ₁, 0, by field_simp; ring⟩
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    refine ⟨ρ, σ₁ + ρ * u₂, σ₂ + ρ * u₁, u₁, u₂, 1, ?_⟩
    apply zmk_congr
    · ring
    · linear_combination -hu - (ρ * ρ + ρ * u₁ * u₂) * h2
    · ring
    · ring
    · ring
    · linear_combination -(ρ * u₂) * h2
    · linear_combination -(ρ * u₁) * h2
    · ring

theorem exists_sub_o0Comm_A1 (c : F) : ∃ t₁ ∈ o0Comm (A1 F), ∃ t₂ ∈ o0Comm (A1 F),
    zmk c 0 0 0 0 0 0 c = t₁ - t₂ := by
  refine ⟨zmk c c 0 0 0 0 0 c, mem_o0Comm_A1_iff.2 ⟨1, 0, 0, 0, 0, c, ?_⟩,
    zmk 0 c 0 0 0 0 0 0, mem_o0Comm_A1_iff.2 ⟨0, c, 0, 1, 0, 0, ?_⟩, ?_⟩
  · apply zmk_congr <;> ring
  · apply zmk_congr <;> ring
  · rw [zmk_sub']
    apply zmk_congr <;> ring

theorem eq_one_of_fix_O0 {γ : ↥(cayleyGroup F)} (h : ∀ x, cayleyTr x = 0 → cgE γ x = x) :
    γ = 1 :=
  cayley_eq_one fun w => by rw [g2Act_apply, h _ (cayleyTr_zI w), zP_zI]

theorem eq_R_of_fixed {x : quasithinZorn F} (hx : cayleyTr x = 0)
    (h : ∀ γ : ↥(cayleyGroup F), cgE γ x = x) : x = zmk x.1 0 0 0 0 0 0 x.1 := by
  have hxa : ∀ a : Fin 3 → F, xaFun a x = x := fun a => h (g2X a)
  have hv : ∀ a : Fin 3 → F, a 0 * x.2.2.1 0 + a 1 * x.2.2.1 1 + a 2 * x.2.2.1 2 = 0 := by
    intro a
    have h1 := congrArg Prod.fst (hxa a)
    simp only [xaFun, zmk] at h1
    linear_combination h1
  have hw : ∀ (a : Fin 3 → F) (j : Fin 3), (xaFun a x).2.2.1 j = x.2.2.1 j :=
    fun a j => congrFun (congrArg (fun y : quasithinZorn F => y.2.2.1) (hxa a)) j
  have v0 := hv ![1, 0, 0]
  have v1 := hv ![0, 1, 0]
  have v2 := hv ![0, 0, 1]
  have u1 := hw ![1, 0, 0] 2
  have u2 := hw ![1, 0, 0] 1
  have u0 := hw ![0, 1, 0] 2
  simp only [xaFun, zmk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at v0 v1 v2 u0 u1 u2
  rw [cayleyTr] at hx
  have hs : x.2.2.2 = x.1 := (CharTwo.add_eq_zero.1 hx).symm
  have hu0 : x.2.1 0 = 0 := by linear_combination -u0
  have hu1 : x.2.1 1 = 0 := by linear_combination u1
  have hu2 : x.2.1 2 = 0 := by linear_combination -u2
  have hv0 : x.2.2.1 0 = 0 := by linear_combination v0
  have hv1 : x.2.2.1 1 = 0 := by linear_combination v1
  have hv2 : x.2.2.1 2 = 0 := by linear_combination v2
  conv_lhs => rw [zorn_eta x]
  rw [hs, hu0, hu1, hu2, hv0, hv1, hv2]

theorem eq_conj_A1_of_offender [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (hΓne : Γ ≠ ⊥)
    (hoff : Nat.card F ^ 6 ≤ Nat.card ↥Γ * Nat.card (fixSub Γ)) :
    ∃ x : ↥(cayleyGroup F), Γ = (A1 F).map (MulAut.conj x).toMonoidHom := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨hΓ3, hfix3⟩ := (card_mul_card_fixSub hF hn hΓ1 hΓc).2 hΓne hoff
  refine eq_conj_A1 hF hn hΓ1 hΓc hΓne ?_
  intro B hB hcard w hw γ hγ
  have hBq : Nat.card F < Nat.card ↥B := by
    have e3 : Nat.card F ^ 3 = Nat.card F ^ 2 * Nat.card F := by ring
    rw [hΓ3, e3] at hcard
    exact Nat.lt_of_mul_lt_mul_left hcard
  have hBne : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hBq
    omega
  have hfixB : Nat.card (fixSub B) < Nat.card F ^ 4 := by
    by_contra hge
    have := card_le_of_card_fixSub (fun b hb => hΓ1 b (hB hb)) hBne (not_lt.1 hge)
    omega
  have hle : fixSub Γ ≤ fixSub B := fun x hx b hb => hx b (hB hb)
  have hdB : Nat.card (fixSub B) = Nat.card F ^ Module.finrank F (fixSub B) :=
    Module.natCard_eq_pow_finrank
  have hd : Module.finrank F (fixSub B) < 4 := by
    rw [hdB] at hfixB
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 hfixB
  have hcB : Nat.card (fixSub B) ≤ Nat.card (fixSub Γ) := by
    rw [hdB, hfix3]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have heq : (fixSub Γ).toAddSubgroup = (fixSub B).toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hle hcB
  have hwΓ : w ∈ fixSub Γ := by
    rw [Submodule.toAddSubgroup_injective heq]
    exact hw
  exact hwΓ γ hγ

end Char2

end CFSG.Quasithin.MS93
