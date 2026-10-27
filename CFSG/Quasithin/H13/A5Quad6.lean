module

public import CFSG.Quasithin.H13.A5S1521f
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Trans

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_transitive_quad (hV : ∀ w : V, w ^ 2 = 1) (X : Subgroup (MulAut V))
    (htr : ∀ a b : V, a ≠ 1 → b ≠ 1 → ∃ x ∈ X, x a = b) (hcard : 4 < Nat.card V)
    (q : V → ZMod 2) (hq : ∀ x ∈ X, ∀ w, q (x w) = q w)
    (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
    (hnd : ∀ a, a ≠ 1 → ∃ w, polarQ q a w ≠ 0) : False := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hmul : ∀ x y : V, x * y = 1 → x = y := fun x y h => by
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV y)
    rw [← hy]
    exact eq_inv_of_mul_eq_one_left h
  have hq1 : q 1 = 0 := by
    have h := polarQ_one_left hβ 1
    rw [polarQ, mul_one] at h
    revert h
    generalize q 1 = t
    decide +revert
  have hconst : ∀ a b : V, a ≠ 1 → b ≠ 1 → q a = q b := by
    intro a b ha hb
    obtain ⟨x, hx, rfl⟩ := htr a b ha hb
    exact (hq x hx a).symm
  have hne : ∃ a : V, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card V ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
    omega
  obtain ⟨a, ha⟩ := hne
  have hb : ∃ b : V, b ∉ ({1, a} : Finset V) := by
    by_contra h
    push Not at h
    have : Nat.card V ≤ 2 := by
      rw [Nat.card_eq_fintype_card]
      calc Fintype.card V = (Finset.univ : Finset V).card := rfl
        _ ≤ ({1, a} : Finset V).card := Finset.card_le_card fun x _ => h x
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨b, hb⟩ := hb
  have hc : ∃ c : V, c ∉ ({1, a, b, a * b} : Finset V) := by
    by_contra h
    push Not at h
    have : Nat.card V ≤ 4 := by
      rw [Nat.card_eq_fintype_card]
      calc Fintype.card V = (Finset.univ : Finset V).card := rfl
        _ ≤ ({1, a, b, a * b} : Finset V).card := Finset.card_le_card fun x _ => h x
        _ ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨c, hc⟩ := hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb hc
  obtain ⟨hb1, hba⟩ := hb
  obtain ⟨hc1, hca, hcb, hcab⟩ := hc
  by_cases h0 : q a = 0
  ·
    obtain ⟨w, hw⟩ := hnd a ha
    apply hw
    have hq0 : ∀ x, q x = 0 := fun x => by
      by_cases hx : x = 1
      · rw [hx, hq1]
      · rw [hconst x a hx ha, h0]
    rw [polarQ, hq0, hq0, hq0]
    decide
  ·
    have h1 : q a = 1 := by
      revert h0
      generalize q a = t
      decide +revert
    have hq1' : ∀ x, x ≠ 1 → q x = 1 := fun x hx => (hconst x a hx ha).trans h1
    have hab : a * b ≠ 1 := fun h => hba (hmul a b h).symm
    have hac : a * c ≠ 1 := fun h => hca (hmul a c h).symm
    have hbc : b * c ≠ 1 := fun h => hcb (hmul b c h).symm
    have habc : a * (b * c) ≠ 1 := fun h => hcab (by
      rw [← mul_assoc] at h
      exact (hmul _ _ h).symm)
    have e1 : polarQ q a b = 1 := by
      rw [polarQ, hq1' _ hab, hq1' _ ha, hq1' _ hb1]
      decide
    have e2 : polarQ q a c = 1 := by
      rw [polarQ, hq1' _ hac, hq1' _ ha, hq1' _ hc1]
      decide
    have e3 : polarQ q a (b * c) = 1 := by
      rw [polarQ, hq1' _ habc, hq1' _ ha, hq1' _ hbc]
      decide
    rw [polarQ_mul_right hβ, e1, e2] at e3
    exact absurd e3 (by decide)

omit [Finite V] in
theorem transitive_of_realizesVia {D : FFModel} {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π)
    (htr : ∀ m₁ ∈ D.sec, m₁ ∉ D.ker → ∀ m₂ ∈ D.sec, m₂ ∉ D.ker →
      ∃ γ : D.Gam, D.act γ m₁ * m₂⁻¹ ∈ D.ker) :
    ∀ x y : V, x ≠ 1 → y ≠ 1 → ∃ g ∈ H, g x = y := by
  obtain ⟨-, -, -, -, -, hsec, -, β, -, hβk, hβe⟩ := h
  intro x y hx hy
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (β ⟨x, trivial⟩)
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (β ⟨y, trivial⟩)
  have hne : ∀ (z : V) (m : ↥D.sec), z ≠ 1 → (QuotientGroup.mk m : ↥D.sec ⧸ _) = β ⟨z, trivial⟩ →
      (m : D.Amb) ∉ D.ker := by
    intro z m hz hm hk
    apply hz
    have h1 : β ⟨z, trivial⟩ = 1 := by
      rw [← hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
    exact Subgroup.mem_bot.mp ((hβk _).mp h1)
  obtain ⟨γ, hγ⟩ := htr m₁ m₁.2 (hne x m₁ hx hm₁) m₂ m₂.2 (hne y m₂ hy hm₂)
  refine ⟨π γ, (π γ).2, ?_⟩
  have he := hβe γ ⟨x, trivial⟩ m₁ trivial (hsec γ m₁ m₁.2) hm₁.symm
  have hβeq : β ⟨((π γ : ↥H) : MulAut V) x, trivial⟩ = β ⟨y, trivial⟩ := by
    rw [he, ← hm₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h' := D.ker.inv_mem hγ
    rw [mul_inv_rev, inv_inv] at h'
    simpa [mul_comm] using h'
  have h1 : β (⟨((π γ : ↥H) : MulAut V) x, trivial⟩ * (⟨y, trivial⟩ : ↥(⊤ : Subgroup V))⁻¹) =
      1 := by
    rw [map_mul, map_inv, hβeq, mul_inv_cancel]
  have h2 := Subgroup.mem_bot.mp ((hβk _).mp h1)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_eq_one] at h2
  exact h2

end Trans

section D6

theorem mem_zpowers_of_mul_self {M : Type*} [Group M] {a x : M} (ha : a * a = 1) :
    x ∈ Subgroup.zpowers a ↔ x = 1 ∨ x = a := by
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    clear hx
    induction k using Int.induction_on with
    | zero => left; rw [zpow_zero]
    | succ i ih =>
      rw [zpow_add_one]
      rcases ih with h | h
      · right; rw [h, one_mul]
      · left; rw [h, ha]
    | pred i ih =>
      rw [zpow_sub_one, hinv]
      rcases ih with h | h
      · right; rw [h, one_mul]
      · left; rw [h, ha]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem allOnes_mul_self (n : ℕ) : G6.allOnes n * G6.allOnes n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  show (1 : ZMod 2) + 1 = 0
  decide

theorem allOnes_mem_coreMod6 : G6.allOnes 6 ∈ G6.coreMod 6 := by
  rw [G6.mem_coreMod]
  decide

theorem d6_class : ∀ m : Fin 6 → ZMod 2, ∑ i, m i = 0 → m ≠ 0 → m ≠ (fun _ => 1) →
    ∃ i j : Fin 6, i ≠ j ∧ (m = Pi.single i 1 + Pi.single j 1 ∨
      m = Pi.single i 1 + Pi.single j 1 + (fun _ => 1)) := by
  decide +kernel

theorem a6_two_trans : ∀ i j : Fin 6, i ≠ j →
    ∃ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ σ 0 = i ∧ σ 1 = j := by
  decide +kernel

theorem d6_class' {m : G6.PermMod 6} (hm : m ∈ G6.coreMod 6)
    (hk : m ∉ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6) :
    ∃ i j : Fin 6, i ≠ j ∧ (m = G64.pairVec i j ∨ m = G64.pairVec i j * G6.allOnes 6) := by
  have h1 : Multiplicative.toAdd m ≠ 0 := fun h => hk ⟨(mem_zpowers_of_mul_self
    (allOnes_mul_self 6)).mpr (Or.inl (Multiplicative.toAdd.injective h)), hm⟩
  have h2 : Multiplicative.toAdd m ≠ (fun _ => 1) := fun h => hk ⟨(mem_zpowers_of_mul_self
    (allOnes_mul_self 6)).mpr (Or.inr (Multiplicative.toAdd.injective h)), hm⟩
  obtain ⟨i, j, hij, h⟩ := d6_class (Multiplicative.toAdd m) (G6.mem_coreMod.mp hm) h1 h2
  refine ⟨i, j, hij, ?_⟩
  rcases h with h | h
  · left
    apply Multiplicative.toAdd.injective
    rw [h]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    rw [h]
    rfl

theorem mem_ker6_of {p ε ε' : G6.PermMod 6} (hε : ε = 1 ∨ ε = G6.allOnes 6)
    (hε' : ε' = 1 ∨ ε' = G6.allOnes 6) :
    p * ε * (p * ε')⁻¹ ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 := by
  have key : ∀ (M : Type) [CommGroup M] (p ε ε' : M), p * ε * (p * ε')⁻¹ = ε * ε'⁻¹ := by
    intro M _ p ε ε'
    rw [mul_inv_rev, mul_comm p ε, mul_assoc, mul_comm ε'⁻¹ p⁻¹, mul_inv_cancel_left]
  have hZ : ∀ x : G6.PermMod 6, (x = 1 ∨ x = G6.allOnes 6) →
      x ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 := by
    rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact ⟨Subgroup.mem_zpowers _, allOnes_mem_coreMod6⟩
  have h := Subgroup.mul_mem _ (hZ ε hε) (Subgroup.inv_mem _ (hZ ε' hε'))
  convert h using 1
  exact key _ p ε ε'

theorem altDn6_transitive : ∀ m₁ ∈ (FFModel.altDn 6).sec, m₁ ∉ (FFModel.altDn 6).ker →
    ∀ m₂ ∈ (FFModel.altDn 6).sec, m₂ ∉ (FFModel.altDn 6).ker →
      ∃ γ : (FFModel.altDn 6).Gam, (FFModel.altDn 6).act γ m₁ * m₂⁻¹ ∈ (FFModel.altDn 6).ker := by
  intro (m₁ : G6.PermMod 6) hm₁ hk₁ (m₂ : G6.PermMod 6) hm₂ hk₂
  obtain ⟨i, j, hij, h1⟩ := d6_class' hm₁ hk₁
  obtain ⟨k, l, hkl, h2⟩ := d6_class' hm₂ hk₂
  obtain ⟨σ₁, hs₁, h10, h11⟩ := a6_two_trans i j hij
  obtain ⟨σ₂, hs₂, h20, h21⟩ := a6_two_trans k l hkl
  refine ⟨⟨σ₂ * σ₁⁻¹, by rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs₁, hs₂]; rfl⟩, ?_⟩
  show G6.permAct 6 (σ₂ * σ₁⁻¹) m₁ * m₂⁻¹ ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6
  have hinv : ∀ x : Fin 6, σ₁⁻¹ (σ₁ x) = x := fun x => by simp
  have hp : G6.permAct 6 (σ₂ * σ₁⁻¹) (G64.pairVec i j) = G64.pairVec k l := by
    rw [G64.permAct_pairVec, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← h10, ← h11,
      hinv, hinv, h20, h21]
  have hA : G6.permAct 6 (σ₂ * σ₁⁻¹) (G6.allOnes 6) = G6.allOnes 6 := permAct_allOnes 6 _
  have hm₁' : G6.permAct 6 (σ₂ * σ₁⁻¹) m₁ = G64.pairVec k l * 1 ∨
      G6.permAct 6 (σ₂ * σ₁⁻¹) m₁ = G64.pairVec k l * G6.allOnes 6 := by
    rcases h1 with rfl | rfl
    · left
      rw [hp]
      exact (mul_one _).symm
    · right
      rw [map_mul, hp, hA]
  have hm₂' : m₂ = G64.pairVec k l * 1 ∨ m₂ = G64.pairVec k l * G6.allOnes 6 := by
    rcases h2 with rfl | rfl
    · left
      exact (mul_one _).symm
    · right
      rfl
  rcases hm₁' with e1 | e1 <;> rcases hm₂' with e2 | e2 <;> rw [e1, e2] <;>
    first
    | exact mem_ker6_of (Or.inl rfl) (Or.inl rfl)
    | exact mem_ker6_of (Or.inl rfl) (Or.inr rfl)
    | exact mem_ker6_of (Or.inr rfl) (Or.inl rfl)
    | exact mem_ker6_of (Or.inr rfl) (Or.inr rfl)

theorem symDn6_transitive : ∀ m₁ ∈ (FFModel.symDn 6).sec, m₁ ∉ (FFModel.symDn 6).ker →
    ∀ m₂ ∈ (FFModel.symDn 6).sec, m₂ ∉ (FFModel.symDn 6).ker →
      ∃ γ : (FFModel.symDn 6).Gam, (FFModel.symDn 6).act γ m₁ * m₂⁻¹ ∈ (FFModel.symDn 6).ker := by
  intro m₁ hm₁ hk₁ m₂ hm₂ hk₂
  obtain ⟨γ, hγ⟩ := altDn6_transitive m₁ hm₁ hk₁ m₂ hm₂ hk₂
  exact ⟨(γ : ↥(alternatingGroup (Fin 6))).1, hγ⟩

theorem d6_pair_ne : ∀ i j : Fin 6, i ≠ j →
    (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin 6 → ZMod 2) ≠ 0 ∧
      (Pi.single i (1 : ZMod 2) + Pi.single j 1 : Fin 6 → ZMod 2) ≠ (fun _ => 1) := by
  decide +kernel

theorem d6_pair_sub : ∀ i j : Fin 6,
    (-(Pi.single (0 : Fin 6) (1 : ZMod 2) + Pi.single i 1) + (Pi.single 0 1 + Pi.single j 1) :
      Fin 6 → ZMod 2) = Pi.single i (1 : ZMod 2) + Pi.single j 1 := by
  decide +kernel

theorem four_lt_card_D6 : 4 < Nat.card (↥(G6.coreMod 6) ⧸
    (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6)) := by
  let f : Fin 5 → ↥(G6.coreMod 6) ⧸
      (Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6) :=
    fun i => QuotientGroup.mk ⟨G64.pairVec 0 i.succ, G64.pairVec_mem_coreMod 0 i.succ⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hij' := QuotientGroup.eq.mp hij
    rw [Subgroup.mem_subgroupOf] at hij'
    have hz := (mem_zpowers_of_mul_self (allOnes_mul_self 6)).mp (Subgroup.mem_inf.mp hij').1
    have hne' : i.succ ≠ j.succ := fun h => hne (Fin.succ_injective _ h)
    obtain ⟨h1, h2⟩ := d6_pair_ne i.succ j.succ hne'
    have e : Multiplicative.toAdd (((⟨G64.pairVec 0 i.succ, G64.pairVec_mem_coreMod 0 i.succ⟩ :
        ↥(G6.coreMod 6))⁻¹ * ⟨G64.pairVec 0 j.succ, G64.pairVec_mem_coreMod 0 j.succ⟩ :
          ↥(G6.coreMod 6)) : G6.PermMod 6) = Pi.single i.succ 1 + Pi.single j.succ 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, toAdd_mul, toAdd_inv, G64.pairVec,
        toAdd_ofAdd]
      exact d6_pair_sub i.succ j.succ
    rcases hz with h | h
    · exact h1 (by rw [← e, h]; rfl)
    · exact h2 (by rw [← e, h]; rfl)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at this
  omega

theorem four_lt_card_of_realizesVia {V : Type} [CommGroup V] [Finite V] {D : FFModel}
    (hD : D = FFModel.altDn 6 ∨ D = FFModel.symDn 6) {H : Subgroup (MulAut V)}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ ⊥ π) : 4 < Nat.card V := by
  obtain ⟨e, -⟩ := G64.RealizesVia.exists_modEquiv h
  rw [Nat.card_congr e.toEquiv]
  rcases hD with rfl | rfl <;> exact four_lt_card_D6

theorem quad_rows_A6 {V : Type} [CommGroup V] [Finite V] (hV : ∀ w : V, w ^ 2 = 1)
    {G L A : Subgroup (MulAut V)} (hB4 : B4Hyp G L)
    (hrow : B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1)
    (q : V → ZMod 2) (hq : ∀ x ∈ G, ∀ w, q (x w) = q w)
    (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
    (hnd : ∀ a, a ≠ 1 → ∃ w, polarQ q a w ≠ 0) : False := by
  rcases hrow with ⟨-, ⟨π, hπ⟩, -⟩ | hSp
  · have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
    exact false_of_transitive_quad hV L (transitive_of_realizesVia hπ altDn6_transitive)
      (four_lt_card_of_realizesVia (Or.inl rfl) hπ) q (fun x hx => hq x (hLG hx)) hβ hnd
  · obtain ⟨π, hπ⟩ := asSp4S6 V _ ⊤ ⊥ hSp
    exact false_of_transitive_quad hV (ffJ G) (transitive_of_realizesVia hπ symDn6_transitive)
      (four_lt_card_of_realizesVia (Or.inr rfl) hπ) q (fun x hx => hq x (B6.ffJ_le G hx)) hβ
      hnd

end D6

end CFSG.Quasithin.H13.A5
