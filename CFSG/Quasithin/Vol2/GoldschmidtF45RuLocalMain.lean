module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLocal
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.F45

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V} [GraphAction X Γ]
  {a b₀ w₀ w₁ : V} {m : ℕ} {Fg : Set X} {L : Finset X} {nG nO d : ℕ}

omit [GraphAction X Γ] in
theorem LocalData.closure_le_fixer (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    Subgroup.closure Fg ≤ fixer X Γ a :=
  (Subgroup.closure_le _).2 fun f hf => D.Fg_fix f hf

theorem LocalData.qtrans [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) (b c : V)
    (hb : Γ.dist a b = m) (hc : Γ.dist a c = m) :
    ∃ q ∈ pCoreOf 2 (MulAction.stabilizer X a), q • b = c := by
  obtain ⟨g₁, hg₁, e₁⟩ := D.Fcov b hb
  obtain ⟨g₂, hg₂, e₂⟩ := D.Fcov c hc
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · rw [D.fixer_eq]
    exact Subgroup.mul_mem _ (D.closure_le_fixer hg₂) (Subgroup.inv_mem _ (D.closure_le_fixer hg₁))
  · rw [mul_smul, ← e₁, inv_smul_smul, e₂]

theorem LocalData.stab_unique [Finite X] (hconn : Γ.Connected)
    (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    ∀ x ∈ MulAction.stabilizer X a, x • b₀ = b₀ → (∀ w, Γ.Adj a w → x • w = w) → x = 1 := by
  set G := MulAction.stabilizer X a with hG
  have horb : MulAction.orbit G b₀ = {b | Γ.dist a b = m} := by
    ext b
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      have hg' : g • a = a := MulAction.mem_stabilizer_iff.mp hg
      have := GPath.dist_smul hconn g a b₀
      rw [hg'] at this
      exact this.trans D.b0
    · intro hb
      obtain ⟨g, hg, e⟩ := D.Fcov b hb
      exact ⟨⟨g, fixer_le_stab (D.closure_le_fixer hg)⟩, e⟩
  have h1 := card_stabilizer_mul_ncard_orbit (G := G) b₀
  rw [horb, D.card_O, D.card_G] at h1
  have hG0 : 0 < nG := by
    rw [← D.card_G]
    exact Nat.card_pos
  have hnO : 0 < nO := by
    rcases Nat.eq_zero_or_pos nO with h | h
    · rw [h, mul_zero] at h1
      omega
    · exact h
  have hSb : Nat.card (MulAction.stabilizer G b₀) = L.card :=
    Nat.eq_of_mul_eq_mul_right hnO (h1.trans D.card_L.symm)
  have hmap : Nat.card ((MulAction.stabilizer G b₀).map G.subtype) = L.card := by
    rw [Subgroup.card_map_of_injective G.subtype_injective, hSb]
  have hsub : (L : Set X) ⊆ ((MulAction.stabilizer G b₀).map G.subtype : Set X) := by
    intro h hh
    obtain ⟨hha, hhb⟩ := D.L_fix h hh
    exact ⟨⟨h, MulAction.mem_stabilizer_iff.mpr hha⟩, MulAction.mem_stabilizer_iff.mpr hhb, rfl⟩
  have heq : (L : Set X) = ((MulAction.stabilizer G b₀).map G.subtype : Set X) :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
      exact hmap.le) (Set.toFinite _)
  intro x hxG hxb hxw
  have hxSb : x ∈ ((MulAction.stabilizer G b₀).map G.subtype : Set X) :=
    ⟨⟨x, hxG⟩, MulAction.mem_stabilizer_iff.mpr hxb, rfl⟩
  have hxL : x ∈ L := by
    rw [← Finset.mem_coe, heq]
    exact hxSb
  by_contra hne
  obtain ⟨w, hw, hmove⟩ := D.L_move x hxL hne
  exact hmove (hxw w hw)

theorem LocalData.qfree [Finite X] (hconn : Γ.Connected)
    (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) (b : V) (hb : Γ.dist a b = m) (q : X)
    (hq : q ∈ pCoreOf 2 (MulAction.stabilizer X a)) (hqb : q • b = b) : q = 1 := by
  obtain ⟨g, hg, e⟩ := D.Fcov b hb
  have hgF : g ∈ fixer X Γ a := D.closure_le_fixer hg
  have hqF : q ∈ fixer X Γ a := D.pCoreOf_le_fixer hq
  have hxF : g⁻¹ * q * g ∈ fixer X Γ a :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgF) hqF) hgF
  have h1 : (g⁻¹ * q * g) • b₀ = b₀ := by
    rw [mul_smul, mul_smul, e, hqb]
    exact inv_smul_eq_iff.mpr e.symm
  have h2 : g⁻¹ * q * g = 1 := D.stab_unique hconn _ (fixer_le_stab hxF) h1 hxF.2
  calc q = g * (g⁻¹ * q * g) * g⁻¹ := by group
    _ = 1 := by rw [h2]; group

omit [GraphAction X Γ] in
theorem LocalData.two (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) (b c b' c' : V)
    (hb : Γ.Adj a b) (hc : Γ.Adj a c) (hbc : b ≠ c) (hb' : Γ.Adj a b') (hc' : Γ.Adj a c')
    (hbc' : b' ≠ c') : ∃ g : X, g • a = a ∧ g • b = b' ∧ g • c = c' := by
  obtain ⟨h₁, hL₁, e₁, e₁'⟩ := D.two_trans b c hb hc hbc
  obtain ⟨h₂, hL₂, e₂, e₂'⟩ := D.two_trans b' c' hb' hc' hbc'
  refine ⟨h₂ * h₁⁻¹, ?_, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.mpr (D.L_fix h₁ hL₁).1.symm, (D.L_fix h₂ hL₂).1]
  · rw [mul_smul, ← e₁, inv_smul_smul, e₂]
  · rw [mul_smul, ← e₁', inv_smul_smul, e₂']

theorem modelBase_of_local [Finite X] (hconn : Γ.Connected)
    (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    ModelBase Γ m a (pCoreOf 2 (MulAction.stabilizer X a)) where
  Qfix w hw _ hq := (D.pCoreOf_le_fixer hq).2 w hw
  Qtrans b c hb hc := D.qtrans b c hb hc
  Qfree b hb q hq hqb := D.qfree hconn b hb q hq hqb
  two := D.two

end CFSG.Quasithin.H13.F45Ru
