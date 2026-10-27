module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexSpec

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Quasithin CFSG.Quasithin.H13.F45Ru CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

universe u v

section Generic

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}
  [GraphAction X Γ]

theorem encard_neighborSet_smul' (g : X) (a : V) :
    (Γ.neighborSet (g • a)).encard = (Γ.neighborSet a).encard := by
  have : Γ.neighborSet (g • a) = (fun w : V => g • w) '' Γ.neighborSet a := by
    ext w
    constructor
    · intro h
      refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
      have := (GraphAction.adj_smul g⁻¹ (g • a) w).mpr h
      simpa using this
    · rintro ⟨w', hw', rfl⟩
      exact (GraphAction.adj_smul g a w').mpr hw'
  rw [this]
  exact Function.Injective.encard_image (f := fun w : V => g • w) (MulAction.injective g) _

theorem cover_of_flags {v₁ v₂ : V} (hconn : Γ.Connected)
    (f₁ : ∀ b, Γ.Adj v₁ b → ∃ y : X, y • v₁ = v₁ ∧ y • v₂ = b)
    (f₂ : ∀ b, Γ.Adj v₂ b → ∃ y : X, y • v₂ = v₂ ∧ y • v₁ = b) (a : V) :
    ∃ y : X, y • v₁ = a ∨ y • v₂ = a := by
  have step : ∀ a b : V, Γ.Adj a b → (∃ y : X, y • v₁ = a ∨ y • v₂ = a) →
      ∃ y : X, y • v₁ = b ∨ y • v₂ = b := by
    intro a b hab ⟨y, hy⟩
    rcases hy with rfl | rfl
    · have h := (GraphAction.adj_smul y⁻¹ (y • v₁) b).mpr hab
      rw [inv_smul_smul] at h
      obtain ⟨y', hy1, hy2⟩ := f₁ _ h
      refine ⟨y * y', Or.inr ?_⟩
      rw [mul_smul, hy2, smul_inv_smul]
    · have h := (GraphAction.adj_smul y⁻¹ (y • v₂) b).mpr hab
      rw [inv_smul_smul] at h
      obtain ⟨y', hy1, hy2⟩ := f₂ _ h
      refine ⟨y * y', Or.inl ?_⟩
      rw [mul_smul, hy2, smul_inv_smul]
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected v₁ a)
  induction hr with
  | refl => exact ⟨1, Or.inl (one_smul _ _)⟩
  | tail _ hbc ih => exact step _ _ hbc ih

end Generic

theorem hexOfCode_zero : hexOfCode 0 = (Sum.inl 0 : HexVtx) := hexOfCode_inl (by norm_num)

theorem hexOfCode_819 : hexOfCode 819 = (Sum.inr 0 : HexVtx) :=
  hexOfCode_inr (by norm_num) (by norm_num)

theorem isGenPolygon_hex_cov {X : Type*} [Group X] [MulAction X HexVtx] [GraphAction X hexGraph]
    {ptL l0 p0 l1 p1 cy : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (hl0 : hexLayOK lineTab ptL 0 l0 p0 = true)
    (hl1 : hexLayOK lineTab ptL 819 l1 p1 = true) (hc : hexCycleOK lineTab ptL cy = true)
    {b : ℕ} (hb : b < 3276) (h6 : l0[b]! = 6)
    (hcov : ∀ x : HexVtx, ∃ g : X, g • (Sum.inl 0 : HexVtx) = x ∨ g • (Sum.inr 0 : HexVtx) = x)
    (hv0 : 2 ≤ (hexGraph.neighborSet (Sum.inl 0)).encard)
    (hv1 : 2 ≤ (hexGraph.neighborSet (Sum.inr 0)).encard) : IsGenPolygon hexGraph 6 := by
  have hLay0 := layers_of_hexLayOK hp hi hl0
  have hLay1 := layers_of_hexLayOK hp hi hl1
  rw [hexOfCode_zero] at hLay0
  rw [hexOfCode_819] at hLay1
  obtain ⟨hcs, hc'⟩ : cy.size = 12 ∧ ∀ i < 12, cy[i]! < 3276 ∧
      cy[(i + 1) % 12]! ∈ hexNbr lineTab ptL cy[i]! ∧ cy[i]! ≠ cy[(i + 2) % 12]! := by
    simp only [hexCycleOK, Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨hc.1, fun i hi' => ?_⟩
    have := allLt_spec hc.2 hi'
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, bne_iff_ne,
      ne_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hmod : ∀ i : ℕ, ((i + 1) % 12) = (i % 12 + 1) % 12 := fun i => by omega
  have hmod2 : ∀ i : ℕ, ((i + 2) % 12) = (i % 12 + 2) % 12 := fun i => by omega
  refine isGenPolygon_of_layers (by norm_num) (fun x => x.isRight) ?_
    (layers_of_cover hLay0 hLay1 hcov) ?_ (fun i => hexOfCode cy[i % 12]!) ?_ ?_ ?_ ?_
  · intro x y h
    cases x <;> cases y <;> first | exact h.elim | simp
  · exact ⟨_, _, hexOfCode b, hLay0, by
      show l0[hexCode (hexOfCode b)]! = 6
      rw [hexCode_hexOfCode hb]
      exact h6⟩
  · intro i
    obtain ⟨h1, h2, -⟩ := hc' (i % 12) (Nat.mod_lt _ (by norm_num))
    show hexGraph.Adj (hexOfCode cy[i % 12]!) (hexOfCode cy[(i + 1) % 12]!)
    rw [hexAdj_iff_nbr hp hi, hexCode_hexOfCode h1,
      hexCode_hexOfCode (hc' _ (Nat.mod_lt _ (by norm_num))).1, hmod]
    exact h2
  · intro i
    obtain ⟨h1, -, h3⟩ := hc' (i % 12) (Nat.mod_lt _ (by norm_num))
    intro h
    have h' := congrArg hexCode h
    rw [hexCode_hexOfCode h1, hmod2,
      hexCode_hexOfCode (hc' _ (Nat.mod_lt _ (by norm_num))).1] at h'
    exact h3 h'
  · intro i
    show hexOfCode cy[(i + 12) % 12]! = hexOfCode cy[i % 12]!
    rw [Nat.add_mod_right]
  · intro x
    obtain ⟨g, hg | hg⟩ := hcov x
    · rw [← hg, encard_neighborSet_smul']
      exact hv0
    · rw [← hg, encard_neighborSet_smul']
      exact hv1

end CFSG.Quasithin.D4Hex
