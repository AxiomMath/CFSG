module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuGrp
public import CFSG.Assembly.Defs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.F3Paths

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V]

@[expose] def fixer (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (a : V) : Subgroup X where
  carrier := {x | x • a = a ∧ ∀ w, Γ.Adj a w → x • w = w}
  one_mem' := ⟨one_smul _ _, fun w _ => one_smul _ _⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨by rw [mul_smul, hy.1, hx.1], fun w hw => by rw [mul_smul, hy.2 w hw, hx.2 w hw]⟩
  inv_mem' := fun {x} hx =>
    ⟨inv_smul_eq_iff.mpr hx.1.symm, fun w hw => inv_smul_eq_iff.mpr (hx.2 w hw).symm⟩

structure LocalData (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (m : ℕ) (a b₀ w₀ w₁ : V) (Fg : Set X) (L : Finset X) (nG nO d : ℕ) : Prop where
  Fg_fix : ∀ f ∈ Fg, f • a = a ∧ ∀ w, Γ.Adj a w → f • w = w
  Fcov : ∀ b, Γ.dist a b = m → ∃ g ∈ Subgroup.closure Fg, g • b₀ = b
  b0 : Γ.dist a b₀ = m
  L_fix : ∀ h ∈ L, h • a = a ∧ h • b₀ = b₀
  L_move : ∀ h ∈ L, h ≠ 1 → ∃ w, Γ.Adj a w ∧ h • w ≠ w
  card_G : Nat.card (MulAction.stabilizer X a) = nG
  card_O : {b | Γ.dist a b = m}.ncard = nO
  card_L : L.card * nO = nG
  card_N : Nat.card (Γ.neighborSet a) = d
  adj0 : Γ.Adj a w₀
  adj1 : Γ.Adj a w₁
  ne01 : w₀ ≠ w₁
  two_trans : ∀ u u', Γ.Adj a u → Γ.Adj a u' → u ≠ u' → ∃ h ∈ L, h • w₀ = u ∧ h • w₁ = u'
  pow2 : ∃ k, nG = 2 ^ k * d
  odd : ¬ 2 ∣ d

section Helpers

variable {Γ : SimpleGraph V} [GraphAction X Γ] {a : V}

theorem adj_smul_of_stab {g : X} (hg : g • a = a) {w : V} (h : Γ.Adj a w) : Γ.Adj a (g • w) := by
  have := (GraphAction.adj_smul g a w).mpr h
  rwa [hg] at this

theorem fixer_normalized {g : X} (hg : g • a = a) {x : X} (hx : x ∈ fixer X Γ a) :
    g * x * g⁻¹ ∈ fixer X Γ a := by
  have hg' : g⁻¹ • a = a := inv_smul_eq_iff.mpr hg.symm
  refine ⟨?_, fun w hw => ?_⟩
  · rw [mul_smul, mul_smul, hg', hx.1, hg]
  · have hw' : Γ.Adj a (g⁻¹ • w) := adj_smul_of_stab hg' hw
    rw [mul_smul, mul_smul, hx.2 _ hw', smul_inv_smul]

omit [GraphAction X Γ] in
theorem fixer_le_stab : fixer X Γ a ≤ MulAction.stabilizer X a :=
  fun _ hx => MulAction.mem_stabilizer_iff.mpr hx.1

theorem stab_normalizes_fixer :
    MulAction.stabilizer X a ≤ Subgroup.normalizer (fixer X Γ a : Set X) := by
  intro g hg
  have hg' : g • a = a := MulAction.mem_stabilizer_iff.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => fixer_normalized hg' hh, fun hh => ?_⟩
  have := fixer_normalized (inv_smul_eq_iff.mpr hg'.symm) hh
  simpa [mul_assoc] using this

end Helpers

section Local

variable {Γ : SimpleGraph V} [GraphAction X Γ] {a b₀ w₀ w₁ : V} {m : ℕ} {Fg : Set X}
  {L : Finset X} {nG nO d : ℕ}

theorem LocalData.orbit_nbr (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    MulAction.orbit (MulAction.stabilizer X a) w₀ = Γ.neighborSet a := by
  ext u
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact adj_smul_of_stab (MulAction.mem_stabilizer_iff.mp hg) D.adj0
  · intro hu
    by_cases h1 : u = w₁
    · obtain ⟨h, hL, hh, -⟩ := D.two_trans u w₀ hu D.adj0 (by rw [h1]; exact D.ne01.symm)
      exact ⟨⟨h, MulAction.mem_stabilizer_iff.mpr (D.L_fix h hL).1⟩, hh⟩
    · obtain ⟨h, hL, hh, -⟩ := D.two_trans u w₁ hu D.adj1 h1
      exact ⟨⟨h, MulAction.mem_stabilizer_iff.mpr (D.L_fix h hL).1⟩, hh⟩

theorem LocalData.card_orbit_nbr (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    (MulAction.orbit (MulAction.stabilizer X a) w₀).ncard = d := by
  rw [D.orbit_nbr, ← Nat.card_coe_set_eq]
  exact D.card_N

omit [GraphAction X Γ] in
theorem LocalData.d_pos (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) : 0 < d :=
  Nat.pos_of_ne_zero fun h => D.odd (by rw [h]; exact dvd_zero 2)

theorem LocalData.isPGroup_stab [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    IsPGroup 2 (MulAction.stabilizer (MulAction.stabilizer X a) w₀) := by
  obtain ⟨k, hk⟩ := D.pow2
  have h1 := card_stabilizer_mul_ncard_orbit (G := MulAction.stabilizer X a) w₀
  rw [D.card_orbit_nbr, D.card_G, hk] at h1
  have := D.d_pos
  exact IsPGroup.of_card (n := k) (Nat.eq_of_mul_eq_mul_right this h1)

theorem LocalData.isPGroup_fixer [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    IsPGroup 2 (fixer X Γ a) := by
  have h1 := D.isPGroup_stab.map (MulAction.stabilizer X a).subtype
  refine IsPGroup.to_le h1 ?_
  intro x hx
  exact ⟨⟨x, fixer_le_stab hx⟩, MulAction.mem_stabilizer_iff.mpr (hx.2 w₀ D.adj0), rfl⟩

theorem fixer_le_pCoreOf [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    fixer X Γ a ≤ pCoreOf 2 (MulAction.stabilizer X a) :=
  le_pCoreOf_of_le_normalizer 2 fixer_le_stab stab_normalizes_fixer D.isPGroup_fixer

theorem LocalData.pCoreOf_le_fixer [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    pCoreOf 2 (MulAction.stabilizer X a) ≤ fixer X Γ a := by
  intro x hx
  have hxG : x ∈ MulAction.stabilizer X a := pCoreOf_le 2 _ hx
  refine ⟨MulAction.mem_stabilizer_iff.mp hxG, fun w hw => ?_⟩
  set G := MulAction.stabilizer X a with hGdef
  have hnorm : ((pCoreOf 2 G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 G)).2 (le_normalizer_pCoreOf 2 G)
  have hpg : IsPGroup 2 ((pCoreOf 2 G).subgroupOf G) :=
    IsPGroup.of_equiv (pCoreOf_isPGroup 2 G) (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 G)).symm
  have hd : ¬ 2 ∣ Nat.card (MulAction.orbit G w₀) := by
    rw [Nat.card_coe_set_eq, D.card_orbit_nbr]
    exact D.odd
  have hwo : w ∈ MulAction.orbit G w₀ := by
    rw [D.orbit_nbr]
    exact hw
  have hnorm' : ((pCoreOf 2 G).subgroupOf G).Normal := hnorm
  have hfin : Finite (MulAction.orbit G w₀) := (Set.finite_range (fun g : G => g • w₀)).to_subtype
  have := normal_pgroup_fixes (Ω := MulAction.orbit G w₀) ((pCoreOf 2 G).subgroupOf G) hpg hd
    ⟨x, hxG⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨w, hwo⟩
  exact congrArg Subtype.val this

theorem LocalData.fixer_eq [Finite X] (D : LocalData X Γ m a b₀ w₀ w₁ Fg L nG nO d) :
    pCoreOf 2 (MulAction.stabilizer X a) = fixer X Γ a :=
  le_antisymm D.pCoreOf_le_fixer (fixer_le_pCoreOf D)

end Local

end CFSG.Quasithin.H13.F45Ru
