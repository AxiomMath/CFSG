module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

public section

namespace CFSG.Sporadic.Mathieu

open MulAction

open scoped Pointwise

theorem exists_smul_eq_seq {H X : Type*} [Group H] [MulAction H X] (L : ℕ → Subgroup H)
    (b : ℕ → X) (hanti : ∀ i, L (i + 1) ≤ L i) (K : ℕ)
    (hfix : ∀ i < K, ∀ g ∈ L (i + 1), g • b i = b i)
    (htrans : ∀ i < K, ∀ p : X, (∀ j < i, p ≠ b j) → ∃ g ∈ L i, g • b i = p) :
    ∀ k ≤ K, ∀ x : ℕ → X, (∀ i < k, ∀ j < i, x i ≠ x j) →
      ∃ g ∈ L 0, ∀ j < k, g • b j = x j := by
  have hmono : Antitone L := antitone_nat_of_succ_le hanti
  intro k
  induction k with
  | zero => exact fun _ x _ => ⟨1, (L 0).one_mem, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    intro hm x hx
    obtain ⟨g, hg, hgx⟩ := ih (by omega) x fun i hi j hj => hx i (by omega) j hj
    have hp : ∀ j < m, g⁻¹ • x m ≠ b j := by
      intro j hj he
      apply hx m (by omega) j hj
      rw [← hgx j hj, ← he, smul_inv_smul]
    obtain ⟨h, hh, hhb⟩ := htrans m (by omega) _ hp
    refine ⟨g * h, (L 0).mul_mem hg (hmono (Nat.zero_le m) hh), fun j hj => ?_⟩
    rcases Nat.lt_or_ge j m with hjm | hjm
    · rw [mul_smul, hfix j (by omega) h (hmono (show j + 1 ≤ m by omega) hh), hgx j hjm]
    · obtain rfl : j = m := by omega
      rw [mul_smul, hhb, smul_inv_smul]

section Orbits

variable {H X : Type*} [Group H] [MulAction H X]

theorem smul_mem_of_isBlock {B : Set X} (hB : IsBlock H B) {g : H} {p q : X} (hp : p ∈ B)
    (hgp : g • p ∈ B) (hq : q ∈ B) : g • q ∈ B := by
  rw [← hB.smul_eq_of_mem hp hgp]
  exact Set.smul_mem_smul_set hq

theorem isPreprimitive_of_orbits [IsPretransitive H X] (x a c : X)
    (hcov : ∀ y, y ≠ x → (∃ g : H, g • x = x ∧ g • a = y) ∨ ∃ g : H, g • x = x ∧ g • c = y)
    (hac : ∃ g : H, g • a = a ∧ g • x = c)
    (hca : ∃ g : H, g • c = c ∧ ∃ h : H, h • x = x ∧ h • a = g • x) :
    IsPreprimitive H X := by
  refine IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have horb : ∀ e : X, (∃ g : H, g • x = x ∧ g • e ∈ B) → ∀ h : H, h • x = x → h • e ∈ B := by
    rintro e ⟨g, hgx, hge⟩ h hhx
    have he : g⁻¹ • g • e ∈ B :=
      smul_mem_of_isBlock hB (g := g⁻¹) (p := x) hxB
        (by rw [inv_smul_eq_iff.2 hgx.symm]; exact hxB) hge
    rw [inv_smul_smul] at he
    exact smul_mem_of_isBlock hB hxB (by rw [hhx]; exact hxB) he
  have hAC : (∀ h : H, h • x = x → h • a ∈ B) → ∀ h : H, h • x = x → h • c ∈ B := by
    intro hA
    obtain ⟨g, hga, hgx⟩ := hac
    have ha : a ∈ B := by simpa using hA 1 (one_smul H x)
    refine horb c ⟨1, one_smul H x, ?_⟩
    rw [one_smul, ← hgx]
    exact smul_mem_of_isBlock hB ha (by rw [hga]; exact ha) hxB
  have hCA : (∀ h : H, h • x = x → h • c ∈ B) → ∀ h : H, h • x = x → h • a ∈ B := by
    intro hC
    obtain ⟨g, hgc, h, hhx, hha⟩ := hca
    have hc : c ∈ B := by simpa using hC 1 (one_smul H x)
    refine horb a ⟨h, hhx, ?_⟩
    rw [hha]
    exact smul_mem_of_isBlock hB hc (by rw [hgc]; exact hc) hxB
  by_cases hsub : ∀ y ∈ B, y = x
  · left
    intro p hp q hq
    rw [hsub p hp, hsub q hq]
  · right
    push Not at hsub
    obtain ⟨y, hyB, hyx⟩ := hsub
    have hboth : (∀ h : H, h • x = x → h • a ∈ B) ∧ ∀ h : H, h • x = x → h • c ∈ B := by
      rcases hcov y hyx with ⟨g, hgx, hgy⟩ | ⟨g, hgx, hgy⟩
      · have hA := horb a ⟨g, hgx, by rw [hgy]; exact hyB⟩
        exact ⟨hA, hAC hA⟩
      · have hC := horb c ⟨g, hgx, by rw [hgy]; exact hyB⟩
        exact ⟨hCA hC, hC⟩
    ext z
    refine ⟨fun _ => Set.mem_univ z, fun _ => ?_⟩
    by_cases hz : z = x
    · rw [hz]
      exact hxB
    · rcases hcov z hz with ⟨g, hgx, rfl⟩ | ⟨g, hgx, rfl⟩
      · exact hboth.1 g hgx
      · exact hboth.2 g hgx

end Orbits

section Duads

variable {n : ℕ}

@[expose] def duad (u v : Fin n) (h : u ≠ v) : Set.powersetCard (Fin n) 2 :=
  ⟨{u, v}, Set.powersetCard.mem_iff.2 (Finset.card_pair h)⟩

theorem duad_val (u v : Fin n) (h : u ≠ v) :
    ((duad u v h : Set.powersetCard (Fin n) 2) : Finset (Fin n)) = {u, v} :=
  rfl

theorem duad_comm (u v : Fin n) (h : u ≠ v) : duad u v h = duad v u h.symm :=
  Subtype.ext (Finset.pair_comm u v)

theorem duad_congr {u v u' v' : Fin n} (h : u ≠ v) (h' : u' ≠ v') (hu : u = u') (hv : v = v') :
    duad u v h = duad u' v' h' := by
  subst hu hv
  rfl

theorem exists_duad (s : Set.powersetCard (Fin n) 2) :
    ∃ u v : Fin n, ∃ h : u ≠ v, s = duad u v h := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨u, v, h, rfl⟩ := Finset.card_eq_two.1 (Set.powersetCard.mem_iff.1 hs)
  exact ⟨u, v, h, rfl⟩

variable {G : Type*} [Group G] [MulAction G (Fin n)]

theorem smul_duad (g : G) (u v : Fin n) (h : u ≠ v) :
    g • duad u v h = duad (g • u) (g • v) fun e => h (smul_left_cancel g e) := by
  apply Subtype.ext
  rw [Set.powersetCard.coe_smul, duad_val, duad_val, Finset.smul_finset_insert,
    Finset.smul_finset_singleton]

theorem smul_duad_eq {g : G} {u v u' v' : Fin n} (h : u ≠ v) (h' : u' ≠ v') (hu : g • u = u')
    (hv : g • v = v') : g • duad u v h = duad u' v' h' := by
  rw [smul_duad]
  exact duad_congr _ _ hu hv

theorem isPreprimitive_duads [IsPretransitive G (Set.powersetCard (Fin n) 2)]
    (p₀ p₁ p₂ p₃ p₄ : Fin n) (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h03 : p₀ ≠ p₃) (h04 : p₀ ≠ p₄)
    (h14 : p₁ ≠ p₄) (h23 : p₂ ≠ p₃) (h24 : p₂ ≠ p₄) (h34 : p₃ ≠ p₄)
    (h3 : ∀ u v w : Fin n, u ≠ v → u ≠ w → v ≠ w →
      ∃ g : G, g • p₀ = u ∧ g • p₁ = v ∧ g • p₂ = w)
    (h4 : ∀ u v w z : Fin n, u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      ∃ g : G, g • p₀ = u ∧ g • p₁ = v ∧ g • p₂ = w ∧ g • p₃ = z) :
    IsPreprimitive G (Set.powersetCard (Fin n) 2) := by
  refine isPreprimitive_of_orbits (duad p₀ p₁ h01) (duad p₀ p₂ h02) (duad p₂ p₃ h23)
    ?_ ?_ ?_
  · intro s hs
    obtain ⟨u, v, huv, rfl⟩ := exists_duad s
    have hA : ∀ w x : Fin n, (hwx : w ≠ x) → (w = p₀ ∨ w = p₁) → x ≠ p₀ → x ≠ p₁ →
        ∃ g : G, g • duad p₀ p₁ h01 = duad p₀ p₁ h01 ∧ g • duad p₀ p₂ h02 = duad w x hwx := by
      intro w x hwx hw hx0 hx1
      rcases hw with hw | hw
      · obtain ⟨g, g0, g1, g2⟩ := h3 w p₁ x (by rw [hw]; exact h01) hwx (Ne.symm hx1)
        exact ⟨g, smul_duad_eq _ _ (g0.trans hw) g1, smul_duad_eq _ _ g0 g2⟩
      · obtain ⟨g, g0, g1, g2⟩ := h3 w p₀ x (by rw [hw]; exact Ne.symm h01) hwx (Ne.symm hx0)
        exact ⟨g, (smul_duad_eq h01 (Ne.symm h01) (g0.trans hw) g1).trans (duad_comm _ _ _),
          smul_duad_eq _ _ g0 g2⟩
    by_cases hu : u = p₀ ∨ u = p₁
    · left
      have hv0 : v ≠ p₀ := by
        intro hv0
        rcases hu with hu | hu
        · exact huv (hu.trans hv0.symm)
        · exact hs ((duad_congr huv (Ne.symm h01) hu hv0).trans (duad_comm _ _ _))
      have hv1 : v ≠ p₁ := by
        intro hv1
        rcases hu with hu | hu
        · exact hs (duad_congr huv h01 hu hv1)
        · exact huv (hu.trans hv1.symm)
      exact hA u v huv hu hv0 hv1
    by_cases hv : v = p₀ ∨ v = p₁
    · left
      push Not at hu
      obtain ⟨g, hg1, hg2⟩ := hA v u (Ne.symm huv) hv hu.1 hu.2
      exact ⟨g, hg1, hg2.trans (duad_comm _ _ _)⟩
    · right
      push Not at hu hv
      obtain ⟨g, g0, g1, g2, g3⟩ := h4 p₀ p₁ u v h01 (Ne.symm hu.1) (Ne.symm hv.1)
        (Ne.symm hu.2) (Ne.symm hv.2) huv
      exact ⟨g, smul_duad_eq _ _ g0 g1, smul_duad_eq _ _ g2 g3⟩
  · obtain ⟨g, g0, g1, g2⟩ := h3 p₂ p₃ p₀ h23 (Ne.symm h02) (Ne.symm h03)
    exact ⟨g, (smul_duad_eq h02 (Ne.symm h02) g0 g2).trans (duad_comm _ _ _),
      smul_duad_eq _ _ g0 g1⟩
  · obtain ⟨g, g0, g1, g2, g3⟩ := h4 p₀ p₄ p₂ p₃ h04 h02 h03 (Ne.symm h24) (Ne.symm h34) h23
    obtain ⟨h, h0, h1, h2⟩ := h3 p₀ p₁ p₄ h01 h04 h14
    exact ⟨g, smul_duad_eq _ _ g2 g3, h, smul_duad_eq _ _ h0 h1,
      (smul_duad_eq h02 h04 h0 h2).trans (smul_duad_eq h01 h04 g0 g1).symm⟩

end Duads

end CFSG.Sporadic.Mathieu
