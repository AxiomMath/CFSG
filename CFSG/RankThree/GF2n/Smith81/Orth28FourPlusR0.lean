module

public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusAct

public section

namespace CFSG.RankThree.GF2n.Smith81.FourPlus

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open scoped commutatorElement

theorem perm_three_key : ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a * b = b * a →
    a = 1 ∨ b = 1 ∨ a = b := by decide

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_mem_Lgen_of_data (F : Data M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    ∃ x₀ ∈ X, x₀ ≠ 1 ∧ x₀ ∈ Lgen M (LB M Q B) := by
  have hcB := F.hc.ctx
  have H := hcB.hyp
  have hXH : X ≤ H0 M Z := (smith_1_12 hs).1
  have hX2 : ∀ w ∈ X, w * w = 1 := by
    intro w hw
    obtain ⟨g, hg⟩ := hs.conj
    have hw' : g⁻¹ * w * g ∈ Z := mem_conjSubgroup.mp (hg ▸ hw)
    have h1 := Z_sq H hw'
    have e : w * w = g * ((g⁻¹ * w * g) ^ 2) * g⁻¹ := by rw [pow_two]; group
    rw [e, h1]; group
  have hXcard : 4 ≤ Nat.card X := by
    obtain ⟨g, hg⟩ := hs.conj
    rw [hg, card_conjSubgroup]
    exact H.q4
  obtain ⟨y, hyX, hy1, hyx⟩ : ∃ y ∈ X, y ≠ 1 ∧ y ≠ x := by
    by_contra hcon
    push Not at hcon
    have hsub : (X : Set G) ⊆ {1, x} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, x} : Set G).ncard ≤ 2 := (Set.ncard_insert_le 1 {x}).trans (by simp)
    have h3 : Nat.card X = (X : Set G).ncard := Nat.card_coe_set_eq (X : Set G)
    omega
  have hxyX : x * y ∈ X := X.mul_mem hs.mem hyX
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hyx
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hs.x_sq
  have hcomm : x * y = y * x := by
    have h1 : (x * y) * (x * y) = 1 := hX2 _ hxyX
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hs.x_sq
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hX2 y hyX)
    have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hxi, hyi]
  set hx' : ↥(H0 M Z) := ⟨x, hXH hs.mem⟩ with hx'def
  set hy' : ↥(H0 M Z) := ⟨y, hXH hyX⟩ with hy'def
  have hx2 : hx' * hx' = 1 := Subtype.ext hs.x_sq
  have hy2 : hy' * hy' = 1 := Subtype.ext (hX2 y hyX)
  have hxy2 : (hx' * hy') * (hx' * hy') = 1 := Subtype.ext (hX2 _ hxyX)
  have hcomm' : hx' * hy' = hy' * hx' := Subtype.ext hcomm
  have key := perm_three_key (permHom F hx') (permHom F hy')
    (by rw [← map_mul, hx2, map_one]) (by rw [← map_mul, hy2, map_one])
    (by rw [← map_mul, ← map_mul, hcomm'])
  rcases key with h | h | h
  · exact ⟨x, hs.mem, hs.ne_one, mem_Lgen_of_permHom_eq_one F hx' h hx2⟩
  · exact ⟨y, hyX, hy1, mem_Lgen_of_permHom_eq_one F hy' h hy2⟩
  · refine ⟨x * y, hxyX, hxy1, mem_Lgen_of_permHom_eq_one F (hx' * hy') ?_ hxy2⟩
    rw [map_mul, h]
    have : permHom F hy' * permHom F hy' = 1 := by rw [← map_mul, hy2, map_one]
    exact this

end CFSG.RankThree.GF2n.Smith81.FourPlus

namespace CFSG.RankThree.GF2n.Smith81

theorem orthR0HypFour_of (hT : OrthTacitStatement) :
    OrthR0HypFourStatement := by
  intro G _ _ M Q Z B hc C h4 hTSP X x hs
  exact FourPlus.exists_mem_Lgen_of_data (FourPlus.Data.ofFrame hc (noA2_of_tacit hT hc) C h4 hTSP)
    hs

end CFSG.RankThree.GF2n.Smith81
