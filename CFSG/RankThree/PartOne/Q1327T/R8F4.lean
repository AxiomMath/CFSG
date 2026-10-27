module

public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import CFSG.RankThree.PartOne.KF.ClsExcE
public import Certificates.Certificate271000

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

theorem closure_pair_comm {G : Type*} [Group G] {A B : G} (hAB : A * B = B * A) :
    ∀ x ∈ Subgroup.closure ({A, B} : Set G), ∀ y ∈ Subgroup.closure ({A, B} : Set G),
      x * y = y * x := by
  have hcomm : ∀ x ∈ ({A, B} : Set G), ∀ y ∈ ({A, B} : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hAB
    · exact hAB.symm
    · rfl
  have h1 : Subgroup.closure ({A, B} : Set G) ≤ Subgroup.centralizer ({A, B} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  have h2 : Subgroup.closure ({A, B} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({A, B} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (h1 hy) x hx).symm
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.1 (h2 hy) x hx

theorem inv_conj_closure_pair {G : Type*} [Group G] {A B g : G} (hAB : A * B = B * A)
    (hA : g * A * g⁻¹ = A⁻¹) (hB : g * B * g⁻¹ = B⁻¹) :
    ∀ e ∈ Subgroup.closure ({A, B} : Set G), g * e * g⁻¹ = e⁻¹ := by
  intro e he
  induction he using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hA
    · exact hB
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := closure_pair_comm hAB x hx y hy
    calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
      _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
      _ = (x * y)⁻¹ := by rw [hc]
  | inv x hx ih =>
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [ih]

theorem exists_inv_of_conj_map {G : Type*} [Group G] {E₀ E₁ : Subgroup G} (c g : G)
    (hc : E₁.map (MulAut.conj c).toMonoidHom = E₀) (h : ∀ e ∈ E₀, g * e * g⁻¹ = e⁻¹) :
    ∃ g' : G, ∀ e ∈ E₁, g' * e * g'⁻¹ = e⁻¹ := by
  refine ⟨c⁻¹ * g * c, fun e he => ?_⟩
  have hmem : c * e * c⁻¹ ∈ E₀ := by
    rw [← hc]
    exact Subgroup.mem_map.2 ⟨e, he, by simp [MulAut.conj_apply]⟩
  have key := h _ hmem
  calc c⁻¹ * g * c * e * (c⁻¹ * g * c)⁻¹ = c⁻¹ * (g * (c * e * c⁻¹) * g⁻¹) * c := by group
    _ = c⁻¹ * (c * e * c⁻¹)⁻¹ * c := by rw [key]
    _ = e⁻¹ := by group

theorem two_pow_mod_seven (g : ℕ) : 2 ^ g % 7 = 1 ∨ 2 ^ g % 7 = 2 ∨ 2 ^ g % 7 = 4 := by
  induction g with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem seven_not_dvd_two_pow_add_one (g : ℕ) : ¬ 7 ∣ 2 ^ g + 1 := by
  have := two_pow_mod_seven g
  omega

end CFSG.RankThree.PartOne.Q1327T.R8

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.SEITZX
  CFSG.LieType.Simplicity.TitsBits
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Plane

theorem exists_inv_of_plane_five {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : ¬ 5 ^ 3 ∣ Nat.card (adjointGroup ReeTag.F4.tag K))
    {E : Subgroup (adjointGroup ReeTag.F4.tag K)} (hE : Nat.card E = 5 ^ 2) :
    ∃ g : adjointGroup ReeTag.F4.tag K, ∀ e ∈ E, g * e * g⁻¹ = e⁻¹ := by
  have hc := (Certificates.certificate14997 : cert5.check = true ∧ cert7.check = true).1
  obtain ⟨hAp, hBp, hAB, hA1, hBA, -, -⟩ := PlaneCert.facts (K := K) cert5 hc
  have hchk := (Certificates.certificate271000 : F4TwoInvCheck)
  set A := evalG K (wordOfCodes cert5.wa) with hAdef
  set B := evalG K (wordOfCodes cert5.wb) with hBdef
  set g₀ := evalG K (wordOfCodes invWordG) with hg₀def
  have hA5 : A ^ 5 = 1 := hAp
  have hB5 : B ^ 5 = 1 := hBp
  have hrev : wordOfCodes invWordG.reverse = (wordOfCodes invWordG).reverse := by
    simp [wordOfCodes, List.map_reverse]
  have hinv : g₀⁻¹ = evalG K (wordOfCodes invWordG.reverse) := by
    rw [hg₀def, evalG_inv, hrev]
  have h0 := hasBits_codes (K := K) invWordG
  have h1 := hasBits_codes (K := K) invWordG.reverse
  have hAb := hasBits_codes (K := K) cert5.wa
  have hBb := hasBits_codes (K := K) cert5.wb
  have hgA : g₀ * A * g₀⁻¹ = A⁻¹ := by
    have h4 : g₀ * A * g₀⁻¹ = A ^ 4 := by
      rw [hinv]
      exact (((h0.mul hAb).mul h1).eq_iff (hasBits_pow hAb 4)).2 hchk.1
    rw [h4]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hA5)
  have hgB : g₀ * B * g₀⁻¹ = B⁻¹ := by
    have h4 : g₀ * B * g₀⁻¹ = B ^ 4 := by
      rw [hinv]
      exact (((h0.mul hBb).mul h1).eq_iff (hasBits_pow hBb 4)).2 hchk.2
    rw [h4]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hB5)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hE₀ : Nat.card (Subgroup.closure ({A, B} : Set (adjointGroup ReeTag.F4.tag K))) =
      5 ^ 2 := card_closure_pair (p := 5) hAp hBp hAB hA1 hBA h3
  obtain ⟨c, hcE⟩ := exists_conj_eq_of_card_eq (p := 5) h3 hE₀ hE
  exact R8.exists_inv_of_conj_map c g₀ hcE (R8.inv_conj_closure_pair hAB hgA hgB)

end Plane

section Leaf

theorem row8U3At_leaf9_six
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf9 6) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hq1, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hLie : Models.LieModel (Q ⧸ Subgroup.center Q) .F4 0 2 q.exponent := by
    obtain ⟨hv, ⟨e0⟩⟩ := hiso
    exact ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      Or.inr ⟨rfl, ⟨.F4 q, hv⟩, ⟨hq2, rfl⟩, ⟨e0⟩⟩⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p hLie fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) (hd.trans (KFU.card_multiplier_F4 (f := q.exponent)))
    omega
  refine h.concl_of_inv hZ ?_
  obtain ⟨X, _, _, hX2, ⟨θ⟩⟩ := exists_adjointF4_two_model hq2 hq1 hiso
  have : CharP X 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 1) (le_refl 1) (by simpa using hX2)
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* adjointGroup ReeTag.F4.tag X := ce.trans θ
  refine exists_inv_of_equiv eQ ?_
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  have hG : Nat.card (adjointGroup ReeTag.F4.tag X) = 3311126603366400 := by
    have hX3 := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := X)
    rw [hX2] at hX3
    exact hX3.trans (by norm_num [CFSG.Open.ordF4])
  have hp2N : p ^ 2 ∣ 3311126603366400 := by
    rw [← hG, ← hEcard]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 : ¬ 5 ^ 3 ∣ Nat.card (adjointGroup ReeTag.F4.tag X) := by
    rw [hG]
    decide
  rcases prime_eq_five_or_seven hp hp5 hp2N with rfl | rfl
  · exact exists_inv_of_plane_five h3 hEcard
  · exact absurd h.p_dvd (R8.seven_not_dvd_two_pow_add_one g)

end Leaf

end CFSG.RankThree.PartOne.Q1327T
