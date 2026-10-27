module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.Adapters.StatedPSLTwoSeven
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic11
public import CFSG.RankThree.PartOne.Q1327T.Perm3

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Sigma3

variable {G : Type*} [Group G]

theorem card_closure_dihedral {a t : G} (ha : orderOf a = 3) (ht : t * t = 1)
    (hc : t * a * t⁻¹ = a⁻¹) : Nat.card ↥(Subgroup.closure ({a, t} : Set G)) = 6 := by
  have h := CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.SigmaDihedral.card_zpowers_sup_zpowers
    (m := 0) (by simpa using ha) ht hc
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure, h]
  norm_num

theorem nonempty_perm_three_closure {a t : G} (ha : orderOf a = 3) (ht : orderOf t = 2)
    (hc : t * a * t⁻¹ = a⁻¹) :
    Nonempty (↥(Subgroup.closure ({a, t} : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hcard := card_closure_dihedral ha ht2 hc
  haveI : Finite ↥(Subgroup.closure ({a, t} : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have haH : a ∈ Subgroup.closure ({a, t} : Set G) := Subgroup.subset_closure (by simp)
  have htH : t ∈ Subgroup.closure ({a, t} : Set G) := Subgroup.subset_closure (by simp)
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three (⟨a, haH⟩ : ↥(Subgroup.closure
    ({a, t} : Set G))) ⟨t, htH⟩ ?_ ?_ ?_ ?_ ?_ hcard
  · apply Subtype.ext
    simpa using (by rw [← ha]; exact pow_orderOf_eq_one a : a ^ 3 = 1)
  · intro h
    have : a = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ha
    omega
  · exact Subtype.ext ht2
  · intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    omega
  · exact Subtype.ext hc

end Sigma3

section L32

abbrev G3 := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

def a0 : G3 := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

theorem a0_cube : a0 ^ 3 = 1 := by decide +kernel

theorem a0_ne_one : a0 ≠ 1 := by decide +kernel

theorem card_G3 : Nat.card G3 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_filter_a0 :
    (Finset.univ.filter (fun g : G3 => g * a0 * g⁻¹ = a0 ∨ g * a0 * g⁻¹ = a0⁻¹)).card = 6 := by
  decide +kernel

variable {G : Type} [Group G]

theorem mem_nor_zpowers_iff {a g : G} (ha : orderOf a = 3) :
    g ∈ Nor (Subgroup.zpowers a) ↔ g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
  constructor
  · intro hg
    have h1 : g * a * g⁻¹ ∈ Subgroup.zpowers a :=
      (Subgroup.mem_normalizer_iff.1 hg a).1 (Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    have hne : a ≠ 1 := by
      intro h; rw [h, orderOf_one] at ha; omega
    have hk' : a ^ (k % 3) = g * a * g⁻¹ := by
      rw [← hk]
      have := zpow_mod_orderOf a k
      rw [ha] at this
      exact_mod_cast this
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · exfalso
      rw [h, zpow_zero] at hk'
      apply hne
      have := congrArg (fun x => g⁻¹ * x * g) hk'
      simpa [mul_assoc] using this.symm
    · left
      rw [h, zpow_one] at hk'
      exact hk'.symm
    · right
      rw [h] at hk'
      rw [← hk']
      have : a ^ (2 : ℤ) = a⁻¹ := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, eq_inv_iff_mul_eq_one,
          ← pow_succ]
        exact ha3
      rw [this]
  · intro h
    simpa using CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.SigmaDihedral.mem_normalizer_zpowers_pow
      (h := a) (g := g) h 1

theorem card_nor_zpowers_a0 : Nat.card ↥(Nor (Subgroup.zpowers a0)) = 6 := by
  have ha : orderOf a0 = 3 := orderOf_eq_prime a0_cube a0_ne_one
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun g => mem_nor_zpowers_iff ha)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert card_filter_a0

theorem card_nor_conjBy (k : G) (H : Subgroup G) :
    Nat.card ↥(Nor (conjBy k H)) = Nat.card ↥(Nor H) := by
  have h : (Nor H).map (MulAut.conj k).toMonoidHom = Nor (conjBy k H) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.conj k)
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem factorization_168 : (168 : ℕ).factorization 3 = 1 := by
  rw [Nat.factorization_def _ Nat.prime_three]
  decide +kernel

theorem card_nor_of_card_three {P : Subgroup G3} (hP : Nat.card P = 3) :
    Nat.card ↥(Nor P) = 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h168 : Nat.card (⊤ : Subgroup G3) = 168 := by rw [Subgroup.card_top]; exact card_G3
  have hS : ∀ Q : Subgroup G3, Nat.card Q = 3 → IsSylowOf 3 Q ⊤ := fun Q hQ =>
    isSylowOf_of_card_p le_top (by rw [hQ, h168, factorization_168]; norm_num)
  have ha : orderOf a0 = 3 := orderOf_eq_prime a0_cube a0_ne_one
  obtain ⟨k, -, hk⟩ := exists_conjBy_eq_sylowOf (hS P hP)
    (hS (Subgroup.zpowers a0) (by rw [Nat.card_zpowers, ha]))
  rw [← hk, card_nor_conjBy, card_nor_zpowers_a0]

theorem le_nor_of_card_six {P A : Subgroup G} [Finite G] (hPA : P ≤ A) (hP : Nat.card P = 3)
    (hA : Nat.card A = 6) : A ≤ Nor P := by
  have hidx : (P.subgroupOf A).index = 2 := by
    have h := Subgroup.card_mul_index (P.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv, hP, hA] at h
    omega
  haveI : (P.subgroupOf A).Normal := Subgroup.normal_of_index_eq_two hidx
  intro x hx
  refine mem_nor_of_forall fun y hy => ?_
  have := (inferInstance : (P.subgroupOf A).Normal).conj_mem ⟨y, hPA hy⟩ hy ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

theorem g3_exists_conj_of_card_six {A B : Subgroup G3} (hA : Nat.card A = 6)
    (hB : Nat.card B = 6) : ∃ g : G3, conjBy g A = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h168 : Nat.card (⊤ : Subgroup G3) = 168 := by rw [Subgroup.card_top]; exact card_G3
  have hS : ∀ Q : Subgroup G3, Nat.card Q = 3 → IsSylowOf 3 Q ⊤ := fun Q hQ =>
    isSylowOf_of_card_p le_top (by rw [hQ, h168, factorization_168]; norm_num)
  have hex : ∀ C : Subgroup G3, Nat.card C = 6 → ∃ c ∈ C, orderOf c = 3 := by
    intro C hC
    haveI : Finite ↥C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
    obtain ⟨c, hc⟩ := @exists_prime_orderOf_dvd_card' ↥C _ _ 3 ⟨Nat.prime_three⟩
      (by rw [hC]; norm_num)
    exact ⟨c.1, c.2, by rw [Subgroup.orderOf_coe]; exact hc⟩
  obtain ⟨a, haA, ha⟩ := hex A hA
  obtain ⟨b, hbB, hb⟩ := hex B hB
  have hPa : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
  have hPb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  obtain ⟨k, -, hk⟩ := exists_conjBy_eq_sylowOf (hS _ hPa) (hS _ hPb)
  have hB'6 : Nat.card ↥(conjBy k B) = 6 := by rw [card_conjBy, hB]
  have hPaB' : Subgroup.zpowers a ≤ conjBy k B := by
    rw [← hk]
    exact Subgroup.map_mono (Subgroup.zpowers_le.2 hbB)
  have hPaA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 haA
  have hA' := le_nor_of_card_six hPaA hPa hA
  have hB'' := le_nor_of_card_six hPaB' hPa hB'6
  have hN := card_nor_of_card_three hPa
  have hAeq : A = Nor (Subgroup.zpowers a) :=
    Subgroup.eq_of_le_of_card_ge hA' (by rw [hN, hA])
  have hBeq : conjBy k B = Nor (Subgroup.zpowers a) :=
    Subgroup.eq_of_le_of_card_ge hB'' (by rw [hN, hB'6])
  refine ⟨k⁻¹, ?_⟩
  have h1 : conjBy k⁻¹ (conjBy k B) = B := by
    ext x
    simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa [mul_assoc] using hz
    · intro hx
      exact ⟨k * x * k⁻¹, ⟨x, hx, rfl⟩, by simp [mul_assoc]⟩
  rw [← h1, hBeq, ← hAeq]

theorem nonempty_equiv_G3_of_isLnq {G : Type} [Group G] {X : Subgroup G} (hX : IsLnq 3 2 1 X) :
    Nonempty (↥X ≃* G3) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_sl_three_two_of_psl_two_seven
    (CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two hX)

theorem exists_conj_of_card_six {G : Type} [Group G] [Finite G] {X A B : Subgroup G}
    (hX : IsLnq 3 2 1 X)
    (hAX : A ≤ X) (hBX : B ≤ X) (hA : Nat.card A = 6) (hB : Nat.card B = 6) :
    ∃ g ∈ X, conjBy g A = B := by
  obtain ⟨e⟩ := nonempty_equiv_G3_of_isLnq hX
  let A' : Subgroup G3 := (A.subgroupOf X).map e.toMonoidHom
  let B' : Subgroup G3 := (B.subgroupOf X).map e.toMonoidHom
  have hA' : Nat.card A' = 6 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hA]
  have hB' : Nat.card B' = 6 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv, hB]
  obtain ⟨g', hg'⟩ := g3_exists_conj_of_card_six hA' hB'
  set gX : ↥X := e.symm g' with hgX
  refine ⟨(gX : G), gX.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : e ⟨x, hAX hx⟩ ∈ A' := ⟨⟨x, hAX hx⟩, hx, rfl⟩
    have h1 : g' * e ⟨x, hAX hx⟩ * g'⁻¹ ∈ B' := by
      rw [← hg']
      exact ⟨e ⟨x, hAX hx⟩, hx', by simp [MulAut.conj_apply]⟩
    obtain ⟨b, hb, hbe⟩ := h1
    have hbe' : e b = g' * e ⟨x, hAX hx⟩ * g'⁻¹ := hbe
    have h2 : b = gX * ⟨x, hAX hx⟩ * gX⁻¹ := by
      apply e.injective
      rw [hbe']
      simp [hgX]
    have h3 : (b : G) ∈ B := hb
    rw [h2] at h3
    simpa [MulAut.conj_apply] using h3
  · rw [card_conjBy, hA, hB]

end L32

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
