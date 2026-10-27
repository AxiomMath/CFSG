module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFrames
public import CFSG.LieType.SeitzGeneration.ExcTorusRankF4
public import CFSG.LieType.SeitzGeneration.ExcTorusRankE7
public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.StandardType

namespace PRankBounds

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

section Arith

variable {p q : ℕ}

theorem three_le_orderOf (hp : p.Prime) (hpq : ¬ p ∣ q) (hq : 1 ≤ q) (h1 : ¬ p ∣ q - 1)
    (h2 : ¬ p ∣ q + 1) : 3 ≤ orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have h0 := orderOf_natCast_ne_zero hp hpq
  have hne1 : orderOf (q : ZMod p) ≠ 1 := fun h => h1 (by
    have hx : (q : ZMod p) = 1 := orderOf_eq_one_iff.mp h
    have : ((q - 1 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hq, hx, Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp this)
  have hne2 : orderOf (q : ZMod p) ≠ 2 := fun h => h2 (by
    have hx2 : (q : ZMod p) ^ 2 = 1 := h ▸ pow_orderOf_eq_one _
    have hx1 : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr fun hx => hne1 (orderOf_eq_one_iff.mpr hx)
    have hm : ((q : ZMod p) - 1) * ((q : ZMod p) + 1) = 0 := by linear_combination hx2
    have : ((q + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      exact (mul_eq_zero.mp hm).resolve_left hx1
    exact (ZMod.natCast_eq_zero_iff _ _).mp this)
  omega

theorem dvd_sq_add_add_one_of_orderOf (hp : p.Prime) (he : orderOf (q : ZMod p) = 3) :
    p ∣ q ^ 2 + q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h3 : (q : ZMod p) ^ 3 = 1 := he ▸ pow_orderOf_eq_one _
  have h1 : (q : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [← orderOf_eq_one_iff] at h
    omega
  have hm : ((q : ZMod p) - 1) * ((q : ZMod p) ^ 2 + q + 1) = 0 := by linear_combination h3
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  exact (mul_eq_zero.mp hm).resolve_left h1

theorem dvd_sq_add_one_of_orderOf (hp : p.Prime) (he : orderOf (q : ZMod p) = 4) :
    p ∣ q ^ 2 + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h4 : (q : ZMod p) ^ 4 = 1 := he ▸ pow_orderOf_eq_one _
  have h2 : (q : ZMod p) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    exact absurd this (by norm_num)
  have hm : ((q : ZMod p) ^ 2 - 1) * ((q : ZMod p) ^ 2 + 1) = 0 := by linear_combination h4
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  exact (mul_eq_zero.mp hm).resolve_left h2

theorem dvd_sq_sub_add_one_of_orderOf (hp : p.Prime) (he : orderOf (q : ZMod p) = 6) :
    p ∣ q ^ 2 - q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h6 : (q : ZMod p) ^ 6 = 1 := he ▸ pow_orderOf_eq_one _
  have h3 : (q : ZMod p) ^ 3 - 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    exact absurd this (by norm_num)
  have h1 : (q : ZMod p) + 1 ≠ 0 := fun h => by
    have hsq : (q : ZMod p) ^ 2 = 1 := by linear_combination ((q : ZMod p) - 1) * h
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [he] at this
    exact absurd this (by norm_num)
  have hm : ((q : ZMod p) ^ 3 - 1) * (((q : ZMod p) + 1) * ((q : ZMod p) ^ 2 - q + 1)) = 0 := by
    linear_combination h6
  have hz : (q : ZMod p) ^ 2 - q + 1 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left h3)).resolve_left h1
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow (by norm_num) q), Nat.cast_pow, Nat.cast_one]
  exact hz

theorem lt_pow_four (hp : p.Prime) : p < p ^ 4 := by
  have := Nat.pow_lt_pow_right hp.one_lt (show 1 < 4 by norm_num)
  simpa using this

theorem not_dvd_card_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

end Arith

section Tori


theorem sylowTorus_of_blocks_of_lt {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M) (ds : List ℕ) {e : ℕ}
    (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod) (hpow : M ^ e = 1)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (he0 : e ≠ 0)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3])
    (hQ : ∀ d ∈ degreesE τ, e ∣ d → d / e ∈ [1, 2, 3, 4, 6])
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    SylowTorus (adjointGroup τ K) p (ds.count e) := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he he0
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have h5 : 5 ≤ p := five_le_of_three_lt hp hp3
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    have hd3 := hso d hd.1 hde
    refine not_dvd_cyclotomic_eval_of_ne hp he hde (fun hdvd => ?_) hpa
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd3
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      (p ^ (Nat.card K ^ e - 1).factorization p) ^ ds.count e := by
    rw [ordProj_card_adjointGroup_E (by rcases hτ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hp
      hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2 he (degreesE τ)
      (fun d hd hed => ⟨(hcard d hd).ne', not_dvd_small hp h5 (hQ d hd hed)⟩), hcount]
  exact sylowTorus_untwisted d hτ K hp hp3 hpq hM _ he0 hpow hn hchar' he hR hord

theorem sylowTorus_E7_three' (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) : SylowTorus (adjointGroup Tag.E7 K) p 3 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  exact sylowTorus_of_blocks_of_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly e7Three_pow he
    (by norm_num) (by decide) (by decide) (by decide)

theorem sylowTorus_E7_six' (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) : SylowTorus (adjointGroup Tag.E7 K) p 3 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  exact sylowTorus_of_blocks_of_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly e7Six_pow he
    (by norm_num) (by decide) (by decide) (by decide)

end Tori

end PRankBounds

section Inputs

open CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration PRankBounds


theorem ggExcNonsplitRankInput_F4 : GGExcNonsplitRankInput .F4 := by
  intro K _ _ _ p hp hp2 h1 h2 E hE
  have hpq := not_dvd_card_of_charTwo (K := K) hp hp2
  have he3 := three_le_orderOf hp hpq Nat.card_pos h1 h2
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at he3
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hsq : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases hcnt : degCount Tag.F4 e ≤ 1
  · exact (rankLE1_F4 K hp hpq (he ▸ hcnt) E hE).trans_lt (lt_pow_four hp)
  · have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
    interval_cases e <;> first | omega | exact absurd hcnt (by decide) | skip
    · exact ((sylowTorus_F4_three K hp (by omega) (dvd_sq_add_add_one_of_orderOf hp he)).rank_le
        hp hE).trans_lt hsq
    · exact ((sylowTorus_F4_four K hp (by omega) (dvd_sq_add_one_of_orderOf hp he)).rank_le
        hp hE).trans_lt hsq
    · exact ((sylowTorus_F4_six K hp (by omega) (dvd_sq_sub_add_one_of_orderOf hp he)).rank_le
        hp hE).trans_lt hsq

theorem ggExcNonsplitRankInput_E7 : GGExcNonsplitRankInput .E7 := by
  intro K _ _ _ p hp hp2 h1 h2 E hE
  have hpq := not_dvd_card_of_charTwo (K := K) hp hp2
  have he3 := three_le_orderOf hp hpq Nat.card_pos h1 h2
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at he3
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hsq : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hcu : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  by_cases hcnt : degCount Tag.E7 e ≤ 1
  · exact (rankLE1_E7 K hp hpq (he ▸ hcnt) E hE).trans_lt (lt_pow_four hp)
  · have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
    interval_cases e <;> first | omega | exact absurd hcnt (by decide) | skip
    · exact ((sylowTorus_E7_three' K hp he).rank_le hp hE).trans_lt hcu
    · exact ((sylowTorus_E7_four K hp he).rank_le hp hE).trans_lt hsq
    · exact ((sylowTorus_E7_six' K hp he).rank_le hp hE).trans_lt hcu

end Inputs

end CFSG.StandardType
