module

public import CFSG.RankThree.PartOne.FOCD.RankInner
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne

theorem card_le_sq_of_exponent {p e : ℕ} (hp : p.Prime)
    (H : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e)))) (hH : ∀ h ∈ H, h ^ p = 1) :
    Nat.card H ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have : NeZero (p ^ e) := ⟨hpe⟩
  let _ : Fintype (Multiplicative (ZMod (p ^ e))) := Fintype.ofFinite _
  have hcyc : ∀ n : ℕ, 0 < n → Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ n = 1} ≤ n := by
    intro n hn
    have := IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod (p ^ e))) hn
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact this
  let ι : H → (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) := fun h i =>
    ⟨(h : Fin 2 → Multiplicative (ZMod (p ^ e))) i, by
      have := congrFun (hH h h.2) i
      simpa using this⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have := congrFun hxy i
    exact congrArg Subtype.val this
  calc Nat.card H ≤ Nat.card (Fin 2 → {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) :=
        Nat.card_le_card_of_injective ι hι
    _ = (Nat.card {a : Multiplicative (ZMod (p ^ e)) // a ^ p = 1}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    _ ≤ p ^ 2 := Nat.pow_le_pow_left (hcyc p hp.pos) 2

variable {T : Type} [Group T] [Finite T]

theorem pRankLeTwo_of_sylowShape {p e : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e T) : PRankLeTwo p T := by
  intro R hRp hRc
  have : Fact p.Prime := ⟨hp⟩
  have hRP : IsPGroup p R := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hRp g.1 g.2))
    rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
    · exact ⟨0, by rw [h2]; simp⟩
    · exact ⟨1, by rw [h2]; simp⟩
  obtain ⟨S, hRS⟩ := hRP.exists_le_sylow
  obtain ⟨φ⟩ := h (S : Subgroup T) S.isPGroup' (Sylow.not_dvd_index S)
  let R' : Subgroup ↥(S : Subgroup T) := R.subgroupOf S
  have hcard : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRS).toEquiv
  have hR'p : ∀ r ∈ R', r ^ p = 1 := by
    intro r hr
    exact Subtype.ext (by simpa using hRp r.1 hr)
  let H : Subgroup (Fin 2 → Multiplicative (ZMod (p ^ e))) := R'.map φ.toMonoidHom
  have hHcard : Nat.card H = Nat.card R' :=
    Subgroup.card_map_of_injective φ.injective
  have hHp : ∀ h ∈ H, h ^ p = 1 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_pow, hR'p r hr, map_one]
  have := card_le_sq_of_exponent hp H hHp
  rw [hHcard, hcard] at this
  exact this

theorem pRankLeTwo_of_not_dvd {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ Nat.card T) : PRankLeTwo p T := by
  intro R hRp hRc
  have : Fact p.Prime := ⟨hp⟩
  have hRP : IsPGroup p R := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hRp g.1 g.2))
    rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
    · exact ⟨0, by rw [h2]; simp⟩
    · exact ⟨1, by rw [h2]; simp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hRP
  have hdvd : Nat.card R ∣ Nat.card T := Subgroup.card_subgroup_dvd_card R
  rw [hj] at hdvd
  by_cases hj0 : j = 0
  · rw [hj, hj0]
    simpa using Nat.one_le_pow 2 p hp.pos
  · exact absurd ((dvd_pow_self p hj0).trans hdvd) h

theorem pRankLeTwo_of_pRank_le_one {p : ℕ} (hp : p.Prime) (h : CFSG.pRank p T ≤ 1) :
    PRankLeTwo p T := by
  intro R hRp hRc
  have : Fact p.Prime := ⟨hp⟩
  have hRP : IsPGroup p R := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hRp g.1 g.2))
    rcases (Nat.dvd_prime hp).1 h1 with h2 | h2
    · exact ⟨0, by rw [h2]; simp⟩
    · exact ⟨1, by rw [h2]; simp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hRP
  have hel : IsElementaryAbelian p R :=
    { is_comm := ⟨fun a b => Subtype.ext (hRc a.1 a.2 b.1 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun g =>
        Subtype.ext (by simpa using hRp g.1 g.2)) }
  have hmem : j ∈ {r : ℕ | ∃ A : Subgroup T, IsElementaryAbelian p A ∧ Nat.card A = p ^ r} :=
    ⟨R, hel, hj⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup T, IsElementaryAbelian p A ∧ Nat.card A = p ^ r} := by
    refine ⟨Nat.card T, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : Nat.card A ≤ Nat.card T := Nat.card_le_card_of_injective _ A.subtype_injective
    rw [hA] at h1
    exact (Nat.lt_pow_self hp.one_lt).le.trans h1
  have hj1 : j ≤ 1 := (le_csSup hbdd hmem).trans h
  rw [hj]
  calc p ^ j ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.RankThree.PartOne.FOCD
