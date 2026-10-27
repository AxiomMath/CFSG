module

public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

namespace Q16

variable {G : Type*} [Group G]

@[expose] def sqSub (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ p ∈ P, x = p * p}

theorem sqSub_le (P : Subgroup G) : sqSub P ≤ P := by
  rw [sqSub, Subgroup.closure_le]
  rintro _ ⟨p, hp, rfl⟩
  exact P.mul_mem hp hp

theorem sqSub_mono {N P : Subgroup G} (h : N ≤ P) : sqSub N ≤ sqSub P :=
  Subgroup.closure_mono fun _ ⟨p, hp, hx⟩ => ⟨p, h hp, hx⟩

theorem sqSub_map {G' : Type*} [Group G'] (f : G →* G') (P : Subgroup G) :
    sqSub (P.map f) = (sqSub P).map f := by
  rw [sqSub, sqSub, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p * p, ⟨p, hp, rfl⟩, map_mul f p p⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨f p, ⟨p, hp, rfl⟩, map_mul f p p⟩

theorem relindex_sqSub_conj (P : Subgroup G) (g : G) :
    (sqSub (P.map (MulAut.conj g).toMonoidHom)).relIndex (P.map (MulAut.conj g).toMonoidHom) =
      (sqSub P).relIndex P := by
  rw [sqSub_map, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem relindex_sqSub_le_of_relindex_two [Finite G] {N P : Subgroup G} (hNP : N ≤ P)
    (h2 : N.relIndex P = 2) :
    (sqSub P).relIndex P ≤ 2 * (sqSub N).relIndex N := by
  have hpos : (sqSub N).relIndex (sqSub P) ≠ 0 :=
    (Subgroup.isFiniteRelIndex_of_finiteIndex (H := sqSub N)).relIndex_ne_zero
  calc (sqSub P).relIndex P
      ≤ (sqSub N).relIndex (sqSub P) * (sqSub P).relIndex P :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hpos)
    _ = (sqSub N).relIndex N * N.relIndex P := by
        rw [Subgroup.relIndex_mul_relIndex _ _ _ (sqSub_mono hNP) (sqSub_le P),
          Subgroup.relIndex_mul_relIndex _ _ _ (sqSub_le N) hNP]
    _ = 2 * (sqSub N).relIndex N := by rw [h2, mul_comm]

theorem card_frattini_quotient_le_relindex_sqSub [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) : Nat.card (Q ⧸ frattini Q) ≤ (sqSub Q).relIndex Q := by
  obtain ⟨-, -, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hmap : sqSub Q ≤ (frattini Q).map Q.subtype := by
    rw [sqSub, Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp⟩ * ⟨p, hp⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two]
    exact hpow _
  have hle : (sqSub Q).subgroupOf Q ≤ frattini Q :=
    (Subgroup.comap_mono hmap).trans
      (Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _).le
  exact Subgroup.index_antitone hle

theorem prod_dvd_of_le_five {d : ℕ} (hd : d ≤ 5) :
    ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) ∣ 9999360 := by
  interval_cases d <;> decide +kernel

theorem card_mulAut_frattini_quotient_dvd_9999360 {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hle : Nat.card (Q ⧸ frattini Q) ≤ 32) :
    Nat.card (MulAut (Q ⧸ frattini Q)) ∣ 9999360 := by
  obtain ⟨-, hcomm, hpow, -, d, hcard, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ
  have hd : d ≤ 5 := by
    rw [hcard, show (32 : ℕ) = 2 ^ 5 by norm_num] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hcomm.is_comm.comm a b) hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  exact prod_dvd_of_le_five hd

theorem le_two_of_prime_pow_dvd_9999360 {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ^ k ∣ 9999360) : k ≤ 2 := by
  by_contra hk
  have h3 : r ^ 3 ∣ 2 ^ 10 * 9765 := (pow_dvd_pow r (by omega)).trans h
  have hcop : Nat.Coprime (r ^ 3) (2 ^ 10) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hodd : r ^ 3 ∣ 9765 := hcop.dvd_of_dvd_mul_left h3
  have hle : r ^ 3 ≤ 9765 := Nat.le_of_dvd (by norm_num) hodd
  have hr21 : r ≤ 21 := by
    by_contra hgt
    have : 22 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  clear h h3 hle
  interval_cases r <;> first | omega | exact absurd hr (by decide)

theorem elemAbelian_oddPrime_rank_le_two_of_relindex_sqSub_le [Finite G]
    (hchar : CFSG.Open.IsCharTwoType G)
    (h : ∀ P : Subgroup G, IsPGroup 2 P → (sqSub P).relIndex P ≤ 32) {M : Subgroup G}
    (hM : CFSG.Open.IsTwoLocal M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G}
    (hEM : E ≤ M) (hE : CFSG.Open.IsElemAbelian r E) {k : ℕ} (hk : Nat.card E = r ^ k) :
    k ≤ 2 := by
  have hQ : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.RankThree.PartOne.SectionalRank.isPGroup_pCoreOf 2 M
  obtain ⟨ψ, hψ⟩ :=
    CFSG.RankThree.PartOne.SectionalRank.exists_injective_hom_mulAut_frattini_quotient hQ
      (hEM.trans (CFSG.RankThree.PartOne.SectionalRank.le_normalizer_pCoreOf 2 M)) hr hr2
      (fun x hx => hE.2 x hx)
      fun x hx hc => hchar M hM ⟨hEM hx, Subgroup.mem_centralizer_iff.2 hc⟩
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  rw [hk] at hdvd
  exact le_two_of_prime_pow_dvd_9999360 hr hr2 (hdvd.trans
    (card_mulAut_frattini_quotient_dvd_9999360 hQ
      ((card_frattini_quotient_le_relindex_sqSub hQ).trans (h _ hQ))))

theorem evenRank_le_two_of_relindex_sqSub_le [Finite G] (hchar : CFSG.Open.IsCharTwoType G)
    (h : ∀ P : Subgroup G, IsPGroup 2 P → (sqSub P).relIndex P ≤ 32) :
    CFSG.Open.evenRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨p, H, hp, hp2, hH, rfl⟩
  refine csSup_le' ?_
  rintro j ⟨E, hEH, hE, hj⟩
  exact elemAbelian_oddPrime_rank_le_two_of_relindex_sqSub_le hchar h hH hp hp2 hEH hE hj

end Q16

end CFSG.RankThree.PartTwo.Sec19.SolEven
