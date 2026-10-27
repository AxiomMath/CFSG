module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgIso
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowCard
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowR27

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


theorem sixteen_dvd_of_odd {q : ℕ} (hq : Odd q) :
    16 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) ∧ 16 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have hq1 : 1 ≤ q := hq.pos
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have h8 : 8 * (q : ZMod 16) = 8 := by
    obtain ⟨m, rfl⟩ := hq
    push_cast
    ring_nf
    have : (16 : ZMod 16) = 0 := rfl
    calc (8 : ZMod 16) + (m : ZMod 16) * 16 = 8 + (m : ZMod 16) * 0 := by rw [this]
      _ = 8 := by ring
  have key : ∀ x : ZMod 16, 8 * x = 8 →
      (x ^ 2 - 1) * (x ^ 3 - 1) = 0 ∧ (x ^ 2 - 1) * (x ^ 3 + 1) = 0 := by decide
  obtain ⟨k1, k2⟩ := key _ h8
  refine ⟨(ZMod.natCast_eq_zero_iff _ _).mp ?_, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  · push_cast [Nat.cast_sub h2, Nat.cast_sub h3]
    exact k1
  · push_cast [Nat.cast_sub h2]
    exact k2

theorem sixteen_dvd_card_of_isoLThreePi {T : Type} [Group T] [Finite T] [Group.IsPerfect T]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (h : IsoLThreePi T p e) : 16 ∣ Nat.card T := by
  have hp : p.Prime := Fact.out
  have h2520 := le_card_of_isoLThreePi he h
  have hcop : ∀ g : ℕ, g ∣ 3 → Nat.Coprime 16 g := fun g hg => by
    rcases (Nat.dvd_prime Nat.prime_three).mp hg with rfl | rfl <;> norm_num
  have h2pow : p = 2 → 2 ≤ e → 16 ∣ (p ^ e) ^ 3 := fun hp2 he2 => by
    subst hp2
    rw [← pow_mul]
    exact (show 16 = 2 ^ 4 by norm_num) ▸ pow_dvd_pow 2 (by omega)
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have h16 : 16 ∣ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
      rcases Nat.even_or_odd (p ^ e) with hev | hodd
      · have hp2 : p = 2 := by
          have := (Nat.even_pow.mp hev).1
          exact (Nat.Prime.even_iff hp).mp this
        subst hp2
        have he2 : 2 ≤ e := by
          by_contra h1
          have : e = 1 := by omega
          subst this
          norm_num at hq
        exact Dvd.dvd.mul_right (h2pow rfl he2) _
      · exact Dvd.dvd.mul_left (sixteen_dvd_of_odd hodd).1 _
    rw [← hc] at h16
    exact (hcop _ (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right h16
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    have h16 : 16 ∣ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
      rcases Nat.even_or_odd (p ^ e) with hev | hodd
      · have hp2 : p = 2 := by
          have := (Nat.even_pow.mp hev).1
          exact (Nat.Prime.even_iff hp).mp this
        subst hp2
        have he2 : 2 ≤ e := by
          by_contra h1
          have he1 : e = 1 := by omega
          subst he1
          have hg : Nat.gcd 3 (2 ^ 1 + 1) = 3 := by norm_num
          rw [hg] at hc
          omega
        exact Dvd.dvd.mul_right (h2pow rfl he2) _
      · exact Dvd.dvd.mul_left (sixteen_dvd_of_odd hodd).2 _
    rw [← hc] at h16
    exact (hcop _ (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right h16

theorem sixteen_or_five_dvd_card_of_isType429
    {T : Type} [Group T] [Finite T]
    [Group.IsPerfect T] (h : IsType429 T) : 16 ∣ Nat.card T ∨ 5 ∣ Nat.card T := by
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact Or.inl (sixteen_dvd_card_of_isoLThreePi he h)
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
    right
    decide
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
    norm_num
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
    norm_num
  · obtain ⟨φ⟩ := h
    rw [Nat.card_congr φ.toEquiv, CFSG.Sporadic.J2.card_J2]
    norm_num

theorem noCfgS429_of_not_dvd_sixteen_five
    {S : Type} [Group S] [Finite S]
    (h16 : ¬ 16 ∣ Nat.card S) (h5 : ¬ 5 ∣ Nat.card S) : NoCfgS429 S := by
  intro A σ K hc
  haveI : Group.IsPerfect K := hc.isPerfect
  have hdvd : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card S :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K)
  rcases sixteen_or_five_dvd_card_of_isType429 hc.isType with h | h
  · exact h16 (h.trans hdvd)
  · exact h5 (h.trans hdvd)

theorem rowSOf429_three :
    ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
      RowSOf429 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr
  obtain ⟨f⟩ := CFSG.AGLEmbedding.ReeModel.nonempty_reeGamma_equiv 1 le_rfl hr
  have hcard : Nat.card RonanK432.Ree27 = 10073444472 := by
    rw [CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq RonanK432.card_ree27Field]
    norm_num
  have hno : NoCfgS429 RonanK432.Ree27 :=
    noCfgS429_of_not_dvd_sixteen_five (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := Finite.of_equiv _ f.toEquiv
  exact rowSOf429_of_noCfgS429 (hno.of_mulEquiv f.symm)

end CFSG.RankThree.PartTwo.Sec4.RonanK429
