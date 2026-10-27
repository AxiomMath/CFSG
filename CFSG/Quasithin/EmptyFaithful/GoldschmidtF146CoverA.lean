module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Quasithin.EmptyFaithful.SBc2SzCore
import CFSG.Quasithin.Vol2.KGNatSL2

public section

open scoped MatrixGroups
open CFSG.Open CFSG.Quasithin

namespace CFSG.Quasithin.F146Field

namespace Cover

private theorem charP_two_of_card_two_pow {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hF])

noncomputable def slTwoCongr {R S : Type} [CommRing R] [CommRing S] (φ : R ≃+* S) :
    SL(2, R) ≃* SL(2, S) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map φ.toRingHom)
    (Matrix.SpecialLinearGroup.map φ.symm.toRingHom) (by ext x i j; simp) (by ext x i j; simp)

noncomputable def ringEquivGalois {F : Type} [Field F] [Finite F] {m : ℕ} (hm : m ≠ 0)
    (hF : Nat.card F = 2 ^ m) : F ≃+* GaloisField 2 m := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hc : Fintype.card F = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 m hm]
  exact FiniteField.ringEquivOfCardEq hc

noncomputable def slTwoEquivGaloisPSL {F : Type} [Field F] [Finite F] {m : ℕ} (hm : m ≠ 0)
    (hF : Nat.card F = 2 ^ m) :
    SL(2, F) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m) :=
  (slTwoCongr (ringEquivGalois hm hF)).trans (pslTwoGf2EquivSl m).symm

noncomputable def pslTwoEquivSl {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* SL(2, F) := by
  have := charP_two_of_card_two_pow hF
  exact (QuotientGroup.quotientMulEquivOfEq CFSG.Quasithin.Vol2.KGNat.center_SL2_eq_bot).trans
    QuotientGroup.quotientBot

end Cover

open Cover

theorem exists_equiv_sl_two_of_isPSL {n : ℕ} {Y : Type} [Group Y] (h : IsPSL 2 2 n Y) :
    1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Y ≃* SL(2, F)) := by
  obtain ⟨⟨-, hn, -⟩, F, iF, iFin, hF, ⟨e⟩⟩ := h
  exact ⟨hn, F, iF, iFin, hF, ⟨e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
      (pslTwoEquivSl hF))⟩⟩

theorem isL2Quot_of_isPSL {n : ℕ} {Y : Type} [Group Y] (h : IsPSL 2 2 n Y) : IsL2Quot n Y := by
  obtain ⟨hn, F, iF, iFin, hF, ⟨e⟩⟩ := exists_equiv_sl_two_of_isPSL h
  exact ⟨e.trans (slTwoEquivGaloisPSL (by omega) hF)⟩

theorem isBenderQuot_of_equiv {m : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsPSL 2 2 m Y ∨ IsSz m Y) : IsBenderQuot m X := by
  rcases h with h | h
  · obtain ⟨e'⟩ := isL2Quot_of_isPSL h
    exact Or.inl ⟨e.trans e'⟩
  · obtain ⟨a, -, rfl, ⟨e'⟩⟩ := SBc2.isSz_equiv h
    exact Or.inr (Or.inl ⟨a, rfl, ⟨e.trans e'⟩⟩)

namespace Cover

private theorem isCyclic_sylow_of_mulEquiv {S T : Type*} [Group S] [Group T] [Finite S]
    (e : S ≃* T) {r : ℕ} [Fact r.Prime] (h : ∀ R : Sylow r T, IsCyclic R) (Q : Sylow r S) :
    IsCyclic Q := by
  have hQ := h (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  change IsCyclic ((Q : Subgroup S).map e.toMonoidHom) at hQ
  exact isCyclic_of_surjective
    ((Q : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    ((Q : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective).symm.surjective

private theorem isCyclic_sylow_of_not_sq_dvd {S : Type*} [Group S] [Finite S] {r : ℕ}
    [Fact r.Prime] (h : ¬ r ^ 2 ∣ Nat.card S) (Q : Sylow r S) : IsCyclic Q := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvd : r ^ k ∣ Nat.card S := hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    exact h ((pow_dvd_pow r (by omega)).trans hdvd)
  interval_cases k
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    infer_instance
  · exact isCyclic_of_prime_card (by rw [hk, pow_one])

theorem isCyclic_sylow_sl_two {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (Q : Sylow r SL(2, F)) :
    IsCyclic Q := by
  refine isCyclic_sylow_of_mulEquiv (slTwoCongr (ringEquivGalois (by omega) hF)) ?_ Q
  clear Q
  intro Q
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    refine isCyclic_sylow_of_not_sq_dvd ?_ Q
    rw [card_sl_two_gf2 2 (by norm_num), show 2 ^ 2 * (4 ^ 2 - 1) = 60 by norm_num]
    intro hdvd
    have hle : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
    have hr7 : r ≤ 7 := by nlinarith
    have := hr.out.two_le
    interval_cases r <;> omega
  · refine isCyclic_sylow_of_mulEquiv (pslTwoGf2EquivSl n).symm (fun R => ?_) Q
    have h7 : 7 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 7 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (GaloisField 2 n)
      (p := 2) (f := n) (GaloisField.card 2 n (by omega)) h7 r hr2 ?_ R
    rw [GaloisField.card 2 n (by omega)]
    exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hr.out).2 fun hd => hr2
      ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).1 hd))

private theorem odd_card_of_forall_odd_orderOf {A : Type*} [Group A] [Finite A]
    (h : ∀ x : A, Odd (orderOf x)) : Odd (Nat.card A) := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne))
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

theorem odd_card_ker {Kb Ks : Type*} [Group Kb] [Finite Kb] [Group Ks] (π : Kb →* Ks)
    (ho : ∀ x ∈ π.ker, Odd (orderOf x)) : Odd (Nat.card π.ker) :=
  odd_card_of_forall_odd_orderOf fun x => by
    rw [← Subgroup.orderOf_coe]
    exact ho _ x.2

theorem ker_eq_bot_of_oddCover_sl_two {n : ℕ} (hn : 2 ≤ n) {Kb F : Type} [Group Kb] [Finite Kb]
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) (hperf : Group.IsPerfect Kb)
    (π : Kb →* SL(2, F)) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center Kb)
    (ho : ∀ x ∈ π.ker, Odd (orderOf x)) : π.ker = ⊥ := by
  have := hperf
  exact CFSG.SectionRank.ker_eq_bot_of_sylow_isCyclic π hπ hc (odd_card_ker π ho)
    fun r hr hr2 _ Q => isCyclic_sylow_sl_two hn hF hr2 Q

theorem ker_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C] (e : B ≃* C) (f : A →* B) :
    (e.toMonoidHom.comp f).ker = f.ker := by
  ext x
  simp [MonoidHom.mem_ker]

end Cover

theorem isL2Quot_of_oddCover {m : ℕ} (hm : 2 ≤ m) {Kb F : Type} [Group Kb] [Finite Kb] [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ m) (hperf : Group.IsPerfect Kb)
    (π : Kb →* SL(2, F)) (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center Kb)
    (ho : ∀ x ∈ π.ker, Odd (orderOf x)) : IsL2Quot m Kb := by
  have hbij : Function.Bijective π :=
    ⟨(MonoidHom.ker_eq_bot_iff π).mp (Cover.ker_eq_bot_of_oddCover_sl_two hm hF hperf π hπ hc ho),
      hπ⟩
  exact ⟨(MulEquiv.ofBijective π hbij).trans (slTwoEquivGaloisPSL (by omega) hF)⟩

theorem isBenderQuot_of_oddCover_sz {n : ℕ} {Kb Ks : Type} [Group Kb] [Finite Kb] [Group Ks]
    (hperf : Group.IsPerfect Kb) (π : Kb →* Ks) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center Kb) (ho : ∀ x ∈ π.ker, Odd (orderOf x))
    (hsz : IsSz n Ks) : IsBenderQuot n Kb := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := SBc2.isSz_equiv hsz
  set e' := e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a) with he'
  have hπ' : Function.Surjective (e'.toMonoidHom.comp π) := e'.surjective.comp hπ
  have hker := ker_comp_equiv e' π
  have hbot : (e'.toMonoidHom.comp π).ker = ⊥ := by
    have := hperf
    exact CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) _ hπ' (hker ▸ hc)
      (hker ▸ odd_card_ker π ho)
  exact Or.inr (Or.inl ⟨a, rfl, ⟨(MulEquiv.ofBijective _
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hbot, hπ'⟩).trans
      (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm⟩⟩)

theorem isBenderQuot_of_oddCover_psl {n : ℕ} (hn : 2 ≤ n) {Kb Ks : Type} [Group Kb] [Finite Kb]
    [Group Ks] (hperf : Group.IsPerfect Kb) (π : Kb →* Ks) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center Kb) (ho : ∀ x ∈ π.ker, Odd (orderOf x))
    (hpsl : IsPSL 2 2 n Ks) : IsBenderQuot n Kb := by
  obtain ⟨-, F, iF, iFin, hF, ⟨e⟩⟩ := exists_equiv_sl_two_of_isPSL hpsl
  have hker := ker_comp_equiv e π
  exact Or.inl (isL2Quot_of_oddCover hn hF hperf (e.toMonoidHom.comp π) (e.surjective.comp hπ)
    (hker ▸ hc) fun x hx => ho x (hker ▸ hx))

end CFSG.Quasithin.F146Field
