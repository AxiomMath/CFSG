module

public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem isCyclic_sylow_of_surjective {H H' : Type*} [Group H] [Group H'] [Finite H] {p : ℕ}
    [Fact p.Prime] (f : H →* H') (hf : Function.Surjective f)
    (hH : ∀ P : Sylow p H, IsCyclic P) (Q : Sylow p H') : IsCyclic Q := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  have := hH P
  rw [Sylow.coe_mapSurjective]
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem isCyclic_sylow_of_mulEquiv {H H' : Type*} [Group H] [Group H'] [Finite H] {p : ℕ}
    [Fact p.Prime] (e : H ≃* H') (hH : ∀ P : Sylow p H, IsCyclic P) (Q : Sylow p H') :
    IsCyclic Q :=
  isCyclic_sylow_of_surjective e.toMonoidHom e.surjective hH Q

theorem isCyclic_sylow_of_quotient {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup H) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hQ : ∀ S : Sylow p (H ⧸ N), IsCyclic S) (P : Sylow p H) : IsCyclic P := by
  set f : (P : Subgroup H) →* H ⧸ N := (QuotientGroup.mk' N).comp (P : Subgroup H).subtype
    with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : H) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have h1 : orderOf (x : H) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard _ hxN
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp P.isPGroup')
    have h2 : orderOf x ∣ p ^ k := hk ▸ orderOf_dvd_natCard x
    rw [Subgroup.orderOf_coe] at h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Fact.out).mp h2
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exfalso
      exact hN ((dvd_pow_self p (by omega)).trans (hi ▸ h1))
  set R := (P : Subgroup H).map (QuotientGroup.mk' N) with hRdef
  have hR : IsPGroup p R := P.isPGroup'.map (QuotientGroup.mk' N)
  obtain ⟨S, hS⟩ := hR.exists_le_sylow
  have := hQ S
  have hRc : IsCyclic R :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom (MulEquiv.surjective _)
  have hfR : f.range = R := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfc : IsCyclic f.range := by
    rw [hfR]
    exact hRc
  exact isCyclic_of_surjective (MonoidHom.ofInjective hfinj).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem false_of_isCyclic_sylow {W : Type} [Group W] [Finite W]
    (hcyc : ∀ P : Sylow 3 W, IsCyclic P) {u v : W} (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (hu1 : u ≠ 1) (huv : u * v = v * u) (hvu : v ∉ Subgroup.zpowers u) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hE
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup huv hx
    have hc : Commute (u ^ i) (v ^ j) := (Commute.zpow_zpow huv i j)
    rw [hc.mul_pow, ← zpow_natCast, ← zpow_natCast (v ^ j), ← zpow_mul, ← zpow_mul, mul_comm i,
      mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hu3, hv3, one_zpow, one_zpow,
      mul_one]
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x x.2)⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have := hcyc P
  have hEc : IsCyclic E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom (MulEquiv.surjective _)
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := E)
  have hw3 : orderOf w ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE3 w w.2))
  have hcardE : Nat.card E ≤ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hw]
    exact Nat.le_of_dvd (by norm_num) hw3
  have hu : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hle : Subgroup.zpowers u ≤ E := le_sup_left
  have heq : Subgroup.zpowers u = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, hu]
    exact hcardE
  exact hvu (heq ▸ (le_sup_right : Subgroup.zpowers v ≤ E) (Subgroup.mem_zpowers v))

theorem isCyclic_sylow_three_of_not_nine_dvd {X : Type*} [Group X] [Finite X]
    (h9 : ¬ 9 ∣ Nat.card X) (P : Sylow 3 X) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card _
  rcases k with _ | _ | k
  · rw [pow_zero] at hk
    have : Subsingleton (P : Subgroup X) := (Nat.card_eq_one_iff_unique.mp hk).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk
  · exact absurd ((pow_dvd_pow 3 (by omega : 2 ≤ k + 2)).trans hdvd) h9

theorem isCyclic_sylow_three_of_psl2 {X : Type} [Group X] [Finite X] (hQ : IsQuasisimple X)
    {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hF : Nat.card F = p ^ n) (e : X ≃* projSL 2 F) (P : Sylow 3 X) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F := e.trans (Sec4.projSLEquivPSL F)
    with he'
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := Finite.of_equiv X e'.toEquiv
  by_cases h7 : 7 ≤ Nat.card F
  · have hcop : Nat.Coprime 3 (Nat.card F) := by
      rw [hF]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Fact.out).mpr
        (Ne.symm hp3))
    have hc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 3
      (by norm_num) hcop
    exact isCyclic_sylow_of_mulEquiv e'.symm hc P
  · have h1 : 1 < Nat.card F := Finite.one_lt_card
    by_cases h3 : Nat.card F ≤ 3
    · exfalso
      have hs : Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
        fieldCent_isSolvable_psl2 h3
      exact fieldCent_not_isSolvable hQ
        (Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective)
    · have h45 : Nat.card F = 4 ∨ Nat.card F = 5 ∨ Nat.card F = 6 := by omega
      have h60 : Nat.card X = 60 := by
        rw [Nat.card_congr e'.toEquiv]
        rcases h45 with h | h | h
        · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four F h
        · exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_five F h
        · exfalso
          rw [hF] at h
          have h3p : 3 ∣ p ^ n := by rw [h]; norm_num
          have h3p' : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h3p
          exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp h3p').symm
      exact isCyclic_sylow_three_of_not_nine_dvd (by rw [h60]; norm_num) P

theorem isCyclic_sylow_three_of_isType424 {X : Type} [Group X] [Finite X] (hX : IsType424 X)
    (hQ : IsQuasisimple X) (P : Sylow 3 X) : IsCyclic P := by
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | ⟨p, n, hp, hp3, hn, ⟨e⟩⟩ | ⟨n, hn, h⟩
  · exact isCyclic_sylow_three_of_psl2 hQ (p := 2) (n := n) (by norm_num)
      (GaloisField.card 2 n (by omega)) e P
  · exact isCyclic_sylow_three_of_psl2 hQ (p := p) (n := n) (by omega)
      (GaloisField.card p n (by omega)) e P
  · exact KFacts.isCyclic_sylow_three_of_isoLThreeMinusPi_of_ne_zero (by omega) h P

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
