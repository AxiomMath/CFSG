module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.A312Ru

theorem isSolvable_of_card_pq {G : Type} [Group G] [Finite G] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  let _ : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_normalCore (hY : ¬ Group.IsSolvable Y) {Y' : Subgroup Y} {e p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Nat.card Y = 2 ^ e * 3 * p)
    (hcard' : Nat.card Y' = 2 ^ e * 3) : IsPGroup 2 Y'.normalCore := by
  have hKY : Y'.normalCore ≤ Y' := Subgroup.normalCore_le Y'
  have hdvd : Nat.card Y'.normalCore ∣ 2 ^ e * 3 := hcard' ▸ Subgroup.card_dvd_of_le hKY
  by_cases h3 : 3 ∣ Nat.card Y'.normalCore
  · exfalso
    apply hY
    obtain ⟨m, hm⟩ := h3
    have hm2 : m ∣ 2 ^ e := by
      rw [hm, mul_comm (2 ^ e) 3] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    obtain ⟨a, hae, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm2
    have hKs : Group.IsSolvable Y'.normalCore :=
      isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) (a := a) (b := 1)
        (by rw [hm, ha]; ring)
    have hquot : Nat.card (Y ⧸ Y'.normalCore) = 2 ^ (e - a) * p ^ 1 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Y'.normalCore
      rw [hcard, hm, ha] at h
      have h2 : (2 : ℕ) ^ e = 2 ^ (e - a) * 2 ^ a := by rw [← pow_add]; congr 1; omega
      have hpos : 0 < 3 * 2 ^ a := by positivity
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [← h, h2]
      ring
    have hQs : Group.IsSolvable (Y ⧸ Y'.normalCore) :=
      isSolvable_of_card_pq Nat.prime_two hp (Ne.symm hp2) hquot
    exact Group.isSolvable_of_ker_le_range Y'.normalCore.subtype
      (QuotientGroup.mk' Y'.normalCore) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  · have hcop : Nat.Coprime (Nat.card Y'.normalCore) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    have hK2 : Nat.card Y'.normalCore ∣ 2 ^ e := hcop.dvd_of_dvd_mul_right hdvd
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hK2
    exact IsPGroup.of_card ha

theorem pCore_le_of_index {Y' : Subgroup Y} {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card Y = 2 ^ e * 3 * p) (hcard' : Nat.card Y' = 2 ^ e * 3) :
    CFSG.pCore 2 Y ≤ Y' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card Y).factorization 2 = e := by
    rw [hcard, Nat.factorization_mul (by positivity) hp.ne_zero,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq
        Nat.prime_two hp).mp h).symm)]
    simp
  have hfac' : (Nat.card Y').factorization 2 = e := by
    rw [hcard', Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  obtain ⟨Q'⟩ : Nonempty (Sylow 2 Y') := inferInstance
  have hQ'card : Nat.card (Q' : Subgroup Y') = 2 ^ e := by
    rw [Sylow.card_eq_multiplicity, hfac']
  let Q : Sylow 2 Y := Sylow.ofCard ((Q' : Subgroup Y').map Y'.subtype) (by
    rw [Subgroup.card_map_of_injective Y'.subtype_injective, hQ'card, hfac])
  have hP : CFSG.pCore 2 Y ≤ (Q : Subgroup Y) :=
    IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := Y)) Q
  refine hP.trans ?_
  rw [Sylow.coe_ofCard]
  intro x hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

theorem exists_hom_perm (hY : ¬ Group.IsSolvable Y) {Y' : Subgroup Y} {e p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcard : Nat.card Y = 2 ^ e * 3 * p) (hcard' : Nat.card Y' = 2 ^ e * 3) :
    ∃ ρ : Y →* Equiv.Perm (Fin p), ρ.ker = CFSG.pCore 2 Y ∧ ∀ i j : Fin p, ∃ y : Y, ρ y i = j := by
  classical
  have hidx : Y'.index = p := by
    have h := Y'.card_mul_index
    rw [hcard, hcard'] at h
    have hpos : 0 < 2 ^ e * 3 := by positivity
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; linarith [h])
  have hcardα : Nat.card (Y ⧸ Y') = p := by rw [← hidx]; rfl
  let e5 : (Y ⧸ Y') ≃ Fin p := (Finite.equivFin (Y ⧸ Y')).trans (finCongr hcardα)
  let ρ0 : Y →* Equiv.Perm (Y ⧸ Y') := MulAction.toPermHom Y (Y ⧸ Y')
  refine ⟨e5.permCongrHom.toMonoidHom.comp ρ0, ?_, ?_⟩
  · have hker : (e5.permCongrHom.toMonoidHom.comp ρ0).ker = ρ0.ker := by
      ext y
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact e5.permCongrHom.map_eq_one_iff
    rw [hker, ← Subgroup.normalCore_eq_ker]
    apply le_antisymm
    · exact le_sSup ⟨inferInstance, isPGroup_normalCore hY hp hp2 hcard hcard'⟩
    · exact Subgroup.normal_le_normalCore.mpr (pCore_le_of_index hp hp2 hcard hcard')
  · intro i j
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y (e5.symm i) (e5.symm j)
    refine ⟨y, ?_⟩
    show e5 (ρ0 y (e5.symm i)) = j
    have h1 : ρ0 y (e5.symm i) = y • e5.symm i := rfl
    rw [h1, hy]
    simp

end CFSG.Quasithin.A312Ru
