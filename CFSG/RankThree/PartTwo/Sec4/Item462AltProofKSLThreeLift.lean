module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

theorem exists_lift_noncyclic_two {S M : Type} [Group S] [Finite S] [Group M] (ρ : S →* M)
    (hker : Nat.card ρ.ker ∣ 3) {V : Subgroup M} (hV : V ≤ ρ.range) (hV2 : IsPGroup 2 V)
    (hVnc : ¬ IsCyclic V) :
    ∃ P : Subgroup S, IsPGroup 2 P ∧ ¬ IsCyclic P ∧ P ≤ V.comap ρ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup S := V.comap ρ with hT
  let g : T →* V := (ρ.domRestrict T).codRestrict V (fun t => t.2)
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := hV hv
    exact ⟨⟨s, by rw [hT, Subgroup.mem_comap, hs]; exact hv⟩, Subtype.ext hs⟩
  haveI : Finite V := Finite.of_surjective _ hg
  obtain ⟨a, ha⟩ := hV2.exists_card_eq
  have hdvd : Nat.card V ∣ Nat.card T := Subgroup.card_dvd_of_surjective hg
  obtain ⟨Q⟩ : Nonempty (Sylow 2 T) := inferInstance
  have hQcard : Nat.card Q = 2 ^ Nat.factorization (Nat.card T) 2 := Q.card_eq_multiplicity
  have ha' : a ≤ Nat.factorization (Nat.card T) 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne', ← ha]
    exact hdvd
  have hQV : Nat.card V ≤ Nat.card Q := by
    rw [ha, hQcard]
    exact Nat.pow_le_pow_right (by norm_num) ha'
  let P : Subgroup S := (Q : Subgroup T).map T.subtype
  let eQ : (Q : Subgroup T) ≃* P := Subgroup.equivMapOfInjective _ T.subtype T.subtype_injective
  have hP2 : IsPGroup 2 P := IsPGroup.of_surjective Q.isPGroup' eQ.toMonoidHom eQ.surjective
  have hPT : P ≤ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  let ρP : P →* M := ρ.domRestrict P
  have hinj : Function.Injective ρP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxk : (x : S) ∈ ρ.ker := hx
    have h3 : (x : S) ^ 3 = 1 := by
      have h1 : orderOf (x : S) ∣ Nat.card ρ.ker := by
        have := orderOf_dvd_natCard (⟨(x : S), hxk⟩ : ρ.ker)
        rwa [Subgroup.orderOf_mk] at this
      exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans hker)
    obtain ⟨k, hk⟩ := hP2 x
    have hk' : (x : S) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h4 : (x : S) ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.mpr ⟨hk', h3⟩
    rw [hcop, pow_one] at h4
    exact Subtype.ext h4
  have hrange_le : ρP.range ≤ V := by
    rintro _ ⟨x, rfl⟩
    exact hPT x.2
  have hcardP : Nat.card ρP.range = Nat.card P :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hPQ : Nat.card P = Nat.card Q := (Nat.card_congr eQ.toEquiv).symm
  have heqV : ρP.range = V :=
    Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hcardP, hPQ]; exact hQV)
  refine ⟨P, hP2, ?_, hPT⟩
  intro hc
  apply hVnc
  let eV : P ≃* V := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr heqV)
  exact eV.isCyclic.mp hc

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
