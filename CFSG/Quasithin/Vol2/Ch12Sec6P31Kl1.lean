module

public import CFSG.Alternating.Multipliers.Small

public section

namespace CFSG.Quasithin.H13.S126P31


theorem mulEquiv_alt5_of_central_quotient {X : Type} [Group X]
    [Finite X] (hperf : commutator X = ⊤)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (e : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 5)) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨q, hq⟩ : ∃ q : X →* alternatingGroup (Fin 5),
      ∀ x : X, q x = e (QuotientGroup.mk x) :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)), fun x => rfl⟩
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨x, hq x⟩
  have hker_iff : ∀ x : X, q x = 1 ↔ x ∈ Subgroup.center X := by
    intro x
    rw [hq x, e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker_le : q.ker ≤ Subgroup.center X := fun x hx => (hker_iff x).1 (MonoidHom.mem_ker.1 hx)
  have hcenter_eq : Subgroup.center X = q.ker := by
    ext x
    rw [MonoidHom.mem_ker, hker_iff x]
  have hperfX : Group.IsPerfect X := Group.isPerfect_def.mpr hperf
  have hdvd : Nat.card q.ker ∣ 2 := by
    have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hqs hker_le
    have h1 := Subgroup.card_map_dvd
      (CFSG.RankThree.PerfectCover.hopfMultiplier ↥(alternatingGroup (Fin 5)))
      (CFSG.RankThree.PerfectCover.hopfLift q hqs hker_le)
    rw [hmap, CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five.2] at h1
    exact h1
  have hcard : Nat.card ↥(Subgroup.center X) ∣ 2 := by
    rw [hcenter_eq]
    exact hdvd
  have hno2 : ∀ x : ↥(Subgroup.center X), orderOf x ≠ 2 := by
    intro x hx
    have h1 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have h2 : (x : X) ^ 2 ^ 1 = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have h3 : (x : X) = 1 := hodd (x : X) x.2 1 h2
    have h4 : x = 1 := Subtype.ext (by simpa using h3)
    rw [h4, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hone : Nat.card ↥(Subgroup.center X) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card ↥(Subgroup.center X) := by omega
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
      exact hno2 x hx
  have hinj : Function.Injective q := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hsub : Subsingleton ↥(Subgroup.center X) := (Nat.card_eq_one_iff_unique.mp hone).1
    have h1 : (⟨x, (hker_iff x).1 hx⟩ : ↥(Subgroup.center X)) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  exact ⟨MulEquiv.ofBijective q ⟨hinj, hqs⟩⟩

end CFSG.Quasithin.H13.S126P31
