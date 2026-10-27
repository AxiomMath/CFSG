module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_central_of_isSylowTwoOf {T H : Subgroup G} (hT : IsSylowTwoOf T H) {g : G}
    (hg : g ∈ H) (hc : ∀ b ∈ H, b * g = g * b) (hg2 : g * g = 1) : g ∈ T := by
  set g' : ↥H := ⟨g, hg⟩ with hg'
  have hcen : ∀ b : ↥H, b * g' = g' * b := fun b => Subtype.ext (hc b b.2)
  have hN : (Subgroup.zpowers g').Normal := ⟨fun n hn b => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcb : Commute g' b := (hcen b).symm
    have h : Commute (g' ^ k) b := hcb.zpow_left k
    rw [← h.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers g' k⟩
  have hp : IsPGroup 2 (Subgroup.zpowers g') := by
    have hg2' : g' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hg2)
    have hdvd : orderOf g' ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hg2'
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hle := hp.le_sylow_of_normal (A4.toSylow hT)
  have : g' ∈ T.subgroupOf H := hle (Subgroup.mem_zpowers g')
  exact Subgroup.mem_subgroupOf.1 this

theorem le_of_normalizer_inf_le {T S : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (hN : S ⊓ Subgroup.normalizer (T : Set G) ≤ T) : S ≤ T := by
  by_contra hne
  let IP : Subgroup S := T.subgroupOf S
  have hIPlt : IP < ⊤ := lt_top_iff_ne_top.2 fun htop => hne fun x hx => by
    have : (⟨x, hx⟩ : S) ∈ IP := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := Group.normalizerCondition_of_isNilpotent (G := S)
  have hlt : IP < Subgroup.normalizer (IP : Set S) := hnc IP hIPlt
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNorm : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf S := by
      rw [Subgroup.subgroupOf_normalizer_eq hTS]
      exact hxN
    exact Subgroup.mem_subgroupOf.1 this
  exact hxnot (Subgroup.mem_subgroupOf.2 (hN ⟨x.2, hxNorm⟩))

theorem isSylowTwoOf_top_of_center {M T : Subgroup G} {z : G} (hT : IsSylowTwoOf T M)
    (hz : z ∈ T) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, z * t = t * z)
    (hZ : ∀ w ∈ T, (∀ t ∈ T, w * t = t * w) → w = 1 ∨ w = z)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ M) : IsSylowTwoOf T ⊤ := by
  obtain ⟨S, hS, hTS⟩ := A4.exists_isSylowTwoOf_ge (le_top : T ≤ ⊤) hT.2.1
  have hKM : S ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
    intro g hg
    obtain ⟨-, hgN⟩ := hg
    have hgN' : g⁻¹ ∈ Subgroup.normalizer (T : Set G) := (Subgroup.normalizer _).inv_mem hgN
    have hw : g * z * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hgN z).1 hz
    have hcomm : ∀ t ∈ T, (g * z * g⁻¹) * t = t * (g * z * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g ∈ T := by
        have := (Subgroup.mem_normalizer_iff.1 hgN' t).1 ht
        simpa using this
      have h := hzc _ ht'
      calc g * z * g⁻¹ * t = g * (z * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * z) * g⁻¹ := by rw [h]
        _ = t * (g * z * g⁻¹) := by group
    have hgz : g * z * g⁻¹ = z := by
      rcases hZ _ hw hcomm with h | h
      · exact absurd (by simpa using h) hz1
      · exact h
    apply hcz
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hgz]
  have hmax := (A4.isSylowTwoOf_iff_maximal.1 hT).2.2
  have hN : S ⊓ Subgroup.normalizer (T : Set G) ≤ T :=
    hmax _ hKM (hS.2.1.to_le inf_le_left) (le_inf hTS Subgroup.le_normalizer)
  have hST : S ≤ T := le_of_normalizer_inf_le hS.2.1 hTS hN
  exact le_antisymm hST hTS ▸ hS

omit [Finite G] in
theorem twoPart_eq_of_card_eq {X : Subgroup G} {k m : ℕ} (hm : ¬ 2 ∣ m)
    (h : Nat.card X = 2 ^ k * m) : twoPart X = 2 ^ k := by
  unfold twoPart
  rw [h, Nat.factorization_mul (by positivity) (fun h0 => hm (by rw [h0]; exact dvd_zero 2)),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

end CFSG.Quasithin.H13.F431.U42Aut
