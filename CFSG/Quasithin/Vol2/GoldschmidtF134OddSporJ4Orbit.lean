module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporJ4Eig

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup

theorem false_of_two_group_stabilizer {X Ω : Type*} [Group X] [Finite X] [MulAction X Ω] (w₀ : Ω)
    {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hS : IsPGroup 2 (MulAction.stabilizer X w₀))
    (hidx : (MulAction.stabilizer X w₀).index = p ^ a)
    (E : Subgroup X) (hEw : ∀ e ∈ E, e • w₀ = w₀) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1)
    (hE4 : ∀ x : X, x • w₀ ≠ w₀ → 4 ≤ {w : Ω | ∃ e ∈ E, e • (x • w₀) = w}.ncard) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := MulAction.stabilizer X w₀ with hSdef
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hS
  have hX : Nat.card X = 2 ^ m * p ^ a := by
    have := S.card_mul_index
    rw [hm, hidx] at this
    exact this.symm
  have hSodd : ¬ 2 ∣ S.index := by
    rw [hidx]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hsolv : Group.IsSolvable X := by
    have : Fintype X := Fintype.ofFinite X
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2)
      (q := p) (a := m) (b := a) Nat.prime_two hp (Ne.symm hp2)
      (by rw [← Nat.card_eq_fintype_card, hX])
  set K₀ := S.normalCore with hK₀
  have hK₀S : K₀ ≤ S := S.normalCore_le
  have hK₀p : IsPGroup 2 K₀ := hS.to_le hK₀S
  let π : X →* X ⧸ K₀ := QuotientGroup.mk' K₀
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K₀
  have hπker : π.ker = K₀ := QuotientGroup.ker_mk' K₀
  have hπK₀ : ∀ x : X, π x = 1 ↔ x ∈ K₀ := fun x => QuotientGroup.eq_one_iff x
  have hcardX := Subgroup.card_eq_card_quotient_mul_card_subgroup K₀
  have hnt : Nontrivial (X ⧸ K₀) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hle : Nat.card K₀ ≤ Nat.card S := Subgroup.card_le_of_le hK₀S
    have hprod : Nat.card (X ⧸ K₀) * Nat.card K₀ = 2 ^ m * p ^ a := by
      rw [← hX]; exact hcardX.symm
    have hpos : 0 < Nat.card (X ⧸ K₀) := Nat.card_pos
    have hpos2 : 0 < 2 ^ m := Nat.two_pow_pos m
    have hpa : 1 < p ^ a := Nat.one_lt_pow ha.ne' hp.one_lt
    have hlt : 2 ^ m < 2 ^ m * p ^ a := lt_mul_of_one_lt_right hpos2 hpa
    by_contra hcon
    have h1 : Nat.card (X ⧸ K₀) = 1 := by omega
    rw [h1, one_mul] at hprod
    rw [hm] at hle
    omega
  have hsolvbar : Group.IsSolvable (X ⧸ K₀) := by
    have := hsolv
    infer_instance
  obtain ⟨N, hNmin⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_minimal_nontrivial_normal (G := X ⧸ K₀)
  have hNn : N.Normal := hNmin.1.1
  have hN1 : N ≠ ⊥ := hNmin.1.2
  obtain ⟨r, hr, hNel, d, hd, hNcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary N hNmin
      (by have := hsolvbar; infer_instance)
  have hr2 : r ≠ 2 := by
    intro hr2
    subst hr2
    have hNp : IsPGroup 2 N := IsPGroup.of_card hNcard
    have hMp : IsPGroup 2 (N.comap π) :=
      hNp.comap_of_ker_isPGroup π (by rw [hπker]; exact hK₀p)
    have : (N.comap π).Normal := hNn.comap π
    have hMS : N.comap π ≤ S := IsPGroup.le_sylow_of_normal hMp (hS.toSylow hSodd)
    have hMK : N.comap π ≤ K₀ := Subgroup.normal_le_normalCore.mpr hMS
    apply hN1
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨x, rfl⟩ := hπs n
    have hx : x ∈ N.comap π := Subgroup.mem_comap.mpr hn
    rw [Subgroup.mem_bot]
    exact (hπK₀ x).mpr (hMK hx)
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hNel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨v, hvN, hv1, hveig⟩ := exists_common_eigenvector N hN1 hNcomm
    ((E.map π : Subgroup (X ⧸ K₀)) : Set (X ⧸ K₀))
    (fun ε _ n hn => hNn.conj_mem n hn ε)
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      rw [← map_mul, ← map_mul, hEc e he e' he'])
    (by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_mul, hE2 e he, map_one])
  obtain ⟨x₀, hx₀v⟩ := hπs v
  have hx₀w : x₀ • w₀ ≠ w₀ := by
    intro h
    obtain ⟨j, hj⟩ := hS ⟨x₀, MulAction.mem_stabilizer_iff.mpr h⟩
    have hx2 : x₀ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hv2 : v ^ 2 ^ j = 1 := by rw [← hx₀v, ← map_pow, hx2, map_one]
    have hd2 : orderOf v ∣ r ^ d := hNcard ▸ Subgroup.orderOf_dvd_natCard N hvN
    have hcop : Nat.Coprime (2 ^ j) (r ^ d) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
    have hord : orderOf v = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hv2) hd2
    exact hv1 (orderOf_eq_one_iff.mp hord)
  have hsub : {w : Ω | ∃ e ∈ E, e • (x₀ • w₀) = w} ⊆ {x₀ • w₀, x₀⁻¹ • w₀} := by
    rintro w ⟨e, he, rfl⟩
    have key : ∀ y : X, π (e * x₀ * e⁻¹) = π y → e • (x₀ • w₀) = y • w₀ := by
      intro y hy
      have h1 : (e * x₀ * e⁻¹)⁻¹ * y ∈ K₀ := QuotientGroup.eq.mp hy
      have h2 : ((e * x₀ * e⁻¹)⁻¹ * y) • w₀ = w₀ := MulAction.mem_stabilizer_iff.mp (hK₀S h1)
      have h3 : y • w₀ = (e * x₀ * e⁻¹) • w₀ := by
        calc y • w₀ = ((e * x₀ * e⁻¹) * ((e * x₀ * e⁻¹)⁻¹ * y)) • w₀ := by
              rw [mul_inv_cancel_left]
          _ = (e * x₀ * e⁻¹) • (((e * x₀ * e⁻¹)⁻¹ * y) • w₀) := by rw [mul_smul]
          _ = (e * x₀ * e⁻¹) • w₀ := by rw [h2]
      calc e • (x₀ • w₀) = (e * x₀ * e⁻¹) • (e • w₀) := by
            rw [smul_smul, smul_smul, inv_mul_cancel_right]
        _ = (e * x₀ * e⁻¹) • w₀ := by rw [hEw e he]
        _ = y • w₀ := h3.symm
    have hcase := hveig (π e) (Subgroup.mem_map_of_mem π he)
    rw [← hx₀v] at hcase
    rcases hcase with h | h
    · exact Or.inl (key x₀ (by rw [map_mul, map_mul, map_inv]; exact h))
    · exact Or.inr (key x₀⁻¹ (by rw [map_mul, map_mul, map_inv, map_inv]; exact h))
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2le : ({x₀ • w₀, x₀⁻¹ • w₀} : Set Ω).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have := hE4 x₀ hx₀w
  omega

end CFSG.Quasithin.H13.NQCore
