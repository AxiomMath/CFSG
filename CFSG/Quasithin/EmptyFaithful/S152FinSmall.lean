module

public import CFSG.Quasithin.Recognition.CertSzZero
public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S152Fin

theorem card_le_two_of_not_four_dvd {X : Type*} [Group X] [Finite X] (hX : ¬ 4 ∣ Nat.card X)
    {E : Subgroup X} (hE2 : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 2 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 E := by
    intro y
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE2 y y.2
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  by_contra hlt
  push Not at hlt
  rw [hn] at hlt
  have h2n : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> simp at hlt
  apply hX
  have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 h2n
  have h4 : 4 ∣ Nat.card E := by rw [hn]; simpa using this
  exact dvd_trans h4 (E.card_subgroup_dvd_card)

theorem factorization_twenty_five : (20 : ℕ).factorization 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [Nat.factorization_def 20 Nat.prime_five]
  have h : (20 : ℕ) = 5 ^ 1 * 4 := by norm_num
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
  have : padicValNat 5 4 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  omega

theorem conj_dichotomy {X : Type*} [Group X] (p e : X) (k : ℤ) (he' : e * e = 1)
    (hk : p ^ k = e * p * e⁻¹) (hord : orderOf p = 5) :
    e * p * e⁻¹ = p ∨ e * p * e⁻¹ = p⁻¹ := by
  have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he'
  have h1 : p = e * (e * p * e⁻¹) * e⁻¹ := by
    rw [hinv]
    calc p = (e * e) * p * (e * e) := by rw [he']; simp
      _ = e * (e * p * e) * e := by group
  have h2 : p = p ^ (k * k) := by
    calc p = e * (p ^ k) * e⁻¹ := by rw [hk]; exact h1
      _ = (e * p * e⁻¹) ^ k := (conj_zpow).symm
      _ = (p ^ k) ^ k := by rw [hk]
      _ = p ^ (k * k) := (zpow_mul p k k).symm
  have h3 : p ^ (k * k - 1) = 1 := by
    rw [zpow_sub, zpow_one, ← h2, mul_inv_cancel]
  have h4 : (5 : ℤ) ∣ k * k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rwa [hord] at this
  have h5 : (5 : ℤ) ∣ (k - 1) * (k + 1) := by
    have : k * k - 1 = (k - 1) * (k + 1) := by ring
    rwa [this] at h4
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  rcases hp5.dvd_or_dvd h5 with h6 | h6
  · left
    have : p ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hord])
    have : p ^ k = p := by
      calc p ^ k = p ^ (k - 1) * p := by rw [← zpow_add_one]; congr 1; ring
        _ = p := by rw [this, one_mul]
    rw [← hk, this]
  · right
    have : p ^ (k + 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hord])
    have : p ^ k = p⁻¹ := by
      rw [zpow_add_one] at this
      exact eq_inv_of_mul_eq_one_left this
    rw [← hk, this]

theorem central_of_conj_fix {X : Type*} [Group X] [Finite X]
    (hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    {E P : Subgroup X} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1)
    (hEcard : Nat.card E = 4) (hPcard : Nat.card P = 5) (p : X)
    (hgen : ∀ x ∈ P, ∃ k : ℤ, p ^ k = x)
    (key : ∀ e ∈ E, e * p * e⁻¹ = p ∨ e * p * e⁻¹ = p⁻¹) (hcard : Nat.card X = 20) : False := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁, he₁, he₁1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [this, Subgroup.card_bot] at hEcard
    omega
  obtain ⟨e₂, he₂, he₂1, he₂ne⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ e₁ := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers e₁ := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]; exact Subgroup.one_mem _
      · rw [hcon x hx hx1]; exact Subgroup.mem_zpowers e₁
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h3 : orderOf e₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (hE2 e₁ he₁)
    have h4 : orderOf e₁ ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    omega
  have he₁sq : e₁ * e₁ = 1 := by simpa [pow_two] using hE2 e₁ he₁
  obtain ⟨z, hz, hz1, hzp⟩ : ∃ z ∈ E, z ≠ 1 ∧ z * p * z⁻¹ = p := by
    rcases key e₁ he₁ with h | h
    · exact ⟨e₁, he₁, he₁1, h⟩
    rcases key e₂ he₂ with h' | h'
    · exact ⟨e₂, he₂, he₂1, h'⟩
    refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, ?_, ?_⟩
    · intro h1
      apply he₂ne
      have : e₂ = e₁⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, inv_eq_of_mul_eq_one_right he₁sq]
    · have e1 : (e₁ * e₂) * p * (e₁ * e₂)⁻¹ = e₁ * (e₂ * p * e₂⁻¹) * e₁⁻¹ := by group
      rw [e1, h']
      have e2 : e₁ * p⁻¹ * e₁⁻¹ = (e₁ * p * e₁⁻¹)⁻¹ := by group
      rw [e2, h]; simp
  have hcomp : P.IsComplement' E := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hPcard, hEcard, hcard]
    · rw [hPcard, hEcard]; norm_num
  have hcomm : ∀ a ∈ P, z * a * z⁻¹ = a := by
    intro a ha
    obtain ⟨k, rfl⟩ := hgen a ha
    rw [← conj_zpow, hzp]
  have hcentral : ∀ x : X, z * x = x * z := by
    intro x
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab, -⟩ :=
      Subgroup.isComplement_iff_existsUnique.mp (Subgroup.isComplement'_def.mp hcomp) x
    simp only at hab
    have h1 : z * a = a * z := by
      have := hcomm a ha
      calc z * a = (z * a * z⁻¹) * z := by group
        _ = a * z := by rw [this]
    have h2 : z * b = b * z := hE z hz b hb
    rw [← hab]
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [h1]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [h2]
      _ = a * b * z := by group
  have hnormal : (Subgroup.zpowers z).Normal := by
    constructor
    intro n hn g
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * z ^ m * g⁻¹ = z ^ m := by
      have hc : Commute g z := (hcentral g).symm
      rw [(hc.zpow_right m).eq]; group
    rw [this]; exact Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hE2 z hz) hz1
  have hpg : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz2]; norm_num
  have := hO2 _ hnormal hpg
  apply hz1
  have hmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [this] at hmem
  simpa using hmem

theorem card_le_two_of_card_twenty {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 20)
    (hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    {E : Subgroup X} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hlt
  push Not at hlt
  have hEcard : Nat.card E = 4 := by
    have hdvd : Nat.card E ∣ 20 := hcard ▸ Subgroup.card_subgroup_dvd_card E
    have hpg : IsPGroup 2 E := by
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa using hE2 x x.2
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hn] at hdvd hlt ⊢
    have : n ≤ 2 := by
      by_contra hn3
      push Not at hn3
      have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
      have h8 : 8 ∣ 20 := by
        have := dvd_trans (by simpa using this) hdvd
        exact this
      omega
    interval_cases n <;> simp_all
  obtain ⟨P⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hPcard : Nat.card (P : Subgroup X) = 5 := by
    rw [P.card_eq_multiplicity, hcard, factorization_twenty_five]
    norm_num
  have hn5 : Nat.card (Sylow 5 X) = 1 := by
    have h1 := card_sylow_modEq_one 5 X
    have h2 := P.card_dvd_index
    have hidx : (P : Subgroup X).index = 4 := by
      have := (P : Subgroup X).card_mul_index
      rw [hPcard, hcard] at this
      omega
    rw [hidx] at h2
    have hle : Nat.card (Sylow 5 X) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 5 X) := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 X) <;> simp_all
  have hsub : Subsingleton (Sylow 5 X) := by
    have : Nat.card (Sylow 5 X) ≤ 1 := hn5.le
    exact (Finite.card_le_one_iff_subsingleton).mp (by simpa [Nat.card_eq_fintype_card] using this)
  have hPn : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
  have hPcyc : IsCyclic (P : Subgroup X) := isCyclic_of_prime_card hPcard
  obtain ⟨p0, hp0⟩ := hPcyc.exists_generator
  have hpP : (p0 : X) ∈ (P : Subgroup X) := p0.2
  have hgen : ∀ x ∈ (P : Subgroup X), ∃ k : ℤ, (p0 : X) ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hp0 ⟨x, hx⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hord : orderOf (p0 : X) = 5 := by
    have h1 : orderOf p0 = Nat.card (P : Subgroup X) := orderOf_eq_card_of_forall_mem_zpowers hp0
    rw [Subgroup.orderOf_coe p0]
    exact h1.trans hPcard
  have key : ∀ e ∈ E, e * (p0 : X) * e⁻¹ = p0 ∨ e * (p0 : X) * e⁻¹ = (p0 : X)⁻¹ := by
    intro e he
    obtain ⟨k, hk⟩ := hgen (e * (p0 : X) * e⁻¹) (hPn.conj_mem _ hpP e)
    have he' : e * e = 1 := by simpa [pow_two] using hE2 e he
    exact conj_dichotomy (p0 : X) e k he' hk hord
  exact central_of_conj_fix hO2 hE hE2 hEcard hPcard (p0 : X) hgen key hcard

theorem card_le_two_of_isSmallGroup152 {X : Type*} [Group X] (hX : IsSmallGroup152 X)
    {E : Subgroup X} (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE2 : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 2 := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    refine card_le_two_of_not_four_dvd ?_ hE2
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  · have : Finite X := Finite.of_equiv _ e.symm.toEquiv
    refine card_le_two_of_not_four_dvd ?_ hE2
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    norm_num
  · have hc20 : Nat.card X = 20 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_sz_zero_eq_twenty
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc20]; norm_num)
    refine card_le_two_of_card_twenty hc20 ?_ hE hE2
    intro N hN hNp
    have hmapN : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
    have hmapp : IsPGroup 2 (N.map e.toMonoidHom) := hNp.map e.toMonoidHom
    have hle := le_pCore 2 hmapN hmapp
    rw [pCore_two_sz_zero_eq_bot] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp (le_bot_iff.mp hle)

end S152Fin

end CFSG.Quasithin
