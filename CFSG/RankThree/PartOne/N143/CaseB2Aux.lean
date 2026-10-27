module

public import CFSG.RankThree.PartOne.N143.CaseASetup
public import CFSG.RankThree.PartOne.N143.CaseA

public section

namespace CFSG.RankThree.PartOne.N143

section Sylow

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem ker_piX_eq (Xs : Subgroup (MulAut A)) :
    (piX Xs).ker = (Subgroup.centralizer (A : Set G)).subgroupOf (Xsub A Xs) := by
  ext x
  rw [mem_ker_piX, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact (mul_inv_eq_iff_eq_mul.1 (h a ha)).symm
  · intro h a ha
    exact mul_inv_eq_iff_eq_mul.2 (h a ha).symm

omit [Finite G] in
theorem card_ker_piX (Xs : Subgroup (MulAut A)) :
    Nat.card (piX Xs).ker = Nat.card (Subgroup.centralizer (A : Set G)) := by
  rw [ker_piX_eq, card_subgroupOf_of_le (centralizer_le_Xsub Xs)]

theorem exists_sylow_exp_three (hC : ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set G)))
    {Xs Ps : Subgroup (MulAut A)} (hXs : Xs ≤ A.normalizerMonoidHom.range)
    (hX54 : Nat.card Xs = 54) (hPs : Ps ≤ Xs) (hPcard : Nat.card Ps = 27)
    (hPmem : ∀ y ∈ Xs, y ∈ Ps ↔ y ^ 3 = 1) {R : Subgroup G} (hRX : R ≤ Xsub A Xs)
    (hR3 : ∀ r ∈ R, r ^ 3 = 1) :
    ∃ P : Subgroup G, R ≤ P ∧ P ≤ Xsub A Xs ∧ Nat.card P = 27 ∧ ∀ y ∈ P, y ^ 3 = 1 := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRpg : IsPGroup 3 (R.subgroupOf (Xsub A Xs)) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hR3 _ g.2))⟩
  obtain ⟨Sx, hSx⟩ := hRpg.exists_le_sylow
  have hCpos : Nat.card (Subgroup.centralizer (A : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hXcard : Nat.card (Xsub A Xs) = 54 * Nat.card (Subgroup.centralizer (A : Set G)) := by
    rw [card_eq_range_mul_ker (piX Xs), range_piX Xs hXs, hX54, card_ker_piX]
  have hSxcard : Nat.card Sx = 27 := by
    have h := Sx.card_eq_multiplicity
    rw [hXcard, factorization_three_fifty_four_mul _ hCpos,
      Nat.factorization_eq_zero_of_not_dvd hC] at h
    simpa using h
  have hPsX : Nat.card (Ps.subgroupOf Xs) = 27 := by
    rw [card_subgroupOf_of_le hPs, hPcard]
  have hPsmem : ∀ y : ↥Xs, y ∈ Ps.subgroupOf Xs ↔ y ^ 3 = 1 := by
    intro y
    rw [Subgroup.mem_subgroupOf, hPmem y y.2]
    constructor
    · intro h
      exact Subtype.ext (by simpa using h)
    · intro h
      simpa using congrArg Subtype.val h
  refine ⟨(Sx : Subgroup ↥(Xsub A Xs)).map (Xsub A Xs).subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro r hr
    exact ⟨⟨r, hRX hr⟩, hSx (by rw [Subgroup.mem_subgroupOf]; exact hr), rfl⟩
  · rw [Subgroup.card_map_of_injective (Xsub A Xs).subtype_injective]
    exact hSxcard
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := Sx.isPGroup' ⟨y, hy⟩
    have hyk : y ^ (3 ^ k) = 1 := congrArg Subtype.val hk
    have hπy : piX Xs y ∈ Xs := by
      have : piX Xs y ∈ (piX Xs).range := ⟨y, rfl⟩
      rwa [range_piX Xs hXs] at this
    have hπk : (⟨piX Xs y, hπy⟩ : ↥Xs) ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow]
      rw [← map_pow, hyk, map_one]
    have hmemPs := mem_Pst_of_threePow (H := ↥Xs) (by rw [← hX54]) (Ps.subgroupOf Xs) hPsX hPsmem hπk
    have hπ3 : piX Xs y ^ 3 = 1 := (hPmem _ hπy).1 hmemPs
    have hker3 : y ^ 3 ∈ (piX Xs).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hπ3
    let w : ↥(piX Xs).ker := ⟨y ^ 3, hker3⟩
    have hwk : w ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      show (y ^ 3) ^ (3 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hyk, one_pow]
    have hd1 : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hwk
    have hd2 : orderOf w ∣ Nat.card (piX Xs).ker := orderOf_dvd_natCard w
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (piX Xs).ker) := by
      rw [card_ker_piX]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC)
    have h1 : orderOf w ∣ 1 := by
      have := Nat.dvd_gcd hd1 hd2
      rwa [hcop] at this
    have hw1 : w = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
    have hy3X : y ^ 3 = 1 := congrArg Subtype.val hw1
    exact congrArg Subtype.val hy3X

end Sylow

section Misc

variable {G : Type*} [Group G]

theorem normal_of_card_nine [Finite G] {P R : Subgroup G} (hRP : R ≤ P) (hP : Nat.card P = 27)
    (hR : Nat.card R = 9) : ∀ y ∈ P, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
  have hcard : Nat.card (R.subgroupOf P) = 9 := by
    rw [card_subgroupOf_of_le hRP, hR]
  have hidx : (R.subgroupOf P).index = 3 := by
    have h := Subgroup.card_mul_index (R.subgroupOf P)
    rw [hcard, hP] at h
    omega
  have hmin : (Nat.card P).minFac = 3 := by
    rw [hP]
    norm_num
  have hn : (R.subgroupOf P).Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  intro y hy r hr
  have := hn.conj_mem ⟨r, hRP hr⟩ (by rw [Subgroup.mem_subgroupOf]; exact hr) ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

theorem disjoint_zpowers_of_prime {x z : G} (hz : orderOf z = 3) (hzx : z ∉ Subgroup.zpowers x) :
    Disjoint (Subgroup.zpowers x) (Subgroup.zpowers z) := by
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hcard : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hz]
  have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases ((Subgroup.zpowers x).subgroupOf (Subgroup.zpowers z)).eq_bot_or_eq_top_of_prime_card with h | h
  · rw [Subgroup.disjoint_def]
    intro y hyx hyz
    have : (⟨y, hyz⟩ : Subgroup.zpowers z) ∈ (Subgroup.zpowers x).subgroupOf (Subgroup.zpowers z) := hyx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    apply hzx
    have : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈
        (Subgroup.zpowers x).subgroupOf (Subgroup.zpowers z) := by
      rw [h]
      trivial
    exact this

theorem mem_zpowers_of_cyclic_cube [Finite G] {U : Subgroup G} [IsCyclic U] {x w : G} (hx : x ∈ U)
    (hx3 : orderOf x = 3) (hw : w ∈ U) (hw3 : w ^ 3 = 1) : w ∈ Subgroup.zpowers x := by
  have h : Subgroup.zpowers (⟨w, hw⟩ : U) ≤ Subgroup.zpowers (⟨x, hx⟩ : U) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
    have h1 : orderOf (⟨x, hx⟩ : U) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact hx3
    rw [h1]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext hw3)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (h (Subgroup.mem_zpowers _))
  exact Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩

end Misc

section Cent

variable {G : Type} [Group G] {A : Subgroup G}

theorem mem_centralizer_of_pi_eq_one {u : G} (hu : u ∈ Subgroup.normalizer (A : Set G))
    (h : A.normalizerMonoidHom ⟨u, hu⟩ = 1) : u ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h2 := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : G)) h
  have e1 : ((A.normalizerMonoidHom ⟨u, hu⟩ ⟨a, ha⟩ : A) : G) = u * a * u⁻¹ := rfl
  simp only [e1, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

theorem conj_mem_centralizer {x d : G} (hx : x ∈ Subgroup.normalizer (A : Set G))
    (hd : d ∈ Subgroup.centralizer (A : Set G)) : x * d * x⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hx) a).1 ha
    simpa using this
  have hcomm : (x⁻¹ * a * x) * d = d * (x⁻¹ * a * x) := Subgroup.mem_centralizer_iff.1 hd _ ha'
  calc a * (x * d * x⁻¹) = x * ((x⁻¹ * a * x) * d) * x⁻¹ := by group
    _ = x * (d * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * d * x⁻¹) * a := by group

theorem inv_comm_mem_centralizer {x z : G} (hx : x ∈ Subgroup.normalizer (A : Set G))
    (hz : z ∈ Subgroup.normalizer (A : Set G))
    (h : A.normalizerMonoidHom ⟨z, hz⟩ * A.normalizerMonoidHom ⟨x, hx⟩ =
      A.normalizerMonoidHom ⟨x, hx⟩ * A.normalizerMonoidHom ⟨z, hz⟩) :
    x⁻¹ * (z * x * z⁻¹) ∈ Subgroup.centralizer (A : Set G) := by
  have hu : x⁻¹ * (z * x * z⁻¹) ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hz hx) (Subgroup.inv_mem _ hz))
  refine mem_centralizer_of_pi_eq_one hu ?_
  have e : (⟨x⁻¹ * (z * x * z⁻¹), hu⟩ : Subgroup.normalizer (A : Set G)) =
      (⟨x, hx⟩ : Subgroup.normalizer (A : Set G))⁻¹ *
        (⟨z, hz⟩ * ⟨x, hx⟩ * (⟨z, hz⟩ : Subgroup.normalizer (A : Set G))⁻¹) := rfl
  rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul.2 h, inv_mul_cancel]

end Cent

end CFSG.RankThree.PartOne.N143
