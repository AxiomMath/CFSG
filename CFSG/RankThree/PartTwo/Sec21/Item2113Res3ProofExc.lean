module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofChoice
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open Subgroup
open scoped Pointwise

theorem eq_or_eq_top_of_index_three {S : Type*} [Group S] {T H : Subgroup S}
    (hidx : T.index = 3) (hTH : T ≤ H) : H = T ∨ H = ⊤ := by
  have h := relIndex_mul_index hTH
  rw [hidx] at h
  have hdvd : H.index ∣ 3 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Or.inr (index_eq_one.mp h1)
  · left
    rw [h3] at h
    have h1 : T.relIndex H = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp h1) hTH

theorem central_of_index_three {S : Type*} [Group S] [Finite S] (hS : IsPGroup 3 S)
    {T : Subgroup S} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hidx : T.index = 3)
    {R : Subgroup S} (hR : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) {d : S}
    (hd : ∀ r ∈ R, r * d = d * r) (s : S) : s * d = d * s := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hR
  by_cases hdT : d ∈ T
  · have hRT : ¬ R ≤ T := fun h => hxy (hT x (h hx) y (h hy))
    have hC : T ⊔ R ≤ centralizer ({d} : Set S) := by
      refine sup_le (fun t ht => ?_) (fun r hr => ?_)
      · exact mem_centralizer_singleton_iff.mpr (hT t ht d hdT)
      · exact mem_centralizer_singleton_iff.mpr (hd r hr)
    rcases eq_or_eq_top_of_index_three hidx (le_sup_left : T ≤ T ⊔ R) with h | h
    · exact absurd (h ▸ (le_sup_right : R ≤ T ⊔ R)) hRT
    · exact mem_centralizer_singleton_iff.mp (hC (h ▸ mem_top s))
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 := T.card_mul_index
      rw [hk, hidx, pow_zero] at h1
      have h2 : 1 ≤ Nat.card T := Nat.card_pos
      omega
    have hTn : T.Normal := normal_of_index_eq_minFac_card (by
      rw [hidx, hk, Nat.Prime.pow_minFac Nat.prime_three hk0])
    have htop : T ⊔ zpowers d = ⊤ := by
      rcases eq_or_eq_top_of_index_three hidx (le_sup_left : T ≤ T ⊔ zpowers d) with h | h
      · exact absurd (h ▸ (le_sup_right : zpowers d ≤ T ⊔ zpowers d) (mem_zpowers d)) hdT
      · exact h
    have hdec : ∀ g : S, ∃ t ∈ T, ∃ k : ℤ, g = t * d ^ k := by
      intro g
      have hg : g ∈ ((T ⊔ zpowers d : Subgroup S) : Set S) := by rw [htop]; exact mem_top g
      rw [normal_mul] at hg
      obtain ⟨t, ht, w, hw, rfl⟩ := hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      exact ⟨t, ht, k, rfl⟩
    have hcomm : ∀ g ∈ centralizer ({d} : Set S), ∀ g' ∈ centralizer ({d} : Set S),
        g * g' = g' * g := by
      intro g hg g' hg'
      obtain ⟨t, ht, i, rfl⟩ := hdec g
      obtain ⟨t', ht', j, rfl⟩ := hdec g'
      have hdi : d ^ i ∈ centralizer ({d} : Set S) :=
        zpow_mem (mem_centralizer_singleton_iff.mpr rfl) i
      have hdj : d ^ j ∈ centralizer ({d} : Set S) :=
        zpow_mem (mem_centralizer_singleton_iff.mpr rfl) j
      have htC : t ∈ centralizer ({d} : Set S) := by
        have : t = t * d ^ i * (d ^ i)⁻¹ := by group
        rw [this]
        exact mul_mem hg (inv_mem hdi)
      have ht'C : t' ∈ centralizer ({d} : Set S) := by
        have : t' = t' * d ^ j * (d ^ j)⁻¹ := by group
        rw [this]
        exact mul_mem hg' (inv_mem hdj)
      have c1 : Commute t' (d ^ i) :=
        (Commute.zpow_right (mem_centralizer_singleton_iff.mp ht'C) i)
      have c2 : Commute t (d ^ j) :=
        (Commute.zpow_right (mem_centralizer_singleton_iff.mp htC) j)
      have c3 : t * t' = t' * t := hT t ht t' ht'
      calc t * d ^ i * (t' * d ^ j) = t * (d ^ i * t') * d ^ j := by group
        _ = t * (t' * d ^ i) * d ^ j := by rw [c1.eq]
        _ = (t * t') * (d ^ i * d ^ j) := by group
        _ = (t' * t) * (d ^ j * d ^ i) := by rw [c3, ← zpow_add, ← zpow_add, add_comm]
        _ = t' * (t * d ^ j) * d ^ i := by group
        _ = t' * (d ^ j * t) * d ^ i := by rw [c2.eq]
        _ = t' * d ^ j * (t * d ^ i) := by group
    exact hxy (hcomm x (mem_centralizer_singleton_iff.mpr (hd x hx)) y
      (mem_centralizer_singleton_iff.mpr (hd y hy)))

theorem exists_abelian_index_three {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hv : (Nat.card X).factorization 3 = (Nat.card T).factorization 3 + 1) (S : Sylow 3 X) :
    ∃ T' : Subgroup (S : Subgroup X), (∀ a ∈ T', ∀ b ∈ T', a * b = b * a) ∧ T'.index = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 T) := inferInstance
  set P' : Subgroup X := (P : Subgroup T).map T.subtype with hP'
  have hP'card : Nat.card P' = 3 ^ (Nat.card T).factorization 3 := by
    rw [hP', card_map_of_injective T.subtype_injective, Sylow.card_eq_multiplicity]
  have hP'3 : IsPGroup 3 P' := P.isPGroup'.map T.subtype
  obtain ⟨Q, hQ⟩ := hP'3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q S
  set T'' : Subgroup X := P'.map (MulAut.conj g).toMonoidHom with hT''
  have hT''S : T'' ≤ (S : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact map_mono hQ
  refine ⟨T''.subgroupOf S, ?_, ?_⟩
  · rintro ⟨a, haS⟩ ha ⟨b, hbS⟩ hb
    rw [mem_subgroupOf] at ha hb
    obtain ⟨a', ⟨a'', ha'', rfl⟩, rfl⟩ := ha
    obtain ⟨b', ⟨b'', hb'', rfl⟩, rfl⟩ := hb
    apply Subtype.ext
    simp only [MulMemClass.mk_mul_mk, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      coe_subtype]
    have h := hT _ a''.2 _ b''.2
    calc g * ↑a'' * g⁻¹ * (g * ↑b'' * g⁻¹) = g * (↑a'' * ↑b'') * g⁻¹ := by group
      _ = g * (↑b'' * ↑a'') * g⁻¹ := by rw [h]
      _ = g * ↑b'' * g⁻¹ * (g * ↑a'' * g⁻¹) := by group
  · have hcard : Nat.card (T''.subgroupOf S) = 3 ^ (Nat.card T).factorization 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hT''S).toEquiv, hT'',
        card_map_of_injective (MulAut.conj g).injective, hP'card]
    have hS := S.card_eq_multiplicity
    have h := (T''.subgroupOf S).card_mul_index
    rw [hcard, hS, hv, pow_succ] at h
    have hpos : 0 < 3 ^ (Nat.card T).factorization 3 := by positivity
    exact (Nat.eq_of_mul_eq_mul_left hpos h)

theorem two_pow_mod_three {n : ℕ} (he : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := he
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem factorization_mul_eq_succ {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hb3 : b.factorization 3 = 1) : (a * b).factorization 3 = a.factorization 3 + 1 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, hb3]

theorem factorization_g2_cofactor {n : ℕ} (he : Even n) :
    ((2 ^ n) ^ 6 * ((2 ^ n) ^ 2 + 2 ^ n + 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)).factorization 3
      = 1 := by
  set q := 2 ^ n with hq
  have hq3 : q % 3 = 1 := two_pow_mod_three he
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h3 : 3 ∣ q - 1 := by omega
  have hA : (q ^ 6).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    rw [hq, ← pow_mul]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega)
  have hB := CFSG.SectionRank.OddCover.factorization_sq_add_add_one Nat.prime_three hq1 h3
  rw [Nat.Prime.factorization_self Nat.prime_three] at hB
  have hC : (q ^ 3 + 1).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro h
    have : (q ^ 3 + 1) % 3 = 2 := by rw [Nat.add_mod, Nat.pow_mod, hq3]
    omega)
  have hD : (q + 1).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  have h0 : ∀ m, q ^ m ≠ 0 := fun m => by positivity
  rw [Nat.factorization_mul (by positivity) (by omega), Nat.factorization_mul (by positivity)
      (by positivity), Nat.factorization_mul (h0 6) (by positivity)]
  simp only [Finsupp.add_apply, hA, hB, hC, hD]

theorem factorization_d4_cofactor {n : ℕ} (he : Even n) :
    ((2 ^ n) ^ 12 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 3 + 1) *
      (2 ^ n + 1)).factorization 3 = 1 := by
  set q := 2 ^ n with hq
  have hq3 : q % 3 = 1 := two_pow_mod_three he
  have hq1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have h3 : 3 ∣ q ^ 4 - 1 := by
    have : q ^ 4 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    omega
  have hA : (q ^ 12).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    rw [hq, ← pow_mul]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega)
  have hB := CFSG.SectionRank.OddCover.factorization_sq_add_add_one Nat.prime_three hq1 h3
  rw [Nat.Prime.factorization_self Nat.prime_three, ← pow_mul] at hB
  have hC : (q ^ 3 + 1).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro h
    have : (q ^ 3 + 1) % 3 = 2 := by rw [Nat.add_mod, Nat.pow_mod, hq3]
    omega)
  have hD : (q + 1).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  have h0 : ∀ m, q ^ m ≠ 0 := fun m => by positivity
  rw [Nat.factorization_mul (by positivity) (by omega), Nat.factorization_mul (by positivity)
      (by positivity), Nat.factorization_mul (h0 12) (by positivity)]
  simp only [Finsupp.add_apply, hA, hB, hC, hD]

section Tori


theorem g2_abelian_index {X : Type} [Group X] [Finite X] {n : ℕ} (he : Even n)
    (hX : ChevalleyExceptionalModel X .G2 2 n) :
    ∃ T : Subgroup X, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (Nat.card X).factorization 3 = (Nat.card T).factorization 3 + 1 := by
  obtain ⟨-, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model hX
  set T₀ : Subgroup (adjointGroup Tag.G2 K) :=
    (torusGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) with hT₀
  refine ⟨T₀.map e.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (triangular_borel_structure.{0, 0} Tag.G2 K).1 _ (mem_subgroupOf.mp ha) _
      (mem_subgroupOf.mp hb)
  · have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hT : Nat.card (T₀.map e.symm.toMonoidHom) = (2 ^ n - 1) ^ 2 := by
      rw [card_map_of_injective e.symm.injective, hT₀,
        Nat.card_congr (subgroupOfEquivOfLe
          CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup).toEquiv,
        CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2, hK]
    have hX' : Nat.card X = CFSG.Open.ordG2 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hX
    have hfac : CFSG.Open.ordG2 (2 ^ n) = (2 ^ n - 1) ^ 2 * ((2 ^ n) ^ 6 *
        ((2 ^ n) ^ 2 + 2 ^ n + 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)) := by
      have h6 : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ hq1
      have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq1
      unfold CFSG.Open.ordG2
      zify [hq1, h6, h2]
      ring
    have hne : (2 ^ n - 1) ^ 2 ≠ 0 := by
      have : 2 ≤ 2 ^ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0
          exact absurd hX.1.2.1 (by omega)
        · calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h0
      exact pow_ne_zero 2 (by omega)
    rw [hT, hX', hfac, factorization_mul_eq_succ hne (by positivity)
      (factorization_g2_cofactor he)]

theorem d4_abelian_index {X : Type} [Group X] [Finite X] {n : ℕ} (he : Even n)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) :
    ∃ T : Subgroup X, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (Nat.card X).factorization 3 = (Nat.card T).factorization 3 + 1 := by
  obtain ⟨hn1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model hX
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set T₀ : Subgroup C :=
    (CFSG.Timmesfeld.ExceptionalOrders.compatTorus (t := TwistTag.D4) σ.toRingHom).subgroupOf C
    with hT₀
  refine ⟨T₀.map e.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hle := CFSG.Timmesfeld.ExceptionalOrders.compatTorus_le_torusGroup
      (t := TwistTag.D4) σ.toRingHom
    exact (triangular_borel_structure.{0, 0} TwistTag.D4.tag K).1 _ (hle (mem_subgroupOf.mp ha)) _
      (hle (mem_subgroupOf.mp hb))
  · have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hodd : Odd (Nat.card K - 1) := by
      rw [hK, ← pow_mul]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.D4)
      (σ := σ.toRingHom) Nat.prime_two hn1 hK (fun c => hσ c)
    have hTc := CFSG.Timmesfeld.ExceptionalOrders.card_compatTorus_mul (t := TwistTag.D4)
      (K := K) σ.toRingHom
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_compat_inf_ker_D4 σ.toRingHom hodd,
      CFSG.Timmesfeld.ExceptionalOrders.card_compatSubgroup, mul_one] at hTc
    simp only [hq] at hTc
    rw [CFSG.Timmesfeld.ExceptionalOrders.prod_orbit_D4] at hTc
    have hT : Nat.card (T₀.map e.symm.toMonoidHom) = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) := by
      rw [card_map_of_injective e.symm.injective, hT₀,
        Nat.card_congr (subgroupOfEquivOfLe
          (CFSG.Timmesfeld.ExceptionalOrders.compatTorus_le_graphFixedRootGroup
            (t := TwistTag.D4) σ.toRingHom)).toEquiv, hTc]
    have hX' : Nat.card X = CFSG.Open.ordTrialityD4 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hX
    have hfac : CFSG.Open.ordTrialityD4 (2 ^ n) = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) *
        ((2 ^ n) ^ 12 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1)) := by
      have h6 : 1 ≤ (2 ^ n) ^ 6 := Nat.one_le_pow _ _ hq1
      have h3 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ hq1
      have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ hq1
      unfold CFSG.Open.ordTrialityD4
      zify [hq1, h6, h3, h2]
      ring
    have hne : ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) ≠ 0 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      have h8 : 8 ≤ (2 ^ n) ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3
      have : 0 < (2 ^ n) ^ 3 - 1 := by omega
      have : 0 < 2 ^ n - 1 := by omega
      positivity
    rw [hT, hX', hfac, factorization_mul_eq_succ hne (by positivity)
      (factorization_d4_cofactor he)]

theorem central_of_model {X : Type} [Group X] [Finite X]
    (hX : ∃ n : ℕ, 0 < n ∧ Even n ∧ (ChevalleyExceptionalModel X .G2 2 n ∨
        ChevalleyExceptionalModel X .trialityD4 2 n))
    {R : Subgroup X} (hR : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) {d : X} (hdR : d ∈ R)
    (hd : ∀ r ∈ R, r * d = d * r) (S : Sylow 3 X) (hRS : R ≤ S) :
    ∀ s ∈ (S : Subgroup X), s * d = d * s := by
  obtain ⟨n, -, he, hm⟩ := hX
  obtain ⟨T, hT, hv⟩ : ∃ T : Subgroup X, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (Nat.card X).factorization 3 = (Nat.card T).factorization 3 + 1 :=
    hm.elim (g2_abelian_index he) (d4_abelian_index he)
  obtain ⟨T', hT', hidx⟩ := exists_abelian_index_three hT hv S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hs
  have hnab : ∃ x ∈ R.subgroupOf (S : Subgroup X), ∃ y ∈ R.subgroupOf (S : Subgroup X),
      x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hR
    exact ⟨⟨x, hRS hx⟩, mem_subgroupOf.mpr hx, ⟨y, hRS hy⟩, mem_subgroupOf.mpr hy,
      fun h => hxy (congrArg Subtype.val h)⟩
  have hcomm : ∀ r ∈ R.subgroupOf (S : Subgroup X), r * ⟨d, hRS hdR⟩ = ⟨d, hRS hdR⟩ * r := by
    rintro ⟨r, hrS⟩ hr
    exact Subtype.ext (hd r (mem_subgroupOf.mp hr))
  have h := central_of_index_three S.isPGroup' hT' hidx hnab hcomm ⟨s, hs⟩
  exact congrArg Subtype.val h

theorem kf2113ExcCentral_holds : KF2113ExcCentral := by
  intro G _ _ L hexc R hRL hR3 hnab d hdR _ _ hdc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hN
  set π := QuotientGroup.mk' N with hπ
  set R' : Subgroup L := R.subgroupOf L with hR'
  have hR'3 : IsPGroup 3 R' := hR3.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨Q, hQ⟩ := hR'3.exists_le_sylow
  have hinj : Set.InjOn π (Q : Set L) := injOn_mk_of_isPGroup Nat.prime_three Q.isPGroup'
  set Qb := Q.mapSurjective (QuotientGroup.mk'_surjective N) with hQb
  have hQb' : (Qb : Subgroup (lBar L)) = (Q : Subgroup L).map π := Sylow.coe_mapSurjective _ _
  set d' : L := ⟨d, hRL hdR⟩ with hd'
  have hd'R : d' ∈ R' := mem_subgroupOf.mpr hdR
  have hd'Q : d' ∈ (Q : Subgroup L) := hQ hd'R
  have hnab' : ∃ x ∈ R'.map π, ∃ y ∈ R'.map π, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    have hx' : (⟨x, hRL hx⟩ : L) ∈ R' := mem_subgroupOf.mpr hx
    have hy' : (⟨y, hRL hy⟩ : L) ∈ R' := mem_subgroupOf.mpr hy
    refine ⟨π ⟨x, hRL hx⟩, mem_map_of_mem π hx', π ⟨y, hRL hy⟩, mem_map_of_mem π hy', ?_⟩
    intro h
    rw [← map_mul, ← map_mul] at h
    have h2 := hinj (Q.mul_mem (hQ hx') (hQ hy')) (Q.mul_mem (hQ hy') (hQ hx')) h
    exact hxy (congrArg Subtype.val h2)
  have hcomm' : ∀ r ∈ R'.map π, r * π d' = π d' * r := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hdc r (mem_subgroupOf.mp hr))
  have hle : R'.map π ≤ (Qb : Subgroup (lBar L)) := by
    rw [hQb']
    exact map_mono hQ
  have key := central_of_model hexc hnab' (mem_map_of_mem π hd'R) hcomm' Qb hle
  refine ⟨(Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, ?_⟩
  have hdQ' : d ∈ (Q : Subgroup L).map L.subtype := mem_map.mpr ⟨d', hd'Q, rfl⟩
  refine mem_map.mpr ⟨⟨d, hdQ'⟩, ?_, rfl⟩
  rw [mem_center_iff]
  rintro ⟨g, hg⟩
  obtain ⟨s, hs, rfl⟩ := mem_map.mp hg
  apply Subtype.ext
  show (s : G) * d = d * s
  have h1 := key (π s) (hQb' ▸ mem_map_of_mem π hs)
  rw [← map_mul, ← map_mul] at h1
  have h2 := hinj (Q.mul_mem hs hd'Q) (Q.mul_mem hd'Q hs) h1
  exact congrArg Subtype.val h2

end Tori

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
