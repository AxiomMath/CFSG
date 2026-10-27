module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Eight
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Gen
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

@[expose] def omegaOut1412 {G : Type*} [Group G] (L : Subgroup G) (b : G) : Subgroup G :=
  ⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆

structure OuterInput1412 {G : Type*} [Group G] (L : Subgroup G) (b : G) : Prop where
  simple : IsSimpleGroup ↥(omegaOut1412 L b)
  noncomm : ∃ x y : ↥(omegaOut1412 L b), x * y ≠ y * x
  norm : centralizer ({b} : Set G) ≤ normalizer ((omegaOut1412 L b : Subgroup G) : Set G)
  cent : L ⊓ centralizer ((omegaOut1412 L b : Subgroup G) : Set G) = ⊥
  words : ∀ E : Subgroup G, E ≤ L ⊓ centralizer ({b} : Set G) → Sec3.IsElemTwo E →
    Nat.card E = 4 →
    (∃ x ∈ E, ∃ g ∈ L ⊓ centralizer ({b} : Set G), ∃ q k : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧
        ¬ q ^ k ∣ 3 ∧ q ^ k ∣ orderOf (x * g * x * g⁻¹)) ∨
      (E ≤ omegaOut1412 L b ∧ (∃ y ∈ L ⊓ centralizer ({b} : Set G), orderOf y = 8) ∧
        ∀ x ∈ E, x ≠ 1 → ∃ g₁ ∈ L ⊓ centralizer ({b} : Set G),
          ∃ g₂ ∈ L ⊓ centralizer ({b} : Set G),
            omegaOut1412 L b ≤ closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set G))
  gen : ∀ y ∈ L, orderOf y = 3 → L ≤ normalizer (zpowers y : Set G) ⊔ omegaOut1412 L b

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOut1412_le (L : Subgroup G) (b : G) :
    omegaOut1412 L b ≤ L ⊓ centralizer ({b} : Set G) := by
  rw [omegaOut1412, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem le_centralizer_of_perfect_of_le_sup1412 {W Q M : Subgroup G} [Q.Normal]
    (hQ : IsPGroup 2 Q) (hM : ⁅M, M⁆ = M) (hMW : M ≤ normalizer (W : Set G))
    (hQW : Q ≤ normalizer (W : Set G)) (hMle : M ≤ centralizer (W : Set G) ⊔ Q) :
    M ≤ centralizer (W : Set G) := by
  set N := normalizer (W : Set G) with hN
  set ρ : N →* MulAut W := W.normalizerMonoidHom with hρ
  set M' : Subgroup N := M.subgroupOf N with hM'
  set Q' : Subgroup N := Q.subgroupOf N with hQ'
  have hle : M'.map ρ ≤ Q'.map ρ := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨c, hc, q, hq, hcq⟩ := mem_sup_of_normal_right.mp (hMle (Subgroup.mem_subgroupOf.mp hm))
    have hqN : q ∈ N := hQW hq
    refine ⟨⟨q, hqN⟩, hq, ?_⟩
    ext w
    simp only [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hcw : ∀ v ∈ W, c * v * c⁻¹ = v := fun v hv => by
      rw [← (Subgroup.mem_centralizer_iff.mp hc) v hv, mul_inv_cancel_right]
    change q * (w : G) * q⁻¹ = (m : G) * w * (m : G)⁻¹
    rw [← hcq]
    have hqw : q * (w : G) * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hqN w).1 w.2
    calc q * (w : G) * q⁻¹ = c * (q * (w : G) * q⁻¹) * c⁻¹ := (hcw _ hqw).symm
      _ = c * q * (w : G) * (c * q)⁻¹ := by group
  have h2 : IsPGroup 2 (Q'.map ρ) := (hQ.comap_subtype (K := N)).map ρ
  have hperf : ⁅M'.map ρ, M'.map ρ⁆ = M'.map ρ := by
    have hM'' : ⁅M', M'⁆ = M' := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_commutator, hM', Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (hMW : M ≤ N), hM]
    rw [← Subgroup.map_commutator, hM'']
  have hbot : M'.map ρ = ⊥ := by
    by_contra hne
    have : Nontrivial ↥(M'.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥(M'.map ρ) := by rw [Subgroup.isPerfect_iff]; exact hperf
    have : Group.IsNilpotent ↥(M'.map ρ) := (h2.to_le hle).isNilpotent
    exact Group.IsPerfect.not_isNilpotent ↥(M'.map ρ) inferInstance
  intro m hm
  have hmN : m ∈ N := hMW hm
  have h1 : ρ ⟨m, hmN⟩ = 1 := by
    have : ρ ⟨m, hmN⟩ ∈ M'.map ρ := ⟨⟨m, hmN⟩, hm, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hker : (⟨m, hmN⟩ : N) ∈ ρ.ker := h1
  rw [hρ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

theorem mem_jG_of_mem_famG_zero1412 {T A : Subgroup G} (hA : A ∈ Sec3.famG T 0) {j : ℕ}
    (hj : j + 1 ≤ CFSG.pRank 2 T) {x : G} (hx : x ∈ A) : x ∈ Sec3.jG T j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : Nat.card (zpowers x) ∣ 2 ^ (CFSG.pRank 2 T - j) := by
    rw [Nat.card_zpowers]
    refine (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hA.2.1.2 x hx)).trans ?_
    exact dvd_pow_self 2 (by omega)
  have hA2 : 2 ^ (CFSG.pRank 2 T - j) ∣ Nat.card A := by
    rw [hA.2.2]
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨K, hK, hxK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hx2 hA2
    ((zpowers_le).mpr hx)
  have hKmem : K ∈ Sec3.famG T j := ⟨hKA.trans hA.1,
    ⟨fun a ha b hb => hA.2.1.1 a (hKA ha) b (hKA hb), fun a ha => hA.2.1.2 a (hKA ha)⟩, hK⟩
  exact Sec3.le_jG hKmem (hxK (mem_zpowers x))

theorem omegaG_jG_le_of_mem_famG_zero1412 {T A : Subgroup G} (hA : A ∈ Sec3.famG T 0) {j : ℕ}
    (hj : j + 1 ≤ CFSG.pRank 2 T) (hET : Sec3.omegaG (Sec3.jG T j) ≤ T) :
    Sec3.omegaG (Sec3.jG T j) ≤ A := by
  intro z hz
  by_contra hzA
  obtain ⟨hzJ, hzc, hz2⟩ := hz
  have hcomm : ∀ a ∈ A, ∀ w ∈ zpowers z, a * w = w * a := by
    intro a ha w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (hzc a (mem_jG_of_mem_famG_zero1412 hA hj ha)).symm n)).eq
  have hz1 : z ≠ 1 := fun h1 => hzA (h1 ▸ A.one_mem)
  have hzp : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hinf : A ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwA, hwz⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hwz
    rw [mem_bot]
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    have hmod : z ^ n = z ^ (n % (2 : ℕ)) := zpow_eq_zpow_emod' n hz2'
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · exfalso
      apply hzA
      rw [hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one] at hwA
      exact hwA
  have hel : Sec3.IsElemTwo (A ⊔ zpowers z) := by
    refine Sec3.isElemTwo_sup hA.2.1 ⟨fun a ha b hb => ?_, fun a ha => ?_⟩ hcomm
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
      rw [← zpow_add, ← two_mul, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two]; exact hz2,
        one_zpow]
  have hle := Sec3.card_le_two_pow_pRank (sup_le hA.1 ((zpowers_le).mpr (hET ⟨hzJ, hzc, hz2⟩)))
    hel
  have hcard := Sec3.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, hA.2.2, hzp, Nat.sub_zero] at hcard
  rw [hcard] at hle
  have : 2 ^ CFSG.pRank 2 T * 2 ≤ 2 ^ CFSG.pRank 2 T * 1 := by simpa using hle
  have hpos : 0 < 2 ^ CFSG.pRank 2 T := by positivity
  nlinarith

end Generic


section Star

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem relIndex_eq_card_map1412 (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) (A : Subgroup X) :
    (CFSG.pCore 2 X).relIndex A =
      Nat.card (A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
  rw [← relIndex_ker, QuotientGroup.ker_mk', hK]

theorem isElemTwo_map1412 {Y : Type*} [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : Sec3.IsElemTwo A) : Sec3.IsElemTwo (A.map f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA.2 a ha, map_one]

theorem exists_outer_of_star1412 (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X)
    (hstar : Star1412 X S)
    (hrank : CFSG.Open.twoRank ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2)
    (hLn : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).Normal)
    (hidx : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2) :
    ∃ A ∈ Sec3.famG S 0, ¬ A ≤ CFSG.pCore 2 X ∧ (CFSG.pCore 2 X).relIndex A = 8 ∧
      Nat.card ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
        A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = 4 ∧
      ∃ a ∈ A, QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a ∉
        L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  obtain ⟨-, ⟨A, hA, hAQ⟩, h8⟩ := hstar
  have hA8 : (CFSG.pCore 2 X).relIndex A = 8 := h8 A hA hAQ
  have hcard : Nat.card (A.map π) = 8 := by rw [← relIndex_eq_card_map1412 hK]; exact hA8
  have hB := isElemTwo_map1412 π hA.2.1
  have hinf : Nat.card ↥(L.map π ⊓ A.map π) ≤ 4 := by
    have h2 := Sec3.card_le_two_pow_pRank (T := L.map π) inf_le_left
      (A := L.map π ⊓ A.map π) ⟨fun a ha b hb => hB.1 a ha.2 b hb.2, fun a ha => hB.2 a ha.2⟩
    have h3 : CFSG.pRank 2 ↥(L.map π) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrank
    have h4 : 2 ^ CFSG.pRank 2 ↥(L.map π) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h3
    exact h2.trans (h4.trans (by norm_num))
  have hrel : (L.map π).relIndex (A.map π) ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal _ _)).trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := L.map π) (K := A.map π)
  rw [hcard] at hmul
  have h4 : Nat.card ↥(L.map π ⊓ A.map π) = 4 := by
    have hpos : 0 < Nat.card ↥(L.map π ⊓ A.map π) := Nat.card_pos
    have hpos' : 0 < (L.map π).relIndex (A.map π) :=
      Nat.pos_of_ne_zero (Sec3.relIndex_ne_zero_of_finite _ _)
    nlinarith
  refine ⟨A, hA, hAQ, hA8, h4, ?_⟩
  by_contra hall
  push Not at hall
  have hle : A.map π ≤ L.map π := by
    rintro _ ⟨a, ha, rfl⟩
    exact hall a ha
  have : L.map π ⊓ A.map π = A.map π := inf_eq_right.mpr hle
  rw [this, hcard] at h4
  norm_num at h4

theorem not_isPGroup_of_simple1412 {Ω : Type*} [Group Ω] [Finite Ω] [IsSimpleGroup Ω]
    (hnc : ∃ x y : Ω, x * y ≠ y * x) {p : ℕ} [Fact p.Prime] : ¬ IsPGroup p Ω := by
  intro hp
  obtain ⟨x, y, hxy⟩ := hnc
  have : Nontrivial Ω := ⟨⟨x * y, y * x, hxy⟩⟩
  have hZ := hp.center_nontrivial
  rcases (Subgroup.center Ω).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact ((Subgroup.nontrivial_iff_ne_bot (Subgroup.center Ω)).mp hZ) h
  · have hx : x ∈ Subgroup.center Ω := h ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)

theorem inf_eq_bot_of_inf_omegaOut_eq_bot1412 {G : Type*} [Group G] {L : Subgroup G} {b : G}
    (hout : OuterInput1412 L b) {R : Subgroup G}
    (hRn : centralizer ({b} : Set G) ≤ normalizer (R : Set G))
    (hRΩ : R ⊓ omegaOut1412 L b = ⊥) :
    R ⊓ (L ⊓ centralizer ({b} : Set G)) = ⊥ := by
  set Ω := omegaOut1412 L b
  have hΩC : Ω ≤ centralizer ({b} : Set G) := (omegaOut1412_le L b).trans inf_le_right
  rw [eq_bot_iff]
  rintro n ⟨hnR, hnL, hnC⟩
  have hncent : n ∈ L ⊓ centralizer (Ω : Set G) := by
    refine ⟨hnL, mem_centralizer_iff.mpr fun ω hω => ?_⟩
    have h1 : n * ω * n⁻¹ * ω⁻¹ ∈ R := by
      have : ω * n⁻¹ * ω⁻¹ ∈ R := (mem_normalizer_iff.mp (hRn (hΩC hω)) _).1 (R.inv_mem hnR)
      rw [show n * ω * n⁻¹ * ω⁻¹ = n * (ω * n⁻¹ * ω⁻¹) by group]
      exact R.mul_mem hnR this
    have h2 : n * ω * n⁻¹ * ω⁻¹ ∈ Ω := by
      have : n * ω * n⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hout.norm hnC) _).1 hω
      exact Ω.mul_mem this (Ω.inv_mem hω)
    have h3 : n * ω * n⁻¹ * ω⁻¹ = 1 := by
      have : n * ω * n⁻¹ * ω⁻¹ ∈ R ⊓ Ω := ⟨h1, h2⟩
      rwa [hRΩ, mem_bot] at this
    calc ω * n = (n * ω * n⁻¹ * ω⁻¹)⁻¹ * (n * ω) := by group
      _ = n * ω := by rw [h3, inv_one, one_mul]
  rw [hout.cent, mem_bot] at hncent
  exact hncent

theorem omegaOut_le_or_inf_eq_bot1412 {G : Type*} [Group G] {L : Subgroup G} {b : G}
    (hout : OuterInput1412 L b) {R : Subgroup G}
    (hRn : centralizer ({b} : Set G) ≤ normalizer (R : Set G)) :
    omegaOut1412 L b ≤ R ∨ R ⊓ omegaOut1412 L b = ⊥ := by
  set Ω := omegaOut1412 L b
  have hΩC : Ω ≤ centralizer ({b} : Set G) := (omegaOut1412_le L b).trans inf_le_right
  have : IsSimpleGroup Ω := hout.simple
  have hn : (R.subgroupOf Ω).Normal :=
    (normal_subgroupOf_iff_le_normalizer_inf).mpr (by
      intro ω hω
      have hωN := hRn (hΩC hω)
      rw [mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxR, hxΩ⟩
        exact ⟨(mem_normalizer_iff.mp hωN x).1 hxR,
          Ω.mul_mem (Ω.mul_mem hω hxΩ) (Ω.inv_mem hω)⟩
      · rintro ⟨hxR, hxΩ⟩
        refine ⟨(mem_normalizer_iff.mp hωN x).2 hxR, ?_⟩
        have := Ω.mul_mem (Ω.mul_mem (Ω.inv_mem hω) hxΩ) hω
        rwa [show ω⁻¹ * (ω * x * ω⁻¹) * ω = x by group] at this)
  rcases hn.eq_bot_or_eq_top with h | h
  · exact Or.inr (disjoint_iff.mp (subgroupOf_eq_bot.mp h))
  · exact Or.inl (subgroupOf_eq_top.mp h)

theorem le_zpowers_of_isPGroup_normal1412 {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hidx : L.index ≤ 2) {b : G} (hbL : b ∉ L) (hout : OuterInput1412 L b) {R : Subgroup G}
    (hRC : R ≤ centralizer ({b} : Set G)) (hRn : centralizer ({b} : Set G) ≤ normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) : R ≤ zpowers b := by
  set Ω := omegaOut1412 L b with hΩ
  have hΩC : Ω ≤ centralizer ({b} : Set G) := (omegaOut1412_le L b).trans inf_le_right
  have : IsSimpleGroup Ω := hout.simple
  have hRΩ : R ⊓ Ω = ⊥ := by
    rcases omegaOut_le_or_inf_eq_bot1412 hout hRn with hle | h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact not_isPGroup_of_simple1412 hout.noncomm (hR2.to_le hle)
    · exact h
  have hRcent : R ≤ centralizer (Ω : Set G) := by
    intro r hr
    rw [mem_centralizer_iff]
    intro ω hω
    have h1 : r * ω * r⁻¹ * ω⁻¹ ∈ R := by
      have : ω * r⁻¹ * ω⁻¹ ∈ R := (mem_normalizer_iff.mp (hRn (hΩC hω)) _).1 (R.inv_mem hr)
      rw [show r * ω * r⁻¹ * ω⁻¹ = r * (ω * r⁻¹ * ω⁻¹) by group]
      exact R.mul_mem hr this
    have h2 : r * ω * r⁻¹ * ω⁻¹ ∈ Ω := by
      have : r * ω * r⁻¹ ∈ Ω := (mem_normalizer_iff.mp (hout.norm (hRC hr)) _).1 hω
      exact Ω.mul_mem this (Ω.inv_mem hω)
    have h3 : r * ω * r⁻¹ * ω⁻¹ = 1 := by
      have : r * ω * r⁻¹ * ω⁻¹ ∈ R ⊓ Ω := ⟨h1, h2⟩
      rwa [hRΩ, mem_bot] at this
    calc ω * r = (r * ω * r⁻¹ * ω⁻¹)⁻¹ * (r * ω) := by group
      _ = r * ω := by rw [h3, inv_one, one_mul]
  have hbcent : b ∈ centralizer (Ω : Set G) := by
    rw [mem_centralizer_iff]
    intro ω hω
    exact (mem_centralizer_singleton_iff.mp (hΩC hω))
  have hidx2 : L.index = 2 := by
    have h1 : L.index ≠ 1 := fun h1 => hbL (Subgroup.index_eq_one.mp h1 ▸ mem_top b)
    have h0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  intro r hr
  by_cases hrL : r ∈ L
  · have : r ∈ L ⊓ centralizer (Ω : Set G) := ⟨hrL, hRcent hr⟩
    rw [hout.cent, mem_bot] at this
    rw [this]
    exact one_mem _
  · have hrb : r * b ∈ L := (mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hrL hbL)
    have : r * b ∈ L ⊓ centralizer (Ω : Set G) := ⟨hrb, mul_mem (hRcent hr) hbcent⟩
    rw [hout.cent, mem_bot] at this
    have hr' : r = b⁻¹ := eq_inv_of_mul_eq_one_left this
    rw [hr']
    exact inv_mem (mem_zpowers b)


section PY

variable (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {a : X}
include hK

theorem mk'_eq_one_iff1412 (x : X) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x = 1 ↔ x ∈ CFSG.pCore 2 X := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', hK]

theorem pCore_le_comap_zpowers1412 :
    CFSG.pCore 2 X ≤ (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  intro q hq
  rw [mem_comap, (mk'_eq_one_iff1412 hK q).2 hq]
  exact one_mem _

theorem comap_zpowers_le1412 (haS : a ∈ S) (hQS : CFSG.pCore 2 X ≤ S) :
    (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤ S := by
  intro x hx
  rw [mem_comap] at hx
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
  have hk : (a ^ n)⁻¹ * x ∈ CFSG.pCore 2 X := by
    rw [← mk'_eq_one_iff1412 hK, map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
  have : x = a ^ n * ((a ^ n)⁻¹ * x) := by group
  rw [this]
  exact mul_mem (zpow_mem haS n) (hQS hk)

omit hK in
theorem comap_zpowers_le_comap_centralizer1412 :
    (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  refine comap_mono ?_
  rw [zpowers_le, mem_centralizer_singleton_iff]

omit hK in
theorem comap_centralizer_le_normalizer1412 :
    (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      normalizer (((zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) : Subgroup X) : Set X) := by
  intro g hg
  refine Sec3.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [mem_comap] at hg hx ⊢
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hx
  have hgb : Commute (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) g)
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a) :=
    mem_centralizer_singleton_iff.mp hg
  rw [map_mul, map_mul, map_inv, ← hn, ((hgb.zpow_right n).eq), mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) n

omit hK in
theorem map_comap_centralizer1412 :
    ((centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) =
      centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
  map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem relIndex_le_two_of_le_comap_zpowers1412 (ha2 : a * a = 1) {A' : Subgroup X}
    (hA' : A' ≤ (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) :
    (CFSG.pCore 2 X).relIndex A' ≤ 2 := by
  rw [relIndex_eq_card_map1412 hK]
  have hle : A'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a) :=
    (map_mono hA').trans (map_comap_le _ _)
  refine (Subgroup.card_le_of_le hle).trans ?_
  rw [Nat.card_zpowers]
  refine orderOf_le_of_pow_eq_one (by norm_num) ?_
  rw [← map_pow, sq, ha2, map_one]

end PY

section Star2

omit [Finite X] in
theorem relIndex_centralizer_conj_of_mem_normalizer1412 {W : Subgroup X} {g : X}
    (hg : g ∈ normalizer (W : Set X)) (x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex W =
      (centralizer ({x} : Set X)).relIndex W := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg).symm

variable (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {a : X}
include hK

theorem le_sup_of_map_inf_ne_bot1412
    (hout : OuterInput1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a))
    {C LY : Subgroup X}
    (hCY : (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      normalizer (C : Set X))
    (hLYmap : LY.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) =
      omegaOut1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a))
    (hne : C.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
        centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
          Set (X ⧸ CFSG.pPrimeCore 3 X))) ≠ ⊥) :
    LY ≤ C ⊔ CFSG.pCore 2 X := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hCn : centralizer ({π a} : Set (X ⧸ CFSG.pPrimeCore 3 X)) ≤
      normalizer ((C.map π : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) :
        Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ :
        c ∈ ((centralizer ({π a} : Set (X ⧸ CFSG.pPrimeCore 3 X))).comap π).map π := by
      rw [map_comap_centralizer1412]
      exact hc
    have hyN := hCY hy
    refine Sec3.mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨y * w * y⁻¹, (mem_normalizer_iff.mp hyN w).1 hw, ?_⟩
    simp only [map_mul, map_inv]
  rcases omegaOut_le_or_inf_eq_bot1412 hout hCn with hle | hbot
  · intro l hl
    have : π l ∈ C.map π := hle (hLYmap ▸ mem_map_of_mem π hl)
    have hl' : l ∈ (C.map π).comap π := this
    rw [comap_map_eq, QuotientGroup.ker_mk', hK] at hl'
    exact hl'
  · exact absurd (inf_eq_bot_of_inf_omegaOut_eq_bot1412 hout hCn hbot) hne

theorem four_le_relIndex_of_star1412 (h : Hyp1411 X L S)
    (hout : OuterInput1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a))
    (haS : a ∈ S) {A W LY : Subgroup X}
    (hAY : A ≤ (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (hAel : Sec3.IsElemTwo A)
    (hE4 : Nat.card ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = 4)
    (hW : Sec3.IsElemTwo W)
    (hWP : W ≤ (zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (hWY : (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      normalizer (W : Set X))
    (hLYY : LY ≤ (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (hLYp : ⁅LY, LY⁆ = LY)
    (hLYn : (centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a} :
        Set (X ⧸ CFSG.pPrimeCore 3 X))).comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
      normalizer (LY : Set X))
    (hLYmap : LY.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) =
      omegaOut1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) a))
    (hLYW : ¬ LY ≤ centralizer (W : Set X)) :
    4 ≤ (centralizer (A : Set X)).relIndex W := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  set b := π a with hb
  set Y := (centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))).comap π with hY
  set P := (zpowers b).comap π with hP
  set Lst := L.map π with hLst
  set Ω := omegaOut1412 Lst b with hΩ
  have hQS : CFSG.pCore 2 X ≤ S := h.2.2.2.2.2.1
  have hS2 : IsPGroup 2 S := h.2.2.2.2.1
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 X) := hS2.to_le hQS
  have hQP : CFSG.pCore 2 X ≤ P := pCore_le_comap_zpowers1412 hK
  have hPS : P ≤ S := comap_zpowers_le1412 hK haS hQS
  have hP2 : IsPGroup 2 P := hS2.to_le hPS
  have hPY : P ≤ Y := comap_zpowers_le_comap_centralizer1412
  have hYP : Y ≤ normalizer (P : Set X) := comap_centralizer_le_normalizer1412
  have hYmap : Y.map π = centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
    map_comap_centralizer1412
  have hQn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hmemY : ∀ c ∈ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)), ∃ y ∈ Y, π y = c := by
    intro c hc
    rw [← hYmap] at hc
    exact hc
  by_contra hlt
  push Not at hlt
  have hW2 : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa [pow_two] using hW.2 _ w.2)⟩
  have hrel2 : (centralizer (A : Set X)).relIndex W ≤ 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hW2
    have hdvd : (centralizer (A : Set X)).relIndex W ∣ 2 ^ n := by
      rw [← hn]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card _ _)
    obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hr] at hlt ⊢
    have : r < 2 := by
      by_contra hr2
      push Not at hr2
      have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
      omega
    interval_cases r <;> norm_num
  have hrelA : ∀ e ∈ A, (centralizer ({e} : Set X)).relIndex W ≤ 2 := fun e he =>
    (Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he))
      (Sec3.relIndex_ne_zero_of_finite _ _)).trans hrel2
  set E : Subgroup (X ⧸ CFSG.pPrimeCore 3 X) := Lst ⊓ A.map π with hE
  have hAmapC : A.map π ≤ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
    rw [← hYmap]
    exact map_mono hAY
  have hEle : E ≤ Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
    le_inf inf_le_left (inf_le_right.trans hAmapC)
  have hAmapel := isElemTwo_map1412 π hAel
  have hEel : Sec3.IsElemTwo E :=
    ⟨fun x hx y hy => hAmapel.1 x hx.2 y hy.2, fun x hx => hAmapel.2 x hx.2⟩
  set CW : Subgroup X := centralizer (W : Set X) ⊓ Y with hCW
  have hCWY : Y ≤ normalizer (CW : Set X) := by
    intro y hy
    refine Sec3.mem_normalizer_of_conj_mem fun z hz => mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro w hw
      have hw' : y⁻¹ * w * y ∈ W := by
        have := (mem_normalizer_iff.mp (hWY (Y.inv_mem hy)) w).1 hw
        simpa using this
      have hzw := (mem_centralizer_iff.mp (mem_inf.mp hz).1) _ hw'
      calc w * (y * z * y⁻¹) = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by rw [hzw]
        _ = y * z * y⁻¹ * w := by group
    · exact Y.mul_mem (Y.mul_mem hy (mem_inf.mp hz).2) (Y.inv_mem hy)
  have hCWbot : CW.map π ⊓ (Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))) = ⊥ := by
    by_contra hne
    have hle := le_sup_of_map_inf_ne_bot1412 hK hout hCWY hLYmap hne
    apply hLYW
    refine le_centralizer_of_perfect_of_le_sup1412 hQ2 hLYp (hLYY.trans hWY)
      (hQP.trans (hPY.trans hWY)) (hle.trans (sup_le_sup_right inf_le_left _))
  rcases hout.words E hEle hEel hE4 with ⟨x, hxE, g, hg, q, k, hq, hq2, hk, hq3, hdvd⟩ |
    ⟨hEΩ, ⟨y, hy, hy8⟩, hgen⟩
  ·
    obtain ⟨e, heA, rfl⟩ := hxE.2
    obtain ⟨gh, hghY, rfl⟩ := hmemY g hg.2
    set u : Fin 2 → X := ![e, gh * e * gh⁻¹] with hu
    have huY : ∀ i, u i ∈ Y := by
      intro i
      fin_cases i
      · exact hAY heA
      · exact Y.mul_mem (Y.mul_mem hghY (hAY heA)) (Y.inv_mem hghY)
    have hun : ∀ i, u i ∈ normalizer (W : Set X) := fun i => hWY (huY i)
    have hu2 : ∀ i, (centralizer ({u i} : Set X)).relIndex W ≤ 2 := by
      intro i
      fin_cases i
      · exact hrelA e heA
      · change (centralizer ({gh * e * gh⁻¹} : Set X)).relIndex W ≤ 2
        rw [relIndex_centralizer_conj_of_mem_normalizer1412 (hWY hghY)]
        exact hrelA e heA
    set w : X := e * (gh * e * gh⁻¹) with hw
    have hwmem : w ∈ closure (Set.range u) :=
      mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
    obtain ⟨N, -, hpow, hN⟩ :=
      exists_pow_mem_centralizer_closure_prime_pow hW u hun (fun _ => 2) hu2 hwmem
    have hwY : w ∈ Y := Y.mul_mem (huY 0) (huY 1)
    have hπw : π w = π e * π gh * π e * (π gh)⁻¹ := by
      simp only [hw, map_mul, map_inv]
      group
    have hwL : π w ∈ Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) := by
      rw [hπw]
      have he' := hEle hxE
      exact mul_mem (mul_mem (mul_mem he' hg) he') (inv_mem hg)
    have h1 : π w ^ (2 * N) = 1 := by
      have hmem : π w ^ (2 * N) ∈ CW.map π ⊓
          (Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))) :=
        ⟨⟨w ^ (2 * N), ⟨hpow, pow_mem hwY _⟩, map_pow _ _ _⟩, pow_mem hwL _⟩
      rwa [hCWbot, mem_bot] at hmem
    rw [← hπw] at hdvd
    have hdvd2 : q ^ k ∣ N * 2 := by
      rw [mul_comm]
      exact hdvd.trans (orderOf_dvd_of_pow_eq_one h1)
    have hcop : Nat.Coprime (q ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    obtain ⟨e', he1, he', hediv⟩ := hN q k hq hq2 hk (hcop.dvd_of_dvd_mul_right hdvd2)
    have he2 : e' ≤ 2 := by
      have : 2 ^ e' ≤ 2 ^ 2 := by simpa using he'
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    interval_cases e'
    · have : q ^ k = 1 := Nat.eq_one_of_dvd_one (by simpa using hediv)
      have : 1 < q ^ k := Nat.one_lt_pow (by omega) hq.one_lt
      omega
    · exact hq3 (by simpa using hediv)
  ·
    have hE1 : E ≠ ⊥ := by
      intro hE0
      rw [hE0, Subgroup.card_bot] at hE4
      norm_num at hE4
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    obtain ⟨g₁, hg₁, g₂, hg₂, hΩD⟩ := hgen x x.2 (fun h1 => hx1 (Subtype.ext h1))
    obtain ⟨e, heA, hex⟩ := x.2.2
    obtain ⟨gh₁, hgh₁Y, rfl⟩ := hmemY g₁ hg₁.2
    obtain ⟨gh₂, hgh₂Y, rfl⟩ := hmemY g₂ hg₂.2
    set u : Fin 3 → X := ![e, gh₁ * e * gh₁⁻¹, gh₂ * e * gh₂⁻¹] with hu
    have huY : ∀ i, u i ∈ Y := by
      intro i
      fin_cases i
      · exact hAY heA
      · exact Y.mul_mem (Y.mul_mem hgh₁Y (hAY heA)) (Y.inv_mem hgh₁Y)
      · exact Y.mul_mem (Y.mul_mem hgh₂Y (hAY heA)) (Y.inv_mem hgh₂Y)
    have hu2 : ∀ i, (centralizer ({u i} : Set X)).relIndex W ≤ 2 := by
      intro i
      fin_cases i
      · exact hrelA e heA
      · change (centralizer ({gh₁ * e * gh₁⁻¹} : Set X)).relIndex W ≤ 2
        rw [relIndex_centralizer_conj_of_mem_normalizer1412 (hWY hgh₁Y)]
        exact hrelA e heA
      · change (centralizer ({gh₂ * e * gh₂⁻¹} : Set X)).relIndex W ≤ 2
        rw [relIndex_centralizer_conj_of_mem_normalizer1412 (hWY hgh₂Y)]
        exact hrelA e heA
    have hD : LY ≤ closure (Set.range u) ⊔ P := by
      have hΩmap : Ω ≤ (closure (Set.range u)).map π := by
        refine hΩD.trans ((Subgroup.closure_le _).mpr ?_)
        rintro _ (h0 | h1 | h2)
        · rw [h0, ← hex]
          exact mem_map_of_mem π (subset_closure ⟨0, rfl⟩)
        · rw [h1, ← hex]
          refine ⟨gh₁ * e * gh₁⁻¹, subset_closure ⟨1, rfl⟩, ?_⟩
          simp only [map_mul, map_inv]
        · rw [Set.mem_singleton_iff] at h2
          rw [h2, ← hex]
          refine ⟨gh₂ * e * gh₂⁻¹, subset_closure ⟨2, rfl⟩, ?_⟩
          simp only [map_mul, map_inv]
      intro l hl
      have hl' : l ∈ ((closure (Set.range u)).map π).comap π := hΩmap (hLYmap ▸ mem_map_of_mem π hl)
      rw [comap_map_eq, QuotientGroup.ker_mk', hK] at hl'
      exact (sup_le_sup_left hQP _) hl'
    obtain ⟨yh, hyhY, rfl⟩ := hmemY y hy.2
    obtain ⟨s', m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos yh).ne'
    set y₀ := yh ^ m with hy₀
    have hy₀Y : y₀ ∈ Y := pow_mem hyhY m
    have hy₀2 : ∃ n : ℕ, y₀ ^ 2 ^ n = 1 :=
      ⟨s', by rw [hy₀, ← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]⟩
    have hπy₀ : orderOf (π y₀) = 8 := by
      rw [hy₀, map_pow, orderOf_pow' _ (by rintro rfl; exact absurd hm (by decide)),
        hy8]
      have hcop : Nat.gcd 8 m = 1 := by
        have : Nat.Coprime 8 m := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
        exact this
      rw [hcop, Nat.div_one]
    have hTR : ∀ C : Subgroup X, C ≤ Y → Y ≤ normalizer (C : Set X) → y₀ ^ 4 ∈ C →
        LY ≤ C ⊔ P := by
      intro C hCY hYC hy₀C
      have hne : C.map π ⊓ (Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))) ≠ ⊥ := by
        intro hbot
        have hmem : π (y₀ ^ 4) ∈ C.map π ⊓
            (Lst ⊓ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))) := by
          refine ⟨mem_map_of_mem π hy₀C, ?_⟩
          rw [map_pow, hy₀, map_pow]
          exact pow_mem (pow_mem hy _) 4
        rw [hbot, mem_bot, map_pow] at hmem
        have := orderOf_dvd_of_pow_eq_one hmem
        rw [hπy₀] at this
        norm_num at this
      exact (le_sup_of_map_inf_ne_bot1412 hK hout hYC hLYmap hne).trans
        (sup_le_sup_left hQP _)
    exact false_of_case_eight1412 hPY hP2 hYP (hWP) hW hWY hLYY hLYp hLYn hLYW huY hu2 hD
      hy₀Y hy₀2 hTR

end Star2

section PartB

open scoped commutatorElement in
theorem commutator_eq_self_of_simple1412 {G : Type*} [Group G] {Ω : Subgroup G}
    [IsSimpleGroup Ω] (hnc : ∃ x y : Ω, x * y ≠ y * x) : ⁅Ω, Ω⁆ = Ω := by
  have h1 : ⁅(⊤ : Subgroup Ω), (⊤ : Subgroup Ω)⁆ = ⊤ := by
    rcases (⁅(⊤ : Subgroup Ω), (⊤ : Subgroup Ω)⁆).normal_of_characteristic.eq_bot_or_eq_top
      with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      have hc : ⁅x, y⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
      rw [commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
    · exact h
  have h2 := congrArg (Subgroup.map Ω.subtype) h1
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2

variable (hK : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X)
include hK

theorem exists_perfect_le_centralizer_fourChar_three1412 (h : Hyp1411 X L S)
    (hstar : Star1412 X S)
    (hrank : CFSG.Open.twoRank ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2)
    (hidx : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2)
    (hout : ∀ b : X ⧸ CFSG.pPrimeCore 3 X, b ∉ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) →
      orderOf b = 2 → OuterInput1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) b) :
    ∃ b : X ⧸ CFSG.pPrimeCore 3 X, b ∉ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ∧
      orderOf b = 2 ∧ ∃ LY : Subgroup X,
        LY.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) =
          omegaOut1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) b ∧
        LY ≤ centralizer (Sec18.fourChar S 3 : Set X) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hLn : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  obtain ⟨A₀, hA₀, hA₀Q, hA₀8, hE4, a, haA, haL⟩ :=
    exists_outer_of_star1412 hK hstar hrank hLn hidx
  have ha2 : a * a = 1 := hA₀.2.1.2 a haA
  have hb1 : π a ≠ 1 := fun h1 => haL (h1 ▸ (L.map π).one_mem)
  have hb2 : orderOf (π a) = 2 := orderOf_eq_prime (by rw [sq, ← map_mul, ha2, map_one]) hb1
  have hob := hout (π a) haL hb2
  refine ⟨π a, haL, hb2, ?_⟩
  set b := π a with hb
  set Lst := L.map π with hLst
  set Ω := omegaOut1412 Lst b with hΩ
  set Y := (centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X))).comap π with hY
  set P := (zpowers b).comap π with hP
  set SY := S ⊓ Y with hSY
  have hS2 : IsPGroup 2 S := h.2.2.2.2.1
  have hQS : CFSG.pCore 2 X ≤ S := h.2.2.2.2.2.1
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 X) := hS2.to_le hQS
  have hCQ := centralizer_pCore_le_of_hyp1411 h
  have hQP : CFSG.pCore 2 X ≤ P := pCore_le_comap_zpowers1412 hK
  have haS : a ∈ S := hA₀.1 haA
  have hPS : P ≤ S := comap_zpowers_le1412 hK haS hQS
  have hP2 : IsPGroup 2 P := hS2.to_le hPS
  have hPY : P ≤ Y := comap_zpowers_le_comap_centralizer1412
  have hYP : Y ≤ normalizer (P : Set X) := comap_centralizer_le_normalizer1412
  have hYmap : Y.map π = centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
    map_comap_centralizer1412
  have hA₀Y : A₀ ≤ Y := by
    intro e he
    rw [mem_comap, mem_centralizer_singleton_iff, hb, ← map_mul, ← map_mul,
      hA₀.2.1.1 e he a haA]
  have hPSY : P ≤ SY := le_inf hPS hPY
  have hA₀SY : A₀ ≤ SY := le_inf hA₀.1 hA₀Y
  have hrankSY : CFSG.pRank 2 SY = CFSG.pRank 2 S := by
    apply le_antisymm
    · rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact CFSG.SectionRank.pRank_mono Nat.one_lt_two inf_le_left
    · have h1 := Sec3.card_le_two_pow_pRank hA₀SY hA₀.2.1
      rw [hA₀.2.2, Nat.sub_zero] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hfam : ∀ (j : ℕ) (B : Subgroup X), B ∈ Sec3.famG SY j → B ∈ Sec3.famG S j :=
    fun j B hB => ⟨hB.1.trans inf_le_left, hB.2.1, by rw [hB.2.2, hrankSY]⟩
  have hA₀' : A₀ ∈ Sec3.famG SY 0 := ⟨hA₀SY, hA₀.2.1, by rw [hA₀.2.2, hrankSY]⟩
  have hcardA₀ := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 X) (K := A₀)
  rw [hA₀8, hA₀.2.2, Nat.sub_zero] at hcardA₀
  have hm3 : 3 ≤ CFSG.pRank 2 S := by
    by_contra hm
    push Not at hm
    have hpos : 0 < Nat.card ↥(CFSG.pCore 2 X ⊓ A₀) := Nat.card_pos
    have : 2 ^ CFSG.pRank 2 S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hAPmap : (A₀ ⊓ P).map π = zpowers b := by
    refine le_antisymm ((map_mono inf_le_right).trans (map_comap_le _ _)) ?_
    rw [zpowers_le]
    exact ⟨a, ⟨haA, show π a ∈ zpowers b from mem_zpowers b⟩, rfl⟩
  have hcardAP := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 X) (K := A₀ ⊓ P)
  rw [relIndex_eq_card_map1412 hK, hAPmap, Nat.card_zpowers, hb2,
    show CFSG.pCore 2 X ⊓ (A₀ ⊓ P) = CFSG.pCore 2 X ⊓ A₀ by
      rw [inf_comm A₀, ← inf_assoc, inf_eq_left.mpr hQP]] at hcardAP
  have hB : A₀ ⊓ P ∈ Sec3.famG SY 2 := by
    refine ⟨inf_le_left.trans hA₀SY, ⟨fun x hx y hy => hA₀.2.1.1 x hx.1 y hy.1,
      fun x hx => hA₀.2.1.2 x hx.1⟩, ?_⟩
    rw [hrankSY, ← hcardAP]
    have h8 : 2 ^ CFSG.pRank 2 S = 2 ^ 2 * 2 ^ (CFSG.pRank 2 S - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [h8] at hcardA₀
    have hpos : 0 < Nat.card ↥(CFSG.pCore 2 X ⊓ A₀) := Nat.card_pos
    nlinarith
  have hO2 : ∀ K' : Subgroup X, K' ≤ Y → (∀ g ∈ Y, ∀ k ∈ K', g * k * g⁻¹ ∈ K') →
      IsPGroup 2 K' → K' ≤ P := by
    intro K' hK'Y hK'n hK'2
    have hle : K'.map π ≤ zpowers b := by
      refine le_zpowers_of_isPGroup_normal1412 hidx haL hob ?_ ?_ (hK'2.map π)
      · rw [← hYmap]
        exact map_mono hK'Y
      · intro c hc
        obtain ⟨y, hy, rfl⟩ : c ∈ Y.map π := by rw [hYmap]; exact hc
        refine Sec3.mem_normalizer_of_conj_mem fun z hz => ?_
        obtain ⟨k, hk, rfl⟩ := hz
        exact ⟨y * k * y⁻¹, hK'n y hy k hk, by simp only [map_mul, map_inv]⟩
    intro k hk
    exact hle (mem_map_of_mem π hk)
  set W := Sec3.omegaG (pJ1412 SY P 2) with hW
  have hJSY : Sec3.jG SY 2 ≤ SY := sSup_le fun _ hA => hA.1
  have hEW : Sec3.omegaG (Sec3.jG SY 2) ≤ W :=
    omegaG_jG_le_omegaG_pJ1412 (H := Y) hQP hPSY hP2 hQ2 hCQ
      (fun g hg p hp => (mem_normalizer_iff.mp (hYP hg) p).1 hp) hO2
      ((Sec3.omegaG_le _).trans (hJSY.trans inf_le_right))
      (fun t ht e he => Sec3.conj_mem_omegaG_jG ht he) (by rw [hrankSY]; omega) hB inf_le_right
  have hS4 : Sec18.fourChar S 3 ≤ Sec3.omegaG (Sec3.jG SY 2) := by
    rw [Sec18.Item181ThreeProof.fourChar_three]
    have hS4A : Sec3.omegaG (Sec3.jG S 2) ≤ A₀ :=
      omegaG_jG_le_of_mem_famG_zero1412 hA₀ (by omega)
        ((Sec3.omegaG_le _).trans (sSup_le fun _ hA => hA.1))
    intro z hz
    refine ⟨mem_jG_of_mem_famG_zero1412 hA₀' (by rw [hrankSY]; omega) (hS4A hz),
      fun y hy => hz.2.1 y ?_, hz.2.2⟩
    exact sSup_le (fun B hB => Sec3.le_jG (hfam 2 B hB)) hy
  have hWel : Sec3.IsElemTwo W := Sec3.isElemTwo_omegaG _
  have hWP : W ≤ P := (Sec3.omegaG_le _).trans (pJ1412_le SY P 2)
  have hWY : Y ≤ normalizer (W : Set X) := by
    intro g hg
    refine Sec3.mem_normalizer_of_conj_mem fun w hw => ?_
    exact conj_mem_omegaG_pJ1412 hPSY (fun p hp => (mem_normalizer_iff.mp (hYP hg) p).1 hp)
      (fun p hp => by
        have := (mem_normalizer_iff.mp (hYP (Y.inv_mem hg)) p).1 hp
        simpa using this) hw
  set LY := CFSG.Quasithin.perfectCore (Ω.comap π) with hLYdef
  have hΩC : Ω ≤ centralizer ({b} : Set (X ⧸ CFSG.pPrimeCore 3 X)) :=
    (omegaOut1412_le Lst b).trans inf_le_right
  have hΩY : Ω.comap π ≤ Y := comap_mono hΩC
  have hLYY : LY ≤ Y := (CFSG.Quasithin.perfectCore_le _).trans hΩY
  have hLYp : ⁅LY, LY⁆ = LY := CFSG.Quasithin.perfectCore_perfect _
  have hYΩ : Y ≤ normalizer ((Ω.comap π : Subgroup X) : Set X) := by
    intro g hg
    refine Sec3.mem_normalizer_of_conj_mem fun z hz => ?_
    rw [mem_comap] at hz ⊢
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hob.norm hg) _).1 hz
  have hLYn : Y ≤ normalizer (LY : Set X) :=
    hYΩ.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
  have hΩp : ⁅Ω, Ω⁆ = Ω := by
    have : IsSimpleGroup Ω := hob.simple
    exact commutator_eq_self_of_simple1412 hob.noncomm
  have hLYmap : LY.map π = Ω := by
    rw [hLYdef, CFSG.Quasithin.map_perfectCore,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hΩp]
  have hLYW : LY ≤ centralizer (W : Set X) := by
    by_contra hLYW
    have h4 := four_le_relIndex_of_star1412 hK h hob haS hA₀Y hA₀.2.1 hE4 hWel hWP hWY hLYY
      hLYp hLYn hLYmap hLYW
    have hA' := sup_mem_famG_zero_of_pJ1412 hPSY (by rw [hrankSY]; omega) hA₀' hB le_rfl
      (by simpa using h4)
    have hA'S := hfam 0 _ hA'
    have hA'P : (A₀ ⊓ P) ⊔ W ≤ P := sup_le inf_le_right hWP
    have haA' : a ∈ (A₀ ⊓ P) ⊔ W :=
      mem_sup_left ⟨haA, show π a ∈ zpowers b from mem_zpowers b⟩
    have haQ : a ∉ CFSG.pCore 2 X := fun haQ => hb1 ((mk'_eq_one_iff1412 hK a).2 haQ)
    have h8 : (CFSG.pCore 2 X).relIndex ((A₀ ⊓ P) ⊔ W) = 8 :=
      hstar.2.2 _ hA'S (fun hle => haQ (hle haA'))
    have h2 := relIndex_le_two_of_le_comap_zpowers1412 hK ha2 hA'P
    omega
  refine ⟨LY, hLYmap, ?_⟩
  intro l hl
  rw [mem_centralizer_iff]
  intro z hz
  exact (mem_centralizer_iff.mp (hLYW hl) z (hEW (hS4 hz)))

theorem sup_normalizer_fourChar_three_eq_top_of_star1412 (h : Hyp1411 X L S)
    (hstar : Star1412 X S)
    (hrank : CFSG.Open.twoRank ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2)
    (hidx : (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).index ≤ 2)
    (hout : ∀ b : X ⧸ CFSG.pPrimeCore 3 X, b ∉ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) →
      orderOf b = 2 → OuterInput1412 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) b)
    {x : X} (hxL : x ∈ L) (hx3 : orderOf x = 3) :
    normalizer (zpowers x : Set X) ⊔ normalizer (Sec18.fourChar S 3 : Set X) = ⊤ := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  obtain ⟨b, hbL, hb2, LY, hLYmap, hLYC⟩ :=
    exists_perfect_le_centralizer_fourChar_three1412 hK h hstar hrank hidx hout
  have hob := hout b hbL hb2
  have hS2 : IsPGroup 2 S := h.2.2.2.2.1
  have hQS : CFSG.pCore 2 X ≤ S := h.2.2.2.2.2.1
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 X) := hS2.to_le hQS
  have hSN : S ≤ normalizer (Sec18.fourChar S 3 : Set X) := by
    intro s hs
    rw [Sec18.Item181ThreeProof.fourChar_three]
    exact Sec3.mem_normalizer_of_conj_mem fun e he => Sec3.conj_mem_omegaG_jG hs he
  have hΩM : omegaOut1412 (L.map π) b ≤ (normalizer (Sec18.fourChar S 3 : Set X)).map π := by
    rw [← hLYmap]
    exact map_mono (hLYC.trans (Subgroup.centralizer_le_normalizer _))
  have hxQ : x ∉ CFSG.pCore 2 X := by
    intro hxQ
    obtain ⟨n, hn⟩ := hQ2 ⟨x, hxQ⟩
    have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : 3 ∣ 2 ^ n := hx3 ▸ orderOf_dvd_of_pow_eq_one hxn
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hπx3 : orderOf (π x) = 3 := by
    have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
    refine orderOf_eq_prime ?_ fun h1 => hxQ ((mk'_eq_one_iff1412 hK x).1 h1)
    rw [← map_pow, hx3', map_one]
  exact sup_normalizer_eq_top_of_gen1412 h hK hxL hx3 hSN hΩM
    (hob.gen (π x) (mem_map_of_mem π hxL) hπx3)

end PartB

end Star

end CFSG.RankThree.PartTwo.Sec20
