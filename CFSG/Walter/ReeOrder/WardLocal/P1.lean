module

public import CFSG.Walter.ReeOrder.WardLocal.Sylow1
public import CFSG.Walter.ReeOrder.WardLocal.Group

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)}

@[expose] noncomputable def CF (S : WardSetup G PSL(2, K) q (-1)) : Subgroup G :=
  Subgroup.centralizer (FF S : Set G)

@[expose] noncomputable def PP1 (S : WardSetup G PSL(2, K) q (-1)) : Subgroup G :=
  ((default : Sylow 3 (CF S)) : Subgroup (CF S)).map (CF S).subtype

omit [CharP K 3] in
theorem FF_le_CF : FF S ≤ CF S := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun _ hy => FF_comm hy hx

omit [CharP K 3] in
theorem J_mem_CF : S.J ∈ CF S :=
  Subgroup.mem_centralizer_iff.mpr fun _ hy => FF_comm_J hy

omit [CharP K 3] in
theorem CF_le_CT : CF S ≤ Subgroup.centralizer ({TT S} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hx) _ TT_mem).symm

omit [CharP K 3] in
theorem PP1_le_CF : PP1 S ≤ CF S := Subgroup.map_subtype_le _

omit [CharP K 3] in
theorem isPGroup_PP1 : IsPGroup 3 (PP1 S) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ((default : Sylow 3 (CF S)).2).map _

variable {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))

include hq hcT in
omit [CharP K 3] in
theorem card_CF : ∃ i ≤ 2 * (2 * k + 1), Nat.card (CF S) = 2 * 3 ^ i := by
  have h1 : Nat.card (CF S) ∣ 2 * q ^ 2 :=
    (Subgroup.card_dvd_of_le CF_le_CT).trans hcT
  have h2 : 2 ∣ Nat.card (CF S) := by
    have := Subgroup.orderOf_dvd_natCard _ (J_mem_CF (S := S))
    rwa [S.orderOf_J] at this
  obtain ⟨c', hc'⟩ := h2
  have h3 : c' ∣ 3 ^ (2 * (2 * k + 1)) := by
    rw [hc', hq, ← pow_mul, mul_comm (2 * k + 1) 2] at h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h1
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  exact ⟨i, hi, hc'⟩

include hq hcT in
omit [CharP K 3] in
theorem card_CF_eq : Nat.card (CF S) = 2 * Nat.card (PP1 S) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, -, hi⟩ := card_CF hq hcT
  have hP : Nat.card (PP1 S) = Nat.card (default : Sylow 3 (CF S)) := by
    rw [PP1, Subgroup.card_map_of_injective (CF S).subtype_injective]
  rw [hP, Sylow.card_eq_multiplicity, hi]
  congr 1
  rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), zero_add,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]

include hq hcT in
omit [CharP K 3] in
theorem mem_PP1 {x : G} (hx : x ∈ CF S) (hodd : Odd (orderOf x)) : x ∈ PP1 S :=
  odd_mem_of_card_eq_two_mul PP1_le_CF (card_CF_eq hq hcT) hx hodd

include hq hcT in
theorem FF_le_PP1 : FF S ≤ PP1 S := by
  intro x hx
  refine mem_PP1 hq hcT (FF_le_CF hx) ?_
  have h3 := FF_pow_three hx
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · rw [h]; exact odd_one
  · rw [h]; decide

omit [CharP K 3] in
theorem conj_mem_CF {d x : G} (hd : d ∈ RR S) (hx : x ∈ CF S) : d * x * d⁻¹ ∈ CF S := by
  rw [CF, Subgroup.mem_centralizer_iff] at hx ⊢
  intro f hf
  have hdN := RR_le_normalizer hd
  have hf' : d⁻¹ * f * d ∈ FF S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) f).mp hf
    simpa using this
  have h := hx _ hf'
  calc f * (d * x * d⁻¹) = d * ((d⁻¹ * f * d) * x) * d⁻¹ := by group
    _ = d * (x * (d⁻¹ * f * d)) * d⁻¹ := by rw [h]
    _ = d * x * d⁻¹ * f := by group

include hq hcT in
omit [CharP K 3] in
theorem RR_le_normalizer_PP1 : RR S ≤ Subgroup.normalizer (PP1 S : Set G) := by
  have hconj : ∀ d ∈ RR S, ∀ x ∈ PP1 S, d * x * d⁻¹ ∈ PP1 S := by
    intro d hd x hx
    refine mem_PP1 hq hcT (conj_mem_CF hd (PP1_le_CF hx)) ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp isPGroup_PP1) ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hN
    rw [hN]; exact Odd.pow (by decide)
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj d hd x, fun h => ?_⟩
  have := hconj d⁻¹ (Subgroup.inv_mem _ hd) _ h
  simpa [mul_assoc] using this

include hq hK hcT in
theorem card_PP1_cases : Nat.card (PP1 S) = q ∨ Nat.card (PP1 S) = q ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi, hci⟩ := card_CF hq hcT
  have hP : Nat.card (PP1 S) = 3 ^ i := by
    have := card_CF_eq hq hcT (S := S); omega
  have hfpf := card_dvd_card_sub_one_of_fpf (RR S) (PP1 S) (RR_le_normalizer_PP1 hq hcT)
    (fun d hd hd1 h hh hdh => by
      by_contra h1
      obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp isPGroup_PP1) ⟨h, hh⟩
      rw [Subgroup.orderOf_mk] at hN
      have hN0 : N ≠ 0 := by
        rintro rfl; rw [pow_zero, orderOf_eq_one_iff] at hN; exact h1 hN
      have h3 : 3 ∣ orderOf h := by rw [hN]; exact dvd_pow_self 3 hN0
      have hcomm : h * d = d * h := by
        calc h * d = d * h * d⁻¹ * d := by rw [hdh]
          _ = d * h := by group
      exact not_three_dvd_of_commute_RR hK hq hd hd1 hcomm h3)
  have hRR := card_RR (S := S) hK hq
  rw [hP, show Nat.card (RR S) = (3 ^ (2 * k + 1) - 1) / 2 by omega] at hfpf
  have hni := dvd_of_pow_three_modEq hfpf
  have hqi : q ∣ 3 ^ i := by
    have := Subgroup.card_dvd_of_le (FF_le_PP1 (S := S) hq hcT)
    rwa [card_FF, hK, hP] at this
  have hle : 2 * k + 1 ≤ i := by
    rw [hq] at hqi
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hqi
  obtain ⟨t, rfl⟩ := hni
  have ht : t = 1 ∨ t = 2 := by
    rcases Nat.lt_or_ge t 3 with h | h
    · interval_cases t <;> simp_all
    · exfalso; nlinarith
  rcases ht with rfl | rfl
  · left; rw [hP, hq, mul_one]
  · right; rw [hP, hq, ← pow_mul, mul_comm]

omit [Fintype G] in
@[expose] def zcen (P : Subgroup G) : Subgroup G := (Subgroup.center P).map P.subtype

omit [Fintype G] in
theorem mem_zcen {P : Subgroup G} {z : G} : z ∈ zcen P ↔ z ∈ P ∧ ∀ p ∈ P, z * p = p * z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, fun p hp => ?_⟩
    have := (Subgroup.mem_center_iff.mp hw) ⟨p, hp⟩
    exact (congrArg Subtype.val this).symm
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun p => Subtype.ext (h p.1 p.2).symm, rfl⟩

omit [Fintype G] in
theorem centralizer_inv (x : G) :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor <;> intro h
  · exact (calc x * g = x * (g * x⁻¹) * x := by group
      _ = x * (x⁻¹ * g) * x := by rw [h]
      _ = g * x := by group).symm
  · exact (calc x⁻¹ * g = x⁻¹ * (g * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * g) * x⁻¹ := by rw [h]
      _ = g * x⁻¹ := by group).symm

include hq hG in
omit [CharP K 3] [DecidableEq K] [Fintype K] in
theorem card_sylow3 (P : Sylow 3 G) : Nat.card P = q ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, Block.three_part hq hG]

omit [CharP K 3] in
theorem zcen_le_CF {P : Subgroup G} (hP : PP1 S ≤ P) (hcT' : FF S ≤ PP1 S) : zcen P ≤ CF S := by
  intro z hz
  rw [CF, Subgroup.mem_centralizer_iff]
  intro f hf
  exact ((mem_zcen.mp hz).2 f (hP (hcT' hf))).symm

include hq hcT in
omit [CharP K 3] in
theorem zcen_le_PP1 {P : Sylow 3 G} (hP : PP1 S ≤ P) (hFF : FF S ≤ PP1 S) :
    zcen (P : Subgroup G) ≤ PP1 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro z hz
  refine mem_PP1 hq hcT (zcen_le_CF hP hFF hz) ?_
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp P.2) ⟨z, (mem_zcen.mp hz).1⟩
  rw [Subgroup.orderOf_mk] at hN
  rw [hN]; exact Odd.pow (by decide)

include hq hK hcT hG in
theorem zcen_no_involution {P : Sylow 3 G} {z t : G} (hz : z ∈ zcen (P : Subgroup G))
    (hz1 : z ≠ 1) (ht : orderOf t = 2) (hzt : z * t = t * z) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    P.2.to_le (Subgroup.zpowers_le.mpr (mem_zcen.mp hz).1)
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((mem_zcen.mp hz).2 p hp).symm
  have hcz : q ^ 3 ≤ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    rw [← card_sylow3 hq hG P]
    exact Subgroup.card_le_of_le hle
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hcTle : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ≤ 2 * q ^ 2 :=
    Nat.le_of_dvd (by positivity) hcT
  rcases isConj_T_of_commute (S := S) hq hK hz1 hzp ht hzt with h | h
  · rw [card_centralizer_of_isConj h] at hcz
    nlinarith
  · rw [card_centralizer_of_isConj h, centralizer_inv] at hcz
    nlinarith

include hq hK hcT hG in
theorem zcen_inf_FF {P : Sylow 3 G} {z : G} (hz : z ∈ zcen (P : Subgroup G)) (hzF : z ∈ FF S) :
    z = 1 := by
  by_contra hz1
  exact zcen_no_involution hq hK hcT hG hz hz1 S.orderOf_J (FF_comm_J hzF)

omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem exists_zcen_ne_one [Finite G] (P : Sylow 3 G) (hP : 1 < Nat.card P) :
    ∃ z ∈ zcen (P : Subgroup G), z ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hP
  obtain ⟨w, hw, hw1⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp (P.2.bot_lt_center)).2
  refine ⟨w, ⟨w, hw, rfl⟩, fun h => hw1 ?_⟩
  rw [Subgroup.mem_bot]
  exact Subtype.ext h

include hq hK hcT hG in
theorem card_PP1 : Nat.card (PP1 S) = q ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := (isPGroup_PP1 (S := S)).exists_le_sylow
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hPc : 1 < Nat.card P := by
    rw [card_sylow3 hq hG P]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨z, hz, hz1⟩ := exists_zcen_ne_one P hPc
  have hFF := FF_le_PP1 (S := S) hq hcT
  have hzP := zcen_le_PP1 hq hcT hP hFF hz
  have hzF : z ∉ FF S := fun h => hz1 (zcen_inf_FF hq hK hcT hG hz h)
  rcases card_PP1_cases hq hK hcT with h | h
  · exfalso
    have heq : FF S = PP1 S := Subgroup.eq_of_le_of_card_ge hFF (by rw [h, card_FF, hK])
    exact hzF (heq ▸ hzP)
  · exact h

include hq hK in
omit [CharP K 3] in
theorem card_RR_invariant {H : Subgroup G} (hH : IsPGroup 3 H)
    (hRH : RR S ≤ Subgroup.normalizer (H : Set G)) : ∃ t : ℕ, Nat.card H = q ^ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ := hH.exists_card_eq
  have hfpf := card_dvd_card_sub_one_of_fpf (RR S) H hRH
    (fun d hd hd1 h hh hdh => by
      by_contra h1
      obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨h, hh⟩
      rw [Subgroup.orderOf_mk] at hN
      have hN0 : N ≠ 0 := by
        rintro rfl; rw [pow_zero, orderOf_eq_one_iff] at hN; exact h1 hN
      have h3 : 3 ∣ orderOf h := by rw [hN]; exact dvd_pow_self 3 hN0
      have hcomm : h * d = d * h := by
        calc h * d = d * h * d⁻¹ * d := by rw [hdh]
          _ = d * h := by group
      exact not_three_dvd_of_commute_RR hK hq hd hd1 hcomm h3)
  have hRR := card_RR (S := S) hK hq
  rw [hi, show Nat.card (RR S) = (3 ^ (2 * k + 1) - 1) / 2 by omega] at hfpf
  obtain ⟨t, rfl⟩ := dvd_of_pow_three_modEq hfpf
  exact ⟨t, by rw [hi, hq, pow_mul]⟩

include hq hK hcT hG in
theorem PP1_comm {x y : G} (hx : x ∈ PP1 S) (hy : y ∈ PP1 S) : x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := zcen (PP1 S) with hZ
  have hZRR : RR S ≤ Subgroup.normalizer (Z : Set G) := by
    have hconj : ∀ d ∈ RR S, ∀ z ∈ Z, d * z * d⁻¹ ∈ Z := by
      intro d hd z hz
      obtain ⟨hzP, hzc⟩ := mem_zcen.mp hz
      have hdN := RR_le_normalizer_PP1 hq hcT hd
      refine mem_zcen.mpr ⟨(Subgroup.mem_normalizer_iff.mp hdN z).mp hzP, fun p hp => ?_⟩
      have hp' : d⁻¹ * p * d ∈ PP1 S := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) p).mp hp
        simpa using this
      have := hzc _ hp'
      calc d * z * d⁻¹ * p = d * (z * (d⁻¹ * p * d)) * d⁻¹ := by group
        _ = d * ((d⁻¹ * p * d) * z) * d⁻¹ := by rw [this]
        _ = p * (d * z * d⁻¹) := by group
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj d hd x, fun h => ?_⟩
    have := hconj d⁻¹ (Subgroup.inv_mem _ hd) _ h
    simpa [mul_assoc] using this
  have hZp : IsPGroup 3 Z := (isPGroup_PP1 (S := S)).to_le (Subgroup.map_subtype_le _)
  obtain ⟨t, ht⟩ := card_RR_invariant hq hK hZp hZRR
  have hFZ : FF S ≤ Z := by
    intro f hf
    refine mem_zcen.mpr ⟨FF_le_PP1 hq hcT hf, fun p hp => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (PP1_le_CF hp)) f hf
  obtain ⟨P, hP⟩ := (isPGroup_PP1 (S := S)).exists_le_sylow
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hPc : 1 < Nat.card P := by
    rw [card_sylow3 hq hG P]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨z, hz, hz1⟩ := exists_zcen_ne_one P hPc
  have hzP1 := zcen_le_PP1 hq hcT hP (FF_le_PP1 hq hcT) hz
  have hzZ : z ∈ Z := mem_zcen.mpr ⟨hzP1, fun p hp => (mem_zcen.mp hz).2 p (hP hp)⟩
  have hzF : z ∉ FF S := fun h => hz1 (zcen_inf_FF hq hK hcT hG hz h)
  have hZle : Nat.card Z ≤ q ^ 2 := by
    rw [← card_PP1 hq hK hcT hG]
    exact Subgroup.card_le_of_le (Subgroup.map_subtype_le _)
  have hZgt : q < Nat.card Z := by
    have hle := Subgroup.card_le_of_le hFZ
    rw [card_FF, hK] at hle
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have heq : FF S = Z := Subgroup.eq_of_le_of_card_ge hFZ (by rw [card_FF, hK, h])
      exact hzF (heq ▸ hzZ)
  have ht2 : t = 2 := by
    rw [ht] at hZle hZgt
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t <;> simp_all
    · rcases h.lt_or_eq with h | h
      · exfalso
        have : q ^ 2 < q ^ t := Nat.pow_lt_pow_right (by omega) h
        omega
      · exact h.symm
  have hZeq : Z = PP1 S := Subgroup.eq_of_le_of_card_ge (Subgroup.map_subtype_le _)
    (by rw [card_PP1 hq hK hcT hG, ht, ht2])
  have hxZ : x ∈ Z := hZeq ▸ hx
  exact (mem_zcen.mp hxZ).2 y hy

include hq hK hcT hG in
theorem PP1_pow_three {x : G} (hx : x ∈ PP1 S) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ PP1 S ∧ y ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rw [(Commute.mul_pow (PP1_comm hq hK hcT hG ha hb) 3), ha3, hb3, one_mul]
      one_mem' := ⟨Subgroup.one_mem _, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha3, inv_one]⟩ }
  have hΩP : Ω ≤ PP1 S := fun y hy => hy.1
  have hΩp : IsPGroup 3 Ω := (isPGroup_PP1 (S := S)).to_le hΩP
  have hΩRR : RR S ≤ Subgroup.normalizer (Ω : Set G) := by
    have hconj : ∀ d ∈ RR S, ∀ y ∈ Ω, d * y * d⁻¹ ∈ Ω := by
      rintro d hd y ⟨hy, hy3⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (RR_le_normalizer_PP1 hq hcT hd) y).mp hy, ?_⟩
      rw [← MulAut.conj_apply, ← map_pow, hy3, map_one]
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj d hd y, fun h => ?_⟩
    have := hconj d⁻¹ (Subgroup.inv_mem _ hd) _ h
    simpa [mul_assoc] using this
  have hFΩ : FF S ≤ Ω := fun f hf => ⟨FF_le_PP1 hq hcT hf, FF_pow_three hf⟩
  obtain ⟨t, ht⟩ := card_RR_invariant hq hK hΩp hΩRR
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hle : Nat.card Ω ≤ q ^ 2 := by
    rw [← card_PP1 hq hK hcT hG]; exact Subgroup.card_le_of_le hΩP
  have hge : q ≤ Nat.card Ω := by
    have := Subgroup.card_le_of_le hFΩ
    rwa [card_FF, hK] at this
  obtain ⟨P, hP⟩ := (isPGroup_PP1 (S := S)).exists_le_sylow
  have hPc : 1 < Nat.card P := by
    rw [card_sylow3 hq hG P]
    calc 1 < 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
  obtain ⟨z, hz, hz1⟩ := exists_zcen_ne_one P hPc
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp P.2) ⟨z, (mem_zcen.mp hz).1⟩
  rw [Subgroup.orderOf_mk] at hN
  have hN0 : N ≠ 0 := by
    rintro rfl; rw [pow_zero, orderOf_eq_one_iff] at hN; exact hz1 hN
  set w := z ^ 3 ^ (N - 1) with hw
  have hwo : orderOf w = 3 := by
    rw [hw, orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hN,
      Nat.gcd_eq_right (pow_dvd_pow 3 (Nat.sub_le N 1)),
      Nat.pow_div (Nat.sub_le N 1) (by norm_num), show N - (N - 1) = 1 by omega, pow_one]
  have hwz : w ∈ zcen (P : Subgroup G) := Subgroup.pow_mem _ hz _
  have hw1 : w ≠ 1 := by
    intro h; rw [h, orderOf_one] at hwo; omega
  have hwΩ : w ∈ Ω := ⟨zcen_le_PP1 hq hcT hP (FF_le_PP1 hq hcT) hwz, by
    rw [← hwo, pow_orderOf_eq_one]⟩
  have hwF : w ∉ FF S := fun h => hw1 (zcen_inf_FF hq hK hcT hG hwz h)
  have ht2 : t = 2 := by
    rw [ht] at hle hge
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t
      · simp at hge; omega
      · exfalso
        have heq : FF S = Ω := Subgroup.eq_of_le_of_card_ge hFΩ (by rw [card_FF, hK, ht, pow_one])
        exact hwF (heq ▸ hwΩ)
    · rcases h.lt_or_eq with h | h
      · exfalso
        have : q ^ 2 < q ^ t := Nat.pow_lt_pow_right (by omega) h
        omega
      · exact h.symm
  have heq : Ω = PP1 S := Subgroup.eq_of_le_of_card_ge hΩP
    (by rw [card_PP1 hq hK hcT hG, ht, ht2])
  exact (heq ▸ hx : x ∈ Ω).2

include hq hK hcT hG in
theorem CT_eq_CF : Subgroup.centralizer ({TT S} : Set G) = CF S ∧
    Nat.card (Subgroup.centralizer ({TT S} : Set G)) = 2 * q ^ 2 := by
  have hCF : Nat.card (CF S) = 2 * q ^ 2 := by
    rw [card_CF_eq hq hcT, card_PP1 hq hK hcT hG]
  have hle := Subgroup.card_le_of_le (CF_le_CT (S := S))
  have hq0 : 0 < q := by rw [hq]; positivity
  have hcTle := Nat.le_of_dvd (by positivity) hcT
  have heq : CF S = Subgroup.centralizer ({TT S} : Set G) :=
    Subgroup.eq_of_le_of_card_ge CF_le_CT (by omega)
  exact ⟨heq.symm, by rw [← heq, hCF]⟩

end CFSG.Walter.WardLocal
