module

public import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

theorem three_mul_card_le_of_lt {H K : Subgroup Y} (hK : IsPGroup 3 K) (hHK : H < K) :
    3 * Nat.card H ≤ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (H.subgroupOf K).index * Nat.card H = Nat.card K := by
    have := Subgroup.card_mul_index (H.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK.le).toEquiv] at this
    rw [mul_comm]
    exact this
  have h2 : (H.subgroupOf K).index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h
    exact hHK.not_ge h
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have h3 : (H.subgroupOf K).index ∣ 3 ^ n := by
    rw [← hn, ← h1]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h2 (by rw [hj', pow_zero])
  rw [← h1, hj']
  have : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hj0)
  exact Nat.mul_le_mul_right _ this

theorem le_pRank_three {E : Subgroup Y} (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  refine le_csSup ⟨Nat.card Y, ?_⟩ ⟨E, le_top, hE, hk⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card Y := Subgroup.card_le_card_group B

theorem false_of_three_commuting (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2) {a b c : Y}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (hab : a * b = b * a) (hac : a * c = c * a)
    (hbc : b * c = c * b) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hcab : c ∉ Subgroup.closure ({a, b} : Set Y)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := Subgroup.closure ({a, b, c} : Set Y) with hE
  have hpair : ({a, b, c} : Set Y).Pairwise Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | exact hab | exact hab.symm | exact hac | exact hac.symm |
        exact hbc | exact hbc.symm
  have hcomm : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hpair
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul y z hy hz ihy ihz =>
      have hyz : Commute y z := congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    | inv y hy ihy => rw [inv_pow, ihy, inv_one]
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hA : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  have hAB : Subgroup.zpowers a < Subgroup.closure ({a, b} : Set Y) := by
    refine lt_of_le_of_ne ?_ fun h => hba ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.subset_closure (by simp)
  have hsub : ({a, b} : Set Y) ⊆ {a, b, c} := by
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hABE : Subgroup.closure ({a, b} : Set Y) < E := by
    refine lt_of_le_of_ne (Subgroup.closure_mono hsub) fun h => hcab ?_
    rw [h]
    exact Subgroup.subset_closure (by simp)
  have h9 := three_mul_card_le_of_lt (hE3.to_le hABE.le) hAB
  have h27 := three_mul_card_le_of_lt hE3 hABE
  obtain ⟨k, hk⟩ := hE3.exists_card_eq
  have hk3 : 3 ≤ k := by
    have h1 : 3 ^ 3 ≤ 3 ^ k := by rw [← hk]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have := le_pRank_three ⟨hcomm, hexp⟩ hk
  omega

theorem le_normalizer_of_three_inner (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {L B D : Subgroup Y} (hLn : L.Normal)
    (hZ3 : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g ^ 3 = 1 → g = 1)
    (hinn : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ x : ↥L, α = MulAut.conj x) (hBL : B ≤ L)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD3 : ∀ x ∈ D, x ^ 3 = 1) (hDL : ¬ D ≤ L)
    {b : Y} (hbB : b ∈ B) (hbD : b ∈ D) (hb1 : b ≠ 1) :
    D ≤ Subgroup.normalizer (B : Set Y) := by
  have := hLn
  have hcube : ∀ w : ↥(Subgroup.center ↥L), ∃ u : ↥(Subgroup.center ↥L), u ^ 3 = w := by
    have hinj : Function.Injective (fun u : ↥(Subgroup.center ↥L) => u ^ 3) := by
      intro u v huv
      have hc : Commute u v := Subtype.ext (Subtype.ext (by
        have := Subgroup.mem_center_iff.mp u.2 v
        exact congrArg Subtype.val this.symm))
      have h1 : (u * v⁻¹) ^ 3 = 1 := by
        rw [(hc.inv_right).mul_pow, inv_pow]
        simp only at huv
        rw [huv, mul_inv_cancel]
      have h2 := hZ3 _ (u * v⁻¹ : ↥(Subgroup.center ↥L)).1.2 (fun l hl => by
        have := Subgroup.mem_center_iff.mp (u * v⁻¹).2 ⟨l, hl⟩
        exact (congrArg Subtype.val this).symm) (by
        have := congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : Y)) h1
        simpa using this)
      have : u * v⁻¹ = 1 := Subtype.ext (Subtype.ext (by simpa using h2))
      exact mul_inv_eq_one.mp this
    exact (Finite.injective_iff_surjective.mp hinj)
  have hx : ∀ d ∈ D, ∃ x : ↥L, x ^ 3 = 1 ∧ ∀ l : ↥L, d * (l : Y) * d⁻¹ = x * l * x⁻¹ := by
    intro d hd
    obtain ⟨x, hx⟩ := hinn (MulAut.conjNormal d) (by rw [← map_pow, hD3 d hd, map_one])
    have hx3 : x ^ 3 ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hc3 : MulAut.conj (x ^ 3) = 1 := by
        rw [map_pow, ← hx, ← map_pow, hD3 d hd, map_one]
      have h := congrArg (fun α : MulAut ↥L => α g) hc3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [h]
        _ = x ^ 3 * g := by group
    obtain ⟨u, hu⟩ := hcube ⟨x ^ 3, hx3⟩
    have huc : ∀ g : ↥L, (u : ↥L) * g = g * u := fun g =>
      (Subgroup.mem_center_iff.mp u.2 g).symm
    refine ⟨x * (u : ↥L)⁻¹, ?_, fun l => ?_⟩
    · have hcomm : Commute x ((u : ↥L)⁻¹) := (show Commute x (u : ↥L) from (huc x).symm).inv_right
      rw [hcomm.mul_pow, inv_pow]
      have : ((u ^ 3 : ↥(Subgroup.center ↥L)) : ↥L) = x ^ 3 := congrArg Subtype.val hu
      rw [← Subgroup.coe_pow, this, mul_inv_cancel]
    · have h := congrArg (fun α : MulAut ↥L => ((α l : ↥L) : Y)) hx
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h
      rw [h]
      have e : x * l * x⁻¹ = x * (u : ↥L)⁻¹ * l * (x * (u : ↥L)⁻¹)⁻¹ := by
        have hul := huc l
        calc x * l * x⁻¹ = x * ((u : ↥L)⁻¹ * ((u : ↥L) * l)) * x⁻¹ := by group
          _ = x * ((u : ↥L)⁻¹ * (l * u)) * x⁻¹ := by rw [hul]
          _ = x * (u : ↥L)⁻¹ * l * (x * (u : ↥L)⁻¹)⁻¹ := by group
      exact congrArg Subtype.val e
  choose! x hx3' hxd using hx
  have hc : ∀ d ∈ D, ∀ l ∈ L, d * ((x d : ↥L) : Y)⁻¹ * l = l * (d * ((x d : ↥L) : Y)⁻¹) := by
    intro d hd l hl
    have h := hxd d hd ⟨(x d)⁻¹ * l * x d, by
      exact L.mul_mem (L.mul_mem (L.inv_mem (x d).2) hl) (x d).2⟩
    simp only [Subgroup.coe_inv] at h
    calc d * ((x d : ↥L) : Y)⁻¹ * l = d * (((x d : ↥L) : Y)⁻¹ * l * (x d)) * d⁻¹ * d *
          ((x d : ↥L) : Y)⁻¹ := by group
      _ = l * (d * ((x d : ↥L) : Y)⁻¹) := by rw [h]; group
  have hxb : ∀ d ∈ D, ((x d : ↥L) : Y) * b = b * x d := by
    intro d hd
    have h := hxd d hd ⟨b, hBL hbB⟩
    have hdb : d * b * d⁻¹ = b := by rw [hDab d hd b hbD, mul_inv_cancel_right]
    have h0 : ((x d : ↥L) : Y) * b * ((x d : ↥L) : Y)⁻¹ = d * b * d⁻¹ := by
      simpa using h.symm
    have h' : ((x d : ↥L) : Y) * b * ((x d : ↥L) : Y)⁻¹ = b := h0.trans hdb
    calc ((x d : ↥L) : Y) * b = ((x d : ↥L) : Y) * b * ((x d : ↥L) : Y)⁻¹ * x d := by group
      _ = b * x d := by rw [h']
  have hcx : ∀ d ∈ D, Commute (d * ((x d : ↥L) : Y)⁻¹) ((x d : ↥L) : Y) := fun d hd =>
    hc d hd _ (x d).2
  have hx3 : ∀ d ∈ D, ((x d : ↥L) : Y) ^ 3 = 1 ∧ (d * ((x d : ↥L) : Y)⁻¹) ^ 3 = 1 := by
    intro d hd
    have hx1 : ((x d : ↥L) : Y) ^ 3 = 1 := by
      have := congrArg Subtype.val (hx3' d hd)
      simpa using this
    have hd3 : (d * ((x d : ↥L) : Y)⁻¹) ^ 3 * ((x d : ↥L) : Y) ^ 3 = 1 := by
      rw [← (hcx d hd).mul_pow, inv_mul_cancel_right, hD3 d hd]
    refine ⟨hx1, ?_⟩
    rw [hx1, mul_one] at hd3
    exact hd3
  by_cases hall : ∀ d ∈ D, ((x d : ↥L) : Y) ∈ Subgroup.zpowers b
  ·
    intro d hd
    have hbN : ∀ y ∈ B, y ∈ Subgroup.normalizer (B : Set Y) := fun y hy =>
      Subgroup.le_normalizer hy
    have hcN : d * ((x d : ↥L) : Y)⁻¹ ∈ Subgroup.normalizer (B : Set Y) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hc d hd y (hBL hy), mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyL : y ∈ L := by
          have h1 := hLn.conj_mem _ (hBL hy) (d * ((x d : ↥L) : Y)⁻¹)⁻¹
          simpa [mul_assoc] using h1
        rw [hc d hd y hyL, mul_inv_cancel_right] at hy
        exact hy
    have hxB : ((x d : ↥L) : Y) ∈ B :=
      (Subgroup.zpowers_le.mpr hbB) (hall d hd)
    have e : d = d * ((x d : ↥L) : Y)⁻¹ * x d := by group
    rw [e]
    exact Subgroup.mul_mem _ hcN (hbN _ hxB)
  ·
    exfalso
    obtain ⟨d₁, hd₁'⟩ := not_forall.mp hall
    obtain ⟨hd₁, hx₁⟩ := not_imp.mp hd₁'
    obtain ⟨d₂, hd₂, hd₂L⟩ := Set.not_subset.mp hDL
    have hc1 : d₂ * ((x d₂ : ↥L) : Y)⁻¹ ≠ 1 := fun h => hd₂L (by
      rw [mul_inv_eq_one] at h
      rw [h]
      exact (x d₂).2)
    refine false_of_three_commuting hrank (hD3 b hbD) (hx3 d₁ hd₁).1 (hx3 d₂ hd₂).2
      (hxb d₁ hd₁).symm (hc d₂ hd₂ b (hBL hbB)).symm ?_ hb1 hx₁ fun hmem => hc1 ?_
    · exact (hc d₂ hd₂ _ (x d₁).2).symm
    · have hle : Subgroup.closure ({b, ((x d₁ : ↥L) : Y)} : Set Y) ≤ L := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact hBL hbB
        · exact (x d₁).2
      exact hZ3 _ (hle hmem) (fun l hl => hc d₂ hd₂ l hl) (hx3 d₂ hd₂).2

theorem exists_center_three_centralizer {L D : Subgroup Y} (hLn : L.Normal) (hD3 : IsPGroup 3 D)
    {z : Y} (hzL : z ∈ L) (hzc : ∀ l ∈ L, l * z = z * l) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    ∃ w ∈ L, (∀ l ∈ L, l * w = w * l) ∧ w ≠ 1 ∧ w ^ 3 = 1 ∧ ∀ d ∈ D, d * w = w * d := by
  let Ω : Subgroup Y :=
    { carrier := {x | x ∈ L ∧ (∀ l ∈ L, l * x = x * l) ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro x y ⟨hxL, hxc, hx3⟩ ⟨hyL, hyc, hy3⟩
        refine ⟨L.mul_mem hxL hyL, fun l hl => ?_, ?_⟩
        · rw [← mul_assoc, hxc l hl, mul_assoc, hyc l hl, mul_assoc]
        · have hxy : Commute x y := hyc x hxL
          rw [hxy.mul_pow, hx3, hy3, one_mul]
      one_mem' := ⟨L.one_mem, fun l _ => by rw [mul_one, one_mul], one_pow 3⟩
      inv_mem' := by
        rintro x ⟨hxL, hxc, hx3⟩
        refine ⟨L.inv_mem hxL, fun l hl => ?_, by rw [inv_pow, hx3, inv_one]⟩
        have h := hxc l hl
        calc l * x⁻¹ = x⁻¹ * (x * l) * x⁻¹ := by group
          _ = x⁻¹ * l := by rw [← h]; group }
  have hΩ3 : IsPGroup 3 Ω := fun x => ⟨1, Subtype.ext (by simpa using x.2.2.2)⟩
  have hconj : ∀ d ∈ D, ∀ g ∈ Ω, d * g * d⁻¹ ∈ Ω := by
    rintro d - g ⟨hgL, hgc, hg3⟩
    refine ⟨hLn.conj_mem g hgL d, fun l hl => ?_, by rw [conj_pow, hg3, mul_one, mul_inv_cancel]⟩
    have hl' : d⁻¹ * l * d ∈ L := by simpa using hLn.conj_mem l hl d⁻¹
    have h := hgc _ hl'
    calc l * (d * g * d⁻¹) = d * ((d⁻¹ * l * d) * g) * d⁻¹ := by group
      _ = d * (g * (d⁻¹ * l * d)) * d⁻¹ := by rw [h]
      _ = d * g * d⁻¹ * l := by group
  have hDΩ : D ≤ Subgroup.normalizer (Ω : Set Y) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hconj d hd g, fun h => ?_⟩
    have h1 := hconj d⁻¹ (D.inv_mem hd) _ h
    simpa [mul_assoc] using h1
  have hne : Ω ≠ ⊥ := fun h => hz1 (by
    have hzΩ : z ∈ Ω := ⟨hzL, hzc, hz3⟩
    rwa [h, Subgroup.mem_bot] at hzΩ)
  have h := CFSG.Walter.inf_centralizer_ne_bot_of_isPGroup Nat.prime_three hD3 hΩ3 hDΩ hne
  obtain ⟨⟨w, hwΩ, hwC⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  obtain ⟨hwL, hwc, hw3⟩ := hwΩ
  refine ⟨w, hwL, hwc, fun h => hw1 (Subtype.ext h), hw3, fun d hd => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hwC d hd

theorem le_normalizer_of_center_or_inner (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 2)
    {L B D : Subgroup Y} (hLn : L.Normal) (hBL : B ≤ L)
    (hcase : (∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1) ∨
      ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ x : ↥L, α = MulAut.conj x)
    (hD3 : IsPGroup 3 D) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD3e : ∀ x ∈ D, x ^ 3 = 1) (hDL : ¬ D ≤ L) {b : Y} (hbB : b ∈ B) (hbD : b ∈ D)
    (hb1 : b ≠ 1) (hbZ : ∃ l ∈ L, l * b ≠ b * l) : D ≤ Subgroup.normalizer (B : Set Y) := by
  by_cases hz : ∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1
  · exfalso
    obtain ⟨z, hzL, hzc, hz1, hz3⟩ := hz
    obtain ⟨w, hwL, hwc, hw1, hw3, hwD⟩ :=
      exists_center_three_centralizer hLn hD3 hzL hzc hz1 hz3
    obtain ⟨d, hd, hdL⟩ := Set.not_subset.mp hDL
    obtain ⟨l, hl, hlb⟩ := hbZ
    refine false_of_three_commuting hrank hw3 (hD3e b hbD) (hD3e d hd) (hwc b (hBL hbB)).symm
      (hwD d hd).symm (hDab b hbD d hd) hw1 (fun hb => hlb ?_) (fun hd' => hdL ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Commute.zpow_right (show Commute l w from hwc l hl) k
    · have hle : Subgroup.closure ({w, b} : Set Y) ≤ L := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact hwL
        · exact hBL hbB
      exact hle hd'
  · have hZ3 : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g ^ 3 = 1 → g = 1 := by
      intro g hg hgc hg3
      by_contra hg1
      exact hz ⟨g, hg, fun l hl => (hgc l hl).symm, hg1, hg3⟩
    exact le_normalizer_of_three_inner hrank hLn hZ3 (hcase.resolve_left hz) hBL hDab hD3e hDL
      hbB hbD hb1

end CFSG.Quasithin.H13.Ch9.TN
