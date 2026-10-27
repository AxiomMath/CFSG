module

public import CFSG.Quasithin.EmptyFaithful.S151TBDef
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace Typ

theorem mem_center_of_map_mem_center {Q X : Type*} [Group Q] [Group X] [Group.IsPerfect Q]
    (π : Q →* X) (hk : π.ker ≤ Subgroup.center Q) {q : Q} (hq : π q ∈ Subgroup.center X) :
    q ∈ Subgroup.center Q := by
  have h2 : q ∈ Subgroup.upperCentralSeries Q (1 + 1) := by
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hq (π y)).symm
  rwa [Group.IsPerfect.upperCentralSeries_eq_center Q (by norm_num : 1 + 1 ≠ 0)] at h2

theorem map_mem_center_of_surjective {Q X : Type*} [Group Q] [Group X] (π : Q →* X)
    (hπ : Function.Surjective π) {q : Q} (hq : q ∈ Subgroup.center Q) :
    π q ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨y, rfl⟩ := hπ x
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hq y]

theorem card_quotient_center_eq {Q X : Type*} [Group Q] [Group X] [Group.IsPerfect Q]
    (π : Q →* X) (hπ : Function.Surjective π) (hk : π.ker ≤ Subgroup.center Q) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card (Q ⧸ Subgroup.center Q) := by
  let f : Q →* X ⧸ Subgroup.center X := (QuotientGroup.mk' (Subgroup.center X)).comp π
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp hπ
  have hker : f.ker = Subgroup.center Q := by
    ext q
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (π q) : X ⧸ Subgroup.center X) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact ⟨mem_center_of_map_mem_center π hk, map_mem_center_of_surjective π hπ⟩
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv.symm).trans
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv)

theorem card_center_dvd_of_surjective {Q X : Type*} [Group Q] [Group X] [Group.IsPerfect Q]
    (π : Q →* X) (hπ : Function.Surjective π) (hk : π.ker ≤ Subgroup.center Q) :
    Nat.card (Subgroup.center X) ∣ Nat.card (Subgroup.center Q) := by
  let g : Subgroup.center Q →* Subgroup.center X :=
    (π.comp (Subgroup.center Q).subtype).codRestrict (Subgroup.center X)
      (fun z => map_mem_center_of_surjective π hπ z.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨q, hq⟩ := hπ y
    have hqc : q ∈ Subgroup.center Q :=
      mem_center_of_map_mem_center π hk (by rw [hq]; exact y.2)
    exact ⟨⟨q, hqc⟩, Subtype.ext hq⟩
  exact Subgroup.card_dvd_of_surjective hg

theorem le_pCore_of_isPGroup {K : Type*} [Group K] {M : Subgroup K} [M.Normal]
    (hM : IsPGroup 2 M) : M ≤ CFSG.pCore 2 K :=
  le_sSup ⟨inferInstance, hM⟩

theorem eq_bot_of_isPGroup_quotient_pCore {K : Type*} [Group K]
    (N : Subgroup (K ⧸ CFSG.pCore 2 K)) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have hM : IsPGroup 2 (N.comap (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
    hN.comap_of_ker_isPGroup _ (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hle := le_pCore_of_isPGroup hM
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective n
  have hx : x ∈ CFSG.pCore 2 K := hle hn
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem odd_card_center_quotient_pCore {K : Type*} [Group K] [Finite K] :
    Odd (Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K))) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hq2 : orderOf (z : K ⧸ CFSG.pCore 2 K) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hle : Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K) ≤
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.zpowers_le]
    exact z.2
  have := Subgroup.normal_of_le_center hle
  have hp : IsPGroup 2 (Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hq2]; rfl)
  have hbot := eq_bot_of_isPGroup_quotient_pCore _ hp
  have h1 : (z : K ⧸ CFSG.pCore 2 K) = 1 := by
    have : (z : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K) :=
      Subgroup.mem_zpowers _
    rwa [hbot, Subgroup.mem_bot] at this
  rw [h1, orderOf_one] at hq2
  exact absurd hq2 (by norm_num)

theorem card_quotient_center_of_listD' {L : Subgroup G} (h : ListD' L) :
    Nat.card (LStar L ⧸ Subgroup.center (LStar L)) = 2520 ∨
      Nat.card (LStar L ⧸ Subgroup.center (LStar L)) = 360 ∨
      Nat.card (LStar L ⧸ Subgroup.center (LStar L)) = 6048 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    left
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 7 (by norm_num)]
    decide
  · obtain ⟨e⟩ := h
    right
    left
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 6 (by norm_num)]
    decide
  · right
    right
    exact CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three h

theorem ne_odd_mul_of_two_pow_dvd {N : ℕ} (hN : 2 ^ 6 ∣ N) {z m : ℕ} (hz : Odd z)
    (hm : m = 2520 ∨ m = 360 ∨ m = 6048) : N ≠ z * m := by
  rintro rfl
  have hc : Nat.Coprime (2 ^ 6) z := Nat.Coprime.pow_left 6 (Nat.coprime_two_left.mpr hz)
  have h64 : 2 ^ 6 ∣ m := hc.dvd_of_dvd_mul_left hN
  rcases hm with rfl | rfl | rfl <;> omega

theorem ne_odd_mul_of_lt {N : ℕ} (hN : N < 360) {z m : ℕ} (hz : Odd z)
    (hm : m = 2520 ∨ m = 360 ∨ m = 6048) : N ≠ z * m := by
  rintro rfl
  have hz0 : 0 < z := hz.pos
  rcases hm with rfl | rfl | rfl <;> omega

theorem ne_odd_mul_sl_two {n : ℕ} (hn : 1 < n) {z m : ℕ} (hz : Odd z)
    (hm : m = 2520 ∨ m = 360 ∨ m = 6048) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ z * m := by
  by_cases h6 : 6 ≤ n
  · exact ne_odd_mul_of_two_pow_dvd (Dvd.dvd.mul_right (pow_dvd_pow 2 h6) _) hz hm
  · obtain ⟨k, rfl⟩ := hz
    interval_cases n <;> rcases hm with rfl | rfl | rfl <;> norm_num <;> omega

theorem exists_star_hom {L : Subgroup G} {X : Type} [Group X] (ψ : ↥L →* X)
    (hψ : Function.Surjective ψ) (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L)) :
    ∃ π : LStar L →* X, Function.Surjective π ∧ π.ker ≤ Subgroup.center (LStar L) := by
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ hO2, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := hψ x
    exact ⟨QuotientGroup.mk y, rfl⟩
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hker x hq

theorem star_mem_center_of_ker_eq {L : Subgroup G} {X : Type*} [Group X] {ψ : ↥L →* X}
    (h : ψ.ker = CFSG.pCore 2 ↥L) (x : ↥L) (hx : ψ x = 1) :
    (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L) := by
  have hx' : x ∈ CFSG.pCore 2 ↥L := by rw [← h]; exact MonoidHom.mem_ker.mpr hx
  have h1 : (QuotientGroup.mk x : LStar L) = 1 := (QuotientGroup.eq_one_iff x).mpr hx'
  rw [h1]
  exact Subgroup.one_mem _

end Typ

theorem listD'_false_of_epi {L : Subgroup G} {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple (LStar L)) (ψ : ↥L →* X) (hψ : Function.Surjective ψ)
    (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L))
    (hX : Nat.card (X ⧸ Subgroup.center X) ≠ 2520 ∧ Nat.card (X ⧸ Subgroup.center X) ≠ 360 ∧
      Nat.card (X ⧸ Subgroup.center X) ≠ 6048) : ¬ ListD' L := by
  intro hD
  have : Group.IsPerfect (LStar L) := hq.1
  obtain ⟨π, hπ, hk⟩ := Typ.exists_star_hom ψ hψ hO2 hker
  have hcard := Typ.card_quotient_center_eq π hπ hk
  rcases Typ.card_quotient_center_of_listD' hD with h | h | h
  · exact hX.1 (hcard.trans h)
  · exact hX.2.1 (hcard.trans h)
  · exact hX.2.2 (hcard.trans h)

theorem listD'_false_of_epi_card [Finite G] {L : Subgroup G} {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple (LStar L)) (ψ : ↥L →* X) (hψ : Function.Surjective ψ)
    (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L))
    (hX : ∀ z m : ℕ, Odd z → (m = 2520 ∨ m = 360 ∨ m = 6048) → Nat.card X ≠ z * m) :
    ¬ ListD' L := by
  have : Group.IsPerfect (LStar L) := hq.1
  obtain ⟨π, hπ, hk⟩ := Typ.exists_star_hom ψ hψ hO2 hker
  have hodd : Odd (Nat.card (Subgroup.center X)) :=
    (Typ.odd_card_center_quotient_pCore (K := ↥L)).of_dvd_nat
      (Typ.card_center_dvd_of_surjective π hπ hk)
  have hcard : Nat.card X = Nat.card (Subgroup.center X) * Nat.card (X ⧸ Subgroup.center X) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)).trans (mul_comm _ _)
  refine listD'_false_of_epi hq ψ hψ hO2 hker ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact hX _ _ hodd (Or.inl h) (by rw [hcard, h])
  · exact hX _ _ hodd (Or.inr (Or.inl h)) (by rw [hcard, h])
  · exact hX _ _ hodd (Or.inr (Or.inr h)) (by rw [hcard, h])

theorem listD'_false_of_epi_ker [Finite G] {L : Subgroup G} {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple (LStar L)) (ψ : ↥L →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = CFSG.pCore 2 ↥L)
    (hX : ∀ z m : ℕ, Odd z → (m = 2520 ∨ m = 360 ∨ m = 6048) → Nat.card X ≠ z * m) :
    ¬ ListD' L :=
  listD'_false_of_epi_card hq ψ hψ hker.ge (Typ.star_mem_center_of_ker_eq hker) hX

theorem listD'_false_of_lin2 {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    {n : ℕ} (hn : 1 < n) (h : IsLin2Type L n) : ¬ ListD' L := by
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := h
  refine listD'_false_of_epi_ker hq α hα hker fun z m hz hm => ?_
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [CFSG.GorensteinWalter.sl2_card_formula, hFn]
  exact Typ.ne_odd_mul_sl_two hn hz hm

theorem listD'_false_of_alt {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    {m : ℕ} (hm : m = 5 ∨ m = 8) {α : ↥L →* alternatingGroup (Fin m)}
    (h : IsAltBlockTypeWith L m α) : ¬ ListD' L := by
  obtain ⟨hα, hker, -⟩ := h
  refine listD'_false_of_epi_ker hq α hα hker fun z k hz hk => ?_
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_alt m (by omega)]
  rcases hm with rfl | rfl
  · exact Typ.ne_odd_mul_of_lt (by decide) hz hk
  · exact Typ.ne_odd_mul_of_two_pow_dvd (by decide) hz hk

theorem listD'_false_of_sp4 {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    (h : IsSp4Block L) : ¬ ListD' L := by
  obtain ⟨-, F, _, _, hF, α, hα, hker, -⟩ := h
  refine listD'_false_of_epi_ker hq α hα hker fun z m hz hm => ?_
  have hFn : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_Sp4_pow hFn]
  exact Typ.ne_odd_mul_of_two_pow_dvd
    (Dvd.dvd.mul_right (pow_dvd_pow 2 (by norm_num)) _) hz hm

theorem listD'_false_of_sl3 {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (ψ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hψ : Function.Surjective ψ)
    (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L)) :
    ¬ ListD' L := by
  refine listD'_false_of_epi_card hq ψ hψ hO2 hker fun z m hz hm => ?_
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_three_pow hFn]
  by_cases h2 : 2 ≤ n
  · exact Typ.ne_odd_mul_of_two_pow_dvd (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _) hz hm
  · obtain rfl : n = 1 := by omega
    exact Typ.ne_odd_mul_of_lt (by norm_num) hz hm

theorem listD'_false_of_sl4 {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    (ψ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) (hψ : Function.Surjective ψ)
    (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L)) :
    ¬ ListD' L := by
  refine listD'_false_of_epi_card hq ψ hψ hO2 hker fun z m hz hm => ?_
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_four_of_two (Nat.card_zmod 2)]
  exact Typ.ne_odd_mul_of_two_pow_dvd (by norm_num) hz hm

theorem listD'_false_of_sl5 {L : Subgroup G} [Finite G] (hq : CFSG.IsQuasisimple (LStar L))
    (ψ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) (hψ : Function.Surjective ψ)
    (hO2 : CFSG.pCore 2 ↥L ≤ ψ.ker)
    (hker : ∀ x : ↥L, ψ x = 1 → (QuotientGroup.mk x : LStar L) ∈ Subgroup.center (LStar L)) :
    ¬ ListD' L := by
  refine listD'_false_of_epi_card hq ψ hψ hO2 hker fun z m hz hm => ?_
  rw [CFSG.Quasithin.Vol2.Ch10.SecA.card_statedSL,
    CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_five_of_two (Nat.card_zmod 2)]
  exact Typ.ne_odd_mul_of_two_pow_dvd (by norm_num) hz hm

end CFSG.Quasithin.S151TB
