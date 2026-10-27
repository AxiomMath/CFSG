module

public import CFSG.Quasithin.EmptyFaithful.SBc2SzCore
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace SzQuot1521

theorem exists_odd_pow_lift {H : Type*} [Group H] [Finite H] {Z : Subgroup H} [Z.Normal]
    (hZ : IsPGroup 2 Z) {l : H} (hd : Odd (orderOf (l : H ⧸ Z))) :
    ∃ k : ℕ, Odd (orderOf (l ^ k)) ∧ ((l ^ k : H) : H ⧸ Z) = (l : H ⧸ Z) := by
  set n := orderOf (l : H ⧸ Z) with hn
  have hl : l ^ n ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ := hZ ⟨l ^ n, hl⟩
  have hj' : (l ^ n) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hco : Nat.Coprime n (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hd)
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hco 1 0
  have hdvd : 2 ^ j ∣ c := (Nat.modEq_zero_iff_dvd.mp hc2)
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨c', rfl⟩ := hdvd
    have h1 : (l ^ (2 ^ j * c')) ^ n = 1 := by
      calc (l ^ (2 ^ j * c')) ^ n = (l ^ n) ^ (2 ^ j * c') := by
            rw [← pow_mul, ← pow_mul, mul_comm]
        _ = ((l ^ n) ^ 2 ^ j) ^ c' := by rw [pow_mul]
        _ = 1 := by rw [hj', one_pow]
    exact hd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · rw [QuotientGroup.mk_pow, ← pow_mod_orderOf]
    have : c % n = 1 % n := hc1
    rw [← hn, this, pow_mod_orderOf, pow_one]

theorem mem_normalizer_of_map_mem {H : Type*} [Group H] {Z P : Subgroup H} [Z.Normal]
    (hZP : Z ≤ P) {l : H}
    (hl : (l : H ⧸ Z) ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' Z) : Subgroup (H ⧸ Z)) : Set (H ⧸ Z))) :
    l ∈ Subgroup.normalizer (P : Set H) := by
  have key : ∀ g : H, (g : H ⧸ Z) ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' Z) : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) →
      ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro g hg p hp
    have h1 : ((g * p * g⁻¹ : H) : H ⧸ Z) ∈ P.map (QuotientGroup.mk' Z) := by
      have := (Subgroup.mem_normalizer_iff.mp hg (p : H ⧸ Z)).mp ⟨p, hp, rfl⟩
      simpa using this
    obtain ⟨p', hp', hpp'⟩ := h1
    have hz : p'⁻¹ * (g * p * g⁻¹) ∈ Z := QuotientGroup.eq.mp hpp'
    have : g * p * g⁻¹ = p' * (p'⁻¹ * (g * p * g⁻¹)) := by group
    rw [this]
    exact P.mul_mem hp' (hZP hz)
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => key l hl p hp, fun hp => ?_⟩
  have hl' : ((l⁻¹ : H) : H ⧸ Z) ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' Z) : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) := by
    rw [QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ hl
  have := key l⁻¹ hl' _ hp
  simpa [mul_assoc] using this

theorem mem_center_of_commutator_mem_center {H : Type} [Group H]
    [Finite H] (hZ : IsPGroup 2 (Subgroup.center H))
    (hB : fusionIsBenderGroup (H ⧸ Subgroup.center H))
    (P : Sylow 2 H) {s : H} (hs : s ∈ (P : Subgroup H))
    (h : ∀ h ∈ Subgroup.normalizer ((P : Subgroup H) : Set H), Odd (orderOf h) →
      ⁅s, h⁆ ∈ Subgroup.center H) : s ∈ Subgroup.center H := by
  classical
  set Z := Subgroup.center H with hZdef
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZP : Z ≤ (P : Subgroup H) := hZ.le_sylow_of_normal P
  let T : Sylow 2 (H ⧸ Z) := P.mapSurjective hπ
  have hT : (T : Subgroup (H ⧸ Z)) = (P : Subgroup H).map π := Sylow.coe_mapSurjective hπ P
  obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB T
  have hone : π s = 1 := by
    refine hD.eq_one_of_commute ?_ ?_
    · rw [hT]
      exact ⟨s, hs, rfl⟩
    · intro d hd
      obtain ⟨l, rfl⟩ := hπ d
      have hodd : Odd (orderOf (l : H ⧸ Z)) :=
        (hD.odd).of_dvd_nat (Subgroup.orderOf_dvd_natCard D hd)
      obtain ⟨k, hk, hkπ⟩ := exists_odd_pow_lift hZ hodd
      have hlN : l ∈ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
        refine mem_normalizer_of_map_mem hZP ?_
        have := hD.le hd
        rw [hT] at this
        exact this
      have hcomm := h (l ^ k) (Subgroup.pow_mem _ hlN k) hk
      have h1 : π ⁅s, l ^ k⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow] at h1
      have h2 : π l ^ k = π l := hkπ
      rw [h2] at h1
      have h3 : π s * π l * (π s)⁻¹ = π l := by
        have := mul_inv_eq_one.mp h1
        exact this
      have h4 : π s * π l = π l * π s :=
        calc π s * π l = (π s * π l * (π s)⁻¹) * π s := by group
          _ = π l * π s := by rw [h3]
      exact h4.symm
  exact (QuotientGroup.eq_one_iff s).mp hone

theorem mem_of_pow_eq_one_of_mem_normalizer {K : Type*} [Group K] (P : Sylow 2 K) {g : K}
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup K) : Set K)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g ∈ (P : Subgroup K) := by
  have hpg : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card ((Nat.card_zpowers g).trans hj)
  have hHN : Subgroup.zpowers g ≤ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer ((P : Subgroup K) : Set K))).mpr hg
  have h := P.is_maximal' (hpg.to_sup_of_normal_right' P.isPGroup' hHN) le_sup_right
  have hmem : g ∈ Subgroup.zpowers g ⊔ (P : Subgroup K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  rwa [h] at hmem

theorem le_center_of_normal_isPGroup {H : Type*} [Group H] [Finite H]
    (hq : CFSG.Open.IsQuasisimple H) (hZ : IsPGroup 2 (Subgroup.center H))
    {N : Subgroup H} [N.Normal] (hN : IsPGroup 2 N) : N ≤ Subgroup.center H := by
  obtain ⟨hperf, hsimple⟩ := hq
  set Z := Subgroup.center H with hZdef
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hnorm : (N.map π).Normal := Subgroup.Normal.map ‹N.Normal› π hπ
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · intro x hx
    have hx' : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  · exfalso
    have hq2 : IsPGroup 2 (H ⧸ Z) := by
      have h1 : IsPGroup 2 (N.map π) := hN.map π
      rw [h] at h1
      exact h1.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent Z := hZ.isNilpotent
    have : Group.IsNilpotent (H ⧸ Z) := hq2.isNilpotent
    have hsolv : Group.IsSolvable H :=
      Group.isSolvable_of_ker_le_range Z.subtype π
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    have : Group.IsPerfect H := ⟨hperf⟩
    have : Nontrivial (H ⧸ Z) := hsimple.toNontrivial
    have : Nontrivial H := hπ.nontrivial
    exact Group.IsPerfect.not_isSolvable (G := H) hsolv

theorem pCore_eq_center {H : Type*} [Group H] [Finite H] (hq : CFSG.Open.IsQuasisimple H)
    (hZ : IsPGroup 2 (Subgroup.center H)) : CFSG.pCore 2 H = Subgroup.center H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ ?_
  · exact le_center_of_normal_isPGroup hq hZ (CFSG.pCore_isPGroup (p := 2) (G := H))
  · exact le_sSup ⟨inferInstance, hZ⟩

theorem fusionIsBenderGroup_of_isSz {X : Type} [Group X] {e : ℕ} (h : IsSz e X) :
    fusionIsBenderGroup X := by
  obtain ⟨a, ha, -, ⟨φ⟩⟩ := SBc2.isSz_equiv h
  exact Or.inr (Or.inr ⟨a, ha, ⟨φ⟩⟩)

theorem isSz_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ} (h : IsSz f X) :
    IsSz f Y := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.symm.trans e'⟩⟩

theorem exists_isSz_quot {H : Type} [Group H] [Finite H] (hq : CFSG.Open.IsQuasisimple H)
    (hZ : IsPGroup 2 (Subgroup.center H))
    (hSz : (∃ e : ℕ, IsSz e H) ∨ IsSz 3 (H ⧸ CFSG.pCore 2 H)) :
    ∃ e : ℕ, IsSz e (H ⧸ Subgroup.center H) := by
  rcases hSz with ⟨e, he⟩ | h3
  · have hsimp : IsSimpleGroup H := (CFSG.LieType.Simplicity.fam_2b2_simplicity H 2 e he).2
    have hbot : Subgroup.center H = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
      · exact h
      · exfalso
        have : Nontrivial (H ⧸ Subgroup.center H) := hq.2.toNontrivial
        obtain ⟨x, hx⟩ := exists_ne (1 : H ⧸ Subgroup.center H)
        induction x using QuotientGroup.induction_on with
        | H y =>
          exact hx ((QuotientGroup.eq_one_iff y).mpr (h ▸ Subgroup.mem_top y))
    exact ⟨e, isSz_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm he⟩
  · exact ⟨3, isSz_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (pCore_eq_center hq hZ)) h3⟩

end SzQuot1521

end CFSG.Quasithin
