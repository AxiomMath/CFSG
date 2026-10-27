module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b
public import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_mulEquiv_statedSL {X : Type} [Group X] {F : Type} [Field F] [CharP F 2]
    (e : X ≃* StatedSL 2 F) : Subgroup.center X = ⊥ := by
  have h : Subgroup.center ↥(StatedSL 2 F) = ⊥ := by
    rw [← Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F),
      CFSG.Timmesfeld.RankOne.center_SL2_eq_bot, Subgroup.map_bot]
  rw [← Subgroup.map_center_eq e] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (f := (e : X →* StatedSL 2 F)) _ e.injective).1 h

theorem mem_pCoreOf_of_central {R Y : Subgroup G} (hYR : Y ≤ R) (hZ : center (Bar2 Y) = ⊥)
    {y : G} (hyY : y ∈ Y)
    (hc : (QuotientGroup.mk (⟨y, hYR hyY⟩ : ↥R) : Bar2 R) ∈ center (Bar2 R)) :
    y ∈ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbar : (QuotientGroup.mk (⟨y, hyY⟩ : ↥Y) : Bar2 Y) ∈ center (Bar2 Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hRc := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk (⟨y', hYR y'.2⟩ : ↥R))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hRc
    have hinR : (((y' * ⟨y, hyY⟩)⁻¹ * (⟨y, hyY⟩ * y') : ↥Y) : G) ∈ pCoreOf 2 R := by
      refine ⟨_, hRc, ?_⟩
      simp
    have hle : Y ⊓ pCoreOf 2 R ≤ pCoreOf 2 Y :=
      uc22p20b_le_pCoreOf inf_le_left
        (IsPGroup.to_le (uc22p20b_isPGroup_pCoreOf R) inf_le_right) fun k hk x hx =>
          ⟨Y.mul_mem (Y.mul_mem hk hx.1) (Y.inv_mem hk),
            uc22p20b_conj_mem_pCoreOf_self (hYR hk) hx.2⟩
    obtain ⟨z, hz, hzeq⟩ := hle ⟨(((y' * ⟨y, hyY⟩)⁻¹ * (⟨y, hyY⟩ * y') : ↥Y)).2, hinR⟩
    have : z = (y' * ⟨y, hyY⟩)⁻¹ * (⟨y, hyY⟩ * y') := Subtype.ext hzeq
    rwa [this] at hz
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hbar
  exact ⟨_, hbar, rfl⟩

omit [Finite G] in
theorem eq_one_of_central_of_inverted {R B : Subgroup G} (hBR : B ≤ R) (hBodd : Odd (Nat.card B))
    {t : G} (htR : t ∈ R) (ht : ∀ x ∈ B, t * x * t⁻¹ = x⁻¹) {b : G} (hb : b ∈ B)
    (hc : (QuotientGroup.mk (⟨b, hBR hb⟩ : ↥R) : Bar2 R) ∈ center (Bar2 R)) : b = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set b' : ↥R := ⟨b, hBR hb⟩ with hb'
  set t' : ↥R := ⟨t, htR⟩ with ht'
  have hcomm := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk t')
  have htb : t' * b' = b'⁻¹ * t' := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.1 (ht b hb)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, htb, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, mul_left_inj] at hcomm
  have hsq : ((QuotientGroup.mk b' : Bar2 R)) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hcomm, QuotientGroup.mk_inv]
    simp
  have hdvd2 : orderOf (QuotientGroup.mk b' : Bar2 R) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hodd : Odd (orderOf b') := by
    have h1 : orderOf b ∣ Nat.card B := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf b' = orderOf b := Subgroup.orderOf_mk b _
    rw [h2]
    exact Odd.of_dvd_nat hBodd h1
  have hdvdb : orderOf (QuotientGroup.mk b' : Bar2 R) ∣ orderOf b' :=
    orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥R)) b'
  have hone : orderOf (QuotientGroup.mk b' : Bar2 R) = 1 := by
    have h1 : Odd (orderOf (QuotientGroup.mk b' : Bar2 R)) := Odd.of_dvd_nat hodd hdvdb
    have h2 := (Nat.dvd_prime Nat.prime_two).1 hdvd2
    rcases h2 with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hmem : b' ∈ CFSG.pCore 2 ↥R :=
    (QuotientGroup.eq_one_iff b').1 (orderOf_eq_one_iff.1 hone)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥R))
    (⟨b', hmem⟩ : ↥(CFSG.pCore 2 ↥R))
  rw [Subgroup.orderOf_mk] at hn
  have hn0 : n = 0 := by
    by_contra hn0
    have : Even (orderOf b') := by
      rw [hn]
      exact (Nat.even_pow.2 ⟨even_two, hn0⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hn0, pow_zero, orderOf_eq_one_iff] at hn
  exact congrArg Subtype.val hn

theorem not_isSolvable_image {Q : Type} [Group Q] {R Y : Subgroup G} (hYR : Y ≤ R)
    (hq : CFSG.Open.IsQuasisimple (Bar2 Y)) (hZ : center (Bar2 Y) = ⊥) (φ : ↥R →* Q)
    (hker : ∀ r : ↥R, φ r = 1 → (QuotientGroup.mk r : Bar2 R) ∈ center (Bar2 R)) :
    ¬ Group.IsSolvable ↥((Y.subgroupOf R).map φ) := by
  intro hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥Y →* ↥((Y.subgroupOf R).map φ) :=
    (φ.subgroupMap (Y.subgroupOf R)).comp (Subgroup.subgroupOfEquivOfLe hYR).symm.toMonoidHom
  have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥Y) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).isNilpotent
  have : Group.IsSolvable ↥(CFSG.pCore 2 ↥Y) := inferInstance
  have : Group.IsSolvable ↥Y := by
    refine Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥Y).subtype ψ ?_
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : φ ⟨(y : G), hYR y.2⟩ = 1 := congrArg Subtype.val hy
    have h2 := mem_pCoreOf_of_central hYR hZ y.2 (hker _ h1)
    obtain ⟨z, hz, hzy⟩ := h2
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have : Group.IsSolvable (Bar2 Y) := inferInstance
  have : Nontrivial (Bar2 Y ⧸ center (Bar2 Y)) := hq.2.toNontrivial
  have : Nontrivial (Bar2 Y) := (QuotientGroup.mk'_surjective (center (Bar2 Y))).nontrivial
  exact (IsSolvable.commutator_lt_top_of_nontrivial (Bar2 Y)).ne hq.1

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
