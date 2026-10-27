module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.L828N

open scoped commutatorElement

private lemma comm_mul_central_left_L828N {Q : Type} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (a b : Q) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b * z⁻¹ = b := by
    rw [← Subgroup.mem_center_iff.mp hz b, mul_inv_cancel_right]
  calc ⁅a * z, b⁆ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = ⁅a, b⁆ := by rw [hzb, commutatorElement_def]

private lemma comm_mul_central_right_L828N {Q : Type} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (a b : Q) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hz a⁻¹, mul_inv_cancel_right]
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = ⁅a, b⁆ := by rw [hza, commutatorElement_def]

theorem quasisimple_proper_normal_le_center {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] (hN : N ≠ ⊤) : N ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimp, -⟩ := hq
  haveI : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) _
      (QuotientGroup.mk'_surjective (Subgroup.center Q))
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map (QuotientGroup.mk' (Subgroup.center Q))) with
    hbot | htop
  · intro n hn
    have hmem : (QuotientGroup.mk' (Subgroup.center Q) n : Q ⧸ Subgroup.center Q) ∈
        N.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hn
    rw [hbot, Subgroup.mem_bot] at hmem
    have hmem' : (n : Q ⧸ Subgroup.center Q) = 1 := hmem
    exact (QuotientGroup.eq_one_iff n).mp hmem'
  · exfalso
    apply hN
    have hdec : ∀ q : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, q = n * z := by
      intro q
      have hqmem : (QuotientGroup.mk' (Subgroup.center Q) q : Q ⧸ Subgroup.center Q) ∈
          N.map (QuotientGroup.mk' (Subgroup.center Q)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := hqmem
      have hnq' : (n : Q ⧸ Subgroup.center Q) = (q : Q ⧸ Subgroup.center Q) := hnq
      exact ⟨n, hn, n⁻¹ * q, QuotientGroup.eq.mp hnq', (mul_inv_cancel_left n q).symm⟩
    have hcomm : ∀ g h : Q, ⁅g, h⁆ ∈ N := by
      intro g h
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec g
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec h
      rw [comm_mul_central_left_L828N hz₁, comm_mul_central_right_L828N hz₂, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    have htopN : (⊤ : Subgroup Q) ≤ N := by
      rw [← hperf.commutator_eq_top]
      show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ N
      exact Subgroup.commutator_le.mpr (fun g _ h _ => hcomm g h)
    exact top_le_iff.mp htopN

theorem quasisimple_solvable_normal_le_center {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] [Group.IsSolvable N] : N ≤ Subgroup.center Q := by
  by_cases hN : N = ⊤
  · exfalso
    obtain ⟨-, hsimp, hnonab⟩ := hq
    have hsurj : Function.Surjective N.subtype := fun q =>
      ⟨⟨q, by rw [hN]; exact Subgroup.mem_top q⟩, rfl⟩
    have hsolv : Group.IsSolvable Q := Group.isSolvable_of_surjective hsurj
    have hqz : Group.IsSolvable (Q ⧸ Subgroup.center Q) := inferInstance
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hqz a b)
  · exact quasisimple_proper_normal_le_center hq N hN

theorem quasisimple_quot_equiv {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hX : IsSimpleGroup X) (hXn : ∃ a b : X, a * b ≠ b * a)
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) :
    Nonempty ((Y ⧸ CFSG.pCore 2 Y) ⧸ Subgroup.center (Y ⧸ CFSG.pCore 2 Y) ≃* X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Finite.of_surjective π hπ
  have hOker : CFSG.pCore 2 Y ≤ π.ker := by
    haveI : ((CFSG.pCore 2 Y).map π).Normal :=
      Subgroup.Normal.map (inferInstance : (CFSG.pCore 2 Y).Normal) π hπ
    rcases Subgroup.Normal.eq_bot_or_eq_top ((CFSG.pCore 2 Y).map π) with hbot | htop
    · intro o ho
      have hmem : π o ∈ (CFSG.pCore 2 Y).map π := Subgroup.mem_map_of_mem π ho
      rw [hbot, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    ·
      exfalso
      have hpg : IsPGroup 2 ((CFSG.pCore 2 Y).map π) := IsPGroup.map CFSG.pCore_isPGroup π
      have hall : ∀ x : X, x ∈ (CFSG.pCore 2 Y).map π := fun x => by
        rw [htop]
        exact Subgroup.mem_top x
      have hX2 : IsPGroup 2 X :=
        hpg.of_surjective ((CFSG.pCore 2 Y).map π).subtype (fun x => ⟨⟨x, hall x⟩, rfl⟩)
      have hnil : Group.IsNilpotent X := hX2.isNilpotent
      have hsolv : Group.IsSolvable X := inferInstance
      obtain ⟨a, b, hab⟩ := hXn
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)
  obtain ⟨πbar, hπbar⟩ : ∃ f : (Y ⧸ CFSG.pCore 2 Y) →* X,
      ∀ y : Y, f (y : Y ⧸ CFSG.pCore 2 Y) = π y :=
    ⟨QuotientGroup.lift (CFSG.pCore 2 Y) π hOker, fun y => rfl⟩
  have hπbar_surj : Function.Surjective πbar := by
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    exact ⟨(y : Y ⧸ CFSG.pCore 2 Y), hπbar y⟩
  have hK_ne : πbar.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hXn
    have hone : ∀ x : X, x = 1 := by
      intro x
      obtain ⟨q, rfl⟩ := hπbar_surj x
      have hq' : q ∈ πbar.ker := by
        rw [htop]
        exact Subgroup.mem_top q
      exact MonoidHom.mem_ker.mp hq'
    exact hab (by rw [hone a, hone b])
  have hcenter_le : Subgroup.center (Y ⧸ CFSG.pCore 2 Y) ≤ πbar.ker := by
    have hXc : Subgroup.center X = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hXn
        have ha : a ∈ Subgroup.center X := by
          rw [h]
          exact Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    intro z hz
    have hcz : πbar z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨q, rfl⟩ := hπbar_surj x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz q]
    rw [hXc, Subgroup.mem_bot] at hcz
    exact MonoidHom.mem_ker.mpr hcz
  have hker_eq : Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = πbar.ker :=
    le_antisymm hcenter_le (quasisimple_proper_normal_le_center hq πbar.ker hK_ne)
  exact ⟨QuotientGroup.liftEquiv (Subgroup.center (Y ⧸ CFSG.pCore 2 Y)) hπbar_surj hker_eq⟩

theorem three_dvd_center_of_solvable_normal {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) (Z : Subgroup Y) [Z.Normal]
    [Group.IsSolvable Z] {e : Y} (he : e ∈ Z) (he3 : orderOf e = 3) :
    3 ∣ Nat.card (Subgroup.center (Y ⧸ CFSG.pCore 2 Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 Y) : Y →* Y ⧸ CFSG.pCore 2 Y) :=
    QuotientGroup.mk'_surjective (CFSG.pCore 2 Y)
  haveI : (Z.map (QuotientGroup.mk' (CFSG.pCore 2 Y))).Normal :=
    Subgroup.Normal.map (inferInstance : Z.Normal) _ hsurj
  haveI : Group.IsSolvable (Z.map (QuotientGroup.mk' (CFSG.pCore 2 Y))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (CFSG.pCore 2 Y)).subgroupMap_surjective Z)
  have hZc := quasisimple_solvable_normal_le_center hq
    (Z.map (QuotientGroup.mk' (CFSG.pCore 2 Y)))
  have hφe : QuotientGroup.mk' (CFSG.pCore 2 Y) e ∈ Subgroup.center (Y ⧸ CFSG.pCore 2 Y) :=
    hZc (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 Y)) he)
  have hφe1 : QuotientGroup.mk' (CFSG.pCore 2 Y) e ≠ 1 := by
    intro h1
    have heO : e ∈ CFSG.pCore 2 Y := (QuotientGroup.eq_one_iff e).mp h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨e, heO⟩
    have hek : e ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : orderOf e ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hek
    rw [he3] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Y) e) = 3 := by
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 Y) e) ∣ 3 := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 Y)) e
      rwa [he3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hφe1
    · exact h
  have hcard := orderOf_dvd_natCard
    (⟨QuotientGroup.mk' (CFSG.pCore 2 Y) e, hφe⟩ : Subgroup.center (Y ⧸ CFSG.pCore 2 Y))
  rw [Subgroup.orderOf_mk, hord] at hcard
  exact hcard

theorem sylow_cyclic_quotient {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hcyc : ∀ S : Sylow 3 Y, IsCyclic (S : Subgroup Y)) :
    ∀ S : Sylow 3 X, IsCyclic (S : Subgroup X) := by
  intro S
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 3 S
  have hmap : (P : Subgroup Y).map π = (S : Subgroup X) := by
    rw [← Sylow.coe_mapSurjective hπ P, hP]
  have hPc : IsCyclic (P : Subgroup Y) := hcyc P
  rw [← hmap]
  exact isCyclic_of_surjective (π.subgroupMap (P : Subgroup Y))
    (π.subgroupMap_surjective (P : Subgroup Y))

end CFSG.Quasithin.H13.L828N
