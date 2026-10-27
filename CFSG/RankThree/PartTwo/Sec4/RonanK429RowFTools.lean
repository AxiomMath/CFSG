module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowETools
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL34
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowCard
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.RonanK429E
open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_commute_of_dvd {r : ℕ} (hr : r.Prime) {y : G} (hy : orderOf y = r)
    (hr2 : ¬ r ^ 2 ∣ Nat.card G) {s : G}
    (hdvd : r ∣ Nat.card (Subgroup.centralizer ({s} : Set G))) :
    ∃ x : G, (x⁻¹ * s * x) * y = y * (x⁻¹ * s * x) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({s} : Set G)) r hdvd
  have hgs : (g : G) * s = s * g := Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hg' : orderOf (g : G) = r := by rw [Subgroup.orderOf_coe, hg]
  have hsyl : ∀ z : G, orderOf z = r →
      IsPGroup r (Subgroup.zpowers z) ∧ ¬ r ∣ (Subgroup.zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), fun hi => ?_⟩
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [Nat.card_zpowers, hz] at hmul
    apply hr2
    rw [← hmul, pow_two]
    exact Nat.mul_dvd_mul_left r hi
  obtain ⟨hPy, hPyi⟩ := hsyl y hy
  obtain ⟨hPg, hPgi⟩ := hsyl _ hg'
  let SY : Sylow r G := hPy.toSylow hPyi
  let SG : Sylow r G := hPg.toSylow hPgi
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G SY SG
  have hmap : Subgroup.zpowers (g : G) =
      (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • SY : Sylow r G) : Subgroup G) = (SG : Subgroup G) := by rw [hx]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  have hgmem : (g : G) ∈ (Subgroup.zpowers y).map (MulAut.conj x).toMonoidHom :=
    hmap ▸ Subgroup.mem_zpowers _
  obtain ⟨u, hu, hgu⟩ := hgmem
  have hgu' : (g : G) = x * u * x⁻¹ := by
    rw [← hgu]
    rfl
  refine ⟨x, ?_⟩
  set s' : G := x⁻¹ * s * x with hs'
  have hus : u * s' = s' * u := by
    have h := hgs
    rw [hgu'] at h
    calc u * s' = x⁻¹ * ((x * u * x⁻¹) * s) * x := by rw [hs']; group
      _ = x⁻¹ * (s * (x * u * x⁻¹)) * x := by rw [h]
      _ = s' * u := by rw [hs']; group
  have hu_ord : orderOf u = r := by
    have : orderOf (g : G) = orderOf u := by
      rw [hgu']
      exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective u
    rw [← this, hg']
  have hyu : y ∈ Subgroup.zpowers u := by
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers y :=
      (Subgroup.zpowers_le).mpr hu
    have hc : Nat.card (Subgroup.zpowers y) ≤ Nat.card (Subgroup.zpowers u) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy, hu_ord]
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    exact Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := hyu
  have hk' : u ^ k = y := hk
  rw [← hk']
  exact (Commute.zpow_left hus k).eq.symm

end Sylow

section Route

variable {S : Type} [Group S] [Finite S]

theorem good429_of_sylowRoute {r : ℕ} (hr : r.Prime) {y : S} (hy : orderOf y = r)
    (hr2 : ¬ r ^ 2 ∣ Nat.card S) {N B : ℕ} (hN : Nat.card S ∣ N) (hN0 : 0 < N) (hB : N < B ^ 3)
    (hall : (typeOrders N B).all (fun t => [r].any (fun r' => decide (r' ∣ t))) = true)
    (hexc : ∀ t : S, t * y = y * t → t ^ 3 = 1 → t ≠ 1 →
      Good429 (Subgroup.centralizer ({t} : Set S)))
    (s : S) (hs : orderOf s = 3) : Good429 (Subgroup.centralizer ({s} : Set S)) := by
  have hs3 : s ^ 3 = 1 := by
    rw [← hs]
    exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  by_cases hd : r ∣ Nat.card (Subgroup.centralizer ({s} : Set S))
  · obtain ⟨x, hx⟩ := exists_conj_commute_of_dvd hr hy hr2 hd
    have ht3 : (x⁻¹ * s * x) ^ 3 = 1 := by
      have : (x⁻¹ * s * x) ^ 3 = x⁻¹ * s ^ 3 * x := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [this, hs3, mul_one, inv_mul_cancel]
    have ht1 : x⁻¹ * s * x ≠ 1 := by
      intro h
      apply hs1
      have : s = x * (x⁻¹ * s * x) * x⁻¹ := by group
      rw [this, h]
      group
    have hconj : IsConj (x⁻¹ * s * x) s := by
      rw [isConj_iff]
      exact ⟨x, by group⟩
    exact Good429.of_isConj hconj (hexc _ hx ht3 ht1)
  · exact good429_of_not_dvd ((Subgroup.card_subgroup_dvd_card _).trans hN) hN0 hB [r]
      (by simpa using hd) hall

end Route

section Perfect

variable {S : Type} [Group S] [Finite S]

theorem Good429.of_perfect_le {C D : Subgroup S} (hDC : D ≤ C)
    (h : ∀ K : Subgroup S, K ≤ C → Group.IsPerfect K → K ≤ D) (hD : Good429 D) : Good429 C := by
  intro K hKC hKp hKs hT
  have hKD : K ≤ D := h K hKC hKp
  exact hD K hKD hKp (isSubnormal_subgroupOf_of_le hDC hKD hKs) hT

theorem le_of_commutator_mem {C D K : Subgroup S}
    (hcomm : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ D) (hKC : K ≤ C) (hKp : Group.IsPerfect K) : K ≤ D := by
  haveI := hKp
  rw [← Subgroup.commutator_eq_self (H := K)]
  exact Subgroup.commutator_le.mpr fun a ha b hb => hcomm a (hKC ha) b (hKC hb)

theorem isPerfect_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  have hn : (commutator G).Normal := inferInstance
  rcases hn.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have hm : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  · exact h

theorem good429_self {D : Subgroup S} [Group.IsPerfect D] {M B : ℕ} (hM : Nat.card D = M)
    (hB : M < B ^ 3) (h64 : M < 2 ^ 64) (hres : residOK M B = true)
    (hD : ¬ IsType429 (D ⧸ CFSG.pCore 2 D)) : Good429 D :=
  good429_of_residual le_rfl (by omega) hM hB h64 hres hD

end Perfect

section A8

theorem pCore_two_eq_bot_of_simple {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hD : ¬ IsPGroup 2 D) : CFSG.pCore 2 D = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (inferInstance : (CFSG.pCore 2 D).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hD
    have h2 : IsPGroup 2 (CFSG.pCore 2 D) := CFSG.pCore_isPGroup
    have h2' : IsPGroup 2 (⊤ : Subgroup D) := h ▸ h2
    exact h2'.of_equiv Subgroup.topEquiv

theorem eq_four_of_ordL {q : ℕ} (h1 : q % 3 = 1)
    (h : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) = 60480) : q = 4 := by
  have hq3 : q ^ 3 ∣ 60480 := h ▸ Dvd.intro _ rfl
  have hle : q ≤ 40 := by
    by_contra hlt
    push Not at hlt
    have : 41 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hlt 3
    have := Nat.le_of_dvd (by norm_num) hq3
    omega
  interval_cases q <;> omega

theorem ordU_ne {q : ℕ} (h1 : q % 3 = 2) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ≠ 60480 := by
  intro h
  have hq3 : q ^ 3 ∣ 60480 := h ▸ Dvd.intro _ rfl
  have hle : q ≤ 40 := by
    by_contra hlt
    push Not at hlt
    have : 41 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hlt 3
    have := Nat.le_of_dvd (by norm_num) hq3
    omega
  interval_cases q <;> omega

theorem not_isType429_of_card_20160 {D : Type} [Group D] [Finite D] (hD : Nat.card D = 20160)
    (h6 : ∃ g : D, orderOf g = 6) : ¬ IsType429 D := by
  rintro (⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩)
  · have hpp : p.Prime := hp.out
    rcases hiso with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    · have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [← Nat.card_congr φ.toEquiv, GaloisField.card p e (by omega), hD] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg] at hc
      have hq : p ^ e = 4 := eq_four_of_ordL h1 (by omega)
      have hp2 : p = 2 := by
        have h2 : p ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hq]
          exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h2)
      subst hp2
      have he2 : e = 2 := Nat.pow_right_injective (le_refl 2) (by simpa using hq)
      subst he2
      obtain ⟨g, hg⟩ := h6
      exact Sec8.Item8ModelProof.false_of_orderOf_six φ hg
    · have hc := KS14.card_projSU_three_mul_gcd p e he
      rw [← Nat.card_congr φ.toEquiv, hD] at hc
      have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg] at hc
      exact ordU_ne h2 (by omega)
  · have := Nat.card_congr φ.toEquiv
    rw [hD, KS14.card_alternatingGroup_five_seven_ten.2.1] at this
    norm_num at this
  · have := Nat.card_congr φ.toEquiv
    rw [hD, KS14.card_nativeM12] at this
    norm_num at this
  · have := Nat.card_congr φ.toEquiv
    rw [hD, KS14.card_nativeM22] at this
    norm_num at this
  · have := Nat.card_congr φ.toEquiv
    rw [hD, KS14.card_nativeJ2] at this
    norm_num at this

theorem not_isType429_quot_of_simple_20160 {D : Type} [Group D] [Finite D] [IsSimpleGroup D]
    (hD : Nat.card D = 20160) (h6 : ∃ g : D, orderOf g = 6) :
    ¬ IsType429 (D ⧸ CFSG.pCore 2 D) := by
  intro hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ IsPGroup 2 D := by
    intro hp
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hD] at hn
    have h7 : 7 ∣ 2 ^ n := hn ▸ (by norm_num : 7 ∣ 20160)
    exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7)) (by norm_num)
  have hO : CFSG.pCore 2 D = ⊥ := pCore_two_eq_bot_of_simple h2
  let eQ : D ⧸ CFSG.pCore 2 D ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  exact not_isType429_of_card_20160 hD h6 (isType429_congr eQ hT)

end A8

section Prod

variable {S : Type} [Group S] [Finite S]

theorem good429_of_prod
    {C : Subgroup S} {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    (f : C →* H₁) (g : C →* H₂) (hinj : ∀ x : C, f x = 1 → g x = 1 → x = 1)
    (hf : Nat.card f.range < 2520) (hg : Nat.card g.range < 2520) : Good429 C := by
  intro K hKC hKp hKs hT
  haveI := hKp
  set T := K ⧸ CFSG.pCore 2 K
  haveI : Group.IsPerfect T := inferInstance
  haveI := isSimpleGroup_of_isType429 hT
  have hT2520 : 2520 ≤ Nat.card T := le_card_of_isType429 hT
  haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  set fK : K →* H₁ := f.comp (Subgroup.inclusion hKC)
  set gK : K →* H₂ := g.comp (Subgroup.inclusion hKC)
  set π : K →* T := QuotientGroup.mk' (CFSG.pCore 2 K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set M := fK.ker
  have hMn : (M.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases hMn.eq_bot_or_eq_top with h | h
  ·
    have hle : M ≤ π.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact h
    let φ : K ⧸ M →* T := QuotientGroup.lift M π hle
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨QuotientGroup.mk x, rfl⟩
    have h1 : Nat.card T ≤ Nat.card (K ⧸ M) := Nat.card_le_card_of_surjective _ hφ
    have h2 : Nat.card (K ⧸ M) = Nat.card fK.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange fK).toEquiv
    have h3 : Nat.card fK.range ≤ Nat.card f.range := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    omega
  ·
    have h1 : Nat.card T ≤ Nat.card M := by
      have hs : Function.Surjective (π.comp M.subtype) := by
        intro y
        have hy : y ∈ M.map π := h ▸ Subgroup.mem_top y
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
      exact Nat.card_le_card_of_surjective _ hs
    have hinjM : Function.Injective (gK.comp M.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx1 : (Subgroup.inclusion hKC (x : K)) = 1 :=
        hinj _ x.2 hx
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hx1
      exact this
    have h2 : Nat.card M ≤ Nat.card g.range := by
      have h3 : Nat.card M = Nat.card (gK.comp M.subtype).range :=
        Nat.card_congr (MonoidHom.ofInjective hinjM).toEquiv
      rw [h3]
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    omega

end Prod

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
