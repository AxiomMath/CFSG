module

public import CFSG.RankThree.PartTwo.Sec3.ElemNineAut
public import CFSG.CharacterTheory.Burnside
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

section Structure

variable (T : Sylow 2 G) (B : Sylow 3 G) (hB9 : Nat.card (B : Subgroup G) = 9)
  (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)

omit [Finite G] in
theorem pCore_two_isPGroup : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup

instance pCore_two_normal' : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal

omit [Finite G] in
theorem pCore_two_le_sylow : CFSG.pCore 2 G ≤ (T : Subgroup G) :=
  IsPGroup.le_sylow_of_normal pCore_two_isPGroup T

include hB9 in
theorem inf_pCore_two_eq_bot : (B : Subgroup G) ⊓ CFSG.pCore 2 G = ⊥ := by
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  obtain ⟨k, hk⟩ := (pCore_two_isPGroup (G := G)).exists_card_eq
  rw [hB9, hk]
  exact Nat.Coprime.pow_right k (by norm_num)

include hB9 hTB in
theorem card_eq_card_sylow_mul :
    Nat.card G = Nat.card (T : Subgroup G) * Nat.card (B : Subgroup G) := by
  have hTB' : (T : Subgroup G) ⊓ (B : Subgroup G) = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    rw [hB9, hk]
    exact Nat.Coprime.pow_left k (by norm_num)
  let μ : ↥(T : Subgroup G) × ↥(B : Subgroup G) → G := fun p => (p.1 : G) * p.2
  have hμ : Function.Bijective μ := by
    refine ⟨?_, fun g => ?_⟩
    · rintro ⟨t, b⟩ ⟨t', b'⟩ h
      have h' : (t : G) * b = t' * b' := h
      have hmem : (t' : G)⁻¹ * t = b' * (b : G)⁻¹ := by
        calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * b) * (b : G)⁻¹ := by group
          _ = (t' : G)⁻¹ * (t' * b') * (b : G)⁻¹ := by rw [h']
          _ = b' * (b : G)⁻¹ := by group
      have hbot : (t' : G)⁻¹ * t ∈ (T : Subgroup G) ⊓ (B : Subgroup G) :=
        ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem t'.2) t.2,
          hmem ▸ (B : Subgroup G).mul_mem b'.2 ((B : Subgroup G).inv_mem b.2)⟩
      rw [hTB', Subgroup.mem_bot] at hbot
      have htt : t = t' := Subtype.ext (by
        have := mul_eq_one_iff_eq_inv.mp hbot
        exact (inv_injective this).symm)
      have hbb : b = b' := Subtype.ext (by
        rw [hbot] at hmem
        exact (mul_inv_eq_one.mp hmem.symm).symm)
      rw [htt, hbb]
    · obtain ⟨t, ht, b, hb, rfl⟩ := hTB g
      exact ⟨(⟨t, ht⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective μ hμ)).symm

include hB9 hTB in
theorem isSolvable_quotient_pCore_two : Group.IsSolvable (G ⧸ CFSG.pCore 2 G) := by
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  obtain ⟨j, hj⟩ := (pCore_two_isPGroup (G := G)).exists_card_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 G)
  rw [card_eq_card_sylow_mul T B hB9 hTB, hk, hB9, hj] at h1
  have hjk : j ≤ k := by
    have hdvd : 2 ^ j ∣ 2 ^ k * 9 := ⟨_, by rw [h1, mul_comm]⟩
    have hcop : Nat.Coprime (2 ^ j) 9 := Nat.Coprime.pow_left j (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  have hcard : Nat.card (G ⧸ CFSG.pCore 2 G) = 2 ^ (k - j) * 3 ^ 2 := by
    have h2 : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
    rw [h2, show (9 : ℕ) = 3 ^ 2 by norm_num] at h1
    have : Nat.card (G ⧸ CFSG.pCore 2 G) * 2 ^ j = 2 ^ (k - j) * 3 ^ 2 * 2 ^ j := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) this
  have : Fintype (G ⧸ CFSG.pCore 2 G) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

include hB9 hTB in
theorem card_quotient_pCore_two :
    ∃ a : ℕ, Nat.card (G ⧸ CFSG.pCore 2 G) = 2 ^ a * 3 ^ 2 := by
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  obtain ⟨j, hj⟩ := (pCore_two_isPGroup (G := G)).exists_card_eq
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 G)
  rw [card_eq_card_sylow_mul T B hB9 hTB, hk, hB9, hj] at h1
  have hjk : j ≤ k := by
    have hdvd : 2 ^ j ∣ 2 ^ k * 9 := ⟨_, by rw [h1, mul_comm]⟩
    have hcop : Nat.Coprime (2 ^ j) 9 := Nat.Coprime.pow_left j (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hdvd)
  refine ⟨k - j, ?_⟩
  have h2 : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hjk]
  rw [h2, show (9 : ℕ) = 3 ^ 2 by norm_num] at h1
  have : Nat.card (G ⧸ CFSG.pCore 2 G) * 2 ^ j = 2 ^ (k - j) * 3 ^ 2 * 2 ^ j := by
    rw [← h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

include hB9 hTB in
theorem normal_and_centralizer_le
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a) :
    ((B : Subgroup G).map (QuotientGroup.mk' (CFSG.pCore 2 G))).Normal ∧
      centralizer (((B : Subgroup G).map (QuotientGroup.mk' (CFSG.pCore 2 G)) :
        Subgroup (G ⧸ CFSG.pCore 2 G)) : Set (G ⧸ CFSG.pCore 2 G)) ≤
        (B : Subgroup G).map (QuotientGroup.mk' (CFSG.pCore 2 G)) := by
  set Q := CFSG.pCore 2 G with hQ
  have hsolv := isSolvable_quotient_pCore_two T B hB9 hTB
  set Bs : Sylow 3 (G ⧸ Q) := B.mapSurjective (QuotientGroup.mk'_surjective Q) with hBsdef
  have hBs : (Bs : Subgroup (G ⧸ Q)) = (B : Subgroup G).map (QuotientGroup.mk' Q) := rfl
  have h2 : CFSG.pCore 2 (G ⧸ Q) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨a, ha⟩ := card_quotient_pCore_two T B hB9 hTB
  have h3' : CFSG.pPrimeCore 3 (G ⧸ Q) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro K hK hcop
    have hdvd : Nat.card K ∣ 2 ^ a := by
      have h := Subgroup.card_subgroup_dvd_card K
      rw [ha] at h
      exact (Nat.Coprime.pow_right 2 hcop.symm).dvd_of_dvd_mul_right h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hK2 : IsPGroup 2 K := IsPGroup.of_card hi
    rw [← le_bot_iff, ← h2]
    exact le_sSup ⟨hK, hK2⟩
  have hF : CFSG.fittingSubgroup (G ⧸ Q) = CFSG.pCore 3 (G ⧸ Q) :=
    CFSG.Fitting_eq_pcore (G ⧸ Q) 3 h3'
  have hC := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
  rw [hF] at hC
  have : (CFSG.pCore 3 (G ⧸ Q)).Normal := CFSG.pCore_normal
  have hle : CFSG.pCore 3 (G ⧸ Q) ≤ Bs := IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Bs
  have hBC : (Bs : Subgroup (G ⧸ Q)) ≤ centralizer (CFSG.pCore 3 (G ⧸ Q) : Set (G ⧸ Q)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hBs] at hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' := hle hy
    rw [hBs] at hy'
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy'
    rw [← map_mul, ← map_mul, hBc v hv u hu]
  have heq : (Bs : Subgroup (G ⧸ Q)) = CFSG.pCore 3 (G ⧸ Q) := le_antisymm (hBC.trans hC) hle
  rw [← hBs, heq]
  exact ⟨CFSG.pCore_normal, hC⟩

include hB9 hTB in
theorem mem_of_forall_commute_mod
    (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
    (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1) {t : G}
    (ht : t ∈ (T : Subgroup G)) (htB : ∀ b ∈ (B : Subgroup G), t * b * t⁻¹ * b⁻¹ ∈ CFSG.pCore 2 G) :
    t ∈ CFSG.pCore 2 G := by
  set Q := CFSG.pCore 2 G
  obtain ⟨-, hC⟩ := normal_and_centralizer_le T B hB9 hTB hBc
  have htC : QuotientGroup.mk' Q t ∈ centralizer
      (((B : Subgroup G).map (QuotientGroup.mk' Q) : Subgroup (G ⧸ Q)) : Set (G ⧸ Q)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h := htB b hb
    have : (b * t)⁻¹ * (t * b) = (t⁻¹ * b⁻¹) * (t * b * t⁻¹ * b⁻¹) * (t⁻¹ * b⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance _ h _
  obtain ⟨b, hb, hbt⟩ := Subgroup.mem_map.mp (hC htC)
  have h3 : (QuotientGroup.mk' Q t) ^ 3 = 1 := by
    rw [← hbt, ← map_pow, hB3 b hb, map_one]
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
  have hk' : (QuotientGroup.mk' Q t) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← map_pow, this, map_one]
  have hdvd : orderOf (QuotientGroup.mk' Q t) ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hdvd
  exact hdvd

end Structure

abbrev bStar (B : Subgroup G) : Subgroup (G ⧸ CFSG.pCore 2 G) :=
  B.map (QuotientGroup.mk' (CFSG.pCore 2 G))

@[expose] noncomputable def actMod (N : Subgroup (G ⧸ CFSG.pCore 2 G)) [N.Normal] :
    G →* MulAut N :=
  (MulAut.conjNormal (H := N)).comp (QuotientGroup.mk' _)

omit [Finite G] in
theorem actMod_apply_coe (N : Subgroup (G ⧸ CFSG.pCore 2 G)) [N.Normal] (g : G) (n : N) :
    ((actMod N g n : N) : G ⧸ CFSG.pCore 2 G) =
      QuotientGroup.mk' (CFSG.pCore 2 G) g * n * (QuotientGroup.mk' (CFSG.pCore 2 G) g)⁻¹ :=
  rfl

omit [Finite G] in
theorem actMod_eq_one_of_mem (N : Subgroup (G ⧸ CFSG.pCore 2 G)) [N.Normal] {q : G}
    (hq : q ∈ CFSG.pCore 2 G) : actMod N q = 1 := by
  apply MulEquiv.ext
  intro n
  apply Subtype.ext
  have hq' : QuotientGroup.mk' (CFSG.pCore 2 G) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  rw [actMod_apply_coe, hq', one_mul, inv_one, mul_one, MulAut.one_apply]

section Action

variable (T : Sylow 2 G) (B : Sylow 3 G) (hB9 : Nat.card (B : Subgroup G) = 9)
  (hTB : ∀ g : G, ∃ t ∈ (T : Subgroup G), ∃ b ∈ (B : Subgroup G), g = t * b)
  (hBc : ∀ a ∈ (B : Subgroup G), ∀ b ∈ (B : Subgroup G), a * b = b * a)
  (hB3 : ∀ b ∈ (B : Subgroup G), b ^ 3 = 1)
include hB9 hTB hBc hB3

omit hTB in
theorem bStar_props :
    (∀ x ∈ bStar (B : Subgroup G), ∀ y ∈ bStar (B : Subgroup G), x * y = y * x) ∧
      (∀ x ∈ bStar (B : Subgroup G), x ^ 3 = 1) ∧ Nat.card (bStar (B : Subgroup G)) = 9 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hB3 a ha, map_one]
  · rw [bStar, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    have h := Subgroup.relIndex_mul_card (H := CFSG.pCore 2 G) (K := (B : Subgroup G))
    have hbot : CFSG.pCore 2 G ⊓ (B : Subgroup G) = ⊥ := by
      rw [inf_comm]; exact inf_pCore_two_eq_bot B hB9
    rw [hbot, Subgroup.card_bot, mul_one, hB9] at h
    exact h

theorem mem_pCore_of_actMod_eq_one [(bStar (B : Subgroup G)).Normal] {t : G}
    (ht : t ∈ (T : Subgroup G)) (h1 : actMod (bStar (B : Subgroup G)) t = 1) :
    t ∈ CFSG.pCore 2 G := by
  apply mem_of_forall_commute_mod T B hB9 hTB hBc hB3 ht
  intro b hb
  have := congrArg (fun σ : MulAut (bStar (B : Subgroup G)) =>
    ((σ ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ : bStar (B : Subgroup G)) :
      G ⧸ CFSG.pCore 2 G)) h1
  simp only [actMod_apply_coe, MulAut.one_apply] at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  change QuotientGroup.mk' _ t * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ t)⁻¹ *
    (QuotientGroup.mk' _ b)⁻¹ = 1
  rw [this, mul_inv_cancel]

omit hTB in
theorem exists_conj_eq_of_quaternion
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    {d d' : G} (hd : d ∈ (B : Subgroup G)) (hd' : d' ∈ (B : Subgroup G)) (hd1 : d ≠ 1)
    (hd'1 : d' ≠ 1) :
    ∃ n ∈ (T : Subgroup G), n ∈ normalizer ((B : Subgroup G) : Set G) ∧ n * d * n⁻¹ = d' := by
  let : CommGroup (B : Subgroup G) := { (inferInstance : Group (B : Subgroup G)) with
    mul_comm := fun a b => Subtype.ext (hBc a a.2 b b.2) }
  have h3 : ∀ b : (B : Subgroup G), b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hB3 b b.2)
  obtain ⟨K, hKle, ⟨e⟩⟩ := hQ8
  obtain ⟨σ, hσK, hσ⟩ := exists_apply_eq_of_quaternion h3 hB9 e (x := ⟨d, hd⟩)
    (y := ⟨d', hd'⟩) (fun h => hd1 (congrArg Subtype.val h))
    (fun h => hd'1 (congrArg Subtype.val h))
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp (hKle hσK)
  refine ⟨n, (Subgroup.mem_subgroupOf.mp hn), n.2, ?_⟩
  have := congrArg Subtype.val hσ
  rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this

theorem exists_inv_mod_of_mul_self_mem {t : G} (ht : t ∈ (T : Subgroup G))
    (htQ : t ∉ CFSG.pCore 2 G) (htt : t * t ∈ CFSG.pCore 2 G) :
    ∃ d ∈ (B : Subgroup G), d ≠ 1 ∧ t * d * t⁻¹ * d ∈ CFSG.pCore 2 G := by
  have hN : (bStar (B : Subgroup G)).Normal := (normal_and_centralizer_le T B hB9 hTB hBc).1
  obtain ⟨hcB, -, -⟩ := bStar_props B hB9 hBc hB3
  let : CommGroup (bStar (B : Subgroup G)) := { (inferInstance : Group _) with
    mul_comm := fun a b => Subtype.ext (hcB a a.2 b b.2) }
  set σ := actMod (bStar (B : Subgroup G)) t with hσ
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul, actMod_eq_one_of_mem _ htt]
  have hσ1 : σ ≠ 1 := fun h => htQ (mem_pCore_of_actMod_eq_one T B hB9 hTB hBc hB3 ht h)
  obtain ⟨⟨_, d, hd, rfl⟩, hd1, hσd⟩ := exists_apply_eq_inv_of_mul_self_eq_one hσσ hσ1
  refine ⟨d, hd, fun h => hd1 (by subst h; exact Subtype.ext (map_one _)), ?_⟩
  have := congrArg Subtype.val hσd
  rw [hσ, actMod_apply_coe] at this
  change QuotientGroup.mk' _ t * QuotientGroup.mk' _ d * (QuotientGroup.mk' _ t)⁻¹ =
    (QuotientGroup.mk' _ d)⁻¹ at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  change QuotientGroup.mk' _ t * QuotientGroup.mk' _ d * (QuotientGroup.mk' _ t)⁻¹ *
    QuotientGroup.mk' _ d = 1
  rw [this, inv_mul_cancel]

theorem relIndex_eq_card_map_actMod [(bStar (B : Subgroup G)).Normal] {A : Subgroup G}
    (hAT : A ≤ (T : Subgroup G)) :
    (CFSG.pCore 2 G).relIndex A = Nat.card (A.map (actMod (bStar (B : Subgroup G)))) := by
  rw [← Subgroup.relIndex_ker]
  rw [Subgroup.relIndex, Subgroup.relIndex]
  congr 1
  ext ⟨a, ha⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact ⟨fun h => actMod_eq_one_of_mem _ h,
    fun h => mem_pCore_of_actMod_eq_one T B hB9 hTB hBc hB3 (hAT ha) h⟩

theorem relIndex_le_four {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    (CFSG.pCore 2 G).relIndex A ≤ 4 := by
  have hN : (bStar (B : Subgroup G)).Normal := (normal_and_centralizer_le T B hB9 hTB hBc).1
  obtain ⟨hcB, h3B, h9B⟩ := bStar_props B hB9 hBc hB3
  let : CommGroup (bStar (B : Subgroup G)) := { (inferInstance : Group _) with
    mul_comm := fun a b => Subtype.ext (hcB a a.2 b b.2) }
  have h3' : ∀ b : bStar (B : Subgroup G), b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact h3B b b.2)
  rw [relIndex_eq_card_map_actMod T B hB9 hTB hBc hB3 hAT]
  apply card_le_four h3' h9B
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA2 a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]

theorem exists_of_relIndex_eq_four {A : Subgroup G} (hAT : A ≤ (T : Subgroup G))
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h4 : (CFSG.pCore 2 G).relIndex A = 4) :
    (∃ z ∈ A, ∀ b ∈ (B : Subgroup G), z * b * z⁻¹ * b ∈ CFSG.pCore 2 G) ∧
      ∃ y ∈ (B : Subgroup G), y ≠ 1 ∧
        (∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.pCore 2 G ∨ a * y * a⁻¹ * y ∈ CFSG.pCore 2 G) ∧
        (∃ s ∈ A, s * y * s⁻¹ * y ∈ CFSG.pCore 2 G) ∧
        (∃ c ∈ A, c ∉ CFSG.pCore 2 G ∧ c * y * c⁻¹ * y⁻¹ ∈ CFSG.pCore 2 G) := by
  classical
  have hN : (bStar (B : Subgroup G)).Normal := (normal_and_centralizer_le T B hB9 hTB hBc).1
  obtain ⟨hcB, h3B, h9B⟩ := bStar_props B hB9 hBc hB3
  let : CommGroup (bStar (B : Subgroup G)) := { (inferInstance : Group _) with
    mul_comm := fun a b => Subtype.ext (hcB a a.2 b b.2) }
  have h3' : ∀ b : bStar (B : Subgroup G), b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact h3B b b.2)
  set ψ := actMod (bStar (B : Subgroup G)) with hψ
  set E := A.map ψ with hE
  have hcard : Nat.card E = 4 := by
    rw [hE, ← relIndex_eq_card_map_actMod T B hB9 hTB hBc hB3 hAT, h4]
  have hE2 : ∀ σ ∈ E, σ * σ = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA2 a ha, map_one]
  have hEc : ∀ σ ∈ E, ∀ τ ∈ E, σ * τ = τ * σ := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have : Fintype E := Fintype.ofFinite E
  have hout : ∀ s : Finset E, s.card < 4 → ∃ σ : E, σ ∉ s := by
    intro s hs
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun σ _ => h σ : Finset.univ ⊆ s)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at this
    omega
  obtain ⟨σ, hσ⟩ := hout {1} (by rw [Finset.card_singleton]; norm_num)
  obtain ⟨τ, hτ⟩ := hout {1, σ} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ hτ
  have hσ1 : (σ : MulAut (bStar (B : Subgroup G))) ≠ 1 := fun h => hσ (Subtype.ext h)
  have hτ1 : (τ : MulAut (bStar (B : Subgroup G))) ≠ 1 := fun h => hτ.1 (Subtype.ext h)
  have hστ : (σ : MulAut (bStar (B : Subgroup G))) ≠ τ := fun h => hτ.2 (Subtype.ext h.symm)
  have hconv : ∀ (a b : G) (hb : b ∈ (B : Subgroup G)),
      ψ a ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ =
        (⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ : bStar (B : Subgroup G))⁻¹ →
      a * b * a⁻¹ * b ∈ CFSG.pCore 2 G := by
    intro a b hb h
    have := congrArg Subtype.val h
    rw [hψ, actMod_apply_coe] at this
    change QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ =
      (QuotientGroup.mk' _ b)⁻¹ at this
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ *
      QuotientGroup.mk' _ b = 1
    rw [this, inv_mul_cancel]
  have hconv' : ∀ (a b : G) (hb : b ∈ (B : Subgroup G)),
      ψ a ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ =
        ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ →
      a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 G := by
    intro a b hb h
    have := congrArg Subtype.val h
    rw [hψ, actMod_apply_coe] at this
    change QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ =
      QuotientGroup.mk' _ b at this
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    change QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ *
      (QuotientGroup.mk' _ b)⁻¹ = 1
    rw [this, mul_inv_cancel]
  obtain ⟨z, hzA, hzι⟩ : ∃ z ∈ A, ∀ b, ψ z b = b⁻¹ := by
    obtain ⟨a₁, ha₁, hσa⟩ := Subgroup.mem_map.mp σ.2
    obtain ⟨a₂, ha₂, hτa⟩ := Subgroup.mem_map.mp τ.2
    rcases inv_mem_of_commute h3' h9B (hE2 σ σ.2) (hEc σ σ.2 τ τ.2) hσ1 hτ1 hστ with
      h | h | h
    · exact ⟨a₁, ha₁, fun b => by rw [hσa]; exact h b⟩
    · exact ⟨a₂, ha₂, fun b => by rw [hτa]; exact h b⟩
    · exact ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, fun b => by rw [map_mul, hσa, hτa]; exact h b⟩
  refine ⟨⟨z, hzA, fun b hb => hconv z b hb (hzι _)⟩, ?_⟩
  obtain ⟨ρ, hρ⟩ := hout {1, ⟨ψ z, Subgroup.mem_map_of_mem _ hzA⟩}
    (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
  obtain ⟨s, hsA, hρs⟩ := Subgroup.mem_map.mp ρ.2
  have hs1 : ψ s ≠ 1 := fun h => hρ.1 (Subtype.ext (hρs.symm.trans h))
  have hsι : ¬ ∀ b, ψ s b = b⁻¹ := fun h => hρ.2 (Subtype.ext (by
    rw [← hρs]; exact (eq_inv_of_forall h).trans (eq_inv_of_forall hzι).symm))
  have hss : ψ s * ψ s = 1 := by rw [← map_mul, hA2 s hsA, map_one]
  obtain ⟨x, hx1, hsx⟩ := exists_apply_eq_self_of_mul_self_eq_one h3' hss hsι
  obtain ⟨⟨_, y, hy, rfl⟩, hy1, hsy⟩ := exists_apply_eq_inv_of_mul_self_eq_one hss hs1
  set ys : bStar (B : Subgroup G) := ⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ hy⟩
  have hys : ys ∉ Subgroup.zpowers x := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    apply hy1
    apply eq_one_of_apply_eq_self_of_apply_eq_inv h3' (σ := ψ s)
    · rw [← hk, map_zpow, hsx]
    · exact hsy
  refine ⟨y, hy, fun h => hy1 (by subst h; exact Subtype.ext (map_one _)), fun a ha => ?_,
    ⟨s, hsA, hconv s y hy hsy⟩, ⟨z * s, A.mul_mem hzA hsA, ?_, ?_⟩⟩
  ·
    have hEa : ψ a ∈ E := Subgroup.mem_map_of_mem _ ha
    have hcomm : ψ s * ψ a = ψ a * ψ s := hEc _ (Subgroup.mem_map_of_mem _ hsA) _ hEa
    have hfix : ψ s (ψ a ys) = (ψ a ys)⁻¹ := by
      rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hsy, map_inv]
    obtain ⟨j, hj3, hj⟩ := exists_eq_pow_of_apply_eq_inv h3' h9B hx1 hys hsx hsy hfix
    interval_cases j
    · exfalso
      rw [pow_zero] at hj
      apply hy1
      have : ψ a ys = ψ a 1 := by rw [hj, map_one]
      exact (ψ a).injective this
    · left
      exact hconv' a y hy (by rw [hj, pow_one])
    · right
      exact hconv a y hy (by rw [hj, ← inv_eq_sq_of_pow_three h3'])
  ·
    intro hzs
    have h1 := actMod_eq_one_of_mem (bStar (B : Subgroup G)) hzs
    rw [map_mul] at h1
    apply hsι
    intro b
    have hb' := congrArg (fun σ : MulAut (bStar (B : Subgroup G)) => σ b) h1
    simp only [MulAut.mul_apply, MulAut.one_apply] at hb'
    rw [← hψ, hzι] at hb'
    calc (ψ s) b = ((ψ s b)⁻¹)⁻¹ := (inv_inv _).symm
      _ = b⁻¹ := by rw [hb']
  · apply hconv' (z * s) y hy
    rw [map_mul, MulAut.mul_apply, hsy, hzι, inv_inv]

omit [Finite G] hB9 hTB hBc hB3 in
theorem actMod_apply_eq_inv_iff [(bStar (B : Subgroup G)).Normal] (a : G) {b : G}
    (hb : b ∈ (B : Subgroup G)) :
    actMod (bStar (B : Subgroup G)) a ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ =
        (⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ : bStar (B : Subgroup G))⁻¹ ↔
      a * b * a⁻¹ * b ∈ CFSG.pCore 2 G := by
  rw [Subtype.ext_iff, actMod_apply_coe, Subgroup.coe_inv, ← QuotientGroup.eq_one_iff,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  change _ ↔ QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ *
    QuotientGroup.mk' _ b = 1
  rw [← eq_inv_iff_mul_eq_one]

omit [Finite G] hB9 hTB hBc hB3 in
theorem actMod_apply_eq_self_iff [(bStar (B : Subgroup G)).Normal] (a : G) {b : G}
    (hb : b ∈ (B : Subgroup G)) :
    actMod (bStar (B : Subgroup G)) a ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ =
        ⟨QuotientGroup.mk' _ b, Subgroup.mem_map_of_mem _ hb⟩ ↔
      a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 G := by
  rw [Subtype.ext_iff, actMod_apply_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  change _ ↔ QuotientGroup.mk' _ a * QuotientGroup.mk' _ b * (QuotientGroup.mk' _ a)⁻¹ *
    (QuotientGroup.mk' _ b)⁻¹ = 1
  rw [← mul_inv_eq_one]

theorem relIndex_le_two_of_centralizes {P : Subgroup G} (hPT : P ≤ (T : Subgroup G)) {y : G}
    (hyB : y ∈ (B : Subgroup G)) (hy1 : y ≠ 1)
    (hPy : ∀ p ∈ P, p * y * p⁻¹ * y⁻¹ ∈ CFSG.pCore 2 G) :
    (CFSG.pCore 2 G).relIndex P ≤ 2 := by
  classical
  have hN : (bStar (B : Subgroup G)).Normal := (normal_and_centralizer_le T B hB9 hTB hBc).1
  obtain ⟨hcB, h3B, h9B⟩ := bStar_props B hB9 hBc hB3
  let _ : CommGroup (bStar (B : Subgroup G)) := { (inferInstance : Group _) with
    mul_comm := fun a b => Subtype.ext (hcB a a.2 b b.2) }
  have h3' : ∀ b : bStar (B : Subgroup G), b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact h3B b b.2)
  set ψ := actMod (bStar (B : Subgroup G)) with hψ
  set ys : bStar (B : Subgroup G) := ⟨QuotientGroup.mk' _ y, Subgroup.mem_map_of_mem _ hyB⟩
  have hys1 : ys ≠ 1 := fun h => hy1 (by
    have h' := congrArg Subtype.val h
    change QuotientGroup.mk' (CFSG.pCore 2 G) y = 1 at h'
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    have : y ∈ (B : Subgroup G) ⊓ CFSG.pCore 2 G := ⟨hyB, h'⟩
    rwa [inf_pCore_two_eq_bot B hB9, Subgroup.mem_bot] at this)
  have hR : IsPGroup 2 ((T : Subgroup G).map ψ) := T.isPGroup'.map ψ
  rw [relIndex_eq_card_map_actMod T B hB9 hTB hBc hB3 hPT]
  have hfix : ∀ σ ∈ P.map ψ, σ ys = ys := by
    rintro _ ⟨p, hp, rfl⟩
    exact (actMod_apply_eq_self_iff B p hyB).mpr (hPy p hp)
  by_cases hbot : ∀ σ ∈ P.map ψ, σ = 1
  · have : P.map ψ = ⊥ := eq_bot_iff.mpr fun σ hσ => (Subgroup.mem_bot).mpr (hbot σ hσ)
    rw [this, Subgroup.card_bot]
    norm_num
  push Not at hbot
  obtain ⟨σ₀, hσ₀, hσ₀1⟩ := hbot
  have hmap : P.map ψ ≤ (T : Subgroup G).map ψ := Subgroup.map_mono hPT
  let f : P.map ψ → Fin 2 := fun σ =>
    if (σ : MulAut (bStar (B : Subgroup G))) = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    by_cases hσ : (σ : MulAut (bStar (B : Subgroup G))) = 1
    · by_cases hτ : (τ : MulAut (bStar (B : Subgroup G))) = 1
      · rw [hσ, hτ]
      · have h1 : f σ = 0 := ite_eq_left_iff.mpr (fun h => absurd hσ h)
        have h2 : f τ = 1 := ite_eq_right_iff.mpr (fun h => absurd h hτ)
        rw [h1, h2] at h
        exact absurd h (by decide)
    · by_cases hτ : (τ : MulAut (bStar (B : Subgroup G))) = 1
      · have h1 : f σ = 1 := ite_eq_right_iff.mpr (fun h => absurd h hσ)
        have h2 : f τ = 0 := ite_eq_left_iff.mpr (fun h => absurd hτ h)
        rw [h1, h2] at h
        exact absurd h (by decide)
      · exact eq_of_apply_eq_self h3' h9B hR hys1 (hmap σ.2) (hmap τ.2) (hfix σ σ.2)
          (hfix τ τ.2) hσ hτ
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fin] at this

theorem forall_mod_of_normal_elem
    (hQ8 : ∃ K : Subgroup (MulAut (B : Subgroup G)),
      K ≤ ((T : Subgroup G).subgroupOf (normalizer ((B : Subgroup G) : Set G))).map
        (B : Subgroup G).normalizerMonoidHom ∧ Nonempty (K ≃* QuaternionGroup 2))
    {F : Subgroup G} (hFn : ∀ t ∈ (T : Subgroup G), ∀ f ∈ F, t * f * t⁻¹ ∈ F)
    (hF2 : ∀ f ∈ F, f * f = 1) (hFc : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f) {f : G} (hf : f ∈ F) :
    (∀ b ∈ (B : Subgroup G), f * b * f⁻¹ * b⁻¹ ∈ CFSG.pCore 2 G) ∨
      ∀ b ∈ (B : Subgroup G), f * b * f⁻¹ * b ∈ CFSG.pCore 2 G := by
  have hN : (bStar (B : Subgroup G)).Normal := (normal_and_centralizer_le T B hB9 hTB hBc).1
  obtain ⟨hcB, h3B, h9B⟩ := bStar_props B hB9 hBc hB3
  let _ : CommGroup (bStar (B : Subgroup G)) := { (inferInstance : Group _) with
    mul_comm := fun a b => Subtype.ext (hcB a a.2 b b.2) }
  have h3' : ∀ b : bStar (B : Subgroup G), b ^ 3 = 1 := fun b =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact h3B b b.2)
  set ψ := actMod (bStar (B : Subgroup G)) with hψ
  have htr : ∀ x y : bStar (B : Subgroup G), x ≠ 1 → y ≠ 1 →
      ∃ r ∈ (T : Subgroup G).map ψ, r x = y := by
    rintro ⟨_, d, hd, rfl⟩ ⟨_, d', hd', rfl⟩ hx hy
    have hd1 : d ≠ 1 := fun h => hx (by subst h; exact Subtype.ext (map_one _))
    have hd'1 : d' ≠ 1 := fun h => hy (by subst h; exact Subtype.ext (map_one _))
    obtain ⟨n, hnT, -, hnd⟩ := exists_conj_eq_of_quaternion T B hB9 hBc hB3 hQ8 hd hd' hd1 hd'1
    refine ⟨ψ n, Subgroup.mem_map_of_mem _ hnT, Subtype.ext ?_⟩
    rw [hψ, actMod_apply_coe]
    change QuotientGroup.mk' _ n * QuotientGroup.mk' _ d * (QuotientGroup.mk' _ n)⁻¹ =
      QuotientGroup.mk' _ d'
    rw [← hnd, map_mul, map_mul, map_inv]
  rcases eq_one_or_inv_of_normal h3' h9B htr (F := F.map ψ)
      (fun r hr g hg => by
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr
        obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hg
        rw [← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (hFn t ht f' hf'))
      (fun g hg => by
        obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hg
        rw [← map_mul, hF2 f' hf', map_one])
      (fun g hg g' hg' => by
        obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.mp hg
        obtain ⟨f'', hf'', rfl⟩ := Subgroup.mem_map.mp hg'
        rw [← map_mul, ← map_mul, hFc f' hf' f'' hf''])
      (Subgroup.mem_map_of_mem ψ hf) with h | h
  · left
    intro b hb
    exact (actMod_apply_eq_self_iff B f hb).mp (by rw [← hψ, h, MulAut.one_apply])
  · right
    intro b hb
    exact (actMod_apply_eq_inv_iff B f hb).mp (by rw [← hψ, h])

end Action

end CFSG.RankThree.PartTwo.Sec3
