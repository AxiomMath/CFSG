module

public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IsElemTwo (A : Subgroup G) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a * a = 1

@[expose] noncomputable def famG (T : Subgroup G) (i : ℕ) : Set (Subgroup G) :=
  {A | A ≤ T ∧ IsElemTwo A ∧ Nat.card A = 2 ^ (CFSG.pRank 2 T - i)}

@[expose] noncomputable def jG (T : Subgroup G) (i : ℕ) : Subgroup G := sSup (famG T i)

@[expose] def omegaG (J : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ J ∧ (∀ x ∈ J, z * x = x * z) ∧ z * z = 1}
  one_mem' := ⟨J.one_mem, fun x _ => by rw [one_mul, mul_one], one_mul 1⟩
  mul_mem' := by
    rintro a b ⟨haJ, hac, ha2⟩ ⟨hbJ, hbc, hb2⟩
    refine ⟨J.mul_mem haJ hbJ, fun x hx => ?_, ?_⟩
    · rw [mul_assoc, hbc x hx, ← mul_assoc, hac x hx, mul_assoc]
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hac b hbJ]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haJ, hac, ha2⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    exact ⟨J.inv_mem haJ, fun x hx => by rw [hinv]; exact hac x hx, by rw [hinv]; exact ha2⟩

theorem mem_omegaG {J : Subgroup G} {z : G} :
    z ∈ omegaG J ↔ z ∈ J ∧ (∀ x ∈ J, z * x = x * z) ∧ z * z = 1 := Iff.rfl

theorem omegaG_le (J : Subgroup G) : omegaG J ≤ J := fun _ h => h.1

theorem isElemTwo_omegaG (J : Subgroup G) : IsElemTwo (omegaG J) :=
  ⟨fun _ ha _ hb => ha.2.1 _ hb.1, fun _ ha => ha.2.2⟩

theorem mem_famG {T A : Subgroup G} {i : ℕ} :
    A ∈ famG T i ↔ A ≤ T ∧ IsElemTwo A ∧ Nat.card A = 2 ^ (CFSG.pRank 2 T - i) := Iff.rfl

theorem le_jG {T A : Subgroup G} {i : ℕ} (hA : A ∈ famG T i) : A ≤ jG T i := le_sSup hA

theorem isElementaryAbelian_of_isElemTwo {T A : Subgroup G} (hA : IsElemTwo A) :
    CFSG.IsElementaryAbelian 2 (A.subgroupOf T) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Subtype.ext (hA.1 _ a.2 _ b.2))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext; apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, pow_two, Subgroup.coe_one, Subgroup.coe_one]
      exact hA.2 _ x.2 }

theorem isElemTwo_map_of_isElementaryAbelian {T : Subgroup G} {A : Subgroup T}
    (hA : CFSG.IsElementaryAbelian 2 A) : IsElemTwo (A.map T.subtype) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := (hA.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have := congrArg (fun x : A => ((x : T) : G)) this
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) ⟨a, ha⟩
    have := congrArg (fun x : A => ((x : T) : G)) h
    simpa [pow_two] using this

theorem map_higherElemThompson [Finite G] (T : Subgroup G) (i : ℕ) :
    (CFSG.higherElemThompson T i).map T.subtype = jG T i := by
  rw [CFSG.higherElemThompson, (Subgroup.gc_map_comap T.subtype).l_sSup, jG, sSup_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    rw [CFSG.mem_higherElemThompsonFamily_iff] at hA
    refine le_iSup₂_of_le (A.map T.subtype)
      ⟨Subgroup.map_subtype_le A, isElemTwo_map_of_isElementaryAbelian hA.1, ?_⟩ le_rfl
    rw [Subgroup.card_map_of_injective T.subtype_injective, hA.2]
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, hA2, hcard⟩ := hA
    have hmem : A.subgroupOf T ∈ CFSG.higherElemThompsonFamily T i := by
      rw [CFSG.mem_higherElemThompsonFamily_iff]
      refine ⟨isElementaryAbelian_of_isElemTwo hA2, ?_⟩
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv
    have hmap : (A.subgroupOf T).map T.subtype = A := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAT]
    rw [← hmap]
    exact le_iSup₂_of_le (A.subgroupOf T) hmem le_rfl

theorem map_omegaOneCenter (T : Subgroup G) (J : Subgroup T) :
    (CFSG.omegaOneCenter J).map T.subtype = omegaG (J.map T.subtype) := by
  ext z
  constructor
  · rintro ⟨w, ⟨⟨c, hc, rfl⟩, hc2⟩, rfl⟩
    refine ⟨⟨c, c.2, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have := (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩).symm
      exact congrArg (fun y : J => ((y : T) : G)) this
    · have : ((c : T) : G) ^ 2 = 1 := by
        have := congrArg Subtype.val hc2
        simpa using this
      rwa [pow_two] at this
  · rintro ⟨⟨w, hw, rfl⟩, hcomm, hz2⟩
    refine ⟨w, ⟨⟨⟨w, hw⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩, ?_⟩, rfl⟩
    · intro x
      apply Subtype.ext; apply Subtype.ext
      exact (hcomm _ ⟨x, x.2, rfl⟩).symm
    · apply Subtype.ext
      rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
      exact hz2

theorem omegaG_normal {J : Subgroup G} (hJ : J.Normal) : (omegaG J).Normal := by
  constructor
  rintro z ⟨hzJ, hzc, hz2⟩ g
  refine ⟨hJ.conj_mem z hzJ g, fun x hx => ?_, ?_⟩
  · have hx' : g⁻¹ * x * g ∈ J := by
      have := hJ.conj_mem x hx g⁻¹
      rwa [inv_inv] at this
    have h := hzc _ hx'
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h]
      _ = x * (g * z * g⁻¹) := by group
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]

theorem map_conj_mem_famG {T A : Subgroup G} {i : ℕ} (hA : A ∈ famG T i) (g : G)
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ T) : A.map (MulAut.conj g).toMonoidHom ∈ famG T i := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA.2.2]; positivity)
  obtain ⟨hAT, hA2, hcard⟩ := hA
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hg a ha
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hA2.1 a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [hA2.2 a ha, mul_one, mul_inv_cancel]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem isElemTwo_sup {K L : Subgroup G} (hK : IsElemTwo K) (hL : IsElemTwo L)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) : IsElemTwo (K ⊔ L) := by
  have hnorm : K ≤ normalizer (L : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : k * x * k⁻¹ = x := by rw [hKL k hk x hx, mul_inv_cancel_right]
      rw [this]; exact hx
    · intro hx
      have hy := hKL k hk _ hx
      have h2 : x = k * x * k⁻¹ := by
        calc x = k⁻¹ * (k * x * k⁻¹ * k) := by group
          _ = k⁻¹ * (k * (k * x * k⁻¹)) := by rw [hy]
          _ = k * x * k⁻¹ := by group
      rw [h2]; exact hx
  have hmem : ∀ x, x ∈ K ⊔ L ↔ ∃ k ∈ K, ∃ l ∈ L, k * l = x := by
    intro x
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K L hnorm, Set.mem_mul]
    constructor
    · rintro ⟨k, hk, l, hl, rfl⟩; exact ⟨k, hk, l, hl, rfl⟩
    · rintro ⟨k, hk, l, hl, rfl⟩; exact ⟨k, hk, l, hl, rfl⟩
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨k, hk, l, hl, rfl⟩ := (hmem a).mp ha
    obtain ⟨k', hk', l', hl', rfl⟩ := (hmem b).mp hb
    calc k * l * (k' * l') = k * (l * k') * l' := by group
      _ = k * (k' * l) * l' := by rw [hKL k' hk' l hl]
      _ = k * k' * (l * l') := by group
      _ = k' * k * (l' * l) := by rw [hK.1 k hk k' hk', hL.1 l hl l' hl']
      _ = k' * (k * l') * l := by group
      _ = k' * (l' * k) * l := by rw [hKL k hk l' hl']
      _ = k' * l' * (k * l) := by group
  · obtain ⟨k, hk, l, hl, rfl⟩ := (hmem a).mp ha
    calc k * l * (k * l) = k * (l * k) * l := by group
      _ = k * (k * l) * l := by rw [hKL k hk l hl]
      _ = (k * k) * (l * l) := by group
      _ = 1 := by rw [hK.2 k hk, hL.2 l hl, one_mul]

theorem jG_normal [Finite G] {T : Subgroup G} {i : ℕ}
    (h : ∀ g : G, ∀ A ∈ famG T i, ∀ a ∈ A, g * a * g⁻¹ ∈ T) : (jG T i).Normal := by
  constructor
  intro n hn g
  have hle : (jG T i).map (MulAut.conj g).toMonoidHom ≤ jG T i := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    exact iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA g (h g A hA))
  exact hle ⟨n, hn, rfl⟩

theorem card_le_two_pow_pRank [Finite G] {T A : Subgroup G} (hAT : A ≤ T) (hA : IsElemTwo A) :
    Nat.card A ≤ 2 ^ CFSG.pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]; exact hA.2 a a.2)⟩
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hmem : k ∈ {r : ℕ | ∃ B : Subgroup T, CFSG.IsElementaryAbelian 2 B ∧
      Nat.card B = 2 ^ r} :=
    ⟨A.subgroupOf T, isElementaryAbelian_of_isElemTwo hA, by
      rw [← hk]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv⟩
  have hbdd : BddAbove {r : ℕ | ∃ B : Subgroup T, CFSG.IsElementaryAbelian 2 B ∧
      Nat.card B = 2 ^ r} := by
    refine ⟨Nat.card T, fun r ⟨B, _, hB⟩ => ?_⟩
    have h1 : 2 ^ r ≤ Nat.card T := hB ▸ Subgroup.card_le_card_group B
    exact (Nat.lt_two_pow_self).le.trans h1
  have := le_csSup hbdd hmem
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) this

theorem card_sup_mul_card_inf_of_commute [Finite G] {K L : Subgroup G}
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) :
    Nat.card ↥(K ⊔ L) * Nat.card ↥(K ⊓ L) = Nat.card K * Nat.card L := by
  let μ : K × L →* G :=
    { toFun := fun p => (p.1 : G) * p.2
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (p.1 : G) * q.1 * (p.2 * q.2) = p.1 * (q.1 * p.2) * q.2 := by group
          _ = p.1 * (p.2 * q.1) * q.2 := by rw [hKL _ q.1.2 _ p.2.2]
          _ = p.1 * p.2 * (q.1 * q.2) := by group }
  have hrange : μ.range = K ⊔ L := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact Subgroup.mul_mem_sup p.1.2 p.2.2
    · refine sup_le (fun k hk => ⟨(⟨k, hk⟩, 1), by simp [μ]⟩)
        (fun l hl => ⟨(1, ⟨l, hl⟩), by simp [μ]⟩)
  have hker : Nat.card μ.ker = Nat.card ↥(K ⊓ L) := by
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), p.1.1.2, ?_⟩
        invFun := fun x => ⟨(⟨x, x.2.1⟩, ⟨(x : G)⁻¹, L.inv_mem x.2.2⟩), by
          simp [μ, MonoidHom.mem_ker]⟩
        left_inv := fun p => ?_
        right_inv := fun x => rfl }
    · have h1 : (p.1.1 : G) * p.1.2 = 1 := p.2
      have : (p.1.1 : G) = (p.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact L.inv_mem p.1.2.2
    · have h1 : (p.1.1 : G) * p.1.2 = 1 := p.2
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact (eq_inv_of_mul_eq_one_right h1).symm
  have h := Subgroup.card_mul_index μ.ker
  rw [Subgroup.index_ker, hrange, hker, Nat.card_prod] at h
  rw [mul_comm]
  exact h

end CFSG.RankThree.PartTwo.Sec3
