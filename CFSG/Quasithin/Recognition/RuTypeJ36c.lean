module

public import CFSG.Quasithin.Recognition.RuTypeJ36b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

noncomputable abbrev NHB (b : G) : Subgroup G :=
  ruH M.T ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G)

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

noncomputable def iel : G := (M.exists_inv_T5_conj hbH hb5).choose

theorem iel_spec
    : iel hbH hb5 ∈ ruH M.T ∧ iel hbH hb5 * iel hbH hb5 = 1 ∧
    IsConj M.z (iel hbH hb5) ∧ iel hbH hb5 * b * (iel hbH hb5)⁻¹ = b⁻¹ ∧
    ∃ t ∈ M.T5 b, t * iel hbH hb5 * t⁻¹ = iel hbH hb5 * M.z :=
  (M.exists_inv_T5_conj hbH hb5).choose_spec

omit hbH hb5 in
theorem mem_normalizer_of_inv {c : G} (hc : c * b * c⁻¹ = b⁻¹) :
    c ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hc, inv_zpow']
  exact Subgroup.zpow_mem_zpowers _ _

theorem iel_mem_NHB : iel hbH hb5 ∈ M.NHB b :=
  ⟨(iel_spec hbH hb5).1, mem_normalizer_of_inv (iel_spec hbH hb5).2.2.2.1⟩

theorem exists_sylow_NHB : ∃ S : Sylow 2 (M.NHB b),
    Subgroup.zpowers (⟨iel hbH hb5, iel_mem_NHB hbH hb5⟩ : M.NHB b) ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.exists_le_sylow ?_
  have h2 : (⟨iel hbH hb5, iel_mem_NHB hbH hb5⟩ : M.NHB b) ^ 2 = 1 :=
    Subtype.ext (by simp [pow_two, (iel_spec hbH hb5).2.1])
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf (⟨iel hbH hb5, iel_mem_NHB hbH hb5⟩ : M.NHB b) ∣ 2 ^ 1 from
      orderOf_dvd_of_pow_eq_one h2)
  exact ⟨j, hj⟩

noncomputable def RB5 : Subgroup G :=
  ((exists_sylow_NHB hbH hb5).choose : Subgroup (M.NHB b)).map (M.NHB b).subtype

theorem RB5_le_NHB
    : RB5 hbH hb5 ≤ M.NHB b := Subgroup.map_subtype_le _

theorem RB5_le_H
    : RB5 hbH hb5 ≤ ruH M.T := fun _ hx => (RB5_le_NHB hbH hb5 hx).1

theorem RB5_le_normalizer
    : RB5 hbH hb5 ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
  fun _ hx => (RB5_le_NHB hbH hb5 hx).2

theorem iel_mem_RB5 : iel hbH hb5 ∈ RB5 hbH hb5 :=
  ⟨_, (exists_sylow_NHB hbH hb5).choose_spec (Subgroup.mem_zpowers _), rfl⟩

theorem RB5_isPGroup : IsPGroup 2 (RB5 hbH hb5) :=
  ((exists_sylow_NHB hbH hb5).choose.isPGroup').map _

theorem eq_RB5_of_le_NHB
    {S : Subgroup G} (hS : IsPGroup 2 S) (hRS : RB5 hbH hb5 ≤ S)
    (hSN : S ≤ M.NHB b) : S = RB5 hbH hb5 := by
  set S0 := (exists_sylow_NHB hbH hb5).choose
  have hle : (S0 : Subgroup (M.NHB b)) ≤ S.subgroupOf (M.NHB b) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRS ⟨x, hx, rfl⟩)
  have hS' : IsPGroup 2 (S.subgroupOf (M.NHB b)) :=
    hS.comap_of_injective (M.NHB b).subtype Subtype.val_injective
  have heq := S0.is_maximal' hS' hle
  apply le_antisymm _ hRS
  intro x hx
  have hx' : (⟨x, hSN hx⟩ : M.NHB b) ∈ S.subgroupOf (M.NHB b) := Subgroup.mem_subgroupOf.mpr hx
  rw [heq] at hx'
  exact ⟨_, hx', rfl⟩

omit hbH hb5 in
theorem conj_mem_T5_of_NHB {g x : G} (hg : g ∈ M.NHB b) (hx : x ∈ M.T5 b) :
    g * x * g⁻¹ ∈ M.T5 b :=
  ⟨M.conj_mem_Q hg.1 hx.1, conj_mem_G5_of_normalizes hg.2 hx.2⟩

theorem T5_le_RB5 : M.T5 b ≤ RB5 hbH hb5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT5N : M.T5 b ≤ M.NHB b := fun x hx =>
    ⟨pCoreOf_le 2 _ hx.1, G5_le_normalizer hx.2⟩
  have hnorm : ((M.T5 b).subgroupOf (M.NHB b)).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_T5_of_NHB g.2 hx⟩
  have hp : IsPGroup 2 ((M.T5 b).subgroupOf (M.NHB b)) := by
    rw [IsPGroup.iff_card, card_subgroupOf_of_le hT5N, card_T5 hbH hb5]
    exact ⟨3, by norm_num⟩
  intro x hx
  have h := hp.le_sylow_of_normal (exists_sylow_NHB hbH hb5).choose
    (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hT5N hx⟩ : M.NHB b) ∈ _)
  exact ⟨_, h, rfl⟩

theorem z_mem_RB5
    : M.z ∈ RB5 hbH hb5 := T5_le_RB5 hbH hb5 (z_mem_T5 hbH)

theorem mem_T5_of_two_elt
    {x : G} (hxH : x ∈ ruH M.T) (hxG : x ∈ G5 b) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ M.T5 b := by
  obtain ⟨t, ht, c, hc, rfl⟩ := CH5_eq_mul hbH hb5 ⟨hxH, hxG⟩
  have hct : c * t = t * c := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left (mem_G5.mp ht.2).symm j)).eq
  rw [(Commute.mul_pow hct _)] at hk
  have hc1 : c ^ 2 ^ k = 1 := by
    have h1 : c ^ 2 ^ k = (t ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have h5 : orderOf (c ^ 2 ^ k) ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b) (pow_mem hc (2 ^ k))
      rwa [Nat.card_zpowers, hb5] at this
    have h8 : orderOf (c ^ 2 ^ k) ∣ 8 := by
      rw [← card_T5 hbH hb5, h1]
      exact Subgroup.orderOf_dvd_natCard _ (inv_mem (pow_mem ht _))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h5 h8)
  have hc1' : c = 1 := by
    have h5 : orderOf c ∣ 5 := by
      have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers b) hc
      rwa [Nat.card_zpowers, hb5] at this
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc1
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right _ (by norm_num)) h5 h2)
  rw [hc1', one_mul]
  exact ht

theorem mem_T5_of_mem_RB5
    {x : G} (hx : x ∈ RB5 hbH hb5) (hxG : x ∈ G5 b) : x ∈ M.T5 b := by
  obtain ⟨k, hk⟩ := RB5_isPGroup hbH hb5 ⟨x, hx⟩
  exact mem_T5_of_two_elt hbH hb5 (RB5_le_H hbH hb5 hx) hxG
    (by simpa using congrArg Subtype.val hk)

omit [Finite G] hbH in
theorem conj_b_of_inv {w : G} (hwN : w ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (hw2 : w * w = 1) : w * b * w⁻¹ = b ∨ w * b * w⁻¹ = b⁻¹ := by
  classical
  have hmem : w * b * w⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.mp hwN b).mp (Subgroup.mem_zpowers b)
  have hfin : IsOfFinOrder b := by
    rw [← orderOf_pos_iff, hb5]; norm_num
  obtain ⟨m, hm, hmb⟩ := (hfin.mem_zpowers_iff_mem_range_orderOf).mp hmem |>
    Finset.mem_image.mp
  rw [Finset.mem_range, hb5] at hm
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hb : b = b ^ (m * m) := by
    calc b = w * (w * b * w⁻¹) * w⁻¹ := by
          rw [hwinv]
          calc b = (w * w) * b * (w * w) := by rw [hw2]; group
            _ = w * (w * b * w) * w := by group
      _ = w * b ^ m * w⁻¹ := by rw [← hmb]
      _ = (w * b * w⁻¹) ^ m := by rw [conj_pow]
      _ = b ^ (m * m) := by rw [← hmb, ← pow_mul]
  have hb5' := pow_five_of_orderOf hb5
  interval_cases m
  · exfalso
    have : b = 1 := by simpa using hb
    rw [this, orderOf_one] at hb5
    norm_num at hb5
  · left; rw [← hmb, pow_one]
  · exfalso
    have h3 : b ^ 3 = 1 := by
      have : b ^ 4 = b := by simpa using hb.symm
      calc b ^ 3 = b ^ 4 * b⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hb5] at this
    norm_num at this
  · exfalso
    have h3 : b ^ 3 = 1 := by
      have h9 : b ^ 9 = b := by simpa using hb.symm
      calc b ^ 3 = b ^ 9 * (b ^ 5)⁻¹ * b⁻¹ := by group
        _ = 1 := by rw [h9, hb5', inv_one, mul_one, mul_inv_cancel]
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hb5] at this
    norm_num at this
  · right
    rw [← hmb]
    calc b ^ 4 = b ^ 5 * b⁻¹ := by group
      _ = b⁻¹ := by rw [hb5', one_mul]

theorem eq_z_of_central_RB5
    {w : G} (hwR : w ∈ RB5 hbH hb5) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwc : ∀ r ∈ RB5 hbH hb5, w * r = r * w) : w = M.z := by
  obtain ⟨hiH, hi2, -, hib, t, ht, hti⟩ := iel_spec hbH hb5
  set i := iel hbH hb5
  have hiR : i ∈ RB5 hbH hb5 := iel_mem_RB5 hbH hb5
  have htR : t ∈ RB5 hbH hb5 := T5_le_RB5 hbH hb5 ht
  have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
  rcases conj_b_of_inv hb5 (RB5_le_normalizer hbH hb5 hwR) hw2 with h | h
  ·
    have hwG : w ∈ G5 b := mem_G5.mpr (by
      calc w * b = (w * b * w⁻¹) * w := by group
        _ = b * w := by rw [h])
    exact eq_z_of_T5 hbH hb5 (mem_T5_of_mem_RB5 hbH hb5 hwR hwG) hw2' hw1
  · exfalso
    have hwi : w * i ∈ G5 b := mem_G5.mpr (by
      have e : (w * i) * b * (w * i)⁻¹ = b := by
        calc (w * i) * b * (w * i)⁻¹ = w * (i * b * i⁻¹) * w⁻¹ := by group
          _ = (w * b * w⁻¹)⁻¹ := by rw [hib]; group
          _ = b := by rw [h, inv_inv]
      calc w * i * b = ((w * i) * b * (w * i)⁻¹) * (w * i) := by group
        _ = b * (w * i) := by rw [e])
    have hwiT := mem_T5_of_mem_RB5 hbH hb5 (mul_mem hwR hiR) hwi
    have hwic : w * i = i * w := hwc i hiR
    have hwi2 : (w * i) ^ 2 = 1 := by
      calc (w * i) ^ 2 = w * (i * w) * i := by rw [pow_two]; group
        _ = w * (w * i) * i := by rw [hwic]
        _ = (w * w) * (i * i) := by group
        _ = 1 := by rw [hw2, hi2, one_mul]
    have hiinv : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
    have hwt : w * t = t * w := hwc t htR
    by_cases h1 : w * i = 1
    ·
      have hwe : w = i := by
        calc w = (w * i) * i⁻¹ := by group
          _ = i := by rw [h1, one_mul, hiinv]
      rw [hwe] at hwt
      have : t * i * t⁻¹ = i := by rw [← hwt, mul_inv_cancel_right]
      rw [hti] at this
      exact M.z_ne_one (by simpa using this)
    ·
      have hz := eq_z_of_T5 hbH hb5 hwiT hwi2 h1
      have hwe : w = i * M.z := by
        calc w = (w * i) * i⁻¹ := by group
          _ = M.z * i := by rw [hz, hiinv]
          _ = i * M.z := (M.Z_comm_H M.z_mem_Z hiH)
      have htz : t * M.z = M.z * t := (M.Z_comm_H M.z_mem_Z (pCoreOf_le 2 _ ht.1)).symm
      rw [hwe] at hwt
      have : t * (i * M.z) * t⁻¹ = i * M.z := by rw [← hwt, mul_inv_cancel_right]
      have e : t * (i * M.z) * t⁻¹ = (t * i * t⁻¹) * M.z := by
        calc t * (i * M.z) * t⁻¹ = t * i * (M.z * t⁻¹) := by group
          _ = t * i * (t⁻¹ * M.z) := by
              rw [(Commute.inv_left (show Commute t M.z from htz)).eq.symm]
          _ = (t * i * t⁻¹) * M.z := by group
      rw [e, hti, mul_assoc, M.z_mul_self, mul_one] at this
      exact M.z_ne_one (by simpa using this.symm)

theorem H_inf_normalizer_P5_le {g : G} (hgH : g ∈ ruH M.T)
    (hgN : g ∈ Subgroup.normalizer (P5 b : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have hyP : y ∈ P5 b := zpowers_le_P5 hb5 hy
  have hgy : g * y * g⁻¹ ∈ P5 b := (Subgroup.mem_normalizer_iff.mp hgN y).mp hyP
  have hzg : M.z * g = g * M.z := M.mem_H_iff_comm.mp hgH
  have hzy : M.z * y = y * M.z := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (mem_G5.mp (z_mem_G5 hbH)) k)).eq
  refine mem_zpowers_of_P5_comm_z hbH hb5 hgy ?_
  have hc : Commute M.z (g * y * g⁻¹) :=
    ((show Commute M.z g from hzg).mul_right (show Commute M.z y from hzy)).mul_right
      (Commute.inv_right (show Commute M.z g from hzg))
  exact hc.eq.symm

omit hbH hb5 in
theorem normalizer_B5_le_normalizer_P5 :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (P5 b : Set G) :=
  fun _ hc => mem_normalizer_of_conj_mem fun _ hx => conj_mem_P5_of_normalizes hc hx

theorem eq_RB5_of_le_normalizer_P5
    {S : Subgroup G} (hS : IsPGroup 2 S) (hRS : RB5 hbH hb5 ≤ S)
    (hSN : S ≤ Subgroup.normalizer (P5 b : Set G)) : S = RB5 hbH hb5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set Rs := (RB5 hbH hb5).subgroupOf S with hRsdef
  have hlt : Rs < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm (fun x hx => ?_) hRS)
    have : (⟨x, hx⟩ : S) ∈ Rs := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨s, hsN, hsR⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent Rs hlt)
  have hconj : ∀ r ∈ RB5 hbH hb5, (s : G) * r * (s : G)⁻¹ ∈ RB5 hbH hb5 := by
    intro r hr
    have h := (Subgroup.mem_normalizer_iff.mp hsN ⟨r, hRS hr⟩).mp
      (Subgroup.mem_subgroupOf.mpr hr)
    simpa using Subgroup.mem_subgroupOf.mp h
  have hconj' : ∀ r ∈ RB5 hbH hb5, (s : G)⁻¹ * r * s ∈ RB5 hbH hb5 := by
    intro r hr
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hsN) ⟨r, hRS hr⟩).mp
      (Subgroup.mem_subgroupOf.mpr hr)
    simpa using Subgroup.mem_subgroupOf.mp h
  have hzR := z_mem_RB5 hbH hb5
  have hzc : ∀ r ∈ RB5 hbH hb5, M.z * r = r * M.z := fun r hr =>
    M.mem_H_iff_comm.mp (RB5_le_H hbH hb5 hr)
  have hsz : (s : G) * M.z * (s : G)⁻¹ = M.z := by
    refine eq_z_of_central_RB5 hbH hb5 (hconj _ hzR) ?_ ?_ ?_
    · calc (s : G) * M.z * (s : G)⁻¹ * ((s : G) * M.z * (s : G)⁻¹) =
          (s : G) * (M.z * M.z) * (s : G)⁻¹ := by group
        _ = 1 := by rw [M.z_mul_self]; group
    · intro h1
      apply M.z_ne_one
      calc M.z = (s : G)⁻¹ * ((s : G) * M.z * (s : G)⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    · intro r hr
      have h1 := hzc _ (hconj' r hr)
      calc (s : G) * M.z * (s : G)⁻¹ * r = (s : G) * (M.z * ((s : G)⁻¹ * r * s)) * (s : G)⁻¹ := by
            group
        _ = (s : G) * (((s : G)⁻¹ * r * s) * M.z) * (s : G)⁻¹ := by rw [h1]
        _ = r * ((s : G) * M.z * (s : G)⁻¹) := by group
  have hsH : (s : G) ∈ ruH M.T := M.mem_H_iff_comm.mpr (by
    calc M.z * s = ((s : G) * M.z * (s : G)⁻¹) * s := by rw [hsz]
      _ = s * M.z := by group)
  have hsNB := H_inf_normalizer_P5_le hbH hb5 hsH (hSN s.2)
  have hSi : IsPGroup 2 (S ⊓ M.NHB b : Subgroup G) := hS.to_le inf_le_left
  have heq := eq_RB5_of_le_NHB hbH hb5 hSi (le_inf hRS (RB5_le_NHB hbH hb5)) inf_le_right
  apply hsR
  rw [Subgroup.mem_subgroupOf, ← heq]
  exact ⟨s.2, hsH, hsNB⟩

theorem card_RB5
    : Nat.card (RB5 hbH hb5) = 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set NB := Subgroup.normalizer (Subgroup.zpowers b : Set G)
  have hRN : RB5 hbH hb5 ≤ NB := RB5_le_normalizer hbH hb5
  let S : Sylow 2 NB :=
    { toSubgroup := (RB5 hbH hb5).subgroupOf NB
      isPGroup' := (RB5_isPGroup hbH hb5).comap_of_injective NB.subtype Subtype.val_injective
      is_maximal' := fun {Q} hQ hle => by
        have hQ' : IsPGroup 2 (Q.map NB.subtype) := hQ.map _
        have hRQ : RB5 hbH hb5 ≤ Q.map NB.subtype := fun x hx =>
          ⟨⟨x, hRN hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
        have heq := eq_RB5_of_le_normalizer_P5 hbH hb5 hQ' hRQ
          ((Subgroup.map_subtype_le Q).trans normalizer_B5_le_normalizer_P5)
        ext x
        rw [Subgroup.mem_subgroupOf, ← heq]
        exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by
          rw [← Subtype.ext hyx]; exact hy⟩ }
  have h := S.card_eq_multiplicity
  rw [show (S : Subgroup NB) = (RB5 hbH hb5).subgroupOf NB from rfl,
    card_subgroupOf_of_le hRN, card_normalizer_B5 hbH hb5] at h
  rw [h]
  have : (4000 : ℕ).factorization 2 = 5 := by
    rw [show (4000 : ℕ) = 2 ^ 5 * 125 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 125 by norm_num)]
  rw [this]
  norm_num

end Five

end RuDataM

end CFSG.Quasithin.RuType
