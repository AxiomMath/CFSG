module

public import CFSG.Sporadic.Recognition.JankoWongBSStep
public import CFSG.Sporadic.Recognition.JankoWongCHa

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

@[expose] def permU0 : Perm (Fin 8) := swap 3 4 * swap 5 6

@[expose] def permV0 : Perm (Fin 8) := swap 3 5 * swap 4 6

theorem permU0_sq : permU0 ^ 2 = 1 := by unfold permU0; decide
theorem permV0_sq : permV0 ^ 2 = 1 := by unfold permV0; decide

theorem cycleType_permU0 : permU0.cycleType = {2, 2} := by
  unfold permU0
  exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_permV0 : permV0.cycleType = {2, 2} := by
  unfold permV0
  exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_permU0_mul_permV0 : (permU0 * permV0).cycleType = {2, 2} := by
  unfold permU0 permV0
  exact cycleType_type22_of_card (by decide) (by decide)

theorem permU0_comm_permA3 : permU0 * permA3 = permA3 * permU0 := by
  unfold permU0 permA3; decide

theorem permV0_comm_permA3 : permV0 * permA3 = permA3 * permV0 := by
  unfold permV0 permA3; decide

theorem permU0_ne_permV0 : permU0 ≠ permV0 := by unfold permU0 permV0; decide

theorem permU0_ne_one : permU0 ≠ 1 := by unfold permU0; decide

theorem permV0_ne_one : permV0 ≠ 1 := by unfold permV0; decide

theorem permV0_ne_permU0_pow (n : ℤ) : permV0 ≠ permU0 ^ n := by
  intro h
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [zpow_mul] at h
    have : permU0 ^ (2 : ℤ) = 1 := by simpa using permU0_sq
    rw [this, one_zpow] at h
    exact permV0_ne_one h
  · rw [zpow_add_one, zpow_mul] at h
    have : permU0 ^ (2 : ℤ) = 1 := by simpa using permU0_sq
    rw [this, one_zpow, one_mul] at h
    exact permU0_ne_permV0 h.symm

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem exists_quaternion_pair :
    ∃ i j : S.H, S.ρ i = permU0 ∧ S.ρ j = permV0 ∧ i ^ 2 = zIn S.z ∧ j ^ 2 = zIn S.z ∧
      (i * j) ^ 2 = zIn S.z ∧ i * c.a = c.a * i ∧ j * c.a = c.a * j := by
  obtain ⟨i, hi⟩ := S.cover.exists_lift (p := permU0) (sign_of_type22 cycleType_permU0)
  obtain ⟨j, hj⟩ := S.cover.exists_lift (p := permV0) (sign_of_type22 cycleType_permV0)
  refine ⟨i, j, hi, hj, S.cover.sq_eq_z_of_type22 (by rw [hi]; exact cycleType_permU0),
    S.cover.sq_eq_z_of_type22 (by rw [hj]; exact cycleType_permV0),
    S.cover.sq_eq_z_of_type22 (by rw [map_mul, hi, hj]; exact cycleType_permU0_mul_permV0),
    S.cover.commute_of_cube c.ha3 (by rw [hi, c.ha]; exact permU0_comm_permA3),
    S.cover.commute_of_cube c.ha3 (by rw [hj, c.ha]; exact permV0_comm_permA3)⟩

@[expose] def Kg : Subgroup G := centralizer ({(c.a : G)} : Set G)

theorem a_comm_z : (c.a : G) * S.z = S.z * (c.a : G) :=
  Subgroup.mem_centralizer_singleton_iff.mp c.a.2

theorem z_mem_Kg : S.z ∈ c.Kg := Subgroup.mem_centralizer_singleton_iff.mpr c.a_comm_z.symm

@[expose] def zK : ↥c.Kg := ⟨S.z, c.z_mem_Kg⟩

theorem exists_quaternion_subgroup :
    ∃ D : Subgroup S.H, Nonempty (D ≃* QuaternionGroup 2) ∧ zIn S.z ∈ D ∧
      ∀ d ∈ D, d * c.a = c.a * d := by
  obtain ⟨i, j, hi, hj, hi2, hj2, hij2, hia, hja⟩ := c.exists_quaternion_pair
  have hiD : i ∈ closure ({i, j} : Set S.H) := subset_closure (by simp)
  have hjD : j ∈ closure ({i, j} : Set S.H) := subset_closure (by simp)
  have hz : zIn S.z ∈ closure ({i, j} : Set S.H) := by
    rw [← hi2]; exact pow_mem hiD 2
  have hcomm : ∀ d ∈ closure ({i, j} : Set S.H), d * c.a = c.a * d := by
    have hle : closure ({i, j} : Set S.H) ≤ centralizer ({c.a} : Set S.H) := by
      rw [closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hia
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hja
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hd)
  refine ⟨closure ({i, j} : Set S.H), ?_, hz, hcomm⟩
  have hz2 : zIn S.z ^ 2 = 1 := S.cover.sq_eq_one
  have hzne : zIn S.z ≠ 1 := S.cover.ne_one
  have hzc : ∀ y : S.H, y * zIn S.z = zIn S.z * y := fun y => S.cover.mul_z_comm y
  have hinv : ∀ y : S.H, y ^ 2 = zIn S.z → y⁻¹ = y * zIn S.z := fun y hy => by
    apply inv_eq_of_mul_eq_one_right
    calc y * (y * zIn S.z) = (y * y) * zIn S.z := (mul_assoc _ _ _).symm
      _ = y ^ 2 * zIn S.z := by rw [pow_two]
      _ = 1 := by rw [hy, ← pow_two, hz2]
  have hio : orderOf i = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ¬ i ^ 2 ^ 1 = 1 := by rw [pow_one, hi2]; exact hzne
    have h2 : i ^ 2 ^ (1 + 1) = 1 := by
      have : (2 : ℕ) ^ (1 + 1) = 2 * 2 := by norm_num
      rw [this, pow_mul, hi2, hz2]
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  have hjzp : j ∉ zpowers i := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
    have := congrArg S.ρ hn
    rw [map_zpow, hi, hj] at this
    exact permV0_ne_permU0_pow n this.symm
  have hji : j * i * j⁻¹ = i⁻¹ := by
    have h1 : i * j * (i * j) = zIn S.z := by rw [← pow_two]; exact hij2
    have hjinv := hinv j hj2
    have hiinv := hinv i hi2
    have h2 : j * i * j = i⁻¹ * zIn S.z := by
      calc j * i * j = i⁻¹ * (i * j * (i * j)) := by group
        _ = i⁻¹ * zIn S.z := by rw [h1]
    calc j * i * j⁻¹ = j * i * (j * zIn S.z) := by rw [hjinv]
      _ = (j * i * j) * zIn S.z := by group
      _ = i⁻¹ * zIn S.z * zIn S.z := by rw [h2]
      _ = i⁻¹ := by rw [mul_assoc, ← pow_two, hz2, mul_one]
  have hgen : (⊤ : Subgroup (closure ({i, j} : Set S.H))) =
      closure ({(⟨i, hiD⟩ : closure ({i, j} : Set S.H)), ⟨j, hjD⟩} : Set _) := by
    rw [← closure_closure_coe_preimage (k := ({i, j} : Set S.H))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have hnf := CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2) (by norm_num)
    (x := (⟨i, hiD⟩ : closure ({i, j} : Set S.H))) (y := ⟨j, hjD⟩) hgen.symm
    (by rw [Subgroup.orderOf_mk, hio]) (by
      intro h
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
      apply hjzp
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩)
    (Subtype.ext (by simpa using hj2.trans hi2.symm))
    (Subtype.ext (by simpa using hji))
  obtain ⟨e, -⟩ := hnf.1
  exact ⟨e.symm⟩

theorem exists_quaternion_sylow_Kg :
    ∃ T : Sylow 2 ↥c.Kg, Nonempty (↥(T : Subgroup ↥c.Kg) ≃* QuaternionGroup 2) ∧
      c.zK ∈ (T : Subgroup ↥c.Kg) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, ⟨eD⟩, hzD, hDa⟩ := c.exists_quaternion_subgroup
  have hDGK : D.map S.H.subtype ≤ c.Kg := by
    rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hDa d hd))
  let eDK : ↥((D.map S.H.subtype).subgroupOf c.Kg) ≃* D :=
    (Subgroup.subgroupOfEquivOfLe hDGK).trans
      (Subgroup.equivMapOfInjective D S.H.subtype S.H.subtype_injective).symm
  have hDKcard : Nat.card ↥((D.map S.H.subtype).subgroupOf c.Kg) = 8 := by
    rw [Nat.card_congr eDK.toEquiv, Nat.card_congr eD.toEquiv, Nat.card_eq_fintype_card,
      QuaternionGroup.card]
  have hDKp : IsPGroup 2 ↥((D.map S.H.subtype).subgroupOf c.Kg) :=
    IsPGroup.of_card (n := 3) (by rw [hDKcard]; norm_num)
  obtain ⟨T, hT⟩ := hDKp.exists_le_sylow
  have hT8 : Nat.card T = 8 := S.card_sylow_centralizer_type3 c.ha3 c.cycleType_a T
  have hDT : (D.map S.H.subtype).subgroupOf c.Kg = (T : Subgroup ↥c.Kg) :=
    Subgroup.eq_of_le_of_card_ge hT (by rw [hT8, hDKcard])
  refine ⟨T, ⟨(MulEquiv.subgroupCongr hDT.symm).trans (eDK.trans eD)⟩, ?_⟩
  rw [← hDT]
  exact Subgroup.mem_subgroupOf.mpr ⟨zIn S.z, hzD, rfl⟩

theorem orderOf_zK : orderOf c.zK = 2 := by
  have hz2 : c.zK ^ 2 = 1 := Subtype.ext (by
    have : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
    simpa [zK] using this)
  have hz1 : c.zK ≠ 1 := fun e =>
    S.cover.ne_one (Subtype.ext (congrArg (fun y : ↥c.Kg => (y : G)) e))
  exact orderOf_eq_prime hz2 hz1

theorem hBS_Kg : (QuotientGroup.mk c.zK : ↥c.Kg ⧸ CFSG.oddCore ↥c.Kg) ∈
    Subgroup.center (↥c.Kg ⧸ CFSG.oddCore ↥c.Kg) := by
  obtain ⟨T, ⟨eT⟩, hzT⟩ := c.exists_quaternion_sylow_Kg
  exact (CFSG.Adapters.brauer_suzuki 3 (by norm_num) T ⟨eT⟩ c.zK hzT c.orderOf_zK).2

theorem card_centralizer_zK : Nat.card (centralizer ({c.zK} : Set ↥c.Kg)) = 360 := by
  rw [card_centralizer_subtype c.zK]
  have h1 : Nat.card ↥(c.Kg ⊓ centralizer ({S.z} : Set G)) = Nat.card ↥(S.H ⊓ c.Kg) := by
    rw [inf_comm]
  have h2 := card_centralizer_subtype (C := S.H) c.a
  have h3 := S.cover.card_centralizer_type3 c.ha3 c.cycleType_a
  show Nat.card ↥(c.Kg ⊓ centralizer ({S.z} : Set G)) = 360
  rw [h1, ← h3, h2]
  rfl

theorem a_mem_Kg : (c.a : G) ∈ c.Kg := Subgroup.mem_centralizer_singleton_iff.mpr rfl

@[expose] def aK : ↥c.Kg := ⟨(c.a : G), c.a_mem_Kg⟩

theorem odd_normal_le_zpowers_aK {W : Subgroup ↥c.Kg}
    (hW : W ≤ centralizer ({c.zK} : Set ↥c.Kg))
    (hn : ∀ t ∈ centralizer ({c.zK} : Set ↥c.Kg), ∀ w ∈ W, t * w * t⁻¹ ∈ W)
    (hodd : Odd (Nat.card W)) : W ≤ zpowers c.aK := by
  set WG : Subgroup G := W.map c.Kg.subtype with hWG
  have hWH : WG ≤ S.H := by
    rintro _ ⟨w, hw, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hW hw)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  have hcard : Nat.card (WG.subgroupOf S.H) = Nat.card W := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv,
      Subgroup.card_map_of_injective c.Kg.subtype_injective]
  have hle : WG.subgroupOf S.H ≤ zpowers c.a := by
    refine c.odd_normal_le_zpowers_a (W := WG.subgroupOf S.H) ?_ ?_ (by rw [hcard]; exact hodd)
    · intro w hw
      have hwG : (w : G) ∈ WG := Subgroup.mem_subgroupOf.mp hw
      obtain ⟨w', hw', hw'e⟩ := hwG
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp w'.2
      show (w : G) * (c.a : G) = (c.a : G) * (w : G)
      rw [← hw'e]
      exact this
    · intro t ht w hw
      have htK : (t : G) ∈ c.Kg :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ht))
      let tK : ↥c.Kg := ⟨(t : G), htK⟩
      have htz : tK ∈ centralizer ({c.zK} : Set ↥c.Kg) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp t.2
      obtain ⟨w', hw', hw'e⟩ := Subgroup.mem_subgroupOf.mp hw
      have := hn tK htz w' hw'
      apply Subgroup.mem_subgroupOf.mpr
      have hw'e' : (w' : G) = (w : G) := hw'e
      exact ⟨tK * w' * tK⁻¹, this, by
        show (t : G) * (w' : G) * (t : G)⁻¹ = ((t * w * t⁻¹ : S.H) : G)
        rw [hw'e']; rfl⟩
  intro w hw
  have hwG : (w : G) ∈ WG := ⟨w, hw, rfl⟩
  have hwH : (w : G) ∈ S.H := hWH hwG
  have hmem : (⟨(w : G), hwH⟩ : S.H) ∈ WG.subgroupOf S.H := Subgroup.mem_subgroupOf.mpr hwG
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hle hmem)
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext ?_⟩
  have := congrArg Subtype.val hn
  simpa [aK] using this

end Ctx


theorem three_pow_six_dvd_card
    (S : Setup G) : 3 ^ 6 ∣ Nat.card G := by
  obtain ⟨c⟩ := S.exists_ctx
  have h27 := S.twentySeven_dvd_card
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁a, hr₂a, hr₁₂⟩ := c.exists_five_elements
  have hr₁K : (r₁ : G) ∈ c.Kg :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₁a)
  have hr₂K : (r₂ : G) ∈ c.Kg :=
    Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hr₂a)
  let r₁K : ↥c.Kg := ⟨(r₁ : G), hr₁K⟩
  let r₂K : ↥c.Kg := ⟨(r₂ : G), hr₂K⟩
  have ha3 : c.aK ^ 3 = 1 := Subtype.ext (by
    have := congrArg Subtype.val c.ha3
    simpa [Ctx.aK] using this)
  have ha1 : c.aK ≠ 1 := fun e => by
    have h1 : c.a = 1 := Subtype.ext (congrArg (fun y : ↥c.Kg => (y : G)) e)
    exact permA3_ne_one (by rw [← c.ha, h1, map_one])
  have haK : ∀ k : ↥c.Kg, k * c.aK = c.aK * k := fun k =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2)
  have hz2 : c.zK ^ 2 = 1 := by
    have := c.orderOf_zK
    rw [← this]; exact pow_orderOf_eq_one c.zK
  have hord : ∀ r : S.H, orderOf r = 5 → ∀ hr : (r : G) ∈ c.Kg,
      orderOf (⟨(r : G), hr⟩ : ↥c.Kg) = 5 := fun r h5 hr => by
    rw [← Subgroup.orderOf_coe (⟨(r : G), hr⟩ : ↥c.Kg)]
    show orderOf ((r : S.H) : G) = 5
    rw [Subgroup.orderOf_coe]; exact h5
  have hr₁₂K : (r₁K * r₂K) ^ 2 = c.zK := Subtype.ext (by
    have := congrArg Subtype.val hr₁₂
    simp only [pow_two, Subgroup.coe_mul] at this ⊢
    exact this)
  have key := three_pow_six_dvd_of_brauerSuzuki (K := ↥c.Kg) (a := c.aK) (z := c.zK)
    (r₁ := r₁K) (r₂ := r₂K) ha3 ha1 haK hz2 c.hBS_Kg c.card_centralizer_zK
    (fun W hW hn hodd => c.odd_normal_le_zpowers_aK hW hn hodd) (hord r₁ hr₁ hr₁K)
    (hord r₂ hr₂ hr₂K) hr₁₂K (c.twentySeven_dvd_card_centralizer_a h27)
  exact key.trans (Subgroup.card_subgroup_dvd_card c.Kg)

end Setup

end CFSG.Sporadic.Recognition.JankoWong
