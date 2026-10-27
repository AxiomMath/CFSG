module

public import CFSG.Quasithin.H13.A7SharedSeed

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Quasithin.BlueprintB2

variable {G : Type*} [Group G]

theorem isPLocal_two_centralizer_of_orderOf_eq_two {e : G} (he : orderOf e = 2) :
    CFSG.IsPLocal 2 (centralizer ({e} : Set G)) := by
  refine ⟨zpowers e, ?_, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one]), ?_⟩
  · intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at he
    exact absurd he (by norm_num)
  · ext g
    rw [mem_centralizer_singleton_iff, mem_normalizer_iff]
    have he2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← he, pow_orderOf_eq_one])
    have hmem : ∀ x : G, x ∈ zpowers e ↔ x = 1 ∨ x = e := by
      intro x
      constructor
      · intro hx
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hx
        rw [← zpow_mod_orderOf, he]
        rcases Int.emod_two_eq_zero_or_one j with h | h
        · left
          rw [show (j % ((2 : ℕ) : ℤ)) = 0 by exact_mod_cast h, zpow_zero]
        · right
          rw [show (j % ((2 : ℕ) : ℤ)) = 1 by exact_mod_cast h, zpow_one]
      · rintro (h | h) <;> rw [h]
        · exact one_mem _
        · exact mem_zpowers e
    constructor
    · intro hg y
      rw [hmem, hmem]
      constructor
      · rintro (h | h) <;> rw [h]
        · left
          group
        · right
          rw [hg, mul_inv_cancel_right]
      · rintro (h | h)
        · left
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        · right
          have h1 : g * e * g⁻¹ = e := by rw [hg, mul_inv_cancel_right]
          calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
            _ = g⁻¹ * e * g := by rw [h]
            _ = g⁻¹ * (g * e * g⁻¹) * g := by rw [h1]
            _ = e := by group
    · intro hg
      have h1 := (hg e).1 (mem_zpowers e)
      rw [hmem] at h1
      rcases h1 with h | h
      · exfalso
        have : e = 1 := by
          calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [this, orderOf_one] at he
        exact absurd he (by norm_num)
      · calc g * e = g * e * g⁻¹ * g := by group
          _ = e * g := by rw [h]

theorem A7_involution_local_central_seed_construction [Finite G]
    (hG : CFSG.IsEvenCharacteristic G) (T : Sylow 2 G) {e : G} (heT : e ∈ (T : Subgroup G))
    (heZ : ∀ t ∈ (T : Subgroup G), t * e = e * t) (he2 : orderOf e = 2) {Y : Subgroup G}
    (hTY : (T : Subgroup G) ≤ Y) (hYe : Y ≤ centralizer ({e} : Set G)) :
    let U := closure {x | ∃ y ∈ Y, ∃ z ∈ centerTorsion 2 (T : Subgroup G), x = y * z * y⁻¹}
    U ≠ ⊥ ∧ U ≤ Y ∧ Y ≤ normalizer (U : Set G) ∧ CFSG.Open.IsElemAbelian 2 U ∧
      U ≤ (T : Subgroup G) ∧
      ∀ D : Subgroup G, D ≤ Y → Y ≤ normalizer (D : Set G) → Y ⊓ centralizer (U : Set G) ≤ D →
        (∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizer (U : Set G)) →
        D = Y ⊓ centralizer (U : Set G) := by
  classical
  intro U
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({e} : Set G) with hCdef
  have hTC : (T : Subgroup G) ≤ C := hTY.trans hYe
  have hchar : CFSG.IsCharacteristicP 2 C :=
    hG C (isPLocal_two_centralizer_of_orderOf_eq_two he2) ⟨T, hTC⟩
  set P : Subgroup G := (CFSG.pCore 2 C).map C.subtype with hPdef
  have hP2 : IsPGroup 2 P := (CFSG.pCore_isPGroup (p := 2) (G := C)).map _
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hCN : C ≤ normalizer (P : Set G) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨⟨c, hc⟩ * x' * ⟨c, hc⟩⁻¹,
        (CFSG.pCore_normal (p := 2) (G := C)).conj_mem x' hx' ⟨c, hc⟩, rfl⟩
    · rintro ⟨x', hx', hx'e⟩
      have hx'e' : (x' : G) = c * x * c⁻¹ := hx'e
      refine ⟨⟨c, hc⟩⁻¹ * x' * ⟨c, hc⟩, ?_, ?_⟩
      · have := (CFSG.pCore_normal (p := 2) (G := C)).conj_mem x' hx' ⟨c, hc⟩⁻¹
        rwa [inv_inv] at this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hx'e']
        group
  have hPT : P ≤ (T : Subgroup G) := by
    have h1 : CFSG.pCore 2 C ≤ (T.subtype hTC : Subgroup C) :=
      (CFSG.pCore_isPGroup (p := 2) (G := C)).le_sylow_of_normal (T.subtype hTC)
    rintro _ ⟨x, hx, rfl⟩
    have := h1 hx
    rwa [Sylow.coe_subtype, mem_subgroupOf] at this
  have hPY : P ≤ Y := hPT.trans hTY
  have hYN : Y ≤ normalizer (P : Set G) := hYe.trans hCN
  have hCP : ∀ y ∈ C, y ∈ centralizer (P : Set G) → y ∈ P := by
    intro y hy hyP
    have h1 : (⟨y, hy⟩ : C) ∈ centralizer (CFSG.pCore 2 C : Set C) := by
      rw [mem_centralizer_iff]
      intro h hh
      exact Subtype.ext (mem_centralizer_iff.1 hyP h ⟨h, hh, rfl⟩)
    exact ⟨_, hchar h1, rfl⟩
  set T' : Sylow 2 Y := T.subtype hTY with hT'def
  set P' : Subgroup Y := P.subgroupOf Y with hP'def
  have hP'n : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).2 hYN
  have hP'2 : IsPGroup 2 P' := IsPGroup.of_equiv hP2 (Subgroup.subgroupOfEquivOfLe hPY).symm
  have hCP' : centralizer (P' : Set Y) ≤ P' := by
    intro y hy
    rw [mem_subgroupOf]
    refine hCP y (hYe y.2) (mem_centralizer_iff.2 fun p hp => ?_)
    exact congrArg Subtype.val (mem_centralizer_iff.1 hy ⟨p, hPY hp⟩ (by
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact hp))
  set Z' : Subgroup Y := (centerTorsion 2 (T : Subgroup G)).subgroupOf Y with hZ'def
  have hZ' : Z' ≤ centerTorsion 2 (T' : Subgroup Y) := by
    intro z hz
    rw [mem_subgroupOf] at hz
    obtain ⟨hzT, hzc, hzp⟩ := mem_centerTorsion_iff.1 hz
    refine mem_centerTorsion_iff.2 ⟨?_, fun k hk => ?_, ?_⟩
    · rw [hT'def, Sylow.coe_subtype, mem_subgroupOf]
      exact hzT
    · rw [hT'def, Sylow.coe_subtype, mem_subgroupOf] at hk
      exact Subtype.ext (hzc _ hk)
    · exact Subtype.ext (by simpa using hzp)
  obtain ⟨hUn, hUel, hUΩ, hUD⟩ := A7_central_Sylow_seed_reduced_module T' hP'2 hCP' hZ'
  have hset : {x | ∃ y ∈ Y, ∃ z ∈ centerTorsion 2 (T : Subgroup G), x = y * z * y⁻¹} =
      Y.subtype '' Group.conjugatesOfSet (Z' : Set Y) := by
    ext x
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      refine ⟨⟨y, hy⟩ * ⟨z, hTY (mem_centerTorsion_iff.1 hz).1⟩ * ⟨y, hy⟩⁻¹, ?_, rfl⟩
      exact Group.mem_conjugatesOfSet_iff.2 ⟨⟨z, hTY (mem_centerTorsion_iff.1 hz).1⟩,
        (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hz), isConj_iff.2 ⟨⟨y, hy⟩, rfl⟩⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, hzw⟩ := Group.mem_conjugatesOfSet_iff.1 hw
      obtain ⟨y, rfl⟩ := isConj_iff.1 hzw
      rw [SetLike.mem_coe, mem_subgroupOf] at hz
      exact ⟨y, y.2, z, hz, rfl⟩
  have hUeq : U = (normalClosure (Z' : Set Y)).map Y.subtype := by
    show Subgroup.closure _ = _
    rw [normalClosure, MonoidHom.map_closure, hset]
  have hmemU : ∀ y : Y, (y : G) ∈ U ↔ y ∈ normalClosure (Z' : Set Y) := by
    intro y
    rw [hUeq]
    constructor
    · rintro ⟨w, hw, hwy⟩
      rwa [show w = y from Subtype.ext hwy] at hw
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hUY : U ≤ Y := hUeq ▸ Subgroup.map_subtype_le _
  have hU' : ∀ u ∈ U, ∃ hu : u ∈ Y, (⟨u, hu⟩ : Y) ∈ normalClosure (Z' : Set Y) := fun u hu =>
    ⟨hUY hu, (hmemU ⟨u, hUY hu⟩).1 hu⟩
  have hUP : ∀ u ∈ U, u ∈ P ∧ (∀ p ∈ P, p * u = u * p) ∧ u ^ 2 = 1 := by
    intro u hu
    obtain ⟨huY, hu'⟩ := hU' u hu
    obtain ⟨h1, h2, h3⟩ := mem_centerTorsion_iff.1 (hUΩ hu')
    refine ⟨by rwa [hP'def, mem_subgroupOf] at h1, fun p hp => ?_,
      by simpa using congrArg Subtype.val h3⟩
    exact congrArg Subtype.val (h2 ⟨p, hPY hp⟩ (by rw [hP'def, mem_subgroupOf]; exact hp))
  refine ⟨?_, hUY, ?_, ?_, fun u hu => hPT (hUP u hu).1, ?_⟩
  ·
    intro hbot
    have he : e ∈ U := subset_closure ⟨1, one_mem _, e,
      mem_centerTorsion_iff.2 ⟨heT, heZ, by rw [← he2, pow_orderOf_eq_one]⟩, by group⟩
    rw [hbot, mem_bot] at he
    rw [he, orderOf_one] at he2
    exact absurd he2 (by norm_num)
  ·
    intro y hy
    rw [mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      obtain ⟨huY, hu'⟩ := hU' u hu
      have := hUn.conj_mem _ hu' ⟨y, hy⟩
      have h2 := (hmemU _).2 this
      simpa using h2
    · intro hu
      obtain ⟨huY, hu'⟩ := hU' _ hu
      have := hUn.conj_mem _ hu' ⟨y, hy⟩⁻¹
      have h2 := (hmemU _).2 this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h2
      convert h2 using 1
      group
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => (hUP x hx).2.2⟩
    exact (hUP y y.2).2.1 x (hUP x x.2).1
  ·
    intro D hDY hYD hCD hDp
    have hcent : ∀ y : Y, y ∈ centralizer (normalClosure (Z' : Set Y) : Set Y) ↔
        (y : G) ∈ centralizer (U : Set G) := by
      intro y
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro h u hu
        obtain ⟨huY, hu'⟩ := hU' u hu
        exact congrArg Subtype.val (h _ hu')
      · intro h w hw
        exact Subtype.ext (h w ((hmemU w).2 hw))
    have hD'n : (D.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).2 hYD
    have h1 := hUD (D.subgroupOf Y) hD'n
      (fun y hy => by
        rw [mem_subgroupOf]
        exact hCD ⟨y.2, (hcent y).1 hy⟩)
      (fun d hd => by
        rw [mem_subgroupOf] at hd
        obtain ⟨k, hk⟩ := hDp d hd
        exact ⟨k, (hcent _).2 (by simpa using hk)⟩)
    apply le_antisymm
    · intro d hd
      have : (⟨d, hDY hd⟩ : Y) ∈ D.subgroupOf Y := by rw [mem_subgroupOf]; exact hd
      rw [h1] at this
      exact ⟨hDY hd, (hcent _).1 this⟩
    · exact hCD

end CFSG.Quasithin.H13.A7
