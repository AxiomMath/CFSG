module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocNF
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocFusion
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4NFGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtraspecialAb
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442XMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocQComm

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.D4Hex
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Transport

variable {M : Type} [Group M]

@[expose] def imgH (b1 : ↥d4H →* M) (S : Subgroup D) : Subgroup M := (S.subgroupOf d4H).map b1

theorem mem_imgH {b1 : ↥d4H →* M} {S : Subgroup D} {m : M} :
    m ∈ imgH b1 S ↔ ∃ x : ↥d4H, (x : D) ∈ S ∧ b1 x = m := by
  simp only [imgH, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_imgH {b1 : ↥d4H →* M} (hinj : Function.Injective b1) {S : Subgroup D}
    (hS : S ≤ d4H) : Nat.card (imgH b1 S) = Nat.card S := by
  rw [imgH, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

theorem isSylowTwoOf_imgH {b1 : ↥d4H →* M} (hinj : Function.Injective b1) {T : Subgroup D}
    (hT : IsSylowTwoOf T ⊤) (hT1 : T ≤ d4H) : IsSylowTwoOf (imgH b1 T) b1.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf d4H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT1).symm
  have hPp : IsPGroup 2 (imgH b1 T) :=
    hTp.of_equiv (Subgroup.equivMapOfInjective _ b1 hinj)
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range b1 _) hPp ?_
  have h1 : (imgH b1 T).relIndex b1.range = (T.subgroupOf d4H).relIndex ⊤ := by
    rw [imgH, MonoidHom.range_eq_map]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  rw [h1, Subgroup.relIndex_top_right]
  exact (F7.isSylowTwoOf_mono_right hT hT1 le_top).2.2

end Transport

theorem d4z_mem_d4H : d4z ∈ d4H := Subgroup.mem_centralizer_singleton_iff.2 rfl

section Apply


theorem d4_nf_apply {M : Type} [Group M] [Finite M] {b1 : ↥d4H →* M}
    (hinj : Function.Injective b1)
    (hb : Subgroup.centralizer ({b1 ⟨d4z, d4z_mem_d4H⟩} : Set M) ≤ b1.range)
    {v : D} (hv : D4O v) (hvH : v ∈ d4H)
    (hpair : ∃ a ∈ d4Q, ∃ b ∈ d4Q, a * v = v * a ∧ b * v = v * b ∧
      a * b * a⁻¹ * b⁻¹ = d4z) :
    ¬ IsConj (b1 ⟨d4z, d4z_mem_d4H⟩) (b1 ⟨v, hvH⟩) := by
  set zH : ↥d4H := ⟨d4z, d4z_mem_d4H⟩ with hzH
  have hQH : d4Q ≤ d4H := d4Q_le_d4U.trans d4U_le_d4H
  have hz2 : b1 zH * b1 zH = 1 := by
    rw [← map_mul, ← map_one b1]
    exact congrArg b1 (Subtype.ext d4z_sq.1)
  have hz1 : b1 zH ≠ 1 := fun h =>
    d4z_sq.2 (congrArg Subtype.val (hinj (h.trans (map_one b1).symm)))
  have hcent : Subgroup.centralizer ({b1 zH} : Set M) = b1.range := by
    refine le_antisymm hb ?_
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg b1 (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2))
  have hQcard : Nat.card (imgH b1 d4Q) = 512 := by rw [card_imgH hinj hQH, card_d4Q]
  have hQcomm : ∀ x ∈ imgH b1 d4Q, ∀ y ∈ imgH b1 d4Q,
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = b1 zH := by
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_imgH.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_imgH.1 hy
    have e : b1 x0 * b1 y0 * (b1 x0)⁻¹ * (b1 y0)⁻¹ = b1 (x0 * y0 * x0⁻¹ * y0⁻¹) := by simp
    rw [e]
    rcases d4_hQcomm _ hx0 _ hy0 with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  have hQZ : ∀ w ∈ imgH b1 d4Q, (∀ q ∈ imgH b1 d4Q, q * w = w * q) → w = 1 ∨ w = b1 zH := by
    intro w hw hc
    obtain ⟨w0, hw0, rfl⟩ := mem_imgH.1 hw
    have hc' : ∀ q ∈ d4Q, q * (w0 : D) = (w0 : D) * q := by
      intro q hq
      have hqH := hQH hq
      have := hc (b1 ⟨q, hqH⟩) (mem_imgH.2 ⟨⟨q, hqH⟩, hq, rfl⟩)
      rw [← map_mul, ← map_mul] at this
      exact congrArg Subtype.val (hinj this)
    rcases d4_hQZ _ hw0 hc' with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  refine not_isConj_of_nfGen (G := M) (z := b1 zH) hz2 hz1 (T := imgH b1 d4U) (Q := imgH b1 d4Q)
    (c := 32) (by rw [hcent]; exact isSylowTwoOf_imgH hinj d4_sylow d4U_le_d4H) ?_ ?_ ?_ ?_
    hQcomm ?_ ?_ (fun m => ∃ w : ↥d4H, D4O (w : D) ∧ b1 w = m) ?_ ?_ ⟨⟨v, hvH⟩, hv, rfl⟩ ?_ ?_ ?_
  · intro m hm
    obtain ⟨x, hx, rfl⟩ := mem_imgH.1 hm
    exact mem_imgH.2 ⟨x, d4Q_le_d4U hx, rfl⟩
  · intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_imgH.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_imgH.1 hy
    exact mem_imgH.2 ⟨x0 * y0 * x0⁻¹ * y0⁻¹, d4_hTQ _ hx0 _ hy0, by simp⟩
  · rw [card_imgH hinj d4U_le_d4H, card_imgH hinj hQH, card_d4U', card_d4Q]
  · intro h hh q hq
    rw [hcent] at hh
    obtain ⟨h0, rfl⟩ := hh
    obtain ⟨q0, hq0, rfl⟩ := mem_imgH.1 hq
    exact mem_imgH.2 ⟨h0 * q0 * h0⁻¹, d4H_norm_Q _ h0.2 _ hq0, by simp⟩
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := mem_imgH.1 hx
    have e : b1 x0 * b1 x0 = b1 (x0 * x0) := by simp
    rw [e]
    rcases d4_hQsq _ hx0 with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  · intro A hA hAab _
    exact card_abelian_le_32 hQcard hQcomm hQZ hA hAab
  · intro h hh m hm
    rw [hcent] at hh
    obtain ⟨h0, rfl⟩ := hh
    obtain ⟨w, hw, rfl⟩ := hm
    exact ⟨h0 * w * h0⁻¹, D4O.conj h0.2 hw, by simp⟩
  · rintro m ⟨w, hw, rfl⟩
    obtain ⟨t0, ht0, h1, h2⟩ := D4O.exists_comm hw
    have ht0H : t0 ∈ d4H := d4U_le_d4H ht0
    refine ⟨b1 ⟨t0, ht0H⟩, mem_imgH.2 ⟨⟨t0, ht0H⟩, ht0, rfl⟩, ?_, ?_⟩
    · intro h
      apply h1
      have : b1 (⟨t0, ht0H⟩ * w * ⟨t0, ht0H⟩⁻¹ * w⁻¹) = b1 1 := by simpa using h
      exact congrArg Subtype.val (hinj this)
    · intro h
      apply h2
      have : b1 (⟨t0, ht0H⟩ * w * ⟨t0, ht0H⟩⁻¹ * w⁻¹) = b1 zH := by simpa using h
      exact congrArg Subtype.val (hinj this)
  · exact mem_imgH.2 ⟨⟨v, hvH⟩, hv.1, rfl⟩
  · intro h
    exact hv.2.2.2 (by rw [show v = d4z from congrArg Subtype.val (hinj h)])
  · obtain ⟨a, haQ, b, hbQ, hav, hbv, hab⟩ := hpair
    have haH := hQH haQ
    have hbH := hQH hbQ
    refine ⟨b1 ⟨a, haH⟩, mem_imgH.2 ⟨⟨a, haH⟩, haQ, rfl⟩, b1 ⟨b, hbH⟩,
      mem_imgH.2 ⟨⟨b, hbH⟩, hbQ, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hav)
    · rw [← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hbv)
    · have : b1 (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹) = b1 zH :=
        congrArg b1 (Subtype.ext hab)
      simpa only [map_mul, map_inv] using this

theorem d4t_mem_d4H : d4t ∈ d4H := d4U_le_d4H d4t_mem_d4U

theorem d4_not_conj {M : Type} [Group M] [Finite M] {b1 : ↥d4H →* M} {b2 : ↥d4N →* M}
    (C : F431Comp d4H d4N b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 d4z} : Set M) ≤ b1.range) :
    ¬ IsConj (amalgamMap b1 b2 d4z) (amalgamMap b1 b2 d4t) := by
  intro hzt
  have hzH := d4z_mem_d4H
  rw [amalgamMap_of_mem₁ b1 b2 hzH] at hb hzt
  obtain ⟨v0, hO, hpair⟩ := d4_hpair
  have hQH : d4Q ≤ d4H := d4Q_le_d4U.trans d4U_le_d4H
  have hv0H : v0 ∈ d4H := hQH hO.1
  have hv0o : orderOf v0 = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hO.2.1) hO.2.2.1
  have hconj : IsConj d4t v0 := (d4_F431LieI.classes v0 hv0o).resolve_left hO.2.2.2
  have hfus := d4_F431LieI.fusion_forward C d4t_mem_d4U (d4Q_le_d4U hO.1) orderOf_d4t hv0o hconj
  rw [amalgamMap_of_mem₁ b1 b2 hv0H, amalgamMap_of_mem₁ b1 b2 d4t_mem_d4H] at hfus
  rw [amalgamMap_of_mem₁ b1 b2 d4t_mem_d4H] at hzt
  exact d4_nf_apply C.inj₁ hb hO hv0H hpair (hzt.trans hfus)

end Apply

section LocalCent


theorem d4_localCent_comp {M : Type} [Group M] [Finite M] {b1 : ↥d4H →* M} {b2 : ↥d4N →* M}
    (C : F431Comp d4H d4N b1 b2)
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 d4z} : Set M) ≤ b1.range) :
    Subgroup.centralizer ({amalgamMap b1 b2 d4t} : Set M) ≤ b2.range := by
  have : Finite D := finite_D
  obtain ⟨q, hD⟩ := d4_Loc442DatumX
  exact loc442X hD C hb (d4_not_conj C hb)

end LocalCent

end CFSG.Quasithin.D4Hex
