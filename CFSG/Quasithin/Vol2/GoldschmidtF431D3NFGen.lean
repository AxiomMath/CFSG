module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4NFGen
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtraspecialAb

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Transport

variable {A : Type} [Group A] {M : Type} [Group M] {M1 : Subgroup A}

@[expose] def imgSub (b1 : ↥M1 →* M) (S : Subgroup A) : Subgroup M := (S.subgroupOf M1).map b1

theorem mem_imgSub {b1 : ↥M1 →* M} {S : Subgroup A} {m : M} :
    m ∈ imgSub b1 S ↔ ∃ x : ↥M1, (x : A) ∈ S ∧ b1 x = m := by
  simp only [imgSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem card_imgSub {b1 : ↥M1 →* M} (hinj : Function.Injective b1) {S : Subgroup A}
    (hS : S ≤ M1) : Nat.card (imgSub b1 S) = Nat.card S := by
  rw [imgSub, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv

theorem isSylowTwoOf_imgSub {b1 : ↥M1 →* M} (hinj : Function.Injective b1) {T : Subgroup A}
    (hT : IsSylowTwoOf T (⊤ : Subgroup A)) (hT1 : T ≤ M1) :
    IsSylowTwoOf (imgSub b1 T) b1.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf M1) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT1).symm
  have hPp : IsPGroup 2 (imgSub b1 T) :=
    hTp.of_equiv (Subgroup.equivMapOfInjective _ b1 hinj)
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range b1 _) hPp ?_
  have h1 : (imgSub b1 T).relIndex b1.range = (T.subgroupOf M1).relIndex ⊤ := by
    rw [imgSub, MonoidHom.range_eq_map]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  rw [h1, Subgroup.relIndex_top_right]
  exact (F7.isSylowTwoOf_mono_right hT hT1 le_top).2.2

end Transport

section Apply

variable {A : Type} [Group A] {M : Type} [Group M] [Finite M] {M1 T Q : Subgroup A} {z : A}

theorem nf_apply_gen {b1 : ↥M1 →* M} (hinj : Function.Injective b1) (hz1 : z ∈ M1)
    (hzsq : z * z = 1) (hzne : z ≠ 1) (hMz : ∀ x ∈ M1, x * z = z * x)
    (hb : Subgroup.centralizer ({b1 ⟨z, hz1⟩} : Set M) ≤ b1.range)
    (hSyl : IsSylowTwoOf T (⊤ : Subgroup A)) (hTM : T ≤ M1) (hQT : Q ≤ T)
    (hTQ : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hQn : ∀ h ∈ M1, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQsq : ∀ x ∈ Q, x * x = 1 ∨ x * x = z)
    (hQZ : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z)
    (hQcard : Nat.card Q = 512) (hTcard : Nat.card T = 4096)
    (O : A → Prop) (hOinv : ∀ h ∈ M1, ∀ v, O v → O (h * v * h⁻¹))
    (hOt : ∀ v, O v → ∃ t ∈ T, t * v * t⁻¹ * v⁻¹ ≠ 1 ∧ t * v * t⁻¹ * v⁻¹ ≠ z)
    {v : A} (hv : O v) (hvQ : v ∈ Q) (hvz : v ≠ z)
    (hpair : ∃ a ∈ Q, ∃ b ∈ Q, a * v = v * a ∧ b * v = v * b ∧ a * b * a⁻¹ * b⁻¹ = z) :
    ¬ IsConj (b1 ⟨z, hz1⟩) (b1 ⟨v, hTM (hQT hvQ)⟩) := by
  set zH : ↥M1 := ⟨z, hz1⟩ with hzH
  have hQH : Q ≤ M1 := hQT.trans hTM
  have hz2 : b1 zH * b1 zH = 1 := by
    rw [← map_mul, ← map_one b1]
    exact congrArg b1 (Subtype.ext hzsq)
  have hz1' : b1 zH ≠ 1 := fun h =>
    hzne (congrArg Subtype.val (hinj (h.trans (map_one b1).symm)))
  have hcent : Subgroup.centralizer ({b1 zH} : Set M) = b1.range := by
    refine le_antisymm hb ?_
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg b1 (Subtype.ext (hMz x x.2))
  have hQcard' : Nat.card (imgSub b1 Q) = 512 := by rw [card_imgSub hinj hQH, hQcard]
  have hQcomm' : ∀ x ∈ imgSub b1 Q, ∀ y ∈ imgSub b1 Q,
      x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = b1 zH := by
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_imgSub.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_imgSub.1 hy
    have e : b1 x0 * b1 y0 * (b1 x0)⁻¹ * (b1 y0)⁻¹ = b1 (x0 * y0 * x0⁻¹ * y0⁻¹) := by simp
    rw [e]
    rcases hQcomm _ hx0 _ hy0 with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  have hQZ' : ∀ w ∈ imgSub b1 Q, (∀ q ∈ imgSub b1 Q, q * w = w * q) → w = 1 ∨ w = b1 zH := by
    intro w hw hc
    obtain ⟨w0, hw0, rfl⟩ := mem_imgSub.1 hw
    have hc' : ∀ q ∈ Q, q * (w0 : A) = (w0 : A) * q := by
      intro q hq
      have hqH := hQH hq
      have h1 := hc (b1 ⟨q, hqH⟩) (mem_imgSub.2 ⟨⟨q, hqH⟩, hq, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hinj h1)
    rcases hQZ _ hw0 hc' with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  refine not_isConj_of_nfGen (G := M) (z := b1 zH) hz2 hz1' (T := imgSub b1 T)
    (Q := imgSub b1 Q) (c := 32) (by rw [hcent]; exact isSylowTwoOf_imgSub hinj hSyl hTM) ?_ ?_
    ?_ ?_ hQcomm' ?_ ?_ (fun m => ∃ w : ↥M1, O (w : A) ∧ b1 w = m) ?_ ?_
    ⟨⟨v, hTM (hQT hvQ)⟩, hv, rfl⟩ ?_ ?_ ?_
  · intro m hm
    obtain ⟨x, hx, rfl⟩ := mem_imgSub.1 hm
    exact mem_imgSub.2 ⟨x, hQT hx, rfl⟩
  · intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := mem_imgSub.1 hx
    obtain ⟨y0, hy0, rfl⟩ := mem_imgSub.1 hy
    exact mem_imgSub.2 ⟨x0 * y0 * x0⁻¹ * y0⁻¹, hTQ _ hx0 _ hy0, by simp⟩
  · rw [card_imgSub hinj hTM, card_imgSub hinj hQH, hTcard, hQcard]
  · intro h hh q hq
    rw [hcent] at hh
    obtain ⟨h0, rfl⟩ := hh
    obtain ⟨q0, hq0, rfl⟩ := mem_imgSub.1 hq
    exact mem_imgSub.2 ⟨h0 * q0 * h0⁻¹, hQn _ h0.2 _ hq0, by simp⟩
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := mem_imgSub.1 hx
    have e : b1 x0 * b1 x0 = b1 (x0 * x0) := by simp
    rw [e]
    rcases hQsq _ hx0 with h | h
    · left
      rw [← map_one b1]
      exact congrArg b1 (Subtype.ext h)
    · right
      exact congrArg b1 (Subtype.ext h)
  · intro B hB hBab _
    exact card_abelian_le_32 hQcard' hQcomm' hQZ' hB hBab
  · intro h hh m hm
    rw [hcent] at hh
    obtain ⟨h0, rfl⟩ := hh
    obtain ⟨w, hw, rfl⟩ := hm
    exact ⟨h0 * w * h0⁻¹, hOinv _ h0.2 _ hw, by simp⟩
  · rintro m ⟨w, hw, rfl⟩
    obtain ⟨t0, ht0, h1, h2⟩ := hOt _ hw
    have ht0H : t0 ∈ M1 := hTM ht0
    refine ⟨b1 ⟨t0, ht0H⟩, mem_imgSub.2 ⟨⟨t0, ht0H⟩, ht0, rfl⟩, ?_, ?_⟩
    · intro h
      apply h1
      have h3 : b1 (⟨t0, ht0H⟩ * w * ⟨t0, ht0H⟩⁻¹ * w⁻¹) = b1 1 := by simpa using h
      exact congrArg Subtype.val (hinj h3)
    · intro h
      apply h2
      have h3 : b1 (⟨t0, ht0H⟩ * w * ⟨t0, ht0H⟩⁻¹ * w⁻¹) = b1 zH := by simpa using h
      exact congrArg Subtype.val (hinj h3)
  · exact mem_imgSub.2 ⟨⟨v, hTM (hQT hvQ)⟩, hvQ, rfl⟩
  · intro h
    exact hvz (congrArg Subtype.val (hinj h))
  · obtain ⟨a, haQ, b, hbQ, hav, hbv, hab⟩ := hpair
    have haH := hQH haQ
    have hbH := hQH hbQ
    refine ⟨b1 ⟨a, haH⟩, mem_imgSub.2 ⟨⟨a, haH⟩, haQ, rfl⟩, b1 ⟨b, hbH⟩,
      mem_imgSub.2 ⟨⟨b, hbH⟩, hbQ, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hav)
    · rw [← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hbv)
    · have h3 : b1 (⟨a, haH⟩ * ⟨b, hbH⟩ * ⟨a, haH⟩⁻¹ * ⟨b, hbH⟩⁻¹) = b1 zH :=
        congrArg b1 (Subtype.ext hab)
      simpa only [map_mul, map_inv] using h3

end Apply

end CFSG.Quasithin.D4Hex
