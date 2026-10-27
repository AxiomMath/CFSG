module

public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem image_pCoreOf_le_bot {H L : Subgroup G} (hLH : L ≤ H)
    (hs : IsSimpleGroup ↥(modO2Image H L)) (hn : ¬ IsPGroup 2 ↥(modO2Image H L)) :
    ∀ m ∈ pCoreOf 2 L, ∀ hm : m ∈ H,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨m, hm⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  let M : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((pCoreOf 2 L).subgroupOf H).map mk
  have hML : M ≤ modO2Image H L := by
    refine Subgroup.map_mono fun x hx => ?_
    exact (pCoreOf_le 2 L) hx
  have hM2 : IsPGroup 2 ↥M := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨n, hn'⟩ := (pCoreOf_isPGroup 2 L) ⟨(x : G), hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (x : G) ^ (2 ^ n) = 1 := congrArg Subtype.val hn'
    have h2 : x ^ (2 ^ n) = 1 := Subtype.ext h1
    show ((y ^ 2 ^ n : ↥M) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1
    rw [Subgroup.coe_pow, ← hxy, ← map_pow, h2, map_one]
  have hnormal : (M.subgroupOf (modO2Image H L)).Normal := by
    refine ⟨fun y hy z => ?_⟩
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨⟨l, hlH⟩, hl, hlz⟩ := z.2
    refine ⟨(⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹ : ↥H), ?_, ?_⟩
    · show ((l * (x : G) * l⁻¹ : G)) ∈ pCoreOf 2 L
      have hlN := le_normalizer_pCoreOf 2 L hl
      exact (Subgroup.mem_normalizer_iff.mp hlN (x : G)).mp hx
    · have hz : (z : ↥H ⧸ CFSG.pCore 2 ↥H) = mk ⟨l, hlH⟩ := hlz.symm
      show mk (⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹) = (z : ↥H ⧸ CFSG.pCore 2 ↥H) * (y : ↥H ⧸ CFSG.pCore 2 ↥H) *
        (z : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹
      rw [hz, map_mul, map_mul, map_inv, hxy]
      rfl
  haveI := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (modO2Image H L)) with hbot | htop
  · intro m hm hmH
    have hmem : mk ⟨m, hmH⟩ ∈ M := ⟨⟨m, hmH⟩, hm, rfl⟩
    have hmL : mk ⟨m, hmH⟩ ∈ modO2Image H L := hML hmem
    have h1 : (⟨mk ⟨m, hmH⟩, hmL⟩ : ↥(modO2Image H L)) ∈ M.subgroupOf (modO2Image H L) := hmem
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    refine hn (hM2.to_le fun w hw => ?_)
    have : (⟨w, hw⟩ : ↥(modO2Image H L)) ∈ M.subgroupOf (modO2Image H L) := by
      rw [htop]; exact Subgroup.mem_top _
    exact this

theorem split_bar {H S L : Subgroup G} (hSH : S ≤ H) (hLH : L ≤ H)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧ s = p * c)
    (hs : IsSimpleGroup ↥(modO2Image H L)) (hn : ¬ IsPGroup 2 ↥(modO2Image H L)) :
    ∀ s ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      ∃ p ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⊓ modO2Image H L,
        ∃ c ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
          (∀ x ∈ modO2Image H L, c * x * c⁻¹ = x) ∧ s = p * c := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  rintro _ ⟨s', hs', rfl⟩
  obtain ⟨p, hp, c, hc, hcent, hsp⟩ := hsplit (s' : G) hs'
  have hpH : p ∈ H := hSH hp.1
  have hcH : c ∈ H := hSH hc
  refine ⟨mk ⟨p, hpH⟩, ⟨⟨⟨p, hpH⟩, hp.1, rfl⟩, ⟨⟨p, hpH⟩, hp.2, rfl⟩⟩, mk ⟨c, hcH⟩,
    ⟨⟨c, hcH⟩, hc, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x', hx', rfl⟩
    obtain ⟨m, hm, hxm⟩ := hcent (x' : G) hx'
    have hmH : m ∈ H := hLH ((pCoreOf_le 2 L) hm)
    have h1 := image_pCoreOf_le_bot hLH hs hn m hm hmH
    have h2 : (⟨c, hcH⟩ : ↥H) * x' * (⟨c, hcH⟩ : ↥H)⁻¹ = x' * ⟨m, hmH⟩ := Subtype.ext hxm
    rw [← map_mul, ← map_inv, ← map_mul, h2, map_mul, h1, mul_one]
  · have : s' = ⟨p, hpH⟩ * ⟨c, hcH⟩ := Subtype.ext hsp
    rw [this, map_mul]

end Stellmacher.CD.L3YC

end CFSG.Quasithin
