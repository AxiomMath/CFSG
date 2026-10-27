module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bA
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G} {z : G}

theorem AutIso.exists_pre (iso : AutIso M₁ M₂) {X : Subgroup G}
    (hX : X ≤ iso.imgG That) : ∃ K : Subgroup Ah, K ≤ That ∧ iso.imgG K = X := by
  set K : Subgroup Ah := (X.comap iso.toGHom).map Bh.subtype with hK
  have hmem : ∀ k : Ah, k ∈ K ↔ ∃ b : Bh, (b : Ah) = k ∧ iso.toG b ∈ X := by
    intro k
    rw [hK, Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, rfl, hb⟩
    · rintro ⟨b, rfl, hb⟩
      exact ⟨b, hb, rfl⟩
  refine ⟨K, ?_, ?_⟩
  · intro k hk
    obtain ⟨b, rfl, hb⟩ := (hmem k).1 hk
    obtain ⟨b', hb', hbb⟩ := iso.mem_imgG.1 (hX hb)
    have : b' = b := iso.toG_injective hbb
    rwa [this] at hb'
  · ext g
    constructor
    · intro hg
      obtain ⟨b, hb, rfl⟩ := iso.mem_imgG.1 hg
      obtain ⟨b', hb', hbb⟩ := (hmem _).1 hb
      have : b' = b := Subtype.ext hb'
      rw [this] at hbb
      exact hbb
    · intro hg
      obtain ⟨b, -, rfl⟩ := iso.mem_imgG.1 (hX hg)
      exact iso.mem_imgG.2 ⟨b, (hmem _).2 ⟨b, rfl, hg⟩, rfl⟩

theorem AutIso.imgG_conjSub (iso : AutIso M₁ M₂) (yb : Bh) (K : Subgroup Ah) :
    iso.imgG (B6.conjSub (yb : Ah) K) = B6.conjSub (iso.toG yb) (iso.imgG K) := by
  ext g
  rw [B6.mem_conjSub, iso.mem_imgG, iso.mem_imgG]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [B6.mem_conjSub] at hb
    refine ⟨yb⁻¹ * b * yb, ?_, ?_⟩
    · simpa using hb
    · rw [AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv]
  · rintro ⟨b, hb, hbg⟩
    refine ⟨yb * b * yb⁻¹, ?_, ?_⟩
    · rw [B6.mem_conjSub]
      simpa [mul_assoc] using hb
    · rw [AutIso.toG_mul, AutIso.toG_mul, AutIso.toG_inv, hbg]
      group

theorem AutIso.map_toG1_normalizer [Finite G]
    (iso : AutIso M₁ M₂) {K : Subgroup Ah} (hK : K ≤ Bh) :
    ((Subgroup.normalizer (K : Set Ah)).subgroupOf P1h).map iso.toG1 =
      Subgroup.normalizer (iso.imgG K : Set G) ⊓ M₁ := by
  set S : Subgroup ↥P1h := (Subgroup.normalizer (K : Set Ah)).subgroupOf P1h with hS
  have hmem : ∀ p : ↥P1h, p ∈ S ↔ (p : Ah) ∈ Subgroup.normalizer (K : Set Ah) := fun p => Iff.rfl
  ext n
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨?_, (iso.phi1 p).2⟩
    refine normalizer_of_conj_le fun g hg => ?_
    obtain ⟨b, hbK, rfl⟩ := iso.mem_imgG.1 hg
    have hb' : (p : Ah) * (b : Ah) * (p : Ah)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1
      ((hmem p).1 hp) (b : Ah)).1 hbK
    refine iso.mem_imgG.2 ⟨⟨(p : Ah) * (b : Ah) * (p : Ah)⁻¹, hK hb'⟩, hb', ?_⟩
    have e : p * Subgroup.inclusion Bh_le_P1h b * p⁻¹ =
        Subgroup.inclusion Bh_le_P1h ⟨(p : Ah) * (b : Ah) * (p : Ah)⁻¹, hK hb'⟩ := Subtype.ext rfl
    have := congrArg iso.toG1 e
    rw [map_mul, map_mul, map_inv, AutIso.toG1_inclusion, AutIso.toG1_inclusion] at this
    exact this.symm
  · rintro ⟨hn, hM⟩
    set p : ↥P1h := iso.phi1.symm ⟨n, hM⟩ with hp
    have hpn : iso.toG1 p = n := by
      show ((iso.phi1 (iso.phi1.symm ⟨n, hM⟩) : ↥M₁) : G) = n
      rw [MulEquiv.apply_symm_apply]
    refine ⟨p, show p ∈ S from (hmem p).2 ?_, hpn⟩
    refine normalizer_of_conj_le fun x hx => ?_
    obtain ⟨b', hb', hbb⟩ := iso.mem_imgG.1 ((Subgroup.mem_normalizer_iff.1 hn
      (iso.toG ⟨x, hK hx⟩)).1 (iso.mem_imgG.2 ⟨⟨x, hK hx⟩, hx, rfl⟩))
    have e : iso.toG1 (p * Subgroup.inclusion Bh_le_P1h ⟨x, hK hx⟩ * p⁻¹) =
        iso.toG1 (Subgroup.inclusion Bh_le_P1h b') := by
      rw [map_mul, map_mul, map_inv, AutIso.toG1_inclusion, AutIso.toG1_inclusion, hpn, hbb]
    have := iso.toG1_injective e
    have h2 := congrArg (fun q : ↥P1h => (q : Ah)) this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 : (p : Ah) * x * (p : Ah)⁻¹ = (b' : Ah) := h2
    rw [h3]
    exact hb'

theorem AutIso.card_normalizer_M1 [Finite G]
    (iso : AutIso M₁ M₂) {K : Subgroup Ah} (hK : K ≤ Bh) :
    Nat.card ↥(Subgroup.normalizer (iso.imgG K : Set G) ⊓ M₁) =
      Nat.card ↥(P1h ⊓ Subgroup.normalizer (K : Set Ah)) := by
  set S : Subgroup ↥P1h := (Subgroup.normalizer (K : Set Ah)).subgroupOf P1h with hS
  have e : (P1h ⊓ Subgroup.normalizer (K : Set Ah)).subgroupOf P1h = S := by
    ext p
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨p.2, h⟩⟩
  have hcardS : Nat.card ↥S = Nat.card ↥(P1h ⊓ Subgroup.normalizer (K : Set Ah)) := by
    rw [← e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← iso.map_toG1_normalizer hK, Subgroup.card_map_of_injective iso.toG1_injective]
  exact hcardS

theorem AutCtx.cenOf_z [Finite G]
    (c : AutCtx G M₁ M₂ z) : cenOf z = M₁ := by
  apply le_antisymm c.cz
  intro m hm
  set p : ↥P1h := c.iso.phi1.symm ⟨m, hm⟩ with hp
  have hpm : c.iso.toG1 p = m := by
    show ((c.iso.phi1 (c.iso.phi1.symm ⟨m, hm⟩) : ↥M₁) : G) = m
    rw [MulEquiv.apply_symm_apply]
  have hxz : c.iso.toG1 (Subgroup.inclusion Bh_le_P1h xB) = z := by
    rw [AutIso.toG1_inclusion]
    exact c.iso.toG_xB c.z2 c.z1 c.zc
  have hcomm : p * Subgroup.inclusion Bh_le_P1h xB = Subgroup.inclusion Bh_le_P1h xB * p :=
    Subtype.ext ((mul_xA_comm_iff (p : Ah)).2 p.2)
  have := congrArg c.iso.toG1 hcomm
  rw [map_mul, map_mul, hxz, hpm] at this
  show m ∈ Subgroup.centralizer ({z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact this

end CFSG.Quasithin.H13.F431.U42Aut
