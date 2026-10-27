module

public import CFSG.Sporadic.Co2Smith.GlNJG1

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section G

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

theorem card_Jc : Nat.card Jc = 1024 := by
  have hb : Function.Bijective (fun m : Fin 1024 => (⟨jcElt m, jcElt_mem m⟩ : Jc)) := by
    constructor
    · intro a b h
      exact Fin.ext (jcElt_inj a.2 b.2 (congrArg Subtype.val h))
    · intro x
      obtain ⟨m, hm, e⟩ := exists_coord x.2
      exact ⟨⟨m, hm⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_JGc : Nat.card (JGc φ) = 1024 := by
  rw [JGc, card_map_of_injective (phiH_injective φ), card_subgroupOf_eq Jc_le_Cz, card_Jc]

theorem elemTwo_JGc : ElemTwo (JGc φ) := by
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : K) ∈ Jc := hy
    obtain ⟨m, -, hm⟩ := exists_coord hy'
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← hm, jcElt_mul_self]; rfl)
    rw [this, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (phiH φ) (Subtype.ext (Jc_comm hy hw))

theorem exists_NG_conj [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (k : Fin 77) :
    ∃ n ∈ normalizer (JGc φ : Set G), n * z * n⁻¹ = omG φ k := by
  have hJ := elemTwo_JGc φ
  refine exists_normalizer_conj_of_class hJ (fun A hA hAe hAc => ?_) (omG_mem φ k)
    (isConj_z_omG φ hz k)
  have hcard : Nat.card (JGc φ) = Nat.card (hypG hz φ).JG := by
    rw [card_JGc, (hypG hz φ).card_JG]
  obtain ⟨g, hg, hAg⟩ := (hypG hz φ).one_class A hA hAe (hAc.trans hcard)
  obtain ⟨g', hg', hJg⟩ := (hypG hz φ).one_class (JGc φ) (JGc_le_H φ) hJ hcard
  refine ⟨g * g'⁻¹, mul_mem hg (inv_mem hg'), ?_⟩
  rw [hAg, hJg, map_conj_mul, inv_mul_cancel_right]

theorem piG_zero_iff [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) (g : normalizer (JGc φ : Set G)) :
    piG φ hz g 0 = 0 ↔ (g : G) ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have e := piG_spec φ hz g 0
    rw [h, omG_zero φ hφz] at e
    calc (g : G) * z = (g : G) * z * (g : G)⁻¹ * g := by group
      _ = z * g := by rw [← e]
  · intro h
    apply omG_injective φ
    rw [piG_spec, omG_zero φ hφz, h, mul_inv_cancel_right]

theorem phiH_mem_NG_iff (y : Cz) :
    phiH φ y ∈ normalizer (JGc φ : Set G) ↔ (y : K) ∈ normalizer (Jc : Set K) := by
  refine ⟨fun h => ?_, phiH_mem_NG φ⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨w, hw, hwe⟩ := (mem_JGc φ).1 ((mem_normalizer_iff.1 h _).1
      ((mem_JGc φ).2 ⟨⟨x, Jc_le_Cz hx⟩, hx, rfl⟩))
    have e : w = y * ⟨x, Jc_le_Cz hx⟩ * y⁻¹ := by
      apply phiH_injective φ
      rw [hwe, map_mul, map_mul, map_inv]
    rw [e] at hw
    exact hw
  · intro hx
    have hxz : x ∈ Cz := by
      have e : x = (y : K)⁻¹ * ((y : K) * x * (y : K)⁻¹) * y := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem y.2) (Jc_le_Cz hx)) y.2
    have h1 : phiH φ y * phiH φ ⟨x, hxz⟩ * (phiH φ y)⁻¹ ∈ JGc φ :=
      (mem_JGc φ).2 ⟨y * ⟨x, hxz⟩ * y⁻¹, hx, by rw [map_mul, map_mul, map_inv]⟩
    obtain ⟨w, hw, hwe⟩ := (mem_JGc φ).1 ((mem_normalizer_iff.1 h _).2 h1)
    have e : w = ⟨x, hxz⟩ := phiH_injective φ hwe
    rw [e] at hw
    exact hw

end G

end CFSG.Sporadic.Co2Smith
