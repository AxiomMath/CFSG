module

public import CFSG.Quasithin.Vol2.GoldschmidtF431q2G2Chain
public import CFSG.Quasithin.Vol2.GoldschmidtF431q2LocMap

public section

namespace CFSG.Quasithin.H13.F431.G2Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F6.G22Perm CFSG.Quasithin.F6.G22Shape

namespace Model

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2

theorem false_of_embeddings {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {z : G}
    (φ₁ : ↥(lat h2 hk2).P₂ →* G) (φ₂ : ↥(lat h2 hk2).P₁ →* G) (inj₁ : Function.Injective φ₁)
    (range₁ : φ₁.range = Subgroup.centralizer ({z} : Set G))
    (agree : ∀ (g : G2Group k) (h₁ : g ∈ (lat h2 hk2).P₁) (h₂ : g ∈ (lat h2 hk2).P₂),
      g ∈ (lat h2 hk2).S → φ₁ ⟨g, h₂⟩ = φ₂ ⟨g, h₁⟩)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) : False := by
  have hzr : z ∈ φ₁.range := by rw [range₁]; exact mem_centralizer_singleton.2 rfl
  obtain ⟨p₀, hp₀⟩ := hzr
  have hcen : ∀ q : ↥(lat h2 hk2).P₂, q * p₀ = p₀ * q := fun q => by
    apply inj₁
    have : φ₁ q ∈ Subgroup.centralizer ({z} : Set G) := by rw [← range₁]; exact ⟨q, rfl⟩
    rw [map_mul, map_mul, hp₀]
    exact (mem_centralizer_singleton.1 this).symm
  have hp1 : p₀ ≠ 1 := fun h => hz1 (by rw [← hp₀, h, map_one])
  have hp2 : p₀ * p₀ = 1 := inj₁ (by rw [map_mul, hp₀, hz2, map_one])
  have hpz : (p₀ : G2Group k) = sEl h2 26 := eq_z_of_central h2 hk2 p₀.2
    (fun h => hp1 (Subtype.ext h)) (congrArg Subtype.val hp2)
    (fun q hq => congrArg Subtype.val (hcen ⟨q, hq⟩))
  have L := g2Loc h2 hk2
  have hzeq : φ₁ ⟨sEl h2 26, L.z_mem_P⟩ = z := by
    rw [← hp₀]
    exact congrArg φ₁ (Subtype.ext hpz.symm)
  have hSz : sEl h2 26 ∈ (lat h2 hk2).S := sEl_mem_S h2 hk2 (by norm_num)
  have hconj : ∀ w ∈ ((TpSub h2 hk2).subgroupOf (lat h2 hk2).P₂).map φ₁, w * w = 1 → w ≠ 1 →
      IsConj (φ₁ ⟨sEl h2 26, L.z_mem_P⟩) w := by
    intro w hw hw2 hw1
    obtain ⟨p, hpT, rfl⟩ := Subgroup.mem_map.1 hw
    have hp2 : (p : G2Group k) * p = 1 :=
      congrArg Subtype.val (inj₁ (by rw [map_mul, hw2, map_one]) : p * p = 1)
    have hp1 : (p : G2Group k) ≠ 1 := fun h => hw1 (by rw [show p = 1 from Subtype.ext h, map_one])
    obtain ⟨a, ha, b, hb, u, hu, hau, hbu⟩ := chain h2 hk2 hpT hp2 hp1
    have e1 : (⟨a, ha⟩ : ↥(lat h2 hk2).P₂) * p * ⟨a, ha⟩⁻¹ = ⟨u, (lat h2 hk2).S_le_P₂ hu⟩ :=
      Subtype.ext hau
    have e2 : (⟨b, hb⟩ : ↥(lat h2 hk2).P₁) * ⟨u, (lat h2 hk2).S_le_P₁ hu⟩ * ⟨b, hb⟩⁻¹ =
        ⟨sEl h2 26, (lat h2 hk2).S_le_P₁ hSz⟩ := Subtype.ext hbu
    have a1 := agree u ((lat h2 hk2).S_le_P₁ hu) ((lat h2 hk2).S_le_P₂ hu) hu
    have a2 := agree (sEl h2 26) ((lat h2 hk2).S_le_P₁ hSz) L.z_mem_P hSz
    refine (isConj_iff.2 ⟨φ₂ ⟨b, hb⟩ * φ₁ ⟨a, ha⟩, ?_⟩).symm
    calc φ₂ ⟨b, hb⟩ * φ₁ ⟨a, ha⟩ * φ₁ p * (φ₂ ⟨b, hb⟩ * φ₁ ⟨a, ha⟩)⁻¹ =
        φ₂ ⟨b, hb⟩ * (φ₁ ⟨a, ha⟩ * φ₁ p * (φ₁ ⟨a, ha⟩)⁻¹) * (φ₂ ⟨b, hb⟩)⁻¹ := by group
      _ = φ₂ ⟨b, hb⟩ * φ₁ ⟨u, (lat h2 hk2).S_le_P₂ hu⟩ * (φ₂ ⟨b, hb⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, e1]
      _ = φ₂ (⟨b, hb⟩ * ⟨u, (lat h2 hk2).S_le_P₁ hu⟩ * ⟨b, hb⟩⁻¹) := by
        rw [a1, map_mul, map_mul, map_inv]
      _ = φ₁ ⟨sEl h2 26, L.z_mem_P⟩ := by rw [e2, ← a2]
  exact (L.toData inj₁ (by rw [hzeq]; exact range₁) hconj).false_of_simple

end Model

end CFSG.Quasithin.H13.F431.G2Two
