module

public import CFSG.Sporadic.Co2Smith.GlCosetU
public import CFSG.Sporadic.Co2Smith.GlClosure

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem mul_mem_smithX_left {G : Type*} [Group G] {G₁ : Subgroup G} {u v x g : G}
    (hg : g ∈ G₁) (hx : x ∈ smithX G₁ u v) : g * x ∈ smithX G₁ u v := by
  rcases hx with hx | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inl (G₁.mul_mem hg hx)
  · exact Or.inr (Or.inl ⟨g * a, G₁.mul_mem hg ha, b, hb, by simp only [mul_assoc]⟩)
  · exact Or.inr (Or.inr ⟨g * a, G₁.mul_mem hg ha, b, hb, by simp only [mul_assoc]⟩)

theorem mul_mul_mem_smithX {G : Type*} [Group G] {G₁ : Subgroup G} {u v x g g' : G}
    (hg : g ∈ G₁) (hx : x ∈ smithX G₁ u v) (hg' : g' ∈ G₁) : g * x * g' ∈ smithX G₁ u v :=
  mul_mem_smithX (mul_mem_smithX_left hg hx) hg'

namespace SmithMarkedData

variable
  {G : Type*} [Group G] {z : G} (S : SmithMarkedData z)

theorem u_not_mem : S.u ∉ S.G₁ := by
  intro h
  have h1 := S.mem_G1c_of_phiInv_mem uK_mem_Cz h
  rw [mem_G1c, co2PermHom_uK] at h1
  exact absurd h1 (by decide)

theorem ρ_mem_of_C1c {k : K} (hk : k ∈ C1c) : S.ρ ⟨k, hk.1⟩ ∈ S.G₁ := by
  rw [S.ρ_eq_Ψ hk.1 hk.2]
  exact S.Ψ_mem _

theorem u_not_mem_normalizer : S.u ∉ normalizer (S.G₁ : Set G) := by
  intro hu
  have h14z : glElt 14 ∈ Cz := glElt_mem_Cz (by decide)
  have hG : S.phiInv ⟨glElt 14, h14z⟩ ∈ S.G₁ := by
    rw [← S.Ψ_eq_phiInv z0_mem_G1c glElt14_mem_G1c h14z]
    exact S.Ψ_mem _
  have h1 := (mem_normalizer_iff.1 hu _).1 hG
  have hc : uK * glElt 14 * uK⁻¹ ∈ Cz := Cz.mul_mem (Cz.mul_mem uK_mem_Cz h14z)
    (Cz.inv_mem uK_mem_Cz)
  have e : S.u * S.phiInv ⟨glElt 14, h14z⟩ * S.u⁻¹ = S.phiInv ⟨_, hc⟩ := by
    rw [u, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e] at h1
  have h2 := S.mem_G1c_of_phiInv_mem hc h1
  rw [mem_G1c, inv_eq_of_mul_eq_one_right uK_mul_self, map_mul, map_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, co2PermHom_uK, glElt14_1172] at h2
  have h3 : co2PermHom uK 1172 = glP0 := by
    rw [← co2PermHom_uK, ← Equiv.Perm.mul_apply, ← map_mul, uK_mul_self, map_one]
    rfl
  exact absurd ((co2PermHom uK).injective (h2.trans h3.symm)) (by decide)


theorem u_mem_of_ρ_mem {k : K} (hk : k ∈ C0c) (hkG : S.ρ ⟨k, hk⟩ ∈ S.G₁) {x : ℕ}
    (hx : x ∈ Native.glWit0Pts 1) (hkx : (co2PermHom k glP0 : ℕ) = x) : S.u ∈ S.G₁ := by
  obtain ⟨hx', a, ha, hax⟩ := exists_C1c_of_mem hx
  have hb0 : (a * uK)⁻¹ * k ∈ C0c :=
    C0c.mul_mem (C0c.inv_mem (C0c.mul_mem ha.1 uK_mem_C0c)) hk
  have hb1 : (a * uK)⁻¹ * k ∈ G1c := by
    show co2PermHom ((a * uK)⁻¹ * k) glP0 = glP0
    have e : co2PermHom k glP0 = co2PermHom (a * uK) glP0 := by
      rw [hax]
      exact Fin.ext hkx
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, e, CFSG.Certificates.perm_inv_apply_self]
  have e : (⟨k, hk⟩ : C0c) = ⟨a, ha.1⟩ * ⟨uK, uK_mem_C0c⟩ * ⟨_, hb0⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  have hu : S.u = (S.ρ ⟨a, ha.1⟩)⁻¹ * S.ρ ⟨k, hk⟩ * (S.ρ ⟨_, hb0⟩)⁻¹ := by
    rw [e, map_mul, map_mul, S.ρ_uK]
    group
  rw [hu]
  exact S.G₁.mul_mem (S.G₁.mul_mem (S.G₁.inv_mem (S.ρ_mem_of_C1c ha)) hkG)
    (S.G₁.inv_mem (S.ρ_mem_of_C1c ⟨hb0, hb1⟩))

theorem v_not_mem_normalizer : S.v ∉ normalizer (S.G₁ : Set G) := by
  intro hv
  have hz0 : z0 ∈ C0c := x16K_eq ▸ x16K_mem_C0c
  have h1 := (mem_normalizer_iff.1 hv _).1 (S.ρ_mem_of_C1c ⟨hz0, z0_mem_G1c⟩)
  have hg0 : v1K * z0 * v1K⁻¹ ∈ C0c :=
    C0c.mul_mem (C0c.mul_mem v1K_mem_C0c hz0) (C0c.inv_mem v1K_mem_C0c)
  have e : S.v * S.ρ ⟨z0, hz0⟩ * S.v⁻¹ = S.ρ ⟨_, hg0⟩ := by
    rw [v, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e] at h1
  refine S.u_not_mem (S.u_mem_of_ρ_mem hg0 h1 mem_glWit0Pts_1977 ?_)
  rw [inv_eq_of_mul_eq_one_right v1K_mul_self, map_mul, Equiv.Perm.mul_apply, co2PermHom_v1K,
    ← x16K_eq, v1K_x16K_582]
  rfl

theorem ρ_mem_smithX {k : K}
    (hk : k ∈ C0c) :
    S.ρ ⟨k, hk⟩ ∈ smithX S.G₁ S.u S.v := by
  rcases mem_C0c_iff.1 hk with h | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
  · exact Or.inl (S.ρ_mem_of_C1c h)
  · refine Or.inr (Or.inl ⟨S.ρ ⟨a, ha.1⟩, S.ρ_mem_of_C1c ha, S.ρ ⟨b, hb.1⟩,
      S.ρ_mem_of_C1c hb, ?_⟩)
    rw [← S.ρ_uK, ← map_mul, ← map_mul]
    rfl
  · have hβ : β3K ∈ C1c := ⟨β3K_mem_C0c, β3K_mem_G1c⟩
    have hβG := S.ρ_mem_of_C1c hβ
    refine Or.inr (Or.inr ⟨S.ρ ⟨a, ha.1⟩ * (S.ρ ⟨β3K, hβ.1⟩)⁻¹ * (S.ρ ⟨β3K, hβ.1⟩)⁻¹,
      S.G₁.mul_mem (S.G₁.mul_mem (S.ρ_mem_of_C1c ha) (S.G₁.inv_mem hβG)) (S.G₁.inv_mem hβG),
      (S.ρ ⟨β3K, hβ.1⟩)⁻¹ * S.ρ ⟨b, hb.1⟩, S.G₁.mul_mem (S.G₁.inv_mem hβG) (S.ρ_mem_of_C1c hb),
      ?_⟩)
    have e : (⟨a * vK * b, hk⟩ : C0c) = ⟨a, ha.1⟩ * (⟨β3K, hβ.1⟩⁻¹ * ⟨β3K, hβ.1⟩⁻¹ *
        ⟨v1K, v1K_mem_C0c⟩ * ⟨β3K, hβ.1⟩⁻¹) * ⟨b, hb.1⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [vK_eq])
    rw [e, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, ← v]
    group

theorem v_mem_closure : S.v ∈ closure ((S.G₁ : Set G) ∪ {S.u}) := by
  have hG : ∀ g ∈ S.G₁, g ∈ closure ((S.G₁ : Set G) ∪ {S.u}) :=
    fun g hg => subset_closure (Or.inl hg)
  have hu : S.u ∈ closure ((S.G₁ : Set G) ∪ {S.u}) := subset_closure (Or.inr rfl)
  rw [S.v_eq]
  exact mul_mem (hG _ (S.Ψ_mem _)) (mul_mem (hG _ (S.Ψ_mem _)) (mul_mem hu
    (mul_mem (hG _ (S.Ψ_mem _)) (mul_mem hu (hG _ (S.Ψ_mem _))))))

end SmithMarkedData

end CFSG.Sporadic.Co2Smith
