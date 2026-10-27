module

public import CFSG.Quasithin.H13.GoldschmidtU43EQAb
public import CFSG.Quasithin.H13.GoldschmidtU43EMat2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6
open scoped commutatorElement

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem comm_z_mem_Vg (hAU : (S.A : G) ∈ Uz z) {x : G} (hx : x ∈ S.Cg1) :
    z * x * z⁻¹ * x⁻¹ ∈ S.Vg := by
  obtain ⟨c, hc, hcH, v, hv, rfl⟩ := S.Cg1_eq_mul hAU hx
  have hzC : z ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact (z_comm_H S.σ₁).symm
  have hcz : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hcH).symm
  have h1 : z * v * z⁻¹ * v⁻¹ ∈ S.Vg :=
    mul_mem (S.conj_mem_Vg hzC hv) (inv_mem hv)
  have h2 : z * (c * v) * z⁻¹ * (c * v)⁻¹ = c * (z * v * z⁻¹ * v⁻¹) * c⁻¹ := by
    calc z * (c * v) * z⁻¹ * (c * v)⁻¹ = (z * c) * v * z⁻¹ * v⁻¹ * c⁻¹ := by group
      _ = (c * z) * v * z⁻¹ * v⁻¹ * c⁻¹ := by rw [hcz]
      _ = c * (z * v * z⁻¹ * v⁻¹) * c⁻¹ := by group
  rw [h2]
  exact S.conj_mem_Vg hc h1

theorem rho_mem_Vg (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : r.ρ ∈ S.Vg := by
  have hρM := r.mem_Mg
  have hσM : (S.σ₁ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₁G_mem_Tg
  have hρC : r.ρ ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact S.abelian_Mg _ hρM _ hσM
  have h := S.comm_z_mem_Vg hAU hρC
  rw [r.inv] at h
  have h3 : r.ρ * r.ρ * r.ρ = 1 := by
    rw [← pow_three']
    exact S.rho_pow_three r.mem r.inv
  have e : r.ρ⁻¹ * r.ρ⁻¹ = r.ρ := by
    calc r.ρ⁻¹ * r.ρ⁻¹ = r.ρ⁻¹ * r.ρ⁻¹ * (r.ρ * r.ρ * r.ρ) := by rw [h3, mul_one]
      _ = r.ρ := by group
  have : r.ρ⁻¹ * r.ρ⁻¹ ∈ S.Vg := by
    have e2 : r.ρ⁻¹ * r.ρ⁻¹ = r.ρ⁻¹ * r.ρ⁻¹ := rfl
    simpa [mul_assoc] using h
  rwa [e] at this

theorem rho2_mem_Vg (hAU : (S.A : G) ∈ Uz z) (r : S.Rho) : S.rho2 r.ρ ∈ S.Vg := by
  have hρM := S.rho2_mem_Mg r.mem_Mg
  have hσM : (S.σ₁ : G) ∈ S.Mg := S.Tg_le_Mg S.σ₁G_mem_Tg
  have hinv := S.z_rho2 r.inv
  have hρC : S.rho2 r.ρ ∈ S.Cg1 := by
    rw [Cg1, Subgroup.mem_centralizer_singleton_iff]
    exact S.abelian_Mg _ hρM _ hσM
  have h := S.comm_z_mem_Vg hAU hρC
  rw [hinv] at h
  have h3 : S.rho2 r.ρ * S.rho2 r.ρ * S.rho2 r.ρ = 1 := by
    rw [← pow_three']
    exact S.pow_three_Mg _ hρM
  have e : (S.rho2 r.ρ)⁻¹ * (S.rho2 r.ρ)⁻¹ = S.rho2 r.ρ := by
    calc (S.rho2 r.ρ)⁻¹ * (S.rho2 r.ρ)⁻¹
        = (S.rho2 r.ρ)⁻¹ * (S.rho2 r.ρ)⁻¹ * (S.rho2 r.ρ * S.rho2 r.ρ * S.rho2 r.ρ) := by
          rw [h3, mul_one]
      _ = S.rho2 r.ρ := by group
  have : (S.rho2 r.ρ)⁻¹ * (S.rho2 r.ρ)⁻¹ ∈ S.Vg := by
    simpa [mul_assoc] using h
  rwa [e] at this

theorem Vg_isNilpotent (hAU : (S.A : G) ∈ Uz z) : Group.IsNilpotent ↥S.Vg := by
  refine ⟨⟨2, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro g
  have hx : ((x : ↥S.Vg) : G)⁻¹ ∈ S.Vg := S.Vg.inv_mem x.2
  have hy : ((y : ↥S.Vg) : G)⁻¹ ∈ S.Vg := S.Vg.inv_mem y.2
  have h := (S.Vg_comm_mem hAU).2 _ hx _ hy
  have ht : ((⁅x, y⁆ : ↥S.Vg) : G) ∈ Subgroup.zpowers (S.σ₁ : G) := by
    simpa [commutatorElement_def] using h
  have hg : (g : G) * (S.σ₁ : G) = (S.σ₁ : G) * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (S.Vg_le_Cg1 g.2)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  apply Subtype.ext
  show (g : G) * ((⁅x, y⁆ : ↥S.Vg) : G) = ((⁅x, y⁆ : ↥S.Vg) : G) * g
  rw [← hk]
  exact ((Commute.zpow_right (show Commute (g : G) (S.σ₁ : G) from hg) k)).eq

theorem exists_V3 (hAU : (S.A : G) ∈ Uz z) : ∃ V₃ : Subgroup G, V₃ ≤ S.Vg ∧ IsPGroup 3 V₃ ∧
    (∀ T : Subgroup G, T ≤ S.Vg → IsPGroup 3 T → T ≤ V₃) ∧
    ∀ c ∈ S.Cg1, ∀ x ∈ V₃, c * x * c⁻¹ ∈ V₃ := by
  have : Group.IsNilpotent ↥S.Vg := S.Vg_isNilpotent hAU
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥S.Vg))
  have hnorm : (P : Subgroup ↥S.Vg).Normal := inferInstance
  let := Sylow.unique_of_normal P hnorm
  have hmax : ∀ T : Subgroup G, T ≤ S.Vg → IsPGroup 3 T →
      T ≤ (P : Subgroup ↥S.Vg).map S.Vg.subtype := by
    intro T hTV hT x hx
    have hT' : IsPGroup 3 (T.subgroupOf S.Vg) := hT.comap_subtype
    obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim _ _
    subst hQP
    exact ⟨⟨x, hTV hx⟩, hQ (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  refine ⟨(P : Subgroup ↥S.Vg).map S.Vg.subtype, ?_, ?_, hmax, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact v.2
  · exact P.isPGroup'.map _
  · intro c hc x hx
    have hle : ((P : Subgroup ↥S.Vg).map S.Vg.subtype).map (MulAut.conj c).toMonoidHom ≤ S.Vg := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨v, -, rfl⟩ := hy
      exact S.conj_mem_Vg hc v.2
    have hp : IsPGroup 3 (((P : Subgroup ↥S.Vg).map S.Vg.subtype).map
        (MulAut.conj c).toMonoidHom) := (P.isPGroup'.map _).map _
    exact hmax _ hle hp ⟨x, hx, rfl⟩

end JWSetup

end CFSG.Quasithin.H13.U43
