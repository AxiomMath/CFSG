module

public import CFSG.Open.FusionDefs

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

theorem kernel_conjugator_into_sylow (S : Sylow p G) (N : Subgroup G) [N.Normal]
    {x : G} (hx : x ∈ (S : Subgroup G) ⊔ N)
    (hxp : IsPGroup p (Subgroup.zpowers x)) :
    ∃ n : G, n ∈ N ∧ n * x * n⁻¹ ∈ (S : Subgroup G) := by
  let K : Subgroup G := (S : Subgroup G) ⊔ N
  let xK : K := ⟨x, hx⟩
  let SK : Sylow p K := S.subtype le_sup_left
  have hxKp : IsPGroup p (Subgroup.zpowers xK) := by
    have hmap : (Subgroup.zpowers xK).map K.subtype = Subgroup.zpowers x :=
      MonoidHom.map_zpowers _ _
    exact hxp.of_equiv
      ((Subgroup.zpowers xK).equivMapOfInjective K.subtype K.subtype_injective |>.trans
        (MulEquiv.subgroupCongr hmap)).symm
  obtain ⟨P, hP⟩ := hxKp.exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq K P SK
  have hbx : (MulAut.conj b) xK ∈ (b • P : Sylow p K) :=
    Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom (hP (Subgroup.mem_zpowers xK))
  rw [hb] at hbx
  have hbxG : (b : G) * x * (b : G)⁻¹ ∈ (S : Subgroup G) := hbx
  obtain ⟨s, hs, n, hn, hsn⟩ := Subgroup.mem_sup_of_normal_right.mp b.property
  refine ⟨n, hn, ?_⟩
  have hmem := (S : Subgroup G).mul_mem
    ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs) hbxG) hs
  rw [← hsn] at hmem
  have heq : s⁻¹ * ((s * n) * x * (s * n)⁻¹) * s = n * x * n⁻¹ := by group
  exact heq ▸ hmem

theorem stronglyClosed_map_surjective {Y : Type*} [Group Y]
    (f : G →* Y) (hf : Function.Surjective f) (S : Sylow p G) (A : Subgroup G)
    (hAS : A ≤ (S : Subgroup G))
    (hclosed : fusionStronglyClosed (A : Set G) (S : Subgroup G)) :
    fusionStronglyClosed (A.map f : Set Y) (S.mapSurjective hf : Subgroup Y) := by
  intro aImage haImage y hy
  obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp haImage
  obtain ⟨g, rfl⟩ := hf y
  let x : G := g⁻¹ * a * g
  have hx : x ∈ (S : Subgroup G) ⊔ f.ker := by
    rw [← Subgroup.comap_map_eq]
    change f x ∈ (S : Subgroup G).map f
    simpa only [x, map_mul, map_inv, Sylow.coe_mapSurjective] using hy
  have hap : IsPGroup p (Subgroup.zpowers a) := by
    have haz : Subgroup.zpowers a ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr (hAS haA)
    exact S.isPGroup'.of_injective (Subgroup.inclusion haz) (Subgroup.inclusion_injective haz)
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    have hmap : (Subgroup.zpowers a).map (MulAut.conj g⁻¹).toMonoidHom =
        Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change g⁻¹ * a * (g⁻¹)⁻¹ = g⁻¹ * a * g
      rw [inv_inv]
    exact hmap ▸ hap.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨n, hn, hnx⟩ := kernel_conjugator_into_sylow S f.ker hx hxp
  have heq : n * x * n⁻¹ = (g * n⁻¹)⁻¹ * a * (g * n⁻¹) := by
    dsimp only [x]
    group
  have hna : n * x * n⁻¹ ∈ A := by
    rw [heq] at hnx ⊢
    exact hclosed a haA (g * n⁻¹) hnx
  have hfn : f n = 1 := hn
  refine Subgroup.mem_map.mpr ⟨n * x * n⁻¹, hna, ?_⟩
  simp only [map_mul, map_inv, hfn, one_mul, inv_one, mul_one]
  simp only [x, map_mul, map_inv]

theorem quotient_stronglyClosed (S : Sylow p G) (A N : Subgroup G) [N.Normal]
    (hAS : A ≤ (S : Subgroup G))
    (hclosed : fusionStronglyClosed (A : Set G) (S : Subgroup G)) :
    ∃ Sbar : Sylow p (G ⧸ N),
      (Sbar : Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) ∧
      fusionStronglyClosed (A.map (QuotientGroup.mk' N) : Set (G ⧸ N))
        (Sbar : Subgroup (G ⧸ N)) := by
  refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective N), Sylow.coe_mapSurjective _ S, ?_⟩
  exact stronglyClosed_map_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) S A hAS hclosed

end CFSG.ShultStronglyClosedTI
