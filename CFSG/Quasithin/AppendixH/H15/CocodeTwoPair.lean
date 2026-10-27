module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoSylow
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiPair
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiRange

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem pair_key (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {z' g' : ↥Γ}
    (hz : (z' : S24) ∈ octFix O) (hz1 : z' ≠ 1) (hcen : ∀ v : V, ρ z' v = v → ρ g' v = v) :
    g' = 1 ∨ g' = z' := by
  obtain ⟨P⟩ := exists_phiData hM
  have hz'fix : ρ z' ∈ rImg ρ (octFix O) :=
    Subgroup.mem_map.2 ⟨z', Subgroup.mem_subgroupOf.2 hz, rfl⟩
  have hg'O : (g' : S24) ∈ octFix O := by
    refine P.mem_octFix_of_fix_pairs hM ?_
    intro p q _ _
    apply hcen
    exact (mem_fixV.1 (P.range_le_fixV hM
      (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (evPair p q), rfl⟩))) (ρ z') hz'fix
  exact kLayer_centralizes hM hz hg'O hz1 hcen

theorem pair_main (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    ∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
      cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ := by
  intro z hzΓ hz2 hc
  let zz : ↥Γ := ⟨z, hzΓ⟩
  have hsub_zp : (Subgroup.zpowers z).subgroupOf Γ = Subgroup.zpowers zz := by
    ext k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa [zz] using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa [zz] using congrArg (fun x : ↥Γ => (x : S24)) hn⟩
  have hrImg : rImg ρ (Subgroup.zpowers z) = Subgroup.zpowers (ρ zz) := by
    unfold rImg
    rw [hsub_zp, MonoidHom.map_zpowers]
  have hvW : ∀ v : V, v ∈ fixV (rImg ρ (Subgroup.zpowers z)) ↔ ρ zz v = v := by
    intro v
    simp only [hrImg, mem_fixV_zpowers_iff_apply]
  have hcen_iff : ∀ g : ↥Γ, g ∈ cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) ↔
      ∀ v : V, ρ zz v = v → ρ g v = v := by
    intro g
    simp only [cenM, Subgroup.mem_comap, mem_centSub]
    constructor
    · intro h v hv; exact h v ((hvW v).2 hv)
    · intro h v hv; exact h v ((hvW v).1 hv)
  ext g
  rw [hcen_iff g, Subgroup.mem_subgroupOf]
  constructor
  · intro hgcen
    obtain ⟨c, hcz⟩ := exists_conj_octFix hM hzΓ hz2 hc
    let z' : ↥Γ := c⁻¹ * zz * c
    have hz'coe : (z' : S24) = (c : S24)⁻¹ * z * (c : S24) := by
      simp [z', zz]
    have hz' : (z' : S24) ∈ octFix O := by
      rw [hz'coe]; exact hcz
    have hz1 : z' ≠ 1 := by
      intro h
      have hzz : zz = 1 := by
        calc zz = c * z' * c⁻¹ := by simp only [z']; group
          _ = c * 1 * c⁻¹ := by rw [h]
          _ = 1 := by group
      have hz_eq : z = 1 := by
        have hcoe := congrArg (fun x : ↥Γ => (x : S24)) hzz
        simpa [zz] using hcoe
      rw [hz_eq, orderOf_one] at hz2
      exact absurd hz2 (by decide)
    let g' : ↥Γ := c⁻¹ * g * c
    have hcen' : ∀ v : V, ρ z' v = v → ρ g' v = v := by
      intro v hv
      have hmul : ρ c * ρ z' = ρ zz * ρ c := by
        calc ρ c * ρ z' = ρ (c * z') := (map_mul ρ c z').symm
          _ = ρ (c * (c⁻¹ * zz * c)) := by simp only [z']
          _ = ρ (zz * c) := by congr 1; group
          _ = ρ zz * ρ c := map_mul ρ zz c
      have h1 : ρ zz (ρ c v) = ρ c v := by
        have hcv : (ρ c * ρ z') v = ρ c v := congrArg (fun w => ρ c w) hv
        rw [hmul, MulAut.mul_apply] at hcv
        exact hcv
      have hgcv : ρ g (ρ c v) = ρ c v := hgcen (ρ c v) h1
      have hgoal : ρ g' v = (ρ c)⁻¹ (ρ g (ρ c v)) := by
        simp only [g', map_mul, map_mul, map_inv, MulAut.mul_apply]
      rw [hgoal, hgcv]
      exact MulAut.inv_apply_self V (ρ c) v
    rcases pair_key hM hz' hz1 hcen' with h | h
    · have hg1 : g = 1 := by
        calc g = c * g' * c⁻¹ := by simp only [g']; group
          _ = c * 1 * c⁻¹ := by rw [h]
          _ = 1 := by group
      rw [hg1]
      exact Subgroup.one_mem _
    · have hgz : g = zz := by
        calc g = c * g' * c⁻¹ := by simp only [g']; group
          _ = c * z' * c⁻¹ := by rw [h]
          _ = zz := by simp only [z']; group
      rw [hgz]
      exact Subgroup.mem_zpowers z
  · intro hg v hv
    have hgmap : ρ g ∈ rImg ρ (Subgroup.zpowers z) :=
      Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    exact (mem_fixV.1 ((hvW v).2 hv)) (ρ g) hgmap

end CFSG.ASVolI.AppH

