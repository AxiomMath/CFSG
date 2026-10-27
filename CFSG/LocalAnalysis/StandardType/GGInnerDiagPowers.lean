module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal

variable {U G : Type*} [Group U] [Group G] {Delta : UniversalRootDatum U} {psi : U →* G}

theorem GGPsiInnerDiag.mul {c d : G} (hc : GGPsiInnerDiag Delta psi c)
    (hd : GGPsiInnerDiag Delta psi d)
    (hdN : d ∈ Subgroup.normalizer (psi.range : Set G)) :
    GGPsiInnerDiag Delta psi (c * d) := by
  obtain ⟨g, hg, hroot⟩ := hc
  obtain ⟨k, hk, kroot⟩ := hd
  have hgd : d⁻¹ * g * d ∈ psi.range := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (psi.range : Set G)).inv_mem hdN) g).mp hg
  refine ⟨d⁻¹ * g * d * k, psi.range.mul_mem hgd hk, fun gamma hgamma => ?_⟩
  obtain ⟨h, hh, hact⟩ := hroot gamma hgamma
  obtain ⟨t, ht, tact⟩ := kroot gamma hgamma
  refine ⟨t * h, (ggTorus Delta).mul_mem ht hh, fun z hz => ?_⟩
  have hz' : h * z * h⁻¹ ∈ Delta.rootGroup gamma :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_ggTorus hh hgamma) z).mp hz
  rw [show c * d * (d⁻¹ * g * d * k) = (c * g) * (d * k) by group]
  calc
    ((c * g) * (d * k))⁻¹ * psi z * ((c * g) * (d * k))
        = (d * k)⁻¹ * ((c * g)⁻¹ * psi z * (c * g)) * (d * k) := by group
    _ = (d * k)⁻¹ * psi (h * z * h⁻¹) * (d * k) := by rw [hact z hz]
    _ = psi (t * (h * z * h⁻¹) * t⁻¹) := tact _ hz'
    _ = psi ((t * h) * z * (t * h)⁻¹) := by congr 1; group

theorem GGPsiInnerDiag.inv {c : G} (hc : GGPsiInnerDiag Delta psi c)
    (hcN : c ∈ Subgroup.normalizer (psi.range : Set G)) :
    GGPsiInnerDiag Delta psi c⁻¹ := by
  obtain ⟨g, hg, hroot⟩ := hc
  have hginv : c * g⁻¹ * c⁻¹ ∈ psi.range :=
    (Subgroup.mem_normalizer_iff.mp hcN g⁻¹).mp (psi.range.inv_mem hg)
  refine ⟨c * g⁻¹ * c⁻¹, hginv, fun gamma hgamma => ?_⟩
  obtain ⟨h, hh, hact⟩ := hroot gamma hgamma
  refine ⟨h⁻¹, (ggTorus Delta).inv_mem hh, fun z hz => ?_⟩
  have hz' : h⁻¹ * z * h ∈ Delta.rootGroup gamma := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_of_mem_ggTorus ((ggTorus Delta).inv_mem hh) hgamma) z).mp hz
  have he := hact (h⁻¹ * z * h) hz'
  rw [show h * (h⁻¹ * z * h) * h⁻¹ = z by group] at he
  rw [show c⁻¹ * (c * g⁻¹ * c⁻¹) = (c * g)⁻¹ by group]
  simp only [inv_inv]
  calc
    (c * g) * psi z * (c * g)⁻¹
        = (c * g) * ((c * g)⁻¹ * psi (h⁻¹ * z * h) * (c * g)) * (c * g)⁻¹ := by rw [he]
    _ = psi (h⁻¹ * z * h) := by group

theorem GGPsiInnerDiag.pow {c : G} (hc : GGPsiInnerDiag Delta psi c)
    (hcN : c ∈ Subgroup.normalizer (psi.range : Set G)) (n : ℕ) :
    GGPsiInnerDiag Delta psi (c ^ n) := by
  induction n with
  | zero => simpa using ggPsiInnerDiag_one psi
  | succ n ih => simpa only [pow_succ] using ih.mul hc hcN

theorem GGPsiInnerDiag.zpow {c : G} (hc : GGPsiInnerDiag Delta psi c)
    (hcN : c ∈ Subgroup.normalizer (psi.range : Set G)) (n : ℤ) :
    GGPsiInnerDiag Delta psi (c ^ n) := by
  cases n with
  | ofNat n =>
      change GGPsiInnerDiag Delta psi (c ^ (n : ℤ))
      rw [zpow_natCast]
      exact hc.pow hcN n
  | negSucc n =>
      simpa only [zpow_negSucc] using (hc.pow hcN (n + 1)).inv
        ((Subgroup.normalizer (psi.range : Set G)).pow_mem hcN (n + 1))

theorem GGPsiInnerDiag.forall_mem_zpowers {c : G} (hc : GGPsiInnerDiag Delta psi c)
    (hcN : c ∈ Subgroup.normalizer (psi.range : Set G)) :
    ∀ z ∈ Subgroup.zpowers c, GGPsiInnerDiag Delta psi z := by
  rintro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact hc.zpow hcN n

end CFSG.StandardType
