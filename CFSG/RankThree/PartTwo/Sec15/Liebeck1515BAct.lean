module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

variable {G Q : Type*} [Group G] [Group Q] {H M : Subgroup G} {ρ : ↥H →* Q}

@[expose] noncomputable def conjOn {g : G} (hgH : g ∈ Subgroup.normalizer (H : Set G)) : ↥H ≃* ↥H :=
  ((MulAut.conj g).subgroupMap H).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgH))

theorem conjOn_apply {g : G} (hgH : g ∈ Subgroup.normalizer (H : Set G)) (h : ↥H) :
    ((conjOn hgH h : ↥H) : G) = g * h * g⁻¹ := rfl

theorem ker_comp_conjOn (hker : ρ.ker = M.subgroupOf H) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G)) :
    ρ.ker = (ρ.comp (conjOn hgH).toMonoidHom).ker := by
  have key : ∀ y : ↥H, ρ y = 1 ↔ (y : G) ∈ M := fun y => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, key,
    conjOn_apply]
  exact Subgroup.mem_normalizer_iff.mp hgM (x : G)

noncomputable def actAut (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G)) :
    Q ≃* Q :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_comp_conjOn hker hgH hgM)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (hρ.comp (conjOn hgH).surjective)))

theorem actAut_apply (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G))
    (h : ↥H) : actAut hρ hker hgH hgM (ρ h) = ρ (conjOn hgH h) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm (ρ h) =
      (QuotientGroup.mk h : ↥H ⧸ ρ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [actAut, MulEquiv.trans_apply, h1]
  rfl

theorem actAut_mul_apply (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H)
    {g₁ g₂ : G} (h₁H : g₁ ∈ Subgroup.normalizer (H : Set G))
    (h₁M : g₁ ∈ Subgroup.normalizer (M : Set G)) (h₂H : g₂ ∈ Subgroup.normalizer (H : Set G))
    (h₂M : g₂ ∈ Subgroup.normalizer (M : Set G)) (q : Q) :
    actAut hρ hker (mul_mem h₁H h₂H) (mul_mem h₁M h₂M) q =
      actAut hρ hker h₁H h₁M (actAut hρ hker h₂H h₂M q) := by
  obtain ⟨h, rfl⟩ := hρ q
  rw [actAut_apply, actAut_apply, actAut_apply]
  congr 1
  apply Subtype.ext
  simp only [conjOn_apply, mul_inv_rev]
  group

theorem actAut_of_mem (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H) {g : G}
    (hgH : g ∈ Subgroup.normalizer (H : Set G)) (hgM : g ∈ Subgroup.normalizer (M : Set G))
    (hg : g ∈ H) (q : Q) : actAut hρ hker hgH hgM q = ρ ⟨g, hg⟩ * q * (ρ ⟨g, hg⟩)⁻¹ := by
  obtain ⟨h, rfl⟩ := hρ q
  rw [actAut_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem actAut_one_apply (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H) (q : Q) :
    actAut hρ hker (one_mem _) (one_mem _) q = q := by
  obtain ⟨h, rfl⟩ := hρ q
  rw [actAut_apply]
  congr 1
  apply Subtype.ext
  rw [conjOn_apply, one_mul, inv_one, mul_one]

@[expose] noncomputable def actHom (hρ : Function.Surjective ρ) (hker : ρ.ker = M.subgroupOf H) :
    ↥(Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (M : Set G)) →* MulAut Q where
  toFun g := actAut hρ hker g.2.1 g.2.2
  map_one' := MulEquiv.ext fun q => actAut_one_apply hρ hker q
  map_mul' g₁ g₂ := MulEquiv.ext fun q => actAut_mul_apply hρ hker g₁.2.1 g₁.2.2 g₂.2.1 g₂.2.2 q

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
