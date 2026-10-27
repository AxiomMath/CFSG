module

public import CFSG.LocalAnalysis.StandardType.GGSignedTorusAutomizer
public import CFSG.LocalAnalysis.StandardType.GGTBJCoverBstar
import CFSG.LocalAnalysis.StandardType.GGNbrReflectionLift
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly Multiplicative

theorem mem_range_inner_lift_of_pow_eq_one_of_commute {G R : Type} [Group G] [Group R]
    {p : ℕ} {Bs : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (ψ : R →* G) (hψinj : Function.Injective ψ) (hZR : Subgroup.center R = ⊥)
    (ℓ : ↥Bs →* R) (hcompat : ∀ (b : ↥Bs) (u : R),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    {z : R} (hzp : z ^ p = 1) (hcz : ∀ a ∈ ℓ.range, z * a = a * z) : z ∈ ℓ.range := by
  have hψC : ψ z ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hcompat ⟨a, ha⟩ z
    rw [(hcz (ℓ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).symm, mul_inv_cancel_right] at h
    have hh := congrArg (fun v : G => a * v) h
    simpa only [Subtype.coe_mk, mul_assoc, mul_inv_cancel_left] using hh.symm
  have hψB : ψ z ∈ Bs := hSC (ψ z) hψC (by rw [← map_pow, hzp, map_one])
  let b : ↥Bs := ⟨ψ z, hψB⟩
  have heq : ℓ b = z⁻¹ := by
    apply CFSG.mulAut_conj_injective hZR
    apply MulEquiv.ext
    intro u
    apply hψinj
    change ψ (ℓ b * u * (ℓ b)⁻¹) = ψ (z⁻¹ * u * z⁻¹⁻¹)
    simpa only [b, map_mul, map_inv, inv_inv] using (hcompat b u).symm
  simpa only [inv_inv] using ℓ.range.inv_mem (show z⁻¹ ∈ ℓ.range from ⟨b, heq⟩)

theorem exists_coxeterB_three_automizer_of_inner_lift
    {G R : Type} [Group G] [Finite G] [Group R] [Finite R]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (ψ : R →* G) (hψinj : Function.Injective ψ) (hψrange : ψ.range = L)
    (hZR : Subgroup.center R = ⊥) (ℓ : ↥Bs →* R)
    (hcompat : ∀ (b : ↥Bs) (z : R),
      (b : G)⁻¹ * ψ z * (b : G) = ψ (ℓ b * z * (ℓ b)⁻¹))
    (e₀ : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer (⊤ : Subgroup R) ℓ.range))
    (he₀ : ∀ i, GGIsReflection p (e₀ ((CoxeterMatrix.B 3).simple i) : MulAut ↥ℓ.range)) :
    ∃ e : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs),
      ∀ i, GGIsReflection p (e ((CoxeterMatrix.B 3).simple i) : MulAut ↥Bs) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let α : R ≃* ↥L := (MonoidHom.ofInjective hψinj).trans
    (MulEquiv.subgroupCongr hψrange)
  have hα : ∀ z, (α z : G) = ψ z := fun _ => rfl
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have hz : α.symm l ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply α.injective
      simpa only [map_mul, α.apply_symm_apply] using
        Subgroup.mem_center_iff.mp hl (α z)
    rw [hZR, Subgroup.mem_bot] at hz
    rw [Subgroup.mem_bot]
    exact α.symm.injective (by simpa only [map_one] using hz)
  let π : ↥L →* R := α.symm.toMonoidHom
  let Λ : R →* MulAut ↥L := (MulAut.conj : ↥L →* MulAut ↥L).comp α.toMonoidHom
  have hΛinj : Function.Injective Λ :=
    (CFSG.mulAut_conj_injective hZL).comp α.injective
  have hΛc : ∀ l, Λ (π l) = MulAut.conj l := by
    intro l
    simp only [Λ, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, α.apply_symm_apply]
  have hΛn : ∀ z l, π (Λ z l) = z * π l * z⁻¹ := by
    intro z l
    simp only [Λ, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, α.symm_apply_apply]
  have hγ : ∀ b : ↥Bs, ggGamma L hBL b = Λ (ℓ (b⁻¹)) := by
    intro b
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    change (b : G) * (l : G) * (b : G)⁻¹ =
      (α (ℓ (b⁻¹)) : G) * (l : G) * (α (ℓ (b⁻¹)) : G)⁻¹
    rw [hα]
    have hback : ψ (α.symm l) = (l : G) := by rw [← hα, α.apply_symm_apply]
    simpa only [Subgroup.coe_inv, inv_inv, map_mul, map_inv, hback] using
      hcompat b⁻¹ (α.symm l)
  have hA : (ggGamma L hBL).range = ℓ.range.map Λ := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨ℓ (b⁻¹), ⟨b⁻¹, rfl⟩, (hγ b).symm⟩
    · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
      exact ⟨b⁻¹, by rw [hγ, inv_inv]⟩
  have hEc : ∀ a ∈ ℓ.range, ∀ b ∈ ℓ.range, a * b = b * a := by
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    rw [← map_mul, ← map_mul, hBs.1.is_comm.comm u v]
  have hπk : π.ker ≤ Subgroup.center ↥L := by
    rw [MonoidHom.ker_eq_bot π α.symm.injective]
    exact bot_le
  obtain ⟨δ, hδ, hδE, hδsurj, hδker, hδL, hδlift, hδuniq, hN1, hN2, hδconj⟩ :=
    ggCover_bstar hBs hSC hBL (fun z hz _ => by simpa only [hZL, Subgroup.mem_bot] using hz)
      π α.symm.surjective hπk Λ hΛinj hΛc hΛn hEc hA
  obtain ⟨θ, hθ⟩ := ggCover_automizer π α.symm.surjective δ hδE hδsurj hδker hδL
    hδlift hδuniq hN1 hN2 hδconj
  let e : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs) := e₀.trans θ.symm
  have hθe : ∀ w, θ (e w) = e₀ w := fun w => θ.apply_symm_apply (e₀ w)
  refine ⟨e, fun i => ?_⟩
  let r : ↥(ggAutomizer L Bs) := e ((CoxeterMatrix.B 3).simple i)
  have hr : GGIsReflection p (θ r : MulAut ↥ℓ.range) := by
    rw [show θ r = e₀ ((CoxeterMatrix.B 3).simple i) from hθe _]
    exact he₀ i
  let β : ↥Bs →* ↥ℓ.range := δ.codRestrict ℓ.range hδE
  have hβsurj : Function.Surjective β := by
    intro z
    obtain ⟨b, hb⟩ := hδsurj z z.2
    exact ⟨b, Subtype.ext hb⟩
  have hθsq : (θ r) ^ 2 = 1 := Subtype.ext hr.1
  have hrsq : r ^ 2 = 1 := θ.injective (by simpa only [map_pow, map_one] using hθsq)
  have hrsq' : (r : MulAut ↥Bs) ^ 2 = 1 := congrArg Subtype.val hrsq
  have hcr : ∀ b, β ((r : MulAut ↥Bs) b) = (θ r : MulAut ↥ℓ.range) (β b) :=
    fun b => Subtype.ext (hθ r b).symm
  have hfix : ∀ b ∈ β.ker, (r : MulAut ↥Bs) b = b := by
    intro b hb
    have hδb : δ b = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hb)
    have hbC := (hδker b).mp hδb
    obtain ⟨g, hgL, -, hrg⟩ := mem_ggAutomizer_iff.mp r.2
    apply Subtype.ext
    rw [hrg b, Subgroup.mem_centralizer_iff.mp hbC g hgL, mul_inv_cancel_right]
  exact isReflection_of_quotient hp hp2
    (fun a b : ↥Bs => hBs.1.is_comm.comm a b)
    (fun b : ↥Bs => Subtype.ext (by simpa using hBs.2 b b.2)) β hβsurj
    (r : MulAut ↥Bs) (θ r : MulAut ↥ℓ.range) hcr hfix
    (a := 1) (by simpa using hrsq') hr.1 hr.2

end CFSG.StandardType

end
