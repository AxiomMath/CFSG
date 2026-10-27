module

public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree

namespace Sec159Cfg

variable {M : Type} [Group M]

@[expose] noncomputable def actQ (X : Subgroup M) [X.Normal] (θ : Subgroup ↥X) [θ.Characteristic] :
    M →* MulAut (↥X ⧸ θ) :=
  (mulAutQuotientHom θ).comp MulAut.conjNormal

theorem actQ_mk (X : Subgroup M) [X.Normal] (θ : Subgroup ↥X) [θ.Characteristic] (g : M) (x : ↥X) :
    actQ X θ g (x : ↥X ⧸ θ) = ((MulAut.conjNormal g x : ↥X) : ↥X ⧸ θ) := rfl

theorem mem_ker_actQ {X : Subgroup M} [X.Normal] {θ : Subgroup ↥X} [θ.Characteristic] {g : M} :
    g ∈ (actQ X θ).ker ↔ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ θ.map X.subtype := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    have h1 := congrArg (fun φ : MulAut (↥X ⧸ θ) => φ ((⟨x, hx⟩ : ↥X) : ↥X ⧸ θ)) h
    simp only [actQ_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq_iff_div_mem] at h1
    exact ⟨_, h1, by simp [MulAut.conjNormal_apply, div_eq_mul_inv]⟩
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [actQ_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem]
      obtain ⟨z, hz, hzx⟩ := h x x.2
      have : z = MulAut.conjNormal g x / x := Subtype.ext (by
        simpa [MulAut.conjNormal_apply, div_eq_mul_inv] using hzx)
      rwa [← this]

theorem pow_mem_of_sup_eq_top {p : ℕ} {X E : Subgroup M} [X.Normal] (hXE : X ⊔ E = ⊤)
    (hE : ∀ e ∈ E, e ^ p = 1) (y : M) : y ^ p ∈ X := by
  have hy : y ∈ X ⊔ E := hXE ▸ Subgroup.mem_top y
  obtain ⟨x, hx, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
  have h1 : (QuotientGroup.mk' X) (x * e) = (QuotientGroup.mk' X) e := by
    simp [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, h1, ← map_pow, hE e he,
    map_one]

theorem mk_mem_center_of_mem_ker {X : Subgroup M} [X.Normal] {θ : Subgroup ↥X} [θ.Characteristic]
    {x : M} (hx : x ∈ X) (hk : x ∈ (actQ X θ).ker) :
    ((⟨x, hx⟩ : ↥X) : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ) := by
  rw [Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    obtain ⟨z, hz, hzx⟩ := mem_ker_actQ.1 hk y y.2
    have : y * ⟨x, hx⟩ / (⟨x, hx⟩ * y) = z⁻¹ := by
      refine Subtype.ext ?_
      have h2 : (x * (y : M) * x⁻¹ * (y : M)⁻¹) = (z : M) := hzx.symm
      calc ((y * ⟨x, hx⟩ / (⟨x, hx⟩ * y) : ↥X) : M) = ((y : M) * x * ((x : M) * y)⁻¹) := by
            simp [div_eq_mul_inv]
        _ = ((x * (y : M) * x⁻¹ * (y : M)⁻¹))⁻¹ := by group
        _ = ((z⁻¹ : ↥X) : M) := by rw [h2]; simp
    rw [this]
    exact θ.inv_mem hz

theorem mem_ker_of_mk_mem_center {X : Subgroup M} [X.Normal] {θ : Subgroup ↥X} [θ.Characteristic]
    {x : M} (hx : x ∈ X)
    (hc : ((⟨x, hx⟩ : ↥X) : ↥X ⧸ θ) ∈ Subgroup.center (↥X ⧸ θ)) : x ∈ (actQ X θ).ker := by
  rw [mem_ker_actQ]
  intro y hy
  have h1 := Subgroup.mem_center_iff.1 hc ((⟨y, hy⟩ : ↥X) : ↥X ⧸ θ)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem] at h1
  refine ⟨_, θ.inv_mem h1, ?_⟩
  simp only [Subgroup.coe_subtype, div_eq_mul_inv, Subgroup.coe_inv, Subgroup.coe_mul]
  group

end Sec159Cfg

end CFSG.RankThree.PartOne
