module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77Wild

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}

@[expose] noncomputable def sec7Op (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x : G}
    (hx : x ∈ H0 M Z) : M₀.E →ₗ[K] M₀.E where
  toFun e := (ρ (QuotientGroup.mk (⟨x, hx.1⟩ : ↥M))).toAdd e
  map_add' a b := map_add (ρ (QuotientGroup.mk (⟨x, hx.1⟩ : ↥M))).toAdd a b
  map_smul' c e := hS.lin _ (Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
    c e

theorem sec7Op_apply (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x : G}
    (hx : x ∈ H0 M Z) (e : M₀.E) :
    sec7Op hc hS hx e = (ρ (QuotientGroup.mk (⟨x, hx.1⟩ : ↥M))).toAdd e := rfl

theorem sec7Op_mul (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x y : G}
    (hx : x ∈ H0 M Z) (hy : y ∈ H0 M Z) (hxy : x * y ∈ H0 M Z) :
    sec7Op hc hS hxy = sec7Op hc hS hx * sec7Op hc hS hy := by
  refine LinearMap.ext fun e => ?_
  rw [Module.End.mul_apply, sec7Op_apply, sec7Op_apply, sec7Op_apply, ← act_mul_apply ρ,
    ← QuotientGroup.mk_mul]
  rfl

theorem sec7Op_one (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) (h1 : (1 : G) ∈ H0 M Z) :
    sec7Op hc hS h1 = 1 := by
  refine LinearMap.ext fun e => ?_
  rw [sec7Op_apply, Module.End.one_apply]
  have : (QuotientGroup.mk (⟨1, h1.1⟩ : ↥M) : Mbar M Q) = 1 := rfl
  rw [this, map_one]
  rfl

theorem sec7Op_congr (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x y : G}
    (hx : x ∈ H0 M Z) (hy : y ∈ H0 M Z) (h : x = y) : sec7Op hc hS hx = sec7Op hc hS hy := by
  subst h
  rfl

theorem sec7Op_pi (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x y : G}
    (hx : x ∈ H0 M Z) (hy : y ∈ Q) : M₀.π (x * y * x⁻¹) = sec7Op hc hS hx (M₀.π y) :=
  hS.conj ⟨x, hx.1⟩ y hy

theorem sec7Op_iso (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x : G}
    (hx : x ∈ H0 M Z) (e e' : M₀.E) : M₀.B (sec7Op hc hS hx e) (sec7Op hc hS hx e') = M₀.B e e' :=
  hS.iso _ (Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩) e e'

theorem sec7Op_sub_comm (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {x y : G}
    (hx : x ∈ H0 M Z) (hy : y ∈ Q) : sec7Op hc hS hx (M₀.π y) - M₀.π y = M₀.π ⁅x, y⁆ :=
  sec7_act_sub_comm hc M₀ ρ b₀ hS hx.1 hy

@[expose] noncomputable def sec7OpHom (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀)
    (R : Subgroup G) (hR : R ≤ H0 M Z) : ↥R →* Module.End K M₀.E where
  toFun r := sec7Op hc hS (hR r.2)
  map_one' := sec7Op_one hc hS _
  map_mul' r s := sec7Op_mul hc hS (hR r.2) (hR s.2) _

end

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}

theorem sec7_mem_Wt_iff_perp (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0) {x : G} (hx : x ∈ Q) :
    x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ M₀.π x ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
  rw [hW x hx, ← sec7_ker_psi_eq_orth hc M₀ ρ b₀ hS ψ hW]
  exact LinearMap.mem_ker.symm

end

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}
  (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}

include hc hS

theorem sec7_op_mem_VtSub (ht : t ∈ LB M Q B) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {u : M₀.E}
    (hu : u ∈ hc.VtSub hS.model t) :
    sec7Op hc hS (hc.Rt_le_H0 t hr) u ∈ hc.VtSub hS.model t :=
  hc.act_mem_VtSub hS ht _ (Subgroup.mem_map.mpr
    ⟨⟨r, hc.Rt_le_M t hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩) u hu

theorem sec7_op_mem_perp (ht : t ∈ LB M Q B) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {w : M₀.E}
    (hw : w ∈ M₀.B.orthogonal (hc.VtSub hS.model t)) :
    sec7Op hc hS (hc.Rt_le_H0 t hr) w ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
  have hr' : r⁻¹ ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).inv_mem hr
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
  intro u hu
  have hu' := sec7_op_mem_VtSub hc hS ht hr' hu
  have hmul : sec7Op hc hS (hc.Rt_le_H0 t hr) (sec7Op hc hS (hc.Rt_le_H0 t hr') u) = u := by
    have h1 := sec7Op_mul hc hS (hc.Rt_le_H0 t hr) (hc.Rt_le_H0 t hr')
      ((H0 M Z).mul_mem (hc.Rt_le_H0 t hr) (hc.Rt_le_H0 t hr'))
    have h2 := sec7Op_congr hc hS ((H0 M Z).mul_mem (hc.Rt_le_H0 t hr) (hc.Rt_le_H0 t hr'))
      (H0 M Z).one_mem (mul_inv_cancel r)
    rw [h2, sec7Op_one hc hS (H0 M Z).one_mem] at h1
    have h3 := LinearMap.congr_fun h1 u
    rw [Module.End.mul_apply, Module.End.one_apply] at h3
    exact h3.symm
  have := sec7Op_iso hc hS (hc.Rt_le_H0 t hr) (sec7Op hc hS (hc.Rt_le_H0 t hr') u) w
  rw [hmul] at this
  rw [this]
  exact hw _ hu'

theorem sec7_ker_act (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) {n' : ℕ}
    (hs : Sec7Hyp hc n' t) (ψ : M₀.E →ₗ[K] M₀.E)
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0) {ν : G}
    (hν : ν ∈ hc.CN t) (hνH : ν ∈ H0 M Z) {w : M₀.E}
    (hw : w ∈ M₀.B.orthogonal (hc.VtSub hS.model t)) :
    sec7Op hc hS hνH w - w ∈ hc.VtSub hS.model t := by
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj w
  have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := (sec7_mem_Wt_iff_perp hc hS ψ hW hxQ).mpr hw
  have hcomm := sec7_N_comm_W_le_V h52a hA hc hs ν hν x hxW
  rw [sec7Op_sub_comm hc hS hνH hxQ]
  exact (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hcomm (sec7_comm_mem_Q hc hνH.1 hxQ))

end

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {n : ℕ} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b₀ : M₀.E}
  (hc : Ctx M Q Z B) (hS : IsTensorSetup hc n M₀ ρ b₀) {t : G}

include hc hS

theorem sec7_equiv_wild (ht : t ∈ LB M Q B) {n' : ℕ} (hs : Sec7Hyp hc n' t) {v : G}
    (hvH : v ∈ H0 M Z) (hvt : ⁅v, t⁆ ∈ Q)
    (hvV : ∀ x ∈ Vt M (LB M Q B) B Z t, ⁅v, x⁆ ∈ Z)
    (hker' : ∀ ν : G, ν ∈ hc.CN t → ∀ hνH : ν ∈ H0 M Z, ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      sec7Op hc hS hνH w - w ∈ hc.VtSub hS.model t)
    (hvW : ∀ w ∈ M₀.B.orthogonal (hc.VtSub hS.model t),
      sec7Op hc hS hvH w ∈ M₀.B.orthogonal (hc.VtSub hS.model t))
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) {w : M₀.E}
    (hw : w ∈ M₀.B.orthogonal (hc.VtSub hS.model t)) :
    sec7Op hc hS (hc.Rt_le_H0 t hr) (sec7Op hc hS hvH w - w) -
      (sec7Op hc hS hvH (sec7Op hc hS (hc.Rt_le_H0 t hr) w) -
        sec7Op hc hS (hc.Rt_le_H0 t hr) w) ∈ hc.VtSub hS.model t := by
  have hrH : r ∈ H0 M Z := hc.Rt_le_H0 t hr
  have hcCN : ⁅r, v⁆ ∈ hc.CN t := comm_mem_CN_of_vanish hc hs hvH.1 hvt hvV hr
  have hcH : ⁅r, v⁆ ∈ H0 M Z := by
    rw [commutatorElement_def]
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).mul_mem hrH hvH) ((H0 M Z).inv_mem hrH))
      ((H0 M Z).inv_mem hvH)
  have hvrH : v * r ∈ H0 M Z := (H0 M Z).mul_mem hvH hrH
  have hrvH : r * v ∈ H0 M Z := (H0 M Z).mul_mem hrH hvH
  have hcvrH : ⁅r, v⁆ * (v * r) ∈ H0 M Z := (H0 M Z).mul_mem hcH hvrH
  have h1 := sec7Op_mul hc hS hrH hvH hrvH
  have h2 := sec7Op_mul hc hS hcH hvrH hcvrH
  have h3 := sec7Op_mul hc hS hvH hrH hvrH
  have h4 := sec7Op_congr hc hS hrvH hcvrH (by simp only [commutatorElement_def]; group)
  have key : sec7Op hc hS hrH (sec7Op hc hS hvH w) =
      sec7Op hc hS hcH (sec7Op hc hS hvH (sec7Op hc hS hrH w)) := by
    have e1 := LinearMap.congr_fun h1 w
    have e2 := LinearMap.congr_fun h2 w
    have e3 := LinearMap.congr_fun h3 w
    rw [h4] at e1
    rw [Module.End.mul_apply] at e1 e2 e3
    rw [← e1, e2, e3]
  have hw1 : sec7Op hc hS hvH (sec7Op hc hS hrH w) ∈ M₀.B.orthogonal (hc.VtSub hS.model t) :=
    hvW _ (sec7_op_mem_perp hc hS ht hr hw)
  have e : sec7Op hc hS hrH (sec7Op hc hS hvH w - w) -
      (sec7Op hc hS hvH (sec7Op hc hS hrH w) - sec7Op hc hS hrH w) =
      sec7Op hc hS hcH (sec7Op hc hS hvH (sec7Op hc hS hrH w)) -
        sec7Op hc hS hvH (sec7Op hc hS hrH w) := by
    rw [map_sub, key]
    abel
  rw [e]
  exact hker' _ hcCN hcH _ hw1

end

end CFSG.RankThree.GF2n.Stroth80
