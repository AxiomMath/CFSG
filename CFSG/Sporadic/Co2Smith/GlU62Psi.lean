module

public import CFSG.Sporadic.Co2Smith.GlU62KerG

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem su6_hom_ext {X : Type*} [Group X] {f g : SU6 →* X}
    (h : ∀ γ ∈ su6D.roots, ∀ x ∈ su6D.rootGroup γ, f x = g x) : f = g := by
  have hle : ⨆ γ ∈ su6D.roots, su6D.rootGroup γ ≤ f.eqLocus g :=
    iSup₂_le fun γ hγ x hx => h γ hγ x hx
  rw [su6_iSup] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

@[expose] noncomputable def psi0
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    (thetaG hz hm).range ≃* G0c :=
  (QuotientGroup.quotientKerEquivRange (thetaG hz hm)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ((ker_thetaG hz hm).trans ker_thetaK.symm)).trans
      ((QuotientGroup.quotientKerEquivRange thetaK).trans (MulEquiv.subgroupCongr range_thetaK)))

theorem psi0_apply
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (x : SU6) :
    (psi0 hz hm ⟨thetaG hz hm x, x, rfl⟩ : K) = thetaK x := by
  have e : (QuotientGroup.quotientKerEquivRange (thetaG hz hm)).symm ⟨thetaG hz hm x, x, rfl⟩ =
      (x : SU6 ⧸ (thetaG hz hm).ker) :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext rfl)
  rw [psi0, MulEquiv.trans_apply, e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  rfl

theorem psiE_mem_range
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {y : K}
    (hy : y ∈ rootSet) : psiE φ ρ y ∈ (thetaG hz hm).range := by
  obtain ⟨r, hr, t, ht, rfl⟩ := hy
  exact ⟨su6Pre r t, thetaG_su6Pre hz hm hr ht⟩

theorem rootSet_mem_G0c
    {y : K} (hy : y ∈ rootSet) :
    y ∈ G0c := by
  obtain ⟨r, hr, t, ht, rfl⟩ := hy
  exact xRootK_mem_G0c_lt hr ht

theorem psi0_psiE
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {y : K} (hy : y ∈ rootSet) :
    (psi0 hz hm ⟨psiE φ ρ y, psiE_mem_range hz hm hy⟩ : K) = y := by
  obtain ⟨r, hr, t, ht, rfl⟩ := hy
  have e : (⟨psiE φ ρ (xRootK r t), psiE_mem_range hz hm ⟨r, hr, t, ht, rfl⟩⟩ :
      (thetaG hz hm).range) = ⟨thetaG hz hm (su6Pre r t), su6Pre r t, rfl⟩ :=
    Subtype.ext (thetaG_su6Pre hz hm hr ht).symm
  rw [e, psi0_apply, thetaK_su6Pre hr ht]

theorem psi0_symm_root
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {y : K}
    (hy : y ∈ rootSet) : ((psi0 hz hm).symm ⟨y, rootSet_mem_G0c hy⟩ : G) = psiE φ ρ y := by
  have : (psi0 hz hm).symm ⟨y, rootSet_mem_G0c hy⟩ = ⟨psiE φ ρ y, psiE_mem_range hz hm hy⟩ :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext (psi0_psiE hz hm hy).symm)
  rw [this]

theorem psi0_symm_mul
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {a b : K}
    (ha : a ∈ G0c) (hb : b ∈ G0c) :
    ((psi0 hz hm).symm ⟨a * b, G0c.mul_mem ha hb⟩ : G) =
      ((psi0 hz hm).symm ⟨a, ha⟩ : G) * ((psi0 hz hm).symm ⟨b, hb⟩ : G) := by
  rw [show (⟨a * b, G0c.mul_mem ha hb⟩ : G0c) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
  rfl

theorem psi0_symm_eq_rhoK
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {g : K}
    (hg : g ∈ G0c) (hT : Transp φ ρ g) : ((psi0 hz hm).symm ⟨g, hg⟩ : G) = rhoK ρ g := by
  set p := ((psi0 hz hm).symm ⟨g, hg⟩ : G)
  have hc : (rhoK ρ g)⁻¹ * p = 1 := by
    refine eq_one_of_comm_psiE hz hm fun r hr t ht => ?_
    have hy : xRootK r t ∈ rootSet := ⟨r, hr, t, ht, rfl⟩
    have hy' := hT.1 _ hy
    have e1 : p * psiE φ ρ (xRootK r t) * p⁻¹ = psiE φ ρ (g * xRootK r t * g⁻¹) := by
      rw [← psi0_symm_root hz hm hy, ← psi0_symm_root hz hm hy', show p = ((psi0 hz hm).symm
        ⟨g, hg⟩ : G) from rfl, ← Subgroup.coe_inv, ← map_inv, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, ← map_mul, ← map_mul]
      rfl
    have e2 := hT.2 _ hy
    rw [← e1] at e2
    calc (rhoK ρ g)⁻¹ * p * psiE φ ρ (xRootK r t)
        = (rhoK ρ g)⁻¹ * (p * psiE φ ρ (xRootK r t) * p⁻¹) * p := by group
      _ = (rhoK ρ g)⁻¹ * (rhoK ρ g * psiE φ ρ (xRootK r t) * (rhoK ρ g)⁻¹) * p := by rw [e2]
      _ = psiE φ ρ (xRootK r t) * ((rhoK ρ g)⁻¹ * p) := by group
  exact (inv_mul_eq_one.1 hc).symm

theorem glD1hWord_mem_glG0Words : Native.glD1hWord ++ [10] ∈ Native.glG0Words := by
  decide +kernel

theorem δ1hK_mul_γ3K_mem_G0c : δ1hK * γ3K ∈ G0c := by
  rw [show δ1hK * γ3K = glE (Native.glD1hWord ++ [10]) by rw [glE_append]; rfl]
  exact Subgroup.subset_closure ⟨_, glD1hWord_mem_glG0Words, rfl⟩

theorem δ1hK_not_mem_G0c :
    δ1hK ∉ G0c := by
  intro h
  apply γ3K_not_mem_G0c
  have := G0c.mul_mem (G0c.inv_mem h) δ1hK_mul_γ3K_mem_G0c
  rwa [inv_mul_cancel_left] at this

theorem transp_δ1hK
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : Transp φ ρ δ1hK :=
  transp_d1 (d1Core_holds hz hm) (transp_w1 (w1Levi_holds hz hm)) (transp_w2 hm)

theorem psi0_conj
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (x : SU6) :
    ∃ h : rhoK ρ δ1hK * thetaG hz hm x * (rhoK ρ δ1hK)⁻¹ ∈ (thetaG hz hm).range,
      (psi0 hz hm ⟨_, h⟩ : K) = δ1hK * thetaK x * δ1hK := by
  set d := rhoK ρ δ1hK
  have hT := transp_δ1hK hz hm
  set θ1 : SU6 →* G := (MulAut.conj d).toMonoidHom.comp (thetaG hz hm) with hθ1
  have hθ1x : ∀ x, θ1 x = d * thetaG hz hm x * d⁻¹ := fun x => rfl
  have hroot : ∀ γ ∈ su6D.roots, ∀ x ∈ su6D.rootGroup γ,
      θ1 x = psiE φ ρ (δ1hK * thetaK x * δ1hK) ∧ thetaK x ∈ rootSet := by
    intro γ hγ x hx
    obtain ⟨r, rfl⟩ := (mem_su6D_roots_iff' γ).1 hγ
    have hy : thetaK x ∈ rootSet := by
      rw [thetaK_root r hx]
      exact ⟨_, r.isLt, _, (su6Entry r x).code.isLt, rfl⟩
    refine ⟨?_, hy⟩
    rw [hθ1x, thetaG_root hz hm ((mem_su6D_roots_iff' _).2 ⟨r, rfl⟩) ⟨x, hx⟩, hT.2 _ hy,
      δ1hK_inv_eq_self]
  have hle : θ1.range ≤ (thetaG hz hm).range := range_le_of_roots θ1 fun γ hγ x hx => by
    rw [(hroot γ hγ x hx).1]
    exact psiE_mem_range hz hm (by
      have := hT.1 _ (hroot γ hγ x hx).2
      rwa [δ1hK_inv_eq_self] at this)
  set F : SU6 →* K := G0c.subtype.comp ((psi0 hz hm).toMonoidHom.comp
    (θ1.codRestrict (thetaG hz hm).range fun x => hle ⟨x, rfl⟩))
  have hF : F = (MulAut.conj δ1hK).toMonoidHom.comp thetaK := by
    refine su6_hom_ext fun γ hγ x hx => ?_
    have hy := (hroot γ hγ x hx).2
    have hy' : δ1hK * thetaK x * δ1hK ∈ rootSet := by
      have := hT.1 _ hy
      rwa [δ1hK_inv_eq_self] at this
    show (psi0 hz hm ⟨θ1 x, hle ⟨x, rfl⟩⟩ : K) = δ1hK * thetaK x * δ1hK⁻¹
    have e : (⟨θ1 x, hle ⟨x, rfl⟩⟩ : (thetaG hz hm).range) =
        ⟨psiE φ ρ (δ1hK * thetaK x * δ1hK), psiE_mem_range hz hm hy'⟩ :=
      Subtype.ext (hroot γ hγ x hx).1
    rw [e, psi0_psiE hz hm hy', δ1hK_inv_eq_self]
  have hmem : d * thetaG hz hm x * d⁻¹ ∈ (thetaG hz hm).range := hle ⟨x, rfl⟩
  refine ⟨hmem, ?_⟩
  have key : F x = δ1hK * thetaK x * δ1hK⁻¹ := DFunLike.congr_fun hF x
  rw [δ1hK_inv_eq_self] at key
  exact key

end CFSG.Sporadic.Co2Smith
