module

public import CFSG.Monster.Tri.LeechModelFix
public import CFSG.Monster.Tri.LeechModelShort
public import CFSG.Monster.Tri.LeechLongMonster
public import CFSG.Monster.Existence.Census.ThreeCosets

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA.Census
  CFSG.Monster.GMS CFSG.YGroups

theorem modTwoEnd_eq_of_mem_cosetR
    {i : ℕ} {p : Pvis}
    (h : (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) ∈ cosetR i) :
    modTwoEnd p.1.2 = modTwoEnd (monoAO i) := by
  have h1 := (mem_cosetR_iff i _).1 h
  rw [piVis_thetaEquiv, piVis_cosetRep] at h1
  have h2 := congrArg opQHom h1
  rw [opQHom_op_mk, opQHom_op_mk] at h2
  exact congrArg (fun u : GLV => (u : Module.End (ZMod 2) L2)) h2

theorem conj_mem_shortClass {g s : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ Gmat) (hs : s ∈ shortClass) :
    g * s * g⁻¹ ∈ shortClass := by
  obtain ⟨h, hh, rfl⟩ := hs
  exact ⟨g * h, mul_mem hg hh, by group⟩

theorem mem_rhoQ_of_mem_shortClass_of_mul_xmat
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (htG : t ∈ Gvis)
    (ht : t ∈ shortClass) (htz : t * xmat ∈ shortClass) : t ∈ rhoQ := by
  by_contra hQ
  set f : Gvis := ⟨t, htG⟩ with hf
  have hff : f * f = 1 := Subtype.ext (mul_self_eq_one_of_mem_shortClass ht)
  obtain ⟨i, hi, k, hk⟩ := CFSG.Monster.Existence.Census.exists_conj_involution_mem_cosetR hff hQ
  obtain ⟨p, hp⟩ := mem_Gvis.1 (k * f * k⁻¹).2
  have hpf : (⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ : Gvis) = k * f * k⁻¹ := Subtype.ext hp
  have hmod : modTwoEnd p.1.2 = modTwoEnd (monoAO i) :=
    modTwoEnd_eq_of_mem_cosetR (by rw [hpf]; exact hk)
  have hkG : (k : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := Hmat_le_Gmat k.2
  have e1 : thetaEquiv p = (k : SpaceB ≃ₗ[ℚ] SpaceB) * t * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := hp
  have hxk : (k : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = xmat :=
    Gvis_conj_xmat k.2
  have hkx : (k : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB) := by
    calc (k : SpaceB ≃ₗ[ℚ] SpaceB) * xmat = (k * xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) * k := by
          group
      _ = xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [hxk]
  have hkx' : (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat = xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by
    calc (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat
        = (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * (xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)) *
            (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by group
      _ = (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * ((k : SpaceB ≃ₗ[ℚ] SpaceB) * xmat) *
            (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by rw [hkx]
      _ = xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by group
  have hT1 : thetaEquiv p ∈ shortClass := by rw [e1]; exact conj_mem_shortClass hkG ht
  have hT2 : thetaEquiv p * xmat ∈ shortClass := by
    have h3 : thetaEquiv p * xmat =
        (k : SpaceB ≃ₗ[ℚ] SpaceB) * (t * xmat) * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by
      rw [e1]
      calc (k : SpaceB ≃ₗ[ℚ] SpaceB) * t * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat
          = (k : SpaceB ≃ₗ[ℚ] SpaceB) * t * ((k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * xmat) := by group
        _ = (k : SpaceB ≃ₗ[ℚ] SpaceB) * t * (xmat * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) := by
            rw [hkx']
        _ = (k : SpaceB ≃ₗ[ℚ] SpaceB) * (t * xmat) * (k : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ := by group
    rw [h3]
    exact conj_mem_shortClass hkG htz
  have hsq : thetaEquiv p * thetaEquiv p = 1 := mul_self_eq_one_of_mem_shortClass hT1
  have hle := trace_theta_add_xmat_le hsq
  rw [trace_eq_of_mem_shortClass hT1, trace_eq_of_mem_shortClass hT2] at hle
  have hfix : (fixShort p.1.2).ncard ≤ 4071 := by
    have : fixShort p.1.2 = fixShort (monoAO i) := by
      unfold fixShort
      rw [hmod]
    rw [this]
    exact ncard_fixShort_monoAO_le hi
  have hfix' : ((fixShort p.1.2).ncard : ℚ) ≤ 4071 := by exact_mod_cast hfix
  linarith

theorem rhoG_comm_xmatG (r : Q) : rhoG r * xmatG = xmatG * rhoG r := by
  have hc : r * zQ = zQ * r := Subgroup.mem_center_iff.1 CFSG.Monster.B.Short.zQ_mem_center r
  have h1 := rhoG_mul zQ r
  have h2 := rhoG_mul r zQ
  rw [hc] at h2
  exact h1.symm.trans h2

theorem exists_rho_of_mem_shortClass
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ shortClass)
    (hc : t * xmat = xmat * t) (htz : t * xmat ∈ shortClass) :
    ∃ r : Q, IsShortCoord (coordOf r) ∧ rhoEquiv r = t := by
  have htG : t ∈ Gvis := by
    have hGm : t ∈ Gmat := by
      obtain ⟨g, hg, rfl⟩ := ht
      exact mul_mem (mul_mem hg tStar_mem_Gmat) (inv_mem hg)
    have h1 : t ∈ Gmat ⊓ Subgroup.centralizer {xmat} :=
      ⟨hGm, Subgroup.mem_centralizer_singleton_iff.2 hc⟩
    rw [Gmat_inf_centralizer_xmat] at h1
    exact h1
  exact exists_short_of_mem_shortClass_of_mem_rhoQ ht
    (mem_rhoQ_of_mem_shortClass_of_mul_xmat htG ht htz)

theorem exists_rho_of_commute
    {a : Gmat} (ha : IsConj tStarG a) (t : ConjVert a)
    (hc : (t : Gmat) * xmatG = xmatG * t) (htz : IsConj a ((t : Gmat) * xmatG)) :
    ∃ r : Q, IsShortCoord (coordOf r) ∧ (t : Gmat) = rhoG r := by
  obtain ⟨r, hr, hrt⟩ := exists_rho_of_mem_shortClass
    (isConj_tStarG_iff.1 (ha.trans t.2)) (congrArg Subtype.val hc)
    (isConj_tStarG_iff.1 (ha.trans htz))
  exact ⟨r, hr, Subtype.ext hrt.symm⟩

theorem exists_lift_of_commonNeighbors
    {a : Gmat} (ha2 : a * a = 1) (ha : IsConj tStarG a)
    {r : Q} (hr : IsShortCoord (coordOf r)) {x : ConjVert a}
    (hx : x ∈ (twoAGraph a).commonNeighbors (rhoVert ha hr)
      (rhoVert ha (isShortCoord_mul_zQ_iff.2 hr))) :
    ∃ s, shortQGraph.Adj r s ∧ (x : Gmat) = rhoG s := by
  obtain ⟨h1, h2⟩ := (SimpleGraph.mem_commonNeighbors _).1 hx
  have hy2 : rhoG r * rhoG r = 1 := by
    have h : r * r = 1 := by
      have := sq_eq_one_of_isShort hr
      rwa [pow_two] at this
    rw [← rhoG_mul, h]
    exact Subtype.ext rhoEquiv_one'
  have hv : ((rhoVert ha (isShortCoord_mul_zQ_iff.2 hr) : ConjVert a) : Gmat) =
      rhoG r * xmatG := (rhoG_mul_xmatG r).symm
  have hz : rhoG r * ((rhoVert ha (isShortCoord_mul_zQ_iff.2 hr) : ConjVert a) : Gmat) =
      xmatG := by
    rw [hv, ← mul_assoc, hy2, one_mul]
  have hxy : rhoG r * (x : Gmat) = x * rhoG r := adj_comm ha2 h1
  have hxv : rhoG r * xmatG * (x : Gmat) = x * (rhoG r * xmatG) := by
    rw [← hv]
    exact adj_comm ha2 h2
  have hxz : (x : Gmat) * xmatG = xmatG * x := by
    rw [← hz, hv]
    calc (x : Gmat) * (rhoG r * (rhoG r * xmatG))
        = (x * rhoG r) * (rhoG r * xmatG) := (mul_assoc _ _ _).symm
      _ = (rhoG r * x) * (rhoG r * xmatG) := by rw [hxy]
      _ = rhoG r * (x * (rhoG r * xmatG)) := mul_assoc _ _ _
      _ = rhoG r * (rhoG r * xmatG * x) := by rw [hxv]
      _ = (rhoG r * (rhoG r * xmatG)) * x := (mul_assoc _ _ _).symm
  have hyz := rhoG_comm_xmatG r
  let u : ConjVert a := ⟨rhoG r * (x : Gmat), h1.2⟩
  have hu_comm : (u : Gmat) * xmatG = xmatG * u := by
    show rhoG r * x * xmatG = xmatG * (rhoG r * x)
    calc rhoG r * (x : Gmat) * xmatG = rhoG r * ((x : Gmat) * xmatG) := mul_assoc _ _ _
      _ = rhoG r * (xmatG * x) := by rw [hxz]
      _ = (rhoG r * xmatG) * x := (mul_assoc _ _ _).symm
      _ = (xmatG * rhoG r) * x := by rw [hyz]
      _ = xmatG * (rhoG r * x) := mul_assoc _ _ _
  have hu_conj : IsConj a ((u : Gmat) * xmatG) := by
    have : (u : Gmat) * xmatG = rhoG r * xmatG * x := by
      show rhoG r * x * xmatG = rhoG r * xmatG * x
      rw [mul_assoc, hxz, ← mul_assoc]
    rw [this, ← hv]
    exact h2.2
  obtain ⟨w, hw, huw⟩ := exists_rho_of_commute ha u hu_comm hu_conj
  have hxq : (x : Gmat) = rhoG (w * r) := by
    rw [rhoG_mul w r]
    have huw' : rhoG r * (x : Gmat) = rhoG w := huw
    calc (x : Gmat) = (rhoG r * rhoG r) * x := by rw [hy2, one_mul]
      _ = rhoG r * (rhoG r * x) := mul_assoc _ _ _
      _ = rhoG r * rhoG w := by rw [huw']
  exact exists_lift_of_mem_rho ha (fun q hq => isShortCoord_of_rhoEquiv_mem_shortClass hq) hr hx
    ⟨w * r, hxq⟩

end CFSG.Monster.Tri.Leech
