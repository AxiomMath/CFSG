module

public import CFSG.Sporadic.HNSchreier.SplitExt
public import CFSG.Sporadic.HNSchreier.FALocal
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Matrix Equiv

@[expose] def jR : JH →* RH where
  toFun g := ⟨g, JH_le_RH g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def cR :
    RH := ⟨cU, cU_mem_RH⟩

theorem jR_def
    (g : JH) : jR g = ⟨g, JH_le_RH g.2⟩ := rfl

theorem jR_val
    (g : JH) : ((jR g : RH) : GL (Fin hnsData.d) (ZMod 5)) = g := by rw [jR_def]

theorem cR_val :
    ((cR : RH) : GL (Fin hnsData.d) (ZMod 5)) = cU := by rw [cR]

theorem jR_injective :
    Function.Injective jR := fun a b h => Subtype.ext (by
  have := congrArg Subtype.val h
  rwa [jR_val, jR_val] at this)

theorem cR_mul_self : cR * cR = 1 :=
  Subtype.ext (by rw [Subgroup.coe_mul, cR_val, Subgroup.coe_one, cU_mul_self])

theorem cR_inv :
    cR⁻¹ = cR := inv_eq_of_mul_eq_one_right cR_mul_self

theorem cR_sq :
    cR ^ 2 = 1 := by rw [pow_two, cR_mul_self]

theorem cR_ne_jR
    (g : JH) : cR ≠ jR g := fun h => cU_not_mem (by
  have := congrArg Subtype.val h
  rw [cR_val, jR_val] at this
  rw [this]
  exact g.2)

theorem cR_ne_one :
    cR ≠ 1 := fun h => cR_ne_jR 1 (h.trans (map_one jR).symm)

theorem orderOf_cR :
    orderOf cR = 2 := orderOf_eq_prime cR_sq cR_ne_one

theorem exists_jR_or
    (r : RH) : (∃ g : JH, r = jR g) ∨ ∃ g : JH, r = jR g * cR := by
  rcases (mem_RH_iff r).1 r.2 with h | ⟨g, hg, he⟩
  · exact Or.inl ⟨⟨r, h⟩, Subtype.ext (by rw [jR_val])⟩
  · exact Or.inr ⟨⟨g, hg⟩, Subtype.ext (by rw [Subgroup.coe_mul, jR_val, cR_val]; exact he)⟩

theorem mem_range_jR_iff
    (r : RH) : r ∈ jR.range ↔ (r : GL (Fin hnsData.d) (ZMod 5)) ∈ JH := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [jR_val]
    exact g.2
  · intro h
    exact ⟨⟨r, h⟩, Subtype.ext (by rw [jR_val])⟩

theorem jR_mul_cR_not_mem
    (g : JH) : jR g * cR ∉ jR.range := by
  rintro ⟨h, hh⟩
  apply cR_ne_jR (g⁻¹ * h)
  rw [map_mul, hh, map_inv, inv_mul_cancel_left]

theorem cR_mul_jR
    (g : JH) : cR * jR g = jR (conjC g) * cR := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, jR_val, jR_val, cR_val, conjC_val]
  group

theorem cR_conj_jR
    (g : JH) : cR * jR g * cR⁻¹ = jR (conjC g) := by
  rw [cR_mul_jR, mul_inv_cancel_right]

theorem range_jR_normal :
    jR.range.Normal := by
  refine ⟨fun x hx r => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  rcases exists_jR_or r with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact ⟨h * g * h⁻¹, by rw [map_mul, map_mul, map_inv]⟩
  · refine ⟨h * conjC g * h⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← cR_conj_jR, cR_inv, _root_.mul_inv_rev, cR_inv]
    group

abbrev matR
    (r : RH) : Matrix (Fin 133) (Fin 133) (ZMod 5) := matG r

theorem matR_mul
    (r s : RH) : matR (r * s) = matR r * matR s := by
  rw [matR, matR, matR, Subgroup.coe_mul, matG_mul]

theorem matR_one :
    matR 1 = 1 := by rw [matR, Subgroup.coe_one, matG_one]

theorem matR_jR
    (g : JH) : matR (jR g) = matJ g := by rw [matR, jR_val, matJ_eq_matG]

theorem matR_cR :
    matR cR = matCx := by rw [matR, cR_val, matG_cU]

theorem matCx_vL
    (i : X) : ∃ j : X, matCx *ᵥ vL i = vL j := by
  have := hns_pretransitive
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq JH x0 i
  refine ⟨conjC h • x0, ?_⟩
  rw [← mat_vL, ← mat_vL, vL_x0, matJ_conjC, ← mulVec_mulVec, ← mulVec_mulVec, matCx_fix]

theorem exists_vL
    (r : RH) (i : X) : ∃ j : X, matR r *ᵥ vL i = vL j := by
  rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨g • i, by rw [matR_jR]; exact mat_vL g i⟩
  · obtain ⟨j, hj⟩ := matCx_vL i
    refine ⟨g • j, ?_⟩
    rw [matR_mul, matR_jR, matR_cR, ← mulVec_mulVec, hj, mat_vL]

@[expose] def rSmul
    (r : RH) (i : X) : X := Classical.choose (exists_vL r i)

theorem vL_rSmul
    (r : RH) (i : X) : vL (rSmul r i) = matR r *ᵥ vL i :=
  (Classical.choose_spec (exists_vL r i)).symm

instance rAction :
    MulAction RH X where
  smul := rSmul
  one_smul i := vL_injective (by
    show vL (rSmul 1 i) = vL i
    rw [vL_rSmul, matR_one, one_mulVec])
  mul_smul r s i := vL_injective (by
    show vL (rSmul (r * s) i) = vL (rSmul r (rSmul s i))
    rw [vL_rSmul, vL_rSmul, vL_rSmul, matR_mul, mulVec_mulVec])

theorem rSmul_eq
    (r : RH) (i : X) : r • i = rSmul r i := by rfl

theorem vL_smul
    (r : RH) (i : X) : vL (r • i : X) = matR r *ᵥ vL i := by
  rw [rSmul_eq, vL_rSmul]

theorem jR_smul
    (g : JH) (i : X) : jR g • i = g • i :=
  vL_injective (by rw [vL_smul, matR_jR, mat_vL])

theorem cR_smul_x0 :
    cR • x0 = x0 := vL_injective (by rw [vL_smul, matR_cR, vL_x0, matCx_fix])

theorem faithful_R :
    FaithfulSMul RH X := by
  have hJ := hns_faithful
  have key : ∀ r : RH, (∀ i : X, r • i = i) → r = 1 := by
    intro r hr
    rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · have : g = 1 := eq_of_smul_eq_smul fun i => by rw [← jR_smul, hr, one_smul]
      rw [this, map_one]
    · exfalso
      have hc : ∀ i : X, cR • i = g⁻¹ • i := fun i => by
        have h1 : g • cR • i = i := by
          have := hr i
          rwa [mul_smul, jR_smul] at this
        calc cR • i = g⁻¹ • (g • (cR • i)) := (inv_smul_smul g _).symm
          _ = g⁻¹ • i := by rw [h1]
      have hk : g⁻¹ * g⁻¹ = 1 := eq_of_smul_eq_smul (α := X) fun i => by
        rw [mul_smul, ← hc, ← hc, ← mul_smul, cR_mul_self, one_smul, one_smul]
      have hkk : g⁻¹⁻¹ = g⁻¹ := (inv_eq_of_mul_eq_one_right hk)
      apply conjC_not_inner g⁻¹
      apply MulEquiv.ext
      intro h
      apply eq_of_smul_eq_smul (α := X)
      intro i
      have e1 : (conjC h) • i = cR • (h • (cR • i)) := by
        rw [← jR_smul, ← cR_conj_jR, cR_inv, mul_smul, mul_smul, jR_smul]
      rw [e1, hc, hc, MulAut.conj_apply, hkk, mul_smul, mul_smul]
  refine ⟨fun {r s} hrs => ?_⟩
  have h1 : r⁻¹ * s = 1 := key _ fun i => by rw [mul_smul, ← hrs i, inv_smul_smul]
  rw [inv_mul_eq_one] at h1
  exact h1

noncomputable abbrev permR :
    RH →* Equiv.Perm X := MulAction.toPermHom RH X

theorem permR_apply
    (r : RH) (i : X) : permR r i = r • i := rfl

theorem permR_injective :
    Function.Injective permR := by
  intro r s h
  have := faithful_R
  exact eq_of_smul_eq_smul fun x => by rw [← permR_apply, h, permR_apply]

theorem permR_jR
    (g : JH) : permR (jR g) = permJ g :=
  Equiv.ext fun i => by rw [permR_apply, jR_smul, permJ_apply]

end CFSG.Sporadic.HNOddCore
