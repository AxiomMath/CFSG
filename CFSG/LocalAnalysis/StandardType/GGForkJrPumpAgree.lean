module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLTypeA
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Internal

variable {G : Type} [Group G] [Finite G]

theorem ggReflection_eq_of_agree_mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {Z : Subgroup G}
    {r₁ r₂ : MulAut ↥Bs} (h₁ : GGIsReflection p r₁) (h₂ : GGIsReflection p r₂)
    (hi₁ : r₁ ∈ ggInduced ⊤ Bs) (hi₂ : r₂ ∈ ggInduced ⊤ Bs)
    (hz₁ : ∀ b : ↥Bs, (b : G) ∈ Z → r₁ b = b) (hz₂ : ∀ b : ↥Bs, (b : G) ∈ Z → r₂ b = b)
    (hmod : ∀ b : ↥Bs, ((r₁ b : ↥Bs) : G)⁻¹ * ((r₂ b : ↥Bs) : G) ∈ Z) : r₁ = r₂ := by
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  obtain ⟨x₁, f₁, hf₁x₁, hT₁⟩ := exists_of_ggIsReflection ι h₁
  obtain ⟨x₂, f₂, hf₂x₂, hT₂⟩ := exists_of_ggIsReflection ι h₂
  obtain ⟨hx₁, -⟩ := ne_zero_of_apply_eq_two hp2 hf₁x₁
  obtain ⟨hx₂, hf₂⟩ := ne_zero_of_apply_eq_two hp2 hf₂x₂
  let S : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) {v : V | ∃ b : ↥Bs, (b : G) ∈ Z ∧ ι (Additive.ofMul b) = v}
  have hgen : ∀ b : ↥Bs, (b : G) ∈ Z → ι (Additive.ofMul b) ∈ S := fun b hb =>
    Submodule.subset_span ⟨b, hb, rfl⟩
  have hfix₁ : ∀ v ∈ S, ggLin (p := p) ι r₁ v = v := by
    have hker₁ : ∀ v : V,
        v ∈ LinearMap.ker (LinearMap.id - (ggLin (p := p) ι r₁).toLinearMap) ↔
          ggLin (p := p) ι r₁ v = v := by
      intro v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm]
      exact Iff.rfl
    intro v hv
    have hle : S ≤ LinearMap.ker (LinearMap.id - (ggLin (p := p) ι r₁).toLinearMap) := by
      apply Submodule.span_le.mpr
      rintro g ⟨b, hbZ, rfl⟩
      exact (hker₁ _).mpr ((ggLin_fix_iff (p := p) ι r₁ b).mp (hz₁ b hbZ))
    exact (hker₁ v).mp (hle hv)
  have hf₁S : ∀ v ∈ S, f₁ v = 0 := by
    intro v hv
    have hfix := hfix₁ v hv
    rw [hT₁ v] at hfix
    have hz : f₁ v • x₁ = 0 := sub_eq_self.mp hfix
    rcases smul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hx₁
  have hf₂S : ∀ v ∈ S, f₂ v = 0 := by
    have hker₂ : ∀ v : V,
        v ∈ LinearMap.ker (LinearMap.id - (ggLin (p := p) ι r₂).toLinearMap) ↔
          ggLin (p := p) ι r₂ v = v := by
      intro v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm]
      exact Iff.rfl
    intro v hv
    have hfix : ggLin (p := p) ι r₂ v = v := by
      have hle : S ≤ LinearMap.ker (LinearMap.id - (ggLin (p := p) ι r₂).toLinearMap) := by
        apply Submodule.span_le.mpr
        rintro g ⟨b, hbZ, rfl⟩
        exact (hker₂ _).mpr ((ggLin_fix_iff (p := p) ι r₂ b).mp (hz₂ b hbZ))
      exact (hker₂ v).mp (hle hv)
    rw [hT₂ v] at hfix
    have hz : f₂ v • x₂ = 0 := sub_eq_self.mp hfix
    rcases smul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hx₂
  have hmodS : ∀ v : V, f₁ v • x₁ - f₂ v • x₂ ∈ S := by
    intro v
    set b : ↥Bs := Additive.toMul (ι.symm v) with hb
    have hbι : ι (Additive.ofMul b) = v := by
      rw [hb, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hmem := hgen ((r₁ b)⁻¹ * r₂ b) (hmod b)
    convert hmem using 1
    have e₁ : f₁ v • x₁ = v - ggLin (p := p) ι r₁ v := by rw [hT₁ v]; abel
    have e₂ : f₂ v • x₂ = v - ggLin (p := p) ι r₂ v := by rw [hT₂ v]; abel
    have t₁ : ggLin (p := p) ι r₁ v = ι (Additive.ofMul (r₁ b)) := by
      rw [← hbι, ggLin_apply_ofMul]
    have t₂ : ggLin (p := p) ι r₂ v = ι (Additive.ofMul (r₂ b)) := by
      rw [← hbι, ggLin_apply_ofMul]
    rw [e₁, e₂, t₁, t₂, ofMul_mul, ofMul_inv, map_add, map_neg]
    abel
  have hμ0 : f₂ x₁ ≠ 0 := by
    intro hμzero
    have hzmem : (2 : ZMod p) • x₁ - f₂ x₁ • x₂ ∈ S := by
      have := hmodS x₁
      rwa [hf₁x₁] at this
    rw [hμzero, zero_smul, sub_zero] at hzmem
    have hz₁ : f₁ ((2 : ZMod p) • x₁) = 0 := hf₁S _ hzmem
    rw [map_smul, hf₁x₁, smul_eq_mul] at hz₁
    rcases mul_eq_zero.mp hz₁ with h | h
    · exact zmod_two_ne_zero hp2 h
    · exact zmod_two_ne_zero hp2 h
  have hzmem : (2 : ZMod p) • x₁ - f₂ x₁ • x₂ ∈ S := by
    have := hmodS x₁
    rwa [hf₁x₁] at this
  set z₀ : V := (f₂ x₁)⁻¹ • ((2 : ZMod p) • x₁ - f₂ x₁ • x₂) with hz₀def
  have hz₀ : z₀ ∈ S := by
    rw [hz₀def]
    exact S.smul_mem ((f₂ x₁)⁻¹) hzmem
  have hz₀eval : z₀ = (2 * (f₂ x₁)⁻¹) • x₁ - x₂ := by
    rw [hz₀def, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul,
      mul_comm (f₂ x₁)⁻¹ 2]
  have hc : ∀ v, (f₁ v - 2 * (f₂ x₁)⁻¹ * f₂ v) • x₁ ∈ S := by
    intro v
    have hw : f₁ v • x₁ - f₂ v • x₂ ∈ S := hmodS v
    have hzv : f₂ v • z₀ ∈ S := S.smul_mem (f₂ v) hz₀
    have hsub := S.sub_mem hw hzv
    convert hsub using 1
    rw [hz₀eval]
    simp only [smul_sub, smul_smul]
    module
  have hd : ∀ v, f₁ v = 2 * (f₂ x₁)⁻¹ * f₂ v := by
    intro v
    by_contra hne
    have hc0 : f₁ v - 2 * (f₂ x₁)⁻¹ * f₂ v ≠ 0 := fun h => hne (sub_eq_zero.mp h)
    have hx₁S : x₁ ∈ S := by
      have h := S.smul_mem (f₁ v - 2 * (f₂ x₁)⁻¹ * f₂ v)⁻¹ (hc v)
      rw [inv_smul_smul₀ hc0 x₁] at h
      exact h
    have h2 := hf₁S x₁ hx₁S
    rw [hf₁x₁] at h2
    exact zmod_two_ne_zero hp2 h2
  have hT1T2 : ∀ v, ggLin (p := p) ι r₁ v = ggLin (p := p) ι r₂ v - f₂ v • z₀ := by
    intro v
    rw [hT₁ v, hT₂ v, hd v, hz₀eval]
    simp only [smul_sub, smul_smul]
    module
  have hT1T2' : ∀ v, ggLin (p := p) ι r₁ (ggLin (p := p) ι r₂ v) = v + f₂ v • z₀ := by
    intro v
    have hsq : ggLin (p := p) ι r₂ (ggLin (p := p) ι r₂ v) = v := by
      have h2 : ggLin (p := p) ι r₂ ^ 2 = 1 := by
        rw [← map_pow, h₂.1, map_one]
      have hv := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) h2
      simpa [pow_two, LinearEquiv.mul_apply] using hv
    have hf₂T₂ : f₂ (ggLin (p := p) ι r₂ v) = -f₂ v := by
      rw [hT₂ v, map_sub, map_smul, hf₂x₂, smul_eq_mul]
      ring
    rw [hT1T2 (ggLin (p := p) ι r₂ v), hsq, hf₂T₂, neg_smul, sub_neg_eq_add]
  have hz₀0 : z₀ = 0 := by
    by_contra hz₀ne
    have htrans : GGIsTransvection p (r₁ * r₂) := by
      refine ggIsTransvection_of_apply (p := p) ι (w := z₀) (f := f₂) hz₀ne hf₂
        (hf₂S z₀ hz₀) (fun v => ?_)
      rw [map_mul, LinearEquiv.mul_apply]
      exact hT1T2' v
    exact hNT (r₁ * r₂) (mul_mem_ggInduced hi₁ hi₂) htrans
  have hTT : ggLin (p := p) ι r₁ = ggLin (p := p) ι r₂ := by
    refine LinearEquiv.ext fun v => ?_
    rw [hT1T2 v, hz₀0, smul_zero, sub_zero]
  exact ggLin_injective ι hTT

theorem ggReflection_eq_of_ggHyperplane_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {r s : MulAut ↥Bs} (hr : GGIsReflection p r) (hs : GGIsReflection p s)
    (hrI : r ∈ ggInduced ⊤ Bs) (hsI : s ∈ ggInduced ⊤ Bs)
    (hH : ggHyperplane Bs r = ggHyperplane Bs s) : r = s := by
  have hpair (t : MulAut ↥Bs) (ht : t ^ 2 = 1) (b : ↥Bs) :
      ((b * t b : ↥Bs) : G) ∈ ggHyperplane Bs t := by
    apply (mem_ggHyperplane_iff' _).mpr
    have htb : t (t b) = b := by
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
        congrArg (fun a : MulAut ↥Bs => a b) ht
    rw [map_mul, htb]
    exact hBs.1.is_comm.comm _ _
  refine ggReflection_eq_of_agree_mod hp2 hBs hNT (Z := ggHyperplane Bs r)
    hr hs hrI hsI (fun b hb => (mem_ggHyperplane_iff' b).mp hb) ?_ ?_
  · intro b hb
    exact (mem_ggHyperplane_iff' b).mp (hH ▸ hb)
  · intro b
    have hbr := hpair r hr.1 b
    have hbs : ((b * s b : ↥Bs) : G) ∈ ggHyperplane Bs r := hH.symm ▸ hpair s hs.1 b
    simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
      (ggHyperplane Bs r).mul_mem ((ggHyperplane Bs r).inv_mem hbr) hbs

end Internal

end CFSG.StandardType
