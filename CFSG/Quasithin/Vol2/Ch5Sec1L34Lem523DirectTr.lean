module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1

public section

namespace CFSG.Quasithin.H13.Tr523

open CFSG.Quasithin.H13.Abs523

variable {G : Type} [Group G] [Finite G]

@[expose] def conjUt {Z₁ X : Subgroup G} (a : ↥(Subgroup.normalizer (Z₁ : Set G)))
    (ha : (a : G) ∈ Subgroup.normalizer (X : Set G)) :
    MulAut ↥(tildeOf Z₁ X) where
  toFun x := ⟨secMk _ _ a * x.1 * (secMk _ _ a)⁻¹, secMk_conj_mem_secImg ha x.2⟩
  invFun x := ⟨(secMk _ _ a)⁻¹ * x.1 * secMk _ _ a, by
    have hainv : (((a⁻¹ : ↥(Subgroup.normalizer (Z₁ : Set G)))) : G) ∈
        Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.coe_inv]
      exact inv_mem ha
    have h := secMk_conj_mem_secImg hainv x.2
    have e : secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ (a⁻¹) =
        (secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁ a)⁻¹ :=
      map_inv (secMk (Subgroup.normalizer (Z₁ : Set G)) Z₁) a
    rw [e, inv_inv] at h
    exact h⟩
  left_inv x := Subtype.ext (by
    show (secMk _ _ a)⁻¹ * (secMk _ _ a * x.1 * (secMk _ _ a)⁻¹) * secMk _ _ a = x.1
    group)
  right_inv x := Subtype.ext (by
    show secMk _ _ a * ((secMk _ _ a)⁻¹ * x.1 * secMk _ _ a) * (secMk _ _ a)⁻¹ = x.1
    group)
  map_mul' x y := Subtype.ext (by
    show secMk _ _ a * (x.1 * y.1) * (secMk _ _ a)⁻¹ =
      (secMk _ _ a * x.1 * (secMk _ _ a)⁻¹) * (secMk _ _ a * y.1 * (secMk _ _ a)⁻¹)
    group)

theorem conjUt_val {Z₁ X : Subgroup G} {a : ↥(Subgroup.normalizer (Z₁ : Set G))}
    {ha : (a : G) ∈ Subgroup.normalizer (X : Set G)} (x : ↥(tildeOf Z₁ X)) :
    (conjUt a ha x).1 = secMk _ _ a * x.1 * (secMk _ _ a)⁻¹ := by
  show secMk _ _ a * x.1 * (secMk _ _ a)⁻¹ = _
  rfl

theorem conjUt_mul {Z₁ X : Subgroup G} {a b : ↥(Subgroup.normalizer (Z₁ : Set G))}
    {ha : (a : G) ∈ Subgroup.normalizer (X : Set G)}
    {hb : (b : G) ∈ Subgroup.normalizer (X : Set G)}
    (hab : ((a * b : ↥(Subgroup.normalizer (Z₁ : Set G))) : G) ∈ Subgroup.normalizer (X : Set G)) :
    conjUt (a * b) hab = conjUt a ha * conjUt b hb := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjUt_val, MulAut.mul_apply, conjUt_val, conjUt_val]
  rw [map_mul]
  group

end CFSG.Quasithin.H13.Tr523
