module

public import CFSG.Sporadic.Fi24.Local
public import CFSG.Fischer.Uniq.EdgeFixed
public import CFSG.Sporadic.Fi23.Graph

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def starFun
    (f : LocalClass D24 tR) : Fi23.D23 :=
  ⟨fi23EquivJMR ⟨(f : R) * tR, mul_tR_mem_MR f.2⟩, isConj_d_fi23EquivJMR f.2⟩

theorem starFun_val
    (f : LocalClass D24 tR) :
    (starFun f : Fi23.J) = fi23EquivJMR ⟨(f : R) * tR, mul_tR_mem_MR f.2⟩ := rfl

theorem starFun_injective :
    Function.Injective starFun := by
  intro f f' h
  have h1 : (starFun f : Fi23.J) = starFun f' := by rw [h]
  rw [starFun_val, starFun_val] at h1
  have h2 := Subtype.ext_iff.1 (fi23EquivJMR.injective h1)
  exact Subtype.ext (mul_right_cancel h2)

theorem starFun_bijective :
    Function.Bijective starFun := by
  have : Finite (LocalClass D24 tR) := Subtype.finite
  refine starFun_injective.bijective_of_nat_card_le ?_
  rw [card_localClass]
  exact Fi23.card_class_d.le

@[expose] noncomputable def starEquiv :
    LocalClass D24 tR ≃ Fi23.D23 :=
  Equiv.ofBijective starFun starFun_bijective

theorem starEquiv_val
    (f : LocalClass D24 tR) :
    (starEquiv f : Fi23.J) = fi23EquivJMR ⟨(f : R) * tR, mul_tR_mem_MR f.2⟩ := rfl

@[expose] noncomputable def localPoints_tR :
    LocalPoints (pairModel Fi23.pair_J) D24 tR where
  χ := starEquiv
  comm f f' := by
    rw [pairModel_perp, starEquiv_val, starEquiv_val, ← map_mul, ← map_mul,
      fi23EquivJMR.injective.eq_iff]
    constructor
    · intro h
      apply Subtype.ext
      show (f : R) * tR * (f' * tR) = f' * tR * (f * tR)
      rw [mul_tR_mul_mul_tR f'.2, mul_tR_mul_mul_tR f.2, h]
    · intro h
      have h' := Subtype.ext_iff.1 h
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
      have h'' : (f : R) * tR * (f' * tR) = f' * tR * (f * tR) := h'
      rwa [mul_tR_mul_mul_tR f'.2, mul_tR_mul_mul_tR f.2] at h''
  tau f f' h := by
    apply Subtype.ext
    rw [pairModel_tv, starEquiv_val, starEquiv_val, starEquiv_val, ← map_mul, ← map_mul]
    refine congrArg fi23EquivJMR (Subtype.ext ?_)
    show (f : R) * f' * f * tR = (f : R) * tR * (f' * tR) * (f * tR)
    rw [mul_tR_mul_mul_tR f'.2]
    group

theorem localPoints_D24 :
    ∀ x ∈ D24, Nonempty (LocalPoints (pairModel Fi23.pair_J) D24 x) :=
  nonempty_localPoints_of_mem pair_R tR_mem_D24 localPoints_tR

theorem exists_commute_D24
    (hPF : PolarFacts) {t : R} (ht : t * t = 1) :
    ∃ x ∈ D24, t * x = x * t :=
  exists_commute_of_involution pair_R Fi23.pair_J Fi22.pair_D Fi22.hasFixedPointProperty_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ht

theorem mem_D24_of_mul_tR
    {t : R} (h : t * tR ∈ MR)
    (hc : IsConj Fi23.d (fi23EquivJMR ⟨t * tR, h⟩)) : t ∈ D24 := by
  obtain ⟨f, hf⟩ := starEquiv.surjective ⟨_, hc⟩
  have h1 : (starEquiv f : Fi23.J) = fi23EquivJMR ⟨t * tR, h⟩ := by rw [hf]
  rw [starEquiv_val] at h1
  have h2 := Subtype.ext_iff.1 (fi23EquivJMR.injective h1)
  rw [← mul_right_cancel h2]
  exact f.2.1

theorem pair_eq_D24
    (hPF : PolarFacts) (E : Set R) (hE : Pair R E) : E = D24 := by
  obtain ⟨e, rfl⟩ := hE.2.1
  have he : e ∈ {x : R | IsConj e x} := IsConj.refl e
  have he2 : e * e = 1 := Pair.mul_self hE he
  obtain ⟨x, hx, hex⟩ := exists_commute_D24 hPF he2
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj pair_R hx tR_mem_D24)
  set t := g * e * g⁻¹ with htdef
  have htE : IsConj e t := isConj_iff.2 ⟨g, rfl⟩
  have htmem : t ∈ {y : R | IsConj e y} := htE
  have htc : t * tR = tR * t := by
    rw [← hg, htdef]
    calc g * e * g⁻¹ * (g * x * g⁻¹) = g * (e * x) * g⁻¹ := by group
      _ = g * (x * e) * g⁻¹ := by rw [hex]
      _ = g * x * g⁻¹ * (g * e * g⁻¹) := by group
  have htt : t * t = 1 := Pair.mul_self hE htmem
  have key : t ∈ D24 → {y : R | IsConj e y} = D24 := by
    intro htD
    have heT : IsConj e tR := htE.trans (htD : IsConj tR t).symm
    ext y
    exact ⟨fun hy => heT.symm.trans hy, fun hy => heT.trans hy⟩
  have htJ : t ∉ JR := by
    intro h
    have hsub : {y : R | IsConj e y} ⊆ (JR : Set R) := by
      intro y hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 (htE.symm.trans hy)
      exact normal_JR.conj_mem _ h c
    have hle : Subgroup.closure {y : R | IsConj e y} ≤ JR := (Subgroup.closure_le _).2 hsub
    rw [hE.2.2.2.2] at hle
    exact tR_not_mem_JR (hle (Subgroup.mem_top _))
  rcases mem_MR_or_of_commute (Subgroup.mem_centralizer_singleton_iff.2 htc) with h | h
  · exact absurd (MR_le_JR h) htJ
  by_cases hm1 : t * tR = 1
  · apply key
    have : t = tR := by
      calc t = t * tR * tR := by rw [mul_assoc, tR_mul_tR, mul_one]
        _ = tR := by rw [hm1, one_mul]
    rw [this]
    exact tR_mem_D24
  apply key
  apply mem_D24_of_mul_tR h
  set m : MR := ⟨t * tR, h⟩
  have hm2 : m * m = 1 := by
    apply Subtype.ext
    show t * tR * (t * tR) = 1
    rw [show t * tR * (t * tR) = t * (tR * t) * tR by group, ← htc,
      show t * (t * tR) * tR = (t * t) * (tR * tR) by group, htt, tR_mul_tR, one_mul]
  have hmne : m ≠ 1 := fun h' => hm1 (by
    have := congrArg (fun z : MR => (z : R)) h'
    rwa [OneMemClass.coe_one] at this)
  apply Fi23.isConj_d_of_orderOf
  · rw [sq, ← map_mul, hm2, map_one]
  · rw [Ne, MulEquiv.map_eq_one_iff]
    exact hmne
  · intro w
    obtain ⟨μ, rfl⟩ := fi23EquivJMR.surjective w
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    have hμ := commute_tR_of_mem_MR μ.2
    have h1 : tR * (μ : R) = (μ : R) * tR := hμ.symm
    have h2 : tR * t = t * tR := htc.symm
    have h3 : tR * (μ : R)⁻¹ = (μ : R)⁻¹ * tR := by
      calc tR * (μ : R)⁻¹ = (μ : R)⁻¹ * ((μ : R) * tR) * (μ : R)⁻¹ := by group
        _ = (μ : R)⁻¹ * (tR * (μ : R)) * (μ : R)⁻¹ := by rw [h1]
        _ = (μ : R)⁻¹ * tR := by group
    have e1 : ((m * (μ * m * μ⁻¹) : MR) : R) = t * ((μ : R) * t * (μ : R)⁻¹) := by
      show t * tR * ((μ : R) * (t * tR) * (μ : R)⁻¹) = t * ((μ : R) * t * (μ : R)⁻¹)
      calc t * tR * ((μ : R) * (t * tR) * (μ : R)⁻¹)
          = t * (tR * (μ : R)) * t * (tR * (μ : R)⁻¹) := by group
        _ = t * ((μ : R) * tR) * t * ((μ : R)⁻¹ * tR) := by rw [h1, h3]
        _ = t * (μ : R) * (tR * t) * (μ : R)⁻¹ * tR := by group
        _ = t * (μ : R) * (t * tR) * (μ : R)⁻¹ * tR := by rw [h2]
        _ = t * (μ : R) * t * (tR * (μ : R)⁻¹) * tR := by group
        _ = t * (μ : R) * t * ((μ : R)⁻¹ * tR) * tR := by rw [h3]
        _ = t * (μ : R) * t * (μ : R)⁻¹ * (tR * tR) := by group
        _ = t * ((μ : R) * t * (μ : R)⁻¹) := by rw [tR_mul_tR]; group
    rw [e1]
    exact hE.2.2.2.1 t htmem _ (htE.trans (isConj_iff.2 ⟨μ, rfl⟩))

end CFSG.Sporadic.Fi24
