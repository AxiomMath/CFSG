module

public import CFSG.Monster.GMS.S365Embed
public import CFSG.Monster.GMS.S365Lines

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_embedded
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hU : Co1FourU)
    {x y t : G} (hl : IsLineTriple a x y) (he : IsEightExt x y t) (h4 : twoBCount z₀ x y t = 4) :
    ∃ q w, w ∈ cosetSet x y t ∧ Embedded a z₀ q x y w := by
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  obtain ⟨w, hw, hwc, hxw, hyw, hxQ, hyQ, hxyQ⟩ := exists_pivot_four I hG hl he h4
  obtain ⟨Lw⟩ := exists_leechSystem_of_isConj hG hw
  have hxC : x ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxw
  have hyC : y ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hyw
  obtain ⟨q, hq, hqw, hqQ, hxq, hyq, hwq⟩ :=
    exists_embed I hG hU hw hl hK.comm hxC hyC hxQ hyQ hxyQ
  have hxyw : x * y * w = w * (x * y) :=
    ((show Commute x w from hxw).mul_left (show Commute y w from hyw)).eq
  have hz : ∀ u : G, u ∈ leechQ w → w⁻¹ * u ∈ leechQ w := fun u hu =>
    mul_mem (inv_mem Lw.z_mem) hu
  refine ⟨q, w, hwc, ⟨hl, hq, hxq, hyq, hwq, hw, hqw.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (isConj_mul_iff I hG hw hl.1 hxw).2 hxQ
  · exact (isConj_mul_iff I hG hw hl.2.1 hyw).2 hyQ
  · rw [mul_assoc]
    exact (isConj_mul_iff I hG hw hl.2.2 hxyw).2 hxyQ
  · intro hh
    apply hxQ
    have : x = w⁻¹ * q := by rw [← hh]; group
    rw [this]
    exact hz q hqQ
  · intro hh
    apply hyQ
    have : y = w⁻¹ * q := by
      have : w * y = q := hh
      rw [← this]
      group
    rw [this]
    exact hz q hqQ
  · intro hh
    apply hxyQ
    have : x * y = w⁻¹ * q := by rw [← hh]; group
    rw [this]
    exact hz q hqQ

theorem eightGroupLinesFour_of_co1
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hU : Co1FourU) (hT : Co1FourT) : EightGroupLinesFour a z₀ := by
  intro x y t x' y' t' hl he hl' he' h4 h4'
  have hK := isKlein_of_isLineTriple hG.1.1 hl
  have hK' := isKlein_of_isLineTriple hG.1.1 hl'
  obtain ⟨q, w, hwc, E⟩ := exists_embedded I hG hU hl he h4
  obtain ⟨q', w', hwc', E'⟩ := exists_embedded I hG hU hl' he' h4'
  obtain ⟨h₀, hh₀⟩ := isConj_iff.1 (E.q2B.symm.trans E'.q2B)
  have E1 := E.conj h₀
  rw [hh₀] at E1
  obtain ⟨g, -, hgx, hgy, hgw⟩ := exists_conj_embedded I hG hT E1 E'
  have hx : g * h₀ * x * (g * h₀)⁻¹ = x' := by
    calc g * h₀ * x * (g * h₀)⁻¹ = g * (h₀ * x * h₀⁻¹) * g⁻¹ := by group
      _ = x' := hgx
  have hy : g * h₀ * y * (g * h₀)⁻¹ = y' := by
    calc g * h₀ * y * (g * h₀)⁻¹ = g * (h₀ * y * h₀⁻¹) * g⁻¹ := by group
      _ = y' := hgy
  refine ⟨g * h₀, hx, hy, ?_⟩
  have hw'' : g * h₀ * w * (g * h₀)⁻¹ ∈ cosetSet x' y' t' := by
    have e : g * h₀ * w * (g * h₀)⁻¹ = g * (h₀ * w * h₀⁻¹) * g⁻¹ := by group
    rw [e, ← hK'.cosetSet_eq hwc']
    exact hgw
  exact conj_mem_cosetSet_of_conj hK hK' hwc hw'' rfl hx hy

theorem eightGroupLines_of_co1
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hU : Co1FourU)
    (hT : Co1FourT) : EightGroupLines a z₀ :=
  eightGroupLines_of_four I hG (eightGroupLinesFour_of_co1 I hG hU hT)

end S365

end CFSG.Monster.GMS
