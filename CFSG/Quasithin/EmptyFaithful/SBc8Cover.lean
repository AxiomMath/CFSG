module

public import CFSG.Quasithin.EmptyFaithful.SBc8Fix
public import CFSG.Quasithin.EmptyFaithful.SBc8Transfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc8

section Cover

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem cover_of_cases123 (h113 : StageLemma14113) (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hout : Outcome31 T V₁ I L)
    (hcase : IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L ∨
      IsC134Case 3 I (Sgp153 T V₁) L)
    {d : G} (hdY : d ∈ Subgroup.centralizer (Yp : Set G))
    (hdQ : d ∈ Subgroup.centralizer (blockU L : Set G))
    (hcomm : ⁅L, Subgroup.zpowers d⁆ ≤ centerOf (blockU L)) :
    d ∈ Subgroup.centralizer (L : Set G) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hF : Facts15325 T Mc M V₁ V₂ Yp I := c25.facts
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hLc : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c25.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hSM : Sgp153 T V₁ ≤ M := inf_le_right.trans c.c29.norm_le
  have hQeq : blockU L = c134Q I L := blockU_eq_c134Q c
  have hW : centerOf (blockU L) ⊓ Subgroup.centralizer (Yp : Set G) = ⊥ := by
    rw [hQeq]
    exact centerOf_inf_centralizer_eq_bot h113 c hout hcase
  set W : Subgroup G := centerOf (blockU L) with hWdef
  have hQP : blockU L ≤ pCoreOf 2 L :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_normalizer_pCoreOf 2 L)
  have hLQ : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (pCoreOf 2 L) L
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => S153D.conj_mem_centerOf (hLQ hx) hy, fun hy => ?_⟩
    have := S153D.conj_mem_centerOf (hLQ (L.inv_mem hx)) hy
    simpa [mul_assoc] using this
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  have hW2 : IsPGroup 2 ↥W := (pCoreOf_isPGroup 2 L).to_le (inf_le_left.trans hQP)
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := B6.isSylowTwoOf_inf_normal hsyl hLI hIL
  have hodd : ¬ 2 ∣ (M ⊓ L).relIndex L := fun h2 =>
    hQsyl.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left L (inf_le_inf_right L hSM)))
  have hdW : ∀ w ∈ W, d * w * d⁻¹ = w := fun w hw => by
    have := Subgroup.mem_centralizer_iff.mp hdQ w hw.1
    calc d * w * d⁻¹ = (w * d) * d⁻¹ := by rw [this]
      _ = w := by group
  have hd : ∀ l ∈ L, l * d * l⁻¹ * d⁻¹ ∈ W := fun l hl => by
    have := hcomm (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers d))
    rwa [commutatorElement_def] at this
  have hMIYp : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := by
    rw [← hF.norm_eq]
    exact inf_le_right
  have hP : ∀ p ∈ M ⊓ L, p * d * p⁻¹ * d⁻¹ = 1 := by
    intro p hp
    have hpI : p ∈ M ⊓ I := ⟨hp.1, hLI hp.2⟩
    have hδW : p * d * p⁻¹ * d⁻¹ ∈ W := hd p hp.2
    have hδC : p * d * p⁻¹ * d⁻¹ ∈ Subgroup.centralizer (Yp : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy2 : p⁻¹ * y * p ∈ Yp := by
        have := (Subgroup.mem_normalizer_iff.mp (hMIYp ((M ⊓ I).inv_mem hpI)) y).mp hy
        simpa using this
      have hdy : y * d = d * y := Subgroup.mem_centralizer_iff.mp hdY y hy
      have hdy2 : (p⁻¹ * y * p) * d = d * (p⁻¹ * y * p) :=
        Subgroup.mem_centralizer_iff.mp hdY _ hy2
      calc y * (p * d * p⁻¹ * d⁻¹)
          = p * ((p⁻¹ * y * p) * d) * p⁻¹ * d⁻¹ := by group
        _ = p * (d * (p⁻¹ * y * p)) * p⁻¹ * d⁻¹ := by rw [hdy2]
        _ = p * d * p⁻¹ * (y * d⁻¹) := by group
        _ = p * d * p⁻¹ * (d⁻¹ * y) := by
          have : y * d⁻¹ = d⁻¹ * y := by
            have h1 : d⁻¹ * (y * d) * d⁻¹ = d⁻¹ * (d * y) * d⁻¹ := by rw [hdy]
            exact (by simpa [mul_assoc] using h1 : d⁻¹ * y = y * d⁻¹).symm
          rw [this]
        _ = (p * d * p⁻¹ * d⁻¹) * y := by group
    have : p * d * p⁻¹ * d⁻¹ ∈ W ⊓ Subgroup.centralizer (Yp : Set G) := ⟨hδW, hδC⟩
    rw [hW, Subgroup.mem_bot] at this
    exact this
  obtain ⟨m, hmW, hm⟩ := exists_mul_centralizer_of_cocycle hLW hWc hW2 (inf_le_right : M ⊓ L ≤ L)
    hodd hdW hd hP
  have hmC : m ∈ Subgroup.centralizer (Yp : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyd : y * d = d * y := Subgroup.mem_centralizer_iff.mp hdY y hy
    have h1 := hm y (hYL hy)
    have h2 : y * m⁻¹ * y⁻¹ = m⁻¹ := by
      have h3 : y * (d * m⁻¹) * y⁻¹ = (y * d * y⁻¹) * (y * m⁻¹ * y⁻¹) := by group
      have h4 : y * d * y⁻¹ = d := by
        calc y * d * y⁻¹ = (d * y) * y⁻¹ := by rw [hyd]
          _ = d := by group
      rw [h3, h4] at h1
      exact mul_left_cancel h1
    have h5 : y * m * y⁻¹ = m := by
      have := congrArg Inv.inv h2
      simpa [mul_assoc] using this
    calc y * m = (y * m * y⁻¹) * y := by group
      _ = m * y := by rw [h5]
  have hm1 : m = 1 := by
    have : m ∈ W ⊓ Subgroup.centralizer (Yp : Set G) := ⟨hmW, hmC⟩
    rw [hW, Subgroup.mem_bot] at this
    exact this
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := hm l hl
  rw [hm1] at this
  simp only [inv_one, mul_one] at this
  calc l * d = (l * d * l⁻¹) * l := by group
    _ = d * l := by rw [this]

end Cover

end SBc8

end CFSG.Quasithin
