module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HSL3NPrime
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch7SL3Pair

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem exists_twist_mem (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) (htw : IsTwistedPair T L I) :
    ∃ φ ∈ autI hV ⊤,
      intSub hV I ⊓ (intSub hV I).map φ.toMonoidHom = ⊥ ∧
      intSub hV I ⊔ (intSub hV I).map φ.toMonoidHom = ⊤ ∧
      ¬ Pair.IsoMod (autI hV (fsuL0 T L)) (intSub hV I) ((intSub hV I).map φ.toMonoidHom) := by
  obtain ⟨t, htT, hsup, hinf, hniso⟩ := htw
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hTV (T.inv_mem htT)) y).mp (hIV hy)
    simpa [mul_assoc] using this
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := hTV (T.inv_mem htT)
  set φ := convI hV ⟨t⁻¹, htN⟩ with hφ
  set V₁ : Subgroup (IntMod (fsuV T I) hV) := intSub hV I with hV₁
  have hmap : V₁.map φ.toMonoidHom = intSub hV (CFSG.conjugate I t) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [mem_intSub]
      change (φ v).val ∈ CFSG.conjugate I t
      rw [hφ, convI_apply_val, mem_conjugate_iff']
      have : t * (t⁻¹ * v.val * t⁻¹⁻¹) * t⁻¹ = v.val := by group
      rw [this]
      exact hv
    · intro hx
      rw [mem_intSub] at hx
      have hx' := mem_conjugate_iff'.mp hx
      refine ⟨IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩, hx', ?_⟩
      apply IntMod.val_injective
      change (φ (IntMod.mk hV ⟨t * x.val * t⁻¹, hIV hx'⟩)).val = x.val
      rw [hφ, convI_apply_val]
      change t⁻¹ * (t * x.val * t⁻¹) * t⁻¹⁻¹ = x.val
      group
  refine ⟨φ, convI_mem_autI hV (Subgroup.mem_top _) htN, ?_, ?_, ?_⟩
  · rw [hmap, eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have : x.val ∈ I ⊓ CFSG.conjugate I t := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact IntMod.val_injective this
  · rw [hmap]
    apply Subgroup.map_injective (valHom_injective hV)
    rw [Subgroup.map_sup, hV₁, map_valHom_intSub hV hIV, map_valHom_intSub hV hItV, hsup,
      map_valHom_top]
  · rw [hmap]
    intro h
    exact hniso (isXSectionIso_of_isoMod hV hIV hItV (le_fsuL0 T L)
      ((le_fsuL0 T L).trans (le_sup_left.trans hN)) h)

theorem stmt7_3_4_nPrime_SL3One : Stmt7_3_4_nPrime_SL3One := by
  intro G _ _ T L I _ hV hN hNM _ hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφM, hinf, hsup, hniso⟩ := exists_twist_mem hV hN htw
  have hL : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  exact SL3One.H4_SL3One_nPrime hL (autI_top_le_normalizer hV hNM hφM) hinf hsup hniso
    (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM) hφM

end CFSG.Quasithin.H13
