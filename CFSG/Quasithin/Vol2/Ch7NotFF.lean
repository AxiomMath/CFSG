module

public import CFSG.Quasithin.Vol2.Ch7Sp4PairA6
public import CFSG.Quasithin.Vol2.Ch7SL3Pair
public import CFSG.Quasithin.Background.HSp4AlphaBridge
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem exists_twist (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) (htw : IsTwistedPair T L I) :
    ∃ φ : MulAut (IntMod (fsuV T I) hV),
      φ ∈ Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV))) ∧
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
  refine ⟨φ, autI_top_le_normalizer hV hNM (convI_mem_autI hV (Subgroup.mem_top _) htN), ?_,
    ?_, ?_⟩
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

omit [Finite G] in
theorem isFFModule_of_concl701FF [IsMulCommutative ↥(fsuV T I)] (h : Concl701FF T L I) :
    IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn (fsuL0 T L) (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
  obtain ⟨A, hAX, hA1, hAel, hmax⟩ := h
  refine ⟨A, hAX, hA1, hAel, ?_⟩
  have h1 := hmax ⊥ bot_le
  have hbot : fixV (⊥ : Subgroup (MulAut ↥(fsuV T I))) = ⊤ := by
    rw [eq_top_iff]
    intro v _ x hx
    rw [Subgroup.mem_bot.mp hx]
    rfl
  rwa [Subgroup.card_bot, one_mul, hbot, Subgroup.card_top] at h1

theorem not_concl701FF_Sp4Pair (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711Sp4Pair T L I → ¬ Concl701FF T L I := by
  intro _ hrow hFF
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hFF' : IsFFModule (V := IntMod (fsuV T I) hV)
      (Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV)))) :=
    isFFModule_of_concl701FF hFF
  rcases hnat with ⟨n, hn2, hn⟩ | h6
  · have hL : BinaryNaturalSp4 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I)
        ⊥ n := hn
    exact (Sp4.H7_Sp4Pair_alpha hn2 hL hφN hinf hsup hniso le_rfl).2.2 hFF'
  · have hL : AlternatingNatural (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))
        (intSub hV I) ⊥ 6 := h6
    exact (Sp4A6.H7_A6Pair_alpha hL hφN hinf hsup hniso le_rfl).2.2 hFF'

theorem not_concl701FF_SL3Pair (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) {n : ℕ} (hn2 : 2 ≤ n) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I n → ¬ Concl701FF T L I := by
  intro _ hrow hFF
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hFF' : IsFFModule (V := IntMod (fsuV T I) hV)
      (Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV)))) :=
    isFFModule_of_concl701FF hFF
  have hL : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 n := hnat
  have hF := (SL3Pair.H4_1_SL3Pair hn2 hL hφN hinf hsup hniso Subgroup.le_normalizer
    le_rfl).2.1
  exact not_isFFModule_of_not_isFOneModule (isPGroup_of_isElemAbelian_two hV) hF hFF'

end CFSG.Quasithin.H13
