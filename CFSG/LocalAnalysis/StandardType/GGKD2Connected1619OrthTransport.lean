module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615

private lemma ltromt_congr_conj {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (y : H) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr, MulAut.conj_apply, map_mul]

private lemma ltromt_quotInner_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (C : Subgroup H) (β : MulAut H) (β' : MulAut H') (hβ : MulAut.congr e β = β') :
    QuotientInner (C.map e.toMonoidHom) β' → QuotientInner C β := by
  intro hQI
  obtain ⟨z', hz'⟩ := hQI
  let φ : ↥C ≃* ↥(C.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
  let Φ : ↥C ⧸ Subgroup.center ↥C ≃*
      ↥(C.map e.toMonoidHom) ⧸ Subgroup.center ↥(C.map e.toMonoidHom) :=
    CFSG.StandardType.centerQuotCongr φ
  refine ⟨Φ.symm z', ?_⟩
  intro c c' hcc'
  apply Φ.injective
  dsimp only [Φ]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [CFSG.StandardType.centerQuotCongr_mk φ c, CFSG.StandardType.centerQuotCongr_mk φ c']
  exact hz' (φ c) (φ c') (by
    change β' (e (c : H)) = e (c' : H)
    rw [← hβ]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hcc'])

theorem classicalModelAction_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (h : ClassicalModelAction H') : ClassicalModelAction H := by
  intro x hx1 hx3 C hC hlab y hxy hyC
  have hxne : e x ≠ 1 := by
    intro h1
    exact hx1 (e.injective (by rw [h1, map_one]))
  have hxpow : (e x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hmap : (Subgroup.centralizer ({x} : Set H)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H') := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      change e x * e w = e w * e x
      rw [← map_mul, ← map_mul, hw x (Set.mem_singleton x)]
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e x) (Set.mem_singleton (e x))
  have hC' : CFSG.Assembly.IsComponentOf (C.map e.toMonoidHom)
      (Subgroup.centralizer ({e x} : Set H')) := by
    rw [← hmap]
    exact CFSG.StandardType.isComponentOf_map_mulEquiv e hC
  have hlab' : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥(C.map e.toMonoidHom) ⧸ Subgroup.center ↥(C.map e.toMonoidHom)) :=
    CFSG.StandardType.ggHasLabel_quotCenter_of_mulEquiv
      (Subgroup.equivMapOfInjective C e.toMonoidHom e.injective) hlab
  have hcomm' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  have hpres' : ∀ c ∈ C.map e.toMonoidHom, MulAut.conj (e y) c ∈ C.map e.toMonoidHom := by
    rintro c ⟨w, hw, rfl⟩
    change MulAut.conj (e y) (e w) ∈ C.map e.toMonoidHom
    simpa only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.coe_toMonoidHom] using
      Subgroup.mem_map_of_mem e.toMonoidHom (hyC w hw)
  exact ltromt_quotInner_map e C (MulAut.conj y) (MulAut.conj (e y)) (ltromt_congr_conj e y)
    (h (e x) hxne hxpow (C.map e.toMonoidHom) hC' hlab' (e y) hcomm' hpres')

end S2MathAs3_1619Final

end
