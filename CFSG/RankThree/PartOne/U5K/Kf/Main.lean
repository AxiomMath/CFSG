module

public import CFSG.RankThree.PartOne.U5K.Kf.Ident

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG CFSG.RankThree.PartOne.U5K.Kf
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4

theorem kf1514Five_holds : KF1514Five := by
  intro f p hf hp hp5 hpf H Ē Ā hInnH hĒH hĀĒ hĒD hĒel hĒcard hĀcard hS
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot (u5FieldData f hf) hp hpf
  let Z : Kf.ZetaData (u5FieldData f hf) p := ⟨ζ, hζ, hpf, hp5⟩
  set e := u5Equiv f hf with he
  set θ : MulAut (projSU 5 2 f) ≃* MulAut (primeFormP (u5FieldData f hf)
    (idGram (GaloisField 2 (2 * f)) 5)) := MulAut.congr e with hθ
  have hfinP : Finite (primeFormP (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) :=
    have := (u5FieldData f hf).finite
    finite_primeFormP
  have hZ' : Subgroup.center (primeFormP (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) =
      ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hz' : e.symm z ∈ Subgroup.center (projSU 5 2 f) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (e y)
    rw [u5_center_eq_bot f hf, Subgroup.mem_bot] at hz'
    simpa using congrArg e hz'
  have hInn' : (MulAut.conj : primeFormP (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) →*
      MulAut (primeFormP (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))).range ≤
        H.map θ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    have hy : MulAut.conj y = θ (MulAut.conj (e.symm y)) := by
      have := mulAut_congr_conj e (e.symm y)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    exact ⟨MulAut.conj (e.symm y), hInnH ⟨e.symm y, rfl⟩, hy.symm⟩
  have hD' : Ā.map θ.toMonoidHom ≤ primeFormD (u5FieldData f hf)
      (idGram (GaloisField 2 (2 * f)) 5) := by
    rintro _ ⟨α, hα, rfl⟩
    have hα1 := hĒD (hĀĒ hα)
    have hα' : α ∈ (u5FieldFactor f hf).ker := by rwa [U5Inndiag_eq f hf] at hα1
    have hα2 : MulAut.congr (u5Equiv f hf) α ∈ (primeFormFieldFactor (u5FieldData f hf)
        (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num)
        (by omega)).ker := hα'
    rw [ker_primeFormFieldFactor] at hα2
    exact hα2
  have hAbel : IsElementaryAbelian p ↥Ā := Sec1514Five.isElementaryAbelian_of_le_aux hĒel hĀĒ
  have hel' : IsElementaryAbelian p ↥(Ā.map θ.toMonoidHom) :=
    IsElementaryAbelian.map θ.toMonoidHom
  have hcard' : Nat.card (Ā.map θ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective θ.injective, hĀcard]
  obtain ⟨S, -, hSne, hS2, hSn⟩ := hS
  have hS' : ∃ S' : Subgroup (MulAut (primeFormP (u5FieldData f hf)
      (idGram (GaloisField 2 (2 * f)) 5))), S' ≠ ⊥ ∧ IsPGroup 2 S' ∧
        Ā.map θ.toMonoidHom ≤ Subgroup.normalizer (S' : Set _) := by
    refine ⟨S.map θ.toMonoidHom, fun h0 => hSne ((Subgroup.map_eq_bot_iff_of_injective S
      (f := θ.toMonoidHom) θ.injective).1 h0), hS2.map _, ?_⟩
    exact (Subgroup.map_mono hSn).trans (Subgroup.le_normalizer_map θ.toMonoidHom)
  obtain ⟨T', hT', hA', B', hB'le, hB'card, hB'n⟩ :=
    Z.kf_identity hZ' hInn' hD' hel' hcard' hS'
  set B : Subgroup (MulAut (projSU 5 2 f)) := B'.map θ.symm.toMonoidHom with hB
  have hBθ : B.map θ.toMonoidHom = B' := map_map_symm_equiv θ.symm B'
  obtain ⟨T, hT, hA, hBn⟩ := transport_back θ (H := H) (Ab := Ā) (B := B) (Th := T') hT' hA'
    (by rw [hBθ]; exact hB'n)
  refine ⟨T, hT, hA, B, ?_, ?_, hBn⟩
  · have := Subgroup.map_mono (f := θ.symm.toMonoidHom) hB'le
    rwa [map_map_symm_equiv θ Ā] at this
  · rw [hB, Subgroup.card_map_of_injective θ.symm.injective, hB'card]

end CFSG.RankThree.PartOne.U5K
