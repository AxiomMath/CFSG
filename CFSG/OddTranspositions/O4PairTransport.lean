module

public import CFSG.OddTranspositions.F25Group
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Walter.PSL2Facts.FieldAut
import all CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.GroupTheory.InternalSemidirectEquiv

public section

noncomputable section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

local instance factPrimeFiveTransport : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

noncomputable def ringAutConjMulEquiv : (F25t ≃+* F25t) ≃* (K25 ≃+* K25) where
  toFun σ := ringEquiv_F25t.symm.trans (σ.trans ringEquiv_F25t)
  invFun τ := ringEquiv_F25t.trans (τ.trans ringEquiv_F25t.symm)
  left_inv σ := by
    apply RingEquiv.ext
    intro x
    simp [RingEquiv.trans_apply]
  right_inv τ := by
    apply RingEquiv.ext
    intro x
    simp [RingEquiv.trans_apply]
  map_mul' σ τ := by
    apply RingEquiv.ext
    intro x
    simp [RingEquiv.trans_apply, RingAut.mul_apply]

@[simp]
theorem ringAutConjMulEquiv_apply (σ : F25t ≃+* F25t) (x : K25) :
    ringAutConjMulEquiv σ x = ringEquiv_F25t (σ (ringEquiv_F25t.symm x)) := (rfl)

theorem ringAutConjMulEquiv_frob25t : ringAutConjMulEquiv frob25t = frob25 := by
  have hxne : ringAutConjMulEquiv frob25t ≠ 1 := by
    intro h
    exact frob25t_ne_one (ringAutConjMulEquiv.injective (by rw [h, map_one]))
  obtain ⟨y, -, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : K25 ≃+* K25)).mp card_ringAut
  exact (huniq _ hxne).trans (huniq frob25 frob25_ne_one).symm

noncomputable def pslEquiv : PSL2 F25t ≃* PSL2 K25 :=
  CFSG.GorensteinWalter.FieldTransport.projectiveSpecialLinearGroupMulEquiv ringEquiv_F25t

theorem pslEquiv_mk (A : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    pslEquiv (QuotientGroup.mk A) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map ringEquiv_F25t.toRingHom A) := (rfl)

theorem pslEquiv_compat (σ : F25t ≃+* F25t) :
    (psl2FieldAut F25t σ).trans pslEquiv =
      pslEquiv.trans (psl2FieldAut K25 (ringAutConjMulEquiv σ)) := by
  ext y
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  show pslEquiv (psl2FieldAut F25t σ (QuotientGroup.mk A)) =
    psl2FieldAut K25 (ringAutConjMulEquiv σ) (pslEquiv (QuotientGroup.mk A))
  simp only [CFSG.Walter.psl2FieldAut_eq_psl2Map, CFSG.Walter.psl2Map_mk, pslEquiv_mk]
  have h1 : Matrix.SpecialLinearGroup.map ringEquiv_F25t.toRingHom
      (Matrix.SpecialLinearGroup.map σ.toRingHom A) =
      Matrix.SpecialLinearGroup.map (ringEquiv_F25t.toRingHom.comp σ.toRingHom) A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  have h2 : Matrix.SpecialLinearGroup.map (ringAutConjMulEquiv σ).toRingHom
      (Matrix.SpecialLinearGroup.map ringEquiv_F25t.toRingHom A) =
      Matrix.SpecialLinearGroup.map (ringEquiv_F25t.toRingHom.comp σ.toRingHom) A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, ringAutConjMulEquiv_apply]
  rw [h1, h2]

noncomputable def psigmaL2Equiv : PSigmaL2t ≃* PSigmaL225 :=
  SemidirectProduct.congr pslEquiv ringAutConjMulEquiv pslEquiv_compat

theorem psigmaL2Equiv_inl (x : PSL2 F25t) :
    psigmaL2Equiv (SemidirectProduct.inl x) = SemidirectProduct.inl (pslEquiv x) :=
  CFSG.GroupTheory.semidirectProduct_congr_inl pslEquiv ringAutConjMulEquiv pslEquiv_compat x

theorem psigmaL2Equiv_inr (σ : F25t ≃+* F25t) :
    psigmaL2Equiv (SemidirectProduct.inr σ) =
      SemidirectProduct.inr (ringAutConjMulEquiv σ) :=
  CFSG.GroupTheory.semidirectProduct_congr_inr pslEquiv ringAutConjMulEquiv pslEquiv_compat σ

theorem psigmaL2Equiv_inr_frob25t :
    psigmaL2Equiv (SemidirectProduct.inr frob25t : PSigmaL2t) =
      (SemidirectProduct.inr frob25 : PSigmaL225) := by
  rw [psigmaL2Equiv_inr, ringAutConjMulEquiv_frob25t]

theorem mem_class65t_iff (x : PSigmaL2t) :
    x ∈ class65t ↔ IsConj (SemidirectProduct.inr frob25t) x := by
  rw [class65t_eq_conjClasses_carrier, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_comm

theorem mem_class65_iff (x : PSigmaL225) :
    x ∈ class65 ↔ IsConj (SemidirectProduct.inr frob25) x := Iff.rfl

theorem psigmaL2Equiv_image_class65t : psigmaL2Equiv '' class65t = class65 := by
  ext x
  simp only [Set.mem_image, mem_class65t_iff, mem_class65_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hy
    refine isConj_iff.mpr ⟨psigmaL2Equiv g, ?_⟩
    simp only [map_mul, map_inv, psigmaL2Equiv_inr_frob25t]
  · intro hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    refine ⟨psigmaL2Equiv.symm (g * SemidirectProduct.inr frob25 * g⁻¹), ?_, ?_⟩
    · have hs : psigmaL2Equiv.symm (SemidirectProduct.inr frob25) =
          (SemidirectProduct.inr frob25t : PSigmaL2t) := by
        rw [← psigmaL2Equiv_inr_frob25t, MulEquiv.symm_apply_apply]
      simp only [map_mul, map_inv, hs]
      exact isConj_iff.mpr ⟨psigmaL2Equiv.symm g, rfl⟩
    · exact psigmaL2Equiv.apply_symm_apply _

theorem psigmaL2Equiv_conj_iff (g x : PSigmaL2t) :
    Commute (psigmaL2Equiv g) (psigmaL2Equiv x) ↔ Commute g x :=
  ⟨fun h => Commute.of_map (f := psigmaL2Equiv) psigmaL2Equiv.injective h,
    fun h => h.map psigmaL2Equiv⟩

end CFSG.OddTranspositions.QZ
