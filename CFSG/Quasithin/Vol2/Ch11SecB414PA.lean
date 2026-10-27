module

public import CFSG.Quasithin.Vol2.Ch11SecB414MH

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix

section Parabolic

variable {H : Type} [Group H]

theorem isSylowTwoOf_map (φ : H ≃* H) {S : Subgroup H}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map φ.toMonoidHom) ⊤ := by
  obtain ⟨-, hp, hi⟩ := hS
  refine ⟨le_top, hp.map _, ?_⟩
  have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have h2 : ((S.map φ.toMonoidHom).subgroupOf ⊤).index = (S.map φ.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  rw [h2, Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
  rwa [h1] at hi

theorem map_symm_map (φ : H ≃* H) (K : Subgroup H) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  ext x
  simp

theorem isParabolic2_map (φ : H ≃* H) {Q : Subgroup H} (hQ : IsParabolic2 ⊤ Q) :
    IsParabolic2 ⊤ (Q.map φ.toMonoidHom) := by
  obtain ⟨-, S, hS, hSQ⟩ := hQ
  refine ⟨le_top, S.map φ.toMonoidHom, isSylowTwoOf_map φ hS, ?_⟩
  rintro x ⟨-, hx⟩
  rw [← Subgroup.map_equiv_normalizer_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hSQ ⟨trivial, hy⟩, rfl⟩

theorem isMaxParabolic2_map (φ : H ≃* H) {P : Subgroup H} (hP : IsMaxParabolic2 ⊤ P) :
    IsMaxParabolic2 ⊤ (P.map φ.toMonoidHom) := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  refine ⟨isParabolic2_map φ hpar, fun h => hne ?_, fun Q hQ hQne hPQ => ?_⟩
  · rw [← map_symm_map φ P, h, Subgroup.map_top_of_surjective _ φ.symm.surjective]
  · have h1 : Q.map φ.symm.toMonoidHom = P := by
      refine hmax _ (isParabolic2_map φ.symm hQ) (fun h => hQne ?_) ?_
      · rw [← map_symm_map φ.symm Q, MulEquiv.symm_symm, h,
          Subgroup.map_top_of_surjective _ φ.surjective]
      · rw [← map_symm_map φ P]
        exact Subgroup.map_mono hPQ
    rw [← h1]
    have h2 := map_symm_map φ.symm Q
    rw [MulEquiv.symm_symm] at h2
    exact h2.symm

end Parabolic

section Conj

variable {G : Type} [Group G] {F : Type} [Field F] {Γ V Z : Subgroup G} {k : ℕ}
  {α : ↥Γ →* PGL3 F}

@[expose] def cj (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (c : Matrix (Fin 3) (Fin 3) F) * M * ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem cj_add (c : GL (Fin 3) F) (M N : Matrix (Fin 3) (Fin 3) F) :
    cj c (M + N) = cj c M + cj c N := by
  simp only [cj, Matrix.mul_add, Matrix.add_mul]

theorem cj_zero (c : GL (Fin 3) F) : cj c 0 = 0 := by
  simp only [cj, Matrix.mul_zero, Matrix.zero_mul]

theorem cj_inv_cj (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) : cj c⁻¹ (cj c M) = M := by
  simp only [cj, inv_inv, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one,
    Units.inv_mul_cancel_left]

theorem cj_cj_inv (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) : cj c (cj c⁻¹ M) = M := by
  have h := cj_inv_cj c⁻¹ M
  rwa [inv_inv] at h

theorem trace_cj (c : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) : (cj c M).trace = M.trace := by
  rw [cj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem cj_twAdj (c g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    cj c (twAdj k (c⁻¹ * g * c) M) = twAdj k g (cj c M) := by
  have hdet : ((c⁻¹ * g * c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      (g : Matrix (Fin 3) (Fin 3) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]
  have hinv : (((c⁻¹ * g * c)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((c⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (c : Matrix (Fin 3) (Fin 3) F) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc]
  rw [cj, cj, twAdj, twAdj, hdet, hinv, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
    Units.mul_inv_cancel_left]

@[expose] noncomputable def Model.conjGL (m : Model Γ V Z F k α) (c : GL (Fin 3) F) :
    Model Γ V Z F k ((MulAut.conj (ProjGenLinGroup.mk c)).toMonoidHom.comp α) where
  β :=
    { toFun := fun v => Multiplicative.ofAdd (cj c (Multiplicative.toAdd (m.β v)))
      map_one' := by
        rw [map_one, toAdd_one, cj_zero]
        rfl
      map_mul' := fun v w => by
        rw [map_mul, toAdd_mul, cj_add]
        rfl }
  sl := fun v => by
    show (cj c (Multiplicative.toAdd (m.β v))).trace = 0
    rw [trace_cj, m.sl]
  onto := fun M hM => by
    obtain ⟨v, hv⟩ := m.onto (cj c⁻¹ M) (by rw [trace_cj, hM])
    exact ⟨v, show cj c (Multiplicative.toAdd (m.β v)) = M by rw [hv, cj_cj_inv]⟩
  ker := fun v => by
    rw [← m.ker v]
    show Multiplicative.ofAdd (cj c (Multiplicative.toAdd (m.β v))) = 1 ↔ _
    constructor
    · intro h
      have h1 : cj c (Multiplicative.toAdd (m.β v)) = 0 := congrArg Multiplicative.toAdd h
      have h2 := cj_inv_cj c (Multiplicative.toAdd (m.β v))
      rw [h1, cj_zero] at h2
      exact Multiplicative.toAdd.injective h2.symm
    · intro h
      rw [h, toAdd_one, cj_zero]
      rfl
  act := fun γ u v huv g hg => by
    have hg' : ProjGenLinGroup.mk (c⁻¹ * g * c) = α γ := by
      rw [map_mul, map_mul, map_inv, hg]
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      group
    show cj c (Multiplicative.toAdd (m.β v)) = twAdj k g (cj c (Multiplicative.toAdd (m.β u)))
    rw [m.act γ u v huv _ hg', cj_twAdj]
  normV := m.normV
  le := m.le

end Conj

end CFSG.Quasithin.H13.Ch4.B414.M
