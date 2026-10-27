module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSLAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUTransAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSURoot
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdUnitaryDiag

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (suCongr coe_suCongr)

@[expose] noncomputable def irgUM_conjMulAut {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}
    (A : GL (Fin n) F) (hA : InnerDiagSU.IsJUnitary σ A) :
    MulAut (SU σ n) where
  toFun := InnerDiagSU.conjSU A hA
  invFun := InnerDiagSU.conjSU A⁻¹ hA.inv
  left_inv x := by
    apply Subtype.ext
    rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
    group
  right_inv x := by
    apply Subtype.ext
    rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
    group
  map_mul' := map_mul (InnerDiagSU.conjSU A hA)

theorem irgUM_conjMulAut_apply {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}
    (A : GL (Fin n) F) (hA : InnerDiagSU.IsJUnitary σ A) (x : SU σ n) :
    ((irgUM_conjMulAut A hA x : SU σ n) : GL (Fin n) F) =
      A * (x : GL (Fin n) F) * A⁻¹ :=
  rfl

theorem irgUM_conjMulAut_toMonoidHom_apply {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}
    (A : GL (Fin n) F) (hA : InnerDiagSU.IsJUnitary σ A) (x : SU σ n) :
    (irgUM_conjMulAut A hA).toMonoidHom x = irgUM_conjMulAut A hA x :=
  rfl

theorem irgUM_conjMulAut_eq_conj {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}
    (s : SU σ n) (hs : InnerDiagSU.IsJUnitary σ (s : GL (Fin n) F)) :
    irgUM_conjMulAut (s : GL (Fin n) F) hs = MulAut.conj s := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [irgUM_conjMulAut_apply, MulAut.conj_apply]
  rfl

theorem irgUM_exists_diag_away {F : Type*} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} {n : ℕ} {i₀ : Fin n} (hi : i₀ ≠ Fin.rev i₀) (hn : 3 ≤ n) {δ : F}
    (hδ : σ δ * δ = 1) :
    ∃ d : Fin n → F, (∀ s, σ (d s) * d (Fin.rev s) = 1) ∧
      d i₀ = 1 ∧ d (Fin.rev i₀) = 1 ∧ (∏ s, d s) = δ := by
  obtain ⟨k, hki, hkri⟩ := irgU_exists_coord hn hi
  by_cases hkr : k = Fin.rev k
  · refine ⟨MpStdSU.pairDiag k δ, MpStdSU.pairDiag_unitary hδ k, ?_, ?_, ?_⟩
    · rw [MpStdSU.pairDiag_of_ne (i := k) (s := i₀) δ (Ne.symm hki)
        (by rw [← hkr]; exact Ne.symm hki)]
    · rw [MpStdSU.pairDiag_of_ne (i := k) (s := Fin.rev i₀) δ (Ne.symm hkri)
        (fun h => hki (Fin.rev_injective h).symm)]
    · rw [Finset.prod_eq_single_of_mem k (Finset.mem_univ k)]
      · exact MpStdSU.pairDiag_self k δ
      · intro b _ hb
        exact MpStdSU.pairDiag_of_ne (i := k) (s := b) δ hb (by rw [← hkr]; exact hb)
  · obtain ⟨y, hy1, hy2⟩ := MpStdSU.exists_sqrt_normOne (σ := σ) hδ
    refine ⟨MpStdSU.pairDiag k y, MpStdSU.pairDiag_unitary hy1 k, ?_, ?_, ?_⟩
    · rw [MpStdSU.pairDiag_of_ne (i := k) (s := i₀) y (Ne.symm hki)
        (fun h => hkri (by rw [h, Fin.rev_rev]))]
    · rw [MpStdSU.pairDiag_of_ne (i := k) (s := Fin.rev i₀) y (Ne.symm hkri)
        (fun h => hki (Fin.rev_injective h).symm)]
    · rw [MpStdSU.prod_pairDiag hkr y, hy2]

theorem irgUM_longRootHom_conj_diagJ_eq_self {F : Type*} [Field F] {σ : F ≃+* F}
    {n : ℕ} (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    {i : Fin n} (hi : i ≠ Fin.rev i) (hdi : d i = 1) (hdri : d (Fin.rev i) = 1)
    (z : traceZero σ) :
    InnerDiagSU.conjSU (InnerDiagSU.diagJ d hd) (InnerDiagSU.isJUnitary_diagJ d hd)
        (longRootHom σ hi (Multiplicative.ofAdd z)) =
      longRootHom σ hi (Multiplicative.ofAdd z) := by
  rw [InnerDiagSU.conjSU_diagJ_longRootHom d hd hi z]
  rw [show (⟨d i * (z : F) * (d (Fin.rev i))⁻¹, _⟩ : traceZero σ) = z by
    ext
    simp [hdi, hdri]]

theorem irgUM_longRootHom_conjMulAut_diagJ_eq_self {F : Type*} [Field F]
    {σ : F ≃+* F} {n : ℕ} (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    {i : Fin n} (hi : i ≠ Fin.rev i) (hdi : d i = 1) (hdri : d (Fin.rev i) = 1)
    (c : Multiplicative (traceZero σ)) :
    irgUM_conjMulAut (InnerDiagSU.diagJ d hd) (InnerDiagSU.isJUnitary_diagJ d hd)
        (longRootHom σ hi c) = longRootHom σ hi c := by
  change InnerDiagSU.conjSU (InnerDiagSU.diagJ d hd)
      (InnerDiagSU.isJUnitary_diagJ d hd) (longRootHom σ hi c) = _
  obtain ⟨z, rfl⟩ : ∃ z : traceZero σ, Multiplicative.ofAdd z = c := ⟨c.toAdd, rfl⟩
  exact irgUM_longRootHom_conj_diagJ_eq_self d hd hi hdi hdri z

theorem irgUM_longRootHom_map_diagJ_eq_self {F : Type*} [Field F] {σ : F ≃+* F}
    {n : ℕ} (d : Fin n → F) (hd : ∀ s, σ (d s) * d (Fin.rev s) = 1)
    {i : Fin n} (hi : i ≠ Fin.rev i) (hdi : d i = 1) (hdri : d (Fin.rev i) = 1) :
    (longRootHom σ hi).range.map
        (irgUM_conjMulAut (InnerDiagSU.diagJ d hd)
          (InnerDiagSU.isJUnitary_diagJ d hd)).toMonoidHom =
      (longRootHom σ hi).range := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := hx
    rw [irgUM_conjMulAut_toMonoidHom_apply,
      irgUM_longRootHom_conjMulAut_diagJ_eq_self d hd hi hdi hdri c]
    exact ⟨c, rfl⟩
  · intro x hx
    obtain ⟨c, rfl⟩ := hx
    have hmem := Subgroup.mem_map_of_mem
      (irgUM_conjMulAut (InnerDiagSU.diagJ d hd)
        (InnerDiagSU.isJUnitary_diagJ d hd)).toMonoidHom
      (show longRootHom σ hi c ∈ (longRootHom σ hi).range from ⟨c, rfl⟩)
    rwa [irgUM_conjMulAut_toMonoidHom_apply,
      irgUM_longRootHom_conjMulAut_diagJ_eq_self d hd hi hdi hdri c] at hmem

theorem irgUM_longRootHom_map_entrywise {F : Type} [Field F] {σ : F ≃+* F}
    (φ : F ≃+* F) (hφ : ∀ c, φ (σ c) = σ (φ c))
    {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    (longRootHom σ hi).range.map
        (suCongr φ hφ n).toMonoidHom =
      (longRootHom σ hi).range := by
  have hφ' : ∀ c, φ.symm (σ c) = σ (φ.symm c) := fun c => by
    apply φ.injective
    rw [φ.apply_symm_apply, hφ, φ.apply_symm_apply]
  have hle : (longRootHom σ hi).range.map
      (suCongr φ hφ n).toMonoidHom ≤
      (longRootHom σ hi).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd
      ⟨φ (z.toAdd : F), irgU_traceZero_preserved σ φ hφ z.toAdd.2⟩, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom]
    apply Units.ext
    ext p q
    rw [coe_suCongr, Unitary.coe_longRootHom, Unitary.coe_longRootHom]
    simpa [Matrix.map_apply] using
      (congrFun (congrFun (irgU_map_longRootMatrix (F := F) (n := n) φ i (z.toAdd : F)) p) q).symm
  have hle' : (longRootHom σ hi).range.map
      (suCongr φ.symm hφ' n).toMonoidHom ≤
      (longRootHom σ hi).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd
      ⟨φ.symm (z.toAdd : F), irgU_traceZero_preserved σ φ.symm hφ' z.toAdd.2⟩, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom]
    apply Units.ext
    ext p q
    rw [coe_suCongr, Unitary.coe_longRootHom, Unitary.coe_longRootHom]
    simpa [Matrix.map_apply] using
      (congrFun (congrFun
        (irgU_map_longRootMatrix (F := F) (n := n) φ.symm i (z.toAdd : F)) p) q).symm
  apply le_antisymm hle
  intro x hx
  have hx' : (suCongr φ.symm hφ' n) x ∈
      (longRootHom σ hi).range :=
    hle' (Subgroup.mem_map_of_mem _ hx)
  have hx'' : (suCongr φ hφ n)
      ((suCongr φ.symm hφ' n) x) ∈
      (longRootHom σ hi).range.map
        (suCongr φ hφ n).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx'
  have hs : (suCongr φ hφ n) ((suCongr φ.symm hφ' n) x) = x := by
    apply Subtype.ext
    apply Units.ext
    ext p q
    simp [coe_suCongr]
  rwa [hs] at hx''

public theorem irgUM_pairAut_of_eq
    {n g : ℕ} (hK : Nat.card (irgU_F g) = (2 ^ g) ^ 2)
    (hadm : StatedLieAdmissible .PSU n 2 g)
    (M : LieUniversal)
    (hM : M = (⟨Unitary.SU (irgU_sigma g) n,
      Unitary.rootDatum (p := 2) (f := g) hK n⟩ : LieUniversal)) :
    ∀ (θ : MulAut (M.K ⧸ Subgroup.center M.K))
      (β' : Fin M.D.rank → ℤ), β' ∈ M.D.roots → GGLongRoot M.D β' →
      ∀ u' : M.K,
      ∃ β, (β ∈ M.D.roots ∧ (GGLongRoot M.D β ∨
          ((StatedLieTag.PSU = StatedLieTag.PSp ∧ n = 2) ∨
            StatedLieTag.PSU = StatedLieTag.F4) ∧ 2 • β ∉ M.D.roots)) ∧
        ∃ u : M.K,
          (ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) β' u').map θ.toMonoidHom =
            ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) β u ∧
          (ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) (-β') u').map
              θ.toMonoidHom =
            ggRootSub M.D (QuotientGroup.mk' (Subgroup.center M.K)) (-β) u := by
  subst hM
  intro θ β' hβ' hlong u'
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨φ, W, hWiso, hWsem⟩ :=
    irgUB_exists_semilinear_of_admissible (irgU_one_le_g hadm) hadm.2.2.1 hadm.2.2.2 θ
  obtain ⟨i, hi, hr, hrn⟩ := irgU_longRoot_shape hK β' hβ' hlong
  have hσ : ∀ c, irgU_sigma g (irgU_sigma g c) = c := irgU_sigma_involutive g hK
  have hφ : ∀ c, φ (irgU_sigma g c) = irgU_sigma g (φ c) := fun c =>
    irgU_ringEquiv_commute_unitaryInvolution (p := 2) (f := g) φ c
  have hW : InnerDiagSU.IsJUnitary (irgU_sigma g) W := hWiso
  have hδ : irgU_sigma g (W : Matrix (Fin n) (Fin n) (irgU_F g)).det *
      (W : Matrix (Fin n) (Fin n) (irgU_F g)).det = 1 := MpStdSU.normOne_det hW
  obtain ⟨d, hd, hdi, hdri, hdprod⟩ := irgUM_exists_diag_away hi hn hδ
  let D₀ : GL (Fin n) (irgU_F g) := InnerDiagSU.diagJ d hd
  have hD : InnerDiagSU.IsJUnitary (irgU_sigma g) D₀ :=
    InnerDiagSU.isJUnitary_diagJ d hd
  have hDdet : (D₀ : Matrix (Fin n) (Fin n) (irgU_F g)).det =
      (W : Matrix (Fin n) (Fin n) (irgU_F g)).det := by
    rw [show (D₀ : Matrix (Fin n) (Fin n) (irgU_F g)) = Matrix.diagonal d by
      exact InnerDiagSU.coe_diagJ d hd, Matrix.det_diagonal, hdprod]
  have hWdet0 : (W : Matrix (Fin n) (Fin n) (irgU_F g)).det ≠ 0 :=
    right_ne_zero_of_mul_eq_one hδ
  let s : SU (irgU_sigma g) n :=
    ⟨W * D₀⁻¹, by
      refine ⟨?_, hW.mul hD.inv⟩
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, Matrix.det_mul,
        Matrix.det_nonsing_inv, hDdet, Ring.inverse_eq_inv]
      exact mul_inv_cancel₀ hWdet0⟩
  have hs_coe : (s : GL (Fin n) (irgU_F g)) = W * D₀⁻¹ := rfl
  have hW_eq : W = (s : GL (Fin n) (irgU_F g)) * D₀ := by
    rw [hs_coe]
    group
  let Φ : MulAut (SU (irgU_sigma g) n) :=
    suCongr φ hφ n
  let Daut : MulAut (SU (irgU_sigma g) n) := irgUM_conjMulAut D₀ hD
  let Saut : MulAut (SU (irgU_sigma g) n) :=
    irgUM_conjMulAut (s : GL (Fin n) (irgU_F g)) s.2.2
  let α : MulAut (SU (irgU_sigma g) n) := Saut * Daut * Φ
  have hαcoe : ∀ x : SU (irgU_sigma g) n,
      ((α x : SU (irgU_sigma g) n) : GL (Fin n) (irgU_F g)) =
        W * Matrix.GeneralLinearGroup.map φ.toRingHom (x : GL (Fin n) (irgU_F g)) * W⁻¹ := by
    intro x
    change ((irgUM_conjMulAut (s : GL (Fin n) (irgU_F g)) s.2.2)
        ((irgUM_conjMulAut D₀ hD)
          ((suCongr φ hφ n) x)) :
        GL (Fin n) (irgU_F g)) =
      W * Matrix.GeneralLinearGroup.map φ.toRingHom (x : GL (Fin n) (irgU_F g)) * W⁻¹
    have h1 := irgUM_conjMulAut_apply (s : GL (Fin n) (irgU_F g)) s.2.2
      ((irgUM_conjMulAut D₀ hD)
        ((suCongr φ hφ n) x))
    have h2 := irgUM_conjMulAut_apply D₀ hD
      ((suCongr φ hφ n) x)
    have h3 : ((suCongr φ hφ n x : SU (irgU_sigma g) n) :
        GL (Fin n) (irgU_F g)) =
        Matrix.GeneralLinearGroup.map φ.toRingHom (x : GL (Fin n) (irgU_F g)) := by
      apply Units.ext
      rw [coe_suCongr]
      rfl
    rw [h1, h2, h3, hW_eq]
    group
  have hα : ∀ x : SU (irgU_sigma g) n,
      θ (QuotientGroup.mk' (Subgroup.center (SU (irgU_sigma g) n)) x) =
        QuotientGroup.mk' (Subgroup.center (SU (irgU_sigma g) n)) (α x) := by
    intro x
    obtain ⟨y, hy, hθy⟩ := hWsem x
    rw [hθy]
    congr 1
    apply Subtype.ext
    rw [hy, hαcoe]
  have hΦfix : (longRootHom (irgU_sigma g) hi).range.map Φ.toMonoidHom =
      (longRootHom (irgU_sigma g) hi).range := by
    simpa only [Φ] using irgUM_longRootHom_map_entrywise φ hφ hi
  have hDfix : (longRootHom (irgU_sigma g) hi).range.map Daut.toMonoidHom =
      (longRootHom (irgU_sigma g) hi).range := by
    simpa only [Daut, D₀] using irgUM_longRootHom_map_diagJ_eq_self d hd hi hdi hdri
  let j : Fin n := Fin.rev i
  have hj : j ≠ Fin.rev j := by
    intro h
    have h' : Fin.rev i = i := by simpa [j] using h
    exact hi h'.symm
  have hrn' : Unitary.rootGroup (irgU_sigma g) hσ n (-β') =
      (longRootHom (irgU_sigma g) hj).range := by
    simpa [j, hj] using hrn
  have hΦfixj : (longRootHom (irgU_sigma g) hj).range.map Φ.toMonoidHom =
      (longRootHom (irgU_sigma g) hj).range := by
    simpa only [Φ] using irgUM_longRootHom_map_entrywise φ hφ hj
  have hDfixj : (longRootHom (irgU_sigma g) hj).range.map Daut.toMonoidHom =
      (longRootHom (irgU_sigma g) hj).range := by
    simpa only [Daut, D₀] using
      irgUM_longRootHom_map_diagJ_eq_self d hd hj (by simpa [j] using hdri)
        (by simpa [j] using hdi)
  have hαcomp : α.toMonoidHom =
      Saut.toMonoidHom.comp (Daut.toMonoidHom.comp Φ.toMonoidHom) := by
    ext x
    simp [α, MulAut.mul_apply]
  have hmap : (Unitary.rootGroup (irgU_sigma g) hσ n β').map α.toMonoidHom =
      (Unitary.rootGroup (irgU_sigma g) hσ n β').map
        (MulAut.conj s).toMonoidHom := by
    rw [hr]
    rw [hαcomp, ← Subgroup.map_map, ← Subgroup.map_map, hΦfix, hDfix]
    dsimp only [Saut]
    rw [irgUM_conjMulAut_eq_conj s s.2.2]
  have hmapneg : (Unitary.rootGroup (irgU_sigma g) hσ n (-β')).map α.toMonoidHom =
      (Unitary.rootGroup (irgU_sigma g) hσ n (-β')).map
        (MulAut.conj s).toMonoidHom := by
    rw [hrn']
    rw [hαcomp, ← Subgroup.map_map, ← Subgroup.map_map, hΦfixj, hDfixj]
    dsimp only [Saut]
    rw [irgUM_conjMulAut_eq_conj s s.2.2]
  refine ⟨β', ⟨hβ', Or.inl hlong⟩, α u' * s, ?_, ?_⟩
  · exact irg_map_conj_subgroup_mulAut
      (QuotientGroup.mk' (Subgroup.center (SU (irgU_sigma g) n))) θ α hα
      (A := Unitary.rootGroup (irgU_sigma g) hσ n β')
      (B := Unitary.rootGroup (irgU_sigma g) hσ n β') (t := s) (u := u') hmap
  · exact irg_map_conj_subgroup_mulAut
      (QuotientGroup.mk' (Subgroup.center (SU (irgU_sigma g) n))) θ α hα
      (A := Unitary.rootGroup (irgU_sigma g) hσ n (-β'))
      (B := Unitary.rootGroup (irgU_sigma g) hσ n (-β')) (t := s) (u := u') hmapneg


end CFSG.StandardType.RCKRP
