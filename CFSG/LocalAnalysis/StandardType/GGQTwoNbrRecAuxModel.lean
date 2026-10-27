module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxCD
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.Open

variable {G Q : Type} [Group G] [Finite G] [Group Q] {Bs K : Subgroup G}

@[expose] noncomputable def qTwoNbrRec_suEquiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) (d : ℕ) : Su F 2 1 d ≃* ↥(unitarySU 2 1 F d) :=
  MulEquiv.subgroupCongr
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1) hF d)

theorem qTwoNbrRec_coe_suEquiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {d : ℕ} (x : Su F 2 1 d) :
    ((qTwoNbrRec_suEquiv hF d x : ↥(unitarySU 2 1 F d)) : GL (Fin d) F) = (x : GL (Fin d) F) :=
  rfl

theorem qTwoNbrRec_isUnitaryMat_of_isDiag {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {d : ℕ} {g : GL (Fin d) F} (hg : ggIsDiagMat g) :
    ggIsUnitaryMat (p := 2) (f := 1) g := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨t, ht⟩ := hg
  have htne : ∀ i, t i ≠ 0 := fun i => LineU.diag_ne_zero_of_eq ht i
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using hF
  have hcube : ∀ i, t i ^ 3 = 1 := by
    intro i
    have h := FiniteField.pow_card_sub_one_eq_one (t i) (htne i)
    rw [hcard] at h
    norm_num at h
    exact h
  rw [ggIsUnitaryMat, CFSG.LieType.Universal.Unitary.conjTr, ht,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  rw [Matrix.diagonal_injective.eq_iff]
  funext i
  show CFSG.LieType.BorelTits.unitaryInvolution F 2 1 (t i) * t i = 1
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, show (2 : ℕ) ^ 1 = 2 by norm_num,
    ← pow_succ]
  exact hcube i

theorem qTwoNbrRec_inducesUnitary_of_actsDiagU {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {d : ℕ} {L' : Type} [Group L'] (ι : L' →* Q)
    {φ : ↥(unitarySU 2 1 F d) →* L'} {a : MulAut L'} {t : Fin d → F}
    (ha : LineU.ActsDiagU φ a t) {b : Q} (hb : ∀ l : L', b * ι l * b⁻¹ = ι (a l)) :
    ∃ g : GL (Fin d) F, ggIsDiagMat g ∧
      GGInducesUnitary (p := 2) (f := 1)
        (ι.comp (φ.comp (qTwoNbrRec_suEquiv hF d).toMonoidHom)) b g := by
  classical
  obtain ⟨D, hD, hDt, hact⟩ := ha
  refine ⟨D, ⟨t, hDt⟩, qTwoNbrRec_isUnitaryMat_of_isDiag (F := F) (d := d) hF ⟨t, hDt⟩, ?_⟩
  intro x
  refine ⟨(qTwoNbrRec_suEquiv hF d).symm (LineU.conjN D hD (qTwoNbrRec_suEquiv hF d x)),
    ?_, ?_⟩
  · rw [← qTwoNbrRec_coe_suEquiv (F := F) hF
      ((qTwoNbrRec_suEquiv hF d).symm (LineU.conjN D hD (qTwoNbrRec_suEquiv hF d x)))]
    rw [MulEquiv.apply_symm_apply, LineU.coe_conjN, qTwoNbrRec_coe_suEquiv]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hb (φ (qTwoNbrRec_suEquiv hF d x)), hact (qTwoNbrRec_suEquiv hF d x),
      MulEquiv.apply_symm_apply]

theorem qTwoNbrRec_model_psi
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBs : IsElemAbelian 3 Bs) {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
    (hF : Nat.card F = (2 ^ 1) ^ 2) (hd : 5 ≤ d)
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 1 F d))
    (hperf : commutator ↥K = ⊤)
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F d))
        (LargeEvenGUSet (Fin d) F (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hrank : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma K hN).range)
    (q : ↥(K ⊔ Bs) →* Q) (hq : q.ker = (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs)) :
    ∃ ψ : Su F 2 1 d →* Q, ψ.ker ≤ Subgroup.center (Su F 2 1 d) ∧
      ψ.range = qTwoNbrRec_Kb q ∧
      GGActsDiagonally (p := 2) (f := 1) ψ
        (q.comp (Subgroup.inclusion (le_sup_right : Bs ≤ K ⊔ Bs))).range := by
  classical
  have hFr : UnitaryFieldData 2 1 F := TableBU.unitaryFieldData_of_card hF le_rfl
  obtain ⟨φ, hφsurj, hφker, hφdiag⟩ :=
    qTwoNbrRec_coverDiag (F := F) (d := d) hN hBs hFr hd θ hperf hind hrank q hq
  refine ⟨(qTwoNbrRec_Kb q).subtype.comp (φ.comp (qTwoNbrRec_suEquiv hF d).toMonoidHom),
    ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxφ : φ ((qTwoNbrRec_suEquiv hF d) x) = 1 := by
      have hx1 : ((qTwoNbrRec_Kb q).subtype.comp
          (φ.comp (qTwoNbrRec_suEquiv hF d).toMonoidHom)) x = 1 := by
        simpa only [MonoidHom.mem_ker] using hx
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hx1
      exact Subtype.ext hx1
    obtain ⟨c, hc⟩ := hφker ((qTwoNbrRec_suEquiv hF d) x) hxφ
    have hxmat : ((x : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        Matrix.diagonal (fun _ => c) := by
      rw [← qTwoNbrRec_coe_suEquiv hF x]
      exact hc
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hxmat]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  · have hsurj : Function.Surjective
        (φ.comp (qTwoNbrRec_suEquiv hF d).toMonoidHom) :=
      hφsurj.comp (qTwoNbrRec_suEquiv hF d).surjective
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj]
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  · intro b' hb'
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hb'
    obtain ⟨t, ha⟩ := hφdiag b
    exact qTwoNbrRec_inducesUnitary_of_actsDiagU (F := F) (d := d) hF
      (qTwoNbrRec_Kb q).subtype ha (fun l => (qTwoNbrRec_gammaB_coe q hN b l).symm)

end CFSG.StandardType.QTwo

end
