module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Model
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType.USixTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.Line63
open scoped commutatorElement

theorem exists_diagModel_frame_odd
    {Lb : Type} [Group Lb] [Finite Lb] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {ψ : Lb →* LargeEvenProj (unitarySU 2 1 K 6)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center Lb) (hperf : commutator Lb = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {A : Subgroup (MulAut Lb)} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)), ∀ l : Lb, x (ψ l) = ψ (a l))
    (hr : 3 ^ 3 ≤ Nat.card A)
    (hU : ∃ U : Subgroup (LargeEvenProj (unitarySU 2 1 K 6)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ A, ∀ l : Lb, ψ l ∈ U → ψ (a l) ∈ U) :
    ∃ φ : ↥(unitarySU 2 1 K 6) →* Lb, UnitTB.Model φ ∧
      ∀ a ∈ A, ∃ t : Fin 6 → K, ActsDiagU φ a t := by
  have hn : 1 ≤ 1 := le_rfl
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hcov := LineU.unitaryCoverOddAt_six_two K hK4
  have hperfSU := hcov.1
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : CFSG.Open.IsElemAbelian 3 Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ Ab, x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ 1)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hAbD : Ab ≤ InndiagSU.inndiagU (d := 6) h (by norm_num) := fun x hx =>
    InndiagSU.congr_mem_primeFormD (d := 6) h (by norm_num) hK (hAbI x hx)
  have hcardAb : Nat.card Ab = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  have hV : ∃ V : Subgroup (LargeEvenProj (unitarySU 2 1 K 6)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ x ∈ Ab, ∀ v ∈ V, x v ∈ V := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hU
    refine ⟨U, hU1, hU2, fun x hx v hv => ?_⟩
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨l, rfl⟩ := hψ v
    rw [hxa l]
    exact hAU a ha l hv
  obtain ⟨P, hP, hframe⟩ := LID63.exists_unitary_frame63 hK hpq hAb hAbD
    (hr.trans_eq hcardAb.symm) hV
  have hPN := primeForm_mem_normalizer h hP
  set θ := TableBUE.conjProj h P hP with hθ
  set ψ'' : Lb →* LargeEvenProj (unitarySU 2 1 K 6) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center Lb := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  have hkerEq : ψ''.ker = ψ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact EmbeddingLike.map_eq_one_iff
  obtain ⟨φ, hφ⟩ := hcov.2 Lb ψ'' hψ''s hker'' hperf (hkerEq ▸ hodd)
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup Lb), (⊤ : Subgroup Lb)⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 1 K 6),
          ψ'' x = LargeEvenProjMk (unitarySU 2 1 K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 1 K 6),
          ψ'' y = LargeEvenProjMk (unitarySU 2 1 K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ s)⁻¹ ∈ Subgroup.center Lb := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs, mul_inv_cancel]
      have hz' : y * (φ s')⁻¹ ∈ Subgroup.center Lb := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs', mul_inv_cancel]
      have hx : x = (x * (φ s)⁻¹) * φ s := by group
      have hy : y = (y * (φ s')⁻¹) * φ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    have htop : (⁅(⊤ : Subgroup Lb), (⊤ : Subgroup Lb)⁆ : Subgroup Lb) = ⊤ := hperf
    rw [htop] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  have hφker : ∀ g : ↥(unitarySU 2 1 K 6), φ g = 1 →
      ∃ c : K, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c) := by
    intro g hg
    have h1 : LargeEvenProjMk (unitarySU 2 1 K 6) g = 1 := by
      rw [← hφ g, hg, map_one]
    have h2 : g ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (unitarySU 2 1 K 6) :=
      (QuotientGroup.eq_one_iff g).mp h1
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at h2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h2
    refine ⟨(c : K), ?_⟩
    rw [← hc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]
  refine ⟨φ, ⟨h, hφs, hφker⟩, ?_⟩
  intro a ha
  obtain ⟨xa, hxaI, hxa⟩ := hAI a ha
  have hxaAb : xa ∈ Ab := TypeA.mem_inducedSub.mpr ⟨a, ha, hxa⟩
  obtain ⟨M, hM, hdiag, hxa_eq⟩ := hframe xa hxaAb
  have hMN : M ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer h hM
  have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
  have htw : ∀ l : Lb, ψ'' (a l) =
      TableB.projConj (unitarySU 2 1 K 6) ⟨P⁻¹ * M * P, hDN⟩ (ψ'' l) := by
    intro l
    have e1 : ψ'' (a l) = θ (xa (ψ l)) := by
      rw [hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxa l]
    rw [e1, hxa_eq]
    exact TableBUD.conjProj_projConj h P hP ⟨M, hMN⟩ hDN (ψ l)
  have hdiag' : ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal (Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
    ((Matrix.isDiag_iff_diagonal_diag _).mp hdiag).symm
  refine ⟨Matrix.diag ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K),
    P⁻¹ * M * P, hDN, hdiag', fun s' => ?_⟩
  have hfun : (MulEquiv.toMonoidHom a).comp φ =
      φ.comp (conjNHom (P⁻¹ * M * P) hDN) := by
    apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
    intro s
    apply hker''
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom]
    rw [htw (φ s), hφ s, projConj_mk_eq _ hDN s, ← hφ (conjN _ hDN s), inv_mul_cancel]
  have := congrArg (fun f => f s') hfun
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom] using this

theorem exists_diagModel_odd
    {Lb : Type} [Group Lb] [Finite Lb] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {ψ : Lb →* LargeEvenProj (unitarySU 2 1 K 6)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center Lb) (hperf : commutator Lb = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {A : Subgroup (MulAut Lb)} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)), ∀ l : Lb, x (ψ l) = ψ (a l))
    (hcard : 3 ^ 4 ≤ Nat.card A) :
    ∃ φ : ↥(unitarySU 2 1 K 6) →* Lb, UnitTB.Model φ ∧
      ∀ a ∈ A, ∃ t : Fin 6 → K, ActsDiagU φ a t := by
  have hcov := LineU.unitaryCoverOddAt_six_two K (by rw [hK]; norm_num)
  obtain ⟨φ, hφs, hφker, hdiag⟩ := Line63.exists_diagModel_of hK le_rfl (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) hcov.1 hψ hker hperf hA hAI (by simpa using hcard)
    (fun ψ'' hs hk => hcov.2 Lb ψ'' hs (hk ▸ hker) hperf (hk ▸ hodd))
  exact ⟨φ, ⟨TableBU.unitaryFieldData_of_card hK le_rfl, hφs, hφker⟩, hdiag⟩

end CFSG.StandardType.USixTwo

end
