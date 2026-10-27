module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Frame
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct

public section

namespace CFSG.StandardType.Line63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType CFSG.StandardType.LineU
open scoped commutatorElement

theorem exists_diagModel_frame
    {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K]
    [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 3 ≤ Nat.card A)
    (hU : ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ A, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U) :
    ∃ φ : ↥(unitarySU 2 n K 6) →* L', UnitTB.Model φ ∧
      ∀ a ∈ A, ∃ t : Fin 6 → K, ActsDiagU φ a t := by
  have hn : 1 ≤ n := by omega
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hne : ((6 : ℕ), n) ≠ (6, 1) := fun he => by
    have := congrArg Prod.snd he
    simp only at this
    omega
  obtain ⟨hperfSU, hcov⟩ := LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num) hne
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : CFSG.Open.IsElemAbelian 3 Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ Ab, x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
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
  have hV : ∃ V : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), V ≠ ⊥ ∧ IsPGroup 2 V ∧
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
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  obtain ⟨φ, hφ⟩ := hcov L' ψ'' hψ''s hker'' hperf
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ'' x = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ'' y = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ s)⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs, mul_inv_cancel]
      have hz' : y * (φ s')⁻¹ ∈ Subgroup.center L' := by
        apply hker''
        rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs', mul_inv_cancel]
      have hx : x = (x * (φ s)⁻¹) * φ s := by group
      have hy : y = (y * (φ s')⁻¹) * φ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    have htop : (⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ : Subgroup L') = ⊤ := hperf
    rw [htop] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  have hφker : ∀ g : ↥(unitarySU 2 n K 6), φ g = 1 →
      ∃ c : K, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c) := by
    intro g hg
    have h1 : LargeEvenProjMk (unitarySU 2 n K 6) g = 1 := by
      rw [← hφ g, hg, map_one]
    have h2 : g ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (unitarySU 2 n K 6) :=
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
  have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer h hM
  have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
  have htw : ∀ l : L', ψ'' (a l) =
      TableB.projConj (unitarySU 2 n K 6) ⟨P⁻¹ * M * P, hDN⟩ (ψ'' l) := by
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

end CFSG.StandardType.Line63

end
