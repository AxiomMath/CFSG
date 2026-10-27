module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxCover
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU5FiveModel

public section

namespace CFSG.StandardType.QTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.StandardType
open scoped commutatorElement

theorem qTwoNbrRec_diagModel
    {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K]
    [Finite K] {n d : ℕ} (h : UnitaryFieldData 2 n K) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2))
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1) {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    {P : GL (Fin d) K} (hP : P ∈ primeFormUnitary h (idGram K d))
    (hframe : ∀ a ∈ TypeA.inducedSub ψ A, ∃ (M : GL (Fin d) K)
      (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
        a = TableB.projConj (unitarySU 2 n K d) ⟨M, TableBUE.gu_subset_normalizer h hM⟩) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, LineU.ActsDiagU φ a t := by
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, Nat.mul_comm]
  haveI : Fact (Nat.Prime 2) := ⟨h.prime⟩
  haveI : CharP K 2 := h.charP
  have hperfSU : commutator (unitarySU 2 n K d) = ⊤ := by
    have hperf' : Group.IsPerfect (unitarySU 2 n K d) := by
      by_cases he : Even d
      · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU
          (F := K) (p := 2) (f := n) hK (by omega)
      · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd
          (F := K) (p := 2) (f := n) hK (by omega) hdq
    exact hperf'.commutator_eq_top
  have hPN := LineU.primeForm_mem_normalizer h hP
  set θ := TableBUE.conjProj h P hP with hθ
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  have hodd'' : ∀ y ∈ ψ''.ker, y ^ 2 = 1 → y = 1 := by
    intro y hy hy2
    apply hodd y ?_ hy2
    rw [MonoidHom.mem_ker] at hy ⊢
    have hy' : θ (ψ y) = θ 1 := by rw [map_one]; exact hy
    exact θ.injective hy'
  obtain ⟨φ₀, hφs₀, hφ₀⟩ := qTwoNbrRec_cover_odd (F := K) (n := n) (d := d)
    hK hn (by omega) hdq (ψ := ψ'') hψ''s hker'' hperf hodd''
  let φ : ↥(unitarySU 2 n K d) →* L' := φ₀
  have hφs : Function.Surjective φ := hφs₀
  have hφu : ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s := fun s => hφ₀ s
  refine ⟨φ, hφs, ?_, ?_⟩
  ·
    intro g hg
    have h1 : LargeEvenProjMk (unitarySU 2 n K d) g = 1 := by
      rw [← hφu g, hg, map_one]
    have h2 : g ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) :=
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
  ·
    intro a ha
    obtain ⟨xa, hxaI, hxa⟩ := hAI a ha
    have hxaAb : xa ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hxa⟩
    obtain ⟨M, hM, hdiag, hxa_eq⟩ := hframe xa hxaAb
    have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      TableBUE.gu_subset_normalizer h hM
    have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hMN) hPN
    have htw : ∀ l : L', ψ'' (a l) =
        TableB.projConj (unitarySU 2 n K d) ⟨P⁻¹ * M * P, hDN⟩ (ψ'' l) := by
      intro l
      have e1 : ψ'' (a l) = θ (xa (ψ l)) := by
        rw [hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hxa l]
      rw [e1, hxa_eq]
      exact TableBUD.conjProj_projConj h P hP ⟨M, hMN⟩ hDN (ψ l)
    have hdiag' : ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (Matrix.diag ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
      ((Matrix.isDiag_iff_diagonal_diag _).mp hdiag).symm
    refine ⟨Matrix.diag ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
      P⁻¹ * M * P, hDN, hdiag', fun s' => ?_⟩
    have hfun : (MulEquiv.toMonoidHom a).comp φ =
        φ.comp (LineU.conjNHom (P⁻¹ * M * P) hDN) := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker''
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, LineU.coe_conjNHom]
      rw [htw (φ s), hφu s, LineU.projConj_mk_eq _ hDN s, ← hφu (LineU.conjN _ hDN s),
        inv_mul_cancel]
    have := congrArg (fun f => f s') hfun
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, LineU.coe_conjNHom] using this

end CFSG.StandardType.QTwo

end
