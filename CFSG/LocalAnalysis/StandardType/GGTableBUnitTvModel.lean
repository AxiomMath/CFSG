module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel

public section

namespace CFSG.StandardType.UnitTv

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType.LineU
open scoped commutatorElement

theorem exists_diagModel' {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hcov : UnitaryCoverAt n d K)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
  obtain ⟨hperfSU, hcov'⟩ := hcov
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  set Ab := TypeA.inducedSub ψ A with hAbdef
  have hAb : CFSG.Open.IsElemAbelian p Ab := TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ Ab, x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
      (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card Ab = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  have hcard' : p ^ (d / p + 2) ≤ Nat.card Ab := hcardAb ▸ hcard
  obtain ⟨P, hP, hframe⟩ := TableBUD.exists_unitary_frame h hK (by omega) hdq hp hpq hAb hAbI
    hcard'
  have hPN := primeForm_mem_normalizer h hP
  set θ := TableBUE.conjProj h P hP with hθ
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : θ (ψ x) = θ 1 := by rw [map_one]; exact hx
    exact θ.injective hx'
  obtain ⟨φ, hφ⟩ := hcov' L' ψ'' hψ''s hker'' hperf
  have hφs : Function.Surjective φ := by
    have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K d),
          ψ'' x = LargeEvenProjMk (unitarySU 2 n K d) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ'' x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K d),
          ψ'' y = LargeEvenProjMk (unitarySU 2 n K d) s := by
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
  refine ⟨φ, hφs, ?_, ?_⟩
  ·
    intro g hg
    have h1 : LargeEvenProjMk (unitarySU 2 n K d) g = 1 := by
      rw [← hφ g, hg, map_one]
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
    have hxaAb : xa ∈ Ab := TypeA.mem_inducedSub.mpr ⟨a, ha, hxa⟩
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
        φ.comp (conjNHom (P⁻¹ * M * P) hDN) := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker''
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom]
      rw [htw (φ s), hφ s, projConj_mk_eq _ hDN s, ← hφ (conjN _ hDN s), inv_mul_cancel]
    have := congrArg (fun f => f s') hfun
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom] using this


theorem card_ge_of_not_dvd {p d N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d)
    (h1 : p ^ (d - 2) ≤ N) : p ^ (d / p + 2) ≤ N := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2 : d / p ≤ d / 3 := Nat.div_le_div_left hp3 (by norm_num)
  have h3 : d / p + 2 ≤ d - 2 := by omega
  exact (Nat.pow_le_pow_right hp.pos h3).trans h1

end CFSG.StandardType.UnitTv

end
