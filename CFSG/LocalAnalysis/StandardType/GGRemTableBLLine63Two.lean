module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo

public section

namespace CFSG.StandardType.Line63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType CFSG.StandardType.LineU
open scoped commutatorElement

@[expose] def UnitaryCoverOddAt (n d : ℕ) (K : Type) [Field K] : Prop :=
  commutator (unitarySU 2 n K d) = ⊤ ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (unitarySU 2 n K d)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Odd (Nat.card ψ.ker) →
        ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s

theorem exists_diagModel_of {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hperfSU : commutator (unitarySU 2 n K d) = ⊤)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : p ^ (d / p + 2) ≤ Nat.card A)
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
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
  have hkerEq : ψ''.ker = ψ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact EmbeddingLike.map_eq_one_iff
  obtain ⟨φ, hφ⟩ := hcov' ψ'' hψ''s hkerEq
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

theorem noInvariantLine63_of_cover {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 4 ≤ Nat.card A) :
    ∃ W : Set L',
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ Λ : Subgroup (MulAut L'), Λ ≤ A → Nat.card Λ = 3 →
        ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ := by
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    exists_diagModel_of hK hn (by norm_num) Nat.prime_three hpq (by norm_num) hperfSU hψ
      hker hperf hA hAI hcard hcov'
  have h := TableBU.unitaryFieldData_of_card hK hn
  haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
    DFunLike.coe_injective
  refine ⟨{x | ∃ σ : Equiv.Perm (Fin 6), x = φ (permSU h σ)},
    weyl_W_prop h (by norm_num) hφker hA.2 hdiag, fun Λ hΛA hΛp => ?_⟩
  obtain ⟨σ, e, heΛ, hmv⟩ := moved_of_diag h (by norm_num) hφs hφker Nat.prime_three hA.2 hdiag
    hΛA hΛp
  exact ⟨φ (permSU h σ), ⟨σ, rfl⟩, e, heΛ, hmv⟩

theorem noInvariantLine63_odd {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hcov : UnitaryCoverOddAt 1 6 K)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 1 K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hodd : Odd (Nat.card ψ.ker))
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)), ∀ l : L', x (ψ l) = ψ (a l))
    (hr : 3 ^ 4 ≤ Nat.card A) :
    ∃ W : Set L',
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      ∀ Λ : Subgroup (MulAut L'), Λ ≤ A → Nat.card Λ = 3 →
        ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ := by
  refine noInvariantLine63_of_cover hK le_rfl (by norm_num) hcov.1 (fun ψ'' hs hk => ?_)
    hψ hker hperf hA hAI hr
  exact hcov.2 L' ψ'' hs (hk ▸ hker) hperf (hk ▸ hodd)

theorem noInvariantLineSCr_unitary63_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hcov : UnitaryCoverOddAt 1 6 K) :
    GGNoInvariantLineSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _h3 _hsc
  exact descent_noInvariantLine hψ hker hperf hA hAI
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc =>
      noInvariantLine63_odd hK hcov hs hk hp hodd hA₁ hAI₁ (by rw [hc]; exact hr))

theorem ggUnitDvd63LineSCr4_of (hU : UnitaryUniversalCover)
    (hodd : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → UnitaryCoverOddAt 1 6 K) :
    GGUnitDvd63LineSCr4 := by
  intro p lab hp hlab h
  by_cases hn1 : lab.n = 1
  · obtain ⟨t, l, n⟩ := lab
    obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
    dsimp only at ht hpn hl5 hp3 hn1
    subst ht hl5 hp3 hn1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    exact ⟨K, i1, i2, hK, ⟨hQ', noInvariantLineSCr_unitary63_two hK (hodd K hK)⟩⟩
  · exact largeEvenLabelAll_unitDvd63_line hU hlab h hn1

theorem ggLNoInvariantLineInputOn_unitDvd63 (h5 : GGUnitDvd63BstarRankInput)
    (hU : UnitaryUniversalCover)
    (hodd : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → UnitaryCoverOddAt 1 6 K) :
    GGLNoInvariantLineInputOn GGUnitDvd63Label :=
  ggLNoInvariantLineInputOn_unitDvd63_of h5 (ggUnitDvd63LineSCr4_of hU hodd)

section Certificates


theorem ggLNoInvariantLineInputOn_unitDvd63_of_holds (h5 : GGUnitDvd63BstarRankInput)
    (hodd : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → UnitaryCoverOddAt 1 6 K) :
    GGLNoInvariantLineInputOn GGUnitDvd63Label :=
  ggLNoInvariantLineInputOn_unitDvd63 h5 LineU.unitaryUniversalCover_holds hodd

end Certificates

end CFSG.StandardType.Line63
