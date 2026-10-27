module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdCodimOne
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine

public section

namespace CFSG.StandardType.LineU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
open scoped commutatorElement

@[expose] def UnitaryCoverAt (n d : ℕ) (K : Type) [Field K] : Prop :=
  commutator (unitarySU 2 n K d) = ⊤ ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (unitarySU 2 n K d)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s

@[expose] def UnitaryUniversalCover : Prop :=
  ∀ (n d : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 → 5 ≤ d →
    (d, n) ≠ (6, 1) → UnitaryCoverAt n d K

@[expose] def conjNHom {n d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d) where
  toFun := conjN D hD
  map_one' := Subtype.ext (by simp [coe_conjN])
  map_mul' x y := Subtype.ext (by simp only [coe_conjN, Subgroup.coe_mul]; group)

theorem coe_conjNHom {n d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) : conjNHom D hD s = conjN D hD s :=
  rfl

theorem primeForm_mem_normalizer {n d : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) {P : GL (Fin d) K}
    (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d)) :
    P ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
  have hdet : ∀ x g : GL (Fin d) K, (g : Matrix (Fin d) (Fin d) K).det = 1 →
      ((x * g * x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
    intro x g hg
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hg, mul_one]
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have key : ∀ x ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d), ∀ g ∈ unitarySU 2 n K d,
      x * g * x⁻¹ ∈ unitarySU 2 n K d := by
    intro x hx g hg
    exact TableBUE.mem_unitarySU_of_mem_primeFormUnitary h
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx (TableBUE.unitarySU_le_primeFormUnitary h hg))
        (Subgroup.inv_mem _ hx))
      (hdet x g ((mem_unitarySU_iff h).mp hg).1)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact key P hP g hg
  · intro hg
    have := key P⁻¹ (Subgroup.inv_mem _ hP) _ hg
    convert this using 1
    group

theorem projConj_mk_eq {n d : ℕ} {K : Type} [Field K] (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    (s : ↥(unitarySU 2 n K d)) :
    (TableB.projConj (unitarySU 2 n K d) ⟨D, hD⟩ (LargeEvenProjMk (unitarySU 2 n K d) s)) =
      LargeEvenProjMk (unitarySU 2 n K d) (conjN D hD s) := by
  rw [TableBUD.projConj_mk_coe]
  rfl

theorem comm_mul_central {L' : Type} [Group L'] {c d : L'} (hc : c ∈ Subgroup.center L')
    (hd : d ∈ Subgroup.center L') (a b : L') : ⁅c * a, d * b⁆ = ⁅a, b⁆ :=
  CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hc hd a b

theorem exists_diagModel_of_frame {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K]
    [Finite K] {n d : ℕ} (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K)
    (hd : 5 ≤ d) (hperfSU : commutator (unitarySU 2 n K d) = ⊤)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K d) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K d) s)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K d))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    {P : GL (Fin d) K} (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
      h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d))
    (hframe : ∀ x ∈ TypeA.inducedSub ψ A, ∃ (M : GL (Fin d) K)
      (hM : M ∈ LargeEvenGUSet (Fin d) K (2 ^ n)),
      ((P⁻¹ * M * P : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag ∧
        x = TableB.projConj (unitarySU 2 n K d) ⟨M, TableBUE.gu_subset_normalizer h hM⟩) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', Function.Surjective φ ∧
      (∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
        ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
  have hPN := primeForm_mem_normalizer h hP
  set θ := TableBUE.conjProj h P hP with hθ
  set ψ'' : L' →* LargeEvenProj (unitarySU 2 n K d) := θ.toMonoidHom.comp ψ with hψ''
  have hψ''s : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hkerEq : ψ''.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ'', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ θ.injective]
  have hker'' : ψ''.ker ≤ Subgroup.center L' := hkerEq ▸ hker
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
        φ.comp (conjNHom (P⁻¹ * M * P) hDN) := by
      apply CFSG.StandardType.TypeA.eq_of_inv_mul_mem_center hperfSU
      intro s
      apply hker''
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom]
      rw [htw (φ s), hφ s, projConj_mk_eq _ hDN s, ← hφ (conjN _ hDN s), inv_mul_cancel]
    have := congrArg (fun f => f s') hfun
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_conjNHom] using this

theorem exists_diagModel {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hcov : UnitaryCoverAt n d K)
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
  exact exists_diagModel_of_frame h hd hcov.1 (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf)
    hψ hker hperf hAI hP hframe


theorem card_ge_of_dvd {p d N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d) (hpd : p ∣ d)
    (hnd : ¬ (d = 6 ∧ p = 3)) (h1 : p ^ (d - 3) ≤ N) (h2 : p ^ 3 ≤ N) :
    p ^ (d / p + 2) ≤ N := by
  obtain ⟨q, rfl⟩ := hpd
  have hq : p * q / p = q := Nat.mul_div_cancel_left q hp.pos
  rw [hq]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · calc p ^ (q + 2) ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by omega)
      _ ≤ N := h2
  · rcases Nat.lt_or_ge q 3 with hq3 | hq3
    · have hq2' : q = 2 := by omega
      subst hq2'
      have hp4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have hp5 : 5 ≤ p := by
        by_contra hlt
        have hp3' : p = 3 := by omega
        subst hp3'
        exact hnd ⟨by norm_num, rfl⟩
      calc p ^ (2 + 2) ≤ p ^ (p * 2 - 3) := Nat.pow_le_pow_right hp.pos (by omega)
        _ ≤ N := h1
    · have h3q : 3 * q ≤ p * q := Nat.mul_le_mul_right q hp3
      calc p ^ (q + 2) ≤ p ^ (p * q - 3) := Nat.pow_le_pow_right hp.pos (by omega)
        _ ≤ N := h1

theorem noInvariantLineSCr_unitary (hU : UnitaryUniversalCover) {n d p : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    CFSG.StandardType.GGNoInvariantLineSCr p (CFSG.StandardType.ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _hsc
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : CFSG.StandardType.ggUnitaryTorusRank p d = d - 3 := by
    simp [CFSG.StandardType.ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    exists_diagModel hK hn hd hp hpq hpd (hU n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  have h := TableBU.unitaryFieldData_of_card hK hn
  haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
    DFunLike.coe_injective
  refine ⟨{x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU h σ)},
    weyl_W_prop h (by omega) hφker hA.2 hdiag, fun Λ hΛA hΛp => ?_⟩
  obtain ⟨σ, e, heΛ, hmv⟩ := moved_of_diag h (by omega) hφs hφker hp hA.2 hdiag hΛA hΛp
  exact ⟨φ (permSU h σ), ⟨σ, rfl⟩, e, heΛ, hmv⟩

end CFSG.StandardType.LineU
