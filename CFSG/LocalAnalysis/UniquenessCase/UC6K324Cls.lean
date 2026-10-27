module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Exc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial

theorem not_isSolvable_of_isQuasisimple_k324 {G : Type*} [Group G]
    (hq : CFSG.Open.IsQuasisimple G) : ¬ IsSolvable G := by
  intro hs
  obtain ⟨hcomm, hsimp⟩ := hq
  have hder : ∀ n, derivedSeries G n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, hcomm]
  obtain ⟨n, hn⟩ := hs.solvable
  rw [hder n] at hn
  obtain ⟨a, b, hab⟩ := hsimp.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      have hx : x = 1 := by
        have : x ∈ (⊤ : Subgroup G) := mem_top x
        rw [hn, mem_bot] at this
        exact this
      have hy : y = 1 := by
        have : y ∈ (⊤ : Subgroup G) := mem_top y
        rw [hn, mem_bot] at this
        exact this
      rw [hx, hy]

theorem ringChar_eq_three_of_card_nine {E : Type} [Field E] [Fintype E] (h : Fintype.card E = 9) :
    ringChar E = 3 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card E (ringChar E)
  have hdvd : ringChar E ∣ 9 := by
    rw [← h, hn]
    exact dvd_pow_self _ n.ne_zero
  have h3 : ringChar E ∣ 3 ^ 2 := by norm_num; exact hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)

theorem noA6Comp_linear {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq3 : q.p ≠ 3) (hq5 : q.p ≠ 5)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) {s : S} (hso : orderOf s = 5) :
    NoA6Comp (MulAut.conj s) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  refine NoA6Comp.of_congr e' ?_
  rw [congr_conj_exc]
  obtain ⟨u, hu⟩ := LinearFlag.proj_surjective (r + 1) (GaloisField q.p q.exponent) (e' s)
  set A : GL (Fin (r + 1)) (GaloisField q.p q.exponent) := Matrix.SpecialLinearGroup.toGL u
    with hAdef
  have hconj : LinearFlag.conjAut (r + 1) _ A =
      MulAut.conj (LinearFlag.proj (r + 1) (GaloisField q.p q.exponent) u) := by
    ext x
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective (r + 1) (GaloisField q.p q.exponent) x
    rw [LinearFlag.conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv]
  have hu5 : u ^ 5 ∈ LinearFlag.scalars (r + 1) (GaloisField q.p q.exponent) := by
    have h1 : LinearFlag.proj (r + 1) (GaloisField q.p q.exponent) (u ^ 5) = 1 := by
      rw [map_pow, hu, ← map_pow, ← hso, pow_orderOf_eq_one, map_one]
    exact (QuotientGroup.eq_one_iff _).1 h1
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hu5
  have hA : A ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
    apply Units.ext
    rw [hAdef, ← map_pow]
    simpa using hc
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ q.p
  have hpk : ((5 : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p]
    intro hd
    exact hq5 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_five).1 hd)
  rw [← hu, ← hconj]
  intro K hK
  obtain ⟨E, _, _, m, hm, hcharE, f, hf, hfk⟩ := linear_inner_component_type hpk hA K hK
  refine ⟨fun g => ?_⟩
  by_cases hsmall : m = 2 ∧ Fintype.card E < 4
  · obtain ⟨rfl, h4⟩ := hsmall
    haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) :=
      isSolvable_specialLinear_two_of_card_le_three (by rw [Nat.card_eq_fintype_card]; omega)
    exact not_isSolvable_of_isQuasisimple_k324 hK.2.2 (solvable_of_surjective hf)
  · have hLF := slFactorFacts_holds E m hm (fun h2 => by
      by_contra h4
      exact hsmall ⟨h2, by omega⟩)
    obtain ⟨e2⟩ := nonempty_centralQuotient_mulEquiv hLF.perfect f hf hfk
    obtain ⟨-, hE9⟩ := slAltSixFacts_holds E m hm ⟨e2.trans g⟩
    have h3 := ringChar_eq_three_of_card_nine hE9
    rw [hcharE, hchar] at h3
    exact hq3 h3

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel in
theorem noA6Comp_primeFormP {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hℓ3 : ℓ ≠ 3) (hℓ5 : ℓ ≠ 5) (u : gramSU h (idGram K n))
    (hu : orderOf (u : primeFormP h (idGram K n)) = 5) :
    NoA6Comp (MulAut.conj (u : primeFormP h (idGram K n))) := by
  have hU : (u : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) := u.2.1
  rw [← UnitaryHigher.primeFormConjHom_eq_conj h (idGram K n) u]
  have hu5 : u ^ 5 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    have h1 := pow_orderOf_eq_one (u : primeFormP h (idGram K n))
    rw [hu] at h1
    rw [QuotientGroup.mk_pow]
    exact h1
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hu5
  have hA : ((⟨u, hU⟩ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) ^ 5 =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc]
    exact (SubmonoidClass.coe_pow u 5).symm
  intro T hT
  obtain ⟨X, _, _, hX, hnA6, g, hg, hgk⟩ :=
    exists_lieFactor_of_component_primeFormConjHom (h := h) (n := n) slFactorFacts_holds
      suFactorFacts_holds Nat.prime_five (Ne.symm hℓ5) (⟨u, hU⟩ : primeFormUnitary h (idGram K n))
      hA T hT
  refine ⟨fun φ => hnA6 slAltSixFacts_holds suAltSixFacts_holds hℓ3 ?_⟩
  obtain ⟨e2⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hgk
  exact ⟨e2.trans φ⟩

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel in
theorem noA6Comp_unitary {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq3 : q.p ≠ 3) (hq5 : q.p ≠ 5)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) {s : S} (hso : orderOf s = 5) :
    NoA6Comp (MulAut.conj s) := by
  obtain ⟨⟨hℓ, hf, -⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  refine NoA6Comp.of_congr e' ?_
  rw [congr_conj_exc]
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e' s)
  rw [← hu]
  exact noA6Comp_primeFormP h hq3 hq5 u (by rw [hu, MulEquiv.orderOf_eq, hso])

theorem noA6Comp_B2 {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) (hq3 : q.p ≠ 3) (hq5 : q.p ≠ 5)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) {s : S} (hso : orderOf s = 5) :
    NoA6Comp (MulAut.conj s) := by
  obtain ⟨⟨hℓ, hf, -, hne⟩, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  refine NoA6Comp.of_congr e' ?_
  rw [congr_conj_exc]
  have ht : (e' s) ^ 5 = 1 := by rw [← map_pow, ← hso, pow_orderOf_eq_one, map_one]
  obtain ⟨x, hx, hxp⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by norm_num) Nat.prime_five
    (by norm_num) ht
  rw [← hx]
  intro K' hK'
  obtain ⟨-, hcomps⟩ := lieCompsCore_conj_sp (a6 := True) slFactorFacts_holds suFactorFacts_holds
    spFactorFacts_holds spFourTwoFacts_holds (fun _ => slAltSixFacts_holds)
    (fun _ => suAltSixFacts_holds) (fun _ => spAltSixFacts_holds) Nat.prime_five (by norm_num) hℓ hf
    hK (by norm_num) (Ne.symm hq5) (fun _ => hq3) x hxp
  obtain ⟨X, _, _, hX, ⟨g, hg, hgk⟩, hA6⟩ := hcomps K' hK'
  refine ⟨fun φ => ?_⟩
  obtain ⟨e2⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hgk
  have h2 := hA6 trivial ⟨e2.trans φ⟩
  rw [hK] at h2
  exact hne (by rw [h2])

end CFSG.LocalAnalysis.UniquenessCase.UCK
