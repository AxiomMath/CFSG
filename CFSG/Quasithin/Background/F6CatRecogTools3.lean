module

public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Sym
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import Certificates.Certificate43
public import Certificates.Certificate4952
public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.Walter.J1Props
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Walter.W67.Statements
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurEight
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Walter.J1Recog
public import CFSG.Walter.J1
public import CFSG.Walter.PSL2Facts
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Fixed
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import TauCeti.Algebra.Central.TensorProduct
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.SymplecticGroup
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

namespace F6

variable {D : Type} [Group D] [Finite D]

section Kernel

theorem card_ker_conjQuotHom (hS : F618RecogSetting D) :
    Nat.card (conjQuotHom D).ker = Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) := by
  rw [ker_conjQuotHom hS]
  exact (Nat.card_congr ((Subgroup.center ↥(twoResidual (⊤ : Subgroup D))).equivMapOfInjective _
    (twoResidual (⊤ : Subgroup D)).subtype_injective).toEquiv).symm

theorem exists_sylow_quotient_ker (hS : F618RecogSetting D) (S : Sylow 2 D) :
    ∃ Q : Sylow 2 (D ⧸ (conjQuotHom D).ker),
      Nonempty (↥(S : Subgroup D) ≃* ↥(Q : Subgroup (D ⧸ (conjQuotHom D).ker))) := by
  have hodd : Odd (Nat.card (conjQuotHom D).ker) := by
    rw [card_ker_conjQuotHom hS]
    obtain ⟨k, hk⟩ := hS.center.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  exact exists_sylow_quotient_mulEquiv _ hodd S

noncomputable def mulEquiv_quotient_ker_of_center_eq_bot (hS : F618RecogSetting D)
    (hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥) :
    D ≃* D ⧸ (conjQuotHom D).ker :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (by rw [ker_conjQuotHom hS, hZ, Subgroup.map_bot]))

theorem isHatSym_of_setting (hS : F618RecogSetting D) {n : ℕ} (hn : 2 ≤ n)
    (hZ : Nat.card (Subgroup.center ↥(twoResidual (⊤ : Subgroup D))) = 3)
    (e : TwoResidualQuot D ≃* ↥(alternatingGroup (Fin n)))
    (ψ : D ⧸ (conjQuotHom D).ker ≃* Equiv.Perm (Fin n)) : IsHatSym n D := by
  have := twoResidual_top_normal (D := D)
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  let φ : D →* Equiv.Perm (Fin n) := ψ.toMonoidHom.comp (QuotientGroup.mk' _)
  have hφ : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = (conjQuotHom D).ker := by
    ext x
    simp [φ]
  have hkerZ : Nat.card φ.ker = 3 := by rw [hker, card_ker_conjQuotHom hS, hZ]
  have hAn : Nat.card ↥(alternatingGroup (Fin n)) = Nat.card (TwoResidualQuot D) :=
    (Nat.card_congr e.toEquiv).symm
  have hLcard : Nat.card ↥L = 3 * Nat.card (TwoResidualQuot D) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hZ, mul_comm]
  have hφL : L.map φ = alternatingGroup (Fin n) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hcardL : Nat.card ↥(L.map φ) * 3 = Nat.card ↥L := by
      have h1 := (φ.comp L.subtype).ker.card_mul_index
      rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype] at h1
      have h2 : (φ.comp L.subtype).ker = (Subgroup.center ↥L) := by
        ext l
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
          ker_conjQuotHom hS]
        constructor
        · rintro ⟨z, hz, hzl⟩
          have : z = l := Subtype.ext hzl
          rw [← this]
          exact hz
        · intro hl
          exact ⟨l, hl, rfl⟩
      rw [h2, hZ] at h1
      rw [← h1, mul_comm]
    have h2 := Subgroup.card_mul_index (L.map φ)
    have h3 : Nat.card (Equiv.Perm (Fin n)) = 2 * Nat.card ↥(alternatingGroup (Fin n)) :=
      (two_mul_nat_card_alternatingGroup).symm
    rw [h3, hAn] at h2
    rw [hLcard] at hcardL
    have hpos : 0 < Nat.card (TwoResidualQuot D) := Nat.card_pos
    have h4 : Nat.card ↥(L.map φ) = Nat.card (TwoResidualQuot D) := by omega
    rw [h4] at h2
    nlinarith
  have hcomap : (alternatingGroup (Fin n)).comap φ = L := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hφL]
      exact Subgroup.le_comap_map φ L
    · have h1 := ((alternatingGroup (Fin n)).comap φ).card_mul_index
      have h2 := (alternatingGroup (Fin n)).card_mul_index
      rw [Subgroup.index_comap_of_surjective _ hφ] at h1
      have h3 := φ.ker.card_mul_index
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top] at h3
      rw [hkerZ, ← h2] at h3
      have h4 : Nat.card ↥((alternatingGroup (Fin n)).comap φ) =
          3 * Nat.card ↥(alternatingGroup (Fin n)) := by
        have hpos : 0 < (alternatingGroup (Fin n)).index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        nlinarith
      rw [h4, hLcard, hAn]
  refine ⟨φ, hφ, hkerZ, ?_⟩
  rw [hcomap]
  exact ⟨⟨Group.isPerfect_def.mp hS.quasisimple.1, hS.quasisimple.2.1⟩, hZ, ⟨e⟩⟩

end Kernel

theorem card_mulAut_le_of_isSporadic_J1 {S : Type} [Group S] [Finite S]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic S .J1) :
    Nat.card (MulAut S) ≤ Nat.card S := by
  obtain ⟨e⟩ := h
  refine Nat.card_le_card_of_surjective (MulAut.conj : S →* MulAut S) fun β => ?_
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.isInnerAut_of_carrierJ1 e β
  refine ⟨l⁻¹, ?_⟩
  ext x
  rw [MulAut.conj_apply, hl x, inv_inv]

section PGammaL2

omit [Finite D] in
theorem conjQuotHom_of_mem (l : ↥(twoResidual (⊤ : Subgroup D))) :
    conjQuotHom D (l : D) = MulAut.conj (QuotientGroup.mk l : TwoResidualQuot D) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [conjQuotHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl

theorem mulAut_congr_conj {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_pGammaL2_subgroup_of_setting (hS : F618RecogSetting D) {K : Type} [Field K]
    [Finite K] {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hodd : IsOddPrimePower (Nat.card K)) (h3 : 3 < Nat.card K)
    (eK : TwoResidualQuot D ≃* StatedProj (StatedSL 2 K)) :
    ∃ H : Subgroup (PGammaL2 K), pGammaL2PSLRange K ≤ H ∧
      (pGammaL2PSLRange K).relIndex H = (twoResidual (⊤ : Subgroup D)).index ∧
      Nonempty (D ⧸ (conjQuotHom D).ker ≃* ↥H) := by
  have := twoResidual_top_normal (D := D)
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective _
    ⟨pGammaL2ToMulAutPSL2_injective K hodd h3, pGammaL2ToMulAutPSL2_surjective K hK hodd h3⟩
  let ε : TwoResidualQuot D ≃* PSL2 K :=
    eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  let χ : MulAut (TwoResidualQuot D) ≃* PGammaL2 K := (MulAut.congr ε).trans Φ.symm
  set H := (conjQuotHom D).range.map χ.toMonoidHom with hH
  have iso : D ⧸ (conjQuotHom D).ker ≃* ↥H :=
    (QuotientGroup.quotientKerEquivRange _).trans
      ((conjQuotHom D).range.equivMapOfInjective χ.toMonoidHom χ.injective)
  have hle : pGammaL2PSLRange K ≤ H := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (ε.symm z)
    refine ⟨conjQuotHom D (l : D), ⟨l, rfl⟩, ?_⟩
    rw [conjQuotHom_of_mem, hl]
    change Φ.symm (MulAut.congr ε (MulAut.conj (ε.symm z))) = _
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_eq]
    change MulAut.conj z = pGammaL2ToMulAutPSL2 K hodd h3 (SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL z))
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  refine ⟨H, hle, ?_, ⟨iso⟩⟩
  have h1 := Subgroup.relIndex_mul_card (pGammaL2PSLRange K) H
  rw [inf_of_le_left hle, ← Nat.card_congr iso.toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (conjQuotHom D)).toEquiv,
    card_range_conjQuotHom hS, ← Nat.card_congr (pGammaL2PSLRangeEquiv K).toEquiv,
    ← Nat.card_congr ε.toEquiv] at h1
  have hpos : 0 < Nat.card (TwoResidualQuot D) := Nat.card_pos
  rw [mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1)

end PGammaL2

section PSigma

open CFSG.LocalAnalysis.ComponentInitial in
theorem isSimpleGroup_pGammaL2PSLRange_nine (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 9) : IsSimpleGroup ↥(pGammaL2PSLRange K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism K
    (by rw [← Nat.card_eq_fintype_card, hK])
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact ((pGammaL2PSLRangeEquiv K).symm.trans φ).isSimpleGroup

theorem pCore_two_eq_bot_of_le {G : Type*} [Group G] [Finite G] {H P : Subgroup G}
    (hPH : P ≤ H) (hPn : P.Normal) (hcen : Subgroup.centralizer (P : Set G) = ⊥)
    (hsimple : IsSimpleGroup ↥P) (hP2 : ¬ IsPGroup 2 ↥P) : CFSG.Open.pCore 2 ↥H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCore 2 ↥H with hNdef
  have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set N' := N.map H.subtype with hN'
  have hN'conj : ∀ g ∈ H, ∀ x ∈ N', g * x * g⁻¹ ∈ N' := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨_, hNn.conj_mem y hy ⟨g, hg⟩, rfl⟩
  have hinf : N' ⊓ P = ⊥ := by
    set M := (N' ⊓ P).subgroupOf P with hM
    have hMn : M.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [hM, Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨hN'conj g (hPH g.2) x hx.1, P.mul_mem (P.mul_mem g.2 x.2) (P.inv_mem g.2)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxM : (⟨x, hx.2⟩ : ↥P) ∈ M := by
        rw [hM, Subgroup.mem_subgroupOf]
        exact hx
      rw [h, Subgroup.mem_bot] at hxM
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxM)
    · exfalso
      apply hP2
      intro x
      have hx : x ∈ M := h ▸ Subgroup.mem_top x
      rw [hM, Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := hx.1
      obtain ⟨k, hk⟩ := hN2 ⟨y, hy⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := congrArg (fun z : ↥N => ((z : ↥H) : G)) hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h1 ⊢
      rw [← hyx]
      simpa using h1
  have hcen' : N' ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hc : x * s * x⁻¹ * s⁻¹ ∈ N' ⊓ P := by
      refine ⟨?_, P.mul_mem (hPn.conj_mem s hs x) (P.inv_mem hs)⟩
      have : x * (s * x⁻¹ * s⁻¹) ∈ N' := N'.mul_mem hx (hN'conj s (hPH hs) _ (N'.inv_mem hx))
      simpa [mul_assoc] using this
    rw [hinf, Subgroup.mem_bot] at hc
    calc s * x = (x * s * x⁻¹ * s⁻¹)⁻¹ * (x * s) := by group
      _ = x * s := by rw [hc, inv_one, one_mul]
  rw [hcen] at hcen'
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp (le_bot_iff.mp hcen')

theorem finite_pGammaL2 (K : Type) [Field K] [Finite K] : Finite (PGammaL2 K) :=
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    fun _ _ h => RingEquiv.ext (congrFun h)
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem pCore_two_pSigmaL2_eq_bot (K : Type) [Field K] [Finite K] (hK : Nat.card K = 9) :
    CFSG.Open.pCore 2 ↥(PSigmaL2 K) = ⊥ := by
  have : Finite (PGammaL2 K) := finite_pGammaL2 K
  have hodd : IsOddPrimePower (Nat.card K) := ⟨3, 2, Nat.prime_three, by decide, by norm_num,
    by rw [hK]; norm_num⟩
  have h3 : 3 < Nat.card K := by rw [hK]; norm_num
  refine pCore_two_eq_bot_of_le le_sup_left (pGammaL2PSLRange_normal K hodd h3)
    (pGammaL2_pslRange_centralizer_eq_bot K hodd h3) (isSimpleGroup_pGammaL2PSLRange_nine K hK)
    fun h2 => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  rw [← Nat.card_congr (pGammaL2PSLRangeEquiv K).toEquiv, psl2_card_formula K hodd, hK] at hk
  have h360 : (2 : ℕ) ^ k = 360 := by norm_num at hk; omega
  have h5 : (5 : ℕ) ∣ 2 ^ k := by rw [h360]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
  norm_num at this

theorem nonempty_pSigmaL2_mulEquiv_perm_six
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 9) : Nonempty (↥(PSigmaL2 K) ≃* Equiv.Perm (Fin 6)) :=
  have : Finite (PGammaL2 K) := finite_pGammaL2 K
  CFSG.Quasithin.EmptyFaithfulMultiple.L15422.nonempty_mulEquiv_perm_six
    (pCore_two_pSigmaL2_eq_bot K hK)
    (CFSG.Quasithin.EmptyFaithfulMultiple.L15422.isL2FieldExt_of_isL2FieldExtCat
      ⟨Nat.prime_three, K, inferInstance, inferInstance, by rw [hK]; norm_num,
        ⟨MulEquiv.refl _⟩⟩)

end PSigma

end F6

end CFSG.Quasithin
