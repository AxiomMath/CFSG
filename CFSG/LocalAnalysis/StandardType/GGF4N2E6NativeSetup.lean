module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcRootTorus
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE6
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus

section FiveTorus

theorem e6NativeChar_pair_gamma (a : Fin 4 → ℤ) (i : Fin 4) :
    ∑ k, e6NativeChar a k * e6NativeGamma i k = 2 * a i := by
  calc
    ∑ k, e6NativeChar a k * e6NativeGamma i k =
        ∑ j, a j * e6NativePair (e6NativeGamma i) (e6NativeGamma j) := by
      simp only [e6NativeChar, e6NativePair, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    _ = 2 * a i := by simp [e6NativePair_gamma, mul_comm]

variable {L : Type} [Field L]

theorem rootDiagUnit_nativeChar_eq_one_iff (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    (a : Fin 4 → ℤ) :
    rootDiagUnit Tag.E6 (fun k => ζ ^ e6NativeChar a k) = 1 ↔
      ∀ i, (5 : ℤ) ∣ a i := by
  have hz : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.coe_units_iff.mp hζ
  constructor
  · intro h i
    have hparam : (fun k => ζ ^ e6NativeChar a k) = (1 : Fin Tag.E6.rank → Lˣ) :=
      rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
    have hchar (k : Fin Tag.E6.rank) : (5 : ℤ) ∣ e6NativeChar a k :=
      (hz.zpow_eq_one_iff_dvd _).mp (congrFun hparam k)
    have hpair : (5 : ℤ) ∣ 2 * a i := by
      rw [← e6NativeChar_pair_gamma]
      exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (hchar k) _
    have hcoprime : IsCoprime (5 : ℤ) 2 := ⟨-1, 3, by norm_num⟩
    exact hcoprime.dvd_of_dvd_mul_left hpair
  · intro h
    have hchar (k : Fin Tag.E6.rank) : (5 : ℤ) ∣ e6NativeChar a k :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (h i) _
    have hparam : (fun k => ζ ^ e6NativeChar a k) = (1 : Fin Tag.E6.rank → Lˣ) :=
      funext fun k => (hz.zpow_eq_one_iff_dvd _).mpr (hchar k)
    rw [hparam, rootDiagUnit_one]

end FiveTorus

section Certs

theorem e6NativeGamma_injective : Function.Injective e6NativeGamma :=
  List.nodup_ofFn.mp e6NativeC_check.1

theorem e6NativeGamma_mem (i : Fin 4) : e6NativeGamma i ∈ e6NativeC :=
  List.mem_ofFn' _ _ |>.mpr ⟨i, rfl⟩

section Pi

variable {Ω : Type} [Field Ω]

@[expose] def nativePi (M : Fin 4 → SL2 Ω) : ModGL Tag.E6 Ω :=
  ((List.finRange 4).map fun i => rootSL2 Tag.E6 Ω (e6NativeGamma i) (M i)).prod

theorem nativePi_pairwise_commute (M N : Fin 4 → SL2 Ω) :
    (List.finRange 4).Pairwise fun i j =>
      Commute (rootSL2 Tag.E6 Ω (e6NativeGamma i) (N i))
        (rootSL2 Tag.E6 Ω (e6NativeGamma j) (M j)) := by
  refine List.Pairwise.imp_of_mem (fun {i j} _ _ hne => ?_) (List.nodup_finRange 4)
  have hne' : e6NativeGamma i ≠ e6NativeGamma j := fun h => hne (e6NativeGamma_injective h)
  have hi := e6NativeGamma_isRoot i
  have hj := e6NativeGamma_isRoot j
  have h0 := e6NativeC_check.2.2.1 _ (e6NativeGamma_mem i) _ (e6NativeGamma_mem j) hne'
  exact rootSL2_commute_of_orth hi hj h0 (e6_not_isRoot_add_of_orth hi hj h0)
    (e6_not_isRoot_sub_of_orth hi hj h0) _ _

@[expose] def nativePiHom : (Fin 4 → SL2 Ω) →* ModGL Tag.E6 Ω where
  toFun := nativePi
  map_one' := by simp [nativePi]
  map_mul' M N := by
    unfold nativePi
    simp only [Pi.mul_apply, map_mul]
    exact list_prod_map_mul_of_pairwise _ _ _ (nativePi_pairwise_commute M N)

theorem nativePiHom_apply (M : Fin 4 → SL2 Ω) : nativePiHom M = nativePi M := rfl

theorem nativeCas_eq_nativePi (M : SL2 Ω) : nativeCas M = nativePi fun _ => M := by
  unfold nativeCas nativePi e6NativeC
  rw [List.map_ofFn, List.ofFn_eq_map]
  rfl

theorem nativePi_mem_adjointGroup (M : Fin 4 → SL2 Ω) :
    nativePi M ∈ adjointGroup Tag.E6 Ω := by
  unfold nativePi
  refine (adjointGroup Tag.E6 Ω).list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact rootSL2_mem_adjointGroup _ (M i)

theorem nativeCas_inv_mul_nativePi_mul (A : SL2 Ω) (M : Fin 4 → SL2 Ω) :
    (nativeCas A)⁻¹ * nativePi M * nativeCas A = nativePi fun i => A⁻¹ * M i * A := by
  rw [nativeCas_eq_nativePi, ← nativePiHom_apply, ← nativePiHom_apply, ← nativePiHom_apply,
    ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem nativePi_HSL (c : Fin 4 → Ωˣ) :
    nativePi (fun i => HSL (c i)) = rootDiagUnit Tag.E6
      (fun k => ∏ i, c i ^ ExceptionalCover.cartanCoord (e6NativeGamma i) k) := by
  have h : ∀ i, rootSL2 Tag.E6 Ω (e6NativeGamma i) (HSL (c i)) =
      rootDiagUnitHom Tag.E6 Ω (fun k => c i ^ ExceptionalCover.cartanCoord (e6NativeGamma i) k) :=
    fun i => CFSG.LocalAnalysis.GLTheoremA.Y10F.rootTorusSL2_eq_rootDiagUnit_cartanCoord
      (by decide) (e6NativeGamma_isRoot i) (c i)
  have hl : (List.finRange 4).map (fun i => rootSL2 Tag.E6 Ω (e6NativeGamma i) (HSL (c i))) =
      ((List.finRange 4).map fun i k =>
        c i ^ ExceptionalCover.cartanCoord (e6NativeGamma i) k).map (rootDiagUnitHom Tag.E6 Ω) := by
    rw [List.map_map]
    exact List.map_congr_left fun i _ => h i
  unfold nativePi
  rw [hl, ← map_list_prod, ← Fin.prod_univ_def]
  show rootDiagUnit Tag.E6 _ = _
  congr 1

end Pi

section Base

variable {K Ω : Type} [Field K] [CharP K 2] [Field Ω]

theorem baseChangeGL_nativePi (f : K →+* Ω) (M : Fin 4 → SL2 K) :
    baseChangeGL f (nativePi M) = nativePi fun i => Matrix.SpecialLinearGroup.map f (M i) := by
  unfold nativePi
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ =>
    baseChangeGL_rootSL2_of_charTwo f (e6NativeGamma_isRoot i) (M i)

theorem HSL_zpow (ζ : Ωˣ) (n : ℤ) : (HSL ζ : SL2 Ω) ^ n = HSL (ζ ^ n) := by
  let H : Ωˣ →* SL2 Ω := MonoidHom.mk' HSL fun a b => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  exact (map_zpow H ζ n).symm

theorem nativeTorus_eq (f : K →+* Ω) (t : SL2 K) {A : SL2 Ω} {ζ : Ωˣ}
    (ht : A⁻¹ * Matrix.SpecialLinearGroup.map f t * A = HSL ζ) (a : Fin 4 → ℤ) :
    (nativeCas A)⁻¹ * baseChangeGL f (nativePi fun i => t ^ a i) * nativeCas A =
      rootDiagUnit Tag.E6 (fun k => ζ ^ e6NativeChar a k) := by
  have hc : ∀ n : ℤ, A⁻¹ * Matrix.SpecialLinearGroup.map f (t ^ n) * A = HSL (ζ ^ n) := by
    intro n
    rw [map_zpow, ← HSL_zpow, ← ht]
    simpa using (conj_zpow (a := A⁻¹) (b := Matrix.SpecialLinearGroup.map f t) (i := n)).symm
  rw [baseChangeGL_nativePi, nativeCas_inv_mul_nativePi_mul]
  simp only [hc]
  rw [nativePi_HSL]
  congr 1
  funext k
  simp only [← zpow_mul]
  rw [prod_zpow_eq_zpow_sum]
  rfl

end Base

section Setup

variable (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (GaloisField 2 2) L]
  [IsAlgClosure (GaloisField 2 2) L]

abbrev nativeIota : ↥(adjointGroup Tag.E6 (GaloisField 2 2)) →* ModGL Tag.E6 L :=
  (baseChangeGL (algebraMap (GaloisField 2 2) L)).comp
    (adjointGroup Tag.E6 (GaloisField 2 2)).subtype

variable {L}

theorem exists_nativeSetup {A : SL2 L}
    (hA : A⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 2) A = eqpW) :
    ∃ S : LangSetup Tag.E6 L 5, S.D.g0 = nativeCas A ∧ S.D.q = 4 ∧
      S.D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 2)) ∧
      S.D.n = canonicalRep (coxeterSystem Tag.E6) L nativeW ∧
      (∀ γ, IsRoot Tag.E6 γ → S.ρ γ = e6NativeW γ) ∧
      S.Γ = (nativeIota L).range.map (MulAut.conj (nativeCas A)⁻¹).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)] <;> norm_num
  have hFr : ∀ c, iterateFrobenius L 2 2 c = c ^ Nat.card (GaloisField 2 2) := fun c => by
    rw [hK4, iterateFrobenius_def] <;> norm_num
  have hperf : Group.IsPerfect ↥(adjointGroup Tag.E6 (GaloisField 2 2)) :=
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 _).1
  have hg0 := entrywiseFrobGL_nativeCas_eq (Ω := L) 2 hA
  obtain ⟨S, hSD, hd⟩ := exists_langSetup_untw_of_datum frobeniusOnRoots_proved 3
    (Or.inl ⟨rfl, rfl⟩) (K := GaloisField 2 2) (L := L) Nat.prime_five (by norm_num)
    (by rw [hK4]; norm_num) hperf hFr nativeW (nativeCas_mem_adjointGroup A) hg0
  have hq : S.D.q = 4 := by rw [hSD]; exact hK4
  have hΦ : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius L 2 2)) := by rw [hSD]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) L nativeW := by rw [hSD]; rfl
  have hg : S.D.g0 = nativeCas A := by rw [hSD]; rfl
  refine ⟨S, hg, hq, hΦ, hn, fun γ hγ => ?_, ?_⟩
  · rw [S.rho_eq_smul_of_frob (fun c => by rw [hq, hFr, hK4]) hΦ hn hγ, nativeW_smul_root hγ]
  · show S.D.Γ = _
    rw [hd.Γ_eq, hg]

theorem nativeTorus_mem (S : LangSetup Tag.E6 L 5) {A : SL2 L}
    (hΓ : S.Γ = (nativeIota L).range.map (MulAut.conj (nativeCas A)⁻¹).toMonoidHom)
    (y : ↥(adjointGroup Tag.E6 (GaloisField 2 2))) {b : Fin Tag.E6.rank → Lˣ}
    (hy : (nativeCas A)⁻¹ * nativeIota L y * nativeCas A = rootDiagUnit Tag.E6 b) :
    rootDiagUnit Tag.E6 b ∈ S.D.torus ⊓ S.Γ := by
  have hdΓ : rootDiagUnit Tag.E6 b ∈ S.Γ := by
    rw [hΓ, ← hy]
    exact ⟨nativeIota L y, ⟨y, rfl⟩, by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hmod : rootDiagUnit Tag.E6 b ∈ S.D.model :=
    commutator_le_self_of_subgroup S.D.model hdΓ
  exact ⟨⟨rootDiagUnit_mem_torusGroup b, hmod.2⟩, hdΓ⟩

end Setup

end Certs

end CFSG.StandardType.N2E6Native

end
