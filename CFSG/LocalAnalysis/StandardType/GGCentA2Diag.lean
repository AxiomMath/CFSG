module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
import CFSG.LocalAnalysis.StandardType.GGCentA2RatPerm
import CFSG.LocalAnalysis.StandardType.GGCentFrob
import CFSG.LocalAnalysis.StandardType.GGCentPerm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
import CFSG.LieType.SeitzGeneration.ExcHighThree.SplitFrame
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S146A2
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch11SecSFacts2
import CFSG.Quasithin.Vol2.Ch11SecSFacts3
import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
import CFSG.Quasithin.Vol2.Ch11SecSI3
import CFSG.Quasithin.Vol2.Ch11SecSObl
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KLCE.Sector
import CFSG.Walter.J1Props
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LieType.SeitzGeneration.ExcHighThree
open scoped MatrixGroups commutatorElement

theorem ntpA2_diag
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 18)
    (horb : ∀ i : KernelComponent (rootCharHom a),
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3)
    (σ : Equiv.Perm (KernelComponent (rootCharHom a))) (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1)
    (hσ : ∀ i, (componentRootSpan L (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
      componentRootSpan L (rootCharHom a) (σ i))
    (hlayer : ∀ J : Subgroup (ModGL .E6 L),
      J ≤ S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) →
        CFSG.IsQuasisimple ↥J → J ≤ ⨆ i, rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (i₀ : KernelComponent (rootCharHom a))
    (φ : SL(3, L) →* ModGL .E6 L) (σφ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
    (hφ : IsSLFrame φ σφ) (hΨ : componentRoots (rootCharHom a) i₀ = frameRoots σφ)
    (hφker : φ.ker ≤ Subgroup.center SL(3, L)) :
    ∃ Δ : SL(3, L) →* ModGL .E6 L, (∀ X, Δ X = cycConjDiag n (φ X)) ∧
      Δ.ker ≤ Subgroup.center SL(3, L) ∧
      (∀ r ∈ φ.range, ∀ s ∈ φ.range, Commute r (n * s * n⁻¹)) ∧
      Δ.range ≤ adjointGroup .E6 L ⊓ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
        Subgroup.zpowers n : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) ∧
      (∀ J : Subgroup (ModGL .E6 L),
        J ≤ S.Γ ⊓ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
          Subgroup.zpowers n : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) →
        CFSG.IsQuasisimple ↥J → J ≤ Δ.range) ∧
      ∃ k : ℕ, ∀ y ∈ φ.range, n ^ k * S.D.step y * (n ^ k)⁻¹ ∈ φ.range := by
  classical
  obtain ⟨hap, hT, -, -, hn3, hdn, -⟩ := hpair
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
    have h3 : (3 : L) = 0 := by exact_mod_cast h
    have h1 : (1 : L) = 0 := by
      calc (1 : L) = 3 - 2 := by norm_num
        _ = 0 := by rw [h3, h2]; simp
    exact one_ne_zero h1
  obtain ⟨c, hc, -⟩ :=
    kernel_classes_of_ncard_eighteen h3L hap hker
  have hI : Nat.card (KernelComponent (rootCharHom a)) = 3 :=
    (Nat.card_congr (Equiv.ofBijective c hc).symm).trans (Nat.card_fin 3)
  haveI hFin : Finite (KernelComponent (rootCharHom a)) :=
    Nat.finite_of_card_ne_zero (by rw [hI]; norm_num)
  letI : Fintype (KernelComponent (rootCharHom a)) := Fintype.ofFinite _
  have hcardF : Fintype.card (KernelComponent (rootCharHom a)) = 3 := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨e, he⟩ := exists_equiv_finRotate hcardF σ hσ1 hσ3
  let Y : KernelComponent (rootCharHom a) → Subgroup (ModGL .E6 L) :=
    fun i => componentRootSpan L (rootCharHom a) i
  let m : Fin 3 := e.symm i₀
  let R : Fin 3 → Subgroup (ModGL .E6 L) := fun k => Y (e (m + k))
  have hmadd_ne : ∀ k l : Fin 3, k ≠ l → m + k ≠ m + l := by
    have hgen : ∀ m' : Fin 3, ∀ k l : Fin 3, k ≠ l → m' + k ≠ m' + l := by
      intro m' k l hkl h
      apply hkl
      fin_cases m' <;> fin_cases k <;> fin_cases l <;> simp_all [Fin.ext_iff]
    exact hgen m
  have henc_inj : Function.Injective (fun k : Fin 3 => e (m + k)) := by
    intro k l h
    by_contra hkl
    exact hmadd_ne k l hkl (e.injective h)
  have henc_bij : Function.Bijective (fun k : Fin 3 => e (m + k)) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨henc_inj, by rw [Fintype.card_fin, hcardF]⟩
  have hEeq : (⨆ i, Y i) = ⨆ k, R k := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      obtain ⟨k, hk⟩ := henc_bij.surjective i
      rw [← hk]
      exact le_iSup R k
    · refine iSup_le fun k => le_iSup Y _
  have hR0Y : R 0 = Y i₀ := by
    change Y (e (m + 0)) = Y i₀
    rw [add_zero]
    exact congrArg Y (e.apply_symm_apply i₀)
  have hφrange : φ.range = Y i₀ := by
    rw [hφ.range, ← hΨ]
    rfl
  have hRcomm : ∀ k l : Fin 3, k ≠ l → ∀ x ∈ R k, ∀ z ∈ R l, Commute x z := by
    intro k l hkl x hx z hz
    have hij : e (m + k) ≠ e (m + l) := fun h => hmadd_ne k l hkl (e.injective h)
    exact (Subgroup.mem_centralizer_iff.mp
      (componentRootSpan_le_centralizer L hij hx) z hz).symm
  have hconj : ∀ k : Fin 3, (R k).map (MulAut.conj n).toMonoidHom = R (finRotate 3 k) := by
    intro k
    change (Y (e (m + k))).map (MulAut.conj n).toMonoidHom = Y (e (m + finRotate 3 k))
    rw [hσ (e (m + k)), he (m + k)]
    congr 1
    rw [finRotate_apply, finRotate_apply, add_assoc]
  have hmemR1 : ∀ r ∈ R 0, n * r * n⁻¹ ∈ R 1 := by
    intro r hr
    have h : n * r * n⁻¹ ∈ (R 0).map (MulAut.conj n).toMonoidHom := by
      refine Subgroup.mem_map_of_mem _ hr
    rwa [hconj 0, show finRotate 3 (0 : Fin 3) = 1 from by decide] at h
  have hmemR2 : ∀ r ∈ R 0, n ^ 2 * r * (n ^ 2)⁻¹ ∈ R 2 := by
    intro r hr
    have h1 : n * r * n⁻¹ ∈ R 1 := hmemR1 r hr
    have h : n * (n * r * n⁻¹) * n⁻¹ ∈ (R 1).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ h1
    rw [hconj 1, show finRotate 3 (1 : Fin 3) = 2 from by decide] at h
    have e2 : n * (n * r * n⁻¹) * n⁻¹ = n ^ 2 * r * (n ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev]; group
    rwa [e2] at h
  have hφrangeR : φ.range = R 0 := by rw [hφrange, ← hR0Y]
  have hφX0Y : ∀ X : SL(3, L), φ X ∈ Y i₀ := by
    intro X
    rw [← hφrange]
    exact ⟨X, rfl⟩
  have hφX0 : ∀ X : SL(3, L), φ X ∈ R 0 := by
    intro X
    rw [← hφrangeR]
    exact ⟨X, rfl⟩
  have hcomm0 : ∀ r ∈ φ.range, ∀ s ∈ φ.range, Commute r (n * s * n⁻¹) := by
    intro r hr s hs
    have hr0 : r ∈ R 0 := by rwa [hφrangeR] at hr
    have hs0 : s ∈ R 0 := by rwa [hφrangeR] at hs
    exact hRcomm 0 1 (by decide) r hr0 _ (hmemR1 s hs0)
  let Δ : SL(3, L) →* ModGL .E6 L :=
    { toFun := fun X => cycConjDiag n (φ X)
      map_one' := by simp [cycConjDiag]
      map_mul' := fun X Y =>
        by simpa only [map_mul] using
          cycConjDiag_mul n φ.range hn3 hcomm0 ⟨X, rfl⟩ ⟨Y, rfl⟩ }
  have hXeq_of_mem : ∀ X : SL(3, L), X ∈ Δ.ker →
      φ X = ((n * φ X * n⁻¹) * (n ^ 2 * φ X * (n ^ 2)⁻¹))⁻¹ := by
    intro X hX
    have h : φ X * ((n * φ X * n⁻¹) * (n ^ 2 * φ X * (n ^ 2)⁻¹)) = 1 := by
      rw [← mul_assoc]
      exact hX
    exact eq_inv_of_mul_eq_one_left h
  have hcentral_of_mem : ∀ X : SL(3, L), X ∈ Δ.ker →
      ∀ Z : SL(3, L), Commute (φ X) (φ Z) := by
    intro X hX Z
    have hXeq := hXeq_of_mem X hX
    have hA : n * φ X * n⁻¹ ∈ R 1 := hmemR1 (φ X) (hφX0 X)
    have hB : n ^ 2 * φ X * (n ^ 2)⁻¹ ∈ R 2 := hmemR2 (φ X) (hφX0 X)
    have h1 : Commute (φ Z) (n * φ X * n⁻¹) := hRcomm 0 1 (by decide) _ (hφX0 Z) _ hA
    have h2 : Commute (φ Z) (n ^ 2 * φ X * (n ^ 2)⁻¹) := hRcomm 0 2 (by decide) _ (hφX0 Z) _ hB
    have h12 : Commute (φ Z) ((n * φ X * n⁻¹) * (n ^ 2 * φ X * (n ^ 2)⁻¹)) :=
      h1.mul_right h2
    rw [hXeq]
    exact h12.inv_right.symm
  have hΔker : Δ.ker ≤ Subgroup.center SL(3, L) := by
    intro X hX
    have hcommXZ : ∀ Z : SL(3, L), ⁅X, Z⁆ ∈ φ.ker := by
      intro Z
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hcentral_of_mem X hX Z).eq
    have hcenterXZ : ∀ Z : SL(3, L), ⁅X, Z⁆ ∈ Subgroup.center SL(3, L) :=
      fun Z => hφker (hcommXZ Z)
    have hperf := CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 L (by norm_num)
    have hQsimple : IsSimpleGroup (SL(3, L) ⧸ Subgroup.center SL(3, L)) := hperf.2.1
    let Zc := Subgroup.center SL(3, L)
    let π : SL(3, L) →* SL(3, L) ⧸ Zc := QuotientGroup.mk' Zc
    have hπX_center : π X ∈ Subgroup.center (SL(3, L) ⧸ Zc) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨Z, rfl⟩ := QuotientGroup.mk'_surjective Zc q
      have hmem : ⁅X, Z⁆ ∈ Zc := hcenterXZ Z
      have hq : π ⁅X, Z⁆ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hmem
      rw [map_commutatorElement] at hq
      rw [commutatorElement_eq_one_iff_mul_comm] at hq
      exact hq.symm
    have hZbot : Subgroup.center (SL(3, L) ⧸ Zc) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (SL(3, L) ⧸ Zc)) with h | h
      · exact h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hperf.2.2
        exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
    have hπX : π X = 1 := by
      have hmem : π X ∈ (⊥ : Subgroup (SL(3, L) ⧸ Zc)) := by
        rw [← hZbot]
        exact hπX_center
      exact Subgroup.mem_bot.mp hmem
    have hXZ : X ∈ Zc := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπX
      exact hπX
    exact hXZ
  have hΔ_in_E : ∀ X : SL(3, L), Δ X ∈ ⨆ k, R k := by
    intro X
    have hA : n * φ X * n⁻¹ ∈ R 1 := hmemR1 (φ X) (hφX0 X)
    have hB : n ^ 2 * φ X * (n ^ 2)⁻¹ ∈ R 2 := hmemR2 (φ X) (hφX0 X)
    change φ X * (n * φ X * n⁻¹) * (n ^ 2 * φ X * (n ^ 2)⁻¹) ∈ ⨆ k, R k
    exact mul_mem (mul_mem (le_iSup R 0 (hφX0 X)) (le_iSup R 1 hA)) (le_iSup R 2 hB)
  have hE_adj : (⨆ k, R k) ≤ adjointGroup .E6 L := by
    refine iSup_le fun k => ?_
    exact (componentRootSpan_le L (e (m + k))).trans
      (rootSpan_le_adjointGroup L (kernelRoots (rootCharHom a)))
  have hΔ_adj : Δ.range ≤ adjointGroup .E6 L := by
    rintro g ⟨X, rfl⟩
    exact hE_adj (hΔ_in_E X)
  have hYd : ∀ i, Y i ≤
      Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) := by
    intro i
    exact (componentRootSpan_le L i).trans
      (rootSpan_le_centralizer_rootDiagUnit a (fun α hα => ⟨hα.1, hα.2⟩))
  have hconjd : (MulAut.conj n) (rootDiagUnit .E6 a) = rootDiagUnit .E6 a := by
    simp only [MulAut.conj_apply]
    calc n * rootDiagUnit .E6 a * n⁻¹ = (rootDiagUnit .E6 a * n) * n⁻¹ := by rw [← hdn]
      _ = rootDiagUnit .E6 a := by group
  have hconjd2 : (MulAut.conj (n ^ 2)) (rootDiagUnit .E6 a) = rootDiagUnit .E6 a := by
    simp only [MulAut.conj_apply]
    have hd2 : rootDiagUnit .E6 a * n ^ 2 = n ^ 2 * rootDiagUnit .E6 a := by
      rw [pow_two]
      calc rootDiagUnit .E6 a * (n * n) = (rootDiagUnit .E6 a * n) * n := by group
        _ = (n * rootDiagUnit .E6 a) * n := by rw [hdn]
        _ = n * (rootDiagUnit .E6 a * n) := by group
        _ = n * (n * rootDiagUnit .E6 a) := by rw [hdn]
        _ = (n * n) * rootDiagUnit .E6 a := by group
    calc n ^ 2 * rootDiagUnit .E6 a * (n ^ 2)⁻¹ =
        (rootDiagUnit .E6 a * n ^ 2) * (n ^ 2)⁻¹ := by rw [← hd2]
      _ = rootDiagUnit .E6 a := by group
  have hΔd : ∀ X : SL(3, L), Commute (rootDiagUnit .E6 a) (Δ X) := by
    intro X
    have hdu : Commute (rootDiagUnit .E6 a) (φ X) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hYd i₀ (hφX0Y X))).symm
    have hdA : Commute (rootDiagUnit .E6 a) (n * φ X * n⁻¹) := by
      have h := hdu.map (MulAut.conj n).toMonoidHom
      change Commute ((MulAut.conj n) (rootDiagUnit .E6 a))
        ((MulAut.conj n) (φ X)) at h
      rw [hconjd, show (MulAut.conj n) (φ X) = n * φ X * n⁻¹ from by
        simp [MulAut.conj_apply]] at h
      exact h
    have hdB : Commute (rootDiagUnit .E6 a) (n ^ 2 * φ X * (n ^ 2)⁻¹) := by
      have h := hdu.map (MulAut.conj (n ^ 2)).toMonoidHom
      change Commute ((MulAut.conj (n ^ 2)) (rootDiagUnit .E6 a))
        ((MulAut.conj (n ^ 2)) (φ X)) at h
      rw [hconjd2, show (MulAut.conj (n ^ 2)) (φ X) =
        n ^ 2 * φ X * (n ^ 2)⁻¹ from by rw [MulAut.conj_apply]] at h
      exact h
    show Commute (rootDiagUnit .E6 a) (cycConjDiag n (φ X))
    rw [cycConjDiag]
    exact (hdu.mul_right hdA).mul_right hdB
  have hΔn : ∀ X : SL(3, L), Commute n (Δ X) := by
    intro X
    have h := cycConjDiag_conj n φ.range hn3 hcomm0 (⟨X, rfl⟩ : φ X ∈ φ.range)
    exact mul_inv_eq_iff_eq_mul.mp h
  have hΔ_cent : Δ.range ≤ Subgroup.centralizer
      (((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
        Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L))) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr (fun X hX => ?_)
      obtain ⟨X', rfl⟩ := hX
      exact (hΔd X').symm
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr (fun X hX => ?_)
      obtain ⟨X', rfl⟩ := hX
      exact (hΔn X').symm
  have hΔrange : Δ.range ≤ adjointGroup .E6 L ⊓ Subgroup.centralizer
      (((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
        Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L))) :=
    le_inf hΔ_adj hΔ_cent
  have hrationalRoots : ∀ i : KernelComponent (rootCharHom a),
      rationalRoots S.ρ (rootCharHom a) i = rootCharKernel a := by
    intro i
    obtain ⟨ρb, hρb, -⟩ := ntpS4_frobPerm S a hT
    have hΨinj : Function.Injective (componentRoots (rootCharHom a)) := by
      intro i j h
      obtain ⟨β, hβ⟩ := Quotient.exists_rep i
      exact eq_of_mem_componentRoots
        (show (β : kernelRoots (rootCharHom a)).1 ∈ componentRoots (rootCharHom a) i from
          ⟨β.2, hβ⟩)
        (h ▸ (show (β : kernelRoots (rootCharHom a)).1 ∈
          componentRoots (rootCharHom a) i from ⟨β.2, hβ⟩))
    have horb' : ∀ j : KernelComponent (rootCharHom a),
        sInf {s : ℕ | 0 < s ∧ (⇑S.ρ)^[s] '' componentRoots (rootCharHom a) j =
          componentRoots (rootCharHom a) j} = 3 := fun j => horb j
    have hmain := ntpA2rat_orbitUnion_eq_iUnion (X := Fin Tag.E6.rank → ℤ) hI S.ρ
      (componentRoots (rootCharHom a)) hΨinj ρb hρb horb' i
    have hrat : rationalRoots S.ρ (rootCharHom a) i =
        {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
          δ ∈ componentRoots (rootCharHom a) i ∧ γ = (⇑S.ρ)^[k] δ} := rfl
    rw [hrat, hmain]
    ext α
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hαj⟩
      exact hαj.1
    · intro hα
      exact ⟨⟦⟨α, hα⟩⟧, ⟨hα, rfl⟩⟩
  have hspan_le : ∀ i : KernelComponent (rootCharHom a),
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        rootSpan .E6 L (rootCharKernel a) := by
    intro i
    have h1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        rationalSpan S.ρ S.Γ (rootCharHom a) i := by
      rw [rationalComponent]
      simpa only [sup_idem] using
        Subgroup.commutator_le_sup (rationalSpan S.ρ S.Γ (rootCharHom a) i)
          (rationalSpan S.ρ S.Γ (rootCharHom a) i)
    have h2 : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤
        rootSpan .E6 L (rootCharKernel a) := by
      rw [rationalSpan, hrationalRoots i]
      exact inf_le_left
    exact h1.trans h2
  have hroot_eq : rootSpan .E6 L (rootCharKernel a) = ⨆ i, Y i := by
    rw [show rootCharKernel a = kernelRoots (rootCharHom a) from rfl,
      ← iSup_componentRootSpan (K := L) (χ := rootCharHom a)]
  have hlayer_le : (⨆ i, rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ ⨆ k, R k := by
    refine iSup_le fun i => ?_
    exact (hspan_le i).trans (le_of_eq (hroot_eq.trans hEeq))
  have hJd : ∀ J : Subgroup (ModGL .E6 L),
      J ≤ S.Γ ⊓ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
        Subgroup.zpowers n : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) →
      CFSG.IsQuasisimple ↥J → J ≤ ⨆ k, R k := by
    intro J hJ hJq
    have hJΓ : J ≤ S.Γ := hJ.trans inf_le_left
    have hJcent : J ≤ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
        Subgroup.zpowers n : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) :=
      hJ.trans inf_le_right
    have hsub : ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) ⊆
        ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n :
          Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hJd : J ≤ Subgroup.centralizer
        ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) :=
      hJcent.trans (Subgroup.centralizer_le hsub)
    exact (hlayer J (le_inf hJΓ hJd) hJq).trans hlayer_le
  have hΔJ : ∀ J : Subgroup (ModGL .E6 L),
      J ≤ S.Γ ⊓ Subgroup.centralizer ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔
        Subgroup.zpowers n : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) →
      CFSG.IsQuasisimple ↥J → J ≤ Δ.range := by
    intro J hJ hJq
    have hJE : J ≤ ⨆ k, R k := hJd J hJ hJq
    have hJN : ∀ g ∈ J, n * g * n⁻¹ = g := by
      intro g hg
      have hmem := Subgroup.mem_centralizer_iff.mp (hJ.trans inf_le_right hg)
        n (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
      exact mul_inv_eq_iff_eq_mul.mpr hmem
    have hJ_le_comm : J ≤ ⁅J, J⁆ := by
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥J) ∈ ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ := by
        have h := hJq.1.commutator_eq_top
        change ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = ⊤ at h
        rw [h]; exact Subgroup.mem_top _
      have h := Subgroup.mem_map_of_mem J.subtype hmem
      rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    have hcomm_le : ⁅J, J⁆ ≤ Δ.range := by
      refine Subgroup.commutator_le.mpr (fun g₁ hg₁ g₂ hg₂ => ?_)
      obtain ⟨a₁, ha₁, z₁, hz₁, hg₁eq⟩ :=
        exists_eq_cycConjDiag_mul_of_fixed n hn3 hRcomm hconj (hJE hg₁) (hJN g₁ hg₁)
      obtain ⟨a₂, ha₂, z₂, hz₂, hg₂eq⟩ :=
        exists_eq_cycConjDiag_mul_of_fixed n hn3 hRcomm hconj (hJE hg₂) (hJN g₂ hg₂)
      obtain ⟨X₁, hX₁⟩ : ∃ X₁ : SL(3, L), φ X₁ = a₁ := by
        have hmem : a₁ ∈ φ.range := by rw [hφrange, ← hR0Y]; exact ha₁
        exact hmem
      obtain ⟨X₂, hX₂⟩ : ∃ X₂ : SL(3, L), φ X₂ = a₂ := by
        have hmem : a₂ ∈ φ.range := by rw [hφrange, ← hR0Y]; exact ha₂
        exact hmem
      have hΔX₁ : Δ X₁ = cycConjDiag n a₁ := by
        change cycConjDiag n (φ X₁) = cycConjDiag n a₁
        rw [hX₁]
      have hΔX₂ : Δ X₂ = cycConjDiag n a₂ := by
        change cycConjDiag n (φ X₂) = cycConjDiag n a₂
        rw [hX₂]
      have h1v : Commute z₁ (Δ X₂) :=
        (Subgroup.mem_centralizer_iff.mp hz₁.2 _ (hΔ_in_E X₂)).symm
      have h2u : Commute z₂ (Δ X₁) :=
        (Subgroup.mem_centralizer_iff.mp hz₂.2 _ (hΔ_in_E X₁)).symm
      have h12 : Commute z₁ z₂ :=
        (Subgroup.mem_centralizer_iff.mp hz₁.2 _ hz₂.1).symm
      rw [hg₁eq, hg₂eq, ← hΔX₁, ← hΔX₂]
      rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute h1v h12 h2u]
      rw [← map_commutatorElement]
      exact ⟨_, rfl⟩
    exact hJ_le_comm.trans hcomm_le
  have hconjpow : ∀ (k : ℕ) (j : KernelComponent (rootCharHom a)),
      (Y j).map (MulAut.conj (n ^ k)).toMonoidHom = Y ((σ ^ k) j) := by
    intro k
    induction k with
    | zero =>
        intro j
        rw [pow_zero, show MulAut.conj (1 : ModGL .E6 L) = 1 from map_one _]
        change Subgroup.map (MonoidHom.id (ModGL .E6 L)) (Y j) = Y j
        exact Subgroup.map_id (Y j)
    | succ k ih =>
        intro j
        have hmul : (MulAut.conj (n ^ (k + 1))).toMonoidHom =
            ((MulAut.conj (n ^ k)).toMonoidHom).comp ((MulAut.conj n).toMonoidHom) := by
          ext x
          simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply]
          rw [pow_succ]
          group
        rw [hmul, ← Subgroup.map_map, hσ j, ih (σ j)]
        congr 1
  have hσiter : ∀ t : Fin 3, (σ ^ (t : ℕ)) i₀ = e (m + t) := by
    intro t
    fin_cases t
    · change (σ ^ (0 : ℕ)) i₀ = e (m + 0)
      rw [pow_zero, add_zero]
      exact (e.apply_symm_apply i₀).symm
    · change (σ ^ (1 : ℕ)) i₀ = e (m + 1)
      rw [pow_one, show i₀ = e m from (e.apply_symm_apply i₀).symm, he m,
        finRotate_apply]
    · change (σ ^ (2 : ℕ)) i₀ = e (m + 2)
      have h1 : (σ ^ (1 : ℕ)) i₀ = e (m + 1) := by
        rw [pow_one, show i₀ = e m from (e.apply_symm_apply i₀).symm, he m,
          finRotate_apply]
      have h3 : (σ ^ (2 : ℕ)) i₀ = σ ((σ ^ (1 : ℕ)) i₀) := by
        rw [show (2 : ℕ) = 1 + 1 from by norm_num, pow_succ']
        rfl
      rw [h3, h1, he (m + 1), finRotate_apply]
      congr 1
      rw [show (2 : Fin 3) = 1 + 1 from by decide, add_assoc]
  have hclause6 : ∃ k : ℕ, ∀ y ∈ φ.range,
      n ^ k * S.D.step y * (n ^ k)⁻¹ ∈ φ.range := by
    obtain ⟨ρb, -, hρbspan⟩ := ntpS4_frobPerm S a hT
    obtain ⟨j₀, hj₀⟩ := henc_bij.surjective (ρb i₀)
    have hj₀' : (σ ^ (j₀ : ℕ)) i₀ = ρb i₀ := by
      rw [hσiter j₀]
      exact hj₀
    refine ⟨3 - (j₀ : ℕ), ?_⟩
    intro y hy
    have hyY : y ∈ Y i₀ := by rw [← hφrange]; exact hy
    have hstep_mem : S.D.step y ∈ Y (ρb i₀) := by
      have h : S.D.step y ∈ (Y i₀).map S.D.step := Subgroup.mem_map_of_mem _ hyY
      rwa [hρbspan i₀] at h
    have hstep_mem' : S.D.step y ∈ Y ((σ ^ (j₀ : ℕ)) i₀) := by
      rw [hj₀']; exact hstep_mem
    have hk : (σ ^ (3 - (j₀ : ℕ))) ((σ ^ (j₀ : ℕ)) i₀) = i₀ := by
      have hsum : 3 - (j₀ : ℕ) + (j₀ : ℕ) = 3 := by
        have := j₀.isLt
        omega
      calc (σ ^ (3 - (j₀ : ℕ))) ((σ ^ (j₀ : ℕ)) i₀)
          = (σ ^ ((3 - (j₀ : ℕ)) + (j₀ : ℕ))) i₀ := by rw [pow_add]; rfl
        _ = (σ ^ (3 : ℕ)) i₀ := by rw [hsum]
        _ = i₀ := by rw [hσ3]; rfl
    have hmap : (Y ((σ ^ (j₀ : ℕ)) i₀)).map
        (MulAut.conj (n ^ (3 - (j₀ : ℕ)))).toMonoidHom = Y i₀ := by
      rw [hconjpow (3 - (j₀ : ℕ)) ((σ ^ (j₀ : ℕ)) i₀)]
      rw [hk]
    have hm : n ^ (3 - (j₀ : ℕ)) * S.D.step y * (n ^ (3 - (j₀ : ℕ)))⁻¹ ∈
        (Y ((σ ^ (j₀ : ℕ)) i₀)).map
          (MulAut.conj (n ^ (3 - (j₀ : ℕ)))).toMonoidHom := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj (n ^ (3 - (j₀ : ℕ)))).toMonoidHom
        hstep_mem'
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
    rw [hmap] at hm
    rwa [hφrange]
  refine ⟨Δ, fun X => rfl, hΔker, hcomm0, hΔrange, hΔJ, hclause6⟩

end CFSG.StandardType.NTPlane
