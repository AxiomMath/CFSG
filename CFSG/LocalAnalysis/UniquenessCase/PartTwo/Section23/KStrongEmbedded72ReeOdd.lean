module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Walter.Models
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups Pointwise

theorem card_centralizer_ree
    {G : Type} [Group G] (a : ℕ) (ha : 1 ≤ a)
    (h : ReeTitsModel G .twistedG2 3 (2 * a + 1)) {x : G} (hx : orderOf x = 2) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) =
      2 * Nat.card (PSL(2, GaloisField 3 (2 * a + 1))) := by
  obtain ⟨-, -, hdecomp, -, -⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
      a ha G h
  obtain ⟨L, hLC, hinf, hsup, ⟨eL⟩, -⟩ := hdecomp x hx
  have hcardL : Nat.card ↥L = Nat.card (PSL(2, GaloisField 3 (2 * a + 1))) :=
    Nat.card_congr eL.toEquiv
  have hcardH : Nat.card ↥(Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, hx]
  have hHnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) := by
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (Subgroup.mem_centralizer_iff.1 (hLC hl) x (by simp)).symm
    exact (Subgroup.zpowers_le.2 hxcent).trans (Subgroup.centralizer_le_normalizer (L : Set G))
  have hcoe : (↑(Subgroup.zpowers x ⊔ L) : Set G) =
      (Subgroup.zpowers x : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHnorm
  let f : ↥(Subgroup.zpowers x) × ↥L → ↥(Subgroup.zpowers x ⊔ L) := fun p =>
    ⟨p.1.1 * p.2.1, by
      rw [← SetLike.mem_coe, hcoe]
      exact Set.mem_mul.mpr ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨h₁, l₁⟩ ⟨h₂, l₂⟩ hEq
      have hval : h₁.1 * l₁.1 = h₂.1 * l₂.1 := congrArg Subtype.val hEq
      have hmem : h₁.1⁻¹ * h₂.1 ∈ Subgroup.zpowers x ⊓ L := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · exact (Subgroup.zpowers x).mul_mem ((Subgroup.zpowers x).inv_mem h₁.2) h₂.2
        · have heq : h₁.1⁻¹ * h₂.1 = l₁.1 * l₂.1⁻¹ := by
            calc h₁.1⁻¹ * h₂.1
                = h₁.1⁻¹ * (h₂.1 * l₂.1) * l₂.1⁻¹ := by group
              _ = h₁.1⁻¹ * (h₁.1 * l₁.1) * l₂.1⁻¹ := by rw [← hval]
              _ = l₁.1 * l₂.1⁻¹ := by group
          rw [heq]
          exact L.mul_mem l₁.2 (L.inv_mem l₂.2)
      rw [hinf, Subgroup.mem_bot] at hmem
      have hh : h₁.1 = h₂.1 := by
        have := congrArg (fun y : G => h₁.1 * y) hmem
        simpa using this.symm
      have hl : l₁.1 = l₂.1 := by
        have := hval
        rw [hh] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext hh) (Subtype.ext hl)
    · rintro ⟨z, hz⟩
      rw [← SetLike.mem_coe, hcoe] at hz
      obtain ⟨h, hh, l, hl, rfl⟩ := Set.mem_mul.1 hz
      exact ⟨(⟨h, hh⟩, ⟨l, hl⟩), Subtype.ext rfl⟩
  have hcard : Nat.card ↥(Subgroup.zpowers x ⊔ L) =
      Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥L := by
    calc Nat.card ↥(Subgroup.zpowers x ⊔ L)
        = Nat.card (↥(Subgroup.zpowers x) × ↥L) :=
          Nat.card_congr (Equiv.ofBijective f hbij).symm
      _ = Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥L := Nat.card_prod _ _
  rw [← hsup, hcard, hcardH, hcardL]

theorem card_centralizer_walterJ1
    {G : Type} [Group G] [Finite G] (e : G ≃* CFSG.Open.walterJ1) {x : G}
    (hx : orderOf x = 2) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 120 :=
  (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free
    ⟨e.trans CFSG.Walter.walterJ1EquivNative⟩ x hx).1

theorem outer_trivial_of_mulEquiv_walterJ1
    {G : Type} [Group G] [Finite G]
    (e : G ≃* CFSG.Open.walterJ1) : Nat.card (Outer G) = 1 := by
  have h := (CFSG.Sporadic.Schreier.at_j1_schreier).1
  rw [← h]
  exact Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (e.trans CFSG.Walter.walterJ1EquivNative)).toEquiv

theorem odd_card_outer_ree
    {G : Type} [Group G] (a : ℕ) (ha : 1 ≤ a)
    (h : ReeTitsModel G .twistedG2 3 (2 * a + 1)) : Odd (Nat.card (Outer G)) :=
  (CFSG.ComponentClassification.LiteratureLocal.ward_kleidman_small_Ree_involution_centralizer_maximal
    a ha G h).2.2.2.2.2.2

theorem ree_case_false
    {X : Type} [Group X] [Finite X] {L K : Subgroup X}
    (hKL : K ≤ L) (hKn : K.Normal) (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    [hKs : IsSimpleGroup ↥K]
    {t : ↥L} (ht : orderOf t = 2)
    (hC24 : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥L)) = 24)
    (a : ℕ) (ha : 1 ≤ a) (hRee : ReeTitsModel ↥K .twistedG2 3 (2 * a + 1)) : False := by
  classical
  haveI : K.Normal := hKn
  let ψ : ↥L →* Outer ↥K :=
    (QuotientGroup.mk' (inner ↥K)).comp
      ((MulAut.conjNormal (H := K)).comp L.subtype)
  have hker_conj : ∀ y : X, MulAut.conjNormal (H := K) y = 1 → y = 1 := by
    intro y hy
    have hyc : y ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h := congrArg (fun f : MulAut ↥K => ((f ⟨m, hm⟩ : ↥K) : X)) hy
      simp only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_one] at h
      have h' : y * m = m * y := by
        have := congrArg (fun z : X => z * y) h
        simpa [mul_assoc] using this
      exact h'.symm
    rw [hKC, Subgroup.mem_bot] at hyc
    exact hyc
  have hmem_iff : ∀ x : ↥L, MulAut.conjNormal (H := K) (x : X) ∈ inner ↥K ↔
      (x : X) ∈ K := by
    intro x
    constructor
    · rintro ⟨k, hk⟩
      have hrel : MulAut.conjNormal (H := K) ((k : X)⁻¹ * (x : X)) = 1 := by
        rw [map_mul (MulAut.conjNormal (H := K)), map_inv (MulAut.conjNormal (H := K)),
          ← hk, MulAut.conjNormal_val]
        simp
      have h1 : (k : X)⁻¹ * (x : X) = 1 := hker_conj _ hrel
      have hx : (x : X) = (k : X) := by
        have := congrArg (fun z : X => (k : X) * z) h1
        simpa using this
      exact hx ▸ k.2
    · intro hx
      exact ⟨⟨(x : X), hx⟩, MulAut.conjNormal_val.symm⟩
  have hker : ψ.ker = K.subgroupOf L := by
    ext x
    change (QuotientGroup.mk (MulAut.conjNormal (H := K) (x : X)) : Outer ↥K) = 1 ↔
      x ∈ K.subgroupOf L
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hmem_iff x
  let eQ : (↥L ⧸ K.subgroupOf L) ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ψ)
  have hOddOut : Odd (Nat.card (Outer ↥K)) :=
    odd_card_outer_ree a ha hRee
  have hOddQ : Odd (Nat.card (↥L ⧸ K.subgroupOf L)) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact Odd.of_dvd_nat hOddOut (by simpa using Subgroup.card_dvd_of_le (le_top :
      ψ.range ≤ (⊤ : Subgroup (Outer ↥K))))
  have htQ : QuotientGroup.mk' (K.subgroupOf L) t = 1 := by
    have hdvd2 : orderOf (QuotientGroup.mk' (K.subgroupOf L) t) ∣ 2 := by
      have := orderOf_map_dvd (QuotientGroup.mk' (K.subgroupOf L)) t
      rwa [ht] at this
    have hodd : Odd (orderOf (QuotientGroup.mk' (K.subgroupOf L) t)) :=
      Odd.of_dvd_nat hOddQ (orderOf_dvd_natCard _)
    have h1 : orderOf (QuotientGroup.mk' (K.subgroupOf L) t) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by norm_num)
    exact orderOf_eq_one_iff.1 h1
  have htK : t ∈ K.subgroupOf L := (QuotientGroup.eq_one_iff t).1 htQ
  have htXK : (t : X) ∈ K := Subgroup.mem_subgroupOf.1 htK
  let tK : ↥K := ⟨(t : X), htXK⟩
  have htK_order : orderOf tK = 2 := by
    rw [← Subgroup.orderOf_coe tK]
    change orderOf ((t : ↥L) : X) = 2
    rw [Subgroup.orderOf_coe t, ht]
  let imb : ↥(Subgroup.centralizer ({tK} : Set ↥K)) →
      ↥(Subgroup.centralizer ({t} : Set ↥L)) := fun y =>
    ⟨⟨((y.1 : ↥K) : X), hKL (y.1 : ↥K).2⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy := Subgroup.mem_centralizer_singleton_iff.1 y.2
      have hy' := congrArg (fun z : ↥K => (z : X)) hy
      apply Subtype.ext
      simpa [tK, Subgroup.coe_mul] using hy'⟩
  have himb : Function.Injective imb := by
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ↥(Subgroup.centralizer ({t} : Set ↥L)) =>
      ((w.1 : ↥L) : X)) hyz
  have hcardK : Nat.card ↥(Subgroup.centralizer ({tK} : Set ↥K)) =
      2 * Nat.card (PSL(2, GaloisField 3 (2 * a + 1))) :=
    card_centralizer_ree a ha hRee htK_order
  have hle : Nat.card ↥(Subgroup.centralizer ({tK} : Set ↥K)) ≤
      Nat.card ↥(Subgroup.centralizer ({t} : Set ↥L)) :=
    Nat.card_le_card_of_injective imb himb
  have hpsl_ge : 168 ≤ Nat.card (PSL(2, GaloisField 3 (2 * a + 1))) := by
    have hm : 2 * a + 1 ≠ 0 := by omega
    have hq : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
      GaloisField.card 3 (2 * a + 1) hm
    have hodd : Odd (Nat.card (GaloisField 3 (2 * a + 1))) := by
      rw [hq]
      exact Odd.pow (n := 2 * a + 1) (by norm_num)
    have h27 : 27 ≤ Nat.card (GaloisField 3 (2 * a + 1)) := by
      rw [hq]
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases CFSG.ABGLocalTools.psl2_card_cases
        (K := GaloisField 3 (2 * a + 1)) hodd with h3 | h5 | hge
    · omega
    · omega
    · exact hge
  omega

theorem j1_case_false
    {X : Type} [Group X] [Finite X] {L K : Subgroup X}
    (hKL : K ≤ L) (hKn : K.Normal) (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    [hKs : IsSimpleGroup ↥K]
    {t : ↥L} (ht : orderOf t = 2)
    (hC24 : Nat.card ↥(Subgroup.centralizer ({t} : Set ↥L)) = 24)
    (eJ : ↥K ≃* CFSG.Open.walterJ1) : False := by
  classical
  haveI : K.Normal := hKn
  let ψ : ↥L →* Outer ↥K :=
    (QuotientGroup.mk' (inner ↥K)).comp
      ((MulAut.conjNormal (H := K)).comp L.subtype)
  have hker_conj : ∀ y : X, MulAut.conjNormal (H := K) y = 1 → y = 1 := by
    intro y hy
    have hyc : y ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h := congrArg (fun f : MulAut ↥K => ((f ⟨m, hm⟩ : ↥K) : X)) hy
      simp only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_one] at h
      have h' : y * m = m * y := by
        have := congrArg (fun z : X => z * y) h
        simpa [mul_assoc] using this
      exact h'.symm
    rw [hKC, Subgroup.mem_bot] at hyc
    exact hyc
  have hmem_iff : ∀ x : ↥L, MulAut.conjNormal (H := K) (x : X) ∈ inner ↥K ↔
      (x : X) ∈ K := by
    intro x
    constructor
    · rintro ⟨k, hk⟩
      have hrel : MulAut.conjNormal (H := K) ((k : X)⁻¹ * (x : X)) = 1 := by
        rw [map_mul (MulAut.conjNormal (H := K)), map_inv (MulAut.conjNormal (H := K)),
          ← hk, MulAut.conjNormal_val]
        simp
      have h1 : (k : X)⁻¹ * (x : X) = 1 := hker_conj _ hrel
      have hx : (x : X) = (k : X) := by
        have := congrArg (fun z : X => (k : X) * z) h1
        simpa using this
      exact hx ▸ k.2
    · intro hx
      exact ⟨⟨(x : X), hx⟩, MulAut.conjNormal_val.symm⟩
  have hker : ψ.ker = K.subgroupOf L := by
    ext x
    change (QuotientGroup.mk (MulAut.conjNormal (H := K) (x : X)) : Outer ↥K) = 1 ↔
      x ∈ K.subgroupOf L
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hmem_iff x
  have hOut : Nat.card (Outer ↥K) = 1 := outer_trivial_of_mulEquiv_walterJ1 eJ
  haveI : Subsingleton (Outer ↥K) :=
    Finite.card_le_one_iff_subsingleton.1 (by rw [hOut])
  have htop : ψ.ker = ⊤ := by
    apply eq_top_iff.2
    intro x _
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hLK : L ≤ K :=
    Subgroup.subgroupOf_eq_top.1 (by rw [← hker, htop])
  have hLeqK : L = K := le_antisymm hLK hKL
  subst hLeqK
  have hcard := card_centralizer_walterJ1 eJ ht
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
