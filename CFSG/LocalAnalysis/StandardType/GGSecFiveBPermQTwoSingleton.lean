module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoSingletonNative
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCrossing
public import CFSG.GroupTheory.GLS2.GroupTheory.Residuals
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLGenerate
import CFSG.Quasithin.Background.G2SL2
import CFSG.Quasithin.H13.A5X1367i
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Line
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLFrameSwap
public import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
import CFSG.Dihedral.FourgroupCycleControl
import CFSG.Dihedral.OriginalCentralizerOddCore
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.Quasithin.Background.A1cA132Action
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B4Dual
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.E4Solv
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.F9Sixteen
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.Background.InternalSecFF
import CFSG.Quasithin.Background.InternalSecRealB
import CFSG.Quasithin.Background.ThreePrimeGroup
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153Nine
import CFSG.Quasithin.EmptyFaithful.SzN17Dig
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5X1367e
import CFSG.Quasithin.H13.A5X1367g
import CFSG.Quasithin.H13.StatementsL3
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecA1012Two
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts04
import CFSG.Quasithin.Vol2.Ch11SecAVi2
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType

open Polynomial Matrix CoordSL Multiplicative Subgroup CFSG.RankThree.CALinearPlane
  CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

@[expose] def ggQTwoSingleton {G : Type} [Group G] {n : ℕ} (d : ℕ)
    (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i j : Fin n) :
    Subgroup G :=
  let C := ggBlockComm Bs eta {i, j} ⊓ centralizer (ggBlockComm Bs eta {j} : Set G)
  if d = 0 then oPrimeResidualOf 2 C else C

theorem ggQTwoSingleton_map_conj {G : Type} [Group G] [Finite G] {n : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (d : ℕ) (i j : Fin n) :
    (ggQTwoSingleton d Bs eta i j).map (MulAut.conj g).toMonoidHom =
      ggQTwoSingleton d Bs eta (τ i) (τ j) := by
  have hp : (ggBlockComm Bs eta {i, j}).map (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta {τ i, τ j} := by
    simpa only [Set.image_insert_eq, Set.image_singleton] using
      ggBlockComm_map_conj hg hτ ({i, j} : Set (Fin n))
  have hs : (ggBlockComm Bs eta {j}).map (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta {τ j} := by
    simpa only [Set.image_singleton] using ggBlockComm_map_conj hg hτ ({j} : Set (Fin n))
  have hc : (ggBlockComm Bs eta {i, j} ⊓ centralizer (ggBlockComm Bs eta {j} : Set G)).map
        (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta {τ i, τ j} ⊓ centralizer (ggBlockComm Bs eta {τ j} : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ublk_centralizer_map_conj, hp, hs]
  unfold ggQTwoSingleton
  by_cases hd : d = 0
  · simp only [if_pos hd]
    rw [CFSG.SecondGeneration.map_oPrimeResidualOf_eq, hc]
  · simpa only [if_neg hd] using hc

@[expose] def ggQTwoIndependentSingleton {G : Type} [Group G] {n : ℕ} (d : ℕ)
    (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i : Fin n) :
    Subgroup G :=
  ⨆ j : Fin n, ⨆ (_ : i ≠ j), ggQTwoSingleton d Bs eta i j

theorem ggQTwoIndependentSingleton_map_conj {G : Type} [Group G] [Finite G] {n : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (d : ℕ) (i : Fin n) :
    (ggQTwoIndependentSingleton d Bs eta i).map (MulAut.conj g).toMonoidHom =
      ggQTwoIndependentSingleton d Bs eta (τ i) := by
  unfold ggQTwoIndependentSingleton
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hij => ?_
    rw [ggQTwoSingleton_map_conj hg hτ]
    exact le_iSup_of_le (τ j) (le_iSup_of_le (fun h => hij (τ.injective h)) le_rfl)
  · refine iSup_le fun j => iSup_le fun hij => ?_
    obtain ⟨k, rfl⟩ := τ.surjective j
    have hik : i ≠ k := fun h => hij (congrArg τ h)
    refine le_iSup_of_le k ?_
    rw [Subgroup.map_iSup]
    exact le_iSup_of_le hik (by rw [ggQTwoSingleton_map_conj hg hτ])

namespace QTwoSingleton

private theorem coordZeroOn_antitone {G : Type} [Group G] {n : ℕ}
    (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3)))
    {S T : Set (Fin n)} (hST : S ⊆ T) : ggBsCoordZeroOn Bs eta T ≤ ggBsCoordZeroOn Bs eta S := by
  intro x hx
  obtain ⟨hb, h⟩ := mem_ggBsCoordZeroOn.mp hx
  exact mem_ggBsCoordZeroOn.mpr ⟨hb, fun i hi => h i (hST hi)⟩

private theorem coordBlockSL_map_card_and_derived {G : Type} [Group G]
    {m : ℕ} (κ : SL(m, ZMod 2) →* G) (hκ : Function.Injective κ)
    (I : Finset (Fin m)) (hI : I.card = 2) :
    Nat.card ((coordBlockSL (ZMod 2) I).map κ) = 6 ∧
      Nat.card (⁅(coordBlockSL (ZMod 2) I).map κ, (coordBlockSL (ZMod 2) I).map κ⁆ : Subgroup G) = 3 := by
  let φ := κ.comp (blockSLOn (ZMod 2) I)
  have hφ : Function.Injective φ := hκ.comp (blockSLOn_injective (k := ZMod 2) I)
  have hR : (coordBlockSL (ZMod 2) I).map κ = φ.range := by
    dsimp only [φ]
    rw [MonoidHom.range_comp, range_blockSLOn]
  have hD : Nat.card (SL(I.card, ZMod 2)) = 6 := by
    rw [hI]
    exact CFSG.Quasithin.SL2Model.card_SL2_of_card_two (Nat.card_zmod 2)
  have hDC : Nat.card (commutator SL(I.card, ZMod 2)) = 3 := by
    rw [hI, CFSG.Quasithin.SL2Model.commutator_eq_zpowers_c3 (Nat.card_zmod 2),
      Nat.card_zpowers, CFSG.Quasithin.SL2Model.orderOf_c3]
  have hderived : ⁅(coordBlockSL (ZMod 2) I).map κ, (coordBlockSL (ZMod 2) I).map κ⁆ =
      (commutator SL(I.card, ZMod 2)).map φ := by
    rw [hR, MonoidHom.range_eq_map, _root_.commutator_def, Subgroup.map_commutator]
  constructor
  · rw [hR, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact hD
  · rw [hderived, ← Nat.card_congr (Subgroup.equivMapOfInjective _ φ hφ).toEquiv]
    exact hDC

private theorem eq_one_of_central_coordBlockSL_map {G : Type} [Group G]
    {m : ℕ} (κ : SL(m, ZMod 2) →* G) (hκ : Function.Injective κ)
    (I : Finset (Fin m)) {z : G} (hz : z ∈ (coordBlockSL (ZMod 2) I).map κ)
    (hc : ∀ x ∈ (coordBlockSL (ZMod 2) I).map κ, z * x = x * z) : z = 1 := by
  let φ := κ.comp (blockSLOn (ZMod 2) I)
  have hφ : Function.Injective φ := hκ.comp (blockSLOn_injective (k := ZMod 2) I)
  have hR : (coordBlockSL (ZMod 2) I).map κ = φ.range := by
    dsimp only [φ]
    rw [MonoidHom.range_comp, range_blockSLOn]
  rw [hR] at hz
  obtain ⟨u, rfl⟩ := hz
  have hu : u ∈ Subgroup.center SL(I.card, ZMod 2) := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hφ
    rw [map_mul, map_mul]
    exact (hc (φ v) (hR ▸ ⟨v, rfl⟩)).symm
  rw [LineL2.center_eq_bot_two (Nat.card_zmod 2), Subgroup.mem_bot] at hu
  rw [hu, map_one]

private theorem map_inf_centralizer_zpowers_eq {A G : Type} [Group A] [Group G]
    (φ : A →* G) (hφ : Function.Injective φ) (R : Subgroup A) (z : A) :
    R.map φ ⊓ centralizer (Subgroup.zpowers (φ z) : Set G) =
      (R ⊓ centralizer ({z} : Set A)).map φ := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    refine ⟨u, ⟨hu, ?_⟩, rfl⟩
    change u ∈ centralizer ({z} : Set A)
    rw [mem_centralizer_singleton_iff]
    apply hφ
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    refine ⟨⟨u, hu, rfl⟩, ?_⟩
    change φ u ∈ centralizer ({φ z} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hcomm : u * z = z * u := mem_centralizer_singleton_iff.mp hc
    rw [← map_mul, ← map_mul, hcomm]

end QTwoSingleton

namespace GGSecFiveBPermQTwoKFrame

variable {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n r m d : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin (r + 2) ≃ Fin n}
  {g : (ZMod 2)[X]} [Fact (Irreducible g)]
  {ε : Fin m ≃ (Fin (rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
  {hC : (rootMat g).det = 1} {hCp : rootMat g ^ 3 = 1} {κ : SL(m, ZMod 2) →* G}
  (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)

include hF

theorem pairComm
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (i j : Fin (r + 1)) (hij : i ≠ j) :
    ggBlockComm Bs eta {π i.succ, π j.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset (Fin (r + 1)))ᶜ)).map κ := by
  have hdim : (rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) (by decide) hF.2.2.1
      ⟨1, by rw [Nat.card_zmod]⟩
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega : 2 < r + 1)
  have hS : ({i, j} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hk : k ∈ ({i, j} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ k
    simp [hki, hkj] at hk
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton] using hF.blockComm hBs hyB hK (S := {i, j})
    ⟨i, by simp⟩ hS (by rw [QTwoBlocks.card_fixS_compl, hdim]; simp [hij]; omega)

theorem singletonComm_even
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d = 0) (j : Fin (r + 1)) :
    ggBlockComm Bs eta {π j.succ} =
      Subgroup.zpowers (frameHom κ 1 ε hC hCp (ofAdd (Pi.single j 1))) := by
  classical
  let J : Finset (Fin m) := SLNS.fixS ε ({j} : Finset (Fin (r + 1)))ᶜ
  let R := (coordBlockSL (ZMod 2) J).map κ
  let z := frameHom κ 1 ε hC hCp (ofAdd (Pi.single j 1))
  let T := Subgroup.zpowers z
  let Y := ggBlockComm Bs eta {π j.succ}
  let H := ggBsCoordZeroOn Bs eta {π j.succ}
  let C := Subgroup.centralizer (H : Set G)
  have hdim : (rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) (by decide) hF.2.2.1
      ⟨1, by rw [Nat.card_zmod]⟩
  have hJ : J.card = 2 := by
    dsimp only [J]
    rw [QTwoBlocks.card_fixS_compl, hdim, hd]
    simp
  obtain ⟨i, hij, -⟩ := Fin.exists_ne_and_ne_of_two_lt j j (by omega : 2 < r + 1)
  obtain ⟨k, hkj, hki⟩ := Fin.exists_ne_and_ne_of_two_lt j i (by omega : 2 < r + 1)
  have hji := hF.pairComm hBs hyB hK hr j i hij.symm
  have hjk := hF.pairComm hBs hyB hK hr j k hkj.symm
  have hsets : SLNS.fixS ε ({j, i} : Finset (Fin (r + 1)))ᶜ ∩
      SLNS.fixS ε ({j, k} : Finset (Fin (r + 1)))ᶜ = J := by
    ext p
    rcases hεp : ε p with ⟨a, l⟩ | w
    · simp only [J, Finset.mem_inter, SLNS.mem_fixS, SLNS.inT, hεp, Sum.elim_inl,
        Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · simp [J, SLNS.mem_fixS, SLNS.inT, hεp]
  have hRpair : ggBlockComm Bs eta {π j.succ, π i.succ} ⊓
      ggBlockComm Bs eta {π j.succ, π k.succ} = R := by
    rw [hji, hjk, ← Subgroup.map_inf _ _ κ hF.1, CFSG.RankThree.CALinearPlane.coordBlockSL_inf, hsets]
  have hCpair (S : Set (Fin n)) (hS : {π j.succ} ⊆ S) :
      C ≤ Subgroup.normalizer (ggBlockComm Bs eta S : Set G) := by
    have hle : C ≤ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) :=
      Subgroup.centralizer_le (QTwoSingleton.coordZeroOn_antitone Bs eta hS)
    exact hle.trans (Subgroup.normalizer_commutator_ge_left
      (H₁ := Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G)) (H₂ := Bs))
  have hCR : C ≤ Subgroup.normalizer (R : Set G) := by
    rw [← hRpair]
    exact (le_inf (hCpair _ (by simp [Set.singleton_subset_iff]))
      (hCpair _ (by simp [Set.singleton_subset_iff]))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hzR : z ∈ R := by
    change frameHom κ 1 ε hC hCp _ ∈ (coordBlockSL (ZMod 2) J).map κ
    rw [frameHom_single]
    exact ⟨_, QTwoBlocks.nsSL_mem_coordBlockSL ε hC (fun a ha => by
      simp only [SLNS.kT, Finset.mem_singleton]
      simp [show a ≠ j from fun h => ha (h ▸ Finset.mem_singleton_self j)]), rfl⟩
  have hTR : T ≤ R := Subgroup.zpowers_le.mpr hzR
  have hzB : z ∈ Bs := hF.frameHom_mem_Bs hBs _
  have hTB : T ≤ Bs := Subgroup.zpowers_le.mpr hzB
  have hzne : z ≠ 1 := by
    intro h
    have h1 := hF.frameHom_injective (h.trans (map_one _).symm)
    have h2 := congrFun (congrArg toAdd h1) j
    simp at h2
  have hzo : orderOf z = 3 := orderOf_eq_prime (CoordSL.frameHom_pow_p κ 1 ε hC hCp _) hzne
  have hTcard : Nat.card T = 3 := by
    dsimp only [T]
    rw [Nat.card_zpowers, hzo]
  obtain ⟨hRcard, hRderived⟩ := QTwoSingleton.coordBlockSL_map_card_and_derived κ hF.1 J hJ
  have hRT : ⁅R, R⁆ = T := CFSG.Quasithin.H13.A5.eq_of_card_three_of_le hRcard
    (Subgroup.commutator_le_self R) hTR hRderived hTcard
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := by
    intro c hc
    rw [← hRT]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCR hc)]
  have hBscomm (a b : G) (ha : a ∈ Bs) (hb : b ∈ Bs) : a * b = b * a := by
    have h : (⟨a, ha⟩ : Bs) * ⟨b, hb⟩ = (⟨b, hb⟩ : Bs) * ⟨a, ha⟩ :=
      eta.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h
  have hgen : ∀ e ∈ Bs, ∃ h ∈ H, ∃ w ∈ T, e = h * w := by
    intro e he
    let b : Bs := ⟨e, he⟩
    let s : Multiplicative (Fin (r + 1) → ZMod 3) := ofAdd (Pi.single j 1)
    let c : ZMod 3 := toAdd (ggSecFiveBPermQTwoCoords eta π b) j
    let w := frameHom κ 1 ε hC hCp (s ^ c.val)
    have hwB : w ∈ Bs := hF.frameHom_mem_Bs hBs _
    have hwT : w ∈ T := by
      change frameHom κ 1 ε hC hCp (s ^ c.val) ∈ Subgroup.zpowers z
      rw [map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
    have hwcoord : toAdd (ggSecFiveBPermQTwoCoords eta π ⟨w, hwB⟩) j = c := by
      rw [hF.coords_frameHom hBs, toAdd_pow]
      simp only [s, toAdd_ofAdd, Pi.smul_apply, Pi.single_eq_same]
      simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    have hhB : e * w⁻¹ ∈ Bs := Bs.mul_mem he (Bs.inv_mem hwB)
    refine ⟨e * w⁻¹, ?_, w, hwT, by group⟩
    have hHmem (b' : Bs) : (b' : G) ∈ H ↔
        toAdd (ggSecFiveBPermQTwoCoords eta π b') j = 0 := by
      simpa only [Finset.coe_singleton, Set.image_singleton, Finset.mem_singleton, forall_eq]
        using (mem_coordZeroOn_iff (eta := eta) (π := π) (S := {j}) b')
    rw [show e * w⁻¹ = ((b * (⟨w, hwB⟩ : Bs)⁻¹ : Bs) : G) from rfl, hHmem,
      coords_mul, coords_inv, toAdd_mul, toAdd_inv]
    change c + -toAdd (ggSecFiveBPermQTwoCoords eta π ⟨w, hwB⟩) j = 0
    rw [hwcoord]
    exact add_neg_cancel c
  have hYT : Y ≤ T := by
    change ⁅C, Bs⁆ ≤ T
    rw [Subgroup.commutator_le]
    intro c hc e he
    obtain ⟨h, hh, w, hw, rfl⟩ := hgen e he
    have hch : c * h = h * c := (Subgroup.mem_centralizer_iff.mp hc h hh).symm
    have hcw : ⁅c, w⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCT hc) w).mp hw) (T.inv_mem hw)
    have hword : ⁅c, h * w⁆ = h * ⁅c, w⁆ * h⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, ← mul_assoc c h w, hch]
      group
    have hfix : h * ⁅c, w⁆ * h⁻¹ = ⁅c, w⁆ := by
      rw [hBscomm h _ (ggBsCoordZeroOn_le _ _ _ hh) (hTB hcw)]
      group
    rwa [hword, hfix]
  have hRC : R ≤ C := by
    simpa only [Finset.coe_singleton, Set.image_singleton] using
      hF.block_le_centralizer_coordZeroOn ({j} : Finset (Fin (r + 1)))
  obtain ⟨v, hvR, hvnc⟩ : ∃ v ∈ R, v * z ≠ z * v := by
    by_contra h
    push Not at h
    exact hzne (QTwoSingleton.eq_one_of_central_coordBlockSL_map κ hF.1 J hzR
      (fun x hx => (h x hx).symm))
  have hwY : ⁅v, z⁆ ∈ Y := Subgroup.commutator_mem_commutator (hRC hvR) hzB
  have hwne : ⁅v, z⁆ ≠ 1 := by
    intro h
    apply hvnc
    calc v * z = (⁅v, z⁆ * z) * v := by rw [commutatorElement_def]; group
      _ = z * v := by rw [h, one_mul]
  let _ : Nontrivial Y := ⟨⟨⟨⁅v, z⁆, hwY⟩, 1, fun h => hwne (congrArg Subtype.val h)⟩⟩
  have hdiv : Nat.card Y ∣ 3 := by simpa only [hTcard] using Subgroup.card_dvd_of_le hYT
  have hgt : 1 < Nat.card Y := Finite.one_lt_card
  have hYcard : Nat.card Y = 3 := ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left hgt.ne'
  exact Subgroup.eq_of_le_of_card_ge hYT (by rw [hYcard, hTcard])

theorem singleton_eq_native
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d ≤ 1) (i j : Fin (r + 1)) (hij : i ≠ j) :
    ggQTwoSingleton d Bs eta (π i.succ) (π j.succ) =
      (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {i})).map κ := by
  classical
  have hcoords : SLNS.fixS ε ({i} : Finset (Fin (r + 1)))ᶜ \ SLNS.fixS ε Finset.univ =
      CoordSL.frameBlockCoords ε {i} := by
    ext p
    rcases hεp : ε p with ⟨a, k⟩ | w <;>
      simp [SLNS.mem_fixS, SLNS.inT, CoordSL.frameBlockCoords, hεp]
  rw [← hcoords]
  have hdim : (rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two Nat.prime_three (by norm_num) (by decide) hF.2.2.1
      ⟨1, by rw [Nat.card_zmod]⟩
  have hpair := hF.pairComm hBs hyB hK hr i j hij
  by_cases hd0 : d = 0
  · have hsingle : ggBlockComm Bs eta {π j.succ} =
        Subgroup.zpowers (κ (SLNS.nsSL ε hC (SLNS.kT {j}))) := by
      simpa only [frameHom_single] using hF.singletonComm_even hBs hyB hK hr hd0 j
    have hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3 :=
      CoordSL.root_isPrimitiveRoot Nat.prime_three (by decide) hF.2.2.1
    have hs : ({i, j} \ {j} : Finset (Fin (r + 1))) = {i} := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hanchor : SLNS.fixS ε Finset.univ = ∅ := by
      ext p
      rcases hεp : ε p with ⟨a, k⟩ | w
      · simp [SLNS.mem_fixS, SLNS.inT, hεp]
      · have hw := w.isLt
        omega
    simp only [ggQTwoSingleton, if_pos hd0]
    rw [hpair, hsingle, QTwoSingleton.map_inf_centralizer_zpowers_eq κ hF.1,
      ← CFSG.SecondGeneration.map_oPrimeResidualOf_eq,
      QTwoSingletonNative.oPrimeResidualOf_inf_centralizer_nsSL_eq ε hprim, hs, hanchor,
      Finset.sdiff_empty]
  · have hd1 : d = 1 := by omega
    have hS : ({j} : Finset (Fin (r + 1))) ≠ Finset.univ := by
      intro h
      have hcard := congrArg Finset.card h
      simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    have hsingle : ggBlockComm Bs eta {π j.succ} =
        (coordBlockSL (ZMod 2) (SLNS.fixS ε ({j} : Finset (Fin (r + 1)))ᶜ)).map κ := by
      simpa only [Finset.coe_singleton, Set.image_singleton] using
        hF.blockComm hBs hyB hK (S := {j}) ⟨j, by simp⟩ hS
          (by rw [QTwoBlocks.card_fixS_compl, hdim, hd1]; simp)
    have hsets : SLNS.fixS ε ({i, j} : Finset (Fin (r + 1)))ᶜ \
        SLNS.fixS ε ({j} : Finset (Fin (r + 1)))ᶜ =
        SLNS.fixS ε ({i} : Finset (Fin (r + 1)))ᶜ \ SLNS.fixS ε Finset.univ := by
      ext p
      rcases hεp : ε p with ⟨a, k⟩ | w
      · simp only [Finset.mem_sdiff, SLNS.mem_fixS, SLNS.inT, hεp, Sum.elim_inl,
          Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ]
        aesop
      · simp [SLNS.mem_fixS, SLNS.inT, hεp]
    simp only [ggQTwoSingleton, if_neg hd0]
    rw [hpair, hsingle, coordBlockSL_map_inf_centralizer_eq_sdiff_of_card_two
      (Nat.card_zmod 2) κ hF.1 _ _ (by rw [QTwoBlocks.card_fixS_compl, hdim, hd1]; simp), hsets]

theorem singleton_independent
    {L : Subgroup G} {f : ℕ} {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d ≤ 1) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    ggQTwoSingleton d Bs eta i j = ggQTwoSingleton d Bs eta i k := by
  classical
  have active (x : Fin n) (hx : x ≠ π 0) : ∃ a : Fin (r + 1), π a.succ = x := by
    let b := π.symm x
    have hbne : b ≠ 0 := by
      intro h
      exact hx (by simpa only [b, Equiv.apply_symm_apply] using congrArg π h)
    have hbpos : 0 < b.val := by
      by_contra h
      have hbzero : b.val = 0 := by omega
      apply hbne
      apply Fin.ext
      simpa only [Fin.val_zero] using hbzero
    have hb := b.isLt
    let a : Fin (r + 1) := ⟨b.val - 1, by omega⟩
    have hsucc : a.succ = b := by
      apply Fin.ext
      dsimp only [a]
      simp only [Fin.val_succ]
      omega
    exact ⟨a, by rw [hsucc]; exact π.apply_symm_apply x⟩
  have localEq (x xj xk : Fin n) (hx : x ≠ π 0) (hxj : xj ≠ π 0) (hxk : xk ≠ π 0)
      (hxxj : x ≠ xj) (hxxk : x ≠ xk) :
      ggQTwoSingleton d Bs eta x xj = ggQTwoSingleton d Bs eta x xk := by
    obtain ⟨a, ha⟩ := active x hx
    obtain ⟨b, hb⟩ := active xj hxj
    obtain ⟨c, hc⟩ := active xk hxk
    have hab : a ≠ b := fun h => hxxj (ha.symm.trans ((congrArg (fun u => π u.succ) h).trans hb))
    have hac : a ≠ c := fun h => hxxk (ha.symm.trans ((congrArg (fun u => π u.succ) h).trans hc))
    rw [← ha, ← hb, ← hc, hF.singleton_eq_native hBs hyB hK hr hd a b hab,
      hF.singleton_eq_native hBs hyB hK hr hd a c hac]
  by_cases hjk : j = k
  · subst k
    rfl
  let a := π.symm i
  let b := π.symm j
  let c := π.symm k
  have hab : a ≠ b := fun h => hij (π.symm.injective h)
  have hac : a ≠ c := fun h => hik (π.symm.injective h)
  have hbc : b ≠ c := fun h => hjk (π.symm.injective h)
  obtain ⟨l, hl⟩ : ∃ l : Fin (r + 2), l ∉ ({a, b, c} : Finset (Fin (r + 2))) := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin (r + 2))) ⊆ {a, b, c} := fun x _ => h x
    have hcard := Finset.card_le_card hsub
    have htrip : ({a, b, c} : Finset (Fin (r + 2))).card = 3 := by simp [hab, hac, hbc]
    rw [Finset.card_univ, Fintype.card_fin, htrip] at hcard
    omega
  have hla : l ≠ a := fun h => hl (by simp [h])
  have hlb : l ≠ b := fun h => hl (by simp [h])
  have hlc : l ≠ c := fun h => hl (by simp [h])
  by_cases hl0 : l = 0
  · have outside (x : Fin n) (hxl : l ≠ π.symm x) : x ≠ π 0 := by
      intro h
      have hx : π.symm x = 0 := by rw [h, π.symm_apply_apply]
      exact hxl (hl0.trans hx.symm)
    exact localEq i j k (outside i hla) (outside j hlb) (outside k hlc) hij hik
  · obtain ⟨hg, hτ⟩ := hLF.permSL_swap_normalizer hBs hA (by omega : 1 ≤ r)
      (show (0 : Fin (r + 2)) ≠ l from fun h => hl0 h.symm)
    let w := σ (TypeA.permSL (Equiv.swap 0 l))
    let τ : Equiv.Perm (Fin n) := Equiv.swap (π 0) (π l)
    have outside (x : Fin n) (hxl : x ≠ π l) : τ x ≠ π 0 := by
      intro h
      have hx : x = π l := by simpa only [τ, Equiv.swap_apply_self, Equiv.swap_apply_left] using congrArg τ h
      exact hxl hx
    have hil : i ≠ π l := by intro h; exact hla (by simp only [a, h, Equiv.symm_apply_apply])
    have hjl : j ≠ π l := by intro h; exact hlb (by simp only [b, h, Equiv.symm_apply_apply])
    have hkl : k ≠ π l := by intro h; exact hlc (by simp only [c, h, Equiv.symm_apply_apply])
    apply Subgroup.map_injective (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective
    rw [ggQTwoSingleton_map_conj hg hτ, ggQTwoSingleton_map_conj hg hτ]
    exact localEq (τ i) (τ j) (τ k) (outside i hil) (outside j hjl) (outside k hkl)
      (fun h => hij (τ.injective h)) (fun h => hik (τ.injective h))

theorem singleton_map_conj_to_aux
    {L : Subgroup G} {f : ℕ} {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d ≤ 1) {w : G} (hw : w ∈ Subgroup.normalizer (Bs : Set G))
    {τ : Equiv.Perm (Fin n)} (hτ : MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ)
    (i j k : Fin n) (hij : i ≠ j) (hik : τ i ≠ k) :
    (ggQTwoSingleton d Bs eta i j).map (MulAut.conj w).toMonoidHom =
      ggQTwoSingleton d Bs eta (τ i) k :=
  (ggQTwoSingleton_map_conj hw hτ d i j).trans
    (hF.singleton_independent hLF hA hBs hyB hK hr hd (τ i) (τ j) k
      (fun h => hij (τ.injective h)) hik)

theorem independentSingleton_eq_aux
    {L : Subgroup G} {f : ℕ} {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    ggQTwoIndependentSingleton d Bs eta i = ggQTwoSingleton d Bs eta i j := by
  unfold ggQTwoIndependentSingleton
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hik => ?_
    rw [hF.singleton_independent hLF hA hBs hyB hK hr hd i k j hik hij]
  · exact le_iSup_of_le j (le_iSup_of_le hij le_rfl)

theorem exists_singleton_family
    {L : Subgroup G} {f : ℕ} {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod 3) →* (GaloisField 2 f)ˣ}
    (hLF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n 3)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hr : 2 ≤ r) (hd : d ≤ 1) :
    ∃ S : Fin n → Subgroup G,
      (∀ a : Fin (r + 1), S (π a.succ) =
        (coordBlockSL (ZMod 2) (CoordSL.frameBlockCoords ε {a})).map κ) ∧
      ∀ (w : G) (hw : w ∈ Subgroup.normalizer (Bs : Set G)) (τ : Equiv.Perm (Fin n)),
        MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut τ →
        ∀ i, (S i).map (MulAut.conj w).toMonoidHom = S (τ i) := by
  refine ⟨ggQTwoIndependentSingleton d Bs eta, ?_, ?_⟩
  · intro a
    obtain ⟨b, hba, -⟩ := Fin.exists_ne_and_ne_of_two_lt a a (by omega : 2 < r + 1)
    have hab : π a.succ ≠ π b.succ := fun h => hba (Fin.succ_inj.mp (π.injective h)).symm
    rw [hF.independentSingleton_eq_aux hLF hA hBs hyB hK hr hd _ _ hab,
      hF.singleton_eq_native hBs hyB hK hr hd a b hba.symm]
  · intro w hw τ hτ i
    exact ggQTwoIndependentSingleton_map_conj hw hτ d i

end GGSecFiveBPermQTwoKFrame

end CFSG.StandardType
