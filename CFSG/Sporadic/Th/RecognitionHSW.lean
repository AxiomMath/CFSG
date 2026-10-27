module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCTh
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.GH74.QTGen4.Recog.G23.Abstract
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.Sporadic.Th

open TauCeti
open CFSG.Sporadic.Bridge
open CFSG.Sporadic.Th.Max3
open CFSG.GH74.QTGen4.Recog.G23
open CFSG.HardMathSupport.Dickson.I271.TabMThreeC

theorem isSporadic_th_of_hswTuple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (img : ℕ → G)
    (hrel : ∀ v ∈ TauCeti.SporadicName.Th.presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd img v = 1)
    (ha : img 0 ≠ 1)
    (hC : Nat.card (Subgroup.centralizer ({img 0} : Set G)) = 92897280) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Th := by
  let P : TauCeti.GroupPresentation := TauCeti.Sporadic.Thompson.presentation
  have hP : TauCeti.SporadicName.Th.presentation = P := rfl
  have hrelP : ∀ v ∈ P.relatorLetters, wordProd img v = 1 := by
    intro v hv
    exact hrel v (by simpa [hP] using hv)
  let T := P.Group
  let z : G := img 0
  let φ : T →* G := presHom P img hrelP
  have hA2 : [(0, true), (0, true)] ∈ P.relatorLetters := by
    change [(0, true), (0, true)] ∈ TauCeti.Sporadic.Thompson.presentation.relatorLetters
    rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def]
    simp [TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
      TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.genA,
      Relator.toWord_gen, Relator.toWord_pow, Relator.toWord_mul]
  have hz2 : z ^ 2 = 1 := by
    have h := hrelP [(0, true), (0, true)] hA2
    simpa [CFSG.Sporadic.Bridge.wordProd, z, pow_two] using h
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2 ha
  have hfincard : Finite T ∧ Nat.card T ≤ 90745943887872000 := by
    have h := CFSG.Sporadic.Presentation.Th.finite_card_le
    simpa [TauCeti.SporadicName.Group, hP] using h
  letI : Finite T := hfincard.1
  have hle : Nat.card T ≤ Nat.card J := by
    rw [CFSG.Sporadic.Bridge.Th.card_J]
    exact hfincard.2
  obtain ⟨eTJ'⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv_of_le_range
    CFSG.Sporadic.Bridge.Th.φ CFSG.Sporadic.Bridge.Th.J_le_range hle
  let eTJ : J ≃* T := eTJ'
  let eJT : T ≃* J := eTJ.symm
  have hJsimple : IsSimpleGroup J := Kernel.isSimpleGroup_J th_kernel_facts
  have hTsimple : IsSimpleGroup T :=
    @MulEquiv.isSimpleGroup T inferInstance J inferInstance hJsimple eJT
  have hgen : P.generatorCount = 8 := CFSG.Sporadic.Bridge.Th.generatorCount_eq
  have hgen0 : 0 < P.generatorCount := by rw [hgen]; norm_num
  have hφgen0 : φ (presGen P 0) = z := by
    dsimp only [φ]
    rw [presHom_presGen P img hrelP hgen0]
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hmem : presGen P 0 ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφgen0] at hmem
      exact ha hmem
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  let K : Subgroup G := φ.range
  have hzK : z ∈ K := ⟨presGen P 0, hφgen0⟩
  have hinj : Function.Injective φ.rangeRestrict := by
    intro x y hxy
    exact hφinj (congrArg Subtype.val hxy)
  let eTK : T ≃* K := MulEquiv.ofBijective φ.rangeRestrict
    ⟨hinj, MonoidHom.rangeRestrict_surjective φ⟩
  let eKT : K ≃* T := eTK.symm
  let eKJ : K ≃* J := eKT.trans eJT
  have hIFJ : InvolutionFacts J 92897280 := involutionFacts_J
  have hIFK : InvolutionFacts K 92897280 :=
    @InvolutionFacts.of_equiv J K inferInstance inferInstance eKJ.symm 92897280 hIFJ
  have hzKord : orderOf (⟨z, hzK⟩ : K) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨z, hzK⟩ : K)]
    exact hzord
  have hCKcard : Nat.card (Subgroup.centralizer ({⟨z, hzK⟩} : Set K)) = 92897280 :=
    hIFK.1 ⟨z, hzK⟩ hzKord
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  have hCcard : Nat.card ↥C = 92897280 := by simpa [C, z] using hC
  have hsub : C.subgroupOf K = Subgroup.centralizer ({⟨z, hzK⟩} : Set K) := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have hCKle : C ≤ K := by
    have hcardInf : Nat.card ↥(C ⊓ K) = 92897280 := by
      have hmap := Subgroup.subgroupOf_map_subtype C K
      rw [← hmap, Subgroup.card_map_of_injective K.subtype_injective]
      rw [hsub]
      exact hCKcard
    have heq : C ⊓ K = C := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardInf, hCcard])
    exact inf_eq_left.mp heq
  have hNSK : NoOddSections ↥(Subgroup.centralizer ({⟨z, hzK⟩} : Set K)) := by
    obtain ⟨t₀, ht₀, hNS₀⟩ := hIFK.2.2.2
    obtain ⟨g, hg⟩ := hIFK.2.1 t₀ (⟨z, hzK⟩ : K) ht₀ hzKord
    have hNS₀' : NoOddSections
        ↥(Subgroup.centralizer ({g * (⟨z, hzK⟩ : K) * g⁻¹} : Set K)) := by
      rw [hg]
      exact hNS₀
    let eC : Subgroup.centralizer ({⟨z, hzK⟩} : Set K) ≃*
        Subgroup.centralizer ({(MulAut.conj g) (⟨z, hzK⟩ : K)} : Set K) :=
      @centralizerMulEquiv K K inferInstance inferInstance (MulAut.conj g) (⟨z, hzK⟩ : K)
    exact @NoOddSections.of_equiv
      ↥(Subgroup.centralizer ({(MulAut.conj g) (⟨z, hzK⟩ : K)} : Set K))
      ↥(Subgroup.centralizer ({⟨z, hzK⟩} : Set K))
      inferInstance inferInstance eC.symm hNS₀'
  have eCK : ↥C ≃* ↥(Subgroup.centralizer ({⟨z, hzK⟩} : Set K)) := by
    rw [← hsub]
    exact (Subgroup.subgroupOfEquivOfLe hCKle).symm
  have hNSC : NoOddSections ↥C :=
    @NoOddSections.of_equiv
      ↥(Subgroup.centralizer ({⟨z, hzK⟩} : Set K)) ↥C
      inferInstance inferInstance eCK.symm hNSK
  have hCns : ¬ Group.IsSolvable ↥C := hNSC.2.2
  have honeclass : ∀ t ∈ K, orderOf t = 2 → ∃ u ∈ K, u * z * u⁻¹ = t := by
    intro t htK ht2
    let tK : K := ⟨t, htK⟩
    have htKord : orderOf tK = 2 := by
      rw [← Subgroup.orderOf_coe tK]
      exact ht2
    obtain ⟨g, hg⟩ := hIFK.2.1 tK (⟨z, hzK⟩ : K) htKord hzKord
    refine ⟨(g : K), g.2, ?_⟩
    simpa using congrArg Subtype.val hg
  let U : Subgroup G := Subgroup.zpowers z
  have hU : U ≠ ⊥ := by
    intro hbot
    exact ha (Subgroup.zpowers_eq_bot.mp (by simpa [U] using hbot))
  have hU2 : IsPGroup 2 ↥U := by
    apply IsPGroup.of_card (n := 1)
    change Nat.card ↥(Subgroup.zpowers z) = 2 ^ 1
    rw [Nat.card_zpowers, hzord]
    norm_num
  have hYnorm : C ≤ Subgroup.normalizer (U : Set G) := by
    have hCU : C ≤ Subgroup.centralizer (U : Set G) := by
      rw [show U = Subgroup.zpowers z from rfl, Subgroup.le_centralizer_iff, Subgroup.zpowers_le,
        Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    exact hCU.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  have hKtop : K = ⊤ :=
    eq_top_of_one_class (X := K) (z := z) hzord hzK hCKle honeclass
      (U := U) (Y := C) hU hU2 hYnorm hCns
  have eKTh : K ≃* Blueprint.NativeSporadic.Th := eKJ.trans thEquivJ.symm
  exact ⟨Subgroup.topEquiv.symm.trans (hKtop ▸ eKTh)⟩

end CFSG.Sporadic.Th
