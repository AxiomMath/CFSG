
module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.A4
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3StructureKGroup
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.SectionRank

section SQTK

variable {G : Type} [Group G]

namespace C2Basic

theorem kGroup_of_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (hB : CFSG.SectionRank.IsKGroupCat B) :
    CFSG.SectionRank.IsKGroupCat A :=
  (hB.subgroup f.range).of_mulEquiv (MonoidHom.ofInjective hf)

end C2Basic

theorem IsSQTKIn.mono [Finite G] {H M : Subgroup G} (h : IsSQTKIn H) (hM : M ≤ H) :
    IsSQTKIn M := by
  refine ⟨sqt_iff.mpr fun q hq hq2 => ?_,
    C2Basic.kGroup_of_injective (Subgroup.inclusion hM) (Subgroup.inclusion_injective hM) h.2⟩
  exact (pRank_top_le_of_injective hq.one_lt (Subgroup.inclusion hM)
    (Subgroup.inclusion_injective hM)).trans (sqt_iff.mp h.1 q hq hq2)

end SQTK

section Radical

variable {G : Type*} [Group G] [Finite G]

theorem le_of_isSignalizer_of_isTwoRadicalIn {H R S : Subgroup G} (hR : IsTwoRadicalIn H R)
    (hS : IsSignalizer H (H ⊓ Subgroup.normalizer (R : Set G)) S) : S ≤ R := by
  have hRp : IsPGroup 2 R := hR.isPGroup
  have hXn : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (S : Set G) := hS.2.2
  have hRX : R ≤ H ⊓ Subgroup.normalizer (R : Set G) := le_inf hR.1 Subgroup.le_normalizer
  set P := S ⊔ R with hP
  have hRS : R ≤ Subgroup.normalizer (S : Set G) := hRX.trans hXn
  have hPp : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hS.2.1 hRp hRS
  have hPH : P ≤ H := sup_le hS.1 hR.1
  have hXP : H ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have hxS := hXn hx
    have hxR : x ∈ Subgroup.normalizer (R : Set G) := hx.2
    exact Subgroup.inf_normalizer_le_normalizer_sup S R ⟨hxS, hxR⟩
  have hPR : P ≤ R := by
    by_contra hnot
    have hlt : R < P := lt_of_le_of_ne le_sup_right (fun h => hnot (h ▸ le_rfl))
    obtain ⟨x, hxP, hxN, hxR⟩ := A4.exists_mem_normalizer_not_mem hPp hlt
    have hQ : (P ⊓ (H ⊓ Subgroup.normalizer (R : Set G))) ≤ R := by
      have hle : P ⊓ (H ⊓ Subgroup.normalizer (R : Set G)) ≤
          pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) :=
        le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hXP hg, Subgroup.le_normalizer hg⟩)
          (hPp.to_le inf_le_left)
      exact hle.trans hR.2.2.symm.le
    exact hxR (hQ ⟨hxP, hPH hxP, hxN⟩)
  exact le_sup_left.trans hPR

theorem isSignalizer_of_isTwoRadicalIn {H R : Subgroup G} (hR : IsTwoRadicalIn H R) :
    IsSignalizer H (H ⊓ Subgroup.normalizer (R : Set G)) R :=
  ⟨hR.1, hR.isPGroup, inf_le_right⟩

theorem c2_1_signalizers {H R : Subgroup G} (hR : IsTwoRadicalIn H R) :
    {S : Subgroup G | IsMaxSignalizer H (H ⊓ Subgroup.normalizer (R : Set G)) S} = {R} := by
  ext S
  constructor
  · intro hS
    have hSR : S ≤ R := le_of_isSignalizer_of_isTwoRadicalIn hR hS.1
    exact le_antisymm hSR (hS.2 (isSignalizer_of_isTwoRadicalIn hR) hSR)
  · intro hS
    have hSR : S = R := hS
    subst hSR
    exact ⟨isSignalizer_of_isTwoRadicalIn hR, fun T hT _ =>
      le_of_isSignalizer_of_isTwoRadicalIn hR hT⟩

theorem c2_1_pCore_le {H R : Subgroup G} (hR : IsTwoRadicalIn H R) : pCoreOf 2 H ≤ R :=
  le_of_isSignalizer_of_isTwoRadicalIn hR
    ⟨pCoreOf_le 2 H, pCoreOf_isPGroup 2 H, fun _ hx => le_normalizer_pCoreOf 2 H hx.1⟩

end Radical

section CentralizerSection

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem centralizerSection_normal {M L : Subgroup G} (hLn : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (centralizerSection M L (pCoreOf 2 L) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := hLn hg
  have hgZ : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L hgL
  intro m
  constructor
  · intro hm
    exact conj_mem_centralizerSection (Subgroup.le_normalizer hg) hgL hgZ hm
  · intro hm
    have := conj_mem_centralizerSection (Subgroup.le_normalizer (M.inv_mem hg))
      (Subgroup.inv_mem _ hgL) (Subgroup.inv_mem _ hgZ) hm
    simpa [mul_assoc] using this

theorem c1_2_four {M L R : Subgroup G} (hL : L = oTwoUpper L) (hLM : L ≤ M)
    (hLn : (L.subgroupOf M).Normal) (hR : IsSylowTwoOf R (centralizerSection M L (pCoreOf 2 L)))
    (hR1 : R ≠ ⊥) : IsSylowTwoOf R (conjClosure R M) ∧ IsTwoRadicalIn M R := by
  have hLN : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hCM : centralizerSection M L (pCoreOf 2 L) ≤ M := centralizerSection_le_left M L _
  have hRC : R ≤ centralizerSection M L (pCoreOf 2 L) := hR.1
  refine ⟨?_, ?_⟩
  · have hcl : conjClosure R M ≤ centralizerSection M L (pCoreOf 2 L) := by
      refine conjClosure_le fun m hm r hr => ?_
      exact (Subgroup.mem_normalizer_iff.mp (centralizerSection_normal hLN hm) r).mp (hRC hr)
    exact B6.isSylowTwoOf_mono hR (le_conjClosure R M) hcl
  · have hRM : R ≤ M := hRC.trans hCM
    have hRp : IsPGroup 2 R := hR.2.1
    refine ⟨hRM, hR1, le_antisymm (le_pCoreOf_inf_normalizer hRM hRp) ?_⟩
    set Q := pCoreOf 2 (M ⊓ Subgroup.normalizer (R : Set G)) with hQ
    have hRmax : IsMaxSignalizer M L R :=
      (a4_2_4 hL (A4.subnormal_of_normal hLM hLn) R).mpr hR
    have hLR : L ≤ Subgroup.normalizer (R : Set G) := hRmax.1.2.2
    have hLNM : L ≤ M ⊓ Subgroup.normalizer (R : Set G) := le_inf hLM hLR
    have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := hLNM.trans (le_normalizer_pCoreOf 2 _)
    have hQM : Q ≤ M := (pCoreOf_le 2 _).trans inf_le_left
    have hQL : Q ≤ Subgroup.normalizer (L : Set G) := hQM.trans hLN
    have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
    have hcomm : ⁅L, Q⁆ ≤ pCoreOf 2 L := by
      have h1 : ⁅L, Q⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hQL
      have h2 : ⁅L, Q⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_right.mp hLQ
      have h3 : L ⊓ Q ≤ pCoreOf 2 L :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left
          (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hLQ hg⟩)
          (hQp.to_le inf_le_right)
      exact (le_inf h1 h2).trans h3
    have hQC : Q ≤ centralizerSection M L (pCoreOf 2 L) :=
      (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr ⟨hQM, hcomm⟩
    have hRQ : R ≤ Q := le_pCoreOf_inf_normalizer hRM hRp
    exact (A4.isSylowTwoOf_iff_maximal.mp hR).2.2 Q hQC hQp hRQ

end CentralizerSection

section Glue

variable {G : Type*} [Group G]

theorem isSubnormal_iff_subgroupOf {L X : Subgroup G} (hLX : L ≤ X) :
    IsSubnormal L X ↔ (L.subgroupOf X).IsSubnormal := by
  constructor
  · intro h
    have := A4.subnormal_subgroupOf X h
    rw [Subgroup.subgroupOf_self] at this
    exact A3.subnormal_top_iff.mp this
  · intro h
    have h1 := A3.subnormal_top_iff.mpr h
    have h2 := A3.subnormal_map X.subtype h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hLX, Subgroup.map_top, Subgroup.range_subtype] at h2

theorem IsBlock2.isSubnormal {X L : Subgroup G} (h : IsBlock2 X L) : IsSubnormal L X :=
  (isSubnormal_iff_subgroupOf h.2.1).mpr h.2.2

theorem conjByElt_le_conjClosure {L M : Subgroup G} {m : G} (hm : m ∈ M) :
    conjByElt m L ≤ conjClosure L M := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  exact mem_conjClosure hm hz

theorem perfect_conjClosure {L M : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅conjClosure L M, conjClosure L M⁆ = conjClosure L M := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · exact (conjClosure L M).mul_mem ((conjClosure L M).mul_mem
      ((conjClosure L M).mul_mem ha hb) ((conjClosure L M).inv_mem ha)) ((conjClosure L M).inv_mem hb)
  · refine conjClosure_le fun m hm z hz => ?_
    have hz' : z ∈ ⁅L, L⁆ := by rw [hL]; exact hz
    have h1 : conjByElt m ⁅L, L⁆ ≤ ⁅conjClosure L M, conjClosure L M⁆ := by
      unfold conjByElt
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (conjByElt_le_conjClosure hm) (conjByElt_le_conjClosure hm)
    exact h1 ⟨z, hz', rfl⟩

end Glue

end CFSG.Quasithin
