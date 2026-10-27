module

public import CFSG.Milestones.ASVolI.C31.J4KWRed
public import CFSG.Assembly.Dichotomy
public import CFSG.Sporadic.J4.QT2LocRadMain
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem burnsideJ4KW_charP_centralizer
    (t : J) (ht : orderOf t = 2) :
    CFSG.Assembly.Dichotomy.dichotomyCharP 2 ↥(Subgroup.centralizer ({t} : Set J)) := by
  have hsq : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht, pow_two] at h1
    exact h1
  have hne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨N, hN2, -, hNC, hnorm, hself, -⟩ := CFSG.Sporadic.J4.QT2.j4_involution_radical t hsq hne
  set C := Subgroup.centralizer ({t} : Set J) with hCdef
  let N' : Subgroup ↥C := N.subgroupOf C
  have hN'n : N'.Normal := ⟨fun n hn g => by
    simp only [N', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact hnorm g g.2 n hn⟩
  have hN'2 : IsPGroup 2 ↥N' := hN2.comap_subtype
  have hle : N' ≤ CFSG.pCore 2 ↥C := le_sSup ⟨hN'n, hN'2⟩
  intro x hx
  apply hle
  rw [Subgroup.mem_subgroupOf]
  refine hself x x.2 fun e he => ?_
  have heC : e ∈ C := hNC he
  have hmem : (⟨e, heC⟩ : ↥C) ∈ CFSG.pCore 2 ↥C := hle (by rw [Subgroup.mem_subgroupOf]; exact he)
  have := Subgroup.mem_centralizer_iff.1 hx _ hmem
  exact (congrArg Subtype.val this).symm

theorem burnsideJ4KW_isCharTwoType :
    CFSG.Assembly.IsCharTwoType ↥J :=
  CFSG.Assembly.Dichotomy.charTwoType_of_involution_centralizers ↥J fun t ht =>
    burnsideJ4KW_charP_centralizer t ht

@[expose] def burnsideJ4KW_MaxNonParabolicCore : Prop :=
  ∀ R : Subgroup J, IsPGroup 2 ↥R → R ≠ ⊥ →
    (∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
      Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) →
      Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (R : Set J)) →
    (∀ Y : Subgroup J, IsPGroup 2 ↥Y →
      Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) → Y ≤ R) →
    Subgroup.centralizer (R : Set J) ≤ R →
    (∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (R : Set J)) →
    ∃ g : J, Subgroup.normalizer (R : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom

theorem burnsideJ4KW_subgroupOf_normal {L Y : Subgroup J} (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set J)) : (Y.subgroupOf L).Normal :=
  ⟨fun n hn' g => by
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn' ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hn g.2) n).1 hn'⟩

theorem burnsideJ4KW_isPGroup_pCoreOf (L : Subgroup J) : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype

theorem burnsideJ4KW_le_normalizer_pCoreOf (L : Subgroup J) :
    L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set J) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hn := CFSG.pCore_normal (p := 2) (G := ↥L)
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨g, hg⟩ : ↥L) * y * (⟨g, hg⟩ : ↥L)⁻¹, hn.conj_mem y hy _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(⟨g, hg⟩ : ↥L)⁻¹ * y * (⟨g, hg⟩ : ↥L), ?_, ?_⟩
    · have := hn.conj_mem y hy ((⟨g, hg⟩ : ↥L)⁻¹)
      rwa [inv_inv] at this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
      rw [hyx]
      group

theorem burnsideJ4KW_le_pCoreOf {L Y : Subgroup J} (hY : IsPGroup 2 ↥Y) (hYL : Y ≤ L)
    (hn : L ≤ Subgroup.normalizer (Y : Set J)) : Y ≤ CFSG.Open.pCoreOf 2 L := by
  have hYn := burnsideJ4KW_subgroupOf_normal hYL hn
  have hY2 : IsPGroup 2 ↥(Y.subgroupOf L) := hY.comap_subtype
  have hle : Y.subgroupOf L ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hYn, hY2⟩
  intro y hy
  exact ⟨⟨y, hYL hy⟩, hle (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩

theorem burnsideJ4KW_pCore_maxTwoLocal {X : Subgroup J} (hX : burnsideJ4KW_IsMaxTwoLocal X) :
    IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 (Subgroup.normalizer (X : Set J))) ∧
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (X : Set J)) ≠ ⊥ ∧
      Subgroup.normalizer
          (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (X : Set J)) : Set J) =
        Subgroup.normalizer (X : Set J) ∧
      ∀ Y : Subgroup J, IsPGroup 2 ↥Y →
        Subgroup.normalizer
            (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (X : Set J)) : Set J) ≤
          Subgroup.normalizer (Y : Set J) →
        Y ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (X : Set J)) := by
  obtain ⟨hX2, hXne, hmax⟩ := hX
  set L := Subgroup.normalizer (X : Set J) with hLdef
  set R := CFSG.Open.pCoreOf 2 L with hRdef
  have hR2 : IsPGroup 2 ↥R := burnsideJ4KW_isPGroup_pCoreOf L
  have hLR : L ≤ Subgroup.normalizer (R : Set J) := burnsideJ4KW_le_normalizer_pCoreOf L
  have hXR : X ≤ R := burnsideJ4KW_le_pCoreOf hX2 Subgroup.le_normalizer le_rfl
  have hRne : R ≠ ⊥ := fun h => hXne (eq_bot_iff.2 (h ▸ hXR))
  have hNR : Subgroup.normalizer (R : Set J) = L := hmax R hR2 hRne hLR
  refine ⟨hR2, hRne, hNR, fun Y hY hRY => ?_⟩
  by_cases hYne : Y = ⊥
  · rw [hYne]; exact bot_le
  have hNY : Subgroup.normalizer (Y : Set J) = L := hmax Y hY hYne (hNR.ge.trans hRY)
  refine burnsideJ4KW_le_pCoreOf hY ?_ hNY.ge
  rw [← hNY]
  exact Subgroup.le_normalizer

theorem burnsideJ4KW_maxNonParabolic_of_core
    (h : burnsideJ4KW_MaxNonParabolicCore) : burnsideJ4KW_MaxNonParabolic := by
  intro X hX hnp
  obtain ⟨hR2, hRne, hNR, hRmax⟩ := burnsideJ4KW_pCore_maxTwoLocal hX
  set L := Subgroup.normalizer (X : Set J) with hLdef
  set R := CFSG.Open.pCoreOf 2 L with hRdef
  have hmaxR : ∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
      Subgroup.normalizer (R : Set J) ≤ Subgroup.normalizer (Y : Set J) →
      Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (R : Set J) := by
    intro Y hY hYne hRY
    rw [hNR] at hRY ⊢
    exact hX.2.2 Y hY hYne hRY
  have hcent : Subgroup.centralizer (R : Set J) ≤ R := by
    intro c hc
    have hcL : c ∈ L := by
      rw [← hNR]
      exact Subgroup.centralizer_le_normalizer _ hc
    exact burnsideJ4KW_isCharTwoType L ⟨X, hX.2.1, hX.1, rfl⟩ ⟨hcL, hc⟩
  obtain ⟨g, hg⟩ := h R hR2 hRne hmaxR hRmax hcent (fun g hg => hnp g (hg.trans hNR.le))
  exact ⟨g, hNR.ge.trans hg⟩

theorem burnsideJ4KW_core_of_maxNonParabolicCore
    (h : burnsideJ4KW_MaxNonParabolicCore) : burnsideC31_J4KWCore :=
  burnsideJ4KW_core_of_maxNonParabolic (burnsideJ4KW_maxNonParabolic_of_core h)

end CFSG.ASVolI
