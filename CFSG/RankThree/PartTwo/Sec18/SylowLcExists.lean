module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofStatements
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
public import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]


namespace SylowLc

variable {A M H : Subgroup G} {c : G}

theorem lc_mem_oTwoComponentsIn (h1812 : Item181_2) (h184 : Item184_1) (h182 : Item182Alt1C)
    (hH : Sec18H G A M H c) :
    lc H c ∈ oTwoComponentsIn (Subgroup.centralizer ({c} : Set G)) ∧
      lc H c = inSubgroup perfectResidual (inSubgroup perfectResidual H ⊓
        Subgroup.centralizer ({c} : Set G)) ⊔ CFSG.Open.pCoreOf 2 (lc H c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.toSec18Std
  have hHs := hH.mem_scriptH
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hHs).1
  have hAH := le_of_mem_scriptH₀ hH₀
  have hAM := sec18Std_le h
  obtain ⟨s, ⟨hsS, hsA, hgf, hsH, -⟩, -, -⟩ := h1812 G A M h H hHs
  have hout : Sec4.InducesOuterTheta s (inSubgroup perfectResidual H) :=
    hgf.inducesOuterTheta _ (by decide)
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hc1 : c ≠ 1 := by
    intro h1
    have := orderOf_eq_three_of_sec18H h184 hH
    rw [h1, orderOf_one] at this
    norm_num at this
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb := (perfectResidual H).map π with hLbdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set R := CFSG.Open.pCoreOf 2 C with hRdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hsC : s ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsA c hcA).symm
  have hCtop : C ≠ ⊤ := Claim184LcProof.centralizer_ne_top h hc1
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hLbn : Lb.Normal := by
    have hc := CFSG.perfect_residual_characterization (G := H)
    have : (perfectResidual H).Characteristic := hc.2.1
    exact (inferInstance : (perfectResidual H).Normal).map π (QuotientGroup.mk'_surjective _)
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hLimg : (L.subgroupOf H).map π = Lb := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  set L₀ := inSubgroup perfectResidual (L ⊓ C) with hL₀def
  have hL₀LC : L₀ ≤ L ⊓ C := Subgroup.map_subtype_le _
  have hL₀L : L₀ ≤ L := hL₀LC.trans inf_le_left
  have hL₀H : L₀ ≤ H := hL₀L.trans hLH
  have hL₀C : L₀ ≤ C := hL₀LC.trans inf_le_right
  have hL₀p : ⁅L₀, L₀⁆ = L₀ := commutator_inSubgroup_perfectResidual _
  have hLL₀ : L ≤ L₀ ⊔ CFSG.Open.pCoreOf 2 L := (le_sup_and_inf_le_of_sec18H hH).1
  have hHCN : H ⊓ C ≤ Subgroup.normalizer (L₀ : Set G) := by
    refine le_trans ?_
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        (L ⊓ C))
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_inSubgroup_perfectResidual H hx.1, Subgroup.le_normalizer hx.2⟩
  have hL₀img : (L₀.subgroupOf H).map π = Lb := by
    apply le_antisymm
    · rw [← hLimg]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hL₀L hx)
    · have hOH : CFSG.Open.pCoreOf 2 L ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH
      have hker : ((CFSG.Open.pCoreOf 2 L).subgroupOf H).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
        intro x hx
        rw [mem_pCore_iff_mem_pCoreOf]
        exact hLO (Subgroup.mem_subgroupOf.mp hx)
      rw [← hLimg]
      calc (L.subgroupOf H).map π ≤ ((L₀ ⊔ CFSG.Open.pCoreOf 2 L).subgroupOf H).map π :=
            Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hLL₀ hx)
        _ = (L₀.subgroupOf H).map π := by
            rw [Subgroup.subgroupOf_sup hL₀H hOH, Subgroup.map_sup, hker, sup_bot_eq]
  have hL₀O : CFSG.Open.pCoreOf 2 L₀ ≤ CFSG.Open.pCoreOf 2 H :=
    Claim184LcProof.pCoreOf_le_of_map_eq hL₀H hL₀img
  obtain ⟨eL⟩ := Claim184LcProof.quotient_mulEquiv_map hLH hLO
  obtain ⟨eL₀⟩ := Claim184LcProof.quotient_mulEquiv_map hL₀H hL₀O
  have hL₀q : CFSG.IsQuasisimple (L₀ ⧸ CFSG.pCore 2 L₀) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (eL.trans ((MulEquiv.subgroupCongr (hLimg.trans hL₀img.symm)).trans eL₀.symm))
      (isQuasisimple_of_mem_oTwoComponentsIn hH₀.2.1)
  set T := CFSG.Open.pCoreOf 2 (H ⊓ M) ⊓ C with hTdef
  have hTHM : T ≤ H ⊓ M := inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hTH : T ≤ H := hTHM.trans inf_le_left
  have hTM : T ≤ M := hTHM.trans inf_le_right
  have hTC : T ≤ C := inf_le_right
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hsT : s ∈ T := ⟨hsS, hsC⟩
  have hNT : ∀ x, x ∈ H → x ∈ M → x ∈ C → x ∈ Subgroup.normalizer (T : Set G) :=
    fun x hxH hxM hxC => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M) ⟨hxH, hxM⟩,
        Subgroup.le_normalizer hxC⟩
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha => hNT a (hAH ha) (hAM ha) (hAC ha)
  have hAL₀ : A ≤ Subgroup.normalizer (L₀ : Set G) := fun a ha => hHCN ⟨hAH ha, hAC ha⟩
  have hTL₀ : T ≤ Subgroup.normalizer (L₀ : Set G) := fun t ht => hHCN ⟨hTH ht, hTC ht⟩
  set Y := L₀ ⊔ A ⊔ T with hYdef
  have hYHC : Y ≤ H ⊓ C :=
    sup_le (sup_le (le_inf hL₀H hL₀C) (le_inf hAH hAC)) (le_inf hTH hTC)
  have hYC : Y ≤ C := hYHC.trans inf_le_right
  have hYT : Y ⊓ M ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    hNT x (hYHC hx.1).1 hx.2 (hYHC hx.1).2
  have hYL₀ : Y ≤ Subgroup.normalizer (L₀ : Set G) := hYHC.trans hHCN
  have hTO : ¬ T ≤ CFSG.Open.pCoreOf 2 Y := fun hle =>
    Claim184LcProof.not_mem_pCoreOf_of_inducesOuterTheta hsH (le_sup_left.trans le_sup_left) hYL₀
      hL₀img hL₀O hout (hle hsT)
  obtain ⟨hY, hYres⟩ :=
    Claim184LcProof.sup_mem_scriptH_of_le h hHs hL₀H hTH hL₀p hL₀q hT2 hTM hAL₀ hTL₀ hAT hYT hTO
  have hcY : c ∈ sectionCentralizer A (inSubgroup perfectResidual Y)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual Y)) := by
    refine ⟨hcA, fun x hx => ?_⟩
    rw [hYres] at hx
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hL₀C hx)).symm, mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨K, hK, hKL⟩ := h182 G A M h Y hY C hYC hCtop c hcA hc1 le_rfl hcY
  rw [hYres] at hKL
  have hKp : ⁅K, K⁆ = K := commutator_eq_of_mem_oTwoComponentsIn hK
  have hKR : CFSG.Open.pCoreOf 2 K ≤ R := pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hKlc : K ≤ lc H c := by
    refine le_inSubgroup_perfectResidual hKp ?_
    rw [hKL]
    exact sup_le (hL₀LC.trans le_sup_left) (hKR.trans le_sup_right)
  have hL₀K : L₀ ≤ K := hKL ▸ le_sup_left
  have hlcK : lc H c ≤ K := by
    have hperf : Group.IsPerfect (lc H c) :=
      Subgroup.isPerfect_iff.mpr (commutator_inSubgroup_perfectResidual _)
    have hle : lc H c ≤ L₀ ⊔ R :=
      Sec6.le_perfectResidual_sup hperf (inf_le_right.trans hCR) (Subgroup.map_subtype_le _)
    have hle' : lc H c ≤ K ⊔ R := hle.trans (sup_le_sup_right hL₀K _)
    rw [← inSubgroup_perfectResidual_sup_pCoreOf hK]
    exact le_inSubgroup_perfectResidual (commutator_inSubgroup_perfectResidual _) hle'
  have hKeq : K = lc H c := le_antisymm hKlc hlcK
  rw [← hKeq]
  exact ⟨hK, hKL⟩

end SylowLc

end CFSG.RankThree.PartTwo.Sec18
