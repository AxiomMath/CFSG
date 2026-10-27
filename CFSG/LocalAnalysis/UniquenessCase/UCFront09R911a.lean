module

public import CFSG.CGT.PushingUpLit.Defs
import CFSG.CGT.PushingUpLit.A78Sp4.CentAux
import CFSG.CGT.PushingUpLit.Glue.RadicalSylow
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualTwoExtension.ResidualTwoExtension
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.ProofSupport Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.CGT.PushingUpLit (centralizerModCore oTwoIn jIn)
open CFSG.LieType.BorelTits (pCoreOf_le pCoreOf_isPGroup le_normalizer_pCoreOf
  le_pCoreOf_of_le_normalizer)

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_pCoreOf_centralizerModCore {X Y S H W : Subgroup G} (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hS : IsSylowOf 2 S Y) (hYXS : Y ≤ X ⊔ S) (hYH : Y ≤ H)
    (hSW : IsSylowOf 2 S W) (hNW : H ⊓ normalizer (pCoreOf 2 Y : Set G) ≤ W) :
    IsSylowOf 2 (pCoreOf 2 Y) (centralizerModCore X ⊓ H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
  have hYR : Y ≤ normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
  have hXO : normalizer (X : Set G) ≤ normalizer (oTwoIn X : Set G) :=
    CFSG.CGT.PushingUpLit.normalizer_le_normalizer_oTwoIn X
  have hSY : S ≤ Y := hS.le
  have hRX : pCoreOf 2 Y ⊓ X ≤ oTwoIn X :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      ((le_inf (hXY.trans hYR) le_normalizer).trans inf_normalizer_le_normalizer_inf)
      ((pCoreOf_isPGroup 2 Y).to_le inf_le_left)
  have hRC : pCoreOf 2 Y ≤ centralizerModCore X ⊓ H := by
    intro r (hr : r ∈ pCoreOf 2 Y)
    refine ⟨⟨hYX (hRY hr), fun x (hx : x ∈ X) => hRX (mem_inf.2 ⟨?_, ?_⟩)⟩, hYH (hRY hr)⟩
    · have h := (mem_normalizer_iff.1 (hYR (hXY hx)) r⁻¹).1 (inv_mem hr)
      simpa [mul_assoc] using mul_mem hr h
    · exact mul_mem ((mem_normalizer_iff.1 (hYX (hRY hr)) x).1 hx) (inv_mem hx)
  have hSC : S ≤ normalizer ((centralizerModCore X ⊓ H : Subgroup G) : Set G) :=
    (le_inf ((hSY.trans hYX).trans
        (CFSG.CGT.PushingUpLit.Glue.normalizer_le_normalizer_centralizerModCore X))
      ((hSY.trans hYH).trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hTR : S ⊓ (centralizerModCore X ⊓ H) ≤ pCoreOf 2 Y := by
    have hTO : S ⊓ (centralizerModCore X ⊓ H) ≤ normalizer (oTwoIn X : Set G) :=
      inf_le_right.trans (inf_le_left.trans
        ((CFSG.CGT.PushingUpLit.Glue.centralizerModCore_le_normalizer X).trans hXO))
    have hXn : X ≤ normalizer
        ((oTwoIn X ⊔ S ⊓ (centralizerModCore X ⊓ H) : Subgroup G) : Set G) := by
      refine le_normalizer_iff.2 fun x hx z hz => ?_
      have hle : oTwoIn X ⊔ S ⊓ (centralizerModCore X ⊓ H) ≤
          (oTwoIn X ⊔ S ⊓ (centralizerModCore X ⊓ H)).comap (MulAut.conj x).toMonoidHom := by
        refine sup_le (fun o (ho : o ∈ oTwoIn X) => ?_)
          (fun t (ht : t ∈ S ⊓ (centralizerModCore X ⊓ H)) => ?_)
        · exact mem_comap.2 (mem_sup_left ((mem_normalizer_iff.1 (hXO (le_normalizer hx)) o).1 ho))
        · have hc : t⁻¹ * x * t⁻¹⁻¹ * x⁻¹ ∈ oTwoIn X :=
            (CFSG.CGT.PushingUpLit.mem_centralizerModCore_iff.1
              (inv_mem (mem_inf.1 (mem_inf.1 ht).2).1)).2 x hx
          have e : (MulAut.conj x).toMonoidHom t = t * (t⁻¹ * x * t⁻¹⁻¹ * x⁻¹) := by
            simp [mul_assoc]
          exact mem_comap.2 (e ▸ mul_mem (mem_sup_right ht) (mem_sup_left hc))
      simpa using hle hz
    have hSn : S ≤ normalizer ((oTwoIn X ⊔ S ⊓ (centralizerModCore X ⊓ H) : Subgroup G) : Set G) :=
      (le_inf ((hSY.trans hYX).trans hXO)
        ((le_inf le_normalizer hSC).trans inf_normalizer_le_normalizer_inf)).trans
        (inf_normalizer_le_normalizer_sup _ _)
    have hO := le_pCoreOf_of_le_normalizer 2
      (sup_le ((CFSG.CGT.PushingUpLit.oTwoIn_le X).trans hXY) (inf_le_left.trans hSY))
      (hYXS.trans (sup_le hXn hSn))
      ((CFSG.CGT.PushingUpLit.isPGroup_oTwoIn X).to_sup_of_normal_left'
        (hS.isPGroup.to_le inf_le_left) hTO)
    exact le_sup_right.trans hO
  have hK : S ≤ normalizer
      ((centralizerModCore X ⊓ H ⊓ normalizer (pCoreOf 2 Y : Set G) : Subgroup G) : Set G) :=
    (le_inf hSC ((hSY.trans hYR).trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hKW : centralizerModCore X ⊓ H ⊓ normalizer (pCoreOf 2 Y : Set G) ≤ W :=
    fun k hk => hNW ⟨hk.1.2, hk.2⟩
  have hSK := (hSW.of_le le_sup_left (sup_le hSW.le hKW)).inf_of_le_normalizer le_sup_right
    (sup_le hK le_normalizer)
  have hSKR : S ⊓ (centralizerModCore X ⊓ H ⊓ normalizer (pCoreOf 2 Y : Set G)) = pCoreOf 2 Y :=
    le_antisymm ((inf_le_inf_left S inf_le_left).trans hTR)
      (le_inf (CFSG.CGT.PushingUpLit.A78Sp4.pCoreOf_le_of_isSylowOf hS)
        (le_inf hRC le_normalizer))
  rw [hSKR] at hSK
  exact isSylowOf_of_inf_normalizer_le hRC le_rfl hSK

theorem exists_mem_calMOf_isSylowOf_centralizerModCore (D : Data G) {Y : Subgroup G}
    (hY : Y ∈ calY2Star9 D) (hR : pCoreOf 2 Y ≠ ⊥) :
    ∃ H ∈ calMOf Y,
      H ⊓ normalizer (jIn (pCoreOf 2 Y) : Set G) ≤ normalizer (Opp 3 Y : Set G) ∧
      IsSylowOf 2 (pCoreOf 2 Y) (centralizerModCore (Opp 3 Y) ⊓ H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYmax : Maximal (· ∈ calY2_9 D) Y := hY
  have hYM : Y ≤ D.M := hYmax.prop.1.1
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hRJ : normalizer (pCoreOf 2 Y : Set G) ≤ normalizer (jIn (pCoreOf 2 Y) : Set G) :=
    CFSG.CGT.PushingUpLit.normalizer_le_normalizer_jIn (pCoreOf 2 Y)
  have hYXS : Y ≤ Opp 3 Y ⊔ S :=
    le_of_le_of_isSylowOf le_sup_left le_sup_right hS hYmax.prop.2.2.2.2
  have key : ∀ H W N : Subgroup G, H ∈ calMOf Y → Y ≤ W → W ≤ D.M → N ∈ calMOf W → N ≠ D.M →
      H ⊓ normalizer (jIn (pCoreOf 2 Y) : Set G) ≤ W →
      ∃ H ∈ calMOf Y,
        H ⊓ normalizer (jIn (pCoreOf 2 Y) : Set G) ≤ normalizer (Opp 3 Y : Set G) ∧
        IsSylowOf 2 (pCoreOf 2 Y) (centralizerModCore (Opp 3 Y) ⊓ H) := by
    intro H W N hH hYW hWM hN hNM hJW
    obtain ⟨hX, hSW⟩ := opp_eq_L9_and_isSylowOf D hY hYW hWM hN hNM hS
    have hWX : W ≤ normalizer (Opp 3 Y : Set G) := by
      rw [hX]
      exact ResidualTwoExtension.le_normalizer_normalClosureUnder (Opp 3 Y) W
    exact ⟨H, hH, hJW.trans hWX, isSylowOf_pCoreOf_centralizerModCore (opp_le_self 3 Y)
      (hYW.trans hWX) hS hYXS hH.2 hSW ((inf_le_inf_left H hRJ).trans hJW)⟩
  by_cases hJM : normalizer (jIn (pCoreOf 2 Y) : Set G) ≤ D.M
  · obtain ⟨N, hN, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
      by_contra h'
      exact hYmax.prop.2.1 (Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, hYM⟩,
        fun N hN => Classical.byContradiction fun hNM => h' ⟨N, hN, hNM⟩⟩)
    exact key N (N ⊓ D.M) N hN (le_inf hN.2 hYM) inf_le_right ⟨hN.1, inf_le_left⟩ hNM
      (inf_le_inf_left N hJM)
  · have hloc : IsTwoLocal (normalizer (jIn (pCoreOf 2 Y) : Set G)) :=
      ⟨_, CFSG.CGT.PushingUpLit.jIn_ne_bot (pCoreOf_isPGroup 2 Y) hR,
        CFSG.CGT.PushingUpLit.isPGroup_jIn (pCoreOf_isPGroup 2 Y), rfl⟩
    obtain ⟨N, hJN, hmax⟩ := Finite.exists_le_maximal hloc
    have hYN : Y ≤ N := ((le_normalizer_pCoreOf 2 Y).trans hRJ).trans hJN
    exact key D.M (D.M ⊓ N) N ⟨D.maxLocal, hYM⟩ (le_inf hYM hYN) inf_le_left
      ⟨⟨hmax.1, fun K hK hNK => le_antisymm (hmax.2 hK hNK) hNK⟩, inf_le_right⟩
      (fun h => hJM (h ▸ hJN)) (inf_le_inf_left D.M hJN)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
