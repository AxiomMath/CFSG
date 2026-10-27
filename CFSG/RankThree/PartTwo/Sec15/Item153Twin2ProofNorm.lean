module

public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofMain
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Claim153TwinNorm (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, ¬ HasFaithfulE9 Y →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) → ∀ m ∈ M,
        Subgroup.normalizer (Y : Set G) ≤
          Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)

@[expose] noncomputable def Claim153TwinNormR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153TwinNorm A (lB A)

namespace Proof153Twin2

theorem normalizer_le_of_norm {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    (hnorm : ∀ m ∈ M, Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 Y with hP
  set K : Subgroup G := ⨆ m : M, P.map (MulAut.conj (m : G)).toMonoidHom with hK
  have hPM : P ≤ CFSG.Open.pCoreOf 2 M := by
    obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_item152 h h152 hY hM
    change Y'.map M.subtype = Y at hYY'
    have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hY'.2.1
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rw [← Sec18.pCoreOf_map M.subtype M.subtype_injective, hYY'] at h2
    exact h2
  have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hKO : K ≤ CFSG.Open.pCoreOf 2 M := by
    refine iSup_le fun m => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMO m.2) x).mp (hPM hx)
  have hK2 : IsPGroup 2 K := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le hKO
  have hK1 : K ≠ ⊥ := by
    intro h0
    apply hY.prop.2.2
    rw [eq_bot_iff]
    have hle : P.map (MulAut.conj ((1 : M) : G)).toMonoidHom ≤ K :=
      le_iSup (fun m : M => P.map (MulAut.conj (m : G)).toMonoidHom) 1
    rw [h0, Subgroup.coe_one, Late.map_conj_one] at hle
    exact hle
  have hmap : ∀ g : G, K.map (MulAut.conj g).toMonoidHom =
      ⨆ m : M, P.map (MulAut.conj (g * m)).toMonoidHom := by
    intro g
    rw [hK, Subgroup.map_iSup]
    congr 1
    funext m
    rw [Late.map_conj_map_conj]
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := by
    have hle : ∀ g ∈ M, K.map (MulAut.conj g).toMonoidHom ≤ K := fun g hg => by
      rw [hmap]
      exact iSup_le fun m => le_iSup (fun m : M => P.map (MulAut.conj (m : G)).toMonoidHom)
        ⟨g * m, M.mul_mem hg m.2⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (hle g hg) ?_
    have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hle g⁻¹ (M.inv_mem hg))
    rwa [Late.map_conj_map_conj, mul_inv_cancel, Late.map_conj_one] at h2
  have hNK : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hK, Subgroup.map_iSup]
    congr 1
    funext m
    have hnm := hnorm m m.2 hn
    have hO : n ∈ Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 (Y.map (MulAut.conj (m : G)).toMonoidHom) : Subgroup G) :
          Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hnm
    rw [Sec18.pCoreOf_map _ (MulAut.conj (m : G)).injective] at hO
    exact Late.map_conj_eq_of_mem_normalizer hO
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hK2 hK1
  have hMeq : M = Subgroup.normalizer (K : Set G) := by
    by_contra hne
    exact hM.1.2 _ (lt_of_le_of_ne hMK hne) hloc
  rw [hMeq]
  exact hNK

end Proof153Twin2

open Proof153Twin2

theorem claim153TwinN_of_norm {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (hn : Claim153TwinNorm A (lB A)) : Claim153TwinN A (lB A) :=
  fun Y hY hE M hM hMY => normalizer_le_of_norm h h152 hY hM (hn Y hY hE M hM hMY)

theorem claim153TwinNR_of_norm (h152 : Item152R) (hn : Claim153TwinNormR) : Claim153TwinNR :=
  fun G _ _ A c L hR => claim153TwinN_of_norm hR.toSec14Std (h152 G A c L hR) (hn G A c L hR)

theorem claim153TwinXR_of_norm (h149 : Sec16.Item149S14) (h152 : Item152R)
    (hn : Claim153TwinNormR) : Claim153TwinXR :=
  claim153TwinXR_of_twinN h149 h152 (claim153TwinNR_of_norm h152 hn)

end CFSG.RankThree.PartTwo.Sec15
