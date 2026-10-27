module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNQuot
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L828N
open scoped IsMulCommutative

section N2a

variable {G : Type} [Group G] [Finite G]

theorem s828N_uniqueMax_le {H T M B : Subgroup G} (h : IsUniqueMaxOver H T M) (hTB : T ≤ B)
    (hBH : B < H) : B ≤ M := by
  obtain ⟨N₀, hN₀, hBN₀⟩ := exists_isMaxSubgroupIn hBH
  obtain ⟨-, -, hu⟩ := isUniqueMaxOver_iff.mp h
  have hNM : N₀ = M := hu N₀ hN₀ (hTB.trans hBN₀)
  rw [← hNM]
  exact hBN₀

theorem s828N_not_le_kerIn {H M V : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hV2 : IsPGroup 2 ↥V) (hVH : V ≤ H) (hVO : ¬ V ≤ pCoreOf 2 H) : ¬ V ≤ kerIn M H := by
  intro hVJ
  have hVJ' : V ≤ kerIn M H ⊓ H := le_inf hVJ hVH
  have hJ'M : kerIn M H ⊓ H ≤ M := (inf_le_left : kerIn M H ⊓ H ≤ kerIn M H).trans kerIn_le
  have hJ'N : kerIn M H ⊓ H ≤ Subgroup.normalizer (V : Set G) := hJ'M.trans hMV
  have hVcore : V ≤ pCoreOf 2 (kerIn M H ⊓ H) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVJ' hJ'N hV2
  have hHnorm : H ≤ Subgroup.normalizer ((kerIn M H ⊓ H : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hJn := Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H hh) x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxJ, hxH⟩
      exact ⟨hJn.mp hxJ, H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)⟩
    · rintro ⟨hyJ, hyH⟩
      refine ⟨hJn.mpr hyJ, ?_⟩
      have h' := H.mul_mem (H.mul_mem (H.inv_mem hh) hyH) hh
      simpa [mul_assoc] using h'
  have hcoreH : pCoreOf 2 (kerIn M H ⊓ H) ≤ H :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (kerIn M H ⊓ H)).trans inf_le_right
  have hcore2 : pCoreOf 2 (kerIn M H ⊓ H) ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hcoreH
      (hHnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (kerIn M H ⊓ H)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kerIn M H ⊓ H))
  exact hVO (hVcore.trans hcore2)

theorem s828N_center_bot {A : Type} [Group A] (hs : IsSimpleGroup A) (hn : ∃ a b : A, a * b ≠ b * a) :
    ∀ x : A, (∀ y : A, x * y = y * x) → x = 1 := by
  intro x hx
  have hmem : x ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun g => (hx g).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have ha : a ∈ Subgroup.center A := by
      rw [h]
      exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem s828N_center_bot_sub {X : Type} [Group X] {S : Subgroup X} (hs : IsSimpleGroup ↥S)
    (hn : ∃ a b : ↥S, a * b ≠ b * a) : ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x = 1 := by
  intro x hx hcomm
  have h := s828N_center_bot hs hn ⟨x, hx⟩ (fun y => Subtype.ext (hcomm y.1 y.2))
  exact congrArg Subtype.val h

theorem s828N_subgroupOf_quot_equiv {H I P : Subgroup G} (hIH : I ≤ H) (hPI : P ≤ I)
    [(P.subgroupOf I).Normal] [((P.subgroupOf H).subgroupOf (I.subgroupOf H)).Normal]
    {D : Type} [Group D] (e : ↥I ⧸ P.subgroupOf I ≃* D) :
    Nonempty (↥(I.subgroupOf H) ⧸ (P.subgroupOf H).subgroupOf (I.subgroupOf H) ≃* D) := by
  have hmap : ((P.subgroupOf H).subgroupOf (I.subgroupOf H)).map
      (Subgroup.subgroupOfEquivOfLe hIH).toMonoidHom = P.subgroupOf I := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact hx
    · intro hy
      exact Subgroup.mem_map.mpr
        ⟨(Subgroup.subgroupOfEquivOfLe hIH).symm y, hy,
          (Subgroup.subgroupOfEquivOfLe hIH).apply_symm_apply y⟩
  exact ⟨(QuotientGroup.congr ((P.subgroupOf H).subgroupOf (I.subgroupOf H)) (P.subgroupOf I)
    (Subgroup.subgroupOfEquivOfLe hIH) hmap).trans e⟩

end N2a

end CFSG.Quasithin.H13
