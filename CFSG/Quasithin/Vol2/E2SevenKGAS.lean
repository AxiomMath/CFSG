module

public import CFSG.Quasithin.Background.E2TwoProofDefs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G]

theorem mem_zOf_subgroupOf_iff {X S : Subgroup G} (hSX : S ≤ X) (z : ↥X) :
    z ∈ E2P.zOf (S.subgroupOf X) ↔ (z : G) ∈ E2P.zOf S := by
  simp only [E2P.zOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨hz, fun s hs => ?_⟩
    have := hc ⟨s, hSX hs⟩ hs
    simpa using congrArg Subtype.val this
  · rintro ⟨hz, hc⟩
    exact ⟨hz, fun s hs => Subtype.ext (by simpa using hc s hs)⟩

theorem mem_centralizer_zOf_subgroupOf_iff {X S : Subgroup G} (hSX : S ≤ X) (y : ↥X) :
    y ∈ Subgroup.centralizer (E2P.zOf (S.subgroupOf X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.centralizer (E2P.zOf S : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h w hw
    have hwX : w ∈ X := hSX hw.1
    have := h ⟨w, hwX⟩ ((mem_zOf_subgroupOf_iff hSX _).mpr hw)
    simpa using congrArg Subtype.val this
  · intro h w hw
    exact Subtype.ext (by simpa using h w ((mem_zOf_subgroupOf_iff hSX w).mp hw))

theorem inf_subgroupOf_eq_of_inf_eq {X T M K : Subgroup G} (hKX : K ≤ X)
    (hMK : M ⊓ K = K ⊓ Subgroup.centralizer (E2P.zOf (T ⊓ K) : Set G)) :
    M.subgroupOf X ⊓ K.subgroupOf X = K.subgroupOf X ⊓
      Subgroup.centralizer (E2P.zOf (T.subgroupOf X ⊓ K.subgroupOf X) : Set ↥X) := by
  have hTKX : (T ⊓ K).subgroupOf X = T.subgroupOf X ⊓ K.subgroupOf X := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  ext y
  rw [← hTKX, Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_zOf_subgroupOf_iff
    (inf_le_right.trans hKX), Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have := congrArg (fun H : Subgroup G => (y : G) ∈ H) hMK
  simp only [Subgroup.mem_inf] at this
  exact this.to_iff.trans (by rfl)

variable [Finite G]

theorem pCoreOf_le_of_minParabolic {X T M : Subgroup G} (hP : MinParabolic X T M) :
    pCoreOf 2 M ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  exact A4.le_of_normal_of_isSylowTwoOf (isSylowTwoOf_mono hP.isSylow hTM hMmax.le)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem subgroupOf_le_pCoreOf {X M V : Subgroup G} (hMX : M ≤ X) (hVO : V ≤ pCoreOf 2 M) :
    V.subgroupOf X ≤ pCoreOf 2 (M.subgroupOf X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.subgroupOf_mono _ hVO).trans ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.subgroupOf_mono _ (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) ?_ ?_
  · intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (Subgroup.mem_subgroupOf.mp hm)) y
    simpa using this
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv (Subgroup.subgroupOfEquivOfLe
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans hMX)).symm

theorem asHyp_subgroupOf {X T M K : Subgroup G} (hP : MinParabolic X T M) (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (hKT : K ⊔ T = X) (hsK : IsSimpleGroup ↥K) :
    E2P.ASHyp (K.subgroupOf X) (T.subgroupOf X) (M.subgroupOf X) := by
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hsK' : IsSimpleGroup ↥(K.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hKX).isSimpleGroup
  have hnab : ∃ a b : ↥(K.subgroupOf X), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hKC : K ≤ X ⊓ Subgroup.centralizer (K : Set G) := fun k hk =>
      ⟨hKX hk, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        have := hcon ⟨⟨y, hKX hy⟩, hy⟩ ⟨⟨k, hKX hk⟩, hk⟩
        simpa using congrArg (fun w : ↥(K.subgroupOf X) => ((w : ↥X) : G)) this⟩
    rw [hC, le_bot_iff] at hKC
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥K)
    have haK : (a : G) ∈ (⊥ : Subgroup G) := hKC ▸ a.2
    exact ha (Subtype.ext (Subgroup.mem_bot.mp haK))
  have hcent : Subgroup.centralizer ((K.subgroupOf X : Subgroup ↥X) : Set ↥X) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyC : (y : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := ⟨y.2,
      Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := Subgroup.mem_centralizer_iff.mp hy ⟨k, hKX hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
        simpa using congrArg Subtype.val this⟩
    rw [hC] at hyC
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hyC))
  have hsup : K.subgroupOf X ⊔ T.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKX hP.isSylow.1, hKT, Subgroup.subgroupOf_self]
  exact ⟨hP.subgroupOf, hKn, hsK', hnab, hsup, hcent⟩

end E2

end CFSG.Quasithin
