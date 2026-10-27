module

public import CFSG.LocalAnalysis.WeakClosure81.EightSix
public import CFSG.LocalAnalysis.WeakClosure81.W15Seven
public import CFSG.LocalAnalysis.WeakClosure81.EightFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type*} [Group G] [Finite G]

private abbrev conjGens (V T : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V), conjSubgroup V g

private theorem inf_centralizer_ne_bot_of_le_normalizer {X T : Subgroup G}
    (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hT2 : IsPGroup 2 T) (hXne : X ≠ ⊥) :
    X ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ := by
  haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
  haveI : (X.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXT).mpr hTX
  have hXsubne : X.subgroupOf T ≠ ⊥ := by
    intro h
    apply hXne
    rw [← Subgroup.map_subgroupOf_eq_of_le hXT, h, Subgroup.map_bot]
  have hZ : X.subgroupOf T ⊓ Subgroup.center ↥T ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hXsubne
  have hZmap : ((X.subgroupOf T) ⊓ Subgroup.center ↥T).map T.subtype ≠ ⊥ :=
    fun h => hZ ((Subgroup.map_eq_bot_iff_of_injective
      ((X.subgroupOf T) ⊓ Subgroup.center ↥T) T.subtype_injective).1 h)
  refine ne_bot_of_le_ne_bot hZmap ?_
  refine (Subgroup.map_inf_le (X.subgroupOf T) (Subgroup.center ↥T) T.subtype).trans
    (inf_le_inf ?_ ?_)
  · exact (Subgroup.map_subgroupOf_eq_of_le hXT).le
  · rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨q, hq⟩)

private theorem mem_normalizer_conjGens_of_le {V T : Subgroup G} {n : G}
    (hnV : n ∈ Subgroup.normalizer (V : Set G))
    (hnT : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V (g * n) ≤ T) :
    n ∈ Subgroup.normalizer (conjGens V T : Set G) := by
  have h1 : conjSubgroup (conjGens V T) n ≤ conjGens V T := by
    have hmap : conjSubgroup (conjGens V T) n =
        ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V),
          conjSubgroup V (g * n) := by
      rw [show conjSubgroup (conjGens V T) n =
          (conjGens V T).map (MulAut.conj n⁻¹).toMonoidHom from rfl]
      unfold conjGens
      rw [Subgroup.map_iSup]
      refine iSup_congr fun g => ?_
      rw [Subgroup.map_iSup]
      refine iSup_congr fun hg => ?_
      show (conjSubgroup V g).map (MulAut.conj n⁻¹).toMonoidHom = conjSubgroup V (g * n)
      exact conjSubgroup_conjSubgroup V g n
    rw [hmap]
    refine iSup₂_le fun g hg => ?_
    change conjSubgroup V (g * n) ≤
      ⨆ (g : G) (_ : conjSubgroup V g ≤ T ∧ conjSubgroup V g ≠ V), conjSubgroup V g
    refine le_iSup₂_of_le (g * n) ⟨hnT g hg.1, ?_⟩ le_rfl
    intro hVn
    exact hg.2 (by
      calc conjSubgroup V g = conjSubgroup (conjSubgroup V (g * n)) n⁻¹ := by
            rw [conjSubgroup_conjSubgroup]; congr 1; group
        _ = conjSubgroup V n⁻¹ := by rw [hVn]
        _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr
            ((Subgroup.normalizer (V : Set G)).inv_mem hnV))
  have heq : conjSubgroup (conjGens V T) n = conjGens V T :=
    Subgroup.eq_of_le_of_card_ge h1 (E3.card_conjSubgroup (conjGens V T) n).ge
  exact conjSubgroup_eq_iff_mem_normalizer.mp heq

theorem not_centralizersInM_and_not_normalizersInMTwo {V H T K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hH : IsCalH V H)
    (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hW : E3.wClos V 0 T ≠ V) (hKH : K ≤ H) (hKM : ¬ K ≤ Subgroup.normalizer (V : Set G))
    (hKX : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≠ V →
      conjSubgroup V g ≤ Subgroup.centralizer (K : Set G)) :
    ¬ CentralizersInM V H T ∧ ¬ NormalizersInMTwo V H (E3.wClos V 0 T) := by
  classical
  have hVT : V ≤ T := le_of_isCalH hV hH hT
  have hTNV : T ≤ Subgroup.normalizer (V : Set G) := hT.le.trans inf_le_right
  have hXleT : conjGens V T ≤ T := iSup₂_le fun _ hg => hg.1
  have hXleW : conjGens V T ≤ E3.wClos V 0 T :=
    iSup₂_le fun _ hg => conjSubgroup_le_wClos_zero hg.1
  obtain ⟨g, hgT, hgV⟩ : ∃ g : G, conjSubgroup V g ≤ T ∧ ¬ conjSubgroup V g ≤ V := by
    by_contra h
    rw [not_exists] at h
    have h' : ∀ g : G, conjSubgroup V g ≤ T → conjSubgroup V g ≤ V := by
      intro g hgT
      by_contra hgV
      exact h g ⟨hgT, hgV⟩
    have hWle : E3.wClos V 0 T ≤ V := by
      rw [wClos_zero_eq_iSup hV]
      exact iSup₂_le fun g hg => h' g hg
    have hVle : V ≤ E3.wClos V 0 T := by
      have h1 : conjSubgroup V 1 ≤ T := by rwa [conjSubgroup_one]
      have h2 : conjSubgroup V 1 ≤ E3.wClos V 0 T := conjSubgroup_le_wClos_zero h1
      rwa [conjSubgroup_one] at h2
    exact hW (le_antisymm hWle hVle)
  have hgne : conjSubgroup V g ≠ V := fun h => hgV (le_of_eq h)
  have hgX : conjSubgroup V g ≤ conjGens V T := le_iSup₂_of_le g ⟨hgT, hgne⟩ le_rfl
  have hXne : conjGens V T ≠ ⊥ := by
    intro hbot
    exact hgV ((le_bot_iff.mp (hbot ▸ hgX)).le.trans bot_le)
  have hXCK : conjGens V T ≤ Subgroup.centralizer (K : Set G) :=
    iSup₂_le fun g hg => hKX g hg.1 hg.2
  have hKCX : K ≤ Subgroup.centralizer (conjGens V T : Set G) :=
    Subgroup.le_centralizer_iff.mpr hXCK
  have hKNX : K ≤ Subgroup.normalizer (conjGens V T : Set G) :=
    hKCX.trans (Subgroup.centralizer_le_normalizer (conjGens V T : Set G))
  have hTNX : T ≤ Subgroup.normalizer (conjGens V T : Set G) := by
    intro n hn
    exact mem_normalizer_conjGens_of_le (hTNV hn) (by
      intro g hg
      calc conjSubgroup V (g * n) = conjSubgroup (conjSubgroup V g) n :=
            (conjSubgroup_conjSubgroup V g n).symm
        _ ≤ conjSubgroup T n := Subgroup.map_mono hg
        _ = T := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hn))
  have hNVNWNX : Subgroup.normalizer (V : Set G) ⊓
      Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤
      Subgroup.normalizer (conjGens V T : Set G) := by
    intro n hn
    obtain ⟨hnV, hnW⟩ := Subgroup.mem_inf.mp hn
    exact mem_normalizer_conjGens_of_le hnV (by
      intro g hg
      calc conjSubgroup V (g * n) = conjSubgroup (conjSubgroup V g) n :=
            (conjSubgroup_conjSubgroup V g n).symm
        _ ≤ conjSubgroup (E3.wClos V 0 T) n :=
            Subgroup.map_mono (conjSubgroup_le_wClos_zero hg)
        _ = E3.wClos V 0 T := conjSubgroup_eq_iff_mem_normalizer.mpr hnW
        _ ≤ T := wClos_zero_le V T)
  have hXCTne : conjGens V T ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_le_normalizer hXleT hTNX hT.isPGroup hXne
  obtain ⟨z, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXCTne
  have hz1 : (z : G) ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hzX : (z : G) ∈ conjGens V T := z.2.1
  have hzC : (z : G) ∈ Subgroup.centralizer (T : Set G) := z.2.2
  have hzT : (z : G) ∈ T := hXleT hzX
  have hKz : K ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
    intro k hk
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (hXCK hzX) k hk).symm
  have hnotCIM : ¬ CentralizersInM V H T := by
    intro hCIM
    have hHz : H ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≤
        Subgroup.normalizer (V : Set G) :=
      hCIM (z : G) hzT (fun t ht => (Subgroup.mem_centralizer_iff.mp hzC t ht).symm) hz1
    exact hKM ((le_inf hKH hKz).trans hHz)
  have hnotNIM : ¬ NormalizersInMTwo V H (E3.wClos V 0 T) := by
    intro hNIM
    have hXle : conjGens V T ≤
        Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) :=
      le_inf (hXleT.trans hTNV) (hXleW.trans Subgroup.le_normalizer)
    have hHX : H ⊓ Subgroup.normalizer (conjGens V T : Set G) ≤
        Subgroup.normalizer (V : Set G) :=
      hNIM (conjGens V T) hXne (hT.isPGroup.to_le hXleT) hXle hNVNWNX
    exact hKM ((le_inf hKH hKNX).trans hHX)
  exact ⟨hnotCIM, hnotNIM⟩

end CFSG.LocalAnalysis.WeakClosure81

end
