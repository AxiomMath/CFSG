module

public import CFSG.Quasithin.Background.E3Basic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

namespace E6

open CFSG.Open
open scoped commutatorElement

structure HypE61 {G : Type} [Group G] [Finite G] (T M V : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylow : CFSG.Open.quasithinIsSylowTwo T
  inM : InM T M
  ne_bot : V ≠ ⊥
  isElemAbelian : IsElemAbelian 2 V
  le : V ≤ T
  normal : T ≤ Subgroup.normalizer (V : Set G)
  tiSet : IsTISetIn V M
  unique : IsUniqueM
    (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
      (M ⊓ Subgroup.normalizer (V : Set G))) M

section Consequences

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem HypE61.isSylowIn_top (h : HypE61 T M V) : IsSylowIn 2 T ⊤ :=
  ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩

theorem HypE61.hyp322 (h : HypE61 T M V) : E3.HypE322 T V :=
  ⟨h.isSylowIn_top, h.le, h.normal⟩

theorem HypE61.isPGroup_V (h : HypE61 T M V) : IsPGroup 2 V :=
  B2F.isPGroup_of_isElemAbelian h.isElemAbelian

theorem HypE61.le_inf_centralizer (h : HypE61 T M V) :
    V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
  le_inf h.le fun _ hv => Subgroup.mem_centralizer_iff.2 fun _ hw =>
    B2F.isElemAbelian_comm h.isElemAbelian hw hv

theorem HypE61.isPGroup_Q (h : HypE61 T M V) : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (V : Set G)) :=
  h.sylow.1.to_le inf_le_left

theorem HypE61.Q_ne_bot (h : HypE61 T M V) : T ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ :=
  fun h0 => h.ne_bot (le_bot_iff.1 (h0 ▸ h.le_inf_centralizer))

theorem HypE61.isUniqueM_of_le (h : HypE61 T M V) {X : Subgroup G} (hX1 : X ≠ ⊥)
    (hX2 : IsPGroup 2 X)
    (hle : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ⊓
      (M ⊓ Subgroup.normalizer (V : Set G)) ≤ Subgroup.normalizer (X : Set G)) :
    IsUniqueM (Subgroup.normalizer (X : Set G)) M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (X : Set G)) := ⟨X, hX1, hX2, rfl⟩
  obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
  have hMM' : M' = M := h.unique.2 M' ⟨hM', hle.trans hle'⟩
  subst hMM'
  exact ⟨⟨hM', hle'⟩, fun M'' hM'' => h.unique.2 M'' ⟨hM''.1, hle.trans hM''.2⟩⟩

theorem HypE61.isUniqueM_normalizer_Q (h : HypE61 T M V) :
    IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M :=
  h.isUniqueM_of_le h.Q_ne_bot h.isPGroup_Q inf_le_left

theorem HypE61.isUniqueM_normalizer_V (h : HypE61 T M V) :
    IsUniqueM (Subgroup.normalizer (V : Set G)) M :=
  h.isUniqueM_of_le h.ne_bot h.isPGroup_V (inf_le_right.trans inf_le_right)

theorem HypE61.normalizer_le (h : HypE61 T M V) : Subgroup.normalizer (V : Set G) ≤ M :=
  h.isUniqueM_normalizer_V.1.2

theorem HypE61.normalizer_Q_le (h : HypE61 T M V) :
    Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤ M :=
  h.isUniqueM_normalizer_Q.1.2

theorem HypE61.centralizer_le (h : HypE61 T M V) : Subgroup.centralizer (V : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans h.normalizer_le

theorem e6_2 (h : HypE61 T M V) {L : Subgroup G} (hL : ¬ L ≤ M) : ⁅V, L⁆ ≠ ⊥ := by
  intro hc
  apply hL
  have h1 : L ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.commutator_comm] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  exact h1.trans h.centralizer_le

omit [Finite G] in
theorem isSylowIn_of_le {P K K' : Subgroup G} (hP : IsSylowIn 2 P K) (hPK' : P ≤ K')
    (hK'K : K' ≤ K) : IsSylowIn 2 P K' := by
  refine ⟨hPK', hP.isPGroup, fun h2 => hP.not_dvd_relIndex (h2.trans ?_)⟩
  rw [← Subgroup.relIndex_mul_relIndex P K' K hPK' hK'K]
  exact Dvd.intro _ rfl

theorem HypE61.isSylowIn_normalizer (h : HypE61 T M V) :
    IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
  isSylowIn_of_le h.isSylowIn_top h.normal le_top

theorem HypE61.isSylowIn_centralizer (h : HypE61 T M V) :
    IsSylowIn 2 (T ⊓ Subgroup.centralizer (V : Set G)) (M ⊓ Subgroup.centralizer (V : Set G)) := by
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hnorm : ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
    intro g hg
    rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 hg]
  have h1 := h.isSylowIn_normalizer.inf_normal hCN hnorm
  exact isSylowIn_of_le h1 (inf_le_inf_right _ h.inM.2) inf_le_right

end Consequences

end E6

end CFSG.Quasithin
