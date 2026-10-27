module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.Quasithin.EmptyFaithful.S146zRSL
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

namespace S1421

section Abstract

variable {L' : Type*} [Group L'] [Finite L']

theorem eq_top_of_map_eq_top_or_solvable {Y : Type*} [Group Y] (α : L' →* Y) {A : Subgroup L'}
    (hker : IsPGroup 2 α.ker) (hkA : α.ker ≤ A) (hA : ¬ Group.IsSolvable ↥A)
    (h : A.map α = ⊤ ∨ Group.IsSolvable ↥(A.map α)) : A = ⊤ := by
  rcases h with h | h
  · have h1 : A ⊔ α.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, h, Subgroup.comap_top]
    rwa [sup_eq_left.mpr hkA] at h1
  · exfalso
    refine hA ?_
    have : Group.IsNilpotent ↥α.ker := hker.isNilpotent
    have : Group.IsSolvable ↥α.ker := inferInstance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hkA) (α.subgroupMap A) ?_
    intro a ha
    have h1 : α (a : L') = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    exact ⟨⟨(a : L'), h1⟩, rfl⟩

theorem sup_eq_top_of_lin2 {F : Type} [Field F] [Fintype F] {m : ℕ}
    (hF : Fintype.card F = 2 ^ m) (hm : 0 < m) (α : L' →* SL(2, F))
    (hα : Function.Surjective α) {K S : Subgroup L'} (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index)
    (hker : α.ker ≤ S) (hK : ¬ Group.IsSolvable ↥K) : K ⊔ S = ⊤ := by
  have hidx : (S.map α).index = S.index := by
    rw [← Subgroup.index_comap_of_surjective (S.map α) hα, Subgroup.comap_map_eq,
      sup_eq_left.mpr hker]
  have hP : IsSylowTwoOf (S.map α) ⊤ := by
    refine ⟨le_top, hS.map α, ?_⟩
    show ¬ 2 ∣ (S.map α).relIndex ⊤
    rw [Subgroup.relIndex_top_right, hidx]
    exact hodd
  have hns : ¬ Group.IsSolvable ↥(K ⊔ S) := fun _hs =>
    hK (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : K ≤ K ⊔ S)))
  refine eq_top_of_map_eq_top_or_solvable α (hS.to_le hker) (hker.trans le_sup_right) hns ?_
  rcases Lin2.dicksonLite hF hm hP (Subgroup.map_mono (le_sup_right : S ≤ K ⊔ S)) with h | h
  · exact Or.inl h
  · right
    have : Finite F := Finite.of_fintype F
    have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm
        (by rw [Nat.card_eq_fintype_card]; exact hF)
    have hsolv := (sl2_normalizer_solvable_dvd (MulEquiv.refl SL(2, F)) (hS.map α)
      (by rw [hidx]; exact hodd)).1
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)

theorem sup_eq_top_of_alt5 (α : L' →* alternatingGroup (Fin 5)) {K S : Subgroup L'}
    (hS : IsPGroup 2 S) (hker : α.ker ≤ S) (hK : ¬ Group.IsSolvable ↥K) : K ⊔ S = ⊤ := by
  have hns : ¬ Group.IsSolvable ↥(K ⊔ S) := fun _hs =>
    hK (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : K ≤ K ⊔ S)))
  refine eq_top_of_map_eq_top_or_solvable α (hS.to_le hker) (hker.trans le_sup_right) hns ?_
  by_cases htop : (K ⊔ S).map α = ⊤
  · exact Or.inl htop
  · right
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have hle := Subgroup.card_le_card_group ((K ⊔ S).map α)
    have hne : Nat.card ↥((K ⊔ S).map α) ≠ Nat.card (alternatingGroup (Fin 5)) := fun h =>
      htop ((Subgroup.card_eq_iff_eq_top _).mp h)
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega

theorem false_of_perfect_of_alt3 {M : Type*} [Group M] (hperf : commutator M = ⊤)
    (α : M →* alternatingGroup (Fin 3)) (hα : Function.Surjective α) : False := by
  have hle : commutator M ≤ α.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    generalize α g₁ = a
    generalize α g₂ = b
    revert a b
    decide
  rw [hperf, top_le_iff] at hle
  obtain ⟨c, hc⟩ : ∃ c : alternatingGroup (Fin 3), c ≠ 1 := by decide
  obtain ⟨x, rfl⟩ := hα c
  exact hc (by rw [← MonoidHom.mem_ker, hle]; exact Subgroup.mem_top x)

end Abstract

section Ambient

variable {G : Type*} [Group G]

theorem commutator_eq_top_of_perfect {L : Subgroup G} (h : ⁅L, L⁆ = L) :
    commutator ↥L = ⊤ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]

theorem not_isSolvable_of_perfect_of_ne_bot [Finite G] {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hne : K ≠ ⊥) : ¬ Group.IsSolvable ↥K := by
  intro hs
  have h1 := (isSolvable_iff_perfectCore_eq_bot K).mp hs
  rw [perfectCore_eq_self_of_perfect hK] at h1
  exact hne h1

theorem not_isSolvable_subgroupOf {K L : Subgroup G} (hKL : K ≤ L) (hK : ¬ Group.IsSolvable ↥K) :
    ¬ Group.IsSolvable ↥(K.subgroupOf L) := fun _hs =>
  hK (Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKL).symm.injective)

theorem pCore_le_subgroupOf_of_isSylowTwoOf {L S₁ : Subgroup G} (hS₁ : IsSylowTwoOf S₁ L) :
    CFSG.pCore 2 ↥L ≤ S₁.subgroupOf L := by
  have hS2 : IsPGroup 2 (S₁.subgroupOf L) :=
    hS₁.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₁.1).symm
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  exact CFSG.pCore_isPGroup.le_sylow_of_normal (hS2.toSylow hS₁.2.2)

end Ambient

theorem false_of_isChi0Block_of_perfect_lt {G : Type} [Group G] [Finite G]
    {G0 L K1 S X : Subgroup G} (hL : L ∈ cComp G0) (hLn : (L.subgroupOf G0).Normal)
    (hS : IsSylowTwoOf S G0) (hSK : S ≤ Subgroup.normalizer (K1 : Set G)) (hK1L : K1 < L)
    (hK1p : ⁅K1, K1⁆ = K1) (hK1ne : K1 ≠ ⊥) (hblk : IsChi0Block X L) : False := by
  have hLG0 : L ≤ G0 := le_of_mem_cComp hL
  have hnormL : G0 ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG0).mp hLn
  have hS₁ : IsSylowTwoOf (S ⊓ L) L := A4.isSylowTwoOf_inf_normal hS hLG0 hnormL
  have hS'2 : IsPGroup 2 ((S ⊓ L).subgroupOf L) :=
    hS₁.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₁.1).symm
  have hker := pCore_le_subgroupOf_of_isSylowTwoOf hS₁
  have hKns : ¬ Group.IsSolvable ↥(K1.subgroupOf L) :=
    not_isSolvable_subgroupOf hK1L.le (not_isSolvable_of_perfect_of_ne_bot hK1p hK1ne)
  have hsup : K1.subgroupOf L ⊔ (S ⊓ L).subgroupOf L = ⊤ := by
    rcases hblk.2 with ⟨n, hn, F, _, _, hcard, α, hαs, hαk, -⟩ | ⟨α, hαs, -, -⟩ | ⟨α, hαs, hαk, -⟩
    · exact sup_eq_top_of_lin2 hcard (by omega) α hαs hS'2 hS₁.2.2 (hαk ▸ hker) hKns
    · exact (false_of_perfect_of_alt3 (commutator_eq_top_of_perfect (perfect_of_mem_cComp hL)) α
        hαs).elim
    · exact sup_eq_top_of_alt5 α hS'2 (hαk ▸ hker) hKns
  have hSK' : (S ⊓ L).subgroupOf L ≤ Subgroup.normalizer (K1.subgroupOf L : Set ↥L) := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simpa [Subgroup.mem_subgroupOf] using
      Subgroup.mem_normalizer_iff.mp (hSK hs.1) (y : G)
  have hnorm : (K1.subgroupOf L).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer hSK'
  exact not_subnormal_of_mem_cComp hL hK1L hK1ne hK1p
    (A3.subnormal_trans (A3.subnormal_of_normal hK1L.le hnorm) (subnormal_of_mem_cComp hL))

end S1421

end CFSG.Quasithin
