module

public import CFSG.Quasithin.EmptyFaithful.S151S4F

import CFSG.Quasithin.Background.B15P4Layer2Final

public section

namespace CFSG.Quasithin.C116Bridge

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

private theorem c116_evenWeight_one_subsingleton : Subsingleton ↥(evenWeight 1) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : ∀ z : ↥(evenWeight 1), (z : Fin 1 → ZMod 2) = 0 := by
    intro z
    have hsum : ∑ j, (z : Fin 1 → ZMod 2) j = 0 := by
      have := z.2
      simpa [evenWeight] using this
    funext j
    rw [Fin.sum_univ_one] at hsum
    rw [Subsingleton.elim j 0, Pi.zero_apply]
    exact hsum
  rw [hx x, hx y]

private theorem c116_not_isAltType_one {L : Subgroup G} (hS : IsShort2 L) : ¬ IsAltType L 1 := by
  rintro ⟨_, -, -, β, -, hβker, -⟩
  haveI : Subsingleton ↥(evenWeight 1) := c116_evenWeight_one_subsingleton
  haveI : Subsingleton (Multiplicative ↥(evenWeight 1)) :=
    ⟨fun a b => Multiplicative.toAdd.injective (Subsingleton.elim _ _)⟩
  have hker : (blockZ L).subgroupOf (blockU L) = ⊤ := by
    rw [← hβker, Subgroup.eq_top_iff']
    exact fun u => MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
  have hle : blockU L ≤ blockZ L := by
    intro u hu
    have hmem : (⟨u, hu⟩ : ↥(blockU L)) ∈ (blockZ L).subgroupOf (blockU L) := by
      rw [hker]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  exact absurd hle (not_le_of_gt hS.2.2.2.2.1)

theorem isChiBlock_of_isChiBlock2 {X L : Subgroup G} (h : IsChiBlock2 X L) : IsChiBlock X L := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hl | ⟨m, hm, hA⟩
  · exact Or.inl hl
  · obtain ⟨k, rfl⟩ := hm
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exact absurd hA (c116_not_isAltType_one h.1.1)
    · exact Or.inr ⟨2 * k + 1, ⟨k, rfl⟩, by omega, hA⟩

theorem isSQTKTC_of_isSQTKIn {X : Subgroup G} (h : IsSQTKIn X) : IsSQTKTC X := by
  exact C1GN.isSQTKTC_iff_sqtkGroup.mpr h

private theorem c116_autOn_commutator {V A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autOn ⁅A, B⁆ V = ⁅autOn A V, autOn B V⁆ := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : ⁅A, B⁆.subgroupOf N = ⁅A.subgroupOf N, B.subgroupOf N⁆ := by
    have e : ⁅A.subgroupOf N, B.subgroupOf N⁆.map N.subtype = ⁅A, B⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
        Subgroup.map_subgroupOf_eq_of_le hB]
    rw [← e]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  unfold autOn
  rw [h1, Subgroup.map_commutator]

theorem not_commutator_le_centralizer {X V L J : Subgroup G} (hred : IsTwoReducedIn X V)
    (hL : L ≤ X) (hJ : J ≤ X) (h : ⁅autOn L V, autOn J V⁆ ≠ ⊥) :
    ¬ ⁅L, J⁆ ≤ Subgroup.centralizer (V : Set G) := by
  intro hle
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hL.trans hred.2.1
  have hJN : J ≤ Subgroup.normalizer (V : Set G) := hJ.trans hred.2.1
  have hcomm : ⁅L, J⁆ ≤ Subgroup.normalizer (V : Set G) := by
    refine Subgroup.commutator_le.mpr fun l hl j hj => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLN hl) (hJN hj))
      (Subgroup.inv_mem _ (hLN hl))) (Subgroup.inv_mem _ (hJN hj))
  apply h
  rw [← c116_autOn_commutator hLN hJN]
  exact (autI_eq_bot_iff hred.2.2.1 hcomm).mpr hle

theorem quasiData_of_autOn {X V L : Subgroup G} (hred : IsTwoReducedIn X V) (hL : L ≤ X)
    (h : CFSG.IsQuasisimple ↥(autOn L V)) :
    ∃ (Q : Type) (_ : Group Q) (φ : ↥L →* Q), Function.Surjective φ ∧
      φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L ∧ CFSG.IsQuasisimple Q := by
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := hL.trans hred.2.1
  have hq : CFSG.IsQuasisimple ↥(convHom hred.2.2.1 L hLN).range := by
    rw [range_convHom hred.2.2.1 L hLN]
    exact h
  refine ⟨↥(convHom hred.2.2.1 L hLN).range, inferInstance,
    (convHom hred.2.2.1 L hLN).rangeRestrict,
    (convHom hred.2.2.1 L hLN).rangeRestrict_surjective, ?_, hq⟩
  rw [MonoidHom.ker_rangeRestrict, ker_convHom]
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h' => h'.2, fun h' => ⟨x.2, h'⟩⟩

private theorem c116_autI_thompsonJ_le_ffJ {X V S : Subgroup G} (hred : IsTwoReducedIn X V)
    (hS : IsSylowTwoOf S X) : autI hred.2.2.1 (thompsonJ S) ≤ ffJ (autI hred.2.2.1 X) := by
  refine (autI_mono hred.2.2.1 (thompsonJ_le_thompsonJ_of_isSylowTwoOf hS)).trans ?_
  rw [autI_thompsonJ hred.2.2.1 hred.2.1]
  refine iSup_le fun A => iSup_le fun hA => iSup_le fun hAH => ?_
  exact le_iSup₂ (f := fun (B : Subgroup (MulAut (IntMod V hred.2.2.1)))
    (_ : IsFFStarOffender (autI hred.2.2.1 X) B) => B) A
    (offenderImages_isFFStarOffender hred.2.2.1 hred.1 hred.2.1 hA)

theorem thompsonJ_normalizes_components {X V T : Subgroup G} (hred : IsTwoReducedIn X V)
    (hT : IsSylowTwoOf T X) :
    ∀ K : Subgroup (MulAut ↥V), CFSG.Open.IsComponentOf K (autOn X V) →
      autOn (thompsonJ T) V ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) := by
  intro K hK
  have hle : autI hred.2.2.1 (thompsonJ T) ≤ ffJ (autI hred.2.2.1 X) :=
    c116_autI_thompsonJ_le_ffJ hred hT
  have hff : ffJ (autI hred.2.2.1 X) ≤ Subgroup.normalizer (K : Set (MulAut ↥V)) := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    exact CFSG.Quasithin.B15P4.asB15Part4 (IntMod V hred.2.2.1) (fun v => IntMod.sq_eq_one v)
      (autI hred.2.2.1 X) A hA K hK
  exact hle.trans hff

theorem c116_of (hC2 : TheoremC116Two) (hC3 : TheoremC116Three) {X V T : Subgroup G}
    (hchar : CharTwo X) (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X) :
    (∀ K : Subgroup (MulAut ↥V), CFSG.Open.IsComponentOf K (autOn X V) →
      autOn (thompsonJ T) V ≤ Subgroup.normalizer (K : Set (MulAut ↥V))) ∧
    (∀ L : Subgroup G, IsChiBlock2 X L →
      ⁅autOn L V, autOn (thompsonJ T) V⁆ ≠ ⊥ → baum T ≤ Subgroup.normalizer (L : Set G)) ∧
    (IsSQTKIn X → ∀ L : Subgroup G, L ∈ cComp X → CFSG.IsQuasisimple ↥(autOn L V) →
      ⁅autOn L V, autOn (thompsonJ T) V⁆ ≠ ⊥ → baum T ≤ Subgroup.normalizer (L : Set G)) := by
  have hJX : thompsonJ T ≤ X :=
    (CFSG.QuasithinUnique.GammaExtra.thompsonJ_le_self T).trans hT.1
  refine ⟨thompsonJ_normalizes_components hred hT, fun L hL hne => ?_,
    fun hX L hLc hq hne => ?_⟩
  · exact hC2 G X T V L hchar hred hT (isChiBlock_of_isChiBlock2 hL)
      (not_commutator_le_centralizer hred hL.1.2.1 hJX hne)
  · exact hC3 G X T V L hchar hred hT (isSQTKTC_of_isSQTKIn hX) hLc
      (quasiData_of_autOn hred (le_of_mem_cComp hLc) hq)
      (not_commutator_le_centralizer hred (le_of_mem_cComp hLc) hJX hne)

end CFSG.Quasithin.C116Bridge
