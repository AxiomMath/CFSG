module

public import CFSG.Quasithin.EmptyFaithful.SzN28PSvGrp
public import CFSG.Quasithin.EmptyFaithful.SzN28PLift
public import CFSG.Quasithin.EmptyFaithful.S142Bridge
public import CFSG.Quasithin.EmptyFaithful.S143VSq
public import CFSG.Quasithin.EmptyFaithful.S143WCl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzN28P

section Card

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem s7_card_le_eight_of_le {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} (e : ↥Γ ≃* Equiv.Perm (Fin 7))
    (hXΓ : X ≤ Γ) (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card X ≤ 8 := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXΓ).toEquiv]
  exact s7_card_le_eight e (fun _ hx => Subtype.ext (hX2 _ hx))
    (fun _ hx _ hy => Subtype.ext (hXc _ hx _ hy))

end Card

theorem not_concl8 (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435)
    {G : Type} [Group G] [Finite G] {T M : Subgroup G} (hyp : Hyp1421 G T M) (hnot : ¬ SixModels G)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) (D : HatModel T M) {g : G}
    (hg : GoodElt128 T (yOfL22 T M) g) :
    ¬ G112Concl8 D.B (D.img (mcOf T)) (D.img (rconj (Hyp1281Two.wOfU T M) g)) := by
  rintro ⟨hd, ⟨e⟩, -⟩
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  obtain ⟨a, haV, haZ⟩ := h1281.exists_mem_VZ_not_mem
  have h101 := (h1281.lemma_12_8_12_three hU hg D haV haZ).toG101Hyp
  have hX8 := s7_card_le_eight_of_le e h101.X_le h101.X_sq h101.X_comm
  have hbot : D.img (rconj (centerOf (uOfL22 T M)) g) = ⊥ := by
    by_contra hne
    obtain ⟨k, hk⟩ := h101.exists_card_X
    have hrank := S143W.rank_le_of_ne_bot h101 hne hk
    have hk3 : k ≤ 3 := by
      by_contra hk4
      push Not at hk4
      have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      omega
    omega
  have hZU := zu_eq_v1_of_img_rconj_bot h1281 hU hg D hbot
  have hker := S143V.centralizerHat_le_T h1281 hZU
  have h35' : ∀ K : Subgroup G, InH T K → (T.relIndex K = 3 ∨ T.relIndex K = 5) → K ≤ M :=
    fun K hK hidx => h35 G T M hyp hnot K hK hidx
  obtain ⟨hTle, hT2, hTi⟩ := S143V.isSylowTwoOf_img_T h1281 D
  obtain ⟨A, B, E, hconf⟩ : ∃ A B E : Subgroup ↥(D.img (mcOf T)),
      s7_Conf ((D.img T).subgroupOf (D.img (mcOf T))) A B E :=
    s7_exists_conf e (hT2.comap_subtype (K := D.img (mcOf T))) hTi
  have hconf' := hconf.map (D.img (mcOf T)).subtype (D.img (mcOf T)).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hTle] at hconf'
  obtain ⟨hTA, hTB, hrA, hrB, hE9, hE3, hEc, hEd⟩ := hconf'
  have hfixA := fix_of_overgroup h1281 D hU haV haZ h35' hker
    (Subgroup.map_subtype_le A) hTA (Or.inl hrA)
  have hfixB := fix_of_overgroup h1281 D hU haV haZ h35' hker
    (Subgroup.map_subtype_le B) hTB (Or.inl hrB)
  have hEfix : ∀ x ∈ E.map (D.img (mcOf T)).subtype, x (D.π a) = D.π a := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hEd x hx
    show y (z (D.π a)) = D.π a
    rw [hfixB z hz, hfixA y hy]
  exact false_of_elem_three_two h1281 D hU haV haZ hZU hker (Subgroup.map_subtype_le E) hE9 hEc
    hE3 hEfix

end SzN28P

end CFSG.Quasithin
