module

public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem s151s_sylow_not_central {L B : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥L) (hB : IsSylowTwoOf B L)
    (hcent : ∀ b ∈ B, ∀ l ∈ L, b * l = l * b) : False := by
  have hBL : B ≤ L := hB.1
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  have hBc : B.subgroupOf L ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := hcent (x : G) ((Subgroup.mem_subgroupOf.mp hx)) (g : G) g.2
    exact Subtype.ext this.symm
  have hodd : Odd (Nat.card (↥L ⧸ Subgroup.center ↥L)) := by
    rw [← Subgroup.index_eq_card]
    have hdvd : (Subgroup.center ↥L).index ∣ (B.subgroupOf L).index := Subgroup.index_dvd_of_le hBc
    have h2 : ¬ 2 ∣ (Subgroup.center ↥L).index := fun h => hB.2.2 (dvd_trans h hdvd)
    exact Nat.odd_iff.mpr (by omega)
  have hsolvQ : Group.IsSolvable (↥L ⧸ Subgroup.center ↥L) := CFSG.Milestones.odd_order_solvable hodd
  have hsolv : Group.IsSolvable ↥L := by
    have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ (Subgroup.center ↥L).subtype.range := by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
    exact Group.isSolvable_of_ker_le_range (Subgroup.center ↥L).subtype (QuotientGroup.mk' (Subgroup.center ↥L)) hker
  exact Group.IsPerfect.not_isSolvable ↥L hsolv


theorem s151s_z_normalizes {Z₁ L S : Subgroup G} {z : G} (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hzG : z ∈ g1_1516 Z₁) (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hzB : ∀ x ∈ S, z * x * z⁻¹ = x) : z ∈ Subgroup.normalizer (L : Set G) := by
  have hconjG : (g1_1516 Z₁).map (MulAut.conj z).toMonoidHom = g1_1516 Z₁ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem hzG hv) ((g1_1516 Z₁).inv_mem hzG)
    · intro hw
      refine ⟨z⁻¹ * w * z, (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem
        ((g1_1516 Z₁).inv_mem hzG) hw) hzG, ?_⟩
      show z * (z⁻¹ * w * z) * z⁻¹ = w
      group
  have hsub : IsSubnormal (L.map (MulAut.conj z).toMonoidHom) (g1_1516 Z₁) := by
    have h1 := A3.subnormal_map (MulAut.conj z).toMonoidHom hcomp.2.1
    rwa [hconjG] at h1
  rcases B113.component_le_or_commutator_eq_bot hcomp hsub with hle | hcomm
  · have hcard : Nat.card ↥(L.map (MulAut.conj z).toMonoidHom) = Nat.card ↥L :=
      Subgroup.card_map_of_injective (MulAut.conj z).injective
    have heq : L = L.map (MulAut.conj z).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle hcard.le
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 heq.symm
  · exfalso
    refine s151s_sylow_not_central hcomp.2.2 hSyl (fun b hb l hl => ?_)
    have hbLz : b ∈ L.map (MulAut.conj z).toMonoidHom :=
      ⟨b, hb.2, by show z * b * z⁻¹ = b; exact hzB _ hb.1⟩
    have hLC : L ≤ Subgroup.centralizer ((L.map (MulAut.conj z).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact Subgroup.mem_centralizer_iff.1 (hLC hl) b hbLz

omit [Finite G] in
@[expose] def AutFixOn (L B : Subgroup G) : Prop :=
  ∀ z : G, z ∈ Subgroup.normalizer (L : Set G) → z ^ 2 = 1 → (∀ x ∈ B, z * x = x * z) →
    ∃ b ∈ centerOf B, ∀ l ∈ L, z * l * z⁻¹ = b * l * b⁻¹

theorem s151s_cent_le_mZ {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hfix : AutFixOn L (s1516 T Z₁ ⊓ L)) :
    L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) ≤ mZ1516 Mc Z₁ ⊓ L := by
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ctx.qtfe.omegaOneCenter_ne_bot
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hyp := hc.h18.six z hzZ hz1
  have hzC : z ∈ Subgroup.centralizer (s1516 T Z₁ : Set G) := hyp.z_central
  have hzG : z ∈ g1_1516 Z₁ := hyp.z_mem_H
  have hzcz : Subgroup.centralizer ({z} : Set G) ≤ Mc := hyp.centralizer_z_le
  have hzB : ∀ x ∈ s1516 T Z₁, z * x * z⁻¹ = x := fun x hx => by
    have h := Subgroup.mem_centralizer_iff.1 hzC x hx
    rw [← h]
    group
  have hzN := s151s_z_normalizes hcomp hzG hSyl hzB
  have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenter T hzZ
  have hzfix : ∀ x ∈ s1516 T Z₁ ⊓ L, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 hzC x hx.1).symm
  obtain ⟨b, hb, hbe⟩ := hfix z hzN hz2 hzfix
  intro x hx
  obtain ⟨hxL, hxC⟩ := hx
  refine ⟨⟨hcomp.1 hxL, hzcz ?_⟩, hxL⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hbx : b * x = x * b := Subgroup.mem_centralizer_iff.1 hxC b hb
  have h1 := hbe x hxL
  have h2 : b * x * b⁻¹ = x := by
    rw [hbx]
    group
  rw [h2] at h1
  have h5 : z * x = x * z := calc
    z * x = (z * x * z⁻¹) * z := by group
    _ = x * z := by rw [h1]
  exact h5.symm


theorem s151s_mZ_eq_of_loc {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hfix : AutFixOn L (s1516 T Z₁ ⊓ L))
    (hmax : IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G))) :
    mZ1516 Mc Z₁ ⊓ L = L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) := by
  have hcle := s151s_cent_le_mZ hc hcomp hfix
  refine le_antisymm ?_ hcle
  by_contra hnle
  have hlt : L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G) < mZ1516 Mc Z₁ ⊓ L :=
    lt_of_le_of_ne hcle fun h => hnle (le_of_eq h.symm)
  have hL : mZ1516 Mc Z₁ ⊓ L = L := hmax.2 _ hlt inf_le_right
  exact hc.hL.not_le (hL ▸ inf_le_left)

@[expose] def CompTypeDEasy15120 (L : Subgroup G) : Prop :=
  IsSporadic .M11 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M12 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .J2 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .He (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def CompTypeDHard15120 (L : Subgroup G) : Prop :=
  IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
    IsSporadic .M24 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)

omit [Finite G] in
theorem compTypeD_easy_or_hard {L : Subgroup G} (h : CompTypeD15120 L) :
    CompTypeDEasy15120 L ∨ CompTypeDHard15120 L := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

@[expose] def Input15120CentLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L B : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) → IsSylowTwoOf B L →
    ((IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∨ CompTypeD15120 L) →
      AutFixOn L B ∧
        (((IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∨ CompTypeDEasy15120 L) →
          IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (centerOf B : Set G)))

theorem input15120MLC_of_loc (hloc : Input15120CentLoc) : Input15120MLC := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hC
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hZ : IsPGroup 2 (Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  obtain ⟨hfix, hmax⟩ := hloc G L _ hcomp.2.2 hZ hSyl (Or.inl hC)
  exact s151s_mZ_eq_of_loc hc hcomp hfix (hmax (Or.inl hC))

@[expose] def Input15120MLDHard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → CompTypeD15120 L →
    CompTypeDHard15120 L →
    mZ1516 Mc Z₁ ⊓ L ≤ L ⊓ Subgroup.centralizer (centerOf (s1516 T Z₁ ⊓ L) : Set G)

theorem input15120MLD_of_loc (hloc : Input15120CentLoc) (hhard : Input15120MLDHard) :
    Input15120MLD := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD _
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hZ : IsPGroup 2 (Subgroup.center ↥L) :=
    isPGroup_two_center_of_isComponentOf1515c hcomp hc.h19.one
  obtain ⟨hfix, hmax⟩ := hloc G L _ hcomp.2.2 hZ hSyl (Or.inr hD)
  rcases compTypeD_easy_or_hard hD with hE | hH
  · exact s151s_mZ_eq_of_loc hc hcomp hfix (hmax (Or.inr hE))
  · exact le_antisymm (hhard G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hD hH) (s151s_cent_le_mZ hc hcomp hfix)

end CFSG.Quasithin
