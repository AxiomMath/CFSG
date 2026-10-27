module

public import CFSG.Quasithin.Vol2.Ch11SecBK2E
public import CFSG.Quasithin.Vol2.Ch11SecAKA20
public import CFSG.Quasithin.Vol2.Ch11SecAViLevi
public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight
public import CFSG.Quasithin.Vol2.Ch11SecBFacts24

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace BK2

variable {G : Type} [Group G] [Finite G]

theorem l2Point_of {L V X T V₁ V₂ : Subgroup G} {n : ℕ} (hfl : Flag24 L V X T V₁ V₂ n)
    (hc : ∀ u ∈ V₂.subgroupOf V,
      (∀ s ∈ perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V)), s u = u) →
        u ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V)
    (hpt : ∀ Q : Subgroup (MulAut ↥V), QuasithinUnique.IsSylowTwoOf Q
        (perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V))) →
      ∀ Y : Subgroup ↥V, (Subgroup.centralizer (L : Set G)).subgroupOf V ≤ Y →
        Y ≤ V₂.subgroupOf V →
        ((Subgroup.centralizer (L : Set G)).subgroupOf V).relIndex Y = 2 ^ n →
        Q ≤ SecA.stabW Y →
        ∃ x ∈ perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V)),
          ∀ w, w ∈ Y ↔ x w ∈ V₁.subgroupOf V) :
    V₂ ⊓ Subgroup.centralizer (LOf L V₂ : Set G) = V ⊓ Subgroup.centralizer (L : Set G) ∧
      ∀ U S : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ U → U ≤ V₂ →
        (V ⊓ Subgroup.centralizer (L : Set G)).relIndex U = 2 ^ n →
        QuasithinUnique.IsSylowTwoOf S (LOf L V₂) → S ≤ Subgroup.normalizer (U : Set G) →
          ∃ l ∈ LOf L V₂, U = conjSubgroup V₁ l := by
  have hLV := hfl.le_normalizer
  have hV₂ := hfl.le₂
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hL₂V : LOf L V₂ ≤ Subgroup.normalizer (V : Set G) := hL₂L.trans hLV
  have hS₂ : autOn (LOf L V₂) V = perfectCore (autOn L V ⊓ SecA.stabW (V₂.subgroupOf V)) := by
    rw [SecA.autOn_perfectCore (inf_le_left.trans hLV), SecA.autOn_inf_normalizer hV₂]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro v ⟨hv, hvc⟩
    have hvV := hV₂ hv
    refine ⟨hvV, hc ⟨v, hvV⟩ hv fun s hs => ?_⟩
    rw [← hS₂] at hs
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    apply Subtype.ext
    rw [SecA.conjV_apply_coe, Subgroup.mem_centralizer_iff.mp hvc l hl, mul_inv_cancel_right]
  · rintro v ⟨hv, hvc⟩
    exact ⟨hfl.le₁₂ (hfl.cV_le ⟨hv, hvc⟩), Subgroup.centralizer_le hL₂L hvc⟩
  · intro U S hCU hUV₂ hidx hS hSU
    have hUV := hUV₂.trans hV₂
    have hQ := SecA.isSylowTwoOf_autOn hL₂V hS
    rw [hS₂] at hQ
    have hQY : autOn S V ≤ SecA.stabW (U.subgroupOf V) := by
      intro x hx
      obtain ⟨s, hs, hsV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact (SecA.conjV_mem_stabW_iff hUV hsV).mpr (hSU hs)
    obtain ⟨x, hx, hxY⟩ := hpt _ hQ (U.subgroupOf V) (fun z hz => hCU ⟨z.2, hz⟩)
      (fun u hu => hUV₂ hu)
      (by rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hUV, hidx]) hQY
    rw [← hS₂] at hx
    obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hx
    refine ⟨l, hl, ?_⟩
    ext w
    rw [mem_conjSubgroup_iff]
    by_cases hw : w ∈ V
    · have h1 := hxY ⟨w, hw⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, SecA.conjV_apply_coe] at h1
      exact h1
    · have h1 : l * w * l⁻¹ ∉ V := fun h => hw ((Subgroup.mem_normalizer_iff.mp hlV w).mpr h)
      exact ⟨fun h => absurd (hUV h) hw, fun h => absurd ((hfl.le₁₂.trans hV₂) h) h1⟩

end BK2

theorem factL2Point_holds : FactL2Point := by
  intro G _ _ L V X T V₁ V₂ n hfl
  obtain ⟨_, hnat⟩ := hfl.nat
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hfl.elem.2 w w.2)
  have hn := hfl.two_le
  have hLV := hfl.le_normalizer
  have hV₁ : V₁ ≤ V := hfl.le₁₂.trans hfl.le₂
  have hV₂ := hfl.le₂
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hfl.sylow le_sup_left (sup_le Subgroup.le_normalizer hfl.T_le_L)
  have hP := SecA.isSylowTwoOf_autOn hLV hTL'
  have hHZ : ∀ h ∈ autOn L V, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, h z = z :=
    fun h hh z hz => SecA.autOn_fixes_cV h hh z hz
  have hFW1 : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (2 ^ n) 1 (V₁.subgroupOf V) := by
    refine ⟨fun z hz => hfl.cV_le ⟨z.2, hz⟩, ?_, ?_, fun x hx => ?_⟩
    · have := (SecA.isEndStable_iff hLV _ V₁).mp hfl.stable₁
      rwa [SecA.inf_centralizer_subgroupOf] at this
    · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hV₁, hfl.index₁,
        pow_one]
    · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact (SecA.conjV_mem_stabW_iff hV₁ hyV).mpr (hfl.T_le_V₁ hy.1)
  have hFW2 : SecA.IsFlagW (autOn L V) (autOn (T ⊓ L) V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) (2 ^ n) 2 (V₂.subgroupOf V) := by
    refine ⟨fun z hz => hfl.le₁₂ (hfl.cV_le ⟨z.2, hz⟩), ?_, ?_, fun x hx => ?_⟩
    · have := (SecA.isEndStable_iff hLV _ V₂).mp hfl.stable₂
      rwa [SecA.inf_centralizer_subgroupOf] at this
    · rw [← SecA.inf_centralizer_subgroupOf, Subgroup.relIndex_subgroupOf hV₂, hfl.index₂,
        pow_mul]
    · obtain ⟨y, hy, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hx
      exact (SecA.conjV_mem_stabW_iff hV₂ hyV).mpr (hfl.T_le_V₂ hy.1)
  rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
  · have hlf := KGNat.factLineSL3_holds K n hn hK _ hsq _ _ π hπ hHZ _ hP _ hFW2
    exact BK2.l2Point_of hfl (fun u hu h => (hlf.2.2.1 u hu).mp h)
      fun Q hQ Y hZY hYU hYi hQY => BK2.l2Point_SL3 hn hK hsq hπ hP hFW1 hFW2 hQ hZY hYU hYi hQY
  · have hlf := (KGNat.factLineSp4_holds K n hn hK _ hsq _ _ π hπ hHZ _ hP _ hFW2).1
    exact BK2.l2Point_of hfl (fun u hu h => (hlf.2.2.1 u hu).mp h)
      fun Q hQ Y hZY hYU hYi hQY => BK2.l2Point_Sp4 hn hK hsq hπ hP hFW1 hFW2 hQ hZY hYU hYi hQY
  · exfalso
    have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
    obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
    obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
    have hinj : Function.Injective π := by
      intro x y hxy
      have h1 : G2Q8.rhoG hc0 hc1 π
          ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm).symm x) =
          G2Q8.rhoG hc0 hc1 π
            ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm).symm y) := by
        change π ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm)
            ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm).symm x)) =
          π ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm)
            ((MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm).symm y))
        exact (congrArg π (MulEquiv.apply_symm_apply _ x)).trans
          (hxy.trans (congrArg π (MulEquiv.apply_symm_apply _ y)).symm)
      exact (MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm).symm.injective
        ((G2Q8.rhoG_bijective hf hc0 hc1).1 h1)
    have hG2 : KindG2 L V n :=
      ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩
    rcases hfl.kind with hk | hk
    · exact SecA.kind_not_SL3_G2 KGNat.factG2DerivedOrder_holds hn hk hG2
    · exact SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn hk hG2

end CFSG.Quasithin.Vol2.Ch11.SecB
