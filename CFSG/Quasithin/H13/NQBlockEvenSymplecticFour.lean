module

public import CFSG.Quasithin.H13.NQBlockWitnessSingleton
public import CFSG.Quasithin.H13.NQRigidB56
public import CFSG.Quasithin.H13.NQRigidAsmTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

theorem originalWitnessExcludesEvenSymplecticFour_holds
    : OriginalWitnessExcludesEvenSymplecticFour := by
  intro G _ _ T L M h p hp hp5 X hXL hXc hXA hW hLW Y K hXTY hKY hKn hXK hKq hZ f hf hmodel
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hTL : T ≤ normalizer (L : Set G) := h.t_le.trans h.eq_normalizer.le
  have hLX : normalizer (L : Set G) ≤ normalizer (X : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (X.subgroupOf L)
    rwa [map_subgroupOf_eq_of_le hXL] at h1
  have hTX : T ≤ normalizer (X : Set G) := hTL.trans hLX
  have hLN : L ≤ normalizer (X : Set G) := le_normalizer.trans hLX
  have hXY : X ≤ Y := le_sup_left.trans hXTY
  have hTY : T ≤ Y := le_sup_right.trans hXTY
  have hcyc :
      IsCyclic ((T.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X)) := by
    have hTs : IsSylowTwoOf T Y := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTY
    have hTY2 : IsPGroup 2 (T.subgroupOf Y) := hTs.2.1.of_equiv (subgroupOfEquivOfLe hTY).symm
    have hTYi : ¬ 2 ∣ (T.subgroupOf Y).index := hTs.2.2
    set Q : Sylow 2 ↥Y := hTY2.toSylow hTYi with hQdef
    have hQ : (Q : Subgroup ↥Y) = T.subgroupOf Y := IsPGroup.toSylow_coe hTY2 hTYi
    have hQD : (Q : Subgroup ↥Y) ≤ (X ⊔ T).subgroupOf Y := by
      rw [hQ]
      exact fun x hx => mem_subgroupOf.mpr ((le_sup_right : T ≤ X ⊔ T) (mem_subgroupOf.mp hx))
    have : (K.subgroupOf Y).Normal := hKn
    have hX'D : X.subgroupOf Y ≤ (X ⊔ T).subgroupOf Y :=
      fun x hx => mem_subgroupOf.mpr ((le_sup_left : X ≤ X ⊔ T) (mem_subgroupOf.mp hx))
    have hX'Dn : ((X.subgroupOf Y).subgroupOf ((X ⊔ T).subgroupOf Y)).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer hX'D]
      intro d hd
      have hdN : (d : G) ∈ normalizer (X : Set G) :=
        (sup_le le_normalizer hTX) (mem_subgroupOf.mp hd)
      have h1 := NQRigid.mem_normalizer_subgroupOf_of d.2 hdN
      exact h1
    have hX'K : X.subgroupOf Y ≤ K.subgroupOf Y :=
      fun x hx => mem_subgroupOf.mpr (hXK (mem_subgroupOf.mp hx))
    have hX'A : IsPGroup p (X.subgroupOf Y ⧸ CFSG.pCore 2 (X.subgroupOf Y)) :=
      NQRigid.isPGroup_coreQuot_subgroupOf hXY hXA
    let eK : ↥(K.subgroupOf Y) ≃* ↥K := subgroupOfEquivOfLe hKY
    let eQ : ↥(K.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(K.subgroupOf Y) ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
      QuotientGroup.congr _ _ eK (CFSG.pCore_map_iso 2 eK)
    let eZ := QuotientGroup.congr _ _ eQ (Subgroup.map_center_eq eQ)
    have hZ' : ¬ p ∣ Nat.card (center (↥(K.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(K.subgroupOf Y))) := by
      have hc : Nat.card (center (↥(K.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(K.subgroupOf Y))) =
          Nat.card (center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        rw [← Subgroup.map_center_eq eQ]
        exact (card_map_of_injective (f := eQ.toMonoidHom) eQ.injective).symm
      rw [hc]
      exact hZ
    have hmodel' := CFSG.SectionRank.statedClassicalModel_of_mulEquiv eZ hmodel
    by_contra hnc'
    have hnc : ¬ IsCyclic ((((Q : Subgroup ↥Y)).subgroupOf
        (normalizer ((X.subgroupOf Y : Subgroup ↥Y) : Set ↥Y))).map
        (normalizerFrattiniConj (X.subgroupOf Y))) := by
      rw [hQ]
      intro hc
      exact hnc' ((NQRigid.isCyclic_congr (NQRigid.imageEquivSubgroupOf hXY hTY hTX)).mp hc)
    exact (NQRigid.stmtNoncyclicLocalSylowFourEven_holds ↥Y p hp hp5 ((X ⊔ T).subgroupOf Y) Q
      hQD (K.subgroupOf Y) (X.subgroupOf Y) hX'D hX'Dn hX'K hX'A hnc hZ').1 f hf hmodel'
  set ψ : ↥L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (Subgroup.inclusion hLN) with hψ
  have : Finite (MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) :=
    Finite.of_injective (fun α : MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =>
      (α : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) →
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) DFunLike.coe_injective
  have hLC : L ∈ cComp (L ⊔ T) := h.maximal_local.1.2.1
  have hLperf : Group.IsPerfect ↥L := by
    refine ⟨?_⟩
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subtype_commutator, perfect_of_mem_cComp hLC, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hIperf : Group.IsPerfect ↥ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hInt : Nontrivial ↥ψ.range := by
    obtain ⟨l, hlL, hl1⟩ := hLW
    refine ⟨⟨⟨ψ ⟨l, hlL⟩, ⟨_, rfl⟩⟩, 1, fun h1 => hl1 ?_⟩⟩
    have h2 : ψ ⟨l, hlL⟩ = 1 := congrArg Subtype.val h1
    have h3 : Subgroup.inclusion hLN ⟨(l : G), hlL⟩ = l := Subtype.ext rfl
    rw [hψ, MonoidHom.comp_apply, h3] at h2
    exact h2
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp hLC)
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
  have hTL2 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTLs.2.1.of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  set SL : Sylow 2 ↥L := hTL2.toSylow hTLs.2.2 with hSLdef
  have hSL : (SL : Subgroup ↥L) = (T ⊓ L).subgroupOf L := IsPGroup.toSylow_coe hTL2 hTLs.2.2
  set SI : Sylow 2 ↥ψ.range := SL.mapSurjective ψ.rangeRestrict_surjective with hSIdef
  have hmem : ∀ s : (SI : Subgroup ↥ψ.range),
      ((s : ↥ψ.range) : MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))) ∈
        (T.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X) := by
    rintro ⟨s, hs⟩
    rw [hSIdef, Sylow.coe_mapSurjective, hSL] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    have hxT : (x : G) ∈ T := (mem_inf.mp (mem_subgroupOf.mp hx)).1
    exact ⟨Subgroup.inclusion hLN x, mem_subgroupOf.mpr hxT, rfl⟩
  let φ : (SI : Subgroup ↥ψ.range) →*
      ↥((T.subgroupOf (normalizer (X : Set G))).map (normalizerFrattiniConj X)) :=
    (ψ.range.subtype.comp (SI : Subgroup ↥ψ.range).subtype).codRestrict _ hmem
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hcycS : IsCyclic (SI : Subgroup ↥ψ.range) := isCyclic_of_injective φ hφ
  by_cases hev : Even (Nat.card ↥ψ.range)
  · exact CFSG.LocalAnalysis.ComponentInitial.perfect_even_sylow_noncyclic hev SI hcycS
  · exact Group.IsPerfect.not_isSolvable ↥ψ.range
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hev))

end CFSG.Quasithin.H13.NQBlock
