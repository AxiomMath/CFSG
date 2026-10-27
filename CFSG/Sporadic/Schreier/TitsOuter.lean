module

public import CFSG.Sporadic.Schreier.TitsPair
public import CFSG.Sporadic.Schreier.TitsAbel
public import CFSG.LieType.Ree.TitsSylowLocalSchreier
public import CFSG.LieType.Ree.TitsAbelianizationAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.LieType.Ree CFSG.ComponentClassification.OuterAutomorphisms

section Transport

variable {G : Type*} [Group G] {D : Subgroup G}

theorem subgroupOf_centralizer_map (Y : Subgroup D) :
    (Subgroup.centralizer ((Y.map D.subtype : Subgroup G) : Set G)).subgroupOf D =
      Subgroup.centralizer (Y : Set D) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact Subtype.ext (h y ⟨y, hy, rfl⟩)
  · rintro h _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (h y hy)

theorem centralizer_subgroupOf_eq {X : Subgroup G} (hX : X ≤ D) :
    (Subgroup.centralizer (X : Set G)).subgroupOf D =
      Subgroup.centralizer ((X.subgroupOf D : Subgroup D) : Set D) := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact Subtype.ext (h x hx)
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hX hx⟩ hx)

theorem map_center_map_subtype (Q : Subgroup D) :
    ((Subgroup.center Q).map Q.subtype).map D.subtype =
      (Subgroup.center (Q.map D.subtype)).map (Q.map D.subtype).subtype := by
  set e := Q.equivMapOfInjective D.subtype D.subtype_injective
  rw [← center_map_equiv e, Subgroup.map_map, Subgroup.map_map]
  rfl

end Transport

theorem titsSubD_le {X Y : Subgroup (Equiv.Perm (Fin 1755))} (h : X ≤ Y) :
    X.subgroupOf titsD ≤ Y.subgroupOf titsD :=
  fun _ hg => h hg

theorem AT_Tits_derived_group_Schreier :
    IsPGroup 2 (Outer titsD) ∧ Group.IsSolvable (Outer titsD) := by
  obtain ⟨⟨P, hP⟩, hH, hN, hHN, hJ2, -, hJn, -, hJS, hKS, hCJ, hCK⟩ :=
    AT_Tits_intrinsic_local_pair
  have hZ : ((Subgroup.center (P : Subgroup titsD)).map (P : Subgroup titsD).subtype).map
      titsD.subtype = (Subgroup.center titsS).map titsS.subtype := by
    rw [map_center_map_subtype, hP, subgroupOf_map_titsD titsS_le_titsD]
  have hH' : titsH.subgroupOf titsD = Subgroup.centralizer
      (((Subgroup.center (P : Subgroup titsD)).map (P : Subgroup titsD).subtype :
        Subgroup titsD) : Set titsD) := by
    rw [← subgroupOf_centralizer_map, hZ, hH, Subgroup.inf_subgroupOf_left]
  have hN' : titsN.subgroupOf titsD =
      Subgroup.normalizer ((titsK.subgroupOf titsD : Subgroup titsD) : Set titsD) := by
    rw [hN, Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq titsK_le_titsD]
  have hKS' : titsK.subgroupOf titsD ≤ P := hP ▸ titsSubD_le hKS
  have hJS' : titsJ.subgroupOf titsD ≤ P := hP ▸ titsSubD_le hJS
  have hJH' : titsJ.subgroupOf titsD ≤ titsH.subgroupOf titsD := titsSubD_le titsJ_le_titsH
  have hJp : IsPGroup 2 (titsJ.subgroupOf titsD) :=
    hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe titsJ_le_titsD).symm
  have hJn' : ((titsJ.subgroupOf titsD).subgroupOf (titsH.subgroupOf titsD)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJH', ← Subgroup.subgroupOf_normalizer_eq
      titsJ_le_titsD]
    exact titsSubD_le ((Subgroup.normal_subgroupOf_iff_le_normalizer titsJ_le_titsH).1 hJn)
  have hCJ' : titsH.subgroupOf titsD ⊓
      Subgroup.centralizer ((titsJ.subgroupOf titsD : Subgroup titsD) : Set titsD) ≤
        titsJ.subgroupOf titsD := by
    rw [← centralizer_subgroupOf_eq titsJ_le_titsD]
    exact fun g hg => hCJ ⟨hg.1, hg.2⟩
  have hCK' : titsN.subgroupOf titsD ⊓
      Subgroup.centralizer ((titsK.subgroupOf titsD : Subgroup titsD) : Set titsD) ≤
        titsK.subgroupOf titsD := by
    rw [← centralizer_subgroupOf_eq titsK_le_titsD]
    exact fun g hg => hCK ⟨hg.1, hg.2⟩
  have hgen : titsH.subgroupOf titsD ⊔ titsN.subgroupOf titsD = ⊤ := by
    apply Subgroup.map_injective titsD.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_titsD titsH_le_titsD, subgroupOf_map_titsD titsN_le_titsD,
      hHN, map_top_titsD]
  obtain ⟨-, -, hsolv, hpgrp⟩ := tits_Sylow_local_Schreier_criterion P _ hH' _ hKS' _ hN' _ hJp
    hJS' hJH' hJn' hCJ' hCK' hgen
  have hS2 : IsPGroup 2 (P : Subgroup titsD) := P.isPGroup'
  have e : Abelianization (P : Subgroup titsD) ≃*
      Multiplicative (ZMod (2 ^ 2)) × Multiplicative (ZMod 2) :=
    (((MulEquiv.subgroupCongr hP).trans
      (Subgroup.subgroupOfEquivOfLe titsS_le_titsD)).abelianizationCongr).trans
      titsAbelianizationEquiv
  obtain ⟨-, haut, haut2⟩ := tits_unequal_cyclic_abelianization_automorphisms hS2 e
  exact ⟨hpgrp (haut2 rfl), hsolv haut⟩

theorem titsModelEquiv
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel G .Tits p f) : Nonempty (G ≃* titsD) := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have : Fact (Nat.card K = 2) := ⟨hK2⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  exact ⟨e'.trans (((QuotientGroup.quotientMulEquivOfEq (center_commutator_reeFixed hK2)).trans
    QuotientGroup.quotientBot).trans titsDerivedIso)⟩

theorem AT_Tits_model_Schreier
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel G .Tits p f) :
    IsPGroup 2 (Outer G) ∧ Group.IsSolvable (Outer G) := by
  obtain ⟨e⟩ := titsModelEquiv G p f h
  obtain ⟨h2, hs⟩ := AT_Tits_derived_group_Schreier
  exact ⟨h2.of_equiv (equivalence e).symm, solvable_of_equiv e.symm⟩

end CFSG.Sporadic.Schreier.Tits
