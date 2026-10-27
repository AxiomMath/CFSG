module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG

theorem exists_sylowOf_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Y : Subgroup G} (hP : IsPGroup p P) (hPY : P ≤ Y) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S Y ∧ P ≤ S := by
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hP.comap_subtype (K := Y))
  refine ⟨(S : Subgroup Y).map Y.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPY hx⟩, hS hx, rfl⟩

theorem exists_sylow_of_normalizer_le {G : Type*} [Group G] [Finite G] {P H : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H) (hN : Subgroup.normalizer (P : Set G) ≤ H) :
    ∃ S : Sylow 3 G, (S : Subgroup G) = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hP
  have hPH : P ≤ H := by
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hP3 : IsPGroup 3 P := by
    rw [← hQ]
    exact Q.isPGroup'.map H.subtype
  have hmaxH : ∀ R : Subgroup G, IsPGroup 3 R → P ≤ R → R ≤ H → R = P := by
    intro R hR hPR hRH
    have hR' : IsPGroup 3 (R.subgroupOf H) :=
      hR.comap_of_injective H.subtype H.subtype_injective
    have hle : (Q : Subgroup H) ≤ R.subgroupOf H := by
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      exact hPR (hQ ▸ Subgroup.mem_map_of_mem H.subtype hq)
    have heq := Q.is_maximal' hR' hle
    apply le_antisymm _ hPR
    intro r hr
    have hr' : (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hr
    rw [heq] at hr'
    rw [← hQ]
    exact Subgroup.mem_map.mpr ⟨_, hr', rfl⟩
  refine ⟨⟨P, hP3, fun {R} hR hPR => ?_⟩, rfl⟩
  by_contra hne
  have : Finite R := inferInstance
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hcond := Group.normalizerCondition_of_isNilpotent (G := R)
  have hPR' : P.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm _ hPR
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ P.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt (hcond _ hPR')
  have hyN' : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN ⟨p, hPR hp⟩).mp
        (Subgroup.mem_subgroupOf.mpr hp)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hp
      have hpR : p ∈ R := by
        have e1 : p = (y : G)⁻¹ * ((y : G) * p * (y : G)⁻¹) * (y : G) := by group
        rw [e1]
        exact R.mul_mem (R.mul_mem (R.inv_mem y.2) (hPR hp)) y.2
      have hmem : (y * ⟨p, hpR⟩ * y⁻¹ : R) ∈ P.subgroupOf R :=
        Subgroup.mem_subgroupOf.mpr hp
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN ⟨p, hpR⟩).mpr hmem)
  have hyH : (y : G) ∈ H := hN hyN'
  have hS3 : IsPGroup 3 (P ⊔ Subgroup.zpowers (y : G) : Subgroup G) := by
    refine hR.to_le (sup_le hPR ?_)
    rw [Subgroup.zpowers_le]
    exact y.2
  have hSH : P ⊔ Subgroup.zpowers (y : G) ≤ H :=
    sup_le hPH (Subgroup.zpowers_le.mpr hyH)
  have hSeq := hmaxH _ hS3 le_sup_left hSH
  apply hyP
  rw [Subgroup.mem_subgroupOf]
  rw [← hSeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem card_mulAut_of_alt7 {X : Type*} [Group X]
    (e : Nonempty (X ≃* alternatingGroup (Fin 7))) : Nat.card (MulAut X) = 5040 := by
  obtain ⟨e⟩ := e
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  have h1 : Nat.card (Equiv.Perm (Fin 7)) = Nat.card (MulAut (alternatingGroup (Fin 7))) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_congr (MulAut.congr e).toEquiv, ← h1, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  rfl

end CFSG.RankThree.PartTwo.Sec13.F135Last
