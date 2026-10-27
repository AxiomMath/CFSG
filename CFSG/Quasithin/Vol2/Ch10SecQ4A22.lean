module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A21
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Vol2.Ch10SecQ4A20
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {J X : Subgroup G}

theorem a318_alt7 (h318 : A318Facts) (h36' : A36ForSQTK) (h38 : Vol2Native.A38ForSQTKCat)
    (hA7 : Ch11.SecA.FactA7Cent) (hXs : CFSG.SectionRank.IsSQTKCat ↥X) (hJ : J ∈ cComp X)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hcase : IsAlt 7 (↥J ⧸ CFSG.pCore 2 ↥J) ∨
      IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7))) :
    J.subgroupOf X = oPrimeResidualOf 3 ⊤ ∨
      (IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)) ∧
        J.subgroupOf X = thetaOf ⊤) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJX := le_of_mem_cComp hJ
  have hS : SQTKGroup ↥X := ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp hXs.1, hXs.2⟩
  have hSQ := SQTKHyp.of_sqtkGroup _ hS
  have hJc := subgroupOf_mem_cComp hJ
  obtain ⟨e₀⟩ := Ch11.SecA.quotPCore_subgroupOf_equiv (L := J) hJX
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hrankY : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) := by
    rcases hcase with he | hhat
    · obtain ⟨e⟩ : Nonempty _ := he
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
      exact C1GN.two_le_pRank_alt7
    · exact two_le_pRank_hat7 hhat
  have hrank : 1 < CFSG.Open.pRank 3 (J.subgroupOf X) := by
    rw [Ch11.SecA.pRank_subgroupOf_eq hJX Nat.prime_three (by norm_num)]
    omega
  have hconc := a318 h318 hS (h36' _ hSQ) (a38ForSQTK_of_cat h38 _ hSQ) hJc hQ' Nat.prime_three
    (by norm_num) hrank
  have hcen : Nat.card (Subgroup.center (↥(J.subgroupOf X) ⧸ CFSG.pCore 2 ↥(J.subgroupOf X))) =
      Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) := by
    rw [← Subgroup.map_center_eq e₀, Subgroup.card_map_of_injective e₀.injective]
  have hZ3 : Nat.card (Subgroup.center (↥(J.subgroupOf X) ⧸
      CFSG.pCore 2 ↥(J.subgroupOf X))) ∣ 3 := by
    rw [hcen]
    rcases hcase with he | hhat
    · obtain ⟨e⟩ : Nonempty _ := he
      rw [← Subgroup.map_center_eq e.symm, Subgroup.card_map_of_injective e.symm.injective,
        center_alt7', Subgroup.card_bot]
      exact one_dvd 3
    · rw [hhat.2.1]
  have h3 : 3 ∣ Nat.card (↥(J.subgroupOf X) ⧸ CFSG.pCore 2 ↥(J.subgroupOf X)) := by
    rw [Nat.card_congr e₀.toEquiv]
    rcases hcase with he | hhat
    · obtain ⟨e⟩ : Nonempty _ := he
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · rw [← hhat.2.1]
      exact Subgroup.card_subgroup_dvd_card _
  have hO := comap_pPrimeCore_eq (subnormal_of_mem_cComp hJc) hQ' hZ3 h3
  obtain ⟨φ⟩ := starImage_equiv' hO
  set ψ := φ.trans e₀ with hψ
  have hcase' : IsAlt 7 ↥(starImage 3 (J.subgroupOf X)) ∨
      IsHat ↥(starImage 3 (J.subgroupOf X)) ↥(alternatingGroup (Fin 7)) := by
    rcases hcase with he | hhat
    · obtain ⟨e⟩ : Nonempty _ := he
      exact Or.inl ⟨ψ.trans e⟩
    · exact Or.inr (IsHat.of_mulEquiv ψ.symm hhat)
  have hA7c := hA7 _ hcase'
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, h3a, h3b⟩
  · exact Or.inl h1
  · exfalso
    obtain ⟨s, q, -, ⟨p, e, -, -, rfl, hPSL⟩, -⟩ := h2
    exact hA7c.2.2 s p e hPSL
  · rcases hcase with he | hhat
    · exfalso
      obtain ⟨e⟩ : Nonempty _ := he
      have hc1 : Nat.card (Subgroup.center ↥(starImage 3 (J.subgroupOf X))) = 1 := by
        rw [← Subgroup.map_center_eq (ψ.trans e).symm,
          Subgroup.card_map_of_injective (ψ.trans e).symm.injective, center_alt7',
          Subgroup.card_bot]
      rcases h3a with ⟨s, q, -, hSL⟩ | h6 | h7 | h22
      · exact hA7c.2.1 s q hSL
      · rw [h6.2.1] at hc1
        exact absurd hc1 (by norm_num)
      · rw [h7.2.1] at hc1
        exact absurd hc1 (by norm_num)
      · rw [h22.2.1] at hc1
        exact absurd hc1 (by norm_num)
    · rcases h3b with hθ | h3b
      · exact Or.inr ⟨hhat, hθ⟩
      · exfalso
        obtain ⟨s, q, x, hSL, -⟩ := h3b
        exact hA7c.2.1 s q hSL

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
