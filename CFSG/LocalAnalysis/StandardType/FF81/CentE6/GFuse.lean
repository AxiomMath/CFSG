module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.RadSetting
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatD
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups Pointwise
open CFSG.RankThree.GF2n.Smith81

theorem exists_conj_eq_of_isConj_mem_sup {G : Type} [Group G] [Finite G] {t : G}
    {Q L : Subgroup G} {eL : ↥L ≃* SL(6, ZMod 2)}
    {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadSetting t Q L eL π b) {x : G} (hx : x ∈ Q ⊔ L) (hconj : IsConj b x) :
    ∃ h ∈ Q ⊔ L, h * x * h⁻¹ = b := by
  have hb3 : orderOf b = 3 := by
    have h := MulEquiv.orderOf_eq eL (⟨b, R.b_mem⟩ : ↥L)
    rw [R.b_mark, orderOf_bStd] at h
    simpa using h.symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hsc : SemiconjBy c b x := by
    rw [SemiconjBy, ← hc, mul_assoc, inv_mul_cancel, mul_one]
  have hx3 : orderOf x = 3 := (SemiconjBy.orderOf_eq c hsc).symm.trans hb3
  let X : Subgroup G := Subgroup.zpowers x
  let P : Subgroup G := Q ⊔ X
  have hxX : x ∈ X := Subgroup.mem_zpowers x
  have hxP : x ∈ P := Subgroup.mem_sup_right hxX
  have hXleP : X ≤ P := le_sup_right
  have hXleM : X ≤ Q ⊔ L := Subgroup.zpowers_le.mpr hx
  have hPleM : P ≤ Q ⊔ L := sup_le le_sup_left hXleM
  have hxcard : Nat.card X = 3 := by
    rw [show Nat.card X = Nat.card (Subgroup.zpowers x) from rfl, Nat.card_zpowers, hx3]
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hxcard)
  have hinfQX : Q ⊓ X = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) Q X R.isPGroup hXp)
  have hQleN : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hLleN : L ≤ Subgroup.normalizer (Q : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact R.conj_mem l hl q
    · intro hq
      have hinv := R.conj_mem l⁻¹ (L.inv_mem hl) (l * q * l⁻¹) hq
      have hqeq : l⁻¹ * (l * q * l⁻¹) * (l⁻¹)⁻¹ = q := by group
      rwa [hqeq] at hinv
  have hPleN : P ≤ Subgroup.normalizer (Q : Set G) :=
    hPleM.trans (sup_le hQleN hLleN)
  have hQnormal : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hPleN
  have hQXsup : Q.subgroupOf P ⊔ X.subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left hXleP]
    exact Subgroup.subgroupOf_self P
  have hQXdisj : Disjoint (Q.subgroupOf P) (X.subgroupOf P) := by
    rw [disjoint_iff]
    ext g
    constructor
    · intro hg
      have hq : (g : G) ∈ Q := hg.1
      have hxx : (g : G) ∈ X := hg.2
      have hbot : (g : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinfQX]
        exact ⟨hq, hxx⟩
      simpa using hbot
    · intro hg
      rw [Subgroup.mem_bot] at hg
      subst hg
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hQXcomp : (Q.subgroupOf P).IsComplement' (X.subgroupOf P) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hQXdisj ?_
    rw [← Subgroup.normal_mul (Q.subgroupOf P) (X.subgroupOf P), hQXsup]
    simp
  have hQcardP : Nat.card (Q.subgroupOf P) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Q) (K := P) le_sup_left)
  have hXcardP : Nat.card (X.subgroupOf P) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := X) (K := P) hXleP)
  have hPcard : Nat.card P = Nat.card Q * 3 := by
    rw [← hQXcomp.card_mul_card, hQcardP, hXcardP, hxcard, Nat.mul_comm]
  have hxQL : x ∈ (Q : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLleN]
    exact hx
  rw [Set.mem_mul] at hxQL
  obtain ⟨q, hq, l, hl, hql⟩ := hxQL
  have hqQ : q ∈ Q := by simpa using hq
  have hlL : l ∈ L := by simpa using hl
  have hyl : q⁻¹ * x ∈ P ⊓ L := by
    refine ⟨?_, ?_⟩
    · exact P.mul_mem (P.inv_mem (Subgroup.mem_sup_left hqQ)) hxP
    · rw [← hql]
      have hqxl : q⁻¹ * (q * l) = l := by group
      rw [hqxl]
      exact hlL
  have hxdecomp : x ∈ Q ⊔ (P ⊓ L) := by
    have h := Subgroup.mul_mem_sup hqQ hyl
    rwa [show q * (q⁻¹ * x) = x by group] at h
  have hsupQY : Q ⊔ (P ⊓ L) = P := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) ?_
    calc P = Q ⊔ X := rfl
      _ ≤ Q ⊔ (P ⊓ L) := sup_le le_sup_left (Subgroup.zpowers_le.mpr hxdecomp)
  have hYleP : P ⊓ L ≤ P := inf_le_left
  have hQYsup : Q.subgroupOf P ⊔ (P ⊓ L).subgroupOf P = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left hYleP, hsupQY]
    exact Subgroup.subgroupOf_self P
  have hQYdisj : Disjoint (Q.subgroupOf P) ((P ⊓ L).subgroupOf P) := by
    rw [disjoint_iff]
    ext g
    constructor
    · intro hg
      have hq : (g : G) ∈ Q := hg.1
      have hl' : (g : G) ∈ L := hg.2.2
      have hbot : (g : G) ∈ (⊥ : Subgroup G) := by
        rw [← R.inf_eq_bot]
        exact ⟨hl', hq⟩
      simpa using hbot
    · intro hg
      rw [Subgroup.mem_bot] at hg
      subst hg
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hQYcomp : (Q.subgroupOf P).IsComplement' ((P ⊓ L).subgroupOf P) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hQYdisj ?_
    rw [← Subgroup.normal_mul (Q.subgroupOf P) ((P ⊓ L).subgroupOf P), hQYsup]
    simp
  have hYcardP : Nat.card ((P ⊓ L).subgroupOf P) = Nat.card (P ⊓ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := P ⊓ L) (K := P) hYleP)
  have hYcard : Nat.card (P ⊓ L : Subgroup G) = 3 := by
    have h := hQYcomp.card_mul_card
    rw [hQcardP, hYcardP, hPcard] at h
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥Q)) h
  have hYp : IsPGroup 3 (P ⊓ L : Subgroup G) := IsPGroup.of_card (n := 1) (by simpa using hYcard)
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp R.isPGroup
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h) (by norm_num)
  have hXindex : ¬ 3 ∣ (X.subgroupOf P).index := by
    rw [hQXcomp.index_eq_card, hQcardP]
    exact h3Q
  have hYindex : ¬ 3 ∣ ((P ⊓ L).subgroupOf P).index := by
    rw [hQYcomp.index_eq_card, hQcardP]
    exact h3Q
  have hXpP : IsPGroup 3 (X.subgroupOf P) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXleP).symm
  have hYpP : IsPGroup 3 ((P ⊓ L).subgroupOf P) :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYleP).symm
  let SX : Sylow 3 P := hXpP.toSylow hXindex
  let SY : Sylow 3 P := hYpP.toSylow hYindex
  have : Finite (Sylow 3 P) := Sylow.finite_of_finiteIndex SX
  obtain ⟨kp, hkp⟩ := MulAction.exists_smul_eq P SX SY
  let xp : P := ⟨x, hxP⟩
  have hxpX : xp ∈ X.subgroupOf P := hxX
  have hkp_mem : MulAut.conj kp xp ∈ (kp • SX : Sylow 3 P) := by
    change MulAut.conj kp xp ∈ (↑(kp • SX) : Subgroup P)
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul xp (MulAut.conj kp) (X.subgroupOf P) hxpX
  have hkp_memY : MulAut.conj kp xp ∈ ((P ⊓ L).subgroupOf P) := by
    have h := hkp_mem
    rw [hkp] at h
    simpa only [SY, IsPGroup.mem_toSylow] using h
  have hy_mem : (kp : G) * x * (kp : G)⁻¹ ∈ P ⊓ L := by
    have h := hkp_memY
    rw [Subgroup.mem_subgroupOf] at h
    simpa [MulAut.conj_apply] using h
  have hyL : (kp : G) * x * (kp : G)⁻¹ ∈ L := hy_mem.2
  have hyconj : IsConj b ((kp : G) * x * (kp : G)⁻¹) :=
    hconj.trans (isConj_iff.mpr ⟨(kp : G), rfl⟩)
  obtain ⟨l, hlL, hl_eq⟩ :=
    R.fuse b ((kp : G) * x * (kp : G)⁻¹) R.b_mem hyL (IsConj.refl b) hyconj
  have hkM : (kp : G) ∈ Q ⊔ L := hPleM kp.2
  have hl_inv_M : l⁻¹ ∈ Q ⊔ L := Subgroup.mem_sup_right (L.inv_mem hlL)
  refine ⟨l⁻¹ * (kp : G), Subgroup.mul_mem (Q ⊔ L) hl_inv_M hkM, ?_⟩
  calc
    (l⁻¹ * (kp : G)) * x * (l⁻¹ * (kp : G))⁻¹
        = l⁻¹ * ((kp : G) * x * (kp : G)⁻¹) * l := by group
    _ = l⁻¹ * (l * b * l⁻¹) * l := by rw [hl_eq]
    _ = b := by group

end CFSG.StandardType.FF81.CentE6
