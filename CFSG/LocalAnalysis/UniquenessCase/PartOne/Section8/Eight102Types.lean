module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem barImage_map_conj {L B : Subgroup G} (hBL : B ≤ L) (l : ↥L) :
    barImage L (B.map (MulAut.conj (l : G)).toMonoidHom) =
      (barImage L B).map (MulAut.conj (uc22p21cPi L l)).toMonoidHom := by
  have hsub : (B.map (MulAut.conj (l : G)).toMonoidHom).subgroupOf L =
      (B.subgroupOf L).map (MulAut.conj l) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
      obtain ⟨b, hb, hbl⟩ := hx
      exact Subgroup.mem_map.2 ⟨⟨b, hBL hb⟩, hb, by ext; simpa [MulAut.conj_apply] using hbl⟩
    · intro hx
      obtain ⟨b, hb, hbl⟩ := Subgroup.mem_map.1 hx
      refine Subgroup.mem_subgroupOf.2
        (Subgroup.mem_map.2 ⟨(b : G), Subgroup.mem_subgroupOf.1 hb, ?_⟩)
      have hval := congrArg Subtype.val hbl
      simpa [MulAut.conj_apply] using hval
  have hpi : (uc22p21cPi L).comp (MulAut.conj l).toMonoidHom =
      (MulAut.conj (uc22p21cPi L l)).toMonoidHom.comp (uc22p21cPi L) := by
    ext x
    simp [MulAut.conj_apply]
  calc barImage L (B.map (MulAut.conj (l : G)).toMonoidHom)
      = ((B.map (MulAut.conj (l : G)).toMonoidHom).subgroupOf L).map (uc22p21cPi L) := rfl
    _ = ((B.subgroupOf L).map (MulAut.conj l)).map (uc22p21cPi L) := by rw [hsub]
    _ = (B.subgroupOf L).map ((uc22p21cPi L).comp (MulAut.conj l).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (B.subgroupOf L).map
          ((MulAut.conj (uc22p21cPi L l)).toMonoidHom.comp (uc22p21cPi L)) := by rw [hpi]
    _ = ((B.subgroupOf L).map (uc22p21cPi L)).map
          (MulAut.conj (uc22p21cPi L l)).toMonoidHom := (Subgroup.map_map _ _ _).symm
    _ = (barImage L B).map (MulAut.conj (uc22p21cPi L l)).toMonoidHom := rfl

private theorem card_sup_pCoreOf_of_card_three {L X : Subgroup G} (hXL : X ≤ L)
    (hX3 : IsPGroup 3 X) (hXc : Nat.card X = 3) :
    Nat.card ↥(X ⊔ pCoreOf 2 L) = 3 * Nat.card (pCoreOf 2 L) := by
  have hdisj : Disjoint (pCoreOf 2 L) X :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) (pCoreOf 2 L) X
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype) hX3
  rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (pCoreOf 2 L) X (hXL.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L)) hdisj,
      hXc, Nat.mul_comm]

private theorem le_sup_pCoreOf_of_barImage_eq {L X Y : Subgroup G} (hXL : X ≤ L) (hYL : Y ≤ L)
    (hbar : barImage L X = barImage L Y) : Y ≤ X ⊔ pCoreOf 2 L := by
  intro y hy
  have hybar : uc22p21cPi L ⟨y, hYL hy⟩ ∈ barImage L Y :=
    uc22p21c_mem_barImage.2 ⟨⟨y, hYL hy⟩, hy, rfl⟩
  rw [← hbar] at hybar
  obtain ⟨m, hm, hmy⟩ := uc22p21c_mem_barImage.1 hybar
  have hmem : m⁻¹ * ⟨y, hYL hy⟩ ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    show uc22p21cPi L (m⁻¹ * ⟨y, hYL hy⟩) = 1
    rw [map_mul, map_inv, hmy]
    simp
  have hmemN : (m : G)⁻¹ * y ∈ pCoreOf 2 L :=
    Subgroup.mem_map.2 ⟨m⁻¹ * ⟨y, hYL hy⟩, hmem, by simp⟩
  rw [show y = (m : G) * ((m : G)⁻¹ * y) from by group]
  exact Subgroup.mul_mem_sup hm hmemN

private theorem not_dvd_index_subgroupOf_of_card_three {L X H : Subgroup G} (hXH : X ≤ H)
    (hXc : Nat.card X = 3) (hHcard : Nat.card ↥H = 3 * Nat.card (pCoreOf 2 L)) :
    ¬ 3 ∣ (X.subgroupOf H).index := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro hdvd
  have hmul := Subgroup.card_mul_index (X.subgroupOf H)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc, hHcard] at hmul
  have hidx : (X.subgroupOf H).index = Nat.card (pCoreOf 2 L) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
  rw [hidx] at hdvd
  obtain ⟨k, hk⟩ := ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype).exists_card_eq
  rw [show pCoreOf 2 L = (pCore 2 ↥L).map L.subtype from rfl] at hdvd
  rw [hk] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)

private theorem exists_conj_of_barImage_eq_of_card_three {L X Y : Subgroup G}
    (hXL : X ≤ L) (hYL : Y ≤ L) (hX3 : IsPGroup 3 X) (hY3 : IsPGroup 3 Y)
    (hXc : Nat.card X = 3) (hYc : Nat.card Y = 3) (hbar : barImage L X = barImage L Y) :
    ∃ l ∈ L, Y = X.map (MulAut.conj l).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hNL : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hXH : X ≤ X ⊔ pCoreOf 2 L := le_sup_left
  have hYH : Y ≤ X ⊔ pCoreOf 2 L := le_sup_pCoreOf_of_barImage_eq hXL hYL hbar
  have hcardH := card_sup_pCoreOf_of_card_three hXL hX3 hXc
  have hXsub3 : IsPGroup 3 (X.subgroupOf (X ⊔ pCoreOf 2 L)) :=
    hX3.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  have hYsub3 : IsPGroup 3 (Y.subgroupOf (X ⊔ pCoreOf 2 L)) :=
    hY3.of_equiv (Subgroup.subgroupOfEquivOfLe hYH).symm
  have hXdvd := not_dvd_index_subgroupOf_of_card_three hXH hXc hcardH
  have hYdvd := not_dvd_index_subgroupOf_of_card_three hYH hYc hcardH
  let P : Sylow 3 ↥(X ⊔ pCoreOf 2 L) := hXsub3.toSylow hXdvd
  let Q : Sylow 3 ↥(X ⊔ pCoreOf 2 L) := hYsub3.toSylow hYdvd
  obtain ⟨h, hh⟩ := CFSG.BenderSuzuki.External.huppert_I_7_5_sylow_subgroups_conjugate P Q
  have hP : (P : Subgroup ↥(X ⊔ pCoreOf 2 L)) = X.subgroupOf (X ⊔ pCoreOf 2 L) :=
    IsPGroup.toSylow_coe hXsub3 hXdvd
  have hQ : (Q : Subgroup ↥(X ⊔ pCoreOf 2 L)) = Y.subgroupOf (X ⊔ pCoreOf 2 L) :=
    IsPGroup.toSylow_coe hYsub3 hYdvd
  have hcomp : (X ⊔ pCoreOf 2 L).subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (h : G)).toMonoidHom.comp (X ⊔ pCoreOf 2 L).subtype := by
    ext x
    rfl
  refine ⟨(h : G), sup_le hXL hNL h.2, ?_⟩
  calc Y = (Y.subgroupOf (X ⊔ pCoreOf 2 L)).map (X ⊔ pCoreOf 2 L).subtype := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYH]
    _ = ((X.subgroupOf (X ⊔ pCoreOf 2 L)).map (MulAut.conj h).toMonoidHom).map
          (X ⊔ pCoreOf 2 L).subtype := by rw [← hQ, hh, hP]
    _ = (X.subgroupOf (X ⊔ pCoreOf 2 L)).map
          ((X ⊔ pCoreOf 2 L).subtype.comp (MulAut.conj h).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (X.subgroupOf (X ⊔ pCoreOf 2 L)).map
          ((MulAut.conj (h : G)).toMonoidHom.comp (X ⊔ pCoreOf 2 L).subtype) := by rw [hcomp]
    _ = ((X.subgroupOf (X ⊔ pCoreOf 2 L)).map (X ⊔ pCoreOf 2 L).subtype).map
          (MulAut.conj (h : G)).toMonoidHom := (Subgroup.map_map _ _ _).symm
    _ = X.map (MulAut.conj (h : G)).toMonoidHom := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXH]

theorem exists_notationA8103 (hK5 : KU45Types) {L P : Subgroup G} {p n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) : ∃ A : Subgroup G, F08.NotationA8103 L P p n A := by
  have hPL : P ≤ L := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  obtain ⟨hS3, hSidx⟩ := isPGroup_barImage_of_isSylowOf (s := 3) (by norm_num) hP
  obtain ⟨A, hA⟩ := (hK5 (Bar2 L) n hX p hp hpn (barImage L P) hS3 hSidx).1
  obtain ⟨A₀, hA₀P, hA₀⟩ :=
    exists_barImage_eq hPL (s := 3) (by norm_num) (by norm_num) hP3 hA.2.1
  refine ⟨A₀, ?_⟩
  refine (notationA8103_barImage_iff hPL hP3 hp hp2 hA₀P).mp ?_
  rwa [hA₀]

theorem exists_notationB8103 (hK5 : KU45Types) {L P : Subgroup G} {p n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    ∃ B : Subgroup G, F08.NotationB8103 L P n B := by
  have hPL : P ≤ L := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  obtain ⟨hS3, hSidx⟩ := isPGroup_barImage_of_isSylowOf (s := 3) (by norm_num) hP
  obtain ⟨B, hB⟩ := (hK5 (Bar2 L) n hX p hp hpn (barImage L P) hS3 hSidx).2.1
  obtain ⟨B₀, hB₀P, hB₀⟩ :=
    exists_barImage_eq hPL (s := 3) (by norm_num) (by norm_num) hP3 hB.2.1
  refine ⟨B₀, ?_⟩
  refine (notationB8103_barImage_iff hPL hP3 hB₀P).mp ?_
  rwa [hB₀]

theorem notationA8103_or_notationB8103 (hK5 : KU45Types) {L P Y : Subgroup G} {p n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hYP : Y ≤ P) (hY : Nat.card Y = 3) :
    F08.NotationA8103 L P p n Y ∨ F08.NotationB8103 L P n Y := by
  have hPL : P ≤ L := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hY3 : IsPGroup 3 Y := hP3.to_le hYP
  obtain ⟨hS3, hSidx⟩ := isPGroup_barImage_of_isSylowOf (s := 3) (by norm_num) hP
  have hYbar_le : barImage L Y ≤ barImage L P := barImage_mono hYP
  have hYbar_card : Nat.card (barImage L Y) = 3 := by
    rw [card_barImage_of_isPGroup (X := Y) (hYP.trans hPL) (s := 3) (by norm_num)
      (by norm_num) hY3, hY]
  rcases (hK5 (Bar2 L) n hX p hp hpn (barImage L P) hS3 hSidx).2.2.1
      (barImage L Y) hYbar_le hYbar_card with h | h
  · exact Or.inl ((notationA8103_barImage_iff hPL hP3 hp hp2 hYP).mp h)
  · exact Or.inr ((notationB8103_barImage_iff hPL hP3 hYP).mp h)

theorem dvd_card_bar2_of_notationA8103 (hK5 : KU45Types) {L P A : Subgroup G} {p n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1) (hA : F08.NotationA8103 L P p n A) :
    p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G)))) := by
  have hPL : P ≤ L := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hA3 : IsPGroup 3 A := hP3.to_le hA.2.1
  obtain ⟨hS3, hSidx⟩ := isPGroup_barImage_of_isSylowOf (s := 3) (by norm_num) hP
  have hAbar : F08.NotationA8103 ⊤ (barImage L P) p n (barImage L A) :=
    (notationA8103_barImage_iff hPL hP3 hp hp2 hA.2.1).mpr hA
  have hdvd := (hK5 (Bar2 L) n hX p hp hpn (barImage L P) hS3 hSidx).2.2.2.1
    (barImage L A) hAbar
  have hcard := Nat.card_congr
    (nonempty_bar2_derInf8_equiv (L := L) (X := A) (hA.2.1.trans hPL) (s := 3)
      (by norm_num) (by norm_num) hA3).some.toEquiv
  rw [hcard]
  exact hdvd

theorem exists_conj_of_notationB8103 (hK5 : KU45Types) {L P B₁ B₂ : Subgroup G} {p n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (h₁ : F08.NotationB8103 L P n B₁) (h₂ : F08.NotationB8103 L P n B₂) :
    ∃ l ∈ L, B₂ = B₁.map (MulAut.conj l).toMonoidHom := by
  have hPL : P ≤ L := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  obtain ⟨hS3, hSidx⟩ := isPGroup_barImage_of_isSylowOf (s := 3) (by norm_num) hP
  have hB₁bar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B₁) :=
    (notationB8103_barImage_iff hPL hP3 h₁.2.1).mpr h₁
  have hB₂bar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B₂) :=
    (notationB8103_barImage_iff hPL hP3 h₂.2.1).mpr h₂
  obtain ⟨x, hx⟩ := (hK5 (Bar2 L) n hX p hp hpn (barImage L P) hS3 hSidx).2.2.2.2
    (barImage L B₁) (barImage L B₂) hB₁bar hB₂bar
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) x
  have hbar' : barImage L (B₁.map (MulAut.conj (l₀ : G)).toMonoidHom) = barImage L B₂ := by
    rw [barImage_map_conj (L := L) (B := B₁) (h₁.2.1.trans hPL) l₀]
    exact hx.symm
  have hXL : B₁.map (MulAut.conj (l₀ : G)).toMonoidHom ≤ L := by
    intro z hz
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hz
    rw [← hbz]
    exact L.mul_mem (L.mul_mem l₀.2 (hPL (h₁.2.1 hb))) (L.inv_mem l₀.2)
  have hX3 : IsPGroup 3 (B₁.map (MulAut.conj (l₀ : G)).toMonoidHom) :=
    (hP3.to_le h₁.2.1).map (MulAut.conj (l₀ : G)).toMonoidHom
  have hXc : Nat.card (B₁.map (MulAut.conj (l₀ : G)).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (l₀ : G)).injective, h₁.1]
  obtain ⟨l₁, hl₁L, hconj⟩ :=
    exists_conj_of_barImage_eq_of_card_three hXL (h₂.2.1.trans hPL) hX3
      (hP3.to_le h₂.2.1) hXc h₂.1 hbar'
  refine ⟨l₁ * l₀, L.mul_mem hl₁L l₀.2, ?_⟩
  rw [hconj, Subgroup.map_map]
  have hcomp : (MulAut.conj l₁).toMonoidHom.comp (MulAut.conj (l₀ : G)).toMonoidHom =
      (MulAut.conj (l₁ * (l₀ : G))).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
