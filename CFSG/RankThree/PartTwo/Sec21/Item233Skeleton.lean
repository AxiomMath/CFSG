module

public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces
public import CFSG.RankThree.PartTwo.Sec21.Item233

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _)

theorem centralizer_inf_le_centralizer_sup (Y X : Subgroup G) :
    Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.centralizer ((Y ⊔ X : Subgroup G) : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [← Subgroup.le_centralizer_iff]
    exact inf_le_left
  · rw [← Subgroup.le_centralizer_iff]
    exact inf_le_right

theorem centralizer_inf_le_of_le_sup {Y X X' : Subgroup G} (h : X' ≤ Y ⊔ X) :
    Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (X : Set G) ≤
      Subgroup.centralizer (X' : Set G) :=
  (centralizer_inf_le_centralizer_sup Y X).trans (Subgroup.centralizer_le h)

theorem map_centralizer_subgroupOf {Y C : Subgroup G} (hYC : Y ≤ C) :
    (Subgroup.centralizer ((Y.subgroupOf C : Subgroup C) : Set C)).map C.subtype =
      Subgroup.centralizer (Y : Set G) ⊓ C := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, c.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp hc) ⟨y, hYC hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  · rintro ⟨hx, hxC⟩
    refine ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))

theorem conj_mem_of_inner {A B Y : Subgroup G} (hYC : Y ≤ Subgroup.centralizer (B : Set G))
    (hAC : A ≤ Subgroup.centralizer (B : Set G))
    (hCY : Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hinner : ∀ a ∈ A, ∃ y ∈ Y, y⁻¹ * a ∈ Subgroup.centralizer (Y : Set G)) :
    ∀ h ∈ Subgroup.centralizer (B : Set G),
      ∀ k ∈ Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (B : Set G)) ⊔ A,
        h * k * h⁻¹ ∈
          Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (B : Set G)) ⊔ A := by
  set C := Subgroup.centralizer (B : Set G)
  set Z := Subgroup.centralizer (Y : Set G) ⊓ C
  have hAYZ : A ≤ Y ⊔ Z := by
    intro a ha
    obtain ⟨y, hy, hya⟩ := hinner a ha
    have hyaC : y⁻¹ * a ∈ C := C.mul_mem (C.inv_mem (hYC hy)) (hAC ha)
    have : a = y * (y⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ⟨hya, hyaC⟩)
  have hK : Y ⊔ Z ⊔ A = Y ⊔ Z := sup_eq_left.mpr hAYZ
  intro h hh k hk
  rw [hK] at hk ⊢
  have hhZ : h ∈ Subgroup.normalizer (Z : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_le_normalizer_centralizer Y (hCY hh), Subgroup.le_normalizer hh⟩
  have hhK : h ∈ Subgroup.normalizer ((Y ⊔ Z : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup Y Z ⟨hCY hh, hhZ⟩
  exact (Subgroup.mem_normalizer_iff.mp hhK k).mp hk

theorem conj_mem_of_innerDiagonalSL34 [Finite G] (hc : InnerDiagonalSL34) {C Y P : Subgroup G}
    (hYC : Y ≤ C) (hPC : P ≤ C) (hCY : C ≤ Subgroup.normalizer (Y : Set G))
    (hY : Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hP : IsPGroup 3 P) :
    ∀ h ∈ C, ∀ k ∈ Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ C) ⊔ P,
      h * k * h⁻¹ ∈ Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ C) ⊔ P := by
  have hY'n : (Y.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYC).mpr hCY
  have hY' : Nonempty (Y.subgroupOf C ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    hY.map fun e => (Subgroup.subgroupOfEquivOfLe hYC).trans e
  have hP' : IsPGroup 3 (P.subgroupOf C) := hP.comap_subtype
  have hQ := hc C (Y.subgroupOf C) (P.subgroupOf C) hY'n hY' hP'
  have hmap : (Y.subgroupOf C ⊔ Subgroup.centralizer ((Y.subgroupOf C : Subgroup C) : Set C) ⊔
      P.subgroupOf C).map C.subtype = Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ C) ⊔ P := by
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYC,
      Subgroup.map_subgroupOf_eq_of_le hPC, map_centralizer_subgroupOf hYC]
  intro h hh k hk
  rw [← hmap] at hk ⊢
  obtain ⟨q, hq, rfl⟩ := hk
  exact ⟨⟨h, hh⟩ * q * ⟨h, hh⟩⁻¹, hQ.conj_mem q hq ⟨h, hh⟩, by simp⟩

theorem centralizer_le_of_frattini [Finite G] {A B Y M : Subgroup G} (hAe : IsElemAbelian 3 A)
    (huniq : ∀ (S : Sylow 3 G) (C : Subgroup G), A ≤ S → C ≤ S → IsElemAbelian 3 C →
      Nat.card A ≤ Nat.card C → C = A)
    (hAM : A ≤ M) (hYM : Y ≤ M) (hW : Subgroup.normalizer (A : Set G) ≤ M)
    (hK : ∀ h ∈ Subgroup.centralizer (B : Set G),
      ∀ k ∈ Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (B : Set G)) ⊔ A,
        h * k * h⁻¹ ∈
          Y ⊔ (Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (B : Set G)) ⊔ A)
    (hCYB : Subgroup.centralizer (Y : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤ M) :
    Subgroup.centralizer (B : Set G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h hh
  obtain ⟨k, hk, hkn⟩ := exists_mem_mul_normalizer hAe huniq le_sup_right hK hh
  have hkM : k ∈ M := (sup_le (sup_le hYM hCYB) hAM) hk
  have := M.mul_mem hkM (hW hkn)
  simpa using this

theorem terminal_of_item231Concl {A : Subgroup G} (h : Item231Concl A) :
    (Nonempty (iGroup A ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) := by
  rcases h with ⟨he, -, hA⟩ | ⟨he, -, hA⟩ | ⟨he, -, hA⟩
  · exact Or.inl ⟨he, hA⟩
  · exact Or.inr (Or.inl ⟨he, hA⟩)
  · exact Or.inr (Or.inr ⟨he, hA⟩)

theorem item233Centralizers_of (h231 : Item231) (h232 : Item232) (ha : TerminalOrderThree)
    (hb : Item233Components) (hc : InnerDiagonalSL34) : Item233Centralizers := by
  intro G _ _ A E U c L hpair B hBA hB3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconc := h231 G A E U c L hpair
  obtain ⟨hAI, h2⟩ := h232 G A E U c L hpair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := iGroup A)).exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup (iGroup A)).map (iGroup A).subtype := by
    intro a ha
    exact ⟨⟨a, hAI ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  obtain ⟨-, hJ, hW, S, hS⟩ := h2 Q hAQ
  have hJ' : (CFSG.elemThompson (S : Subgroup G) 3).map (S : Subgroup G).subtype = A := by
    rw [hS]; exact hJ
  have huniq := unique_of_elemThompson_eq S hAe hJ'
  have hT := ha G (iGroup A) A hAI hAe (terminal_of_item231Concl hconc)
  have hAN : A ≤ nGroup A := hAI.trans (iGroup_le_nGroup A)
  have step : ∀ X : Subgroup G, X ≤ A → Nat.card X = 3 →
      Subgroup.centralizer (layerCent (iGroup A) X : Set G) ⊓
          Subgroup.centralizer (X : Set G) ≤ nGroup A →
        Subgroup.centralizer (X : Set G) ≤ nGroup A := by
    intro X hXA hX3 hCN
    have hYC := layerCent_le_centralizer (iGroup A) X
    have hAC := le_centralizer_of_isElemAbelian hAe hXA
    have hCY := hb G A E U c L hpair X hXA hX3
    refine centralizer_le_of_frattini hAe huniq hAN
      ((layerCent_le_left (iGroup A) X).trans (iGroup_le_nGroup A)) hW ?_ hCN
    rcases (hT X hXA hX3).1 with hinner | hSL
    · exact conj_mem_of_inner hYC hAC hCY hinner
    · exact conj_mem_of_innerDiagonalSL34 hc hYC hAC hCY hSL hAp
  obtain ⟨-, B₁, B₂, hB₁A, hB₁3, hB₁, hB₂A, hB₂3, hB₂, hAB₂⟩ := hT B hBA hB3
  have hC₂ : Subgroup.centralizer (B₂ : Set G) ≤ nGroup A :=
    step B₂ hB₂A hB₂3 ((centralizer_inf_le_of_le_sup hAB₂).trans
      ((Subgroup.centralizer_le_normalizer _).trans hW))
  have hC₁ : Subgroup.centralizer (B₁ : Set G) ≤ nGroup A :=
    step B₁ hB₁A hB₁3 ((centralizer_inf_le_of_le_sup hB₂).trans hC₂)
  exact step B hBA hB3 ((centralizer_inf_le_of_le_sup hB₁).trans hC₁)

end CFSG.RankThree.PartTwo.Sec21
