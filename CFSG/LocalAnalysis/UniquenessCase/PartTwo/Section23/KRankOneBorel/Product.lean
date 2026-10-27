module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Dich
import CFSG.Goldschmidt75.B1Perfect
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup

private theorem surjective_quotient_comp_subtype {Y : Type} [Group Y] {Y₁ Y₂ : Subgroup Y}
    [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤) :
    Function.Surjective ((QuotientGroup.mk' Y₂).comp Y₁.subtype) := by
  have hmap : Subgroup.map (QuotientGroup.mk' Y₂) Y₁ = ⊤ := by
    have hcomap : Subgroup.comap (QuotientGroup.mk' Y₂)
        (Subgroup.map (QuotientGroup.mk' Y₂) Y₁) = ⊤ := by
      rw [QuotientGroup.comap_map_mk' Y₂ Y₁, sup_comm, hsup]
    have h1 := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y₂)
      (Subgroup.map (QuotientGroup.mk' Y₂) Y₁)
    rw [hcomap, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Y₂)] at h1
    exact h1.symm
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hmap]

private theorem rankOneOver_quotient {Y : Type} [Group Y] [Finite Y] {Y₁ Y₂ : Subgroup Y}
    [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤) (hr : RankOneOver ↥Y₁) : RankOneOver (Y ⧸ Y₂) :=
  RankOneOver.of_surjective ((QuotientGroup.mk' Y₂).comp Y₁.subtype)
    (surjective_quotient_comp_subtype hsup) hr

private theorem sup_eq_top_of_map_quotient_eq_top {Y : Type} [Group Y] {Y₂ H : Subgroup Y}
    [Y₂.Normal] (h : Subgroup.map (QuotientGroup.mk' Y₂) H = ⊤) : H ⊔ Y₂ = ⊤ := by
  have h1 : Subgroup.comap (QuotientGroup.mk' Y₂)
      (Subgroup.map (QuotientGroup.mk' Y₂) H) = ⊤ := by
    rw [h, Subgroup.comap_top]
  rw [QuotientGroup.comap_map_mk' Y₂ H, sup_comm] at h1
  exact h1

private theorem le_normalizer_sup_of_quotient {Y : Type} [Group Y] [Finite Y]
    {Y₁ Y₂ : Subgroup Y} [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤) (hr : RankOneOver ↥Y₁)
    (S : Sylow 2 Y) (H : Subgroup Y) (hSH : (S : Subgroup Y) ≤ H)
    (hHY₂ : H ⊔ Y₂ ≠ ⊤) :
    H ≤ normalizer ((((S : Subgroup Y) ⊔ Y₂) : Subgroup Y) : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrq : RankOneOver (Y ⧸ Y₂) := rankOneOver_quotient hsup hr
  have hle : ((S.mapSurjective (QuotientGroup.mk'_surjective Y₂) : Sylow 2 (Y ⧸ Y₂)) :
      Subgroup (Y ⧸ Y₂)) ≤ H.map (QuotientGroup.mk' Y₂) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSH
  rcases hrq (S.mapSurjective (QuotientGroup.mk'_surjective Y₂))
      (H.map (QuotientGroup.mk' Y₂)) hle with hN | htop
  · have hcomap : Subgroup.comap (QuotientGroup.mk' Y₂) (H.map (QuotientGroup.mk' Y₂)) ≤
        Subgroup.comap (QuotientGroup.mk' Y₂)
          (normalizer (((S.mapSurjective (QuotientGroup.mk'_surjective Y₂) :
            Sylow 2 (Y ⧸ Y₂)) : Subgroup (Y ⧸ Y₂)) : Set (Y ⧸ Y₂))) :=
      Subgroup.comap_mono hN
    rw [Subgroup.comap_normalizer_eq_of_surjective
      (H := ((S.mapSurjective (QuotientGroup.mk'_surjective Y₂) : Sylow 2 (Y ⧸ Y₂)) :
        Subgroup (Y ⧸ Y₂))) (QuotientGroup.mk'_surjective Y₂)] at hcomap
    rw [QuotientGroup.comap_map_mk' Y₂ H] at hcomap
    have hcomap' : H ≤ normalizer ((Subgroup.comap (QuotientGroup.mk' Y₂)
        (((S.mapSurjective (QuotientGroup.mk'_surjective Y₂) : Sylow 2 (Y ⧸ Y₂)) :
          Subgroup (Y ⧸ Y₂)))) : Set Y) :=
      le_trans le_sup_right hcomap
    have heq : Subgroup.comap (QuotientGroup.mk' Y₂)
        (((S.mapSurjective (QuotientGroup.mk'_surjective Y₂) : Sylow 2 (Y ⧸ Y₂)) :
          Subgroup (Y ⧸ Y₂))) = (S : Subgroup Y) ⊔ Y₂ := by
      rw [Sylow.coe_mapSurjective, QuotientGroup.comap_map_mk', sup_comm]
    rwa [heq] at hcomap'
  · exact absurd (sup_eq_top_of_map_quotient_eq_top htop) hHY₂

private theorem le_of_sup_eq_top_of_perfect {Y : Type} [Group Y] [Finite Y]
    {Y₁ Y₂ : Subgroup Y} [Y₁.Normal] [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤)
    (hcomm : ⁅Y₁, Y₂⁆ = ⊥) (hp₁ : ⁅Y₁, Y₁⁆ = Y₁) (S : Sylow 2 Y) (H : Subgroup Y)
    (hSH : (S : Subgroup Y) ≤ H) (hHY₂ : H ⊔ Y₂ = ⊤) : Y₁ ≤ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : Y₂ ≤ Subgroup.centralizer ((Y₁ : Subgroup Y) : Set Y) := by
    have hc : ⁅Y₂, Y₁⁆ = (⊥ : Subgroup Y) := by rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hnorm : Y₁ ≤ Subgroup.normalizer ((H ⊓ Y₁ : Subgroup Y) : Set Y) := by
    have hHY₁ : H ≤ Subgroup.normalizer ((Y₁ : Subgroup Y) : Set Y) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hH : H ≤ Subgroup.normalizer ((H ⊓ Y₁ : Subgroup Y) : Set Y) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := Y₁)
        ⟨Subgroup.le_normalizer hx, hHY₁ hx⟩
    have hAY₁ : H ⊓ Y₁ ≤ Y₁ := inf_le_right
    have hY₂N : Y₂ ≤ Subgroup.normalizer ((H ⊓ Y₁ : Subgroup Y) : Set Y) :=
      hcent.trans ((Subgroup.centralizer_le (fun x hx => hAY₁ hx)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hHN : H ⊔ Y₂ ≤ Subgroup.normalizer ((H ⊓ Y₁ : Subgroup Y) : Set Y) :=
      sup_le hH hY₂N
    rw [hHY₂] at hHN
    exact le_top.trans hHN
  have hNnormal : ((H ⊓ Y₁).subgroupOf Y₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnorm
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S Y₁
  have hPN : (P : Subgroup ↥Y₁) ≤ (H ⊓ Y₁).subgroupOf Y₁ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, x.2⟩
    have hxS : (x : Y) ∈ (S : Subgroup Y) := by
      have h1 : Y₁.subtype x ∈ (P : Subgroup ↥Y₁).map Y₁.subtype := ⟨x, hx, rfl⟩
      rw [hP] at h1
      exact (Subgroup.mem_inf.mp h1).1
    exact hSH hxS
  have hodd : Odd ((H ⊓ Y₁).subgroupOf Y₁).index :=
    Odd.of_dvd_nat
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Sylow.not_dvd_index P)))
      (Subgroup.index_dvd_of_le hPN)
  exact le_trans (CFSG.Goldschmidt75.le_of_perfect_of_odd_index hp₁ hNnormal hodd) inf_le_left

private theorem sup_eq_inf_sup_of_isSylow {Y : Type} [Group Y] [Finite Y]
    {Y₁ Y₂ : Subgroup Y} [Y₁.Normal] [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤) (S : Sylow 2 Y) :
    (S : Subgroup Y) ⊔ Y₂ = ((S : Subgroup Y) ⊓ Y₁) ⊔ Y₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S Y₁
  have hf₁ : Function.Surjective ((QuotientGroup.mk' Y₂).comp Y₁.subtype) :=
    surjective_quotient_comp_subtype hsup
  let Q : Sylow 2 (Y ⧸ Y₂) := P.mapSurjective hf₁
  have hQcoe : (Q : Subgroup (Y ⧸ Y₂)) =
      ((S : Subgroup Y) ⊓ Y₁).map (QuotientGroup.mk' Y₂) := by
    have hQ : (Q : Subgroup (Y ⧸ Y₂)) =
        (P : Subgroup ↥Y₁).map ((QuotientGroup.mk' Y₂).comp Y₁.subtype) :=
      Sylow.coe_mapSurjective hf₁ P
    rw [hQ, ← Subgroup.map_map, hP]
  have hle : (Q : Subgroup (Y ⧸ Y₂)) ≤ (S : Subgroup Y).map (QuotientGroup.mk' Y₂) := by
    rw [hQcoe]
    exact Subgroup.map_mono inf_le_left
  have h2 : IsPGroup 2 (((S : Subgroup Y).map (QuotientGroup.mk' Y₂) : Subgroup (Y ⧸ Y₂))) :=
    S.isPGroup'.map (QuotientGroup.mk' Y₂)
  have hmax : (S : Subgroup Y).map (QuotientGroup.mk' Y₂) =
      ((S : Subgroup Y) ⊓ Y₁).map (QuotientGroup.mk' Y₂) := by
    have := Q.is_maximal' h2 hle
    rwa [hQcoe] at this
  have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' Y₂)) hmax
  rw [QuotientGroup.comap_map_mk' Y₂ (S : Subgroup Y),
      QuotientGroup.comap_map_mk' Y₂ ((S : Subgroup Y) ⊓ Y₁)] at h1
  rw [sup_comm (Y₂ : Subgroup Y) ((S : Subgroup Y)),
      sup_comm (Y₂ : Subgroup Y) (((S : Subgroup Y) ⊓ Y₁))] at h1
  exact h1

private theorem eq_sup_inf_of_isSylow {Y : Type} [Group Y] [Finite Y]
    {Y₁ Y₂ : Subgroup Y} [Y₁.Normal] [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤) (S : Sylow 2 Y) :
    (S : Subgroup Y) = ((S : Subgroup Y) ⊓ Y₁) ⊔ ((S : Subgroup Y) ⊓ Y₂) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro s hs
  have hsY₂ : s ∈ ((S : Subgroup Y) ⊓ Y₁) ⊔ Y₂ := by
    rw [← sup_eq_inf_sup_of_isSylow hsup S]
    exact Subgroup.mem_sup_left hs
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hsY₂
  have hbS : b ∈ (S : Subgroup Y) := by
    have hb' : b = a⁻¹ * s := by rw [← hab]; group
    rw [hb']
    exact (S : Subgroup Y).mul_mem ((S : Subgroup Y).inv_mem ha.1) hs
  rw [← hab]
  exact Subgroup.mul_mem_sup ha (Subgroup.mem_inf.mpr ⟨hbS, hb⟩)

private theorem inf_sup_le_normalizer {Y : Type} [Group Y] [Finite Y]
    {Y₁ Y₂ : Subgroup Y} [Y₁.Normal] [Y₂.Normal] (hsup : Y₁ ⊔ Y₂ = ⊤)
    (hcomm : ⁅Y₁, Y₂⁆ = ⊥) (S : Sylow 2 Y) :
    (((S : Subgroup Y) ⊔ Y₁) ⊓ ((S : Subgroup Y) ⊔ Y₂)) ≤
      normalizer ((S : Subgroup Y) : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent₂ : Y₂ ≤ Subgroup.centralizer ((Y₁ : Subgroup Y) : Set Y) := by
    have hc : ⁅Y₂, Y₁⁆ = (⊥ : Subgroup Y) := by rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcent₁ : Y₁ ≤ Subgroup.centralizer ((Y₂ : Subgroup Y) : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  set A : Subgroup Y := (S : Subgroup Y) ⊓ Y₁ with hA
  set B : Subgroup Y := (S : Subgroup Y) ⊓ Y₂ with hB
  have hS₂ : (S : Subgroup Y) ⊔ Y₂ = A ⊔ Y₂ := by
    rw [hA]
    exact sup_eq_inf_sup_of_isSylow hsup S
  have hsup' : Y₂ ⊔ Y₁ = ⊤ := by rw [sup_comm, hsup]
  have hS₁ : (S : Subgroup Y) ⊔ Y₁ = B ⊔ Y₁ := by
    rw [hB]
    exact sup_eq_inf_sup_of_isSylow (Y₁ := Y₂) (Y₂ := Y₁) hsup' S
  intro w hw
  obtain ⟨hw₁, hw₂⟩ := Subgroup.mem_inf.mp hw
  have hw₂' : w ∈ A ⊔ Y₂ := by rwa [hS₂] at hw₂
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hw₂'
  have hw₁' : w ∈ B ⊔ Y₁ := by rwa [hS₁] at hw₁
  obtain ⟨c, hc, d, hd, hcd⟩ := Subgroup.mem_sup_of_normal_right.mp hw₁'
  have hAY₁ : A ≤ Y₁ := by rw [hA]; exact inf_le_right
  have hBY₂ : B ≤ Y₂ := by rw [hB]; exact inf_le_right
  have hY₂N : Y₂ ≤ normalizer (A : Set Y) :=
    hcent₂.trans ((Subgroup.centralizer_le (fun x hx => hAY₁ hx)).trans
      (Subgroup.centralizer_le_normalizer (A : Set Y)))
  have hY₁N : Y₁ ≤ normalizer (B : Set Y) :=
    hcent₁.trans ((Subgroup.centralizer_le (fun x hx => hBY₂ hx)).trans
      (Subgroup.centralizer_le_normalizer (B : Set Y)))
  have hwN₂ : w ∈ normalizer (A : Set Y) := by
    rw [← hab]
    exact (Subgroup.normalizer (A : Set Y)).mul_mem (Subgroup.le_normalizer ha) (hY₂N hb)
  have hwN₁ : w ∈ normalizer (B : Set Y) := by
    rw [← hcd]
    exact (Subgroup.normalizer (B : Set Y)).mul_mem (Subgroup.le_normalizer hc) (hY₁N hd)
  have hSeq : (S : Subgroup Y) = A ⊔ B := by
    rw [hA, hB]
    exact eq_sup_inf_of_isSylow hsup S
  have := Subgroup.inf_normalizer_le_normalizer_sup (H := A) (K := B) ⟨hwN₂, hwN₁⟩
  rwa [← hSeq] at this

theorem dich_of_product {Y : Type} [Group Y] [Finite Y] (Y₁ Y₂ : Subgroup Y) (hn₁ : Y₁.Normal)
    (hn₂ : Y₂.Normal) (hsup : Y₁ ⊔ Y₂ = ⊤) (hcomm : ⁅Y₁, Y₂⁆ = ⊥) (hp₁ : ⁅Y₁, Y₁⁆ = Y₁)
    (hp₂ : ⁅Y₂, Y₂⁆ = Y₂) (hr₁ : RankOneOver ↥Y₁) (hr₂ : RankOneOver ↥Y₂) (S : Sylow 2 Y)
    (H : Subgroup Y) (hSH : (S : Subgroup Y) ≤ H) (h12 : Y₁ ≤ H → Y₂ ≤ H)
    (h21 : Y₂ ≤ H → Y₁ ≤ H) :
    H ≤ normalizer ((S : Subgroup Y) : Set Y) ∨ H = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Y₁.Normal := hn₁
  haveI : Y₂.Normal := hn₂
  by_cases hHY₂ : H ⊔ Y₂ = ⊤
  · have hY₁H : Y₁ ≤ H :=
      le_of_sup_eq_top_of_perfect hsup hcomm hp₁ S H hSH hHY₂
    have hY₂H : Y₂ ≤ H := h12 hY₁H
    refine Or.inr (le_antisymm le_top ?_)
    rw [← hsup]
    exact sup_le hY₁H hY₂H
  by_cases hHY₁ : H ⊔ Y₁ = ⊤
  · have hsup' : Y₂ ⊔ Y₁ = ⊤ := by rw [sup_comm, hsup]
    have hcomm' : ⁅Y₂, Y₁⁆ = ⊥ := by rw [Subgroup.commutator_comm, hcomm]
    have hY₂H : Y₂ ≤ H :=
      le_of_sup_eq_top_of_perfect hsup' hcomm' hp₂ S H hSH hHY₁
    have hY₁H : Y₁ ≤ H := h21 hY₂H
    refine Or.inr (le_antisymm le_top ?_)
    rw [← hsup]
    exact sup_le hY₁H hY₂H
  · left
    have hHN₂ : H ≤ normalizer ((((S : Subgroup Y) ⊔ Y₂) : Subgroup Y) : Set Y) :=
      le_normalizer_sup_of_quotient hsup hr₁ S H hSH hHY₂
    have hsup' : Y₂ ⊔ Y₁ = ⊤ := by rw [sup_comm, hsup]
    have hHN₁ : H ≤ normalizer ((((S : Subgroup Y) ⊔ Y₁) : Subgroup Y) : Set Y) :=
      le_normalizer_sup_of_quotient (Y₁ := Y₂) (Y₂ := Y₁) hsup' hr₂ S H hSH hHY₁
    set W : Subgroup Y :=
      ((S : Subgroup Y) ⊔ Y₁) ⊓ ((S : Subgroup Y) ⊔ Y₂) with hWdef
    have hSW : (S : Subgroup Y) ≤ W := by
      rw [hWdef]
      exact le_inf le_sup_left le_sup_left
    have hWN : W ≤ normalizer ((S : Subgroup Y) : Set Y) := by
      rw [hWdef]
      exact inf_sup_le_normalizer hsup hcomm S
    have hHNW : H ≤ normalizer (W : Set Y) := by
      rw [hWdef]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (H := ((S : Subgroup Y) ⊔ Y₁)) (K := ((S : Subgroup Y) ⊔ Y₂))
        ⟨hHN₁ hx, hHN₂ hx⟩
    exact hHNW.trans (normalizer_le_normalizer_of_le_normalizer S hSW hWN)

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel
