module

public import CFSG.RankThree.Coprime.EvenCenterSectionCover
public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree.Coprime

theorem le_pRank_of_elementaryAbelian {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H]
    (E : Subgroup H) (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem sectionsForceEvenRankFour_of_even_center_cover {Bg : Type} [Group Bg] [Finite Bg]
    {M : Subgroup Bg} (hM : IsQuasisimple M) (hZ : Even (Nat.card (Subgroup.center M)))
    {C : Type} [Group C] (e : M ⧸ Subgroup.center M ≃* C)
    (U : Subgroup C) (hU : IsElementaryAbelian 2 U) (hUc : Nat.card U = 2 ^ 5)
    (hcover : ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
      f.ker ≤ Subgroup.center Y →
      ∃ V : Subgroup Y, IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ 4) :
    SectionsForceEvenRankFour Bg := by
  intro G _ _ H K _ ⟨φ0⟩
  by_contra hlt
  have h3 : evenRank G ≤ 3 := by omega
  let q : H →* Bg := φ0.toMonoidHom.comp (QuotientGroup.mk' K)
  have hq : Function.Surjective q := φ0.surjective.comp (QuotientGroup.mk'_surjective K)
  let H' : Subgroup H := M.comap q
  let H₁ : Subgroup G := H'.map H.subtype
  let e1 : H₁ ≃* H' := (H'.equivMapOfInjective H.subtype H.subtype_injective).symm
  let π : H₁ →* M := ((q.comp H'.subtype).codRestrict M (fun x => x.2)).comp e1.toMonoidHom
  have hπ : Function.Surjective π := by
    intro m
    obtain ⟨h, hh⟩ := hq (m : Bg)
    have hmem : h ∈ H' := by
      show q h ∈ M
      rw [hh]
      exact m.2
    refine ⟨e1.symm ⟨h, hmem⟩, Subtype.ext ?_⟩
    show (q.comp H'.subtype) (e1 (e1.symm ⟨h, hmem⟩)) = (m : Bg)
    rw [MulEquiv.apply_symm_apply]
    exact hh
  have hS : ∃ U' : Subgroup (M ⧸ Subgroup.center M), IsElementaryAbelian 2 U' ∧
      Nat.card U' = 2 ^ (3 + 2) := by
    obtain ⟨h1, h2⟩ := isElementaryAbelian_map_mulEquiv e.symm hU
    exact ⟨U.map e.symm.toMonoidHom, h1, by rw [h2, hUc]⟩
  obtain ⟨Y, _, _, _, φY, hs, hk, hr⟩ :=
    even_center_section_small_rank_central_cover 3 h3 hM hZ hS H₁ π hπ
  have hf : Function.Surjective (e.toMonoidHom.comp φY) := e.surjective.comp hs
  have hfk : (e.toMonoidHom.comp φY).ker ≤ Subgroup.center Y := by
    intro y hy
    apply hk
    rw [MonoidHom.mem_ker] at hy ⊢
    exact e.injective (by simpa using hy)
  obtain ⟨V, hV, hVc⟩ := hcover Y _ hf hfk
  have h4 := le_pRank_of_elementaryAbelian (by norm_num : 1 < 3) V hV hVc
  have h5 := hr 3 Nat.prime_three (by norm_num)
  omega

theorem sectionsForceEvenRankFour_of_centralizer_component {Sg : Type} [Group Sg] [Finite Sg]
    {s : Sg} {K : Subgroup (Subgroup.centralizer ({s} : Set Sg))} (hK : IsQuasisimple K)
    (hZ : Even (Nat.card (Subgroup.center K)))
    {C : Type} [Group C] (e : K ⧸ Subgroup.center K ≃* C)
    (U : Subgroup C) (hU : IsElementaryAbelian 2 U) (hUc : Nat.card U = 2 ^ 5)
    (hcover : ∀ (Y : Type) [Group Y] [Finite Y] (f : Y →* C), Function.Surjective f →
      f.ker ≤ Subgroup.center Y →
      ∃ V : Subgroup Y, IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ 4) :
    SectionsForceEvenRankFour Sg := by
  set M : Subgroup Sg := K.map (Subgroup.centralizer ({s} : Set Sg)).subtype with hM
  let eK : K ≃* M :=
    K.equivMapOfInjective (Subgroup.centralizer ({s} : Set Sg)).subtype Subtype.val_injective
  have hMq : IsQuasisimple M := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK
  have hMZ : Even (Nat.card (Subgroup.center M)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact hZ
  let eQ : M ⧸ Subgroup.center M ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.congr _ _ eK.symm (Subgroup.map_center_eq eK.symm)
  exact sectionsForceEvenRankFour_of_even_center_cover hMq hMZ (eQ.trans e) U hU hUc hcover

end CFSG.RankThree.PartOne
