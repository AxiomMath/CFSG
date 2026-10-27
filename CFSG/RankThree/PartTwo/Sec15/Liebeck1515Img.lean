module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G]

section Img

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_le_iff {X : Subgroup G} (hX : X ≤ Y ⊔ A) {N : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} :
    img148 A Y X ≤ N ↔
      X ≤ (N.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype := by
  rw [img148, Subgroup.map_le_iff_le_comap]
  constructor
  · intro h x hx
    exact ⟨⟨x, hX hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · rintro h ⟨x, hx'⟩ hx
    obtain ⟨y, hy, hyx⟩ := h (Subgroup.mem_subgroupOf.mp hx)
    have : y = ⟨x, hx'⟩ := Subtype.ext hyx
    exact this ▸ hy

theorem img148_sSup_le {S : Set (Subgroup G)} (hS : ∀ Q ∈ S, Q ≤ Y ⊔ A)
    {N : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)} (h : ∀ Q ∈ S, img148 A Y Q ≤ N) :
    img148 A Y (sSup S) ≤ N := by
  rw [img148_le_iff (sSup_le hS)]
  exact sSup_le fun Q hQ => (img148_le_iff (hS Q hQ)).mp (h Q hQ)

theorem img148_mono {X X' : Subgroup G} (h : X ≤ X') : img148 A Y X ≤ img148 A Y X' :=
  Subgroup.map_mono fun _ hx => h hx

variable [Finite G]

theorem card_img148_dvd (X : Subgroup G) : Nat.card (img148 A Y X) ∣ Nat.card X := by
  exact (Subgroup.card_map_dvd _ _).trans
    (Subgroup.card_comap_dvd_of_injective X (Y ⊔ A).subtype Subtype.val_injective)

theorem eq_top_of_isPGroup_three {LB : Subgroup G → Subgroup G}
    (N : Subgroup ↥(img148 A Y (deltaZero A LB Y))) [N.Normal]
    (hN : IsPGroup 3 (↥(img148 A Y (deltaZero A LB Y)) ⧸ N)) : N = ⊤ := by
  have key : ∀ Q ∈ collectionIn (scriptQZero A LB) Y,
      img148 A Y Q ≤ N.map (img148 A Y (deltaZero A LB Y)).subtype := by
    intro Q hQ
    have hQX : img148 A Y Q ≤ img148 A Y (deltaZero A LB Y) :=
      img148_mono (le_deltaZero hQ.1 hQ.2)
    have hQ3 : ¬ 3 ∣ Nat.card Q :=
      (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.1.2.1
    set K : Subgroup ↥(img148 A Y (deltaZero A LB Y)) :=
      (img148 A Y Q).subgroupOf (img148 A Y (deltaZero A LB Y)) with hK
    have hK3 : ¬ 3 ∣ Nat.card K := by
      intro h3
      apply hQ3
      refine h3.trans ((Subgroup.card_comap_dvd_of_injective _
        (img148 A Y (deltaZero A LB Y)).subtype Subtype.val_injective).trans (card_img148_dvd Q))
    have hKN : K ≤ N := by
      have hmap : K.map (QuotientGroup.mk' N) = ⊥ := by
        have hp : IsPGroup 3 (K.map (QuotientGroup.mk' N)) := hN.to_subgroup _
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
        rcases n with _ | n
        · exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero])
        · exfalso
          apply hK3
          exact (hn ▸ dvd_pow_self 3 (Nat.succ_ne_zero n)).trans (Subgroup.card_map_dvd _ _)
      have h := (Subgroup.map_eq_bot_iff K).mp hmap
      rwa [QuotientGroup.ker_mk'] at h
    intro x hx
    exact ⟨⟨x, hQX hx⟩, hKN (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hle : img148 A Y (deltaZero A LB Y) ≤ N.map (img148 A Y (deltaZero A LB Y)).subtype :=
    img148_sSup_le (fun Q hQ => hQ.2.trans le_sup_left) key
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, hnx⟩ := hle x.2
  have : n = x := Subtype.ext hnx
  exact this ▸ hn

theorem img148_eq_of_noNormal3 {X D : Subgroup G} (hXY : X ≤ Y ⊔ A) (hDX : D ≤ X)
    (hX : X = pPrimeCoreOf 3 X ⊔ D) (hno : Ronan148W.NoNormal3 ↥(img148 A Y X)) :
    img148 A Y X = img148 A Y D := by
  set O := pPrimeCoreOf 3 X with hO
  have hOX : O ≤ X := pPrimeCoreOf_le 3 X
  have hOX' : img148 A Y O ≤ img148 A Y X := img148_mono hOX
  have hnorm : img148 A Y X ≤ Subgroup.normalizer ((img148 A Y O : Subgroup _) : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxN : (x : G) ∈ Subgroup.normalizer (O : Set G) :=
      le_normalizer_pPrimeCoreOf 3 X (Subgroup.mem_subgroupOf.mp hx)
    constructor
    · rintro ⟨o, ho, rfl⟩
      refine ⟨x * o * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.mem_subgroupOf.mp ho)
    · rintro ⟨o, ho, hoy⟩
      refine ⟨x⁻¹ * o * x, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) _).mp
          (Subgroup.mem_subgroupOf.mp ho)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hoy]
        group
  set K : Subgroup ↥(img148 A Y X) := (img148 A Y O).subgroupOf (img148 A Y X) with hK
  have hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOX').mpr hnorm
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h3
    have hO3 := coprime_card_pPrimeCoreOf 3 X
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3
      (h3.trans ((Subgroup.card_comap_dvd_of_injective _ _ Subtype.val_injective).trans
        (card_img148_dvd O)))
  have hK0 : K = ⊥ := hno K hKn hK3
  have hO0 : img148 A Y O = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hOX' hy⟩ : ↥(img148 A Y X)) ∈ K := Subgroup.mem_subgroupOf.mpr hy
    rw [hK0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  refine le_antisymm ?_ (img148_mono hDX)
  have hOD : img148 A Y (O ⊔ D) ≤ img148 A Y O ⊔ img148 A Y D := by
    rw [img148_le_iff (sup_le (hOX.trans hXY) (hDX.trans hXY))]
    exact sup_le ((img148_le_iff (hOX.trans hXY)).mp le_sup_left)
      ((img148_le_iff (hDX.trans hXY)).mp le_sup_right)
  calc img148 A Y X = img148 A Y (O ⊔ D) := by rw [← hX]
    _ ≤ img148 A Y O ⊔ img148 A Y D := hOD
    _ = img148 A Y D := by rw [hO0, bot_sup_eq]

theorem img148_inSubgroup_perfectResidual {D : Subgroup G} (hD : D ≤ Y ⊔ A)
    (hp : Group.IsPerfect ↥(img148 A Y D)) :
    img148 A Y (inSubgroup perfectResidual D) = img148 A Y D := by
  set H := Y ⊔ A with hH
  set D' : Subgroup ↥H := D.subgroupOf H with hD'
  have hDmap : D'.map H.subtype = D := by
    rw [hD', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hD
  have h1 : inSubgroup perfectResidual D =
      ((perfectResidual ↥D').map D'.subtype).map H.subtype := by
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map H.subtype D']
    exact congrArg (inSubgroup perfectResidual) hDmap.symm
  have h2 : (inSubgroup perfectResidual D).subgroupOf H = (perfectResidual ↥D').map D'.subtype := by
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [img148, h2, CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hp

end Img

theorem exists_hom_of_inf_eq_theta {X M : Subgroup G}
    (hXM : X ≤ Subgroup.normalizer (M : Set G))
    (heq : X ⊓ M = inSubgroup (aschbacherSolvableCore 3) X) :
    ∃ ρ : ↥(X ⊔ M) →* ↥X ⧸ aschbacherSolvableCore 3 ↥X,
      Function.Surjective ρ ∧ ρ.ker = M.subgroupOf (X ⊔ M) := by
  have hθ : M.subgroupOf X = aschbacherSolvableCore 3 ↥X := by
    have h1 : M.subgroupOf X = (X ⊓ M).subgroupOf X := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1, heq, inSubgroup]
    exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hXM
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXM
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X M hXM
  let e₂ : ↥X ⧸ M.subgroupOf X ≃* ↥X ⧸ aschbacherSolvableCore 3 ↥X :=
    QuotientGroup.quotientMulEquivOfEq hθ
  refine ⟨(e₂.toMonoidHom.comp e.symm.toMonoidHom).comp
    (QuotientGroup.mk' (M.subgroupOf (X ⊔ M))), ?_, ?_⟩
  · exact (e₂.surjective.comp e.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  · rw [MonoidHom.ker_comp_of_injective _ _ (by exact e₂.injective.comp e.symm.injective)]
    exact QuotientGroup.ker_mk' _

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515
