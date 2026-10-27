module

public import CFSG.Quasithin.Background.RonanE111Dich
public import CFSG.Quasithin.Background.RonanE111SemiMap
public import CFSG.Quasithin.Background.RonanE111SolvConj
public import CFSG.Quasithin.Background.RonanE111CoverSec
public import CFSG.Quasithin.Background.RonanE111Jsub

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem half_two_step {X₀ T J : Subgroup G} (hR : E111Reduced G X₀ T) (hJ : IsComp X₀ J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁)
    (hsol : ∀ H : Subgroup G, T ≤ H → Group.IsSolvable ↥H → H ≤ G₁) {A₀ : Subgroup G}
    (hA₀T : A₀ ≤ T) (hA₀ab : IsElemAbelian 2 A₀)
    (hA₀S : ¬ A₀ ≤ T ⊓ Subgroup.normalizer (J : Set G))
    (hmem : ∀ K : Subgroup G, E1.IsE n ⊤ T A₀ K → K ≤ G₁) {W₀ : Subgroup G}
    (hW₀S : W₀ ≤ T ⊓ Subgroup.normalizer (J : Set G))
    (hV₀ : A₀ ⊓ Subgroup.normalizer (J : Set G) ≤ W₀) {U X Y : Subgroup G}
    (hSU : T ⊓ Subgroup.normalizer (J : Set G) ≤ U)
    (hUJS : U ≤ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (hW₀U : ∀ u ∈ U, ∀ w ∈ W₀, u * w * u⁻¹ ∈ W₀)
    (hXU : X ≤ U) (hXJ : X ≤ J) (hYX : Y ≤ X) (hne : Y ≠ X)
    (hXn : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ ∈ X) (hYn : ∀ u ∈ U, ∀ y ∈ Y, u * y * u⁻¹ ∈ Y)
    (hUXS : U = X ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (hmin : ∀ N : Subgroup G, N ≤ X → Y ≤ N → (∀ u ∈ U, ∀ x ∈ N, u * x * u⁻¹ ∈ N) →
      N = Y ∨ N = X)
    (hK : ∀ K : Subgroup G, T ⊓ Subgroup.normalizer (J : Set G) ≤ K → K ≤ U → K ⊔ Y = U → K = U)
    (hYCov : Y ≤ Cov G₁ J) : X ≤ Cov G₁ J := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hSdef
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hS2 : IsPGroup 2 ↥S := hT.2.1.to_le hST
  have hJS : J ⊔ S ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSN
  have hYU : Y ≤ U := hYX.trans hXU
  have hSCov : S ≤ Cov G₁ J := fun s hs => mem_Cov_of_mem (hTG hs.1) hs.2
  have hSylU : IsSylowIn 2 S U := by
    have h1 := isSylowIn_compSup hR hJ
    refine ⟨hSU, hS2, fun h2 => h1.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex S U (J ⊔ S) hSU hUJS
    rw [← this]
    exact Dvd.dvd.mul_right h2 _
  haveI hXn' : (X.subgroupOf U).Normal := normal_subgroupOf_of_conj hXU hXn
  haveI hYn' : (Y.subgroupOf U).Normal := normal_subgroupOf_of_conj hYU hYn
  have hSylQ : IsSylowIn 2 (S.subgroupOf U) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective U.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hSU, Subgroup.map_top, Subgroup.range_subtype]
    exact hSylU
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U → A.subgroupOf U = B.subgroupOf U → A = B := by
    intro A B hA hB h
    rw [← Subgroup.map_subgroupOf_eq_of_le hA, ← Subgroup.map_subgroupOf_eq_of_le hB, h]
  have hne' : Y.subgroupOf U ≠ X.subgroupOf U := fun h => hne (hinj hYU hXU h)
  have hmin' : ∀ N' : Subgroup ↥U, N'.Normal → Y.subgroupOf U ≤ N' → N' ≤ X.subgroupOf U →
      N' = Y.subgroupOf U ∨ N' = X.subgroupOf U := by
    intro N' hN'n hYN' hN'X
    have h1 : N'.map U.subtype ≤ X := by
      calc N'.map U.subtype ≤ (X.subgroupOf U).map U.subtype := Subgroup.map_mono hN'X
        _ = X := Subgroup.map_subgroupOf_eq_of_le hXU
    have h2 : Y ≤ N'.map U.subtype := by
      calc Y = (Y.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hYU).symm
        _ ≤ N'.map U.subtype := Subgroup.map_mono hYN'
    have h3 : ∀ u ∈ U, ∀ x ∈ N'.map U.subtype, u * x * u⁻¹ ∈ N'.map U.subtype := by
      intro u hu x hx
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨⟨u, hu⟩ * x' * ⟨u, hu⟩⁻¹, hN'n.conj_mem x' hx' ⟨u, hu⟩, rfl⟩
    rcases hmin _ h1 h2 h3 with e | e
    · left
      rw [← Subgroup.comap_map_eq_self_of_injective U.subtype_injective N', e]
      rfl
    · right
      rw [← Subgroup.comap_map_eq_self_of_injective U.subtype_injective N', e]
      rfl
  have hXS' : X.subgroupOf U ⊔ S.subgroupOf U = ⊤ := by
    apply Subgroup.map_injective (f := U.subtype) U.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXU,
      Subgroup.map_subgroupOf_eq_of_le hSU, Subgroup.map_top, Subgroup.range_subtype, ← hUXS]
  have hK' : ∀ K : Subgroup ↥U, S.subgroupOf U ≤ K → K ⊔ Y.subgroupOf U = ⊤ → K = ⊤ := by
    intro K hSK hKY
    have h1 : S ≤ K.map U.subtype := by
      calc S = (S.subgroupOf U).map U.subtype := (Subgroup.map_subgroupOf_eq_of_le hSU).symm
        _ ≤ K.map U.subtype := Subgroup.map_mono hSK
    have h2 : K.map U.subtype ⊔ Y = U := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hYU, ← Subgroup.map_sup, hKY, Subgroup.map_top,
        Subgroup.range_subtype]
    have h3 := hK _ h1 (by rintro _ ⟨k, -, rfl⟩; exact k.2) h2
    apply Subgroup.map_injective (f := U.subtype) U.subtype_injective
    rw [h3, Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨hYs, hdich⟩ := chief_dichotomy hSylQ (Subgroup.subgroupOf_mono U hYX) hne' hmin' hXS' hK'
  have hXs_of : Group.IsSolvable ↥(X.subgroupOf U) → Group.IsSolvable ↥X := fun h =>
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXU).surjective
  rcases hdich with hXsol | ⟨ℒQ, hne𝒟, hSM, hW⟩
  ·
    have hXs := hXs_of hXsol
    have hSX : ∀ s ∈ T ⊓ Subgroup.normalizer (J : Set G), ∀ x ∈ X, s * x * s⁻¹ ∈ X :=
      fun s hs x hx => hXn s (hSU hs) x hx
    have hHs := solvable_conj_sup hR hJ hXJ hXs hSX
    have hH := hsol _ le_sup_right hHs
    have hXH : X ≤ (⨆ t ∈ T, A1b.conjSub t X) ⊔ T := by
      refine le_sup_of_le_left (le_iSup₂_of_le (f := fun t (_ : t ∈ T) => A1b.conjSub t X)
        1 T.one_mem ?_)
      rw [A1b.conjSub_one]
    exact fun x hx => mem_Cov_of_mem (hH (hXH hx)) (Subgroup.le_normalizer (hXJ hx))
  ·
    have hSM' := SemisimpleMod.map_subtype U hSM
    rw [Subgroup.map_subgroupOf_eq_of_le hSU, Subgroup.map_subgroupOf_eq_of_le hXU,
      Subgroup.map_subgroupOf_eq_of_le hYU] at hSM'
    have hYsol : Group.IsSolvable ↥Y := by
      haveI := hYs
      exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hYU).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYU).surjective
    have hnorm : ∀ {Z : Subgroup G}, (∀ u ∈ U, ∀ z ∈ Z, u * z * u⁻¹ ∈ Z) →
        U ≤ Subgroup.normalizer (Z : Set G) := by
      intro Z hZ u hu
      rw [Subgroup.mem_normalizer_iff]
      intro z
      refine ⟨fun hz => hZ u hu z hz, fun hz => ?_⟩
      have := hZ u⁻¹ (U.inv_mem hu) _ hz
      simpa [mul_assoc] using this
    have hSec : SecData S X Y ((fun L : Subgroup ↥U => L.map U.subtype) '' ℒQ) :=
      ⟨hSM', hne𝒟.image _, fun x hx => hnorm hYn (hXU hx), fun s hs => hnorm hXn (hSU hs),
        fun s hs => hnorm hYn (hSU hs), hYsol⟩
    set V₀ : Subgroup G := A₀ ⊓ Subgroup.normalizer (J : Set G) with hV₀def
    have hV₀A : V₀ ≤ A₀ := inf_le_left
    obtain ⟨Z₀, hZ₀A, hZ₀V, hZ₀VA⟩ := exists_compl hA₀ab hV₀A
    have hZ₀ne : Z₀ ≠ ⊥ := by
      intro h
      apply hA₀S
      rw [← hZ₀VA, h, bot_sup_eq]
      exact le_inf (inf_le_left.trans hA₀T) inf_le_right
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z₀, z ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hZ₀ne ((Subgroup.eq_bot_iff_forall Z₀).mpr hc)
    have hZ₀e := isElemAbelian_of_le hA₀ab hZ₀A
    obtain ⟨C, hCZ, hCz, hCzZ⟩ := exists_compl hZ₀e (Subgroup.zpowers_le.mpr hzZ)
    have hset : DiagSetting X₀ T A₀ J C :=
      ⟨hR, hA₀T, hA₀ab, hJ, hCZ.trans hZ₀A,
        le_bot_iff.mp ((inf_le_inf_right _ hCZ).trans hZ₀V.le)⟩
    haveI : Fintype ↥C := Fintype.ofFinite _
    have hzCV : z ∉ C ⊔ V₀ := by
      intro hzm
      have hVC : V₀ ≤ Subgroup.normalizer (C : Set G) :=
        le_normalizer_of_comm fun a ha b hb => hset.comm ha.1 (hset.CA hb)
      obtain ⟨c, hc, v, hv, hcv⟩ := exists_mul_of_mem_sup hVC hzm
      have hvZ : v ∈ Z₀ := by
        have : v = c⁻¹ * z := by rw [hcv]; group
        rw [this]
        exact Z₀.mul_mem (Z₀.inv_mem (hCZ hc)) hzZ
      have hv1 : v = 1 := by
        have : v ∈ Z₀ ⊓ V₀ := ⟨hvZ, hv⟩
        rwa [hZ₀V] at this
      rw [hv1, mul_one] at hcv
      have hzC : z ∈ C := by rw [hcv]; exact hc
      have : z ∈ C ⊓ Subgroup.zpowers z := ⟨hzC, Subgroup.mem_zpowers z⟩
      rw [hCz] at this
      exact hz1 this
    have hcomm : ∀ v ∈ V₀, ∀ s ∈ X, v * s * v⁻¹ * s⁻¹ ∈ Y := by
      intro v hv s hs
      have hvW : v ∈ W₀ := hV₀ hv
      have hvU : v ∈ U := hSU (hW₀S hvW)
      have hW₀U' : W₀ ≤ U := hW₀S.trans hSU
      haveI hW' : (W₀.subgroupOf U).Normal := normal_subgroupOf_of_conj hW₀U' hW₀U
      have hW2 : IsPGroup 2 ↥(W₀.subgroupOf U) :=
        (hT.2.1.to_le (hW₀S.trans hST)).of_equiv (Subgroup.subgroupOfEquivOfLe hW₀U').symm
      have h1 := hW (W₀.subgroupOf U) hW' hW2
      have hmem : ⁅(⟨s, hXU hs⟩ : ↥U), (⟨v, hvU⟩ : ↥U)⁆ ∈
          ⁅X.subgroupOf U, W₀.subgroupOf U⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hs)
          (Subgroup.mem_subgroupOf.mpr hvW)
      have h2 : s * v * s⁻¹ * v⁻¹ ∈ Y := by
        have := Subgroup.mem_subgroupOf.mp (h1 hmem)
        simpa [commutatorElement_def] using this
      have : v * s * v⁻¹ * s⁻¹ = (s * v * s⁻¹ * v⁻¹)⁻¹ := by group
      rw [this]
      exact Y.inv_mem h2
    have hSylX : IsSylowIn 2 (T ⊓ X) X := by
      have hTX : T ⊓ X = S ⊓ X := by
        ext x
        constructor
        · rintro ⟨hxT, hxX⟩
          exact ⟨⟨hxT, Subgroup.le_normalizer (hXJ hxX)⟩, hxX⟩
        · rintro ⟨⟨hxT, _⟩, hxX⟩
          exact ⟨hxT, hxX⟩
      rw [hTX]
      refine ⟨inf_le_right, hS2.to_le inf_le_left, ?_⟩
      show ¬ 2 ∣ (S ⊓ X).relIndex X
      rw [B6.relIndex_inf_eq_relIndex_sup (fun s hs => hnorm hXn (hSU hs))]
      intro h2
      apply hSylU.2.2
      have := Subgroup.relIndex_mul_relIndex S (S ⊔ X) U le_sup_left (sup_le hSU hXU)
      rw [← this]
      exact Dvd.dvd.mul_right h2 _
    obtain ⟨L₁, hL₁⟩ := hSec.nonempty
    have hcov := cover_section_sup hn hset hSec le_rfl (inf_le_left : actE T A₀ J ≤ S) hXJ hSylX
      hL₁ (Or.inr ⟨z, hZ₀A hzZ, hzCV⟩)
      (fun L hL ⟨v, hv, s', hs', hvs⟩ => absurd (hcomm v ⟨hv.1.1, hv.1.2⟩ s'
        (hSec.SM.le_D L hL hs')) hvs)
    have hG₁ : T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A₀ K}, K ≤ G₁ :=
      sup_le hTG (iSup₂_le fun K hK => hmem K hK)
    exact hcov.trans (sup_le (Cov_mono J hG₁) hYCov)

end CFSG.Quasithin.RonanE111
