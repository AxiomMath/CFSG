module

public import CFSG.RankThree.S4Free.Stellmacher29
public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin Subgroup

universe u

section Transport

variable {V V' : Type*} [CommGroup V] [CommGroup V']

theorem fixV_map_congr (φ : V ≃* V') (B : Subgroup (MulAut V)) :
    fixV (B.map (MulAut.congr φ).toMonoidHom) = (fixV B).map φ.toMonoidHom := by
  ext v
  constructor
  · intro hv
    refine ⟨φ.symm v, fun b hb => φ.injective ?_, by simp⟩
    have := hv _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply] at this
    rw [this, MulEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hw b hb]

theorem isElemAbelian2_map_congr_iff (φ : V ≃* V') {B : Subgroup (MulAut V)} :
    IsElemAbelian2 (B.map (MulAut.congr φ).toMonoidHom) ↔ IsElemAbelian2 B := by
  have hinj : Function.Injective (MulAut.congr φ).toMonoidHom := (MulAut.congr φ).injective
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb => hinj ?_, fun a ha => hinj ?_⟩
    · rw [map_mul, map_mul]
      exact h1 _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    · rw [map_pow, map_one]
      exact h2 _ ⟨a, ha, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, h1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, h2 a ha, map_one]

variable [Finite V] [Finite V']

theorem agt_top_map_congr_iff (φ : V ≃* V') {T : Subgroup (MulAut V)} {e : ℚ} :
    AGt (T.map (MulAut.congr φ).toMonoidHom) ⊤ e ↔ AGt T ⊤ e := by
  set Φ := (MulAut.congr φ).toMonoidHom with hΦ
  have hinj : Function.Injective Φ := (MulAut.congr φ).injective
  have hsurj : Function.Surjective Φ := (MulAut.congr φ).surjective
  have hdim : ∀ B : Subgroup (MulAut V), dimOn (B.map Φ) ⊤ = dimOn B ⊤ := by
    intro B
    rw [dimOn_top, dimOn_top]
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have hcodim : ∀ B : Subgroup (MulAut V), codimOn (B.map Φ) ⊤ = codimOn B ⊤ := by
    intro B
    rw [codimOn_top, codimOn_top, hΦ, fixV_map_congr]
    unfold rkIdx
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  have hoff : ∀ B : Subgroup (MulAut V), IsOff (T.map Φ) (B.map Φ) ⊤ ↔ IsOff T B ⊤ := by
    intro B
    rw [isOff_top_iff, isOff_top_iff, IsA2, IsA2, Subgroup.map_le_map_iff_of_injective hinj,
      Ne, Ne, Subgroup.map_eq_bot_iff_of_injective B hinj, hΦ, isElemAbelian2_map_congr_iff]
  constructor
  · intro h B hB
    have := h _ ((hoff B).mpr hB)
    rwa [hdim, hcodim] at this
  · intro h B' hB'
    have hB'' : B' = (B'.comap Φ).map Φ :=
      (Subgroup.map_comap_eq_self_of_surjective hsurj B').symm
    rw [hB''] at hB' ⊢
    have := h _ ((hoff _).mp hB')
    rwa [hdim, hcodim]

end Transport

section Internal

open scoped IsMulCommutative

variable {G G' : Type*} [Group G] [Group G']

@[expose] noncomputable def subgroupOfMapEquiv {f : G →* G'} (hf : Function.Injective f)
    {U : Subgroup G}
    {Y : Subgroup G'} (hUY : U.map f ≤ Y) : U ≃* (U.map f).subgroupOf Y :=
  (U.equivMapOfInjective f hf).trans (Subgroup.subgroupOfEquivOfLe hUY).symm

theorem coe_subgroupOfMapEquiv_apply {f : G →* G'} (hf : Function.Injective f) {U : Subgroup G}
    {Y : Subgroup G'} (hUY : U.map f ≤ Y) (u : U) :
    (((subgroupOfMapEquiv hf hUY u : (U.map f).subgroupOf Y) : Y) : G') = f u := rfl

theorem conjAct_mem_stabSub_subgroupOf {f : G →* G'} {U : Subgroup G} {Y : Subgroup G'}
    [IsMulCommutative Y] {p : G} (hpU : p ∈ normalizer (U : Set G))
    (hpY : f p ∈ normalizer (Y : Set G')) :
    conjAct Y ⟨f p, hpY⟩ ∈ stabSub ((U.map f).subgroupOf Y) := by
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, AutOn.coe_conjAct_apply]
  constructor
  · rintro ⟨u, hu, hfu⟩
    refine ⟨p⁻¹ * u * p, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpU) u).mp hu
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hfu, map_inv]
      group
  · rintro ⟨u, hu, hfu⟩
    refine ⟨p * u * p⁻¹, (Subgroup.mem_normalizer_iff.mp hpU u).mp hu, ?_⟩
    rw [map_mul, map_mul, hfu, map_inv]

theorem autSub_autOn_map_eq {f : G →* G'} (hf : Function.Injective f) {P U : Subgroup G}
    {Y : Subgroup G'} [IsMulCommutative Y] (hPU : P ≤ normalizer (U : Set G))
    (hUY : U.map f ≤ Y) (hPY : P.map f ≤ normalizer (Y : Set G')) :
    autSub (autOn (P.map f) Y) ((U.map f).subgroupOf Y) =
      (autOn P U).map (MulAut.congr (subgroupOfMapEquiv hf hUY)).toMonoidHom := by
  set φ := subgroupOfMapEquiv hf hUY with hφ
  have key : ∀ (p : G) (hpU : p ∈ normalizer (U : Set G)) (hpY : f p ∈ normalizer (Y : Set G')),
      resHom ((U.map f).subgroupOf Y) ⟨conjAct Y ⟨f p, hpY⟩,
        conjAct_mem_stabSub_subgroupOf hpU hpY⟩ = MulAut.congr φ (conjAct U ⟨p, hpU⟩) := by
    intro p hpU hpY
    ext w
    have hw : f ((φ.symm w : U) : G) = ((w : Y) : G') := by
      have := coe_subgroupOfMapEquiv_apply hf hUY (φ.symm w)
      rw [← hφ, MulEquiv.apply_symm_apply] at this
      exact this.symm
    change ((conjAct Y ⟨f p, hpY⟩ (w : Y) : Y) : G') =
      ((φ (conjAct U ⟨p, hpU⟩ (φ.symm w)) : Y) : G')
    rw [AutOn.coe_conjAct_apply, hφ, coe_subgroupOfMapEquiv_apply, AutOn.coe_conjAct_apply,
      map_mul, map_mul, map_inv, ← hφ, hw]
  ext ψ
  constructor
  · intro hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ
    obtain ⟨n, hn, hng⟩ := AutOn.mem_autOn_iff.mp hg
    obtain ⟨p, hp, hpn⟩ := hn
    have hpY : f p ∈ normalizer (Y : Set G') := hPY ⟨p, hp, rfl⟩
    have hn' : n = ⟨f p, hpY⟩ := Subtype.ext hpn.symm
    subst hn'
    refine ⟨conjAct U ⟨p, hPU hp⟩, AutOn.conjAct_mem_autOn _ hp, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← key p (hPU hp) hpY]
    congr 1
    exact Subtype.ext hng
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hα
    have hpY : f n ∈ normalizer (Y : Set G') := hPY ⟨n, hn, rfl⟩
    refine mem_autSub.mpr ⟨⟨conjAct Y ⟨f n, hpY⟩, conjAct_mem_stabSub_subgroupOf n.2 hpY⟩,
      AutOn.conjAct_mem_autOn _ ⟨n, hn, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, key n n.2 hpY]

theorem agt_autOn_map_iff {f : G →* G'} (hf : Function.Injective f) {P U : Subgroup G}
    [IsMulCommutative U] [Finite U] {Y : Subgroup G'} [IsMulCommutative Y] [Finite Y]
    (hPU : P ≤ normalizer (U : Set G)) (hUY : U.map f ≤ Y)
    (hPY : P.map f ≤ normalizer (Y : Set G')) {e : ℚ} :
    AGt (autOn (P.map f) Y) ((U.map f).subgroupOf Y) e ↔ AGt (autOn P U) ⊤ e := by
  have hst : autOn (P.map f) Y ≤ stabSub ((U.map f).subgroupOf Y) := by
    intro g hg
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hg
    obtain ⟨p, hp, hpn⟩ := hn
    have hpY : f p ∈ normalizer (Y : Set G') := by rw [hpn]; exact n.2
    have := conjAct_mem_stabSub_subgroupOf (hPU hp) hpY
    rwa [show (⟨f p, hpY⟩ : normalizer (Y : Set G')) = n from Subtype.ext hpn] at this
  rw [← agt_autSub_iff hst le_rfl, Subgroup.subgroupOf_self, autSub_autOn_map_eq hf hPU hUY hPY,
    agt_top_map_congr_iff]

end Internal

section Internal29

open scoped IsMulCommutative

variable {G G' : Type*} [Group G] [Group G']

theorem holds_map {𝒦 : HostClass} (f : G →* G') {K : Subgroup G} (h : 𝒦.Holds K) :
    𝒦.Holds (K.map f) := by
  have hf : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact HostClass.Holds.of_mulEquiv ((QuotientGroup.quotientKerEquivRange _).trans
    (MulEquiv.subgroupCongr hf)) (h.quotient (f.comp K.subtype).ker)

theorem isSym3Free_map (f : G →* G') {K : Subgroup G} (h : IsSym3Free K) :
    IsSym3Free (K.map f) := by
  have hf : (f.comp K.subtype).range = K.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact IsSym3Free.of_mulEquiv ((QuotientGroup.quotientKerEquivRange _).trans
    (MulEquiv.subgroupCongr hf)) (h.quotient (f.comp K.subtype).ker)

theorem relIndex_map_dvd [Finite G] (f : G →* G') {S H : Subgroup G} (hSH : S ≤ H) :
    (S.map f).relIndex (H.map f) ∣ S.relIndex H := by
  have : Finite ↥(S.map f) := Finite.of_surjective _ (f.subgroupMap_surjective S)
  have : Finite ↥(H.map f) := Finite.of_surjective _ (f.subgroupMap_surjective H)
  have h1 := Subgroup.relIndex_mul_card (S.map f) (H.map f)
  rw [inf_eq_left.mpr (Subgroup.map_mono hSH)] at h1
  have h2 := Subgroup.relIndex_mul_card f.ker H
  rw [Subgroup.relIndex_ker] at h2
  have h3 := Subgroup.relIndex_mul_card f.ker S
  rw [Subgroup.relIndex_ker] at h3
  have h4 := Subgroup.relIndex_mul_card S H
  rw [inf_eq_left.mpr hSH] at h4
  have h5 := Subgroup.relIndex_mul_card (f.ker ⊓ S) (f.ker ⊓ H)
  rw [inf_eq_left.mpr (inf_le_inf_left _ hSH)] at h5
  refine ⟨(f.ker ⊓ S).relIndex (f.ker ⊓ H), ?_⟩
  have hpos : 0 < Nat.card ↥(S.map f) * Nat.card ↥(f.ker ⊓ S) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc S.relIndex H * (Nat.card ↥(S.map f) * Nat.card ↥(f.ker ⊓ S))
      = S.relIndex H * Nat.card S := by rw [h3]
    _ = Nat.card H := h4
    _ = Nat.card ↥(H.map f) * Nat.card ↥(f.ker ⊓ H) := h2.symm
    _ = (S.map f).relIndex (H.map f) * (f.ker ⊓ S).relIndex (f.ker ⊓ H) *
        (Nat.card ↥(S.map f) * Nat.card ↥(f.ker ⊓ S)) := by
      rw [← h1, ← h5]
      ring

theorem agt_autOn_of_agt {𝒦 : HostClass} (h24 : Hyp29.{u} 𝒦) {X : Type u} [Group X] [Finite X]
    {H S Y Z : Subgroup X} [IsMulCommutative Y] [IsMulCommutative Z]
    (hY2 : ∀ y ∈ Y, y ^ 2 = 1) (hH : 𝒦.Holds H) (hH3 : IsSym3Free H)
    (hHY : H ≤ normalizer (Y : Set X)) (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.relIndex H) (hZY : Z ≤ Y) (hSZ : S ≤ normalizer (Z : Set X))
    (hgen : ∀ W : Subgroup X, (∀ h ∈ H, Z.map (MulAut.conj h).toMonoidHom ≤ W) → Y ≤ W)
    (hZ : AGt (autOn S Z) ⊤ 1) : AGt (autOn S Y) ⊤ 1 := by
  have hHN : 𝒦.Holds (H.subgroupOf (normalizer (Y : Set X))) :=
    HostClass.Holds.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHY).symm hH
  have hHN3 : IsSym3Free (H.subgroupOf (normalizer (Y : Set X))) :=
    IsSym3Free.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHY).symm hH3
  have hset : Setting29 𝒦 (autOn H Y) (autOn S Y) (Z.subgroupOf Y) :=
    { sq := fun v => Subtype.ext (hY2 v v.2)
      holds := holds_map (conjAct Y) hHN
      sym3Free := isSym3Free_map (conjAct Y) hHN3
      le := AutOn.autOn_mono hSH
      isPGroup := AutOn.isPGroup_autOn hS
      not_dvd := by
        have h1 := relIndex_map_dvd (conjAct Y)
          (show S.subgroupOf (normalizer (Y : Set X)) ≤ H.subgroupOf (normalizer (Y : Set X)) from
            fun x hx => hSH hx)
        rw [Subgroup.relIndex_subgroupOf hHY] at h1
        exact fun h2 => hSi (h2.trans h1)
      stab := by
        intro φ hφ
        obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.mp hφ
        intro y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, AutOn.coe_conjAct_apply]
        constructor
        · intro hy
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSZ hn)) _).mp hy
          rwa [show (n : X)⁻¹ * ((n : X) * y * (n : X)⁻¹) * (n : X)⁻¹⁻¹ = y by group] at this
        · intro hy
          exact (Subgroup.mem_normalizer_iff.mp (hSZ hn) y).mp hy
      gen := by
        intro W hW
        have hle : Y ≤ W.map Y.subtype := by
          refine hgen _ fun h hh => ?_
          rintro _ ⟨z, hz, rfl⟩
          have h1 := hW (conjAct Y ⟨h, hHY hh⟩) (AutOn.conjAct_mem_autOn _ hh)
            ⟨⟨z, hZY hz⟩, show z ∈ Z from hz, rfl⟩
          exact ⟨_, h1, by simp [AutOn.coe_conjAct_apply]⟩
        intro y _
        obtain ⟨w, hw, hwy⟩ := hle y.2
        rwa [show w = y from Subtype.ext hwy] at hw }
  have hZ' : AGt (autOn S Y) (Z.subgroupOf Y) 1 := by
    have h := (agt_autOn_map_iff (f := MonoidHom.id X) (P := S) (U := Z) (Y := Y)
      Function.injective_id hSZ (by rwa [Subgroup.map_id])
      (by rw [Subgroup.map_id]; exact hSH.trans hHY)).mpr hZ
    rwa [Subgroup.map_id, Subgroup.map_id] at h
  rw [← not_ale_iff] at hZ' ⊢
  exact fun h => hZ' (ale_of_ale h24 hset h)

end Internal29

section ThreeOne

open scoped IsMulCommutative

variable {𝒦 : HostClass} {S : Type u} [Group S]

@[expose] def AGtOne (U : Subgroup S) : Prop :=
  U.Normal ∧ ∀ [IsMulCommutative U], AGt (autOn (⊤ : Subgroup S) U) ⊤ 1

theorem agtOne_omegaOneCenterOf : AGtOne (omegaOneCenterOf (⊤ : Subgroup S)) := by
  refine ⟨normal_omegaOneCenterOf' ⊤, fun B hB => ?_⟩
  exfalso
  apply hB.2.1
  have hc : (⊤ : Subgroup S) ≤ centralizer ((omegaOneCenterOf (⊤ : Subgroup S) : Subgroup S) :
      Set S) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' := (omegaOneCenterOf_le_centerOf (⊤ : Subgroup S) hu)
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu').2 g (Subgroup.mem_top g)).symm
  have hbot := AutOn.autOn_eq_bot_of_le_centralizer hc
  have : B = ⊥ := eq_bot_iff.mpr (hB.1.trans hbot.le)
  rw [this, B1.fixV_bot]

theorem AGtOne.step (h24 : Hyp29.{u} 𝒦) [Finite S] {U : Subgroup S} (hU : AGtOne U)
    (hUW : U ≤ stellW 𝒦 S) {X : Type u} [Group X] {ι : S →* X} (hι : F1Host 𝒦 ι) :
    AGtOne ((normalClosure ((U.map ι : Subgroup X) : Set X)).comap ι) := by
  have := hι.admissible.finite
  have hinj := hι.admissible.injective
  set K := normalClosure ((U.map ι : Subgroup X) : Set X) with hK
  have hKn : K.Normal := normalClosure_normal
  have hKW : K ≤ (stellW 𝒦 S).map ι := by
    have := stellW_normal hι
    exact normalClosure_le_normal (Subgroup.map_mono hUW)
  have hUK : U.map ι ≤ K := le_normalClosure
  have hWel : CFSG.Open.IsElemAbelian 2 ((stellW 𝒦 S).map ι) :=
    CFSG.RankThree.S4Free.isElemAbelian_map isElemAbelian_stellW ι
  have hKel : CFSG.Open.IsElemAbelian 2 K := isElemAbelian_of_le hWel hKW
  have hUel : CFSG.Open.IsElemAbelian 2 (U.map ι) := isElemAbelian_of_le hKel hUK
  have hUel' : CFSG.Open.IsElemAbelian 2 U :=
    isElemAbelian_of_le isElemAbelian_stellW hUW
  haveI : IsMulCommutative K := hKel.1
  haveI : IsMulCommutative (U.map ι) := hUel.1
  haveI : IsMulCommutative U := hUel'.1
  have hrange : K ≤ ι.range := hKW.trans (Subgroup.map_le_range _ _)
  have hKmap : (K.comap ι).map ι = K := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hrange]
  have hnorm : ∀ {T : Subgroup X}, T.Normal → (⊤ : Subgroup X) ≤ normalizer (T : Set X) :=
    fun hT x _ => by rw [normalizer_eq_top_iff.mpr hT]; exact Subgroup.mem_top x
  have hnormS : ∀ {T : Subgroup S}, T.Normal → (⊤ : Subgroup S) ≤ normalizer (T : Set S) :=
    fun hT x _ => by rw [normalizer_eq_top_iff.mpr hT]; exact Subgroup.mem_top x
  obtain ⟨P, hP⟩ := hι.admissible.sylow
  have hS2 : IsPGroup 2 ι.range := hP ▸ P.isPGroup'
  have hSi : ¬ 2 ∣ ι.range.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, ← hP]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact P.not_dvd_index
  refine ⟨hKn.comap ι, fun B hB => ?_⟩
  revert B
  change AGt (autOn (⊤ : Subgroup S) (K.comap ι)) ⊤ 1
  rw [← agt_autOn_map_iff (f := ι) (P := ⊤) (U := K.comap ι) (Y := K) hinj
    (hnormS (hKn.comap ι)) (by rw [hKmap]) ((le_top).trans (hnorm hKn)), hKmap,
    Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  refine agt_autOn_of_agt h24 (H := ⊤) (Z := U.map ι) hKel.2
    (HostClass.Holds.of_mulEquiv Subgroup.topEquiv.symm hι.holds)
    (IsSym3Free.of_mulEquiv Subgroup.topEquiv.symm hι.admissible.isSym3Free) (hnorm hKn) le_top
    hS2 hSi hUK (range_le_normalizer_map ι hU.1) ?_ ?_
  · intro W hW
    rw [hK, Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    exact hW c (Subgroup.mem_top c) ⟨a, ha, rfl⟩
  · have hN : (⊤ : Subgroup S).map ι ≤ normalizer ((U.map ι : Subgroup X) : Set X) := by
      rw [← MonoidHom.range_eq_map]
      exact range_le_normalizer_map ι hU.1
    have h := (agt_autOn_map_iff (f := ι) (P := ⊤) (U := U) (Y := U.map ι) hinj
      (hnormS hU.1) le_rfl hN).mpr hU.2
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h

theorem agtOne_stellW (h24 : Hyp29.{u} 𝒦) [Finite S] : AGtOne (stellW 𝒦 S) := by
  refine stellW_induction AGtOne agtOne_omegaOneCenterOf ?_
  intro U hP _ hUW X _ ι hι _
  exact hP.step h24 hUW hι

end ThreeOne

end CFSG.RankThree.S4Free.Stell
