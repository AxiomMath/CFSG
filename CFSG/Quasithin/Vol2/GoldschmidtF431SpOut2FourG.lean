module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Four

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Blueprint

universe u v

section CoreG

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T Sb N1 N2 : Subgroup Mb}
  {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

theorem F431SpOutCore.T_le_spN (O : F431SpOutCore T Sb f N1 N2 I) (j : Fin 2) :
    T ≤ spN N1 N2 j := by
  fin_cases j
  · exact O.T_le₁
  · exact O.T_le₂

theorem F431SpOutCore.spQ_le [Finite Mb] (O : F431SpOutCore T Sb f N1 N2 I) (j : Fin 2) :
    spQ N1 N2 j ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right O.sylow (O.T_le_spN j) le_top)

theorem F431SpOutCore.T_le_normalizer_spQ (O : F431SpOutCore T Sb f N1 N2 I) (j : Fin 2) :
    T ≤ Subgroup.normalizer (spQ N1 N2 j : Set Mb) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => pCoreOf_conj_mem (O.T_le_spN j ht) hx, fun hx => by
    have := pCoreOf_conj_mem ((spN N1 N2 j).inv_mem (O.T_le_spN j ht)) hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at this⟩

namespace SpGSetup

variable (S : SpGSetup N1 N2 b1 b2 M1 M2)

include S

theorem shapeAC [Finite Mb] (O : F431SpOutCore T Sb f N1 N2 I) :
    SpShapeA (subImg b1 T) (fun j => subImg b1 (spQ N1 N2 j)) where
  Q_le j := subImg_mono b1 (O.spQ_le j)
  Q_norm j := subImg_le_normalizer b1 (O.T_le_normalizer_spQ j)
  Q_abel j := by
    intro x hx y hy
    obtain ⟨x', hx'N, hx'Q, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy'N, hy'Q, rfl⟩ := mem_subImg.mp hy
    exact (commute_iff_of_injective S.comp.inj₁ hy'N hx'N).mpr (O.Q_abel j x' hx'Q y' hy'Q)
  Q_card := by
    have h1 : spQ N1 N2 1 ≤ N1 := (O.spQ_le 1).trans O.T_le₁
    have h0 : spQ N1 N2 0 ≤ N1 := (O.spQ_le 0).trans O.T_le₁
    show Nat.card (subImg b1 (spQ N1 N2 1)) = Nat.card (subImg b1 (spQ N1 N2 0))
    rw [card_subImg S.comp.inj₁ h1, card_subImg S.comp.inj₁ h0]
    exact O.Q_card
  A_eq := by
    intro A hAT hAab hcard
    obtain ⟨A', hA'T, rfl⟩ := exists_preimage S.comp.inj₁ hAT
    have hA'N : A' ≤ N1 := hA'T.trans O.T_le₁
    have hab' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
      intro x hx y hy
      have := hAab (b1 ⟨x, hA'N hx⟩) (mem_subImg_of_mem b1 (hA'N hx) hx) (b1 ⟨y, hA'N hy⟩)
        (mem_subImg_of_mem b1 (hA'N hy) hy)
      exact (commute_iff_of_injective S.comp.inj₁ (hA'N hy) (hA'N hx)).mp this
    have h0 : spQ N1 N2 0 ≤ N1 := (O.spQ_le 0).trans O.T_le₁
    have hcard' : Nat.card A' = Nat.card (spQ N1 N2 0) := by
      have := hcard
      change Nat.card (subImg b1 A') = Nat.card (subImg b1 (spQ N1 N2 0)) at this
      rwa [card_subImg S.comp.inj₁ hA'N, card_subImg S.comp.inj₁ h0] at this
    rcases O.A_eq A' hA'T hab' hcard' with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem normalizer_le_outC [Finite Mb] (O : F431SpOutCore T Sb f N1 N2 I) {n : G}
    (hn : n ∈ Subgroup.normalizer (subImg b1 T : Set G))
    (hS : IsSylowTwoOf (subImg b1 T) ⊤) : n ∈ M1 ∧ n ∈ M2 := by
  obtain ⟨hN0, hN1⟩ := S.normalizer_Q_of (O.Q_abel 0) (O.Q_abel 1)
    ((O.spQ_le 1).trans O.T_le₁)
  have h0 := (S.shapeAC O).normalizer_le hS hn 0
  have h1 := (S.shapeAC O).normalizer_le hS hn 1
  exact ⟨hN0 ▸ h0, hN1 ▸ h1⟩

end SpGSetup

theorem F431SpOutCore.exists_conj (O : F431SpOutCore T Sb f N1 N2 I)
    (C : F431Comp N1 N2 b1 b2) {x : Mb}
    (hx : x ∈ Sb) (hxo : orderOf x = 2) :
    ∃ i ∈ I, IsConj i x ∧ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 x) := by
  have hxN1 : x ∈ N1 := O.T_le₁ (O.S_le hx)
  have hxN2 : x ∈ N2 := O.T_le₂ (O.S_le hx)
  obtain ⟨i, hiI, ⟨m, hm, hmx⟩ | ⟨m, hm, hmx⟩⟩ := O.fusion x hx hxo
  · have hiN : i ∈ N1 := O.T_le₁ (mem_centerOf_iff.mp (O.I_center i hiI)).1
    refine ⟨i, hiI, isConj_iff.mpr ⟨m⁻¹, ?_⟩, ?_⟩
    · rw [← hmx]
      group
    · refine isConj_iff.mpr ⟨(b1 ⟨m, hm⟩)⁻¹, ?_⟩
      rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hxN1]
      have : (⟨i, hiN⟩ : ↥N1) = ⟨m, hm⟩ * ⟨x, hxN1⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext hmx.symm
      rw [this, map_mul, map_mul, map_inv]
      group
  · have hiN : i ∈ N2 := O.T_le₂ (mem_centerOf_iff.mp (O.I_center i hiI)).1
    refine ⟨i, hiI, isConj_iff.mpr ⟨m⁻¹, ?_⟩, ?_⟩
    · rw [← hmx]
      group
    · refine isConj_iff.mpr ⟨(b2 ⟨m, hm⟩)⁻¹, ?_⟩
      rw [amalgamMap_of_mem₂ b1 b2 C.agree hiN, amalgamMap_of_mem₂ b1 b2 C.agree hxN2]
      have : (⟨i, hiN⟩ : ↥N2) = ⟨m, hm⟩ * ⟨x, hxN2⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext hmx.symm
      rw [this, map_mul, map_mul, map_inv]
      group

theorem SpGSetup.sylow_outC (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOutCore T Sb f N1 N2 I) :
    IsSylowTwoOf (subImg b1 T) ⊤ :=
  isSylowTwoOf_image_of_odd_index S.comp S.range1 S.range2 O.sylow O.T_le₁ O.T_le₂ S.odd

theorem SpGSetup.not_conj_outC [Finite Mb] [Finite G] (S : SpGSetup N1 N2 b1 b2 M1 M2)
    (O : F431SpOutCore T Sb f N1 N2 I) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j) := by
  intro i hi j hj hij hconj
  have hiT : i ∈ T := (mem_centerOf_iff.mp (O.I_center i hi)).1
  have hjT : j ∈ T := (mem_centerOf_iff.mp (O.I_center j hj)).1
  have hiN : i ∈ N1 := O.T_le₁ hiT
  have hjN : j ∈ N1 := O.T_le₁ hjT
  rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hjN] at hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hu : b1 ⟨i, hiN⟩ ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ O.T_le₁]
    exact mem_subImg_of_mem b1 hiN (O.I_center i hi)
  have hv : b1 ⟨j, hjN⟩ ∈ centerOf (subImg b1 T) := by
    rw [subImg_centerOf S.comp.inj₁ O.T_le₁]
    exact mem_subImg_of_mem b1 hjN (O.I_center j hj)
  obtain ⟨n, hn, hnuv⟩ := exists_normalizer_conj_of_central (S.sylow_outC O) hu hv hg
  obtain ⟨hn1, hn2⟩ := S.normalizer_le_outC O hn (S.sylow_outC O)
  obtain ⟨n', h1', h2', hn'⟩ := S.inter n hn1 hn2
  have hconj' : n' * i * n'⁻¹ = j := by
    have e : (⟨n' * i * n'⁻¹, N1.mul_mem (N1.mul_mem h1' hiN) (N1.inv_mem h1')⟩ : ↥N1) =
        ⟨j, hjN⟩ := by
      apply S.comp.inj₁
      have : (⟨n' * i * n'⁻¹, N1.mul_mem (N1.mul_mem h1' hiN) (N1.inv_mem h1')⟩ : ↥N1) =
          ⟨n', h1'⟩ * ⟨i, hiN⟩ * ⟨n', h1'⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hn', hnuv]
    exact congrArg Subtype.val e
  obtain ⟨w, ⟨hwI, hw⟩, huniq⟩ := O.rep i (O.I_le_S i hi) (O.order_two i hi)
  have h1 : j = w := huniq j ⟨hj, isConj_iff.mpr ⟨n'⁻¹, by rw [← hconj']; group⟩⟩
  have h2 : i = w := huniq i ⟨hi, IsConj.refl i⟩
  exact hij (h2.trans h1.symm)
omit [Group Mb] in
theorem conj_mem_centerOf_of_normalizer {X : Subgroup G} {n u : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) (hu : u ∈ centerOf X) :
    n * u * n⁻¹ ∈ centerOf X := by
  obtain hu1 := mem_centerOf_iff.mp hu
  have hnX := Subgroup.mem_normalizer_iff.mp hn
  rw [mem_centerOf_iff]
  refine ⟨(hnX u).mp hu1.1, fun t ht => ?_⟩
  have ht' : n⁻¹ * t * n ∈ X := by
    refine (hnX (n⁻¹ * t * n)).mpr ?_
    rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group]
    exact ht
  have := hu1.2 _ ht'
  calc t * (n * u * n⁻¹) = n * ((n⁻¹ * t * n) * u) * n⁻¹ := by group
    _ = n * (u * (n⁻¹ * t * n)) * n⁻¹ := by rw [this]
    _ = n * u * n⁻¹ * t := by group

omit [Group Mb] in
theorem mem_of_normalizes_sylow [Finite G] {Tf K₀ : Subgroup G} (hTf : IsSylowTwoOf Tf K₀) {x : G}
    (hxK : x ∈ K₀) (hxN : x ∈ Subgroup.normalizer (Tf : Set G))
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ Tf := by
  have hZN : Subgroup.zpowers x ≤ Subgroup.normalizer (Tf : Set G) := Subgroup.zpowers_le.mpr hxN
  have hp : IsPGroup 2 (Subgroup.zpowers x ⊔ Tf : Subgroup G) :=
    CFSG.QuasithinUnique.Lin2.isPGroup_sup_of_le_normalizer hZN hx2 hTf.2.1
  have hle : (Subgroup.zpowers x ⊔ Tf : Subgroup G) ≤ K₀ :=
    sup_le (Subgroup.zpowers_le.mpr hxK) hTf.le
  have hcard : Nat.card (Subgroup.zpowers x ⊔ Tf : Subgroup G) ≤ Nat.card Tf := by
    rw [hTf.card_eq]
    exact card_le_twoPart hle hp
  have heq : Tf = Subgroup.zpowers x ⊔ Tf := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)

theorem sylow_Tf_in_M [Finite Mb] [Finite G] {N : Subgroup Mb} {b : ↥N →* G}
    (hb : Function.Injective b) {M : Subgroup G} (hrange : b.range = M) {T : Subgroup Mb}
    {f : Mb} (hTN : T ≤ N) (hf : f ∈ T)
    (hSylTf : IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ N)) :
    IsSylowTwoOf (subImg b (spTf T f))
      (M ⊓ Subgroup.centralizer ({b ⟨f, hTN hf⟩} : Set G)) := by
  have hTfN : spTf T f ≤ N := inf_le_left.trans hTN
  have hfN : f ∈ N := hTN hf
  set fg : G := b ⟨f, hfN⟩ with hfg
  have himg : subImg b (Subgroup.centralizer ({f} : Set Mb) ⊓ N) =
      M ⊓ Subgroup.centralizer ({fg} : Set G) := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hxN, ⟨hxC, -⟩, rfl⟩ := mem_subImg.mp hg
      refine ⟨hrange ▸ ⟨⟨x, hxN⟩, rfl⟩, ?_⟩
      show b ⟨x, hxN⟩ ∈ Subgroup.centralizer ({fg} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_iff_of_injective hb hfN hxN).mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    · rintro ⟨hgM, hgC⟩
      obtain ⟨⟨y, hyN⟩, rfl⟩ : g ∈ b.range := hrange ▸ hgM
      refine mem_subImg.mpr ⟨y, hyN, ⟨?_, hyN⟩, rfl⟩
      show y ∈ Subgroup.centralizer ({f} : Set Mb)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_iff_of_injective hb hfN hyN).mp (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  rw [← himg]
  exact isSylowTwoOf_subImg hb (fun x hx => ⟨hx.2, hTfN hx⟩) inf_le_right hSylTf

theorem SpGSetup.sylow_Tf_four [Finite Mb] [Finite G] {i0 i1 : Mb}
    (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut4 T Sb f N1 N2 I i0 i1) :
    IsSylowTwoOf (subImg b1 (spTf T f))
      (Subgroup.centralizer ({b1 ⟨f, O.core.T_le₁ O.core.f_mem⟩} : Set G)) := by
  have hC := O.core
  have hfT := hC.f_mem
  have hfN1 : f ∈ N1 := hC.T_le₁ hfT
  have hfN2 : f ∈ N2 := hC.T_le₂ hfT
  have hTf1 : spTf T f ≤ N1 := inf_le_left.trans hC.T_le₁
  have hTf2 : spTf T f ≤ N2 := inf_le_left.trans hC.T_le₂
  have hb := S.comp.inj₁
  have hnf := S.not_conj_outC hC
  set fg : G := b1 ⟨f, hfN1⟩ with hfg
  set B : Subgroup G := subImg b1 (spTf T f) with hB
  have hsyl1 : IsSylowTwoOf B (M1 ⊓ Subgroup.centralizer ({fg} : Set G)) :=
    sylow_Tf_in_M hb S.range1 hC.T_le₁ hfT (hC.Sylow_Tf 0)
  have hsyl2 : IsSylowTwoOf B (M2 ⊓ Subgroup.centralizer ({fg} : Set G)) := by
    have h := sylow_Tf_in_M S.comp.inj₂ S.range2 hC.T_le₂ hfT (hC.Sylow_Tf 1)
    have e : subImg b2 (spTf T f) = subImg b1 (spTf T f) :=
      (subImg_eq_of_agree S.comp.agree hTf1 hTf2).symm
    have e' : b2 ⟨f, hfN2⟩ = b1 ⟨f, hfN1⟩ := (S.comp.agree f hfN1 hfN2).symm
    rw [e, e'] at h
    exact h
  have hβ1 : ∀ r ∈ I, r ∈ N1 := fun r hr => hC.T_le₁ (mem_centerOf_iff.mp (hC.I_center r hr)).1
  have hβa : ∀ (r : Mb) (hr : r ∈ N1), amalgamMap b1 b2 r = b1 ⟨r, hr⟩ := fun r hr =>
    amalgamMap_of_mem₁ b1 b2 hr
  have hff : f * f = 1 := by rw [← sq]; exact hC.f_sq
  have key : ∀ x : G, x ∈ Subgroup.centralizer ({fg} : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) → ∀ r ∈ I,
      x * amalgamMap b1 b2 r * x⁻¹ ≠ amalgamMap b1 b2 r →
      IsConj (amalgamMap b1 b2 r) fg := by
    intro x hxC hxN r hr hmove
    have hrN1 : r ∈ N1 := hβ1 r hr
    have hrT : r ∈ T := (mem_centerOf_iff.mp (hC.I_center r hr)).1
    have hrZ : r ∈ centerOf (spTf T f) := by
      rw [mem_centerOf_iff]
      refine ⟨⟨hrT, ?_⟩, fun t ht => (mem_centerOf_iff.mp (hC.I_center r hr)).2 t ht.1⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact ((mem_centerOf_iff.mp (hC.I_center r hr)).2 f hfT).symm
    have hβrZ : amalgamMap b1 b2 r ∈ centerOf B := by
      rw [hB, subImg_centerOf hb hTf1, hβa r hrN1]
      exact mem_subImg_of_mem b1 hrN1 hrZ
    have hwZ : x * amalgamMap b1 b2 r * x⁻¹ ∈ centerOf B :=
      conj_mem_centerOf_of_normalizer hxN hβrZ
    rw [hB, subImg_centerOf hb hTf1] at hwZ
    obtain ⟨z, hzN, hzZ, hzw⟩ := mem_subImg.mp hwZ
    have hconj : IsConj (amalgamMap b1 b2 r) (b1 ⟨z, hzN⟩) := isConj_iff.mpr ⟨x, hzw.symm⟩
    rcases O.Zf z hzZ with (h1 | hzI) | (h2 | hfzI)
    · exfalso
      subst h1
      have hw : x * amalgamMap b1 b2 r * x⁻¹ = 1 := by rw [← hzw]; exact map_one b1
      have hr1 : amalgamMap b1 b2 r = 1 := by
        calc amalgamMap b1 b2 r = x⁻¹ * (x * amalgamMap b1 b2 r * x⁻¹) * x := by group
          _ = 1 := by rw [hw]; group
      rw [hβa r hrN1] at hr1
      have hr1' : r = 1 := congrArg Subtype.val (hb (hr1.trans (map_one b1).symm))
      have := hC.order_two r hr
      rw [hr1', orderOf_one] at this
      exact absurd this (by norm_num)
    · by_cases hzr : z = r
      · exfalso
        subst hzr
        apply hmove
        rw [← hzw, hβa z hzN]
      · exfalso
        apply hnf r hr z hzI (Ne.symm hzr)
        rw [hβa z hzN]
        exact hconj
    · exfalso
      have hzf : z = f := by
        have : z = f⁻¹ := eq_inv_of_mul_eq_one_right h2
        rw [this]
        exact inv_eq_of_mul_eq_one_right hff
      subst hzf
      have hxf : x * fg * x⁻¹ = fg := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hxC
        calc x * fg * x⁻¹ = fg * x * x⁻¹ := by rw [this]
          _ = fg := by group
      have h3 : amalgamMap b1 b2 r = fg := by
        have e1 : x * amalgamMap b1 b2 r * x⁻¹ = fg := by rw [← hzw]
        calc amalgamMap b1 b2 r = x⁻¹ * (x * amalgamMap b1 b2 r * x⁻¹) * x := by group
          _ = x⁻¹ * fg * x := by rw [e1]
          _ = x⁻¹ * (x * fg * x⁻¹) * x := by rw [hxf]
          _ = fg := by group
      have hrf : r = z := by
        have : b1 ⟨r, hrN1⟩ = b1 ⟨z, hfN1⟩ := by rw [← hβa r hrN1]; exact h3
        exact congrArg Subtype.val (hb this)
      exact hC.f_not (hrf ▸ hC.I_le_S r hr)
    · obtain ⟨t, htT, htk⟩ := O.fconj _ hfzI
      have htN1 : t ∈ N1 := hC.T_le₁ htT
      have hz' : z = t * f * t⁻¹ := by
        rw [htk, ← mul_assoc, hff, one_mul]
      have hzeq : (⟨z, hzN⟩ : ↥N1) = ⟨t, htN1⟩ * ⟨f, hfN1⟩ * ⟨t, htN1⟩⁻¹ := by
        apply Subtype.ext
        exact hz'
      have hw : b1 ⟨z, hzN⟩ = b1 ⟨t, htN1⟩ * fg * (b1 ⟨t, htN1⟩)⁻¹ := by
        rw [hzeq, map_mul, map_mul, map_inv]
      refine hconj.trans (isConj_iff.mpr ⟨(b1 ⟨t, htN1⟩)⁻¹, ?_⟩)
      rw [hw]
      group
  obtain ⟨R, hBR, hR⟩ := exists_isSylowTwoOf_of_le (hsyl1.le.trans inf_le_right) hsyl1.2.1
  have hRB : R = B := by
    by_contra hne
    obtain ⟨x, hxR, hxN, hxB⟩ := exists_mem_normalizer_not_mem hR.isPGroup hBR (Ne.symm hne)
    have hxC : x ∈ Subgroup.centralizer ({fg} : Set G) := hR.le hxR
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
      hR.isPGroup.to_le (Subgroup.zpowers_le.mpr hxR)
    have hi0I := O.i0_mem
    have hi1I := O.i1_mem
    have hi0N : i0 ∈ N1 := hβ1 i0 hi0I
    have hi1N : i1 ∈ N1 := hβ1 i1 hi1I
    have hi1N2 : i1 ∈ N2 := hC.T_le₂ (mem_centerOf_iff.mp (hC.I_center i1 hi1I)).1
    by_cases c0 : x * amalgamMap b1 b2 i0 * x⁻¹ = amalgamMap b1 b2 i0
    · have hz0 : b1 ⟨i0, hi0N⟩ ∈ centerOf (perfectCore M1) :=
        map_mem_centerOf_perfectCore hb S.range1 hi0N O.i0_Z
      have hxcent : x ∈ Subgroup.centralizer ({b1 ⟨i0, hi0N⟩} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hβa i0 hi0N] at c0
        calc x * b1 ⟨i0, hi0N⟩ = x * b1 ⟨i0, hi0N⟩ * x⁻¹ * x := by group
          _ = b1 ⟨i0, hi0N⟩ * x := by rw [c0]
      have hxM1 : x ∈ M1 :=
        S.cent1 _ hz0 ((orderOf_img hb hi0N).trans (hC.order_two i0 hi0I)) hxcent
      exact hxB (mem_of_normalizes_sylow hsyl1 ⟨hxM1, hxC⟩ hxN hx2)
    by_cases c1 : x * amalgamMap b1 b2 i1 * x⁻¹ = amalgamMap b1 b2 i1
    · have hz1 : b2 ⟨i1, hi1N2⟩ ∈ centerOf (perfectCore M2) :=
        map_mem_centerOf_perfectCore S.comp.inj₂ S.range2 hi1N2 O.i1_Z
      have hxcent : x ∈ Subgroup.centralizer ({b2 ⟨i1, hi1N2⟩} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [amalgamMap_of_mem₂ b1 b2 S.comp.agree hi1N2] at c1
        calc x * b2 ⟨i1, hi1N2⟩ = x * b2 ⟨i1, hi1N2⟩ * x⁻¹ * x := by group
          _ = b2 ⟨i1, hi1N2⟩ * x := by rw [c1]
      have hxM2 : x ∈ M2 :=
        S.cent2 _ hz1 ((orderOf_img S.comp.inj₂ hi1N2).trans (hC.order_two i1 hi1I)) hxcent
      exact hxB (mem_of_normalizes_sylow hsyl2 ⟨hxM2, hxC⟩ hxN hx2)
    exact hnf i0 hi0I i1 hi1I O.i0_ne ((key x hxC hxN i0 hi0I c0).trans
      (key x hxC hxN i1 hi1I c1).symm)
  rw [hRB] at hR
  exact hR

theorem SpGSetup.out_false4 [Finite Mb] [Finite G] [IsSimpleGroup G] {i0 i1 : Mb}
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut4 T Sb f N1 N2 I i0 i1) : False := by
  have hC := O.core
  have hfT := hC.f_mem
  have hfN1 : f ∈ N1 := hC.T_le₁ hfT
  have hSyl := S.sylow_outC hC
  have hTf1 : spTf T f ≤ N1 := inf_le_left.trans hC.T_le₁
  have hTfSyl : IsSylowTwoOf (subImg b1 (spTf T f))
      (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := S.sylow_Tf_four O
  have hb := S.comp.inj₁
  have hSN1 : Sb ≤ N1 := hC.S_le.trans hC.T_le₁
  obtain ⟨t₀, ht₀⟩ := hC.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N1 := hC.T_le₁ ht₀T
  have hcyc : subImg b1 T = subImg b1 Sb ⊔ Subgroup.zpowers (b1 ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN1 (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.transfer_contradiction_cyclic hnab hSyl
    (subImg_mono b1 hC.S_le) (subImg_le_normalizer b1 hC.S_norm) hcyc
    (mem_subImg_of_mem b1 hfN1 hfT)
    (fun h => hC.f_not ((mem_subImg_iff_of_injective hb hfN1).mp h))
    ((sq_eq_one_iff_of_injective hb hfN1).mpr hC.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => hC.f_not (h ▸ Sb.one_mem)
  have hfg2 : b1 ⟨f, hfN1⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN1).mpr hC.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b1 ⟨f, hfN1⟩ * g) ^ 2 = g⁻¹ * b1 ⟨f, hfN1⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b1 ⟨1, hsN⟩ = 1 := map_one b1
    rw [h1] at hs
    have : b1 ⟨f, hfN1⟩ = 1 := by
      calc b1 ⟨f, hfN1⟩ = g * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b1).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hiI, -, hiφ⟩ := hC.exists_conj S.comp hsS hso
  have hiT : i ∈ T := (mem_centerOf_iff.mp (hC.I_center i hiI)).1
  have hiN : i ∈ N1 := hC.T_le₁ hiT
  rw [amalgamMap_of_mem₁ b1 b2 hiN, amalgamMap_of_mem₁ b1 b2 hsN] at hiφ
  obtain ⟨c, hc⟩ := isConj_iff.mp hiφ
  set u : G := b1 ⟨i, hiN⟩ with hu
  have hfu : (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = u := by
    have h1 : c * u * c⁻¹ = g⁻¹ * b1 ⟨f, hfN1⟩ * g := hc.trans hs
    calc (g * c)⁻¹ * b1 ⟨f, hfN1⟩ * (g * c)⁻¹⁻¹ = c⁻¹ * (g⁻¹ * b1 ⟨f, hfN1⟩ * g) * c := by group
      _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [h1]
      _ = u := by group
  have hTg_le : subImg b1 T ≤ Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, htT, rfl⟩ := mem_subImg.mp hy
    show b1 ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr
      ((mem_centerOf_iff.mp (hC.I_center i hiI)).2 t htT)
  have h1 : Nat.card (subImg b1 T) ≤ twoPart (Subgroup.centralizer ({u} : Set G)) :=
    card_le_twoPart hTg_le hSyl.2.1
  have h2 : twoPart (Subgroup.centralizer ({u} : Set G)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b1 (spTf T f)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card T := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hC.f_not_central ?_)
    rw [mem_centerOf_iff]
    refine ⟨hfT, fun t ht => ?_⟩
    have : t ∈ spTf T f := by
      rw [h]
      exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  rw [card_subImg hb hC.T_le₁] at h1
  rw [card_subImg hb hTf1] at h3
  omega

theorem f431Out_four_of_lie : F431Out .PSp 2 2 := by
  have hLie := f431SpOut4Lie
  intro G _ _ hG hnab M1 M2 hyps D _ hD E
  by_contra hodd
  have : IsSimpleGroup G := hG
  have : Finite D := finite_of_lieModel_psp hD
  have : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite ↥E.K := inferInstance
  obtain ⟨T, Sb, g, I, i0, i1, O⟩ := hLie D hD E.toLieAmalgamExt hodd
  have ha := hyps.2.1 (Or.inl rfl)
  have hb := hyps.2.2.2.1 (by simp)
  have hd := hyps.2.2.2.2 rfl
  have S : SpGSetup E.Mb1 E.Mb2 E.b1 E.b2 M1 M2 :=
    ⟨E.comp, E.range_b1, E.range_b2, E.inter_mem, ha.1, ha.2, hb.1, hb.2, hd.1, hd.2⟩
  exact S.out_false4 hnab O

end CoreG

end CFSG.Quasithin.H13.F431
