module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutAbs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLocal

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Blueprint

universe u v

section Transport

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {N : Subgroup Mb} {b : ↥N →* G}

theorem card_subImg (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) :
    Nat.card (subImg b X) = Nat.card X := by
  have hf : Function.Injective (b.comp (Subgroup.inclusion hX)) :=
    hb.comp (Subgroup.inclusion_injective hX)
  rw [subImg_eq_range hX]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem exists_preimage (hb : Function.Injective b) {Y : Subgroup Mb} {A : Subgroup G}
    (hA : A ≤ subImg b Y) : ∃ A' : Subgroup Mb, A' ≤ Y ∧ subImg b A' = A := by
  refine ⟨(A.comap b).map N.subtype, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hxN, hxY, hx⟩ := mem_subImg.mp (hA hy)
    have : y = ⟨x, hxN⟩ := hb hx.symm
    rw [this]
    exact hxY
  · ext g
    constructor
    · intro hg
      obtain ⟨x, hxN, ⟨y, hy, rfl⟩, rfl⟩ := mem_subImg.mp hg
      exact hy
    · intro hg
      obtain ⟨x, hxN, hxY, rfl⟩ := mem_subImg.mp (hA hg)
      exact mem_subImg.mpr ⟨x, hxN, ⟨⟨x, hxN⟩, hg, rfl⟩, rfl⟩

theorem subImg_inf (hb : Function.Injective b) {X Y : Subgroup Mb} :
    subImg b (X ⊓ Y) = subImg b X ⊓ subImg b Y := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hxN, ⟨hxX, hxY⟩, rfl⟩ := mem_subImg.mp hg
    exact ⟨mem_subImg_of_mem b hxN hxX, mem_subImg_of_mem b hxN hxY⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_subImg.mp h1
    refine mem_subImg.mpr ⟨x, hxN, ⟨hxX, ?_⟩, rfl⟩
    exact (mem_subImg_iff_of_injective hb hxN).mp h2

theorem subImg_derivedSeriesOf {X : Subgroup Mb} (hX : X ≤ N) (n : ℕ) :
    derivedSeriesOf (subImg b X) n = subImg b (derivedSeriesOf X n) := by
  have hr : subImg b X = (b.comp (Subgroup.inclusion hX)).range := subImg_eq_range hX
  ext g
  rw [hr, derivedSeriesOf_range]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine mem_subImg.mpr ⟨d.1, hX d.2, ?_, rfl⟩
    rw [derivedSeriesOf_eq_map_derivedSeries]
    exact ⟨d, hd, rfl⟩
  · intro hg
    obtain ⟨x, hxN, hxd, rfl⟩ := mem_subImg.mp hg
    rw [derivedSeriesOf_eq_map_derivedSeries] at hxd
    obtain ⟨d, hd, rfl⟩ := hxd
    exact ⟨d, hd, rfl⟩

theorem subImg_commutator {X : Subgroup Mb} (hX : X ≤ N) :
    ⁅subImg b X, subImg b X⁆ = subImg b ⁅X, X⁆ :=
  subImg_derivedSeriesOf hX 1

theorem subImg_zpowers {x : Mb} (hx : x ∈ N) :
    subImg b (Subgroup.zpowers x) = Subgroup.zpowers (b ⟨x, hx⟩) := by
  ext g
  rw [mem_subImg, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨y, hyN, hy, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨k, by
      have : (⟨x ^ k, hyN⟩ : ↥N) = ⟨x, hx⟩ ^ k := Subtype.ext (by simp)
      rw [this, map_zpow]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨x ^ k, N.zpow_mem hx k, Subgroup.zpow_mem_zpowers x k, ?_⟩
    have : (⟨x ^ k, N.zpow_mem hx k⟩ : ↥N) = ⟨x, hx⟩ ^ k := Subtype.ext (by simp)
    rw [this, map_zpow]

theorem subImg_sup {X Y : Subgroup Mb} (hX : X ≤ N) (hY : Y ≤ N) :
    subImg b (X ⊔ Y) = subImg b X ⊔ subImg b Y := by
  unfold subImg
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem isSylowTwoOf_subImg [Finite Mb] [Finite G] (hb : Function.Injective b)
    {X Y : Subgroup Mb} (hXY : X ≤ Y) (hY : Y ≤ N) (h : IsSylowTwoOf X Y) :
    IsSylowTwoOf (subImg b X) (subImg b Y) := by
  rw [isSylowTwoOf_iff] at h ⊢
  obtain ⟨-, hp, hc⟩ := h
  refine ⟨subImg_mono b hXY, ?_, ?_⟩
  · let e : ↥X ≃* ↥(subImg b X) :=
      (Subgroup.subgroupOfEquivOfLe (hXY.trans hY)).symm.trans
        (Subgroup.equivMapOfInjective _ b hb)
    exact hp.of_equiv e
  · rw [card_subImg hb (hXY.trans hY), hc]
    unfold twoPart
    rw [card_subImg hb hY]

end Transport

section Shape

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T Sb N1 N2 : Subgroup Mb}
  {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

theorem F431SpOut.T_le_spN (O : F431SpOut T Sb f N1 N2 I) (j : Fin 2) : T ≤ spN N1 N2 j := by
  fin_cases j
  · exact O.T_le₁
  · exact O.T_le₂

theorem F431SpOut.spQ_le [Finite Mb] (O : F431SpOut T Sb f N1 N2 I) (j : Fin 2) :
    spQ N1 N2 j ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le (F7.isSylowTwoOf_mono_right O.sylow (O.T_le_spN j) le_top)

theorem F431SpOut.T_le_normalizer_spQ (O : F431SpOut T Sb f N1 N2 I) (j : Fin 2) :
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

theorem normalizer_Q_of (habel0 : ∀ x ∈ pCoreOf 2 N1, ∀ y ∈ pCoreOf 2 N1, x * y = y * x)
    (habel1 : ∀ x ∈ pCoreOf 2 N2, ∀ y ∈ pCoreOf 2 N2, x * y = y * x)
    (hQ : pCoreOf 2 N2 ≤ N1) :
    Subgroup.normalizer (subImg b1 (pCoreOf 2 N1) : Set G) = M1 ∧
      Subgroup.normalizer (subImg b1 (pCoreOf 2 N2) : Set G) = M2 := by
  have h1 : centerOf (pCoreOf 2 M1) = subImg b1 (pCoreOf 2 N1) := by
    have := S.range1
    subst this
    rw [← subImg_self b1, subImg_pCoreOf S.comp.inj₁ le_rfl,
      subImg_centerOf S.comp.inj₁ (LieType.BorelTits.pCoreOf_le 2 N1),
      centerOf_eq_of_abelian habel0]
  have h2 : centerOf (pCoreOf 2 M2) = subImg b1 (pCoreOf 2 N2) := by
    have h2' : centerOf (pCoreOf 2 M2) = subImg b2 (pCoreOf 2 N2) := by
      have := S.range2
      subst this
      rw [← subImg_self b2, subImg_pCoreOf S.comp.inj₂ le_rfl,
        subImg_centerOf S.comp.inj₂ (LieType.BorelTits.pCoreOf_le 2 N2),
        centerOf_eq_of_abelian habel1]
    rw [h2']
    exact (subImg_eq_of_agree S.comp.agree hQ (LieType.BorelTits.pCoreOf_le 2 N2)).symm
  exact ⟨h1 ▸ S.normalizer1, h2 ▸ S.normalizer2⟩

theorem shapeA [Finite Mb] (O : F431SpOut T Sb f N1 N2 I) :
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

theorem normalizer_le_out [Finite Mb] (O : F431SpOut T Sb f N1 N2 I) {n : G}
    (hn : n ∈ Subgroup.normalizer (subImg b1 T : Set G))
    (hS : IsSylowTwoOf (subImg b1 T) ⊤) : n ∈ M1 ∧ n ∈ M2 := by
  obtain ⟨hN0, hN1⟩ := S.normalizer_Q_of (O.Q_abel 0) (O.Q_abel 1)
    ((O.spQ_le 1).trans O.T_le₁)
  have h0 := (S.shapeA O).normalizer_le hS hn 0
  have h1 := (S.shapeA O).normalizer_le hS hn 1
  exact ⟨hN0 ▸ h0, hN1 ▸ h1⟩

end SpGSetup

end Shape

section F435

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T Sb N1 N2 : Subgroup Mb}
  {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

theorem F431SpOut.exists_conj (O : F431SpOut T Sb f N1 N2 I) (C : F431Comp N1 N2 b1 b2) {x : Mb}
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

theorem F431SpOut.lemma_F435 (O : F431SpOut T Sb f N1 N2 I) (C : F431Comp N1 N2 b1 b2)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    {x y : Mb} (hx : x ∈ Sb) (hy : y ∈ Sb) (hxo : orderOf x = 2) (hyo : orderOf y = 2) :
    IsConj x y ↔ IsConj (amalgamMap b1 b2 x) (amalgamMap b1 b2 y) := by
  obtain ⟨i₀, hi₀I, hi₀c, hi₀φ⟩ := O.exists_conj C hx hxo
  obtain ⟨j₀, hj₀I, hj₀c, hj₀φ⟩ := O.exists_conj C hy hyo
  constructor
  · intro h
    have h1 : IsConj i₀ j₀ := (hi₀c.trans h).trans hj₀c.symm
    have hij : j₀ = i₀ := by
      obtain ⟨w, -, huniq⟩ := O.rep i₀ (O.I_le_S i₀ hi₀I) (O.order_two i₀ hi₀I)
      exact (huniq j₀ ⟨hj₀I, h1.symm⟩).trans (huniq i₀ ⟨hi₀I, IsConj.refl i₀⟩).symm
    rw [hij] at hj₀φ
    exact hi₀φ.symm.trans hj₀φ
  · intro h
    have h1 : IsConj (amalgamMap b1 b2 i₀) (amalgamMap b1 b2 j₀) :=
      (hi₀φ.trans h).trans hj₀φ.symm
    have hij : i₀ = j₀ := by
      by_contra hne
      exact hnf i₀ hi₀I j₀ hj₀I hne h1
    rw [hij] at hi₀c
    exact hi₀c.symm.trans hj₀c

end F435

section ClaimA

variable {Mb : Type u} [Group Mb] {G : Type v} [Group G] {T Sb N1 N2 : Subgroup Mb}
  {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G} {M1 M2 : Subgroup G}

theorem SpGSetup.sylow_out (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut T Sb f N1 N2 I) :
    IsSylowTwoOf (subImg b1 T) ⊤ :=
  isSylowTwoOf_image_of_odd_index S.comp S.range1 S.range2 O.sylow O.T_le₁ O.T_le₂ S.odd

theorem SpGSetup.not_conj_out [Finite Mb] [Finite G] (S : SpGSetup N1 N2 b1 b2 M1 M2)
    (O : F431SpOut T Sb f N1 N2 I) :
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
  obtain ⟨n, hn, hnuv⟩ := exists_normalizer_conj_of_central (S.sylow_out O) hu hv hg
  obtain ⟨hn1, hn2⟩ := S.normalizer_le_out O hn (S.sylow_out O)
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
theorem conj_mem_Wg {X : Subgroup G} {n u : G} (hn : n ∈ Subgroup.normalizer (X : Set G))
    (hu : u ∈ centerOf X ⊓ ⁅X, X⁆) : n * u * n⁻¹ ∈ centerOf X ⊓ ⁅X, X⁆ := by
  obtain ⟨hu1, hu2⟩ := hu
  have hnX := Subgroup.mem_normalizer_iff.mp hn
  refine ⟨?_, ?_⟩
  · have hu1' := mem_centerOf_iff.mp hu1
    show n * u * n⁻¹ ∈ centerOf X
    rw [mem_centerOf_iff]
    refine ⟨(hnX u).mp hu1'.1, fun t ht => ?_⟩
    have ht' : n⁻¹ * t * n ∈ X := by
      refine (hnX (n⁻¹ * t * n)).mpr ?_
      rw [show n * (n⁻¹ * t * n) * n⁻¹ = t by group]
      exact ht
    have := hu1'.2 _ ht'
    calc t * (n * u * n⁻¹) = n * ((n⁻¹ * t * n) * u) * n⁻¹ := by group
      _ = n * (u * (n⁻¹ * t * n)) * n⁻¹ := by rw [this]
      _ = n * u * n⁻¹ * t := by group
  · have hX : X.map (MulAut.conj n).toMonoidHom = X := by
      ext x
      rw [mem_map_conj_iff]
      have := hnX (n⁻¹ * x * n)
      rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at this
      exact this
    have hmap : (⁅X, X⁆).map (MulAut.conj n).toMonoidHom = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, hX]
    rw [← hmap]
    exact ⟨u, hu2, by simp [MulAut.conj_apply]⟩

end ClaimA

section ClaimAGeneric

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]

theorem sylow_Tf_of_weakly_closed {T Sb N : Subgroup Mb} {f : Mb} {b : ↥N →* G}
    (hb : Function.Injective b) {M : Subgroup G} (hrange : b.range = M)
    (hcent : ∀ z ∈ centerOf (perfectCore M), orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ≤ M)
    (hTN : T ≤ N) (hf : f ∈ T)
    (hSylTf : IsSylowTwoOf (spTf T f) (Subgroup.centralizer ({f} : Set Mb) ⊓ N))
    (hZsq : ∀ x ∈ centerOf (perfectCore N), x ^ 2 = 1)
    (hZcls : ∀ x ∈ centerOf (perfectCore N), ∀ y ∈ centerOf Sb, IsConj x y →
      y ∈ centerOf (perfectCore N))
    (hWle : spWf T f ≤ centerOf Sb)
    (hWne : ∃ x ∈ spWf T f, x ∈ centerOf (perfectCore N) ∧ x ≠ 1)
    (hwc : ∀ (x y : Mb) (hx : x ∈ N) (hy : y ∈ N), x ∈ Sb → y ∈ Sb → orderOf x = 2 →
      orderOf y = 2 → IsConj (b ⟨x, hx⟩) (b ⟨y, hy⟩) → IsConj x y) :
    IsSylowTwoOf (subImg b (spTf T f)) (Subgroup.centralizer ({b ⟨f, hTN hf⟩} : Set G)) := by
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
  have hTfSyl : IsSylowTwoOf (subImg b (spTf T f)) (M ⊓ Subgroup.centralizer ({fg} : Set G)) := by
    rw [← himg]
    exact isSylowTwoOf_subImg hb (fun x hx => ⟨hx.2, hTfN hx⟩) inf_le_right hSylTf
  obtain ⟨R, hTfR, hR⟩ := exists_isSylowTwoOf_of_le (hTfSyl.le.trans inf_le_right)
    hTfSyl.2.1
  have hWg : centerOf (subImg b (spTf T f)) ⊓ ⁅subImg b (spTf T f), subImg b (spTf T f)⁆ =
      subImg b (spWf T f) := by
    unfold spWf
    rw [subImg_inf hb, subImg_centerOf hb hTfN, subImg_commutator hTfN]
  set W1 : Subgroup G := subImg b (spWf T f ⊓ centerOf (perfectCore N)) with hW1
  have hW1p : IsPGroup 2 W1 := fun g => ⟨1, by
    obtain ⟨z', hz'N, ⟨-, hz'Z⟩, hz⟩ := mem_subImg.mp g.2
    apply Subtype.ext
    have : (g : G) ^ 2 = 1 := by
      rw [← hz]
      exact (sq_eq_one_iff_of_injective hb hz'N).mpr (hZsq z' hz'Z)
    simpa using this⟩
  have hW1ne : W1 ≠ ⊥ := by
    obtain ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ := hWne
    intro h
    have hxN : x₀ ∈ N := hTfN (by
      unfold spWf at hx₀W
      exact (mem_centerOf_iff.mp hx₀W.1).1)
    have hmem : b ⟨x₀, hxN⟩ ∈ W1 := mem_subImg_of_mem b hxN ⟨hx₀W, hx₀Z⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hx₀1 (congrArg Subtype.val (hb (hmem.trans (map_one b).symm)))
  have hnorm : ∀ n ∈ R, n ∈ Subgroup.normalizer (subImg b (spTf T f) : Set G) →
      ∀ x ∈ W1, n * x * n⁻¹ ∈ W1 := by
    intro n _ hnT x hx
    obtain ⟨x', hx'N, ⟨hx'W, hx'Z⟩, rfl⟩ := mem_subImg.mp hx
    by_cases hx1 : x' = 1
    · subst hx1
      have h1 : b ⟨1, hx'N⟩ = 1 := map_one b
      rw [h1, mul_one, mul_inv_cancel]
      exact W1.one_mem
    · have hx'2 : orderOf x' = 2 := orderOf_eq_prime (hZsq x' hx'Z) hx1
      have hu : b ⟨x', hx'N⟩ ∈ centerOf (subImg b (spTf T f)) ⊓
          ⁅subImg b (spTf T f), subImg b (spTf T f)⁆ := by
        rw [hWg]
        exact mem_subImg_of_mem b hx'N hx'W
      have hnu := conj_mem_Wg hnT hu
      rw [hWg] at hnu
      obtain ⟨y, hyN, hyW, hy⟩ := mem_subImg.mp hnu
      have hyS : y ∈ Sb := (mem_centerOf_iff.mp (hWle hyW)).1
      have hx'S : x' ∈ Sb := (mem_centerOf_iff.mp (hWle hx'W)).1
      have hy1 : y ≠ 1 := by
        rintro rfl
        have h1 : b ⟨1, hyN⟩ = 1 := map_one b
        rw [h1] at hy
        have : b ⟨x', hx'N⟩ = 1 := by
          calc b ⟨x', hx'N⟩ = n⁻¹ * (n * b ⟨x', hx'N⟩ * n⁻¹) * n := by group
            _ = 1 := by rw [← hy]; group
        exact hx1 (congrArg Subtype.val (hb (this.trans (map_one b).symm)))
      have hy2 : y ^ 2 = 1 := by
        have hu2 : b ⟨x', hx'N⟩ ^ 2 = 1 :=
          (sq_eq_one_iff_of_injective hb hx'N).mpr (hZsq x' hx'Z)
        have : b ⟨y, hyN⟩ ^ 2 = 1 := by
          rw [hy]
          calc (n * b ⟨x', hx'N⟩ * n⁻¹) ^ 2 = n * b ⟨x', hx'N⟩ ^ 2 * n⁻¹ := by
                rw [sq, sq]; group
            _ = 1 := by rw [hu2]; group
        exact (sq_eq_one_iff_of_injective hb hyN).mp this
      have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
      have hconj : IsConj (b ⟨x', hx'N⟩) (b ⟨y, hyN⟩) := isConj_iff.mpr ⟨n, hy.symm⟩
      have hxy := hwc x' y hx'N hyN hx'S hyS hx'2 hyo hconj
      have hyZ := hZcls x' hx'Z y (hWle hyW) hxy
      rw [← hy]
      exact mem_subImg_of_mem b hyN ⟨hyW, hyZ⟩
  have hcent' : ∀ z ∈ W1, z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ M := by
    intro z hz hz1
    obtain ⟨z', hz'N, ⟨-, hz'Z⟩, rfl⟩ := mem_subImg.mp hz
    have hz'1 : z' ≠ 1 := fun h => hz1 (by subst h; exact map_one b)
    have hz'o : orderOf z' = 2 := orderOf_eq_prime (hZsq z' hz'Z) hz'1
    exact hcent _ (map_mem_centerOf_perfectCore hb hrange hz'N hz'Z)
      ((orderOf_img hb hz'N).trans hz'o)
  have hRTf := eq_of_weakly_closed hR hTfR hTfSyl hW1p hW1ne hnorm hcent'
  rw [hRTf] at hR
  exact hR

end ClaimAGeneric

section Main

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]
  {T Sb N1 N2 : Subgroup Mb} {I : Finset Mb} {f : Mb} {b1 : ↥N1 →* G} {b2 : ↥N2 →* G}
  {M1 M2 : Subgroup G}

omit [Finite G] in
theorem card_centralizer_eq_of_conj {a u c : G} (h : c * a * c⁻¹ = u) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) =
      Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  have hmap : (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({u} : Set G) := by
    ext y
    rw [mem_map_conj_iff]
    show c⁻¹ * y * c ∈ Subgroup.centralizer ({a} : Set G) ↔ y ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← h]
    constructor
    · intro hy
      calc y * (c * a * c⁻¹) = c * ((c⁻¹ * y * c) * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * y * c)) * c⁻¹ := by rw [hy]
        _ = c * a * c⁻¹ * y := by group
    · intro hy
      calc c⁻¹ * y * c * a = c⁻¹ * (y * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * a * c⁻¹) * y) * c := by rw [hy]
        _ = a * (c⁻¹ * y * c) := by group
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem SpGSetup.out_false [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : SpGSetup N1 N2 b1 b2 M1 M2) (O : F431SpOut T Sb f N1 N2 I) : False := by
  have hfT := O.f_mem
  have hfN1 : f ∈ N1 := O.T_le₁ hfT
  have hfN2 : f ∈ N2 := O.T_le₂ hfT
  have hSyl := S.sylow_out O
  have hnf := S.not_conj_out O
  have hTf1 : spTf T f ≤ N1 := inf_le_left.trans O.T_le₁
  have hTf2 : spTf T f ≤ N2 := inf_le_left.trans O.T_le₂
  have hwc1 : ∀ (x y : Mb) (hx : x ∈ N1) (hy : y ∈ N1), x ∈ Sb → y ∈ Sb → orderOf x = 2 →
      orderOf y = 2 → IsConj (b1 ⟨x, hx⟩) (b1 ⟨y, hy⟩) → IsConj x y := by
    intro x y hx hy hxS hyS hxo hyo h
    refine (O.lemma_F435 S.comp hnf hxS hyS hxo hyo).mpr ?_
    rw [amalgamMap_of_mem₁ b1 b2 hx, amalgamMap_of_mem₁ b1 b2 hy]
    exact h
  have hwc2 : ∀ (x y : Mb) (hx : x ∈ N2) (hy : y ∈ N2), x ∈ Sb → y ∈ Sb → orderOf x = 2 →
      orderOf y = 2 → IsConj (b2 ⟨x, hx⟩) (b2 ⟨y, hy⟩) → IsConj x y := by
    intro x y hx hy hxS hyS hxo hyo h
    refine (O.lemma_F435 S.comp hnf hxS hyS hxo hyo).mpr ?_
    rw [amalgamMap_of_mem₂ b1 b2 S.comp.agree hx, amalgamMap_of_mem₂ b1 b2 S.comp.agree hy]
    exact h
  obtain ⟨j, x₀, hx₀W, hx₀Z, hx₀1⟩ := O.W_ne
  have hTfSyl : IsSylowTwoOf (subImg b1 (spTf T f))
      (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    fin_cases j
    · exact sylow_Tf_of_weakly_closed S.comp.inj₁ S.range1 S.cent1 O.T_le₁ hfT (O.Sylow_Tf 0)
        (O.Z_sq 0) (O.Z_cls 0) O.W_le ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ hwc1
    · have h := sylow_Tf_of_weakly_closed S.comp.inj₂ S.range2 S.cent2 O.T_le₂ hfT (O.Sylow_Tf 1)
        (O.Z_sq 1) (O.Z_cls 1) O.W_le ⟨x₀, hx₀W, hx₀Z, hx₀1⟩ hwc2
      have e : subImg b2 (spTf T f) = subImg b1 (spTf T f) :=
        (subImg_eq_of_agree S.comp.agree hTf1 hTf2).symm
      have e' : b2 ⟨f, hfN2⟩ = b1 ⟨f, hfN1⟩ := (S.comp.agree f hfN1 hfN2).symm
      rw [e, e'] at h
      exact h
  have hb := S.comp.inj₁
  have hSN1 : Sb ≤ N1 := O.S_le.trans O.T_le₁
  obtain ⟨t₀, ht₀⟩ := O.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N1 := O.T_le₁ ht₀T
  have hcyc : subImg b1 T = subImg b1 Sb ⊔ Subgroup.zpowers (b1 ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN1 (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.transfer_contradiction_cyclic hnab hSyl
    (subImg_mono b1 O.S_le) (subImg_le_normalizer b1 O.S_norm) hcyc
    (mem_subImg_of_mem b1 hfN1 hfT)
    (fun h => O.f_not ((mem_subImg_iff_of_injective hb hfN1).mp h))
    ((sq_eq_one_iff_of_injective hb hfN1).mpr O.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => O.f_not (h ▸ Sb.one_mem)
  have hfg2 : b1 ⟨f, hfN1⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN1).mpr O.f_sq
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
  obtain ⟨i, hiI, -, hiφ⟩ := O.exists_conj S.comp hsS hso
  have hiT : i ∈ T := (mem_centerOf_iff.mp (O.I_center i hiI)).1
  have hiN : i ∈ N1 := O.T_le₁ hiT
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
      ((mem_centerOf_iff.mp (O.I_center i hiI)).2 t htT)
  have h1 : Nat.card (subImg b1 T) ≤ twoPart (Subgroup.centralizer ({u} : Set G)) :=
    card_le_twoPart hTg_le hSyl.2.1
  have h2 : twoPart (Subgroup.centralizer ({u} : Set G)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b1 (spTf T f)) =
      twoPart (Subgroup.centralizer ({b1 ⟨f, hfN1⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card T := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => O.f_not_central ?_)
    rw [mem_centerOf_iff]
    refine ⟨hfT, fun t ht => ?_⟩
    have : t ∈ spTf T f := by
      rw [h]
      exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  rw [card_subImg hb O.T_le₁] at h1
  rw [card_subImg hb hTf1] at h3
  omega

theorem finite_of_lieModel_psp {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f) :
    Finite D := by
  rcases hD with ⟨-, -, K, _, _, -, ⟨e⟩⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  all_goals exact absurd h (by norm_num)

theorem f431SpOut_of_lie {f : ℕ} (hLie : F431SpOutLieProp f) : F431Out .PSp 2 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E
  by_contra hodd
  have : IsSimpleGroup G := hG
  have : Finite D := finite_of_lieModel_psp hD
  have : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite ↥E.K := inferInstance
  obtain ⟨T, Sb, g, I, O⟩ := hLie D hD E.toLieAmalgamExt hodd
  have ha := hyps.2.1 (Or.inl rfl)
  have hb := hyps.2.2.2.1 (by simp)
  have hd := hyps.2.2.2.2 rfl
  have S : SpGSetup E.Mb1 E.Mb2 E.b1 E.b2 M1 M2 :=
    ⟨E.comp, E.range_b1, E.range_b2, E.inter_mem, ha.1, ha.2, hb.1, hb.2, hd.1, hd.2⟩
  exact S.out_false hnab O

theorem f431_sp_inputs_of_lie
    (hLie : ∀ f : ℕ, IsSec53Param .PSp 2 f → F431SpLieProp f)
    (hOutLie : ∀ f : ℕ, IsSec53Param .PSp 2 f → 3 ≤ f → F431SpOutLieProp f)
    (hOut4 : F431Out .PSp 2 2) :
    (∀ f : ℕ, IsSec53Param .PSp 2 f → F431SpLocal f) ∧
      (∀ f : ℕ, IsSec53Param .PSp 2 f → F431Out .PSp 2 f) := by
  refine ⟨fun f hf => f431SpLocal_of_lie (hLie f hf), fun f hf => ?_⟩
  by_cases h3 : 3 ≤ f
  · exact f431SpOut_of_lie (hOutLie f hf h3)
  · have h2 : f = 2 := by
      have := hf.1
      omega
    subst h2
    exact hOut4

end Main

end CFSG.Quasithin.H13.F431
