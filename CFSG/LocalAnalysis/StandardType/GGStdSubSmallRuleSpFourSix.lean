module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourLin

public section

namespace CFSG.StandardType.SpFour

open Module CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpFull CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.TwoThree CFSG.Assembly TableB
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (StatedSp)

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def fixSub (W : Submodule K (Fin m ⊕ Fin m → K)) :
    Subgroup (StatedSp m K) :=
  (fixG W).comap (spLin m K)

section LemI

variable [Finite K] [CharP K 2]

theorem lemI_sp (hK : Nat.card K = 2) (hm : 3 ≤ m) {Ã : Subgroup (StatedSp m K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ (m - 1) ≤ Nat.card Ã)
    {T : Submodule K (Fin m ⊕ Fin m → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0) (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T)
    {x : StatedSp m K} (hx : x ∈ Ã) (hx1 : x ≠ 1) :
    (∃ b ∈ Ã, b ∉ Subgroup.zpowers x ∧ ∀ u ∈ LinearMap.ker (spEnd x - 1), spEnd b u = u) ∨
      (finrank K (LinearMap.range (spEnd x - 1)) ≤ 4 ∧
        3 ^ (m - 2) ≤ Nat.card (Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) :
          Subgroup (StatedSp m K))) := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := m)
  haveI := finite_units_end (K := K) (V := Fin m ⊕ Fin m → K)
  set Xg : Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ := Ã.map (spLin m K) with hXg
  have hXiso := SpFin.isoSetup_map hÃ
  have hx₀ : spLin m K x ∈ Xg := ⟨x, hx, rfl⟩
  have hx₁ : spLin m K x ≠ 1 := fun h => hx1 (spLin_injective (h.trans (map_one _).symm))
  have hcardX : 3 ^ (m - 1) ≤ Nat.card Xg := by
    rw [hXg, ← Nat.card_congr (Ã.equivMapOfInjective (spLin m K) spLin_injective).toEquiv]
    exact hcard
  have hTX : ∀ g ∈ Xg, ∀ t ∈ T, (g : Module.End K (Fin m ⊕ Fin m → K)) t ∈ T := by
    rintro _ ⟨a, ha, rfl⟩ t ht
    exact hTÃ a ha t ht
  have hlem := SpFin.lemI hK spForm_nondegenerate spForm_isAlt.isRefl hXiso hx₀ hx₁ (n := m) hm
    (SpFin.finrank_spSpace m) hcardX hT0 hTiso hTX
  rcases hlem with ⟨g, hgX, hgn, hgf⟩ | ⟨hdm, hX2⟩
  · left
    obtain ⟨b, hb, rfl⟩ := hgX
    refine ⟨b, hb, ?_, fun u hu => hgf u hu⟩
    intro hbz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
    exact hgn (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩)
  · right
    refine ⟨hdm, ?_⟩
    have hle : (Xg ⊓ fixG (LinearMap.range (spEnd x - 1)) :
        Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ) ≤
        (Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) : Subgroup (StatedSp m K)).map
          (spLin m K) := by
      rintro g ⟨⟨b, hb, rfl⟩, hgf⟩
      exact ⟨b, ⟨hb, hgf⟩, rfl⟩
    calc 3 ^ (m - 2) ≤ Nat.card (Xg ⊓ fixG (LinearMap.range (spEnd x - 1)) :
          Subgroup (Module.End K (Fin m ⊕ Fin m → K))ˣ) := hX2
      _ ≤ Nat.card ((Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) :
          Subgroup (StatedSp m K)).map (spLin m K)) := Subgroup.card_le_of_le hle
      _ = Nat.card (Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) : Subgroup (StatedSp m K)) :=
        (Nat.card_congr ((Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) :
          Subgroup (StatedSp m K)).equivMapOfInjective (spLin m K) spLin_injective).toEquiv).symm

end LemI

section Helpers

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {Ã U : Subgroup G}
    (hUA : ∀ s ∈ Ã, ∀ u ∈ U, s * u * s⁻¹ ∈ U) {t : G} (ht : t ∈ Ã) :
    t ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hUA t ht h hh, fun hh => ?_⟩
  have h1 := hUA t⁻¹ (Ã.inv_mem ht) _ hh
  have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
  rwa [e] at h1

theorem mem_zpowers_symm {G : Type*} [Group G] [Finite G] {x t : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (h : t ∈ Subgroup.zpowers x) : x ∈ Subgroup.zpowers t := by
  have heq : Subgroup.zpowers t = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1,
        orderOf_eq_prime ht3 ht1])
  rw [heq]
  exact Subgroup.mem_zpowers x

variable [Finite K] [CharP K 2]

theorem not_mem_zpowers_of_fix {x t : StatedSp m K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hfix : ∀ w ∈ LinearMap.range (spEnd x - 1), spEnd t w = w) :
    t ∉ Subgroup.zpowers x := by
  haveI := SpFin.finite_statedSp_group (K := K) (m := m)
  intro h
  have hxt := mem_zpowers_symm hx3 hx1 ht3 ht1 h
  have htfix : t ∈ fixSub (LinearMap.range (spEnd x - 1)) := hfix
  have hxfix : x ∈ fixSub (LinearMap.range (spEnd x - 1)) :=
    (Subgroup.zpowers_le.mpr htfix) hxt
  have hx3' : spLin m K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  refine SpFin.rng_ne_bot (x₀ := spLin m K x)
    (fun h1 => hx1 (spLin_injective (h1.trans (map_one _).symm))) ?_
  rw [eq_bot_iff]
  intro w hw
  exact (Submodule.mem_bot K).mpr (OddIso.eq_zero_of_fixed_range (p := 3) ⟨1, by norm_num⟩
    (by rw [← Units.val_pow_eq_pow_val, hx3', Units.val_one]) hw (hxfix w hw))

theorem inf_range_eq_bot_of_finrank_two (hK : Nat.card K = 2) {x : StatedSp m K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hrk : finrank K (LinearMap.range (spEnd x - 1)) = 2)
    {T : Submodule K (Fin m ⊕ Fin m → K)} (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm m K u v = 0)
    (hTx : ∀ t ∈ T, spEnd x t ∈ T) : T ⊓ LinearMap.range (spEnd x - 1) = ⊥ := by
  by_contra hne
  have hx3' : spLin m K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : spLin m K x ≠ 1 := fun h => hx1 (spLin_injective (h.trans (map_one _).symm))
  set Tm := T ⊓ LinearMap.range (spEnd x - 1) with hTm
  have hxTm : ∀ u ∈ Tm, spEnd x u ∈ Tm := fun u hu =>
    ⟨hTx u hu.1, OddIso.range_invariant (spEnd x) hu.2⟩
  have hfp : ∀ u ∈ Tm, spEnd x u = u → u = 0 := fun u hu h =>
    OddIso.eq_zero_of_fixed_range (p := 3) ⟨1, by norm_num⟩ (spEnd_pow hx3) hu.2 h
  have heven := even_finrank_of_fpf hK (spEnd_pow hx3) hxTm hfp
  have h1 : 1 ≤ finrank K Tm := Submodule.one_le_finrank_iff.mpr hne
  have h2 : finrank K Tm ≤ finrank K (LinearMap.range (spEnd x - 1)) :=
    Submodule.finrank_mono inf_le_right
  obtain ⟨c, hc⟩ := heven
  have heq : Tm = LinearMap.range (spEnd x - 1) :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
  have hrT : ∀ w ∈ LinearMap.range (spEnd x - 1), w ∈ T := fun w hw => by
    have : w ∈ Tm := heq ▸ hw
    exact this.1
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (SpFin.rng_ne_bot hx1')
  obtain ⟨v, hv⟩ : ∃ v, spForm m K w v ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 ((spForm_nondegenerate (r := m) (K := K)).1 w h)
  obtain ⟨v₁, hv₁, w', hw', rfl⟩ := OddIso.exists_fix_add_range (p := 3) ⟨1, by norm_num⟩
    (spEnd_pow hx3) v
  have hinv : ∀ a b, spForm m K ((spLin m K x : Module.End K _) a)
      ((spLin m K x : Module.End K _) b) = spForm m K a b := fun a b => spEnd_isom x a b
  have h3 : spForm m K w v₁ = 0 := SpFin.rng_fix_orth (spForm m K) hinv hv₁ hw
  rw [map_add, h3, zero_add] at hv
  exact hv (hTiso w (hrT w hw) w' (hrT w' hw'))

end Helpers

section Six

variable [Finite K] [CharP K 2]

theorem conclAt_of_six (hK : Nat.card K = 2) {Ã : Subgroup (StatedSp 4 K)}
    (hÃ : IsElemAbelian 3 Ã) (hcard : 3 ^ 3 ≤ Nat.card Ã)
    {T : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hT0 : T ≠ ⊥)
    (hTiso : ∀ u ∈ T, ∀ v ∈ T, spForm 4 K u v = 0) (hTÃ : ∀ a ∈ Ã, ∀ t ∈ T, spEnd a t ∈ T)
    {x : StatedSp 4 K} (hx : x ∈ Ã) (hx1 : x ≠ 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 4 K x)) (hd : spFixedDim x = 6)
    (hEN : EndNodeAt Ã x) : ConclAt Ã x := by
  classical
  haveI := SpFin.finite_statedSp_group (K := K) (m := 4)
  have hx3 : x ^ 3 = 1 := hÃ.2 x hx
  have hx3' : spLin 4 K x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hbx : ∀ b ∈ Ã, b * x = x * b := fun b hb => TableB.IsElemAbelian.comm hÃ hb hx
  have hsum : finrank K (LinearMap.ker (spEnd x - 1)) +
      finrank K (LinearMap.range (spEnd x - 1)) = 2 * 4 := by
    have h := Submodule.finrank_add_eq_of_isCompl (SpFin.isCompl_fix_rng hx3')
    rw [SpFin.finrank_spSpace 4] at h
    exact h
  have hfix : finrank K (LinearMap.ker (spEnd x - 1)) = spFixedDim x := by
    rw [← blocks.fixed_eq]
    rfl
  have hrk : finrank K (LinearMap.range (spEnd x - 1)) = 2 := by omega
  have hDq : CFSG.IsQuasisimple (spFixedFactor x) :=
    SpFin.isQuasisimple_fixedFactor_of_six_le hK blocks (by omega)
  have hlay : layerC x = spFixedFactor x :=
    SpFin.layer_eq_of_isComponentOf (SpFin.isComponentOf_of_normalized
      (spFixedFactor_le_centralizer x) (fun c hc q hq => spFixedFactor_conj hc hq) hDq) hEN.1
  have hcent : ∀ s ∈ Ã, (∀ j ∈ spFixedFactor x, s * j = j * s) ↔ s ∈ Subgroup.zpowers x := by
    intro s hs
    have h := hEN.2 s hs
    rw [hlay] at h
    exact h
  rcases lemI_sp hK (by norm_num) hÃ hcard hT0 hTiso hTÃ hx hx1 with ⟨b, hb, hbn, hbf⟩ | ⟨-, h9⟩
  · exfalso
    exact hbn ((hcent b hb).mp fun j hj =>
      SpFin.commute_of_fix_fixedFactor hx3 blocks (hbx b hb) hbf hj)
  have h1 : 1 < Nat.card (Ã ⊓ fixSub (LinearMap.range (spEnd x - 1)) : Subgroup (StatedSp 4 K)) :=
    lt_of_lt_of_le (by norm_num) h9
  obtain ⟨⟨t, htmem⟩, ht1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
  obtain ⟨htÃ, htf⟩ := Subgroup.mem_inf.mp htmem
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have ht3 : t ^ 3 = 1 := hÃ.2 t htÃ
  have htD : t ∈ spFixedFactor x := mem_spFixedFactor_of_fix (hbx t htÃ) htf
  have htn : t ∉ Subgroup.zpowers x := not_mem_zpowers_of_fix hx3 hx1 ht3 ht1 htf
  have hj : ∃ j ∈ spFixedFactor x, t * j ≠ j * t := by
    by_contra hcon
    push Not at hcon
    exact htn ((hcent t htÃ).mp hcon)
  have hTker : T ⊓ LinearMap.ker (spEnd x - 1) ≠ ⊥ := by
    rcases SpFin.splitTI hx3' (fun t ht => hTÃ x hx t ht) hT0 with h | h
    · exact h
    · exact absurd (inf_range_eq_bot_of_finrank_two hK hx3 hx1 hrk hTiso (hTÃ x hx)) h
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTker
  have hwT : w ∈ T := hwmem.1
  have hwfix : spEnd x w = w := mem_ker_sub_one_iff.mp hwmem.2
  set U : Subgroup (StatedSp 4 K) := gammaT T ⊓ spFixedFactor x with hU
  have hτ : spTransvection w (1 : K) ∈ U :=
    ⟨spTransvection_mem_gammaT hTiso hwT 1, spTransvection_mem_spFixedFactor hwfix 1⟩
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hτ
    exact spTransvection_ne_one' hw0 hτ
  have hU2 : IsPGroup 2 U := (isPGroup_gammaT T).to_le inf_le_left
  have hUA : ∀ s ∈ Ã, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    exact ⟨conj_mem_gammaT (hTÃ s hs) (hTÃ s⁻¹ (Ã.inv_mem hs)) hu.1,
      spFixedFactor_conj (Subgroup.mem_centralizer_singleton_iff.mpr (hbx s hs)) hu.2⟩
  obtain ⟨j, hjD, hjt⟩ := hj
  refine ⟨U, hU1, hU2, ?_, hUA, t, ?_, ht3, fun s hs => TableB.IsElemAbelian.comm hÃ hs htÃ,
    mem_normalizer_of_conj_mem hUA htÃ, j, ?_, hjt⟩
  · rw [hlay]
    exact inf_le_right
  · rw [hlay]
    exact htD
  · rw [hlay]
    exact hjD

end Six

end CFSG.StandardType.SpFour
