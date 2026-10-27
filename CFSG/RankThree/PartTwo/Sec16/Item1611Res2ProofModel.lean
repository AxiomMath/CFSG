module

public import CFSG.RankThree.PartTwo.Sec16.Item1611ResProofConfig
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofLower
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec16.Item169General

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1611Res2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem not_three_dvd_card_of_isPGroup_two {X : Type*} [Group X] [Finite X] {Y : Subgroup X}
    (hY : IsPGroup 2 Y) : ¬ 3 ∣ Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  rw [hk]
  intro h3
  have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem le_k142_of_item142 (h : Sec14Std G A c L) {hAab : IsMulCommutative A} {hcA : c ∈ A}
    (h142 : Item142 A (lB A) c L hAab hcA)
    (hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≠ 20160) :
    L ≤ k142 A (lB A) c := by
  have hD := h.toSec13Data
  obtain ⟨Q₀, -, hQ₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)))
    (Item148PtRes2.sup_mem_invariantPiSubgroups hD.mem_A fun x hx y hy => hD.commute hx hy)
  rcases (h142 Q₀ hQ₀).2 with ⟨⟨ψ⟩, -, -, -⟩ | ⟨hK, -⟩
  · exfalso
    obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
    obtain ⟨-, -, -, ⟨χ⟩⟩ := Sec13.facts_of_prod hD hS hZ ψ
    exact hcard (by rw [Nat.card_congr χ.toEquiv, Sec16.card_projSL_three_four])
  · rw [hK]
    exact le_sup_left.trans le_sup_left

theorem img142_eq_inf [(ker142 A (lB A) c).Normal] (hcA : c ∈ A)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    img142 A (lB A) c A = img142 A (lB A) c (A ⊓ L) := by
  have hZ : Subgroup.zpowers c ≤ kA142 A (lB A) c :=
    (Subgroup.zpowers_le.mpr hcA).trans le_sup_right
  have hAL : A ⊓ L ≤ kA142 A (lB A) c := inf_le_left.trans le_sup_right
  have h1 : img142 A (lB A) c A = img142 A (lB A) c (Subgroup.zpowers c ⊔ (A ⊓ L)) :=
    congrArg (fun X => img142 A (lB A) c X) hAc
  rw [h1, img142, img142, Subgroup.subgroupOf_sup hZ hAL, Subgroup.map_sup]
  have hbot : ((Subgroup.zpowers c).subgroupOf (kA142 A (lB A) c)).map
      (QuotientGroup.mk' (ker142 A (lB A) c)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    rw [ker142, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)
  rw [hbot, bot_sup_eq]

theorem not_transOn_of_model (hspor : SporadicModels131) (h : Sec14Std G A c L)
    [(ker142 A (lB A) c).Normal] (hLK : L ≤ k142 A (lB A) c)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({c} : Set G)))
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    {Γ : Type*} [Group Γ] [Finite Γ] (φ : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* Γ)
    {P : Subgroup Γ}
    (hφ : (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map φ.toMonoidHom = P)
    {Θ₁ Θ₂ : Subgroup Γ} {e : Γ} (he : e ∈ P)
    (hΘ₁ : IsPGroup 2 Θ₁) (hPΘ₁ : P ≤ Subgroup.normalizer (Θ₁ : Set Γ))
    (hΘ₂ : IsPGroup 2 Θ₂) (hPΘ₂ : P ≤ Subgroup.normalizer (Θ₂ : Set Γ))
    (h1 : ∀ X : Subgroup Γ, IsPGroup 2 X → P ≤ Subgroup.normalizer (X : Set Γ) → Θ₁ ≤ X →
      X ⊓ Subgroup.centralizer ({e} : Set Γ) = ⊥)
    (h2 : Θ₂ ⊓ Subgroup.centralizer ({e} : Set Γ) ≠ ⊥) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hAab : IsMulCommutative A := hD.isElemAbelian.1
  have hcA : c ∈ A := hD.mem_A
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Lα := img142 A (lB A) c L with hLα
  obtain ⟨ι, hι⟩ := Proof1611Res.exists_lbarEquiv hspor h hLK
  set Ψ : Γ ≃* ↥Lα := φ.symm.trans ι with hΨ
  set f : Γ →* ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c := Lα.subtype.comp Ψ.toMonoidHom
    with hf
  have hfinj : Function.Injective f := Lα.subtype_injective.comp Ψ.injective
  have hfφ : ∀ l : ↥L, f (φ (QuotientGroup.mk' θ l)) =
      QuotientGroup.mk' (ker142 A (lB A) c) ⟨(l : G), Subgroup.mem_sup_left (hLK l.2)⟩ := by
    intro l
    have h' : Ψ (φ (QuotientGroup.mk' θ l)) = ι (QuotientGroup.mk' θ l) := by
      rw [hΨ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change ((Ψ (φ (QuotientGroup.mk' θ l)) : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) = _
    rw [h', hι]
  have hfP : P.map f = img142 A (lB A) c A := by
    rw [img142_eq_inf hcA hAc]
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [← hφ] at hp
      obtain ⟨_, ⟨l, hl, rfl⟩, rfl⟩ := hp
      change f (φ (QuotientGroup.mk' θ l)) ∈ _
      rw [hfφ]
      exact Sec15.Proof1513Res3.mk_mem_img142 (Subgroup.mem_subgroupOf.mp hl)
    · rintro _ ⟨k, hk, rfl⟩
      have hkAL : ((k : ↥(kA142 A (lB A) c)) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hk
      refine ⟨φ (QuotientGroup.mk' θ ⟨(k : G), hkAL.2⟩), ?_, ?_⟩
      · rw [← hφ]
        exact ⟨_, ⟨⟨(k : G), hkAL.2⟩, Subgroup.mem_subgroupOf.mpr hkAL, rfl⟩, rfl⟩
      · rw [hfφ]
  have hfL : ∀ x : Γ, f x ∈ Lα := fun x => (Ψ x).2
  have hmapN : ∀ W : Subgroup Γ, P ≤ Subgroup.normalizer (W : Set Γ) →
      img142 A (lB A) c A ≤ Subgroup.normalizer ((W.map f : Subgroup _) : Set _) := by
    intro W hW
    rw [← hfP]
    exact (Subgroup.map_mono hW).trans (Subgroup.le_normalizer_map f)
  have hmapL : ∀ W : Subgroup Γ, W.map f ≤ Lα := by
    rintro W _ ⟨w, -, rfl⟩
    exact hfL w
  obtain ⟨S₁, hS₁, hΘS₁⟩ := Proof1611Res.exists_mem_star_ge hspor h hLK h142
    (hΘ₁.map f) (hmapL Θ₁) (hmapN Θ₁ hPΘ₁)
  obtain ⟨S₂, hS₂, hΘS₂⟩ := Proof1611Res.exists_mem_star_ge hspor h hLK h142
    (hΘ₂.map f) (hmapL Θ₂) (hmapN Θ₂ hPΘ₂)
  obtain ⟨a, haAL, hfe⟩ : ∃ a : G, ∃ ha : a ∈ A ⊓ L,
      f e = alpha142 A (lB A) c a ha.1 := by
    have he' := he
    rw [← hφ] at he'
    obtain ⟨_, ⟨l, hl, rfl⟩, rfl⟩ := he'
    refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, ?_⟩
    change f (φ (QuotientGroup.mk' θ l)) = _
    rw [hfφ]
    rfl
  have hAS₁ : img142 A (lB A) c A ≤
      Subgroup.normalizer ((img142 A (lB A) c S₁ : Subgroup _) : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Sec15.Proof1513Res3.mk_mem_normalizer_img142
      (hS₁.prop.1.1.1.2.2 (Subgroup.mem_subgroupOf.mp hk))
  have hS₁2 : IsPGroup 2 (img142 A (lB A) c S₁) :=
    Proof1611Res.isPGroup_img142 (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁.prop)
      (Proof1611Res.le_kA142_of_mem hS₁.prop)
  refine Proof1611Res.not_transOn_of_inf_centralizer hAab hcA (Proof1611Res.xA_le_normalizer h)
    hS₁ hS₂ haAL.1 ?_ ?_
  ·
    set X := (img142 A (lB A) c S₁).comap f with hX
    have hX2 : IsPGroup 2 X := hS₁2.comap_of_injective f hfinj
    have hPX : P ≤ Subgroup.normalizer (X : Set Γ) := by
      intro p hp
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hfp : f p ∈ img142 A (lB A) c A := hfP ▸ Subgroup.mem_map_of_mem f hp
      have h1' := (Subgroup.mem_normalizer_iff.mp (hAS₁ hfp) (f x)).mp hx
      change f (p * x * p⁻¹) ∈ img142 A (lB A) c S₁
      rw [map_mul, map_mul, map_inv]
      exact h1'
    have hΘX : Θ₁ ≤ X := fun t ht => hΘS₁ (Subgroup.mem_map_of_mem f ht)
    have hXe := h1 X hX2 hPX hΘX
    rw [eq_bot_iff]
    rintro y ⟨⟨hyS, hyL⟩, hyC⟩
    set x := Ψ.symm ⟨y, hyL⟩ with hx
    have hfx : f x = y := by
      change ((Ψ (Ψ.symm ⟨y, hyL⟩) : ↥Lα) : ↥(kA142 A (lB A) c) ⧸ ker142 A (lB A) c) = y
      rw [MulEquiv.apply_symm_apply]
    have hxX : x ∈ X := by
      change f x ∈ img142 A (lB A) c S₁
      rw [hfx]
      exact hyS
    have hxC : x ∈ Subgroup.centralizer ({e} : Set Γ) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hfinj
      rw [map_mul, map_mul, hfx, hfe]
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hx1 : x = 1 := by
      have : x ∈ (⊥ : Subgroup Γ) := hXe ▸ ⟨hxX, hxC⟩
      exact Subgroup.mem_bot.mp this
    rw [Subgroup.mem_bot, ← hfx, hx1, map_one]
  ·
    obtain ⟨⟨t, htΘ, htC⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h2
    have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
    intro hbot
    have hft : f t ∈ img142 A (lB A) c S₂ ⊓ Lα ⊓
        Subgroup.centralizer ({alpha142 A (lB A) c a haAL.1} : Set _) := by
      have hc : f t * alpha142 A (lB A) c a haAL.1 = alpha142 A (lB A) c a haAL.1 * f t := by
        rw [← hfe, ← map_mul, ← map_mul]
        exact congrArg f (Subgroup.mem_centralizer_singleton_iff.mp htC)
      exact ⟨⟨hΘS₂ (Subgroup.mem_map_of_mem f htΘ), hfL t⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
    rw [hbot, Subgroup.mem_bot] at hft
    exact ht1' (hfinj (hft.trans (map_one f).symm))

end CFSG.RankThree.PartTwo.Sec16.Proof1611Res2
