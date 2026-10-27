module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res11Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Subgroup
open scoped Pointwise

section Rank

variable {Y : Type*} [Group Y] [Finite Y]

theorem mem_of_normal_of_three_dvd (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    {N : Subgroup Y} [hN : N.Normal] (h3 : 3 ∣ Nat.card N) {x : Y} (hx : orderOf x = 3) :
    x ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hZN : zpowers x ≤ normalizer (N : Set Y) := by
    rw [normalizer_eq_top_iff.mpr hN]
    exact le_top
  let _ : MulDistribMulAction (zpowers x) N :=
    MulDistribMulAction.compHom N (Subgroup.inclusion hZN)
  have hcard := hZ.card_modEq_card_fixedPoints (Sylow 3 N)
  have hone : Nat.card (Sylow 3 N) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 N
  obtain ⟨R, hR⟩ : (MulAction.fixedPoints (zpowers x) (Sylow 3 N)).Nonempty := by
    rcases (MulAction.fixedPoints (zpowers x) (Sylow 3 N)).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hcard
      have h0 : Nat.card (Sylow 3 N) ≡ 0 [MOD 3] := by simpa using hcard
      have := h0.symm.trans hone
      exact absurd this (by decide)
    · exact h
  set R' : Subgroup Y := (R : Subgroup N).map N.subtype with hR'
  have hxR : ∀ r ∈ R', x * r * x⁻¹ ∈ R' := by
    rintro _ ⟨r, hr, rfl⟩
    have hfix : (⟨x, mem_zpowers x⟩ : zpowers x) • R = R := hR ⟨x, mem_zpowers x⟩
    have hmem : (⟨x, mem_zpowers x⟩ : zpowers x) • r ∈
        (⟨x, mem_zpowers x⟩ : zpowers x) • (R : Subgroup N) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hr
    have hsub : (((⟨x, mem_zpowers x⟩ : zpowers x) • R : Sylow 3 N) : Subgroup N) =
        (⟨x, mem_zpowers x⟩ : zpowers x) • (R : Subgroup N) := Sylow.pointwise_smul_def
    rw [← hsub, hfix] at hmem
    exact ⟨_, hmem, rfl⟩
  have hR'3 : IsPGroup 3 R' := R.isPGroup'.map _
  have hR'1 : R' ≠ ⊥ := by
    intro h
    apply Sylow.ne_bot_of_dvd_card R h3
    rw [eq_bot_iff]
    intro r hr
    have : (r : Y) ∈ R' := ⟨r, hr, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hZR : zpowers x ≤ normalizer (R' : Set Y) := by
    rw [zpowers_le]
    exact mem_normalizer_fintype hxR
  let _ : MulDistribMulAction (zpowers x) R' :=
    MulDistribMulAction.compHom R' (Subgroup.inclusion hZR)
  have hcard' := hZ.card_modEq_card_fixedPoints R'
  obtain ⟨k, hk⟩ := hR'3.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hR'1
    exact Subgroup.eq_bot_of_card_eq R' (by rw [hk, pow_zero])
  have hR'0 : Nat.card R' ≡ 0 [MOD 3] := by
    rw [hk, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self 3 hk0
  have hfix0 : Nat.card (MulAction.fixedPoints (zpowers x) R') ≡ 0 [MOD 3] :=
    hcard'.symm.trans hR'0
  have hone' : (1 : R') ∈ MulAction.fixedPoints (zpowers x) R' := fun z => smul_one z
  obtain ⟨r, hrfix, hr1⟩ : ∃ r ∈ MulAction.fixedPoints (zpowers x) R', r ≠ 1 := by
    by_contra! hall
    have hsub : MulAction.fixedPoints (zpowers x) R' = {1} := by
      ext r
      exact ⟨fun h => hall r h, fun h => h ▸ hone'⟩
    rw [hsub, Nat.card_unique] at hfix0
    exact absurd hfix0 (by decide)
  have hxr : x * (r : Y) = (r : Y) * x := by
    have h1 := congrArg Subtype.val (hrfix ⟨x, mem_zpowers x⟩)
    change x * (r : Y) * x⁻¹ = r at h1
    calc x * (r : Y) = x * (r : Y) * x⁻¹ * x := by group
      _ = (r : Y) * x := by rw [h1]
  have hr3 : IsPGroup 3 (zpowers (r : Y)) := hR'3.to_le (zpowers_le.mpr r.2)
  have hrne : (r : Y) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have h3r : 3 ∣ Nat.card (zpowers (r : Y)) := by
    obtain ⟨j, hj⟩ := hr3.exists_card_eq
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hj
      exact hrne hj
    rw [hj]
    exact dvd_pow_self 3 hj0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := zpowers (r : Y)) 3 h3r
  have hzo : orderOf (z : Y) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hzx : (z : Y) * x = x * (z : Y) := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp z.2
    rw [← hj]
    exact ((Commute.zpow_left (show Commute (r : Y) x from hxr.symm) j)).eq
  have hxz : x ∈ zpowers (z : Y) :=
    Sec20.Res5.mem_zpowers_of_commute hr hzo hx hzx
  have hzN : (z : Y) ∈ N := by
    have hzR : (z : Y) ∈ R' := (zpowers_le.mpr r.2) z.2
    obtain ⟨w, -, hw⟩ := hzR
    rw [← hw]
    exact w.2
  exact (zpowers_le.mpr hzN) hxz

theorem isSimpleGroup_of_pRank_le_one [Nontrivial Y] (hr : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    (hO : CFSG.pPrimeCore 3 Y = ⊥) {S : Set Y} (hS : closure S = ⊤)
    (hS3 : ∀ s ∈ S, s = 1 ∨ orderOf s = 3) : IsSimpleGroup Y := by
  refine ⟨fun N hN => ?_⟩
  by_cases h3 : 3 ∣ Nat.card N
  · right
    rw [eq_top_iff, ← hS, closure_le]
    intro s hs
    rcases hS3 s hs with rfl | h
    · exact N.one_mem
    · exact mem_of_normal_of_three_dvd hr h3 h
  · left
    have hle : N ≤ CFSG.pPrimeCore 3 Y :=
      le_sSup ⟨hN, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
    rw [hO] at hle
    exact eq_bot_iff.mpr hle

end Rank

section Core

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_core {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer (((CFSG.pPrimeCore 3 ↥Y).map Y.subtype : Subgroup G) : Set G) := by
  apply mem_normalizer_fintype
  rintro _ ⟨o, ho, rfl⟩
  have hchar := (Subgroup.characteristic_iff_map_eq.mp
    (CFSG.pPrimeCore_characteristic (p := 3) (G := ↥Y))) (Sec20.Res5.conjAutOf Y ⟨g, hg⟩)
  have hmem : Sec20.Res5.conjAutOf Y ⟨g, hg⟩ o ∈ CFSG.pPrimeCore 3 ↥Y := by
    rw [← hchar]
    exact ⟨o, ho, rfl⟩
  exact ⟨_, hmem, rfl⟩

theorem act_trivial_of_le {X Y : Subgroup G} (hYX : Y ≤ X) {d : G}
    (hdY : d ∈ normalizer (Y : Set G))
    (h : ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ (CFSG.pPrimeCore 3 ↥X).map X.subtype) :
    ∀ y ∈ Y, d * y * d⁻¹ * y⁻¹ ∈ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set OX : Subgroup G := (CFSG.pPrimeCore 3 ↥X).map X.subtype with hOX
  have hXOX : ∀ x ∈ X, x ∈ normalizer (OX : Set G) := fun x hx =>
    mem_normalizer_core (le_normalizer hx)
  have hnorm : (OX.subgroupOf Y).Normal := by
    refine ⟨fun o ho y => ?_⟩
    rw [mem_subgroupOf] at ho ⊢
    have := (mem_normalizer_iff.mp (hXOX y (hYX y.2)) o).mp ho
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card (OX.subgroupOf Y)) := by
    have h1 : Nat.card (OX.subgroupOf Y) ∣ Nat.card OX := by
      rw [← Subgroup.card_map_of_injective Y.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card OX = Nat.card (CFSG.pPrimeCore 3 ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    exact Nat.Coprime.coprime_dvd_right h1 (h2 ▸ CFSG.pPrimeCore_coprime_card)
  have hle : OX.subgroupOf Y ≤ CFSG.pPrimeCore 3 ↥Y := le_sSup ⟨hnorm, hcop⟩
  intro y hy
  have hw : d * y * d⁻¹ * y⁻¹ ∈ Y :=
    mul_mem ((mem_normalizer_iff.mp hdY y).mp hy) (inv_mem hy)
  have hwO : (⟨_, hw⟩ : Y) ∈ OX.subgroupOf Y := by
    rw [mem_subgroupOf]
    exact h y (hYX hy)
  exact ⟨_, hle hwO, rfl⟩

theorem not_three_dvd_card_sup {Y S : Subgroup G} (hS2 : IsPGroup 2 S) (hSY : S ≤ Y) :
    ¬ 3 ∣ Nat.card (S ⊔ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := (CFSG.pPrimeCore 3 ↥Y).map Y.subtype with hO
  set Γ : Subgroup G := S ⊔ O with hΓ
  have hSO : S ≤ normalizer (O : Set G) := fun s hs => mem_normalizer_core (le_normalizer (hSY hs))
  have hOO : O ≤ normalizer (O : Set G) := le_normalizer
  have hΓO : Γ ≤ normalizer (O : Set G) := sup_le hSO hOO
  have hOΓ : O ≤ Γ := le_sup_right
  have hnorm : (O.subgroupOf Γ).Normal := by
    refine ⟨fun o ho g => ?_⟩
    rw [mem_subgroupOf] at ho ⊢
    have := (mem_normalizer_iff.mp (hΓO g.2) o).mp ho
    simpa using this
  set q : S →* Γ ⧸ O.subgroupOf Γ :=
    (QuotientGroup.mk' (O.subgroupOf Γ)).comp (Subgroup.inclusion le_sup_left) with hq
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (O.subgroupOf Γ) y
    have hg : (g : G) ∈ ((S : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S O hSO]
      exact g.2
    obtain ⟨s, hs, o, ho, hso⟩ := hg
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [hq, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [mem_subgroupOf]
    have : ((Subgroup.inclusion le_sup_left ⟨s, hs⟩ : Γ)⁻¹ * g : Γ) = (⟨o, hOΓ ho⟩ : Γ) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hso]
      group
    rw [this]
    exact ho
  have hquot : IsPGroup 2 (Γ ⧸ O.subgroupOf Γ) := hS2.of_surjective q hqs
  obtain ⟨a, ha⟩ := hquot.exists_card_eq
  have hcardΓ : Nat.card Γ = Nat.card (Γ ⧸ O.subgroupOf Γ) * Nat.card (O.subgroupOf Γ) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hOcard : Nat.card (O.subgroupOf Γ) = Nat.card (CFSG.pPrimeCore 3 ↥Y) := by
    rw [← Subgroup.card_map_of_injective Γ.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hOΓ]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  intro h3
  rw [hcardΓ, ha, hOcard] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card h

theorem exists_sylow_two_normalized {Γ B : Subgroup G} (hB : IsPGroup 3 B)
    (hBΓ : B ≤ normalizer (Γ : Set G)) (hΓ : ¬ 3 ∣ Nat.card Γ) :
    ∃ P : Sylow 2 Γ, B ≤ normalizer ((((P : Subgroup Γ).map Γ.subtype : Subgroup G)) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulDistribMulAction B Γ := MulDistribMulAction.compHom Γ (Subgroup.inclusion hBΓ)
  have hcard := hB.card_modEq_card_fixedPoints (Sylow 2 Γ)
  obtain ⟨P, hP⟩ : (MulAction.fixedPoints B (Sylow 2 Γ)).Nonempty := by
    rcases (MulAction.fixedPoints B (Sylow 2 Γ)).eq_empty_or_nonempty with h | h
    · exfalso
      rw [h] at hcard
      have h0' : Nat.card (Sylow 2 Γ) ≡ 0 [MOD 3] := by simpa using hcard
      have h0 : 3 ∣ Nat.card (Sylow 2 Γ) := Nat.modEq_zero_iff_dvd.mp h0'
      obtain ⟨Q⟩ : Nonempty (Sylow 2 Γ) := inferInstance
      exact hΓ ((h0.trans (Sylow.card_dvd_index Q)).trans (Subgroup.index_dvd_card _))
    · exact h
  refine ⟨P, fun b hb => mem_normalizer_fintype ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hfix : (⟨b, hb⟩ : B) • P = P := hP ⟨b, hb⟩
  have hmem : (⟨b, hb⟩ : B) • x ∈ (⟨b, hb⟩ : B) • (P : Subgroup Γ) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  have hsub : (((⟨b, hb⟩ : B) • P : Sylow 2 Γ) : Subgroup Γ) =
      (⟨b, hb⟩ : B) • (P : Subgroup Γ) := Sylow.pointwise_smul_def
  rw [← hsub, hfix] at hmem
  exact ⟨_, hmem, rfl⟩

end Core

section Closure

variable {G : Type} [Group G]

theorem self_mem_normalClosureIn (M : Subgroup G) (c : G) : c ∈ Late.normalClosureIn M c :=
  Subgroup.subset_closure ⟨1, M.one_mem, by group⟩

theorem normalClosureIn_le {M : Subgroup G} {c : G} (hc : c ∈ M) :
    Late.normalClosureIn M c ≤ M := by
  rw [Late.normalClosureIn, closure_le]
  rintro _ ⟨m, hm, rfl⟩
  exact M.mul_mem (M.mul_mem hm hc) (M.inv_mem hm)

theorem normalClosureIn_mono {M M' : Subgroup G} (h : M ≤ M') (c : G) :
    Late.normalClosureIn M c ≤ Late.normalClosureIn M' c := by
  rw [Late.normalClosureIn, Late.normalClosureIn]
  apply Subgroup.closure_mono
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, h hm, rfl⟩

theorem le_normalizer_normalClosureIn [Finite G] (M : Subgroup G) (c : G) :
    M ≤ normalizer (Late.normalClosureIn M c : Set G) := by
  intro m hm
  apply mem_normalizer_fintype
  intro x hx
  have hle : (Late.normalClosureIn M c).map (MulAut.conj m).toMonoidHom ≤
      Late.normalClosureIn M c := by
    rw [Late.normalClosureIn, MonoidHom.map_closure, closure_le]
    rintro _ ⟨y, ⟨m', hm', rfl⟩, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨m * m', M.mul_mem hm hm', by simp [mul_assoc]⟩
  exact hle ⟨x, hx, rfl⟩

end Closure

section Perfect

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification

theorem exists_zpow_act_trivial
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {M : Subgroup G} {c : G} (hc : orderOf c = 3)
    (hr : CFSG.Open.pRank 3 (Late.normalClosureIn M c) ≤ 1)
    (hK : CFSG.IsKGroup ↥(Late.normalClosureIn M c))
    {Λ : Subgroup G} [Group.IsPerfect Λ] (hΛM : Λ ≤ M)
    (hΛc : Λ ≤ centralizer ({c} : Set G)) {r : G} (hrΛ : r ∈ Λ) (hr3 : r ^ 3 = 1) :
    ∃ k : ℤ, ∀ x ∈ Late.normalClosureIn M c, r * c ^ (-k) * x * (r * c ^ (-k))⁻¹ * x⁻¹ ∈
      (CFSG.pPrimeCore 3 ↥(Late.normalClosureIn M c)).map (Late.normalClosureIn M c).subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Late.normalClosureIn M c with hX
  set N := CFSG.pPrimeCore 3 ↥X with hN
  have hcX : c ∈ X := self_mem_normalClosureIn M c
  have hΛX : Λ ≤ normalizer (X : Set G) := hΛM.trans (le_normalizer_normalClosureIn M c)
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hNcop : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  set c' : X := ⟨c, hcX⟩ with hc'
  set cb : X ⧸ N := π c' with hcb'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hcb : orderOf cb = 3 := by
    apply orderOf_eq_prime (by rw [hcb', ← map_pow, hc'3, map_one])
    intro h1
    rw [hcb', hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hNcop
    have h2 : orderOf (⟨c', h1⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc] at h2
  have hrQ : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ N)) ≤ 1 := by
    rw [Sec20.Res5.pRank_top_quotient_eq N hNcop,
      ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num) X]
    exact hr
  set gens : Set G := {y | ∃ m ∈ M, y = m * c * m⁻¹} with hgens
  have hgenX : closure (Subtype.val ⁻¹' gens : Set X) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hgenQ : closure (π '' (Subtype.val ⁻¹' gens : Set X)) = ⊤ := by
    rw [← MonoidHom.map_closure, hgenX, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
  have hgen3 : ∀ s ∈ π '' (Subtype.val ⁻¹' gens : Set X), s = 1 ∨ orderOf s = 3 := by
    rintro _ ⟨g, ⟨m, -, hg⟩, rfl⟩
    have hg3 : g ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hg, conj_pow, hc3, mul_one, mul_inv_cancel, Subgroup.coe_one])
    have : (π g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    by_cases h1 : π g = 1
    · exact Or.inl h1
    · exact Or.inr (orderOf_eq_prime this h1)
  set φ : Λ →* MulAut (X ⧸ N) :=
    (Sec20.Res5.autQuot N).comp ((Sec20.Res5.conjAutOf X).comp (Subgroup.inclusion hΛX)) with hφ
  have hφx : ∀ (l : Λ) (x : X), φ l (π x) =
      π (Sec20.Res5.conjAutOf X (Subgroup.inclusion hΛX l) x) := fun l x => rfl
  have hrc : r * c * r⁻¹ = c := by
    have h1 : r * c = c * r := mem_centralizer_singleton_iff.mp (hΛc hrΛ)
    rw [h1, mul_inv_cancel_right]
  have hφc : φ ⟨r, hrΛ⟩ cb = cb := by
    rw [hcb', hφx]
    congr 1
    apply Subtype.ext
    rw [Sec20.Res5.conjAutOf_apply]
    exact hrc
  have hkey : ∃ k : ℤ, ∀ q : X ⧸ N, φ ⟨r, hrΛ⟩ q = cb ^ k * q * (cb ^ k)⁻¹ := by
    by_cases hab : ∀ a b : X ⧸ N, a * b = b * a
    · refine ⟨0, fun q => ?_⟩
      simp only [zpow_zero, one_mul, inv_one, mul_one]
      have hq : q ∈ zpowers cb := by
        have hle : (⊤ : Subgroup (X ⧸ N)) ≤ zpowers cb := by
          rw [← hgenQ, closure_le]
          intro s hs
          rcases hgen3 s hs with rfl | h
          · exact one_mem _
          · exact Sec20.Res5.mem_zpowers_of_commute hrQ hcb h (hab _ _)
        exact hle (mem_top q)
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hq
      rw [map_zpow, hφc]
    · push Not at hab
      obtain ⟨a, b, hab⟩ := hab
      have : Nontrivial (X ⧸ N) := nontrivial_of_ne _ _ hab
      have hsimp : IsSimpleGroup (X ⧸ N) := isSimpleGroup_of_pRank_le_one hrQ
        (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) hgenQ hgen3
      have hZ : center (X ⧸ N) = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (X ⧸ N)) with h | h
        · exact h
        · exfalso
          apply hab
          have hb : b ∈ center (X ⧸ N) := h ▸ mem_top b
          exact (mem_center_iff.mp hb a)
      have hSS : LBalance.SchreierSections (X ⧸ N) :=
        (LBalance.SchreierSections.of_isKGroup (fun S _ _ _ hnc hcat => hSch S hnc hcat)
          (Sec20.Res5.openIsKGroup_of_isKGroup hK)).quotient N
      have hsol : Group.IsSolvable (OuterAutomorphisms.Outer (X ⧸ N)) :=
        hSS.outer_solvable ⊤ ⟨a, b, hab⟩ (Subgroup.topEquiv (G := X ⧸ N)).toMonoidHom
          (Subgroup.topEquiv (G := X ⧸ N)).surjective
      have hout := SolvableKernelContainment.hom_eq_one
        ((QuotientGroup.mk' (OuterAutomorphisms.inner (X ⧸ N))).comp φ)
      have hin : φ ⟨r, hrΛ⟩ ∈ OuterAutomorphisms.inner (X ⧸ N) := by
        have h3 := congrArg (fun f => f ⟨r, hrΛ⟩) hout
        simp only [MonoidHom.comp_apply, MonoidHom.one_apply, QuotientGroup.mk'_apply] at h3
        exact (QuotientGroup.eq_one_iff _).mp h3
      obtain ⟨y, hy⟩ := hin
      have hycb : y * cb = cb * y := by
        have h1 : MulAut.conj y cb = cb := by rw [hy, hφc]
        rw [MulAut.conj_apply] at h1
        calc y * cb = y * cb * y⁻¹ * y := by group
          _ = cb * y := by rw [h1]
      have hy3 : y ^ 3 = 1 := by
        have h1 : MulAut.conj (y ^ 3) = 1 := by
          rw [map_pow, hy, ← map_pow]
          have : (⟨r, hrΛ⟩ : Λ) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
          rw [this, map_one]
        have h2 : y ^ 3 ∈ center (X ⧸ N) := by
          rw [mem_center_iff]
          intro g
          have h3 := congrArg (fun σ : MulAut (X ⧸ N) => σ g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at h3
          calc g * y ^ 3 = y ^ 3 * g * (y ^ 3)⁻¹ * y ^ 3 := by rw [h3]
            _ = y ^ 3 * g := by group
        rw [hZ, mem_bot] at h2
        exact h2
      have hyz : y ∈ zpowers cb := by
        by_cases hy1 : y = 1
        · rw [hy1]
          exact one_mem _
        · exact Sec20.Res5.mem_zpowers_of_commute hrQ hcb (orderOf_eq_prime hy3 hy1) hycb.symm
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyz
      refine ⟨k, fun q => ?_⟩
      rw [← hy, ← hk, MulAut.conj_apply]
  obtain ⟨k, hk⟩ := hkey
  refine ⟨k, fun x hx => ?_⟩
  have hck : c ^ k ∈ X := zpow_mem hcX k
  have hx0 : c ^ (-k) * x * c ^ k ∈ X :=
    mul_mem (mul_mem (zpow_mem hcX (-k)) hx) hck
  have h1 := hk (π ⟨_, hx0⟩)
  rw [hφx] at h1
  have h2 : cb ^ k * π ⟨_, hx0⟩ * (cb ^ k)⁻¹ = π ⟨x, hx⟩ := by
    rw [hcb', ← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, hc']
    group
  rw [h2, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
  set d := r * c ^ (-k) with hd
  have hdx : ((Sec20.Res5.conjAutOf X (Subgroup.inclusion hΛX ⟨r, hrΛ⟩) ⟨_, hx0⟩ : X) : G) =
      d * x * d⁻¹ := by
    rw [Sec20.Res5.conjAutOf_apply, hd]
    simp only [Subgroup.coe_inclusion]
    group
  have hw : (d * x * d⁻¹)⁻¹ * x ∈ (N.map X.subtype : Subgroup G) := by
    refine ⟨_, h1, ?_⟩
    rw [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, hdx]
  have hxN : x ∈ normalizer ((N.map X.subtype : Subgroup G) : Set G) :=
    mem_normalizer_core (le_normalizer hx)
  have := (mem_normalizer_iff.mp hxN _).mp (inv_mem hw)
  have e : x * ((d * x * d⁻¹)⁻¹ * x)⁻¹ * x⁻¹ = d * x * d⁻¹ * x⁻¹ := by group
  rwa [e] at this

end Perfect

end CFSG.RankThree.PartTwo.Sec21.Item21Res11Proof
