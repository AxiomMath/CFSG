module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11B
public import CFSG.Quasithin.Background.E3Odd
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

theorem isElemAbelian_conjSubgroup627 {G : Type} [Group G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (g : G) : IsElemAbelian 2 (conjSubgroup V g) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, B2F.isElemAbelian_comm hV hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hV.2 x hx, map_one]

variable {G : Type} [Group G] [Finite G] {U UH H A B : Subgroup G}
  [(U.subgroupOf UH).Normal] [CommModCh611 UH U]
  (hHUH : H ≤ Subgroup.normalizer (UH : Set G)) (hHU : H ≤ Subgroup.normalizer (U : Set G))

include hHUH hHU

omit [Finite G] [CommModCh611 UH U] in
theorem card_offender627 (hAH : A ≤ H) (hA16 : Nat.card A = 16) (hB4 : Nat.card B = 4)
    (hAB : A ⊓ centralizerMod U H UH = B) :
    Nat.card ((A.subgroupOf H).map (actQuot UH U H hHUH hHU)) = 4 := by
  have hker : (actQuot UH U H hHUH hHU).ker = (centralizerMod U H UH).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizerMod_iff_actQuot']
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hAH]
  have h1 := Subgroup.relIndex_mul_card (centralizerMod U H UH) A
  rw [inf_comm, hAB, hB4, hA16] at h1
  omega

omit [Finite G] in
theorem isElemAbelian2_offender627 (hAab : IsElemAbelian 2 A) :
    IsElemAbelian2 ((A.subgroupOf H).map (actQuot UH U H hHUH hHU)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact B2F.isElemAbelian_comm hAab ha hb
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hAab.2 _ ha)
    rw [this, map_one]

omit [Finite G] [CommModCh611 UH U] in
theorem actQuot_mk_eq_iff627 {a : G} (haH : a ∈ H) (u : ↥UH) :
    actQuot UH U H hHUH hHU ⟨a, haH⟩ (u : ↥UH ⧸ U.subgroupOf UH) = (u : ↥UH ⧸ U.subgroupOf UH) ↔
      (u : G) * a * (u : G)⁻¹ * a⁻¹ ∈ U := by
  rw [actQuot_mk_eq_iff]
  have hau : a * (u : G)⁻¹ * a⁻¹ ∈ UH :=
    (Subgroup.mem_normalizer_iff.mp (hHUH haH) _).mp (UH.inv_mem u.2)
  constructor
  · intro h
    have := U.inv_mem h
    convert this using 1
    group
  · intro h
    have := U.inv_mem h
    convert this using 1
    group

omit [Finite G] in
theorem mem_aSet_two627 (hUHH : UH ≤ H) (hAH : A ≤ H) (hAab : IsElemAbelian 2 A)
    (hA16 : Nat.card A = 16) (hB4 : Nat.card B = 4) (hAB : A ⊓ centralizerMod U H UH = B)
    (hstar : ∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
      centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G)) :
    (A.subgroupOf H).map (actQuot UH U H hHUH hHU) ∈ aSet 2 (actQuot UH U H hHUH hHU).range := by
  classical
  set ρ := actQuot UH U H hHUH hHU with hρ
  set As := (A.subgroupOf H).map ρ with hAs
  have hAs4 : Nat.card As = 4 := card_offender627 hHUH hHU hAH hA16 hB4 hAB
  refine ⟨Subgroup.map_le_range _ _, ?_, isElemAbelian2_offender627 hHUH hHU hAab, ?_⟩
  · intro h0
    rw [h0, Subgroup.card_bot] at hAs4
    omega
  intro B' hB'As hm
  refine le_antisymm (fun q hq => ?_) (fun q hq x hx => hq x (hB'As hx))
  have hB'1 : B' ≠ ⊥ := by
    intro h0
    rw [h0, mQuot, Subgroup.relIndex_bot_left, hAs4,
      show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow] at hm
    omega
  obtain ⟨⟨b, hbB'⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB'1
  obtain ⟨⟨a₁, ha₁H⟩, ha₁A, ha₁b⟩ := hB'As hbB'
  set A₁ : Subgroup G := ((B'.comap ρ).map H.subtype) ⊓ A with hA₁
  have hBA₁ : B ≤ A₁ := by
    intro x hx
    have hx' : x ∈ A ⊓ centralizerMod U H UH := hAB ▸ hx
    have hxH : x ∈ H := hx'.2.1
    refine ⟨⟨⟨x, hxH⟩, ?_, rfl⟩, hx'.1⟩
    show ρ ⟨x, hxH⟩ ∈ B'
    rw [(mem_centralizerMod_iff_actQuot hxH).mp hx'.2]
    exact B'.one_mem
  have hA₁ne : (a₁ : G) ∉ B := by
    intro ha₁
    have hx' : a₁ ∈ A ⊓ centralizerMod U H UH := hAB ▸ ha₁
    apply hb1
    apply Subtype.ext
    show b = 1
    rw [← ha₁b]
    exact (mem_centralizerMod_iff_actQuot ha₁H).mp hx'.2
  have ha₁A₁ : a₁ ∈ A₁ := by
    refine ⟨⟨⟨a₁, ha₁H⟩, ?_, rfl⟩, ha₁A⟩
    show ρ ⟨a₁, ha₁H⟩ ∈ B'
    rw [ha₁b]
    exact hbB'
  have hlt : B < A₁ := lt_of_le_of_ne hBA₁ fun h => hA₁ne (h ▸ ha₁A₁)
  have hcen := hstar A₁ hlt inf_le_right
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu : (u : G) ∈ centralizerMod U UH A₁ := by
      refine ⟨u.2, hHU (hUHH u.2), fun a' ha' => ?_⟩
      obtain ⟨⟨⟨a'', ha''H⟩, ha''B', rfl⟩, -⟩ := ha'
      have h1 := hq _ ha''B'
      exact (actQuot_mk_eq_iff627 hHUH hHU ha''H u).mp h1
    have hu' := hcen hu
    rintro _ ⟨⟨a, haH⟩, haA, rfl⟩
    refine (actQuot_mk_eq_iff627 hHUH hHU haH u).mpr ?_
    have := Subgroup.mem_centralizer_iff.mp hu' a haA
    rw [← this, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem

omit [Finite G] in
theorem comap_fixV_offender627 (hUHH : UH ≤ H) (hAH : A ≤ H) :
    (fixV ((A.subgroupOf H).map (actQuot UH U H hHUH hHU))).comap
        (QuotientGroup.mk' (U.subgroupOf UH)) = (centralizerMod U UH A).subgroupOf UH := by
  ext u
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    refine ⟨u.2, hHU (hUHH u.2), fun a ha => ?_⟩
    exact (actQuot_mk_eq_iff627 hHUH hHU (hAH ha) u).mp (hu _ ⟨⟨a, hAH ha⟩, ha, rfl⟩)
  · rintro ⟨-, -, hu⟩ _ ⟨⟨a, haH⟩, haA, rfl⟩
    exact (actQuot_mk_eq_iff627 hHUH hHU haH u).mpr (hu a haA)

theorem index_fixV_offender627 (hUHH : UH ≤ H) (hAH : A ≤ H) (hUH2 : IsPGroup 2 UH)
    (hm2 : mQuot UH (centralizerMod U UH A) = 2) :
    (fixV ((A.subgroupOf H).map (actQuot UH U H hHUH hHU))).index = 4 := by
  rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (U.subgroupOf UH)),
    comap_fixV_offender627 hHUH hHU hUHH hAH]
  show (centralizerMod U UH A).relIndex UH = 4
  rw [relIndex_eq_two_pow hUH2, hm2]
  norm_num

theorem isFFStarOffender627 (hUHH : UH ≤ H) (hAH : A ≤ H) (hAab : IsElemAbelian 2 A)
    (hA16 : Nat.card A = 16) (hB4 : Nat.card B = 4) (hAB : A ⊓ centralizerMod U H UH = B)
    (hstar : ∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
      centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G))
    (hUH2 : IsPGroup 2 UH) (hm2 : mQuot UH (centralizerMod U UH A) = 2) :
    IsFFStarOffender (actQuot UH U H hHUH hHU).range
      ((A.subgroupOf H).map (actQuot UH U H hHUH hHU)) := by
  set As := (A.subgroupOf H).map (actQuot UH U H hHUH hHU) with hAs
  have hmem := mem_aSet_two627 hHUH hHU hUHH hAH hAab hA16 hB4 hAB hstar
  have hAs4 : Nat.card As = 4 := card_offender627 hHUH hHU hAH hA16 hB4 hAB
  have hidx := index_fixV_offender627 hHUH hHU hUHH hAH hUH2 hm2
  have hQ : Nat.card (↥UH ⧸ U.subgroupOf UH) = 4 * Nat.card (fixV As) := by
    rw [← hidx, (fixV As).index_mul_card]
  refine ⟨hmem.1, hmem.2.1, hmem.2.2.1, fun B' hB' => ?_⟩
  by_cases h0 : B' = ⊥
  · rw [h0, Subgroup.card_bot, one_mul, hAs4]
    have : fixV (⊥ : Subgroup (MulAut (↥UH ⧸ U.subgroupOf UH))) = ⊤ := by
      ext q
      simp [fixV]
    rw [this, Subgroup.card_top, hQ]
  · have hrel := Subgroup.relIndex_mul_card B' As
    rw [inf_eq_left.mpr hB', hAs4] at hrel
    have hB'2 : 2 ≤ Nat.card B' := by
      by_contra hcon
      push Not at hcon
      have hpos : 0 < Nat.card B' := Nat.card_pos
      have h1 : Nat.card B' = 1 := by omega
      exact h0 (Subgroup.card_eq_one.mp h1)
    have hm : mQuot As B' < 2 := by
      have hr : B'.relIndex As ≤ 2 := by
        by_contra hcon
        push Not at hcon
        have : 3 * 2 ≤ B'.relIndex As * Nat.card B' := Nat.mul_le_mul hcon hB'2
        omega
      unfold mQuot
      interval_cases hri : B'.relIndex As
      · simp
      · simp
      · simp
    rw [hmem.2.2.2 B' hB' hm]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hB')

theorem le_centralizer_oddCore627 (hUHH : UH ≤ H) (hAH : A ≤ H) (hAab : IsElemAbelian 2 A)
    (hA16 : Nat.card A = 16) (hB4 : Nat.card B = 4) (hAB : A ⊓ centralizerMod U H UH = B)
    (hstar : ∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
      centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G))
    (hsq : ∀ q : ↥UH ⧸ U.subgroupOf UH, q ^ 2 = 1) :
    (A.subgroupOf H).map (actQuot UH U H hHUH hHU) ≤
      Subgroup.centralizer (oddCoreIn (actQuot UH U H hHUH hHU).range :
        Set (MulAut (↥UH ⧸ U.subgroupOf UH))) :=
  e3_40 hsq (mem_aSet_two627 hHUH hHU hUHH hAH hAab hA16 hB4 hAB hstar)

omit [Finite G] in
theorem card_commV_offender627 (hAH : A ≤ H) (hB : ⁅UH, A⁆ = B) (hBU : B ⊓ U = ⊥)
    (hB4 : Nat.card B = 4) :
    Nat.card (commV ((A.subgroupOf H).map (actQuot UH U H hHUH hHU))) = 4 := by
  classical
  set ρ := actQuot UH U H hHUH hHU with hρ
  set As := (A.subgroupOf H).map ρ with hAs
  set mk := QuotientGroup.mk' (U.subgroupOf UH) with hmk
  have hBUH : B ≤ UH := by
    rw [← hB, Subgroup.commutator_le]
    intro u hu a ha
    have hau : a * u⁻¹ * a⁻¹ ∈ UH :=
      (Subgroup.mem_normalizer_iff.mp (hHUH (hAH ha)) _).mp (UH.inv_mem hu)
    rw [commutatorElement_def]
    have e : u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) := by group
    rw [e]
    exact UH.mul_mem hu hau
  set φ := mk.comp (B.subgroupOf UH).subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hmk, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
    have hxB : ((x : ↥UH) : G) ∈ B := Subgroup.mem_subgroupOf.mp x.2
    have h1 : ((x : ↥UH) : G) ∈ B ⊓ U := ⟨hxB, hx⟩
    rw [hBU, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hgen : ∀ (u : G) (hu : u ∈ UH) (a : G) (ha : a ∈ A),
      mk ⟨u * a * u⁻¹ * a⁻¹, by
        have hau : a * u⁻¹ * a⁻¹ ∈ UH :=
          (Subgroup.mem_normalizer_iff.mp (hHUH (hAH ha)) _).mp (UH.inv_mem hu)
        have e : u * a * u⁻¹ * a⁻¹ = u * (a * u⁻¹ * a⁻¹) := by group
        rw [e]
        exact UH.mul_mem hu hau⟩ =
        (ρ ⟨a, hAH ha⟩ ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH) *
          ((⟨u, hu⟩ : ↥UH) : ↥UH ⧸ U.subgroupOf UH)⁻¹)⁻¹ := by
    intro u hu a ha
    rw [hρ, actQuot_mk, mul_inv_rev, inv_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      hmk, QuotientGroup.mk'_apply]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have heq : commV As = φ.range := by
    apply le_antisymm
    · rw [commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨⟨a, haH⟩, haA, rfl⟩, q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H u =>
        have haA' : a ∈ A := haA
        have hmem : ⁅a, (u : G)⁆ ∈ B := by
          rw [← hB, Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator haA' u.2
        have hmemUH : ⁅a, (u : G)⁆ ∈ UH := hBUH hmem
        refine ⟨⟨⟨_, hmemUH⟩, Subgroup.mem_subgroupOf.mpr hmem⟩, ?_⟩
        rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ, actQuot_mk, hmk,
          QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        congr 1
    · rintro _ ⟨⟨b, hb⟩, rfl⟩
      have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
      set P : Subgroup G := ((commV As).comap mk).map UH.subtype with hP
      have hBP : B ≤ P := by
        rw [← hB, Subgroup.commutator_le]
        intro u hu a ha
        have hcUH : ⁅u, a⁆ ∈ UH := by
          rw [← hB] at hBUH
          exact hBUH (Subgroup.commutator_mem_commutator hu ha)
        refine ⟨⟨_, hcUH⟩, ?_, rfl⟩
        show mk ⟨⁅u, a⁆, hcUH⟩ ∈ commV As
        have e := hgen u hu a ha
        have e' : mk ⟨⁅u, a⁆, hcUH⟩ = mk ⟨u * a * u⁻¹ * a⁻¹, by
            rw [← commutatorElement_def]; exact hcUH⟩ := by
          congr 1
        rw [e', e]
        exact (commV As).inv_mem (Subgroup.subset_closure ⟨_, ⟨⟨a, hAH ha⟩, ha, rfl⟩, _, rfl⟩)
      obtain ⟨⟨b', hb'UH⟩, hb'P, hb'b⟩ := hBP hbB
      show mk b ∈ commV As
      rw [show b = ⟨b', hb'UH⟩ from Subtype.ext hb'b.symm]
      exact hb'P
  rw [heq, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBUH).toEquiv, hB4]

end CFSG.Quasithin.H13
