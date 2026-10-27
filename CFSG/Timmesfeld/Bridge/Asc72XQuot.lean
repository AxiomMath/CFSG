module

public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
open scoped commutatorElement

namespace CentralQuot

variable {X : Type} [Group X] {z : X} [(Subgroup.zpowers z).Normal]

abbrev mk (z : X) [(Subgroup.zpowers z).Normal] : X →* X ⧸ Subgroup.zpowers z :=
  QuotientGroup.mk' (Subgroup.zpowers z)

theorem mk_ne_one (hzz : z * z = 1) {E : Set X} (hE : IsOddTransp E) (hzE : z ∉ E) {d : X}
    (hd : d ∈ E) : mk z d ≠ 1 := by
  intro h
  rcases (mem_zpowers_of_mul_self hzz).mp ((QuotientGroup.eq_one_iff d).mp h) with h1 | h1
  · exact hE.ne_one hd h1
  · exact hzE (h1 ▸ hd)

theorem setup_mk (hzz : z * z = 1) {E : Set X} (hS : Setup X E) (hzE : z ∉ E) :
    Setup (X ⧸ Subgroup.zpowers z) (mk z '' E) :=
  hS.map (mk z) (QuotientGroup.mk'_surjective _) fun _ hd => mk_ne_one hzz hS.oddT hzE hd

omit [(Subgroup.zpowers z).Normal] in
theorem commute_of_inv_mul_mem (hzc : z ∈ Subgroup.center X) (hzz : z * z = 1) {a b : X}
    (h : a⁻¹ * b ∈ Subgroup.zpowers z) : Commute a b := by
  rcases (mem_zpowers_of_mul_self hzz).mp h with h1 | h1
  · rw [show b = a by rw [← mul_inv_cancel_left a b, h1, mul_one]]
  · have hb : b = a * z := by rw [← h1, mul_inv_cancel_left]
    rw [hb]
    exact (Commute.refl a).mul_right (Subgroup.mem_center_iff.mp hzc a)

theorem disconnected_mk (hzc : z ∈ Subgroup.center X) (hzz : z * z = 1) {E : Set X}
    (hE : IsOddTransp E) (hdisc : Disconnected E) : Disconnected (mk z '' E) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hdisc
  refine ⟨mk z a, ⟨a, ha, rfl⟩, mk z b, ⟨b, hb, rfl⟩, fun h => hab ?_⟩
  refine reach_of_reach_quotient hE (fun x hx y hy hxy => ?_) ha hb h
  exact reach_of_commute hx hy (commute_of_inv_mul_mem hzc hzz hxy)

theorem meetsSq_mk (hzz : z * z = 1) {E : Set X} (hE : IsOddTransp E) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) (hab : a ≠ b) (hc : Commute a b) (habz : a * b * z ∈ E) :
    MeetsSq (mk z '' E) := by
  refine ⟨mk z a, ⟨a, ha, rfl⟩, mk z b, ⟨b, hb, rfl⟩, fun h => ?_, hc.map _,
    ⟨a * b * z, habz, ?_⟩⟩
  ·
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hE.inv_eq ha] at h
    rcases (mem_zpowers_of_mul_self hzz).mp h with h1 | h1
    · exact hab (hE.eq_of_mul_eq_one ha h1)
    · rw [h1, hzz] at habz
      exact hE.ne_one habz rfl
  · have h1 : mk z z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
    rw [map_mul, map_mul, h1, mul_one]

theorem pCore_eq_comap (hzz : z * z = 1) :
    CFSG.pCore 2 X = (CFSG.pCore 2 (X ⧸ Subgroup.zpowers z)).comap (mk z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hn : ((CFSG.pCore 2 X).map (mk z)).Normal :=
      CFSG.pCore_normal.map _ (QuotientGroup.mk'_surjective _)
    have hp : IsPGroup 2 ((CFSG.pCore 2 X).map (mk z)) := CFSG.pCore_isPGroup.map _
    have hle : (CFSG.pCore 2 X).map (mk z) ≤ CFSG.pCore 2 (X ⧸ Subgroup.zpowers z) :=
      le_sSup ⟨hn, hp⟩
    exact Subgroup.map_le_iff_le_comap.mp hle
  · have hn : ((CFSG.pCore 2 (X ⧸ Subgroup.zpowers z)).comap (mk z)).Normal :=
      CFSG.pCore_normal.comap _
    have hp : IsPGroup 2 ((CFSG.pCore 2 (X ⧸ Subgroup.zpowers z)).comap (mk z)) := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := X ⧸ Subgroup.zpowers z)
        ⟨mk z x, hx⟩
      have hk' : mk z (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      refine ⟨k + 1, Subtype.ext ?_⟩
      show x ^ 2 ^ (k + 1) = 1
      rcases (mem_zpowers_of_mul_self hzz).mp ((QuotientGroup.eq_one_iff _).mp hk') with h | h
      · rw [pow_succ, pow_mul, h, one_pow]
      · rw [pow_succ, pow_mul, h, pow_two, hzz]
    exact le_sSup ⟨hn, hp⟩

theorem map_pCore (hzz : z * z = 1) :
    (CFSG.pCore 2 X).map (mk z) = CFSG.pCore 2 (X ⧸ Subgroup.zpowers z) := by
  rw [pCore_eq_comap hzz, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _)]

theorem zStar_eq_comap (hzz : z * z = 1) :
    zStar X = (zStar (X ⧸ Subgroup.zpowers z)).comap (mk z) := by
  ext g
  rw [Subgroup.mem_comap, mem_zStar_iff, mem_zStar_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_commutatorElement, ← Subgroup.mem_comap, ← pCore_eq_comap hzz]
    exact h x
  · intro h x
    rw [pCore_eq_comap hzz, Subgroup.mem_comap, map_commutatorElement]
    exact h _

theorem isBenderGroup_zStar (hzz : z * z = 1)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      ((X ⧸ Subgroup.zpowers z) ⧸ zStar (X ⧸ Subgroup.zpowers z))) :
    CFSG.BenderSuzuki.IsBenderGroup (X ⧸ zStar X) := by
  have hz2 : Subgroup.zpowers z ≤ zStar X := by
    rw [zStar_eq_comap hzz]
    intro x hx
    have h1 : mk z x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [Subgroup.mem_comap, h1]
    exact Subgroup.one_mem _
  have hmap : (zStar X).map (mk z) = zStar (X ⧸ Subgroup.zpowers z) := by
    rw [zStar_eq_comap hzz, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
  have e : X ⧸ zStar X ≃* (X ⧸ Subgroup.zpowers z) ⧸ zStar (X ⧸ Subgroup.zpowers z) :=
    (QuotientGroup.quotientQuotientEquivQuotient (Subgroup.zpowers z) (zStar X) hz2).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hmap)
  exact isBenderGroup_of_mulEquiv e hB

theorem map_commutator_of_surjective {Y : Type*} [Group Y] {f : X →* Y}
    (hf : Function.Surjective f) : (commutator X).map f = commutator Y := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf, commutator_def]

theorem pCore_le_center_of_commute {E : Set X} (hS : Setup X E) {a : X} (ha : a ∈ E)
    (hcon : ∀ q ∈ CFSG.pCore 2 X, Commute q a) : CFSG.pCore 2 X ≤ Subgroup.center X := by
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure E := hS.gen ▸ Subgroup.mem_top g
  have hgen : ∀ k ∈ E, Commute q k := by
    intro k hk
    obtain ⟨h, rfl⟩ := isConj_iff.mp (hS.isConj ha hk)
    have h1 := hcon (h⁻¹ * q * h⁻¹⁻¹) ((CFSG.pCore_normal (p := 2) (G := X)).conj_mem q hq h⁻¹)
    have h2 := h1.map (MulAut.conj h).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
    convert h2 using 1
    group
  exact (commute_of_mem_closure (S := {q}) (T := E)
    (fun u hu k hk => by rw [Set.mem_singleton_iff] at hu; rw [hu]; exact hgen k hk)
    (Subgroup.subset_closure rfl) hg).eq.symm

theorem mem_pCore (hzz : z * z = 1) : z ∈ CFSG.pCore 2 X := by
  have hn : (Subgroup.zpowers z).Normal := inferInstance
  have h2 : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases (mem_zpowers_of_mul_self hzz).mp hg with rfl | rfl
    · simp
    · simp [pow_two, hzz]
  have hle2 : Subgroup.zpowers z ≤ CFSG.pCore 2 X := le_sSup ⟨hn, h2⟩
  exact hle2 (Subgroup.mem_zpowers _)

section Bender

variable [Finite X]
  (hzc : z ∈ Subgroup.center X) (hzz : z * z = 1) {E : Set X} (hS : Setup X E) (hzE : z ∉ E)
  (hdisc : Disconnected E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) (hc : Commute a b)
  (habz : a * b * z ∈ E)
include hzc hzz hS hzE hdisc ha hb hab hc habz

theorem quot_facts : commutator (X ⧸ Subgroup.zpowers z) = ⊤ ∧
    CFSG.BenderSuzuki.IsBenderGroup
      ((X ⧸ Subgroup.zpowers z) ⧸ zStar (X ⧸ Subgroup.zpowers z)) := by
  have hS' := setup_mk hzz hS hzE
  have hM := meetsSq_mk hzz hS.oddT ha hb hab hc habz
  exact ⟨OddTransp.commutator_eq_top hS' hM, oddTranspZStar _ _ hS'.oddT hS'.normal hS'.gen hM
    (disconnected_mk hzc hzz hS.oddT hdisc)⟩

theorem noPerfectCentralExt : NoPerfectCentralExt X (CFSG.pCore 2 X) := by
  obtain ⟨hperf', hB'⟩ := quot_facts hzc hzz hS hzE hdisc ha hb hab hc habz
  have hS' := setup_mk hzz hS hzE
  have hB := isBenderGroup_zStar hzz hB'
  by_cases hperf : commutator X = ⊤
  · exact noPerfectCentralExt_of_isBenderGroup hS hperf hB
  have hzX : z ∉ commutator X := by
    intro hz
    apply hperf
    rw [eq_top_iff]
    intro g _
    have hg : mk z g ∈ (commutator X).map (mk z) := by
      rw [map_commutator_of_surjective (QuotientGroup.mk'_surjective _), hperf']
      exact Subgroup.mem_top _
    obtain ⟨c, hcX, hcg⟩ := hg
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcg
    rw [show g = c * (c⁻¹ * g) by group]
    rcases (mem_zpowers_of_mul_self hzz).mp hcg with h1 | h1
    · rw [h1, mul_one]
      exact hcX
    · rw [h1]
      exact (commutator X).mul_mem hcX hz
  have hle := pCore_le_commutator_of_isBenderGroup hS' hperf' hB'
  intro Q₀ _ _ hQ₀
  rintro x ⟨hxQ, hxX⟩
  have hx' : mk z x ∈ CFSG.pCore 2 (X ⧸ Subgroup.zpowers z) := by
    rw [pCore_eq_comap hzz] at hxQ
    exact hxQ
  have hx'' := hle hx'
  rw [← map_pCore hzz, ← Subgroup.map_top_of_surjective (mk z) (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_commutator] at hx''
  obtain ⟨c, hcN, hcx⟩ := hx''
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
  have hcX : c ∈ commutator X := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_rfl hcN
  rw [show x = c * (c⁻¹ * x) by group]
  rcases (mem_zpowers_of_mul_self hzz).mp hcx with h1 | h1
  · rw [h1, mul_one]
    exact hQ₀ hcN
  · exfalso
    apply hzX
    rw [← h1]
    exact (commutator X).mul_mem ((commutator X).inv_mem hcX) hxX

theorem exists_pCore_not_commute (hz1 : z ≠ 1) (hperf : commutator X = ⊤) :
    ∃ q ∈ CFSG.pCore 2 X, ¬ Commute q a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hnpc := noPerfectCentralExt hzc hzz hS hzE hdisc ha hb hab hc habz
  have hcomm0 : ⁅CFSG.pCore 2 X, (⊤ : Subgroup X)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr (pCore_le_center_of_commute hS ha hcon)
  have hle := hnpc ⊥ inferInstance bot_le (hcomm0 ▸ le_rfl)
  rw [hperf, inf_top_eq] at hle
  exact hz1 ((Subgroup.mem_bot).mp (hle (mem_pCore hzz)))

theorem pCore_eq_zpowers (hcon : ∀ q ∈ CFSG.pCore 2 X, Commute q a) :
    CFSG.pCore 2 X = Subgroup.zpowers z := by
  obtain ⟨hperf', -⟩ := quot_facts hzc hzz hS hzE hdisc ha hb hab hc habz
  have hnpc := noPerfectCentralExt hzc hzz hS hzE hdisc ha hb hab hc habz
  have hcomm0 : ⁅CFSG.pCore 2 X, (⊤ : Subgroup X)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr (pCore_le_center_of_commute hS ha hcon)
  have hle := hnpc ⊥ inferInstance bot_le (hcomm0 ▸ le_rfl)
  have hzQ := mem_pCore (X := X) hzz
  refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hzQ)
  have hg : mk z x ∈ (commutator X).map (mk z) := by
    rw [map_commutator_of_surjective (QuotientGroup.mk'_surjective _), hperf']
    exact Subgroup.mem_top _
  obtain ⟨c, hcX, hcx⟩ := hg
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
  have hcQ : c ∈ CFSG.pCore 2 X := by
    rw [show c = x * (c⁻¹ * x)⁻¹ by group]
    exact (CFSG.pCore 2 X).mul_mem hx ((CFSG.pCore 2 X).inv_mem
      (Subgroup.zpowers_le.mpr hzQ hcx))
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hle ⟨hcQ, hcX⟩)
  rw [hc1, inv_one, one_mul] at hcx
  exact hcx

end Bender

end CentralQuot

end CFSG.Timmesfeld.Bridge.Asc72
