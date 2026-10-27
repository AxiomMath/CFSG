module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveStep
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

abbrev sylowBar2 (L U : Subgroup G) : Subgroup (Bar2 L) :=
  (U.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

theorem isSylowTwoOf_inf_of_mem_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
  CFSG.ABGLocalTools.isSylowOf_iff.mp
    (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_fo_sylow_inf D.sylowM hL.1)

theorem isSylowTwoOf_sylowBar2_of {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    CFSG.QuasithinUnique.IsSylowTwoOf (sylowBar2 L U) ⊤ :=
  CFSG.Quasithin.A312.isSylowTwoOf_top_map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSyl)

theorem rhoL_map_sylowBar2 {L U : Subgroup G} (m : ↥(normalizer (L : Set G)))
    (hmU : (m : G) ∈ normalizer (U : Set G)) :
    (sylowBar2 L U).map (UC6S846.rhoL L m).toMonoidHom = sylowBar2 L U := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hmu : (m : G) * (u : G) * (m : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hmU (u : G)).mp huU
    let u' : ↥L := Subgroup.normalizerMonoidHom L m u
    have hu' : u' ∈ U.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf, UC6S846.rhoL_mk_coe]
      exact hmu
    exact Subgroup.mem_map.mpr ⟨u', hu', rfl⟩
  · rw [Subgroup.card_map_of_injective (f := (UC6S846.rhoL L m).toMonoidHom)
      (UC6S846.rhoL L m).injective]

theorem exists_rhoL_pow_two_pow_eq_one {T L : Subgroup G} (hT2 : IsPGroup 2 T)
    (m : ↥(normalizer (L : Set G))) (hmT : (m : G) ∈ T) :
    ∃ k : ℕ, UC6S846.rhoL L m ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hT2 ⟨(m : G), hmT⟩
  refine ⟨k, ?_⟩
  have hm : m ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  rw [← map_pow, hm, map_one]

theorem powerMap_zero_of_mem_inner {Y : Type} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : CFSG.QuasithinUnique.IsSylowTwoOf W ⊤) (hZ : Subgroup.center Y = ⊥)
    {α : MulAut Y} (hα : α ∈ inner Y) (hpow : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hαW : W.map α.toMonoidHom = W) :
    ∀ x ∈ normalizer (W : Set Y), α x * (x ^ 2 ^ 0)⁻¹ ∈ W := by
  obtain ⟨k, hk⟩ := hpow
  obtain ⟨q, rfl⟩ := hα
  have hqN : q ∈ normalizer (W : Set Y) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hαW
  have hqpow : q ^ 2 ^ k = 1 := by
    have h2 : MulAut.conj (q ^ 2 ^ k) = 1 := by rw [map_pow]; exact hk
    have hcent : q ^ 2 ^ k ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun φ : MulAut Y => φ y) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * q ^ 2 ^ k = (q ^ 2 ^ k * y * (q ^ 2 ^ k)⁻¹) * q ^ 2 ^ k := by rw [hy]
        _ = q ^ 2 ^ k * y := by group
    rw [hZ] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hqW : q ∈ W :=
    CFSG.Quasithin.H13.KGHe.mem_of_mem_normalizer_of_pow hW (Subgroup.mem_top q) hqN hqpow
  intro x hx
  have h1 : x * q⁻¹ * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hx q⁻¹).mp (W.inv_mem hqW)
  have h3 : (MulAut.conj q) x * (x ^ 2 ^ 0)⁻¹ = q * (x * q⁻¹ * x⁻¹) := by
    simp only [MulAut.conj_apply, pow_zero, pow_one]
    group
  rw [h3]
  exact W.mul_mem hqW h1

theorem powerMap_lift_of_rhoL {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (m : ↥(normalizer (L : Set G))) {j : ℕ}
    (hj : ∀ x ∈ normalizer ((sylowBar2 L U : Subgroup (Bar2 L)) : Set (Bar2 L)),
      UC6S846.rhoL L m x * (x ^ 2 ^ j)⁻¹ ∈ sylowBar2 L U) :
    ∀ b ∈ L ⊓ normalizer (U : Set G),
      (m : G) * b * (m : G)⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  intro b hb
  obtain ⟨hbL, hbU⟩ := hb
  have hbW : (sylowBar2 L U).map
      (MulAut.conj (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)).toMonoidHom =
        sylowBar2 L U := by
    rw [← UC6S846.rhoL_inner L b hbL]
    exact rhoL_map_sylowBar2 _ hbU
  have hbN : (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) ∈
      normalizer ((sylowBar2 L U : Subgroup (Bar2 L)) : Set (Bar2 L)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbW
  have hmem := hj _ hbN
  rw [UC6S846.rhoL_mk] at hmem
  have hxW : QuotientGroup.mk' (CFSG.pCore 2 ↥L)
      (Subgroup.normalizerMonoidHom L m ⟨b, hbL⟩ * ((⟨b, hbL⟩ : ↥L) ^ 2 ^ j)⁻¹) ∈
        sylowBar2 L U := by
    rw [map_mul, map_inv, map_pow]
    exact hmem
  have hker_le : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ≤ U.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.Quasithin.pCore_two_le_subgroupOf hSyl
  have hx' : (Subgroup.normalizerMonoidHom L m ⟨b, hbL⟩ * ((⟨b, hbL⟩ : ↥L) ^ 2 ^ j)⁻¹) ∈
      ((U.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := hxW
  rw [Subgroup.comap_map_eq_self hker_le, Subgroup.mem_subgroupOf] at hx'
  have hxeq : (((Subgroup.normalizerMonoidHom L m ⟨b, hbL⟩ *
      ((⟨b, hbL⟩ : ↥L) ^ 2 ^ j)⁻¹ : ↥L)) : G) = (m : G) * b * (m : G)⁻¹ * (b ^ 2 ^ j)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, UC6S846.rhoL_mk_coe]
  rw [← hxeq]
  exact hx'

theorem mem_map_comap_mk_iff {L : Subgroup G} (P : Subgroup (Bar2 L)) (x : ↥L) :
    (x : G) ∈ (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype ↔
      (QuotientGroup.mk x : Bar2 L) ∈ P := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isMaxParabolicOver_preimage {T L : Subgroup G} {P : Subgroup (Bar2 L)}
    (hP : IsMaxParabolicOver (⊤ : Subgroup (Bar2 L)) (sylowBar2 L (T ⊓ L)) P) :
    IsMaxParabolicOver L (T ⊓ L)
      ((P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype) := by
  obtain ⟨-, hBor, hne, hmax⟩ := hP
  set Q : Subgroup G :=
    (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype with hQdef
  have hQmem : ∀ x : ↥L, (x : G) ∈ Q ↔ (QuotientGroup.mk x : Bar2 L) ∈ P :=
    mem_map_comap_mk_iff P
  have hQL : Q ≤ L := Subgroup.map_subtype_le _
  have hkerQ : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L → (x : G) ∈ Q := by
    intro x hx
    rw [hQmem]
    have h1 : (QuotientGroup.mk x : Bar2 L) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact P.one_mem
  · refine ⟨hQL, ?_, ?_, ?_⟩
    · rintro b ⟨hbL, hbN⟩
      apply (hQmem ⟨b, hbL⟩).mpr
      apply hBor
      refine ⟨Subgroup.mem_top _, ?_⟩
      have hbW := rhoL_map_sylowBar2 (L := L) (U := T ⊓ L) ⟨b, Subgroup.le_normalizer hbL⟩ hbN
      rw [UC6S846.rhoL_inner L b hbL] at hbW
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbW
    · intro hQeq
      apply hne
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hxQ : (x : G) ∈ Q := by rw [hQeq]; exact x.2
      exact (hQmem x).mp hxQ
    · intro R hQR hRL
      set Rb : Subgroup (Bar2 L) :=
        (R.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hRbdef
      have hPR : P ≤ Rb := by
        intro y hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        exact ⟨x, Subgroup.mem_subgroupOf.mpr (hQR ((hQmem x).mpr hy)), rfl⟩
      have hRmem : ∀ x : ↥L, (QuotientGroup.mk x : Bar2 L) ∈ Rb → (x : G) ∈ R := by
        intro x hx
        obtain ⟨z, hz, hzx⟩ := hx
        have hk : z⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
            show (QuotientGroup.mk z : Bar2 L) = QuotientGroup.mk x from hzx]
          exact inv_mul_cancel _
        have hzR : (z : G) ∈ R := Subgroup.mem_subgroupOf.mp hz
        have hkR : ((z⁻¹ * x : ↥L) : G) ∈ R := hQR (hkerQ _ hk)
        have hxeq : (x : G) = (z : G) * ((z⁻¹ * x : ↥L) : G) := by simp
        rw [hxeq]
        exact R.mul_mem hzR hkR
      rcases hmax Rb hPR le_top with hRP | hRtop
      · left
        refine le_antisymm (fun g hg => ?_) hQR
        have hgL : g ∈ L := hRL hg
        have hgR : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : Bar2 L) ∈ Rb :=
          ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
        rw [hRP] at hgR
        exact (hQmem ⟨g, hgL⟩).mpr hgR
      · right
        refine le_antisymm hRL (fun g hgL => ?_)
        have hgR : (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : Bar2 L) ∈ Rb := by
          rw [hRtop]; exact Subgroup.mem_top _
        exact hRmem ⟨g, hgL⟩ hgR

theorem rhoL_map_eq_of_not_swaps {T L : Subgroup G} (hns : ¬ SwapsParabolics T L)
    (m : ↥(normalizer (L : Set G))) (hmT : (m : G) ∈ T) :
    ∀ P : Subgroup (Bar2 L),
      IsMaxParabolicOver (⊤ : Subgroup (Bar2 L)) (sylowBar2 L (T ⊓ L)) P →
        P.map (UC6S846.rhoL L m).toMonoidHom = P := by
  intro P hP
  set Q : Subgroup G :=
    (P.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype with hQdef
  have hQmax : IsMaxParabolicOver L (T ⊓ L) Q := isMaxParabolicOver_preimage hP
  have hQfix : Q.map (MulAut.conj (m : G)).toMonoidHom = Q := by
    by_contra hneq
    exact hns ⟨(m : G), hmT, Q, hQmax, hneq⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
    have hzQ : (z : G) ∈ Q := (mem_map_comap_mk_iff P z).mpr hx
    have hmz : (m : G) * (z : G) * (m : G)⁻¹ ∈ Q := by
      rw [← hQfix]
      exact ⟨(z : G), hzQ, by simp [MulAut.conj_apply]⟩
    change UC6S846.rhoL L m (QuotientGroup.mk z) ∈ P
    rw [UC6S846.rhoL_mk]
    apply (mem_map_comap_mk_iff P _).mp
    rw [UC6S846.rhoL_mk_coe]
    exact hmz
  · rw [Subgroup.card_map_of_injective (f := (UC6S846.rhoL L m).toMonoidHom)
      (UC6S846.rhoL L m).injective]

theorem powerMap_of_rhoL_mem_inner {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hin : ∀ m : ↥(normalizer (L : Set G)), (m : G) ∈ T →
      UC6S846.rhoL L m ∈ inner (Bar2 L)) :
    ∀ t ∈ T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ T ⊓ L := by
  intro t ht
  have hTU : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := T)) hTL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let m : ↥(normalizer (L : Set G)) := ⟨t, hTL ht⟩
  exact ⟨0, powerMap_lift_of_rhoL hSyl m
    (powerMap_zero_of_mem_inner (isSylowTwoOf_sylowBar2_of hSyl) hZ (hin m ht)
      (exists_rhoL_pow_two_pow_eq_one hT2 m ht) (rhoL_map_sylowBar2 m (hTU ht)))⟩

theorem powerMap_of_rhoL_powerMap {T L : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L)
    (hpm : ∀ α : MulAut (Bar2 L), (∃ k : ℕ, α ^ 2 ^ k = 1) →
      (sylowBar2 L (T ⊓ L)).map α.toMonoidHom = sylowBar2 L (T ⊓ L) →
      ∃ j : ℕ, ∀ x ∈ normalizer ((sylowBar2 L (T ⊓ L) : Subgroup (Bar2 L)) : Set (Bar2 L)),
        α x * (x ^ 2 ^ j)⁻¹ ∈ sylowBar2 L (T ⊓ L)) :
    ∀ t ∈ T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ T ⊓ L := by
  intro t ht
  have hTU : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := T)) hTL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let m : ↥(normalizer (L : Set G)) := ⟨t, hTL ht⟩
  obtain ⟨j, hj⟩ := hpm (UC6S846.rhoL L m) (exists_rhoL_pow_two_pow_eq_one hT2 m ht)
    (rhoL_map_sylowBar2 m (hTU ht))
  exact ⟨j, powerMap_lift_of_rhoL hSyl m hj⟩

theorem le_normalizer_of_le_borel {T L B : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hpow : ∀ t ∈ T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ T ⊓ L)
    {s r : ℕ} (hs : Odd s) (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (hBorel : B ≤ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hcard : Nat.card B = r) :
    B ≤ normalizer (T : Set G) := by
  have hTU : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := T)) hTL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hXr : ∀ x ∈ B, x ≠ 1 → orderOf x = r := by
    intro x hx hx1
    have hxdvd : orderOf x ∣ r := by
      rw [← hcard]; exact Subgroup.orderOf_dvd_natCard B hx
    rcases (Nat.dvd_prime hr).mp hxdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  exact le_normalizer_of_powerMap (B := L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G))
    (U := T ⊓ L) hBorel (hBorel.trans inf_le_right) hTU inf_le_left
    (hT2.to_le inf_le_left) hT2 hpow hs hr hrdvd hXr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
