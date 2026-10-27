module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
import CFSG.RankThree.PartTwo.Sec14.Item148Res9ONProofCube

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section CenterQuotient

variable {J : Type} [Group J]

private theorem l125_comm_mem_center {j : J} {S : Subgroup (J ⧸ Subgroup.center J)}
    (hS : ∀ t ∈ S, t * (j : J ⧸ Subgroup.center J) = (j : J ⧸ Subgroup.center J) * t) {s : J}
    (hs : (s : J ⧸ Subgroup.center J) ∈ S) : s * j * s⁻¹ * j⁻¹ ∈ Subgroup.center J := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hS _ hs]
  group

private theorem l125_mk_mem_zpowers {c : MulAut J} {j : J} (hj : MulAut.conj j = c)
    (hin : ∀ x : J, Commute x j → x ^ 3 = 1 → x ∈ Subgroup.zpowers j ⊔ Subgroup.center J)
    (hcube : ∀ x : J, c x = x → x ^ 3 ∈ Subgroup.center J → x ^ 3 = 1) {w : J}
    (hw : w * j = j * w) (hw3 : (w : J ⧸ Subgroup.center J) ^ 3 = 1) :
    (w : J ⧸ Subgroup.center J) ∈ Subgroup.zpowers (j : J ⧸ Subgroup.center J) := by
  have h3c : w ^ 3 ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hw3
  have hcw : c w = w := by
    rw [← hj, MulAut.conj_apply, mul_inv_eq_iff_eq_mul, hw]
  have hmem := hin w hw (hcube w hcw h3c)
  have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center J)) hmem
  rwa [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq] at h

variable [Finite J]

theorem res3L125_card_le_three_mul_card_center {c : MulAut J} {j : J} (hj : MulAut.conj j = c)
    (hj3 : j ^ 3 = 1)
    (hin : ∀ x : J, Commute x j → x ^ 3 = 1 → x ∈ Subgroup.zpowers j ⊔ Subgroup.center J)
    (hcube : ∀ x : J, c x = x → x ^ 3 ∈ Subgroup.center J → x ^ 3 = 1)
    (T : Subgroup (J ⧸ Subgroup.center J)) (hT3 : ∀ t ∈ T, t ^ 3 = 1)
    (hTC : ∀ t ∈ T, t * (j : J ⧸ Subgroup.center J) = (j : J ⧸ Subgroup.center J) * t) :
    Nat.card T ≤ 3 * Nat.card (Subgroup.center J) := by
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let Tt : Subgroup J := T.comap π
  let φ : Tt →* Subgroup.center J :=
    Sec14.Res9ON.commHom (le_refl _) j (fun s hs => l125_comm_mem_center hTC hs)
  have hpos : 0 < Nat.card (Subgroup.center J) := Nat.card_pos
  have h4 : Nat.card Tt = Nat.card T * Nat.card (Subgroup.center J) := by
    have hidx : Tt.index = T.index :=
      Subgroup.index_comap_of_surjective T (QuotientGroup.mk'_surjective _)
    have hipos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hipos
    calc Nat.card Tt * T.index = Nat.card J := by
          rw [← hidx]
          exact Subgroup.card_mul_index Tt
      _ = Nat.card (J ⧸ Subgroup.center J) * Nat.card (Subgroup.center J) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup _
      _ = (Nat.card T * T.index) * Nat.card (Subgroup.center J) := by
          rw [Subgroup.card_mul_index T]
      _ = Nat.card T * Nat.card (Subgroup.center J) * T.index := by ring
  have h1 := Sec14.Res9ON.card_eq_card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ Nat.card (Subgroup.center J) := Subgroup.card_le_card_group _
  have h3 : Nat.card φ.ker ≤ 3 * Nat.card (Subgroup.center J) := by
    let g : φ.ker →* J ⧸ Subgroup.center J := π.comp (Tt.subtype.comp φ.ker.subtype)
    have hg := Sec14.Res9ON.card_eq_card_ker_mul_card_range g
    have hk : Nat.card g.ker ≤ Nat.card (Subgroup.center J) := by
      have hx : ∀ x : g.ker, (((x : φ.ker) : Tt) : J) ∈ Subgroup.center J := fun x =>
        (QuotientGroup.eq_one_iff (((x : φ.ker) : Tt) : J)).mp (MonoidHom.mem_ker.mp x.2)
      refine Nat.card_le_card_of_injective (fun x => ⟨(((x : φ.ker) : Tt) : J), hx x⟩) ?_
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
    have hr : Nat.card g.range ≤ 3 := by
      have hle : g.range ≤ Subgroup.zpowers (π j) := by
        rintro _ ⟨k, rfl⟩
        have hkc : (((k : φ.ker) : Tt) : J) * j = j * (((k : φ.ker) : Tt) : J) :=
          (Sec14.Res9ON.mem_ker_commHom (le_refl _) _ ((k : φ.ker) : Tt)).mp k.2
        exact l125_mk_mem_zpowers hj hin hcube hkc (hT3 _ ((k : φ.ker) : Tt).2)
      calc Nat.card g.range ≤ Nat.card (Subgroup.zpowers (π j)) := Subgroup.card_le_of_le hle
        _ = orderOf (π j) := Nat.card_zpowers _
        _ ≤ 3 := Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hj3, map_one]))
    calc Nat.card φ.ker = Nat.card g.ker * Nat.card g.range := hg
      _ ≤ Nat.card (Subgroup.center J) * 3 := Nat.mul_le_mul hk hr
      _ = 3 * Nat.card (Subgroup.center J) := mul_comm _ _
  have hmul : Nat.card T * Nat.card (Subgroup.center J) ≤
      (3 * Nat.card (Subgroup.center J)) * Nat.card (Subgroup.center J) := by
    rw [← h4, h1]
    exact Nat.mul_le_mul h3 h2
  exact Nat.le_of_mul_le_mul_right hmul hpos

theorem res3L125_mem_zpowers_of_perfect {c : MulAut J} {j : J} (hj : MulAut.conj j = c)
    (hj3 : j ^ 3 = 1)
    (hin : ∀ x : J, Commute x j → x ^ 3 = 1 → x ∈ Subgroup.zpowers j ⊔ Subgroup.center J)
    (hcube : ∀ x : J, c x = x → x ^ 3 ∈ Subgroup.center J → x ^ 3 = 1)
    (I : Subgroup (J ⧸ Subgroup.center J)) (hI : ⁅I, I⁆ = I)
    (hIC : ∀ t ∈ I, t * (j : J ⧸ Subgroup.center J) = (j : J ⧸ Subgroup.center J) * t)
    {u : J ⧸ Subgroup.center J} (hu : u ∈ I) (hu3 : u ^ 3 = 1) :
    u ∈ Subgroup.zpowers (j : J ⧸ Subgroup.center J) := by
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let It : Subgroup J := I.comap π
  let φ : It →* Subgroup.center J :=
    Sec14.Res9ON.commHom (le_refl _) j (fun s hs => l125_comm_mem_center hIC hs)
  have hcommj : ∀ a ∈ It, ∀ b ∈ It, (a * b * a⁻¹ * b⁻¹) * j = j * (a * b * a⁻¹ * b⁻¹) := by
    intro a ha b hb
    have h1 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := mul_comm' _ _
    have h2 : (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ : It) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact (Sec14.Res9ON.mem_ker_commHom (le_refl _) _ _).mp h2
  have hcl : ⁅I, I⁆ ≤ (It ⊓ Subgroup.centralizer {j}).map π := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) y
    have ha : a ∈ It := hx
    have hb : b ∈ It := hy
    refine ⟨a * b * a⁻¹ * b⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact It.mul_mem (It.mul_mem (It.mul_mem ha hb) (It.inv_mem ha)) (It.inv_mem hb)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommj a ha b hb)
    · simp only [commutatorElement_def, map_mul, map_inv]
      rfl
  obtain ⟨w, ⟨-, hwC⟩, hwu⟩ := (hI.symm.le.trans hcl) hu
  have hwj : w * j = j * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
  subst hwu
  exact l125_mk_mem_zpowers hj hin hcube hwj hu3

end CenterQuotient

theorem res3L125_isPGroup_two_outer_of_card_le_two {G : Type*} [Group G] [Finite (Outer G)]
    (h : Nat.card (Outer G) ≤ 2) : IsPGroup 2 (Outer G) := by
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  generalize Nat.card (Outer G) = n at h hpos
  interval_cases n <;> decide

section Engine

private noncomputable def l125Phi {J G : Type} [Group J] [Group G]
    (e : J ⧸ Subgroup.center J ≃* G) : MulAut J →* MulAut G :=
  (MulAut.congr e).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J)

private theorem l125Phi_apply {J G : Type} [Group J] [Group G] (e : J ⧸ Subgroup.center J ≃* G)
    (a : MulAut J) (k : J) :
    l125Phi e a (e (k : J ⧸ Subgroup.center J)) = e ((a k : J) : J ⧸ Subgroup.center J) := by
  change e ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom J a)
      (e.symm (e (k : J ⧸ Subgroup.center J)))) = _
  rw [e.symm_apply_apply]
  exact congrArg e
    (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk a k)

private theorem l125Phi_injective {J G : Type} [Group J] [Group G] [Group.IsPerfect J]
    (e : J ⧸ Subgroup.center J ≃* G) : Function.Injective (l125Phi e) :=
  (MulAut.congr e).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective J)

theorem res3L125_false_of_rows
    {J : Type} [Group J] [Finite J] (hq : CFSG.IsQuasisimple J)
    {G : Type} [Group G] [Finite G] (e : J ⧸ Subgroup.center J ≃* G)
    (hout : IsPGroup 2 (Outer G))
    (hrow : ∀ x : G, orderOf x = 3 →
      (¬ 5 ∣ Nat.card (Subgroup.centralizer {x}) ∧ ¬ 7 ∣ Nat.card (Subgroup.centralizer {x})) ∨
      (∃ T : Subgroup G, T ≤ Subgroup.centralizer {x} ∧ (∀ t ∈ T, t ^ 3 = 1) ∧
        3 * Nat.card (Subgroup.center J) < Nat.card T) ∨
      (∃ I : Subgroup G, I ≤ Subgroup.centralizer {x} ∧ ⁅I, I⁆ = I ∧
        ∃ u ∈ I, orderOf u = 3 ∧ u ∉ Subgroup.zpowers x))
    {c g : MulAut J} {V U : Subgroup (MulAut J)} (hd : Res3Datum c g V U) : False := by
  haveI : Group.IsPerfect J := hq.1
  have hΦ := l125Phi_injective e
  have hZG : Subgroup.center G = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e,
      Group.IsPerfect.center_quotient_center_eq_bot J, Subgroup.map_bot]
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot hZG
  have hσ3 : (l125Phi e c) ^ 3 = 1 := by rw [← map_pow, hd.c_pow, map_one]
  have hσ1 : l125Phi e c ≠ 1 := fun h => hd.c_ne_one (hΦ (h.trans (map_one _).symm))
  obtain ⟨x₀, hx₀⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hout
    (by decide : Odd (3 : ℕ)) hσ3
  have hox₀ : orderOf x₀ = 3 := by
    rw [← orderOf_injective _ hinj x₀, hx₀]
    exact orderOf_eq_prime hσ3 hσ1
  obtain ⟨j, hj⟩ : ∃ j : J, e (j : J ⧸ Subgroup.center J) = x₀ := by
    obtain ⟨y, hy⟩ := e.surjective x₀
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨j, hy⟩
  have hjc : MulAut.conj j = c := by
    apply hΦ
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
    rw [l125Phi_apply, ← hx₀, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv, hj]
  obtain ⟨hj3, hin⟩ := hd.inner_threes j hjc
  have hcube := hd.cube
  have hodd : Odd (orderOf g) := Nat.odd_iff.mpr (by have := hd.not_two_dvd; omega)
  have hτ1 : l125Phi e g ≠ 1 := fun h => hd.g_ne_one (hΦ (h.trans (map_one _).symm))
  obtain ⟨y₀, hy₀⟩ := CFSG.StandardType.RawAut.mem_inner_of_isPGroup_outer hout hodd
    (show (l125Phi e g) ^ orderOf g = 1 by rw [← map_pow, pow_orderOf_eq_one, map_one])
  have hoy₀ : orderOf y₀ = orderOf g := by
    rw [← orderOf_injective _ hinj y₀, hy₀]
    exact orderOf_injective _ hΦ g
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    apply hinj
    rw [map_mul, map_mul, hx₀, hy₀, ← map_mul, ← map_mul, hd.comm.eq]
  have hn1 : orderOf y₀ ≠ 1 := by
    rw [hoy₀]
    exact fun h => hd.g_ne_one (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
  have hp57 : p = 5 ∨ p = 7 := hd.g_primes p hp (by rwa [hoy₀] at hpd)
  have hy₀C : y₀ ∈ Subgroup.centralizer {x₀} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hjx : (j : J ⧸ Subgroup.center J) = e.symm x₀ := by rw [← hj, e.symm_apply_apply]
  rcases hrow x₀ hox₀ with ⟨h5, h7⟩ | ⟨T, hTC, hT3, hT⟩ | ⟨I, hIC, hI, u, huI, huo, hun⟩
  ·
    have hdvd : p ∣ Nat.card (Subgroup.centralizer {x₀}) :=
      hpd.trans (Subgroup.orderOf_dvd_natCard _ hy₀C)
    rcases hp57 with rfl | rfl
    · exact h5 hdvd
    · exact h7 hdvd
  ·
    have hT3' : ∀ t ∈ T.map (e.symm : G →* J ⧸ Subgroup.center J), t ^ 3 = 1 := by
      rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow, hT3 t ht, map_one]
    have hTC' : ∀ t ∈ T.map (e.symm : G →* J ⧸ Subgroup.center J),
        t * (j : J ⧸ Subgroup.center J) = (j : J ⧸ Subgroup.center J) * t := by
      rintro _ ⟨t, ht, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hTC ht)
      rw [hjx]
      show e.symm t * e.symm x₀ = e.symm x₀ * e.symm t
      rw [← map_mul, ← map_mul, h]
    have hle := res3L125_card_le_three_mul_card_center hjc hj3 hin hcube _ hT3' hTC'
    rw [Subgroup.card_map_of_injective (f := (e.symm : G →* J ⧸ Subgroup.center J))
      e.symm.injective] at hle
    exact absurd hle (not_le.mpr hT)
  ·
    have hI' : ⁅I.map (e.symm : G →* J ⧸ Subgroup.center J),
        I.map (e.symm : G →* J ⧸ Subgroup.center J)⁆ =
          I.map (e.symm : G →* J ⧸ Subgroup.center J) := by
      rw [← Subgroup.map_commutator, hI]
    have hIC' : ∀ t ∈ I.map (e.symm : G →* J ⧸ Subgroup.center J),
        t * (j : J ⧸ Subgroup.center J) = (j : J ⧸ Subgroup.center J) * t := by
      rintro _ ⟨t, ht, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hIC ht)
      rw [hjx]
      show e.symm t * e.symm x₀ = e.symm x₀ * e.symm t
      rw [← map_mul, ← map_mul, h]
    have hu3 : u ^ 3 = 1 := by
      have h := pow_orderOf_eq_one u
      rwa [huo] at h
    have hmem := res3L125_mem_zpowers_of_perfect hjc hj3 hin hcube _ hI' hIC'
      (Subgroup.mem_map_of_mem (e.symm : G →* J ⧸ Subgroup.center J) huI)
      (show (e.symm u) ^ 3 = 1 by rw [← map_pow, hu3, map_one])
    apply hun
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← hj, ← map_zpow, hn]
    exact e.apply_symm_apply u

end Engine

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
