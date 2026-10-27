module

public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

noncomputable def toModO2 {H J : Subgroup G} (hJH : J ≤ H) : ↥J →* ↥(modO2Image H J) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hJH)).codRestrict _
    fun j => ⟨⟨j, hJH j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩

omit [Finite G] in
theorem toModO2_surjective {H J : Subgroup G} (hJH : J ≤ H) :
    Function.Surjective (toModO2 hJH) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

omit [Finite G] in
theorem mem_pCoreOf_of_toModO2_eq_one {H J : Subgroup G} (hJH : J ≤ H) {j : ↥J}
    (hj : toModO2 hJH j = 1) : (j : G) ∈ pCoreOf 2 H := by
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨j, hJH j.2⟩ = 1 := congrArg Subtype.val hj
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨j, hJH j.2⟩, h1, rfl⟩

omit [Finite G] in
theorem subsingleton_of_isSolvable_of_isPerfect {X : Type*} [Group X] (hs : Group.IsSolvable X)
    (hp : Group.IsPerfect X) : Subsingleton X := by
  have hall : ∀ n, derivedSeries X n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih]; exact hp.commutator_eq_top
  obtain ⟨n, hn⟩ := (Group.isSolvable_def X).mp hs
  rw [hall n] at hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup X) := hn ▸ Subgroup.mem_top a
  have hb : b ∈ (⊥ : Subgroup X) := hn ▸ Subgroup.mem_top b
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

theorem not_three_dvd_solvableRadical {X : Type} [Group X] [Finite X]
    (hidx : (CFSG.fittingSubgroup X).relIndex (CFSG.solvableRadical X) = 2)
    (hF : ¬ 3 ∣ Nat.card ↥(CFSG.fittingSubgroup X)) :
    ¬ 3 ∣ Nat.card ↥(CFSG.solvableRadical X) := by
  intro h3
  rw [← Subgroup.relIndex_mul_card, hidx] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact absurd h (by decide)
  · exact hF (h.trans (Subgroup.card_dvd_of_le inf_le_left))

namespace Conf

variable {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem solvRad_dichotomy (h36 : Vol2Native.A36CoreForSQTKCat) :
    (∀ x ∈ solvRad J, ∀ j ∈ J,
        x * j * x⁻¹ * j⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({w} : Set G))) ∨
      ¬ 3 ∣ Nat.card ↥(((solvRad J).subgroupOf J).map (toModO2 c.J_le)) := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hH := pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq
  obtain ⟨hcases, hcommon, -⟩ :=
    Vol2Native.lemma_1_2_1_four_core hK h36 hH c.mem
  set φ := toModO2 c.J_le with hφ
  set Nb := ((solvRad J).subgroupOf J).map φ with hNb
  have hRn : ((solvRad J).subgroupOf J).Normal := solvRad_normal J
  have hNbn : Nb.Normal := hRn.map φ (toModO2_surjective c.J_le)
  have hNbs : Group.IsSolvable ↥Nb := by
    have := solvRad_isSolvable J
    have : Group.IsSolvable ↥((solvRad J).subgroupOf J) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le J)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le J)).injective
    exact Group.isSolvable_of_surjective (φ.subgroupMap_surjective ((solvRad J).subgroupOf J))
  have hNbR : Nb ≤ CFSG.solvableRadical ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J) :=
    A3.le_solvableRadical hNbn hNbs
  have hcentral : Nb ≤ Subgroup.center ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J) →
      ∀ x ∈ solvRad J, ∀ j ∈ J,
        x * j * x⁻¹ * j⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) := by
    intro hZ x hx j hj
    have hxJ : x ∈ J := solvRad_le J hx
    have hxN : φ ⟨x, hxJ⟩ ∈ Nb := ⟨⟨x, hxJ⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hc := Subgroup.mem_center_iff.mp (hZ hxN) (φ ⟨j, hj⟩)
    have h1 : φ (⟨x, hxJ⟩ * ⟨j, hj⟩ * ⟨x, hxJ⟩⁻¹ * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group
    exact mem_pCoreOf_of_toModO2_eq_one c.J_le h1
  have hdvd : ∀ {X : Type} [Group X] [Finite X], ∀ N : Subgroup X, N ≤ CFSG.solvableRadical X →
      ¬ 3 ∣ Nat.card ↥(CFSG.solvableRadical X) → ¬ 3 ∣ Nat.card ↥N :=
    fun N hN h h3 => h (h3.trans (Subgroup.card_dvd_of_le hN))
  rcases hcommon.2.2.1 with ⟨-, hidx⟩ | ⟨hFZ, hFR, -⟩
  · rcases hcases with hcomp | h3 | h4
    · left
      apply hcentral
      rcases A3.eq_top_or_le_center_of_subnormal hcomp.1 hNbn.isSubnormal with h | h
      · exfalso
        have hs : Group.IsSolvable ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J) := by
          have e : ↥Nb ≃* ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J) :=
            (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
          exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
        obtain ⟨hperf, -, a, b, hab⟩ := hcomp.1
        have hsub := subsingleton_of_isSolvable_of_isPerfect hs hperf
        exact hab (Subsingleton.elim (α := ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J) ⧸
          Subgroup.center ↥(modO2Image (Subgroup.centralizer ({w} : Set G)) J)) _ _)
      · exact h
    · right
      obtain ⟨p, hp, hp3, -, ⟨e⟩, -⟩ := h3
      have : Fact p.Prime := ⟨hp⟩
      refine hdvd Nb hNbR (not_three_dvd_solvableRadical hidx ?_)
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        Fintype.card_fun, ZMod.card, Fintype.card_fin]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    · right
      obtain ⟨-, -, -, hprimes⟩ := h4
      refine hdvd Nb hNbR (not_three_dvd_solvableRadical hidx fun h3 => ?_)
      have := (hprimes 3 Nat.prime_three h3).1
      omega
  · left
    apply hcentral
    rw [← hFZ, hFR]
    exact hNbR

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
