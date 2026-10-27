module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12StA
public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.Background.C124AsmOrder
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitHatA6
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem16Mod

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

open Orbit

namespace Lem12St

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G}

theorem isSolvable_of_card_dvd_192 {X : Type} [Group X] [Finite X] (h : Nat.card X ∣ 2 ^ 6 * 3) :
    Group.IsSolvable X := by
  obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
  have hb' : b ∣ 3 ^ 1 := by rwa [pow_one]
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hb'
  exact A312J2.isSolvable_of_card_pq Nat.prime_two Nat.prime_three (by norm_num) hab.symm

theorem isSolvable_of_card_dvd_24 {X : Type} [Group X] [Finite X] (h : Nat.card X ∣ 2 ^ 3 * 3) :
    Group.IsSolvable X :=
  isSolvable_of_card_dvd_192 (h.trans (by norm_num))

omit [Finite G] in
theorem not_le_centralizer (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V)
    (hv1 : v ≠ 1) (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    ¬ L ≤ Subgroup.centralizer (V : Set G) := by
  intro hle
  have hle' : oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G)) ≤ L :=
    (oTwoUpper_le _).trans inf_le_left
  refine autOn_ne_bot (hle'.trans hLV) hVL hv hv1 ?_
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff (hle'.trans hLV)).mp ha
  rw [Subgroup.mem_bot]
  exact (A4.actionOn_eq_one_iff _ _).mpr (hle (hle' hl))

omit [Finite G] in
theorem commutator_eq (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G}
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) : ⁅V, L⁆ = V := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact Lem12.commutator_le_of_le_normalizer hLV
  · conv_lhs => rw [hVL]
    exact Subgroup.commutator_mono le_rfl ((oTwoUpper_le _).trans inf_le_left)

omit [Finite G] in
theorem stab_lt [IsMulCommutative ↥V] (hLV : L ≤ Subgroup.normalizer (V : Set G)) {v : G}
    (hv : v ∈ V) (hvL : v ∉ Subgroup.centralizer (L : Set G)) :
    autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) < autOn L V := by
  refine lt_of_le_of_ne inf_le_left fun h => hvL ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hmem : A4.actionOn V L hLV ⟨l, hl⟩ ∈ autOn L V ⊓
      MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V) := by
    rw [h]
    exact (A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩
  have h1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hmem.2)
  change ((A4.actionOn V L hLV ⟨l, hl⟩ ⟨v, hv⟩ : ↥V) : G) = v at h1
  rw [A4.actionOn_apply_coe] at h1
  calc l * v = l * v * l⁻¹ * l := by group
    _ = v * l := by rw [h1]

variable [IsMulCommutative ↥V]

theorem simple_case_l3 (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hirr : ∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) →
        J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hperf : autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V =
      perfectCore (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V))
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  by_cases hvL : v ∈ Subgroup.centralizer (L : Set G)
  · exact isSimpleGroup_of_mem_centralizer hLV hV2 hq hO2 hirr hv hv1 hvL hK2 hVL
  exfalso
  obtain ⟨e⟩ := he
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
  obtain ⟨eH⟩ := nonempty_autOn_mulEquiv_of_simple hLV hO2 (not_le_centralizer hLV hv hv1 hVL) e
  have hcard : Nat.card (autOn L V) = 168 := by
    rw [Nat.card_congr eH.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  have hlt := Subgroup.card_lt_of_lt (stab_lt hLV hv hvL)
  rw [hcard] at hlt
  have hdvd : Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V)) ∣ 168 :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  exact false_of_isSolvable (autOn_le_stab hLV hv) (A312Ru.isSolvable_of_card_dvd_168 hdvd hlt)
    hperf (autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1)

omit [IsMulCommutative ↥V] in
theorem card_stab_eq [IsMulCommutative ↥V] {v : G} (hv : v ∈ V) {ℓ : ℕ}
    (h : Nat.card (orbitIn (autOn L V) (⟨v, hv⟩ : ↥V)) = ℓ) :
    ℓ * Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V)) =
      Nat.card (autOn L V) := by
  rw [← h]
  exact card_orbitIn_mul_card_stab (autOn L V) _

theorem simple_case_a7 (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV2 : ∀ x ∈ V, x ^ 2 = 1)
    (hcardV : Nat.card V = 2 ^ 4) (φ : ↥L →* ↥(alternatingGroup (Fin 7)))
    (hφ : Function.Surjective φ) (hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hperf : autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V =
      perfectCore (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V))
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hV2 x x.2)
  have hsurj := autOnSurj_surjective hLV
  let e₁ : ↥L ⧸ (autOnSurj hLV).ker ≃* ↥(autOn L V) :=
    QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  let e₂ : ↥L ⧸ φ.ker ≃* ↥(alternatingGroup (Fin 7)) :=
    QuotientGroup.quotientKerEquivOfSurjective _ hφ
  have hkk : (autOnSurj hLV).ker = φ.ker := by rw [ker_autOnSurj, hker]
  let e : ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 7)) :=
    (e₁.symm.trans (QuotientGroup.quotientMulEquivOfEq hkk)).trans e₂
  have hcard : Nat.card (autOn L V) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have horb := (orbitA7Four ↥V hsq hcardV (autOn L V) ⟨e⟩).1 ⟨v, hv⟩
    (fun h => hv1 (congrArg Subtype.val h))
  simp only [List.mem_singleton] at horb
  have h168 := card_stab_eq hv horb
  rw [hcard] at h168
  exact isSimpleGroup_of_card_168 (autOn_le_stab hLV hv) (by omega) hperf
    (autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1)

theorem simple_case_g2
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hirr : ∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) →
        J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V)
    (hG2 : G2NaturalDerived (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V) 1)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hperf : autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V =
      perfectCore (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V))
    (hK2 : pCoreOf 2 (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) = ⊥)
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  by_cases hvL : v ∈ Subgroup.centralizer (L : Set G)
  · exact isSimpleGroup_of_mem_centralizer hLV hV2 hq hO2 hirr hv hv1 hvL hK2 hVL
  exfalso
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hV2 x x.2)
  have hcomm := commV_autOn_eq_top hLV (commutator_eq hLV hVL)
  have hfix := fixV_autOn_eq hLV
  have hdvd : Nat.card (autOn L V) ∣ 12096 := by
    obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    have hK2' : Nat.card K = 2 := by rw [hK, pow_one]
    have h1 : Nat.card ↥(autOn L V) ∣
        Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      Subgroup.card_dvd_of_surjective hπ.1
    have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤
        CFSG.Open.quasithinG2 K := by
      refine Subgroup.commutator_le.2 fun g hg h hh => ?_
      rw [commutatorElement_def]
      exact (CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem
        ((CFSG.Open.quasithinG2 K).mul_mem hg hh) ((CFSG.Open.quasithinG2 K).inv_mem hg))
        ((CFSG.Open.quasithinG2 K).inv_mem hh)
    exact h1.trans ((Subgroup.card_dvd_of_le hle).trans (C124.card_G2_two hK2').dvd)
  set Z := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZdef
  have hv1' : (⟨v, hv⟩ : ↥V) ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  have horb : Nat.card (orbitIn (autOn L V) (⟨v, hv⟩ : ↥V)) = 63 := by
    by_cases hZ : Z = ⊥
    · rw [hZ] at hG2
      have := (orbitG2Natural ↥V (autOn L V) hG2).1 ⟨v, hv⟩ hv1'
      simpa using this
    · rcases VolI.g2NaturalCover_holds ↥V hsq (autOn L V) Z hfix.symm.le hcomm hG2 with
        h | ⟨hZ2, -, hW⟩
      · exact absurd h hZ
      · obtain ⟨z, hz1, hzZ⟩ := Lem16.exists_eq_zpowers_of_card_two hZ2
        have hzfix : z ∈ fixV (autOn L V) := by
          rw [hfix]
          change z ∈ Z
          rw [hzZ]
          exact Subgroup.mem_zpowers z
        have hvz : (⟨v, hv⟩ : ↥V) ≠ z := by
          intro h
          apply hvL
          have hzZ' : z ∈ Z := by rw [hzZ]; exact Subgroup.mem_zpowers z
          rw [← h] at hzZ'
          exact Subgroup.mem_subgroupOf.mp hzZ'
        have := (orbitG2Weyl ↥V (autOn L V) z hz1 hzfix hW).1 ⟨v, hv⟩ hv1' hvz
        simpa using this
  have h63 := card_stab_eq hv horb
  have hS : Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V)) ∣
      2 ^ 6 * 3 := by
    have h1 : 63 * Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V)) ∣
        63 * (2 ^ 6 * 3) := by
      rw [h63]
      exact hdvd.trans (by norm_num)
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  exact false_of_isSolvable (autOn_le_stab hLV hv) (isSolvable_of_card_dvd_192 hS) hperf
    (autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1)

theorem simple_case_hatA6 (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3)
    (he6 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 6)))
    (hCO : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L) (hcardV : Nat.card V = 2 ^ 6)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hperf : autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V =
      perfectCore (autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V))
    (hVL : V = ⁅V, oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))⁆) :
    IsSimpleGroup ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({v} : Set G))) V) := by
  have hsq : ∀ x : ↥V, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hV2 x x.2)
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := hCO ▸ inf_le_right
  obtain ⟨e6⟩ := he6
  have hinj : Function.Injective (autOnQuot hLV hO2) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [autOnQuot_mk] at hx
      have h1 : (l : G) ∈ Subgroup.centralizer (V : Set G) :=
        (mem_ker_autOnSurj hLV l).mp (MonoidHom.mem_ker.mpr hx)
      have h2 : (l : G) ∈ pCoreOf 2 L := by
        rw [← hCO]
        exact ⟨l.2, h1⟩
      rw [QuotientGroup.eq_one_iff]
      obtain ⟨l', hl', hl'l⟩ := h2
      rwa [show l' = l from Subtype.ext hl'l] at hl'
  let eQ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L V) :=
    MulEquiv.ofBijective _ ⟨hinj, autOnQuot_surjective hLV hO2⟩
  have : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := hq.1
  have hperf' : Group.IsPerfect ↥(autOn L V) :=
    Group.IsPerfect.ofSurjective (autOnQuot_surjective hLV hO2)
  have hZ3' : Nat.card (Subgroup.center ↥(autOn L V)) = 3 := by
    rw [← Nat.card_congr (Subgroup.centerCongr eQ).toEquiv]
    exact hZ3
  let e6' : ↥(autOn L V) ⧸ Subgroup.center ↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.congr (Subgroup.center ↥(autOn L V)) (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      eQ.symm (Subgroup.map_center_eq eQ.symm)).trans e6
  have hcard : Nat.card (autOn L V) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(autOn L V)),
      Nat.card_congr e6'.toEquiv, hZ3', nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have horb := (orbitHatA6Six_of Orbit.orbitTripleA6Six HatA6.hatA6SixModel ↥V hsq hcardV
    (autOn L V) hperf' hZ3' ⟨e6'⟩).1 ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))
  have hK1 := autOn_ne_bot (((oTwoUpper_le _).trans inf_le_left).trans hLV) hVL hv hv1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at horb
  rcases horb with h18 | h45
  · have h := card_stab_eq hv h18
    rw [hcard] at h
    exact isSimpleGroup_of_card_sixty (autOn_le_stab hLV hv) (by omega) hperf hK1
  · exfalso
    have h := card_stab_eq hv h45
    rw [hcard] at h
    exact false_of_isSolvable (autOn_le_stab hLV hv)
      (isSolvable_of_card_dvd_24 (by rw [show Nat.card ↥(autOn L V ⊓
        MulAction.stabilizer (MulAut ↥V) (⟨v, hv⟩ : ↥V)) = 24 by omega]; norm_num)) hperf hK1

end Lem12St

end CFSG.Quasithin.H13
