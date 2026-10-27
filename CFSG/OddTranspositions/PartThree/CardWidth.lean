module

public import CFSG.OddTranspositions.FusionStep
public import CFSG.GroupTheory.SylowOrbitCard
public import CFSG.Timmesfeld.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.SecondKindCoset
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.GroupTheory
open MulAction

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem card_centralizer_mul_card_of_pretransitive [hDnorm : NormalizesSet ⊤ D]
    (hpre : IsPretransitive G ↥D) (x : ↥D) :
    Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) * Nat.card ↥D = Nat.card G := by
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G)
  have hidx : (MulAction.stabilizer G x).index = Nat.card ↥D :=
    @MulAction.index_stabilizer_of_transitive G ↥D _ _ x hpre
  have hstab : MulAction.stabilizer G x = C := stabilizer_conjMulActionOfTop x
  have h := Subgroup.card_mul_index (MulAction.stabilizer G x)
  rw [hidx, hstab] at h
  simpa [mul_comm] using h

omit [Finite G] in
theorem sylow_le_normalizer_inter (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g}) (S : Sylow 2 G) :
    (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) := by
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxD⟩
    exact ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs),
      CFSG.Timmesfeld.conj_mem_of_isClass hcl s hxD⟩
  · rintro ⟨hxS, hxD⟩
    have h1 : s⁻¹ * (s * x * s⁻¹) * s ∈ (S : Set G) ∩ D :=
      ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs,
        by simpa using CFSG.Timmesfeld.conj_mem_of_isClass hcl s⁻¹ hxD⟩
    have hEq : s⁻¹ * (s * x * s⁻¹) * s = x := by group
    rwa [hEq] at h1

theorem isPretransitive_normalizer_inter
    (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsOddTransp D) (S : Sylow 2 G)
    [hN : NormalizesSet (Subgroup.normalizer ((S : Set G) ∩ D)) ((S : Set G) ∩ D)] :
    IsPretransitive ↥(Subgroup.normalizer ((S : Set G) ∩ D))
      ↥((S : Set G) ∩ D) :=
  isPretransitive_of_forall_conj fun x y => sylow_inter_D_transitive hcl hD S x.2 y.2

theorem padicValNat_card_inf_centralizer [hDnorm : NormalizesSet ⊤ D]
    (hpre : IsPretransitive G ↥D) (S : Sylow 2 G) (u : ↥D)
    (horb : Nat.card (MulAction.orbit (↥S) u) = 2 ^ padicValNat 2 (Nat.card D)) :
    padicValNat 2 (Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ({(u : G)} : Set G))) =
      padicValNat 2 (Nat.card (Subgroup.centralizer ({(u : G)} : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({(u : G)} : Set G)
  let CS : Subgroup G := (S : Subgroup G) ⊓ C
  have hD0 : Nat.card ↥D ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨u⟩, inferInstance⟩
  have hC0 : Nat.card C ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨(1 : G), C.one_mem⟩⟩, inferInstance⟩
  have hCS0 : Nat.card CS ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨(1 : G), CS.one_mem⟩⟩, inferInstance⟩
  have hS_mul : 2 ^ padicValNat 2 (Nat.card D) * Nat.card CS = Nat.card S := by
    rw [← horb]
    simpa [CS, C, inf_comm] using card_orbit_sylow_mul_card_centralizer D S u
  have hG_mul : Nat.card C * Nat.card ↥D = Nat.card G :=
    card_centralizer_mul_card_of_pretransitive hpre u
  have hS_val : padicValNat 2 (Nat.card (S : Subgroup G)) =
      padicValNat 2 (Nat.card D) + padicValNat 2 (Nat.card CS) := by
    rw [← hS_mul, padicValNat.mul (pow_ne_zero _ (by norm_num)) hCS0,
      padicValNat.prime_pow]
  have hSylowS : Nat.card (S : Subgroup G) = 2 ^ padicValNat 2 (Nat.card G) := by
    rw [Sylow.card_eq_multiplicity,
      Nat.factorization_def (Nat.card G) (by norm_num : Nat.Prime 2)]
  have hG_val : padicValNat 2 (Nat.card G) =
      padicValNat 2 (Nat.card C) + padicValNat 2 (Nat.card D) := by
    rw [← hG_mul, padicValNat.mul hC0 hD0]
  have hvS : padicValNat 2 (Nat.card (S : Subgroup G)) = padicValNat 2 (Nat.card G) := by
    rw [hSylowS, padicValNat.prime_pow]
  have hvCS : padicValNat 2 (Nat.card CS) = padicValNat 2 (Nat.card C) := by
    have h1 : padicValNat 2 (Nat.card G) =
        padicValNat 2 (Nat.card D) + padicValNat 2 (Nat.card CS) := by
      rw [← hvS, hS_val]
    omega
  exact hvCS

theorem exists_sylow_inf_centralizer [hDnorm : NormalizesSet ⊤ D]
    (hpre : IsPretransitive G ↥D) (S : Sylow 2 G) (u : ↥D)
    (horb : Nat.card (MulAction.orbit (↥S) u) = 2 ^ padicValNat 2 (Nat.card D)) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({(u : G)} : Set G)),
      (P : Subgroup (Subgroup.centralizer ({(u : G)} : Set G))) =
        (((S : Subgroup G) ⊓ Subgroup.centralizer ({(u : G)} : Set G)).subgroupOf
          (Subgroup.centralizer ({(u : G)} : Set G))) := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({(u : G)} : Set G)
  let CS : Subgroup G := (S : Subgroup G) ⊓ C
  let K : Subgroup C := CS.subgroupOf C
  have hvCS : padicValNat 2 (Nat.card CS) = padicValNat 2 (Nat.card C) :=
    padicValNat_card_inf_centralizer hpre S u horb
  have hKcard : Nat.card K = Nat.card CS :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hK0 : Nat.card K ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨(1 : C), K.one_mem⟩⟩, inferInstance⟩
  have hCmul : Nat.card K * K.index = Nat.card C := Subgroup.card_mul_index K
  have hidx0 : padicValNat 2 K.index = 0 := by
    have hval : padicValNat 2 (Nat.card C) =
        padicValNat 2 (Nat.card K) + padicValNat 2 K.index := by
      rw [← hCmul, padicValNat.mul hK0 (Subgroup.index_ne_zero_of_finite)]
    have hKval : padicValNat 2 (Nat.card K) = padicValNat 2 (Nat.card C) := by
      rw [hKcard, hvCS]
    omega
  have hKodd : ¬ 2 ∣ K.index := by
    rcases (padicValNat.eq_zero_iff.mp hidx0) with h | h | h
    · norm_num at h
    · exact absurd h (Subgroup.index_ne_zero_of_finite)
    · exact h
  have hKp : IsPGroup 2 K := by
    have hCS_p : IsPGroup 2 CS := (S : Sylow 2 G).isPGroup'.to_le inf_le_left
    rw [show K = CS.subgroupOf C from rfl, ← Subgroup.comap_subtype CS C]
    exact hCS_p.comap_subtype (K := C)
  exact ⟨hKp.toSylow hKodd, IsPGroup.toSylow_coe hKp hKodd⟩

theorem mem_sylow_of_card_orbit_eq_pow [hDnorm : NormalizesSet ⊤ D]
    (hpre : IsPretransitive G ↥D) (hD : IsOddTransp D) (S : Sylow 2 G) (u : ↥D)
    (horb : Nat.card (MulAction.orbit (↥S) u) = 2 ^ padicValNat 2 (Nat.card D)) :
    (u : G) ∈ (S : Set G) := by
  classical
  obtain ⟨P, hPK⟩ := exists_sylow_inf_centralizer hpre S u horb
  let C : Subgroup G := Subgroup.centralizer ({(u : G)} : Set G)
  have huC : (u : G) ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  let x : C := ⟨(u : G), huC⟩
  have hx_center : x ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hx_p : IsPGroup 2 (Subgroup.zpowers x) := by
    have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hD.1 (u : G) u.2]
    exact IsPGroup.of_card (n := 1) (by simpa using hcard)
  have : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hx_center)
  have hxP : x ∈ (P : Subgroup C) := hx_p.le_sylow_of_normal P (Subgroup.mem_zpowers x)
  have hxK : x ∈ ((S : Subgroup G) ⊓ C).subgroupOf C := by
    rw [← hPK]
    exact hxP
  have hxCS : (u : G) ∈ (S : Subgroup G) ⊓ C := Subgroup.mem_subgroupOf.mp hxK
  exact (Subgroup.mem_inf.mp hxCS).1

theorem card_orbit_sylow_normalizer_eq [hDnorm : NormalizesSet ⊤ D]
    (S : Sylow 2 G) {N : Subgroup G} {E : Set G} [hE : NormalizesSet N E]
    (hS_le_N : (S : Subgroup G) ≤ N) (hED : E ⊆ D) (x : ↥E) :
    Nat.card (MulAction.orbit (↥(S.subgroupOf N)) x) =
      Nat.card (MulAction.orbit (↥S) (⟨(x : G), hED x.2⟩ : ↥D)) := by
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G)
  have hE_formula : Nat.card (MulAction.orbit (↥(S.subgroupOf N)) x) *
      Nat.card (↥(C ⊓ S)) = Nat.card S :=
    card_orbit_subgroupOf_mul_card_centralizer (A := N) (D := E) (S := S) hS_le_N x
  have hD_formula : Nat.card (MulAction.orbit (↥S) (⟨(x : G), hED x.2⟩ : ↥D)) *
      Nat.card (↥(C ⊓ S)) = Nat.card S :=
    card_orbit_sylow_mul_card_centralizer D S (⟨(x : G), hED x.2⟩ : ↥D)
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥(C ⊓ S)))
    (hE_formula.trans hD_formula.symm)

theorem card_orbit_sylow_subtype_eq [hDnorm : NormalizesSet ⊤ D]
    (S : Sylow 2 G) {N : Subgroup G} {E : Set G} [hE : NormalizesSet N E]
    (hS_le_N : (S : Subgroup G) ≤ N) (hED : E ⊆ D) (x : ↥E) :
    Nat.card (MulAction.orbit (↥(S.subtype hS_le_N)) x) =
      Nat.card (MulAction.orbit (↥S) (⟨(x : G), hED x.2⟩ : ↥D)) := by
  change Nat.card (MulAction.orbit (↥((S : Subgroup G).subgroupOf N)) x) =
    Nat.card (MulAction.orbit (↥S) (⟨(x : G), hED x.2⟩ : ↥D))
  exact card_orbit_sylow_normalizer_eq S hS_le_N hED x

theorem padicValNat_two_card_eq_width_of_normalizes
    (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsOddTransp D) (S : Sylow 2 G)
    [hDnorm : NormalizesSet ⊤ D]
    [hN : NormalizesSet (Subgroup.normalizer ((S : Set G) ∩ D)) ((S : Set G) ∩ D)]
    (hpre : IsPretransitive G ↥D) (hneD : Nonempty ↥D) :
    padicValNat 2 (Nat.card D) = padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) := by
  classical
  have hDne : Nat.card D ≠ 0 := Nat.card_ne_zero.mpr ⟨hneD, inferInstance⟩
  obtain ⟨u, huorb⟩ :=
    exists_orbit_card_eq_pow_padicValNat_of_sylow_of_pretransitive hpre hneD S
  have huS : (u : G) ∈ (S : Set G) :=
    mem_sylow_of_card_orbit_eq_pow (hDnorm := hDnorm) hpre hD S u huorb
  have hS_le_N : (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) :=
    sylow_le_normalizer_inter hcl S
  let SN : Sylow 2 ↥(Subgroup.normalizer ((S : Set G) ∩ D)) := S.subtype hS_le_N
  have hpreN : IsPretransitive ↥(Subgroup.normalizer ((S : Set G) ∩ D))
      ↥((S : Set G) ∩ D) :=
    isPretransitive_normalizer_inter (hN := hN) hcl hD S
  let uE : ↥((S : Set G) ∩ D) := ⟨(u : G), ⟨huS, u.2⟩⟩
  have hneE : Nonempty ↥((S : Set G) ∩ D) := ⟨uE⟩
  have hdivE : 2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) ∣
      Nat.card (MulAction.orbit (↥SN) uE) :=
    pow_padicValNat_dvd_card_orbit_of_sylow_of_pretransitive hpreN SN uE
  have hu_orbit_eq : Nat.card (MulAction.orbit (↥SN) uE) =
      Nat.card (MulAction.orbit (↥S) u) := by
    exact card_orbit_sylow_subtype_eq (hDnorm := hDnorm) (hE := hN) S
      hS_le_N (fun _ hx => hx.2) uE
  have hw_dvd_D : 2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) ∣
      2 ^ padicValNat 2 (Nat.card D) := by
    rw [hu_orbit_eq, huorb] at hdivE
    exact hdivE
  obtain ⟨x, hxorb⟩ :=
    exists_orbit_card_eq_pow_padicValNat_of_sylow_of_pretransitive hpreN hneE SN
  have hD_dvd_w : 2 ^ padicValNat 2 (Nat.card D) ∣
      2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) := by
    have hdivD : 2 ^ padicValNat 2 (Nat.card D) ∣
        Nat.card (MulAction.orbit (↥S) (⟨(x : G), x.2.2⟩ : ↥D)) :=
      pow_padicValNat_dvd_card_orbit_of_sylow_of_pretransitive hpre S
        ⟨(x : G), x.2.2⟩
    have hx_orbit_eq : Nat.card (MulAction.orbit (↥SN) x) =
        Nat.card (MulAction.orbit (↥S) (⟨(x : G), x.2.2⟩ : ↥D)) := by
      exact card_orbit_sylow_subtype_eq (hDnorm := hDnorm) (hE := hN) S
        hS_le_N (fun _ hx => hx.2) x
    rw [← hx_orbit_eq, hxorb] at hdivD
    exact hdivD
  have hv1 : padicValNat 2 (Nat.card D) ≤ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hD_dvd_w
  have hv2 : padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) ≤ padicValNat 2 (Nat.card D) :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hw_dvd_D
  exact le_antisymm hv1 hv2

theorem padicValNat_two_card_eq_width_aux [hDnorm : NormalizesSet ⊤ D]
    (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsOddTransp D) (S : Sylow 2 G) :
    padicValNat 2 (Nat.card D) = padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) := by
  classical
  have hDne : Nat.card D ≠ 0 := by
    obtain ⟨d₀, rfl⟩ := hcl
    exact Nat.card_ne_zero.mpr ⟨⟨d₀, IsConj.refl d₀⟩, inferInstance⟩
  have hneD : Nonempty ↥D := Nat.card_ne_zero.mp hDne |>.1
  have hpre : IsPretransitive G ↥D := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isClass hcl x.2 y.2)
    exact ⟨g, by apply Subtype.ext; change g * (x : G) * g⁻¹ = (y : G); exact hg⟩
  let E : Set G := (S : Set G) ∩ D
  let N : Subgroup G := Subgroup.normalizer E
  have hN : NormalizesSet N E :=
    ⟨fun n hn x hx => (Subgroup.mem_set_normalizer_iff.mp hn x).1 hx⟩
  have hNexp : NormalizesSet (Subgroup.normalizer ((S : Set G) ∩ D)) ((S : Set G) ∩ D) := by
    simpa [N, E] using hN
  exact padicValNat_two_card_eq_width_of_normalizes (hN := hNexp) hcl hD S hpre hneD

theorem padicValNat_two_card_eq_width (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsOddTransp D) (S : Sylow 2 G) :
    padicValNat 2 (Nat.card D) = padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) := by
  have hDnorm : NormalizesSet ⊤ D :=
    ⟨fun g _ x hx => CFSG.Timmesfeld.conj_mem_of_isClass hcl g hx⟩
  exact padicValNat_two_card_eq_width_aux (hDnorm := hDnorm) hcl hD S

theorem card_modEq_two_part_width (hcl : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsOddTransp D) (S : Sylow 2 G) :
    Nat.card D ≡ 2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D))
      [MOD 2 ^ (padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) + 1)] := by
  classical
  have hDne : Nat.card D ≠ 0 := by
    obtain ⟨d₀, rfl⟩ := hcl
    exact Nat.card_ne_zero.mpr ⟨⟨d₀, IsConj.refl d₀⟩, inferInstance⟩
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hDne
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hm
    omega
  have hk : k = padicValNat 2 (Nat.card D) := by
    have hval : padicValNat 2 (Nat.card D) = k := by
      rw [hkm, padicValNat.mul (pow_ne_zero _ (by norm_num)) hm0,
        padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (Odd.not_two_dvd_nat hm)]
      omega
    omega
  have hv := padicValNat_two_card_eq_width hcl hD S
  have hDeq : Nat.card D =
      2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D)) * m := by
    rw [hkm, hk, hv]
  rw [hDeq]
  have hm1 : m ≡ 1 [MOD 2] := by
    rw [Nat.ModEq, Nat.odd_iff.mp hm]
  have hmul := Nat.ModEq.mul_left'
    (2 ^ padicValNat 2 (Nat.card ↥((S : Set G) ∩ D))) hm1
  simpa [pow_succ] using hmul

end CFSG.OddTranspositions.PartThree
