module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.5 from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_prime_mem_and_rank_le_two_of_not_sigma_prime_order
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (hXcard : Nat.card X = p.val) (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    p ∈ subgroupPrimeSet M ∧ primeRank p.val M ≤ 2 := by
  have hXleM : X ≤ M := Subgroup.le_normalizer.trans hNX
  have hpX : p.val ∣ Nat.card X := by
    rw [hXcard]
  have hpM : p ∈ subgroupPrimeSet M :=
    hpX.trans (Subgroup.card_dvd_of_le hXleM)
  have hp_not_alpha : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hpσ (section10_alpha_subset_sigma hM hpα)
  have hrank_le : primeRank p.val M ≤ 2 := by
    by_contra hnot
    have hgt : 2 < primeRank p.val M := by omega
    exact hp_not_alpha ⟨hpM, hgt⟩
  exact ⟨hpM, hrank_le⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq_pre
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_two_le_primeRank_of_elementaryAbelian_card_p_sq_pre
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    {A : Subgroup R} (hAcard : Nat.card A = p ^ 2)
    (hAelem : IsElementaryAbelian p A) :
    2 ≤ primeRank p R := by
  letI : IsElementaryAbelian p A := hAelem
  have hAgen : 2 ≤ generatorRank A :=
    section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq_pre
      (p := p) (A := A) hAcard
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section10_generatorRank_le_natCard_pre B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A, IsElementaryAbelian.isPGroup p A, inferInstance, hAgen⟩

omit [IsMinCE G] in
public theorem CFSG.section10_sylow_isCyclic_of_primeRank_le_one
    {M : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M)
    (hpodd : p.val ≠ 2) (hrank : primeRank p.val M ≤ 1) :
    IsCyclic P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  by_contra hPnoncyc
  haveI : Fact (IsPGroup p.val P) := ⟨P.isPGroup'⟩
  obtain ⟨E, _hEnorm, hEcard, hEelem⟩ :=
    lemma_4_5_a (R := P) (p := p.val) hpodd hPnoncyc
  let EM : Subgroup M := E.map (P : Subgroup M).subtype
  have hEMcard : Nat.card EM = p.val ^ 2 := by
    calc
      Nat.card EM = Nat.card E := by
        exact Subgroup.card_map_of_injective
          (K := E) (f := (P : Subgroup M).subtype) (P : Subgroup M).subtype_injective
      _ = p.val ^ 2 := hEcard
  have hEMelem : IsElementaryAbelian p.val EM := by
    letI : IsElementaryAbelian p.val E := hEelem
    simpa [EM] using
      section10_isElementaryAbelian_map_pre
        (G := P) (p := p.val) (A := E) (G' := M) (P : Subgroup M).subtype
  have htwo : 2 ≤ primeRank p.val M :=
    section10_two_le_primeRank_of_elementaryAbelian_card_p_sq_pre
      (R := M) (p := p.val) hEMcard hEMelem
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_characteristic_of_subgroup_of_isCyclic_pre
    {H : Type*} [Group H] {K : Subgroup H} [IsCyclic H] :
    K.Characteristic := by
  classical
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hK_le_z : K ≤ Subgroup.zpowers g := by
    intro x _hx
    exact hg x
  obtain ⟨n, hK_eq⟩ := (Subgroup.le_zpowers_iff g K).mp hK_le_z
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  rw [hK_eq] at hx ⊢
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨k, rfl⟩
  rw [map_zpow]
  apply Subgroup.zpow_mem
  rw [map_pow]
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic φ.toMonoidHom
  rw [hm g]
  have hpow : (g ^ m) ^ n = (g ^ n) ^ m := by
    rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast]
  rw [hpow]
  exact (Subgroup.zpowers (g ^ n)).zpow_mem (Subgroup.mem_zpowers (g ^ n)) m

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
    (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, by simp⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1_isElementaryAbelian_of_commutative_pre
    {p : ℕ} [Fact p.Prime]
    (H : Type*) [Group H] [IsMulCommutative H] :
    IsElementaryAbelian p (omega₁ (G := H) (p := p)) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : H | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy)
      (by simp)
      (by
        intro a b _ha _hb hpa hpb
        have hab : Commute a b :=
          (commute_iff_eq a b).2
            ((IsMulCommutative.is_comm (M := H)).comm a b)
        calc
          (a * b) ^ p = a ^ p * b ^ p := hab.mul_pow p
          _ = 1 := by simp [hpa, hpb])
      (by
        intro a _ha hpa
        rw [inv_pow, hpa, inv_one])
      x.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1Z_isElementaryAbelian_pre
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] :
    IsElementaryAbelian p (Ω₁Z p R) := by
  change IsElementaryAbelian p
    ((omega₁ (G := Subgroup.center R) (p := p)).map
      (Subgroup.center R).subtype)
  let Ωc : Subgroup (Subgroup.center R) := omega₁ (G := Subgroup.center R) (p := p)
  have hΩcelem : IsElementaryAbelian p Ωc := by
    letI : IsMulCommutative (Subgroup.center R) := inferInstance
    simpa [Ωc] using
      section10_omega1_isElementaryAbelian_of_commutative_pre
        (p := p) (Subgroup.center R)
  letI : IsElementaryAbelian p Ωc := hΩcelem
  refine
    { toIsMulCommutative := by
        simpa [Ωc] using
          (Subgroup.map_isMulCommutative (f := (Subgroup.center R).subtype) (H := Ωc))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
  let yΩ : Ωc := ⟨y, hy⟩
  have hypow : yΩ ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p Ωc) yΩ
  have hx_eq : ((x : Ω₁Z p R) : R) = ((yΩ : Ωc) : Subgroup.center R) := by
    simpa [yΩ] using hyx.symm
  simpa [hx_eq] using congrArg (fun z : Ωc => (((z : Ωc) : Subgroup.center R) : R)) hypow

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1Z_le_center_pre
    (p : ℕ) (R : Type*) [Group R] :
    Ω₁Z p R ≤ Subgroup.center R := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_omega1Z_characteristic_pre
    (p : ℕ) (R : Type*) [Group R] :
    (Ω₁Z p R).Characteristic := by
  let ZR : Subgroup R := Subgroup.center R
  let Ωc : Subgroup ZR := omega₁ (G := ZR) (p := p)
  have hZchar : ZR.Characteristic := Subgroup.centerCharacteristic
  letI : ZR.Characteristic := hZchar
  have hΩchar : Ωc.Characteristic := by
    simpa [Ωc] using omega₁_characteristic (G := ZR) (p := p)
  letI : Ωc.Characteristic := hΩchar
  simpa [Ω₁Z, ZR, Ωc] using
    characteristic_map_subtype_of_characteristic (G := R) ZR Ωc

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_of_prime_card_isCyclic_pre
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hcard : Nat.card H = p) :
    IsElementaryAbelian p H := by
  letI : CommGroup H := IsCyclic.commGroup
  refine
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  exact orderOf_dvd_iff_pow_eq_one.mp <| by
    simpa [hcard] using (orderOf_dvd_natCard x)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_isElementaryAbelian_sup_of_le_centralizer_pre
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H]
    {E C : Subgroup H}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set H)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  let s : Set H := (E : Set H) ∪ (C : Set H)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : H) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : H)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          have hclosure_comm : IsMulCommutative ↥(Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
          show y * z = z * y
          simpa using congrArg Subtype.val
            (hclosure_comm.is_comm.comm
              (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

omit [IsMinCE G] in
private theorem CFSG.section10_exists_rank_two_elementary_over_prime_order
    {M X : Subgroup G} {p : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (hXcard : Nat.card X = p.val) (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    ∃ A : Subgroup G, X ≤ A ∧ A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hXM : X ≤ M := Subgroup.le_normalizer.trans hNX
  have hXp : IsPGroup p.val X := by
    exact IsPGroup.of_card (p := p.val) (G := X) (n := 1) (by simp [hXcard])
  let XM : Subgroup M := X.subgroupOf M
  have hXM_p : IsPGroup p.val XM :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXM).symm
  obtain ⟨P, hXM_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hXM_p
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hXPG : X ≤ PG := by
    intro x hx
    let xM : M := ⟨x, hXM hx⟩
    have hxM : xM ∈ XM := hx
    exact Subgroup.mem_map.mpr ⟨xM, hXM_le_P hxM, rfl⟩
  have hPG_le_M : PG ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcard_one : Nat.card X = 1 := (Subgroup.card_eq_one (H := X)).2 hXbot
    exact p.property.ne_one (by simpa [hXcard] using hcard_one)
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    exact hXne <| le_bot_iff.mp <| hXPG.trans (le_of_eq hPGbot)
  letI : Nontrivial PG := (Subgroup.nontrivial_iff_ne_bot PG).2 hPGne
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    simpa using
      IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  let Z : Subgroup G := section10OmegaOneCenter p PG
  have hZ_ne_bot : Z ≠ ⊥ := by
    have hZ_nontrivial : Nontrivial (Subgroup.center PG) := hPGp.center_nontrivial
    have hpdvd_center : p.val ∣ Nat.card (Subgroup.center PG) := by
      have hcenter_p : IsPGroup p.val (Subgroup.center PG) :=
        hPGp.to_subgroup (Subgroup.center PG)
      rcases (IsPGroup.nontrivial_iff_card
          (p := p.val) (G := Subgroup.center PG) (hG := hcenter_p)).1 hZ_nontrivial with
        ⟨n, hn, hcard⟩
      rw [hcard]
      exact dvd_pow_self p.val (Nat.ne_of_gt hn)
    have hΩlocal_ne_bot : Ω₁Z p.val PG ≠ ⊥ := by
      simpa [Ω₁Z] using
        omega₁_map_subtype_ne_bot (M := Subgroup.center PG) (p := p.val) hpdvd_center
    simpa [Z, section10OmegaOneCenter] using
      section10_map_subtype_ne_bot_of_ne_bot (G := G) (M := PG) hΩlocal_ne_bot
  have hZ_not_le_X : ¬ Z ≤ X := by
    intro hZX
    have hZ_eq_X : Z = X := by
      apply le_antisymm hZX
      have hZsub_ne_bot : Z.subgroupOf X ≠ ⊥ := by
        intro hbot
        apply hZ_ne_bot
        apply le_bot_iff.mp
        intro z hz
        have hzsub : (⟨z, hZX hz⟩ : X) ∈ Z.subgroupOf X := hz
        have hzbot : (⟨z, hZX hz⟩ : X) ∈ (⊥ : Subgroup X) := by simpa [hbot] using hzsub
        simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzbot)
      haveI : Fact (Nat.card X).Prime := ⟨by simpa [hXcard] using p.property⟩
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z.subgroupOf X) with hbot | htop
      · exact False.elim (hZsub_ne_bot hbot)
      · intro x hx
        have hxsub : (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) := by simp
        rw [← htop] at hxsub
        change x ∈ Z at hxsub
        exact hxsub
    have hΩchar : (Ω₁Z p.val PG).Characteristic :=
      section10_omega1Z_characteristic_pre p.val PG
    letI : (Ω₁Z p.val PG).Characteristic := hΩchar
    have hnormPG_le_normZ :
        Subgroup.normalizer (PG : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
      have hnorm :=
        section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
          (G := G) PG (Ω₁Z p.val PG)
      simpa [Z, section10OmegaOneCenter] using hnorm
    have hnormPG_le_M : Subgroup.normalizer (PG : Set G) ≤ M := by
      intro g hg
      exact hNX (by simpa [hZ_eq_X] using hnormPG_le_normZ hg)
    have hpM : p ∈ subgroupPrimeSet M := by
      have hpX : p.val ∣ Nat.card X := by rw [hXcard]
      exact hpX.trans (Subgroup.card_dvd_of_le hXM)
    exact hpσ ⟨hpM, P, by simpa [PG] using hnormPG_le_M⟩
  obtain ⟨z, hzZ, hzX⟩ := Set.not_subset.mp hZ_not_le_X
  have hzZ' : z ∈ (Ω₁Z p.val PG).map PG.subtype := by
    simpa [Z, section10OmegaOneCenter] using hzZ
  rcases Subgroup.mem_map.mp hzZ' with ⟨zPG, hzΩ, hz_eq⟩
  subst z
  let XPG : Subgroup PG := X.subgroupOf PG
  have hzPG_not_XPG : zPG ∉ XPG := by
    intro hz
    change (zPG : G) ∈ X at hz
    exact hzX hz
  let S : Subgroup PG := Subgroup.zpowers zPG
  have hzPG_ne_one : zPG ≠ 1 := by
    intro hz1
    exact hzPG_not_XPG (by simp [XPG, hz1])
  have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val PG) :=
    section10_omega1Z_isElementaryAbelian_pre (p := p.val) PG
  have hzpow : zPG ^ p.val = 1 := by
    letI : IsElementaryAbelian p.val (Ω₁Z p.val PG) := hΩelem
    exact elemPow_eq_one_of_isElementaryAbelian zPG hzΩ
  have hScard : Nat.card S = p.val := by
    calc
      Nat.card S = orderOf zPG := by simp [S]
      _ = p.val := orderOf_eq_prime hzpow hzPG_ne_one
  have hS_le_center : S ≤ Subgroup.center PG := by
    refine (Subgroup.zpowers_le).2 ?_
    exact section10_omega1Z_le_center_pre p.val PG hzΩ
  have hSnormal : S.Normal := by
    refine ⟨?_⟩
    intro s hs g
    have hscent : s ∈ Subgroup.center PG := hS_le_center hs
    have hconj : g * s * g⁻¹ = s := by
      have hmul : g * s = s * g := (Subgroup.mem_center_iff.mp hscent) g
      calc
        g * s * g⁻¹ = s * g * g⁻¹ := by rw [hmul]
        _ = s := by simp [mul_assoc]
    simpa [hconj] using hs
  have hXPGcard : Nat.card XPG = p.val := by
    simpa [XPG, hXcard] using natCard_subgroupOf_eq X PG hXPG
  have hXPGelem : IsElementaryAbelian p.val XPG := by
    have hcyc : IsCyclic XPG := isCyclic_of_prime_card hXPGcard
    letI : IsCyclic XPG := hcyc
    exact section10_isElementaryAbelian_of_prime_card_isCyclic_pre
      (p := p.val) (H := XPG) hXPGcard
  have hSelem : IsElementaryAbelian p.val S := by
    have hcyc : IsCyclic S := isCyclic_of_prime_card hScard
    letI : IsCyclic S := hcyc
    exact section10_isElementaryAbelian_of_prime_card_isCyclic_pre
      (p := p.val) (H := S) hScard
  have hdisj : Disjoint S XPG := by
    rw [Subgroup.disjoint_def]
    intro y hyS hyX
    by_contra hyne
    have hXsub_ne_bot : XPG.subgroupOf S ≠ ⊥ := by
      intro hbot
      have hysub : (⟨y, hyS⟩ : S) ∈ XPG.subgroupOf S := hyX
      have hybot : (⟨y, hyS⟩ : S) ∈ (⊥ : Subgroup S) := by simpa [hbot] using hysub
      exact hyne (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hybot))
    haveI : Fact (Nat.card S).Prime := ⟨by simpa [hScard] using p.property⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (XPG.subgroupOf S) with hbot | htop
    · exact False.elim (hXsub_ne_bot hbot)
    · have hzS : zPG ∈ S := Subgroup.mem_zpowers zPG
      have hzX : zPG ∈ XPG := by
        have hzsub : (⟨zPG, hzS⟩ : S) ∈ (⊤ : Subgroup S) := by simp
        rw [← htop] at hzsub
        change zPG ∈ XPG at hzsub
        exact hzsub
      exact hzPG_not_XPG hzX
  let A0 : Subgroup PG := S ⊔ XPG
  have hX_le_centS : XPG ≤ Subgroup.centralizer (S : Set PG) := by
    exact (Subgroup.le_centralizer_iff).mp
      (hS_le_center.trans (Subgroup.center_le_centralizer (XPG : Set PG)))
  have hA0elem : IsElementaryAbelian p.val A0 := by
    letI : IsElementaryAbelian p.val S := hSelem
    letI : IsElementaryAbelian p.val XPG := hXPGelem
    simpa [A0] using
      section10_isElementaryAbelian_sup_of_le_centralizer_pre
        (p := p.val) (E := S) (C := XPG) hX_le_centS
  have hA0card : Nat.card A0 = p.val ^ 2 := by
    have hcomp :
        (S.subgroupOf A0).IsComplement' (XPG.subgroupOf A0) := by
      letI : S.Normal := hSnormal
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [Subgroup.disjoint_def]
        intro y hyS hyX
        apply Subtype.ext
        exact Subgroup.disjoint_def.mp hdisj hyS hyX
      · rw [Set.eq_univ_iff_forall]
        intro y
        rcases (Subgroup.mem_sup_of_normal_left
            (x := (y : PG)) (s := S) (t := XPG)).1 y.2 with
          ⟨s, hsS, x, hxX, hsx⟩
        let sA : S.subgroupOf A0 := ⟨⟨s, Subgroup.mem_sup_left hsS⟩, hsS⟩
        let xA : XPG.subgroupOf A0 := ⟨⟨x, Subgroup.mem_sup_right hxX⟩, hxX⟩
        refine ⟨(sA : A0), sA.2, (xA : A0), xA.2, ?_⟩
        apply Subtype.ext
        simpa using hsx
    have hmul := hcomp.card_mul
    rw [natCard_subgroupOf_eq S A0 le_sup_left,
      natCard_subgroupOf_eq XPG A0 le_sup_right, hScard, hXPGcard] at hmul
    simpa [A0, pow_two] using hmul.symm
  let A : Subgroup G := A0.map PG.subtype
  have hAcard : Nat.card A = p.val ^ 2 := by
    calc
      Nat.card A = Nat.card A0 := by
        exact Subgroup.card_map_of_injective (K := A0) (f := PG.subtype) PG.subtype_injective
      _ = p.val ^ 2 := hA0card
  have hAelem : IsElementaryAbelian p.val A := by
    letI : IsElementaryAbelian p.val A0 := hA0elem
    simpa [A] using
      section10_isElementaryAbelian_map_pre
        (G := PG) (p := p.val) (A := A0) (G' := G) PG.subtype
  have hX_le_A : X ≤ A := by
    intro x hx
    let xPG : PG := ⟨x, hXPG hx⟩
    have hxXPG : xPG ∈ XPG := hx
    have hxA0 : xPG ∈ A0 := Subgroup.mem_sup_right hxXPG
    exact Subgroup.mem_map.mpr ⟨xPG, hxA0, rfl⟩
  exact ⟨A, hX_le_A, ⟨hAcard, hAelem⟩⟩

private theorem CFSG.section10_primeRank_eq_two_of_prime_order_normalizer_le_not_sigma
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (hXcard : Nat.card X = p.val) (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    primeRank p.val M = 2 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases section10_prime_mem_and_rank_le_two_of_not_sigma_prime_order
      (G := G) hM hpσ hXcard hNX with
    ⟨hpM, hrank_le_two⟩
  have hXM : X ≤ M := Subgroup.le_normalizer.trans hNX
  have hp_dvd_G : p.val ∣ Nat.card G := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact (hpX.trans (Subgroup.card_dvd_of_le hXM)).trans
      (Subgroup.card_subgroup_dvd_card M)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  have hnot_le_one : ¬ primeRank p.val M ≤ 1 := by
    intro hrank_le_one
    have hXp : IsPGroup p.val X := by
      exact IsPGroup.of_card (p := p.val) (G := X) (n := 1) (by simp [hXcard])
    let XM : Subgroup M := X.subgroupOf M
    have hXM_p : IsPGroup p.val XM :=
      hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXM).symm
    obtain ⟨P, hXM_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hXM_p
    let PG : Subgroup G := section10AmbientSylowSubgroup M P
    have hXPG : X ≤ PG := by
      intro x hx
      let xM : M := ⟨x, hXM hx⟩
      have hxM : xM ∈ XM := hx
      exact Subgroup.mem_map.mpr ⟨xM, hXM_le_P hxM, rfl⟩
    have hPcyc : IsCyclic P :=
      section10_sylow_isCyclic_of_primeRank_le_one
        (G := G) (M := M) (p := p) P hpodd hrank_le_one
    have hPGcyc : IsCyclic PG := by
      let e : P ≃* PG :=
        Subgroup.equivMapOfInjective (P : Subgroup M) M.subtype M.subtype_injective
      exact e.isCyclic.1 hPcyc
    let XPG : Subgroup PG := X.subgroupOf PG
    have hXPGchar : XPG.Characteristic := by
      letI : IsCyclic PG := hPGcyc
      exact section10_characteristic_of_subgroup_of_isCyclic_pre (K := XPG)
    letI : XPG.Characteristic := hXPGchar
    have hnormPG_le_normX :
        Subgroup.normalizer (PG : Set G) ≤ Subgroup.normalizer (X : Set G) := by
      have hnorm :=
        section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
          (G := G) PG XPG
      have hmap : (XPG.map PG.subtype : Subgroup G) = X := by
        simpa [XPG] using (Subgroup.map_subgroupOf_eq_of_le hXPG)
      simpa [XPG, hmap] using hnorm
    have hnormPG_le_M : Subgroup.normalizer (PG : Set G) ≤ M :=
      hnormPG_le_normX.trans hNX
    exact hpσ ⟨hpM, P, by simpa [PG] using hnormPG_le_M⟩
  omega

/-- Lemma 10.5. -/
public theorem CFSG.lemma_10_5
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpσ : p ∉ section10SigmaPrimes M)
    (hXcard : Nat.card X = p.val) (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    primeRank p.val M = 2 ∧
      ¬ section10IdealPrime p G ∧
      ∃ A : Subgroup G, X ≤ A ∧ A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
  classical
  have hprank : primeRank p.val M = 2 :=
    section10_primeRank_eq_two_of_prime_order_normalizer_le_not_sigma
      (G := G) hM hpσ hXcard hNX
  have hnotIdeal : ¬ section10IdealPrime p G := (lemma_10_4_c hM hpσ hprank).1
  have hA :
      ∃ A : Subgroup G, X ≤ A ∧ A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
    section10_exists_rank_two_elementary_over_prime_order
      (G := G) hM hpσ hXcard hNX
  exact ⟨hprank, hnotIdeal, hA⟩

end Section10
