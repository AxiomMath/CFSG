module

public import CFSG.OddTranspositions.PartThree.EightOne.Bender
public import CFSG.Timmesfeld.Bridge.Asc72Central
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Bridge.Asc72Width
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.GH74.Uniqueness.Bender

theorem not_mem_of_isBenderGroup_quotient {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) {u : X} (hu : u ∈ D) : u ∉ E := by
  intro huE
  have hDsub : D ⊆ E := by
    rcases hS.subset_or_disjoint E with h | h
    · exact h
    · exact absurd huE (h u hu)
  have hEtop : E = ⊤ := hS.eq_top_of_subset E hDsub
  haveI : Nontrivial (X ⧸ E) := (IsBenderGroup.isSimpleGroup hB).toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ E)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective E a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E b
  exact hab (QuotientGroup.eq.mpr (hEtop ▸ Subgroup.mem_top (x⁻¹ * y)))

theorem orderOf_mk'_eq_two {X : Type} [Group X] {E : Subgroup X} [E.Normal] {g : X}
    (hg : g * g = 1) (hgE : g ∉ E) : orderOf (QuotientGroup.mk' E g) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_two, hg, map_one]
  · intro h1
    exact hgE ((QuotientGroup.eq_one_iff g).mp h1)

theorem exists_mem_D_of_mk_eq_two {X : Type} [Group X] [Finite X] {D : Set X} (hS : Setup X D)
    {E : Subgroup X} [E.Normal] (hB : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) {u : X}
    (hu : u ∈ D) {s : X ⧸ E} (hs : orderOf s = 2) :
    ∃ d ∈ D, QuotientGroup.mk' E d = s := by
  have huE : u ∉ E := not_mem_of_isBenderGroup_quotient hS hB hu
  have htu : orderOf (QuotientGroup.mk' E u) = 2 :=
    orderOf_mk'_eq_two (hS.oddT.mul_self_eq_one hu) huE
  obtain ⟨c, hc⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB htu hs)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E c
  refine ⟨g * u * g⁻¹, hS.conj_mem g hu, ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hc

theorem mem_commSet_of_mk_commute {X : Type} [Group X] {D : Set X} (hS : Setup X D)
    {E : Subgroup X} [E.Normal] {u d : X} (hu : u ∈ D) (hd : d ∈ D)
    (hc : Commute (QuotientGroup.mk' E d) (QuotientGroup.mk' E u))
    (hne : QuotientGroup.mk' E d ≠ QuotientGroup.mk' E u) : d ∈ commSet D u := by
  have hd2 : (QuotientGroup.mk' E d) * (QuotientGroup.mk' E d) = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hd, map_one]
  have hu2 : (QuotientGroup.mk' E u) * (QuotientGroup.mk' E u) = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hu, map_one]
  have hprod2 : ((QuotientGroup.mk' E d) * (QuotientGroup.mk' E u)) ^ 2 = 1 := by
    rw [pow_two, hc.symm.mul_mul_mul_comm (QuotientGroup.mk' E d) (QuotientGroup.mk' E u),
      hd2, hu2, mul_one]
  have hprod1 : (QuotientGroup.mk' E d) * (QuotientGroup.mk' E u) ≠ 1 := by
    intro h
    apply hne
    calc (QuotientGroup.mk' E d) = (QuotientGroup.mk' E d) * 1 := (mul_one _).symm
      _ = (QuotientGroup.mk' E d) * ((QuotientGroup.mk' E u) * (QuotientGroup.mk' E u)) := by
          rw [hu2]
      _ = ((QuotientGroup.mk' E d) * (QuotientGroup.mk' E u)) * (QuotientGroup.mk' E u) := by
          rw [mul_assoc]
      _ = 1 * (QuotientGroup.mk' E u) := by rw [h]
      _ = QuotientGroup.mk' E u := one_mul _
  refine ⟨hd, ?_, ?_⟩
  · rcases hS.oddT.commute_or_odd hd hu with h | hodd
    · exact h
    · exfalso
      have h2 : orderOf ((QuotientGroup.mk' E d) * (QuotientGroup.mk' E u)) = 2 :=
        orderOf_eq_prime hprod2 hprod1
      have hdvd : 2 ∣ orderOf (d * u) := by
        have h := orderOf_map_dvd (QuotientGroup.mk' E) (d * u)
        rwa [map_mul, h2] at h
      exact hodd.not_two_dvd_nat hdvd
  · intro h
    exact hne (by rw [h])

theorem exists_commSet_of_two_factors {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) {u : X} (hu : u ∈ D) {s1 s2 : X ⧸ E}
    (ho1 : orderOf s1 = 2) (ho2 : orderOf s2 = 2)
    (hc1 : Commute s1 (QuotientGroup.mk' E u)) (hc2 : Commute s2 (QuotientGroup.mk' E u))
    (hne1 : s1 ≠ QuotientGroup.mk' E u) (hne2 : s2 ≠ QuotientGroup.mk' E u) :
    ∃ d1 d2 : X, d1 ∈ commSet D u ∧ d2 ∈ commSet D u ∧
      QuotientGroup.mk' E d1 = s1 ∧ QuotientGroup.mk' E d2 = s2 := by
  obtain ⟨d1, hd1D, hd1⟩ := exists_mem_D_of_mk_eq_two hS hB hu ho1
  obtain ⟨d2, hd2D, hd2⟩ := exists_mem_D_of_mk_eq_two hS hB hu ho2
  exact ⟨d1, d2,
    mem_commSet_of_mk_commute hS hu hd1D (by rw [hd1]; exact hc1) (by rw [hd1]; exact hne1),
    mem_commSet_of_mk_commute hS hu hd2D (by rw [hd2]; exact hc2) (by rw [hd2]; exact hne2),
    hd1, hd2⟩

theorem exists_commSet_of_three_factors {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) {u : X} (hu : u ∈ D) {s1 s2 s3 : X ⧸ E}
    (ho1 : orderOf s1 = 2) (ho2 : orderOf s2 = 2) (ho3 : orderOf s3 = 2)
    (hc1 : Commute s1 (QuotientGroup.mk' E u)) (hc2 : Commute s2 (QuotientGroup.mk' E u))
    (hc3 : Commute s3 (QuotientGroup.mk' E u))
    (hne1 : s1 ≠ QuotientGroup.mk' E u) (hne2 : s2 ≠ QuotientGroup.mk' E u)
    (hne3 : s3 ≠ QuotientGroup.mk' E u) :
    ∃ d1 d2 d3 : X, d1 ∈ commSet D u ∧ d2 ∈ commSet D u ∧ d3 ∈ commSet D u ∧
      QuotientGroup.mk' E d1 = s1 ∧ QuotientGroup.mk' E d2 = s2 ∧
      QuotientGroup.mk' E d3 = s3 := by
  obtain ⟨d1, hd1D, hd1⟩ := exists_mem_D_of_mk_eq_two hS hB hu ho1
  obtain ⟨d2, hd2D, hd2⟩ := exists_mem_D_of_mk_eq_two hS hB hu ho2
  obtain ⟨d3, hd3D, hd3⟩ := exists_mem_D_of_mk_eq_two hS hB hu ho3
  exact ⟨d1, d2, d3,
    mem_commSet_of_mk_commute hS hu hd1D (by rw [hd1]; exact hc1) (by rw [hd1]; exact hne1),
    mem_commSet_of_mk_commute hS hu hd2D (by rw [hd2]; exact hc2) (by rw [hd2]; exact hne2),
    mem_commSet_of_mk_commute hS hu hd3D (by rw [hd3]; exact hc3) (by rw [hd3]; exact hne3),
    hd1, hd2, hd3⟩

theorem mem_closure_of_two_factors {X : Type} [Group X] {D : Set X} {E : Subgroup X} [E.Normal]
    {u d1 d2 : X} (hcd1 : d1 ∈ commSet D u) (hcd2 : d2 ∈ commSet D u)
    (hmul : QuotientGroup.mk' E d1 * QuotientGroup.mk' E d2 = QuotientGroup.mk' E u)
    (hbot : E = ⊥) : u ∈ Subgroup.closure (commSet D u) := by
  have hπ : QuotientGroup.mk' E (d1 * d2) = QuotientGroup.mk' E u := by
    rw [map_mul, hmul]
  have hmem : u⁻¹ * (d1 * d2) ∈ E := by
    have h1 : QuotientGroup.mk' E (u⁻¹ * (d1 * d2)) = 1 := by
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (u⁻¹ * (d1 * d2))).mp h1
  rw [hbot, Subgroup.mem_bot] at hmem
  have hueq : u = d1 * d2 := inv_mul_eq_one.mp hmem
  have hprod : d1 * d2 ∈ Subgroup.closure (commSet D u) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure hcd1) (Subgroup.subset_closure hcd2)
  rwa [← hueq] at hprod

theorem eq_mul_of_mk_eq {X : Type} [Group X] {D : Set X} (hS : Setup X D) {E : Subgroup X}
    [E.Normal] {u d1 d2 d3 : X} (hu : u ∈ D) (hd1 : d1 ∈ D) (hd2 : d2 ∈ D) (hd3 : d3 ∈ D)
    (hπ : QuotientGroup.mk' E (d1 * d2 * d3) = QuotientGroup.mk' E u)
    (hinf : E ⊓ commutator X = ⊥) : u = d1 * d2 * d3 := by
  have heE : u * (d1 * d2 * d3)⁻¹ ∈ E := by
    have h1 : QuotientGroup.mk' E (u * (d1 * d2 * d3)⁻¹) = 1 := by
      rw [map_mul, map_inv, hπ, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (u * (d1 * d2 * d3)⁻¹)).mp h1
  have heC : u * (d1 * d2 * d3)⁻¹ ∈ commutator X := by
    rw [← Abelianization.ker_of X, MonoidHom.mem_ker]
    have hcc : Abelianization.of u * Abelianization.of u = 1 := by
      rw [← map_mul, hS.oddT.mul_self_eq_one hu, map_one]
    have huw : Abelianization.of (d1 * d2 * d3) = Abelianization.of u := by
      rw [map_mul, map_mul, hS.abelianization_eq hd1 hu, hS.abelianization_eq hd2 hu,
        hS.abelianization_eq hd3 hu, hcc, one_mul]
    rw [map_mul, map_inv, huw, mul_inv_cancel]
  have hebot : u * (d1 * d2 * d3)⁻¹ = 1 := by
    have hmem : u * (d1 * d2 * d3)⁻¹ ∈ E ⊓ commutator X :=
      Subgroup.mem_inf.mpr ⟨heE, heC⟩
    rwa [hinf, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hebot

theorem mem_closure_of_three_factors {X : Type} [Group X] {D : Set X} {u d1 d2 d3 : X}
    (hcd1 : d1 ∈ commSet D u) (hcd2 : d2 ∈ commSet D u) (hcd3 : d3 ∈ commSet D u)
    (hueq : u = d1 * d2 * d3) : u ∈ Subgroup.closure (commSet D u) := by
  have hw : d1 * d2 * d3 ∈ Subgroup.closure (commSet D u) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hcd1)
      (Subgroup.subset_closure hcd2)) (Subgroup.subset_closure hcd3)
  rwa [← hueq] at hw

theorem mem_closure_commSet_of_benderType {X : Type} [Group X]
    [Finite X] {D : Set X} (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hEc : E ≤ Subgroup.center X) (hE2 : IsPGroup 2 E) {n i e : ℕ}
    (hB : BenderType (X ⧸ E) n i e) (hn : E = ⊥ ∨ 3 ≤ n) {u : X} (hu : u ∈ D) :
    u ∈ Subgroup.closure (commSet D u) := by
  have hBX : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E) :=
    isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, hB⟩
  have huE : u ∉ E := not_mem_of_isBenderGroup_quotient hS hBX hu
  have htu : orderOf (QuotientGroup.mk' E u) = 2 :=
    orderOf_mk'_eq_two (hS.oddT.mul_self_eq_one hu) huE
  rcases hn with hbot | hn3
  · obtain ⟨s1, s2, ho1, ho2, hc1, hc2, hne1, hne2, hmul⟩ :=
      (exists_mul_eq_of_benderType hB htu).1
    obtain ⟨d1, d2, hcd1, hcd2, hd1, hd2⟩ :=
      exists_commSet_of_two_factors hS hBX hu ho1 ho2 hc1 hc2 hne1 hne2
    exact mem_closure_of_two_factors hcd1 hcd2 (by rw [hd1, hd2]; exact hmul) hbot
  · obtain ⟨s1, s2, s3, ho1, ho2, ho3, hc1, hc2, hc3, hne1, hne2, hne3, hmul3⟩ :=
      (exists_mul_eq_of_benderType hB htu).2 hn3
    obtain ⟨d1, d2, d3, hcd1, hcd2, hcd3, hd1, hd2, hd3⟩ :=
      exists_commSet_of_three_factors hS hBX hu ho1 ho2 ho3 hc1 hc2 hc3 hne1 hne2 hne3
    have hπ : QuotientGroup.mk' E (d1 * d2 * d3) = QuotientGroup.mk' E u := by
      rw [map_mul, map_mul, hd1, hd2, hd3, hmul3]
    have hinf : E ⊓ commutator X = ⊥ :=
      inf_commutator_eq_bot_of_isBenderGroup hS hEc hE2 hBX
    exact mem_closure_of_three_factors hcd1 hcd2 hcd3
      (eq_mul_of_mk_eq hS hu hcd1.1 hcd2.1 hcd3.1 hπ hinf)

theorem nonempty_mulEquiv_prod_of_ne_bot {X : Type} [Group X]
    [Finite X] {D : Set X} (hS : Setup X D) {E : Subgroup X} [E.Normal]
    (hEc : E ≤ Subgroup.center X) (hE2 : IsPGroup 2 E)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ E)) (hE : E ≠ ⊥) :
    Nonempty (X ≃* Multiplicative (ZMod 2) × (X ⧸ E)) := by
  have hcardE : Nat.card E = 2 := by
    have h1 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hE
    have h2 : Nat.card E ≤ 2 := card_le_two_of_isBenderGroup hS hEc hE2 hB
    omega
  have hcompl : IsCompl E (commutator X) :=
    isCompl_commutator_of_isBenderGroup hS hEc hE2 hB
  have hcomp : E.IsComplement' (commutator X) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint ?_
    rw [← Subgroup.normal_mul E (commutator X), hcompl.sup_eq_top]
    rfl
  have hcardQ : Nat.card (X ⧸ commutator X) = 2 := by
    rw [Nat.card_congr hcomp.QuotientMulEquiv.toEquiv, hcardE]
  have hcardM2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
  let e : X ⧸ commutator X ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hcardQ hcardM2
  let ψ : X →* Multiplicative (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (commutator X))
  have hψker : ψ.ker = commutator X := by
    ext x
    dsimp only [ψ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' : (QuotientGroup.mk' (commutator X)) x = 1 := by
        refine e.injective ?_
        simpa using h
      exact (QuotientGroup.eq_one_iff (N := commutator X) x).mp h'
    · have h' : (QuotientGroup.mk' (commutator X)) x = 1 :=
        (QuotientGroup.eq_one_iff (N := commutator X) x).mpr h
      rw [h', map_one]
  let φ : X →* Multiplicative (ZMod 2) × (X ⧸ E) := ψ.prod (QuotientGroup.mk' E)
  have hφker : φ.ker = ⊥ := by
    dsimp only [φ]
    rw [MonoidHom.ker_prod, hψker, QuotientGroup.ker_mk', inf_comm, hcompl.inf_eq_bot]
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  have hcard : Nat.card X = Nat.card (Multiplicative (ZMod 2) × (X ⧸ E)) := by
    rw [Nat.card_prod, hcardM2, Subgroup.card_eq_card_quotient_mul_card_subgroup E, hcardE,
      Nat.mul_comm (Nat.card (X ⧸ E)) 2]
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end CFSG.OddTranspositions.PartThree.EightOne
