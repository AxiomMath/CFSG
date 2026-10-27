module

public import CFSG.Quasithin.H13.NQCoreP134OutThree
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived

@[expose] def OutThreeSplit (X : Type*) [Group X] : Prop :=
  ∃ N : Subgroup X, N.Normal ∧
    (∀ V : Subgroup X, IsPGroup 3 V → ∃ v ∈ V, V ≤ Subgroup.zpowers v ⊔ N) ∧
    ∀ V : Subgroup X, V ≤ N → IsPGroup 3 V → IsCyclic V

section Split

variable {X Y : Type*} [Group X] [Group Y]

theorem le_zpowers_sup_comap (φ : X →* Y) {N : Subgroup Y} (hN : N.Normal) {U : Subgroup X}
    {u : X} (h : U.map φ ≤ Subgroup.zpowers (φ u) ⊔ N) :
    U ≤ Subgroup.zpowers u ⊔ N.comap φ := by
  intro x hx
  have hx' : φ x ∈ N ⊔ Subgroup.zpowers (φ u) := by
    rw [sup_comm]; exact h ⟨x, hx, rfl⟩
  have hNtop : ∀ K : Subgroup Y, K ≤ Subgroup.normalizer (N : Set Y) := fun K => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]; exact le_top
  obtain ⟨n, hn, y, hy, hxy⟩ := (mem_sup_iff_of_le_normalizer (hNtop _)).1 hx'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmem : x * u ^ (-k) ∈ N.comap φ := by
    rw [Subgroup.mem_comap, map_mul, map_zpow, ← hxy, mul_assoc, ← zpow_add, add_neg_cancel,
      zpow_zero, mul_one]
    exact hn
  have : x = x * u ^ (-k) * u ^ k := by group
  rw [this, sup_comm]
  exact Subgroup.mul_mem_sup hmem (Subgroup.zpow_mem_zpowers u k)

theorem outThreeSplit_of_isCyclic (h : ∀ V : Subgroup X, IsPGroup 3 V → IsCyclic V) :
    OutThreeSplit X := by
  refine ⟨⊥, Subgroup.normal_bot, fun V hV => ?_, fun V hV _ => ?_⟩
  · obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top V).mp (h V hV)
    have hgV : g ∈ V := by
      have := hg ▸ Subgroup.mem_zpowers g
      exact this
    refine ⟨g, hgV, fun x hx => ?_⟩
    have hx' : x ∈ Subgroup.zpowers g := hg.symm ▸ hx
    exact Subgroup.mem_sup_left hx'
  · rw [le_bot_iff] at hV
    subst hV
    exact isCyclic_of_subsingleton

theorem outThreeSplit_of_sylow [Finite X] (h : ∀ P : Sylow 3 X, IsCyclic P) :
    OutThreeSplit X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine outThreeSplit_of_isCyclic fun V hV => ?_
  obtain ⟨P, hP⟩ := hV.exists_le_sylow
  have := h P
  exact Subgroup.isCyclic_of_le hP

theorem outThreeSplit_of_card_le_four [Finite X] (h : Nat.card X ≤ 4) : OutThreeSplit X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine outThreeSplit_of_isCyclic fun V hV => ?_
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
  have hle : 3 ^ k ≤ 4 := hk ▸ (Subgroup.card_le_card_group V).trans h
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hk).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem outThreeSplit_of_injective (ι : X →* Y) (hι : Function.Injective ι)
    (h : OutThreeSplit Y) : OutThreeSplit X := by
  obtain ⟨N, hN, h1, h2⟩ := h
  refine ⟨N.comap ι, hN.comap ι, fun V hV => ?_, fun V hVN hV => ?_⟩
  · obtain ⟨w, hw, hle⟩ := h1 (V.map ι) (hV.map ι)
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, hv, le_zpowers_sup_comap ι hN hle⟩
  · have hc := h2 (V.map ι) (Subgroup.map_le_iff_le_comap.mpr hVN) (hV.map ι)
    exact isCyclic_of_injective (V.equivMapOfInjective ι hι).toMonoidHom
      (V.equivMapOfInjective ι hι).injective

theorem outThreeSplit_of_hom {Z : Type*} [Group Z] [IsCyclic Z] (F : X →* Z)
    (hker : ∀ V : Subgroup X, V ≤ F.ker → IsPGroup 3 V → IsCyclic V) : OutThreeSplit X := by
  refine ⟨F.ker, F.normal_ker, fun V _ => ?_, hker⟩
  have hc : IsCyclic (V.map F) := inferInstance
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (V.map F)).mp hc
  obtain ⟨v, hv, rfl⟩ : g ∈ V.map F := hg ▸ Subgroup.mem_zpowers g
  have h1 := le_zpowers_sup_comap F Subgroup.normal_bot (U := V) (u := v)
    (by rw [hg]; exact le_sup_left)
  rw [MonoidHom.comap_bot] at h1
  exact ⟨v, hv, h1⟩

theorem outThreeSplit_of_section [Finite X] {N M : Subgroup X} (hMn : M.Normal)
    (hNn : N.Normal) (hMi : M.index ≤ 2) (hcyc : IsCyclic (M ⧸ N.subgroupOf M))
    (hN : IsCyclic N) : OutThreeSplit X := by
  refine ⟨N, hNn, fun V hV => ?_, fun V hVN _ => Subgroup.isCyclic_of_le hVN⟩
  have hVM : V ≤ M := by
    intro v hv
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨a, ha⟩ := hV ⟨v, hv⟩
    have hva : v ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hodd : Odd (3 ^ a) := Odd.pow (by decide)
    obtain ⟨b, hb⟩ := hodd
    have hv2 : v ^ 2 ∈ M := by
      have hidx := Subgroup.pow_index_mem M v
      rcases (by have := M.index_ne_zero_of_finite; omega : M.index = 1 ∨ M.index = 2) with h | h
      · rw [Subgroup.index_eq_one.1 h]
        exact Subgroup.mem_top _
      · rwa [h] at hidx
    have h1 : v * (v ^ 2) ^ b = 1 := by
      rw [← pow_mul, ← pow_succ', show 2 * b + 1 = 3 ^ a from hb.symm, hva]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact M.inv_mem (M.pow_mem hv2 b)
  have : (N.subgroupOf M).Normal := hNn.subgroupOf M
  have : IsCyclic (M ⧸ N.subgroupOf M) := hcyc
  set V' : Subgroup M := V.subgroupOf M with hV'
  set q := QuotientGroup.mk' (N.subgroupOf M) with hq
  have hc : IsCyclic (V'.map q) := inferInstance
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (V'.map q)).mp hc
  obtain ⟨w, hw, rfl⟩ : g ∈ V'.map q := hg ▸ Subgroup.mem_zpowers g
  have h1 := le_zpowers_sup_comap q Subgroup.normal_bot (U := V') (u := w)
    (by rw [hg]; exact le_sup_left)
  rw [MonoidHom.comap_bot, hq, QuotientGroup.ker_mk'] at h1
  refine ⟨w, Subgroup.mem_subgroupOf.mp hw, fun x hx => ?_⟩
  have hx' : (⟨x, hVM hx⟩ : M) ∈ Subgroup.zpowers w ⊔ N.subgroupOf M :=
    h1 (Subgroup.mem_subgroupOf.mpr hx)
  have hx'' := Subgroup.mem_map_of_mem M.subtype hx'
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.subgroupOf_map_subtype] at hx''
  exact (sup_le_sup_left (inf_le_left : N ⊓ M ≤ N) (Subgroup.zpowers (w : X))) hx''

end Split

section Families

open Matrix CFSG.GorensteinWalter
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem outThreeSplit_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    OutThreeSplit (Outer (projectiveSL n K)) := by
  classical
  set π := QuotientGroup.mk' (inner (projectiveSL n K)) with hπ
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDR, hER, -, ⟨g, hgE, hg⟩, -, hEidx, -⟩ :=
    standard_outer_quotients (K := K) (n := n)
  have hnormal : ∀ X : Subgroup (MulAut (projectiveSL n K)),
      (X.subgroupOf (standardAutGroup n K)).Normal → X.Normal := by
    intro X hX
    constructor
    intro x hx y
    have := hX.conj_mem ⟨x, by rw [hR]; trivial⟩ (Subgroup.mem_subgroupOf.2 hx)
      ⟨y, by rw [hR]; trivial⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hDn := hnormal _ hDR
  have hEn := hnormal _ hER
  set N := (linearAutGroup n K).map π with hN
  set M := (semilinearAutGroup n K).map π with hM
  have hNM : N ≤ M := Subgroup.map_mono linearAutGroup_le_semilinearAutGroup
  have hMn : M.Normal := hEn.map π (QuotientGroup.mk'_surjective _)
  have hNn : N.Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ semilinearAutGroup n K := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hID.trans linearAutGroup_le_semilinearAutGroup
  have hMi : M.index ≤ 2 := by
    rw [hM, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker,
      ← Subgroup.relIndex_top_right, ← hR]
    exact hEidx
  have hcyc : IsCyclic (M ⧸ N.subgroupOf M) := by
    refine ⟨⟨QuotientGroup.mk ⟨π g, Subgroup.mem_map_of_mem π hgE⟩, fun x => ?_⟩⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨k, hk⟩ := hg e he
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk ⟨π g, _⟩ : M ⧸ N.subgroupOf M) ^ (-k) = QuotientGroup.mk ⟨π e, hy⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((⟨π g, Subgroup.mem_map_of_mem π hgE⟩ : M) ^ (-k))⁻¹ * ⟨π e, hy⟩ : M) =
        ⟨π (g ^ k * e), hNM (Subgroup.mem_map_of_mem π hk)⟩ := by
      ext
      simp [map_mul, map_zpow, _root_.zpow_neg]
    rw [h1]
    exact Subgroup.mem_map_of_mem π hk
  have hNcyc : IsCyclic N := by
    have hD : linearAutGroup n K = (LinearFlag.conjAut n K).range := by
      rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    have hNeq : N = (π.comp (LinearFlag.conjAut n K)).range := by
      rw [hN, hD, MonoidHom.range_comp]
    rw [hNeq]
    exact (linear_diagonal_outer (K := K) (n := n) (by omega)).1
  exact outThreeSplit_of_section hMn hNn hMi hcyc hNcyc

open CFSG.Quasithin.OuterPrimeControl CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem outThreeSplit_classical (J : Type) [Group J] [Finite J] [Group.IsPerfect J]
    (hSQT : CFSG.IsStronglyQuasithin (J ⧸ Subgroup.center J))
    (hrep : CFSG.Milestones.ClassicalRep (J ⧸ Subgroup.center J)) : OutThreeSplit (Outer J) := by
  have hS : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (J ⧸ Subgroup.center J)) ≤ 2 :=
    SectionRank.isStronglyQuasithin_iff.1 hSQT
  obtain ⟨t, n, p, f, hm⟩ := hrep
  have hp : p.Prime := hm.1.1
  have hf : 1 ≤ f := hm.1.2.1
  have hodd : p ≠ 2 → t = .PSL ∨ t = .PSU := fun hp2 => by
    rcases SectionRank.sqt_odd_classical_restriction hS hp2 hm with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact .inl ht
    · exact .inl ht
    · exact .inr ht
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  cases t with
  | PSL =>
    obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
    ·
      have hnd : ¬ 3 ∣ Nat.gcd 2 (Nat.card K - 1) := by
        intro h3
        have := Nat.le_of_dvd (by norm_num) (h3.trans (Nat.gcd_dvd_left _ _))
        omega
      exact outThreeSplit_of_sylow
        ((perfect_projective_linear_central_quotient_outer_prime_control J K (le_refl 2)
          (e.trans (NQTerm.statedProjSLEquivProjectiveSL 2 K))).1 3 Nat.prime_three
            (by norm_num) hnd).1
    · exact outThreeSplit_of_injective _
        (outer_comp_injective J (e.trans (NQTerm.statedProjSLEquivProjectiveSL n K)))
        (outThreeSplit_projectiveSL hn3)
  | PSU =>
    obtain ⟨⟨-, -, hn, hq⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have hu : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun h => hq (by rw [h.1, h.2])
    by_cases hd : 3 ∣ Nat.gcd n (p ^ f + 1)
    ·
      have h3n : 3 ∣ n := hd.trans (Nat.gcd_dvd_left _ _)
      have h3q : 3 ∣ p ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
      have hrank := (SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hp
        (by omega : 2 ≤ n) (r := 3) (by norm_num) (H := StatedSU n (p ^ f) K) (.inr ⟨hK, rfl, h3q⟩)
        ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) le_rfl).1
      have h2 := hS 3 Nat.prime_three (by norm_num)
      rw [SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h2
      have hn3 : n = 3 := by
        obtain ⟨k, hk⟩ := h3n
        omega
      subst hn3
      obtain ⟨⟨eT⟩, -, -, -, -⟩ :=
        LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hu le_rfl hq'
      obtain ⟨F, hF⟩ := exists_unitary_outer_field_factor hu le_rfl hq'
      have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
      have hgcd : Nat.gcd 3 (p ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
      have hsplit := outThreeSplit_of_hom F fun V hV _ => by
        have hdvd : Nat.card V ∣ 3 :=
          ((Subgroup.card_dvd_of_le hV).trans hF).trans hgcd
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
        · have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
          exact isCyclic_of_subsingleton
        · exact isCyclic_of_prime_card h3
      exact outThreeSplit_of_injective _ (outer_comp_injective J
        ((e.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (by omega)).symm).trans eT.symm))
        hsplit
    · exact outThreeSplit_of_sylow
        ((perfect_unitary_central_quotient_outer_prime_control hu hn hq' J
          (e.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (by omega)).symm)).2.1 3
            Nat.prime_three hd).1
  | PSp =>
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have h := perfect_symplectic_central_quotient_outer_prime_control hp hf hn hK J ⟨e⟩
    exact outThreeSplit_of_sylow (h.1 3 Nat.prime_three (by norm_num))
  | POmegaOdd =>
    have hp2 : p ≠ 2 := hm.1.2.2.2
    rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | POmegaPlus =>
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
        Finite.of_equiv _ e.toEquiv
      exact (QuasithinUnique.Setup.Family.even_orthogonal_plus_not_sqt hK hn
        (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
    · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | POmegaMinus =>
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hm
      have : Finite (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
        Finite.of_equiv _ e.toEquiv
      exact (QuasithinUnique.Setup.Family.even_orthogonal_minus_not_sqt hK hn b c hbc
        (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
    · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hm.2.elim

theorem outThreeSplit_quasisimple
    (J : Type) [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hsqtk : SectionRank.IsSQTKCat J) : OutThreeSplit (Outer J) := by
  obtain ⟨hSQT, hcat⟩ := NQCat.sqt_catalog_center_quotient hJ hsqtk
  obtain ⟨hperf, hsimple, hnonab⟩ := hJ
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hexc | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  ·
    have hle : Nat.card (Outer (J ⧸ Subgroup.center J)) ≤ 4 := by
      rcases (show n = 6 ∨ n = 5 ∨ 7 ≤ n by omega) with rfl | hn'
      · rw [Nat.card_congr (equivalence e).toEquiv]
        exact Sporadic.SchreierLemmas.outer_alternating_six.1
      · exact (Nat.le_of_dvd (by norm_num)
          (CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six hn' e)).trans
          (by norm_num)
    exact outThreeSplit_of_card_le_four
      ((NQCat.card_outer_le_of_perfect J (MulEquiv.refl _)).trans hle)
  · exact outThreeSplit_classical J hSQT hcl
  · exact outThreeSplit_of_sylow
      ((NQCat.sqt_exceptional_central_quotient_outer_prime_control J hSQT hexc).2 3
        Nat.prime_three (by norm_num)).1
  · rcases NQCat.sqt_sporadic_perfect_cover_outer_J4_alternative J inferInstance hSQT hspor with
      hJ4 | ⟨-, hle, -⟩
    ·
      obtain ⟨e⟩ := hJ4
      have hinn : ∀ α : MulAut (J ⧸ Subgroup.center J), α ∈ inner (J ⧸ Subgroup.center J) :=
        fun α => by
          obtain ⟨g, hg⟩ := KGInsp.j4_all_inner
            (e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)) α
          exact ⟨g, hg.symm⟩
      have : Subsingleton (Outer (J ⧸ Subgroup.center J)) := by
        constructor
        intro a b
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [QuotientGroup.eq]
        exact hinn _
      have h1 : Nat.card (Outer (J ⧸ Subgroup.center J)) ≤ 1 :=
        (Nat.card_of_subsingleton (1 : Outer (J ⧸ Subgroup.center J))).le
      exact outThreeSplit_of_card_le_four
        ((NQCat.card_outer_le_of_perfect J (MulEquiv.refl _)).trans (h1.trans (by norm_num)))
    · exact outThreeSplit_of_card_le_four hle

theorem outThreeFact_holds :
    OutThreeFact := by
  intro A _ _ L hS hLn hL
  have := hLn
  have : Finite (MulAut ↥L) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut ↥L))
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥L :=
    ⟨CFSG.SectionRank.IsStronglyQuasithin.subgroup hS.sqt L,
      CFSG.SectionRank.IsKGroupCat.subgroup hS.kgroup L⟩
  obtain ⟨N, hN, h1, h2⟩ := outThreeSplit_quasisimple ↥L hL.1 hsqtk
  set φ : A →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp (MulAut.conjNormal (H := L))
    with hφ
  have hkerle : φ.ker ≤ L ⊔ Subgroup.centralizer (L : Set A) := fun x hx =>
    mem_sup_centralizer_of_conjNormal_inner ((QuotientGroup.eq_one_iff _).mp hx)
  have hLker : L ≤ φ.ker := fun l hl => by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨⟨l, hl⟩, ?_⟩
    ext z
    simp [MulAut.conj_apply, MulAut.conjNormal_apply]
  have hCker : Subgroup.centralizer (L : Set A) ≤ φ.ker := fun c hc => by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    refine ⟨1, ?_⟩
    ext z
    have hcz : z * c = c * z := (Subgroup.mem_centralizer_iff.mp hc) z z.2
    simp [MulAut.conjNormal_apply, ← hcz]
  refine ⟨N.comap φ, hN.comap φ, ?_, fun U hU => ?_, fun U hUD hU => ?_⟩
  · exact (sup_le hLker hCker).trans (fun x hx => by
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).mp hx]; exact N.one_mem)
  · obtain ⟨w, hw, hle⟩ := h1 (U.map φ) (hU.map φ)
    obtain ⟨u, hu, rfl⟩ := hw
    exact ⟨u, hu, le_zpowers_sup_comap φ hN hle⟩
  · have hc := h2 (U.map φ) (Subgroup.map_le_iff_le_comap.mpr hUD) (hU.map φ)
    obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (U.map φ)).mp hc
    obtain ⟨u, hu, rfl⟩ : g ∈ U.map φ := hg ▸ Subgroup.mem_zpowers g
    have hle := le_zpowers_sup_comap φ Subgroup.normal_bot (U := U) (u := u)
      (by rw [hg]; exact le_sup_left)
    rw [MonoidHom.comap_bot] at hle
    exact ⟨u, hu, hle.trans (sup_le_sup_left hkerle _)⟩

end Families

end CFSG.Quasithin.H13.NQCore
