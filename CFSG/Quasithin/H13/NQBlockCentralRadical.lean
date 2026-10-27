module

public import CFSG.Quasithin.H13.NQBlockCanonicalWitnesses

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement Pointwise

theorem radical_eq_comap_center {L M : Type*} [Group L] [Finite L] [Group M] {ρ : L →* M}
    (hJq : CFSG.IsQuasisimple ρ.range) (hker : ρ.ker = CFSG.fittingSubgroup L) :
    CFSG.solvableRadical L = (center ρ.range).comap ρ.rangeRestrict := by
  classical
  obtain ⟨-, hRsolv, hRmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hNn : (CFSG.solvableRadical L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  obtain ⟨P, hP⟩ : ∃ P : Subgroup L, P = (center ρ.range).comap ρ.rangeRestrict := ⟨_, rfl⟩
  rw [← hP]
  have hmemP : ∀ x : L, x ∈ P ↔ ρ.rangeRestrict x ∈ center ρ.range := fun x => by
    rw [hP, mem_comap]
  have hFP : CFSG.fittingSubgroup L ≤ P := by
    intro x hx
    have h1 : ρ.rangeRestrict x = 1 := Subtype.ext (by
      rw [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, ← MonoidHom.mem_ker, hker]
      exact hx)
    rw [hmemP, h1]
    exact one_mem _
  have hPsolv : Group.IsSolvable P := by
    have : Group.IsSolvable (center ρ.range) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp b.2 a)
    obtain ⟨g, hg⟩ : ∃ g : P →* center ρ.range, ∀ x, ((g x : ρ.range) : M) = ρ x :=
      ⟨(ρ.rangeRestrict.comp P.subtype).codRestrict (center ρ.range) fun x => (hmemP x).mp x.2,
        fun _ => rfl⟩
    refine Group.isSolvable_of_ker_le_range (inclusion hFP) g fun x hx => ?_
    have h1 : ρ x = 1 := by
      have h2 : g x = 1 := hx
      rw [← hg, h2]
      rfl
    have hxF : (x : L) ∈ CFSG.fittingSubgroup L := by
      rw [← hker]
      exact h1
    exact ⟨⟨x, hxF⟩, rfl⟩
  have hPn : P.Normal := by
    rw [hP]
    infer_instance
  have hPN : P ≤ CFSG.solvableRadical L := hRmax P hPn hPsolv
  have hNP : CFSG.solvableRadical L ≤ P := by
    have hBn : ((CFSG.solvableRadical L).map ρ.rangeRestrict).Normal :=
      hNn.map _ ρ.rangeRestrict_surjective
    have hBs : Group.IsSolvable ((CFSG.solvableRadical L).map ρ.rangeRestrict) :=
      Group.isSolvable_of_surjective (f := ρ.rangeRestrict.subgroupMap (CFSG.solvableRadical L))
        (ρ.rangeRestrict.subgroupMap_surjective _)
    have hB := le_center_of_isSolvable_of_isQuasisimple hJq _ hBs
    intro x hx
    exact (hmemP x).mpr (hB ⟨x, hx, rfl⟩)
  exact le_antisymm hNP hPN

theorem relIndex_fitting_radical {L M : Type*} [Group L] [Finite L] [Group M] {ρ : L →* M}
    (hJq : CFSG.IsQuasisimple ρ.range) (hker : ρ.ker = CFSG.fittingSubgroup L)
    (hZ : Nat.card (center ρ.range) = 2) :
    (CFSG.fittingSubgroup L).relIndex (CFSG.solvableRadical L) = 2 := by
  classical
  have hNeq := radical_eq_comap_center hJq hker
  have hmemN : ∀ x : L, x ∈ CFSG.solvableRadical L ↔ ρ.rangeRestrict x ∈ center ρ.range :=
    fun x => by rw [hNeq, mem_comap]
  obtain ⟨g, hg⟩ : ∃ g : CFSG.solvableRadical L →* center ρ.range,
      ∀ x, ((g x : ρ.range) : M) = ρ x :=
    ⟨(ρ.rangeRestrict.comp (CFSG.solvableRadical L).subtype).codRestrict (center ρ.range)
      fun x => (hmemN x).mp x.2, fun _ => rfl⟩
  have hgs : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := ρ.rangeRestrict_surjective z
    have hxN : x ∈ CFSG.solvableRadical L := by
      rw [hmemN, hx]
      exact hz
    refine ⟨⟨x, hxN⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hg]
    exact congrArg Subtype.val hx
  have hgker : g.ker = (CFSG.fittingSubgroup L).subgroupOf (CFSG.solvableRadical L) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hker, MonoidHom.mem_ker, ← hg]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext (Subtype.ext h)
  have h1 : Nat.card (CFSG.solvableRadical L ⧸ g.ker) = Nat.card (center ρ.range) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hgs).toEquiv
  rw [hgker, hZ] at h1
  exact h1

theorem radical_quotient_equiv {L M : Type*} [Group L] [Finite L] [Group M] {ρ : L →* M}
    (hJq : CFSG.IsQuasisimple ρ.range) (hker : ρ.ker = CFSG.fittingSubgroup L) :
    Nonempty (L ⧸ CFSG.solvableRadical L ≃* ρ.range ⧸ center ρ.range) ∧
      IsSimpleGroup (L ⧸ CFSG.solvableRadical L) ∧
        ∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a := by
  classical
  have hNn : (CFSG.solvableRadical L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hNeq := radical_eq_comap_center hJq hker
  have hsurj : Function.Surjective ((QuotientGroup.mk' (center ρ.range)).comp ρ.rangeRestrict) :=
    (QuotientGroup.mk'_surjective _).comp ρ.rangeRestrict_surjective
  have hkerN : ((QuotientGroup.mk' (center ρ.range)).comp ρ.rangeRestrict).ker =
      CFSG.solvableRadical L := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hNeq]
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hJq
  obtain ⟨e, -⟩ : ∃ e : L ⧸ CFSG.solvableRadical L ≃* ρ.range ⧸ center ρ.range, True :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hkerN.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj), trivial⟩
  refine ⟨⟨e⟩, MulEquiv.isSimpleGroup e, e.symm a, e.symm b, fun h => hab ?_⟩
  have h1 := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem radical_of_quasisimple_image {L M : Type*} [Group L] [Finite L] [Group M] {ρ : L →* M}
    (hJq : CFSG.IsQuasisimple ρ.range) (hker : ρ.ker = CFSG.fittingSubgroup L)
    (hZ : Nat.card (center ρ.range) = 2) {s : ℕ} [Fact s.Prime]
    (ψ : ρ.range ⧸ center ρ.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) :
    CFSG.fittingSubgroup L ≤ CFSG.solvableRadical L ∧
      (∀ n ∈ CFSG.solvableRadical L, ∀ l : L, ⁅n, l⁆ ∈ CFSG.fittingSubgroup L) ∧
      (CFSG.fittingSubgroup L).relIndex (CFSG.solvableRadical L) = 2 ∧
      IsSimpleGroup (L ⧸ CFSG.solvableRadical L) ∧
      (∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a) ∧
      Nonempty (L ⧸ CFSG.solvableRadical L ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s)) := by
  classical
  obtain ⟨-, -, hRmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L
  have hFN : CFSG.fittingSubgroup L ≤ CFSG.solvableRadical L :=
    hRmax _ inferInstance inferInstance
  have hNeq := radical_eq_comap_center hJq hker
  have hNc : ∀ n ∈ CFSG.solvableRadical L, ∀ l : L, ⁅n, l⁆ ∈ CFSG.fittingSubgroup L := by
    intro n hn l
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have h1 : ρ.rangeRestrict n ∈ center ρ.range := by
      rw [hNeq] at hn
      exact hn
    exact (congrArg Subtype.val (mem_center_iff.mp h1 (ρ.rangeRestrict l))).symm
  obtain ⟨⟨e⟩, hsL, hnabL⟩ := radical_quotient_equiv hJq hker
  exact ⟨hFN, hNc, relIndex_fitting_radical hJq hker hZ, hsL, hnabL,
    ⟨e.trans (ψ.trans (CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod s)).symm)⟩⟩

theorem radical_setup
    {L : Type*} [Group L] [Finite L] (hSQT : CFSG.IsStronglyQuasithin L)
    (hO2 : CFSG.pCore 2 L = ⊥) (hLC : CFSG.IsCComponent (⊤ : Subgroup L))
    (hq : ¬ CFSG.IsQuasisimple L) :
    CFSG.fittingSubgroup L ≠ ⊥ ∧ Odd (Nat.card (CFSG.fittingSubgroup L)) ∧
      CFSG.fittingSubgroup L ≤ CFSG.solvableRadical L ∧
      (∀ n ∈ CFSG.solvableRadical L, ∀ l : L, ⁅n, l⁆ ∈ CFSG.fittingSubgroup L) ∧
      (CFSG.fittingSubgroup L).relIndex (CFSG.solvableRadical L) = 2 ∧
      IsSimpleGroup (L ⧸ CFSG.solvableRadical L) ∧
      (∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a) ∧
      ∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧ Nonempty (L ⧸ CFSG.solvableRadical L ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s)) := by
  classical
  obtain ⟨-, hFne, hodd, -, -, -⟩ := odd_Fitting_cores_self hSQT hO2 hLC hq
  obtain ⟨-, hcrit⟩ := all_prime_critical_actions_self hSQT hO2 hLC hq
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr ((one_lt_card_iff_ne_bot _).mpr hFne)
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  obtain ⟨-, D, hDc, hD, hker⟩ := hcrit r hr
  obtain ⟨s, hs, hs5, -, ⟨ψ⟩⟩ := hD.projective
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨hFN, hNc, hidx, hsimple, hnab, he⟩ :=
    radical_of_quasisimple_image hD.isQuasisimple hker hD.card_center ψ
  exact ⟨hFne, hodd, hFN, hNc, hidx, hsimple, hnab, s, ⟨hs⟩, hs5, he⟩

theorem eq_one_of_eq_inv_of_odd {W : Type*} [Group W] [Finite W] (hW : Odd (Nat.card W))
    {w : W} (h : w = w⁻¹) : w = 1 := by
  have h2 : w ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 2 [h]
    exact mul_inv_cancel w
  have h3 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left h3 (Nat.coprime_comm.mp (Odd.coprime_two_right hW)))
    (orderOf_dvd_natCard w)
  exact orderOf_eq_one_iff.mp h4

theorem criticalAction_eq_inv {L : Type*} [Group L] {r : ℕ} {Q : Subgroup L} [Q.Normal]
    {D : Subgroup Q} [D.Characteristic] (hD : IsCriticalData r Q D) {K : Subgroup L}
    (hker : (criticalAction D).ker = K) {t : L} (ht : t ∉ K) (htK : ∀ l : L, ⁅t, l⁆ ∈ K)
    (w : D ⧸ frattini D) : criticalAction D t w = w⁻¹ := by
  have hcen : (⟨criticalAction D t, t, rfl⟩ : (criticalAction D).range) ∈
      center (criticalAction D).range := by
    rw [mem_center_iff]
    rintro ⟨_, l, rfl⟩
    apply Subtype.ext
    have h1 : criticalAction D ⁅t, l⁆ = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact htK l
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rcases (hD.mem_center_iff _).mp hcen with h | h
  · exact absurd (by rw [← hker, MonoidHom.mem_ker]; exact h) ht
  · exact h w

theorem pCore_inf_centralizer_eq_commutator {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hodd : Odd (Nat.card (CFSG.fittingSubgroup L)))
    (hQL : ⁅CFSG.pCore r L, (⊤ : Subgroup L)⁆ = CFSG.pCore r L)
    (D : Subgroup (CFSG.pCore r L)) [D.Characteristic] (hD : IsCriticalData r (CFSG.pCore r L) D)
    (hker : (criticalAction D).ker = CFSG.fittingSubgroup L) {t : L}
    (ht : ∀ w, criticalAction D t w = w⁻¹) :
    CFSG.pCore r L ⊓ centralizer ({t} : Set L) = ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ∧
      ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ≤ center L := by
  classical
  have hWodd : Odd (Nat.card (D ⧸ frattini D)) := by
    rw [hD.card_quotient]
    exact (hr.out.odd_of_ne_two hr2).pow
  have hfix : ∀ d : D, t * ((d : CFSG.pCore r L) : L) * t⁻¹ = d → d ∈ frattini D := by
    intro d hd
    have h1 : criticalAction D t (d : D ⧸ frattini D) = (d : D ⧸ frattini D) := by
      change frattiniAction D (MulAut.conjNormal t) (d : D ⧸ frattini D) = _
      rw [frattiniAction_mk]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact hd
    rw [ht] at h1
    have h2 := eq_one_of_eq_inv_of_odd hWodd h1.symm
    rwa [QuotientGroup.eq_one_iff] at h2
  have hconj : ∀ x ∈ centralizer ({t} : Set L), t * x * t⁻¹ = x := by
    intro x hx
    rw [← mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]
  obtain ⟨hnab, hab⟩ := critical_whole_shape hr2 hodd hQL D hD hker
  rcases hD.shape with ⟨hel, hcard⟩ | ⟨hnc, hcard, hΦ, -⟩
  ·
    obtain ⟨hQab, -, hDΩ⟩ := hab hel
    have hQQ : ⁅CFSG.pCore r L, CFSG.pCore r L⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hQab.is_comm.comm (⟨y, hy⟩ : CFSG.pCore r L) ⟨x, hx⟩)
    rw [hQQ]
    refine ⟨?_, bot_le⟩
    by_contra hne
    have hKp : IsPGroup r (CFSG.pCore r L ⊓ centralizer ({t} : Set L) : Subgroup L) :=
      (CFSG.pCore_isPGroup : IsPGroup r (CFSG.pCore r L)).to_le inf_le_left
    have hKnt : Nontrivial (CFSG.pCore r L ⊓ centralizer ({t} : Set L) : Subgroup L) :=
      (nontrivial_iff_ne_bot _).mpr hne
    have hdvd : r ∣ Nat.card (CFSG.pCore r L ⊓ centralizer ({t} : Set L) : Subgroup L) := by
      rcases hKp.card_eq_or_dvd with h | h
      · exact absurd h Finite.one_lt_card.ne'
      · exact h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hyQ : (y : L) ∈ CFSG.pCore r L := (mem_inf.mp y.2).1
    have hyt := hconj y (mem_inf.mp y.2).2
    have hyr : (y : L) ^ r = 1 := by
      have h1 := pow_orderOf_eq_one y
      rw [hy] at h1
      have h2 := congrArg Subtype.val h1
      rwa [SubgroupClass.coe_pow] at h2
    have hyD : (⟨y, hyQ⟩ : CFSG.pCore r L) ∈ D := by
      rw [hDΩ]
      apply Subgroup.subset_closure
      show (⟨y, hyQ⟩ : CFSG.pCore r L) ^ r ^ 1 = 1
      rw [pow_one]
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hyr
    have hΦbot : frattini D = ⊥ := by
      have : Fact (IsPGroup r D) := ⟨IsPGroup.of_card hcard⟩
      exact CFSG.frattini_eq_bot_of_isElementaryAbelian (R := D) (p := r)
    have h1 := hfix ⟨⟨y, hyQ⟩, hyD⟩ hyt
    rw [hΦbot, mem_bot] at h1
    have h2 : (y : L) = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
    have h3 : y = 1 := Subtype.ext h2
    rw [h3, orderOf_one] at hy
    exact hr.out.one_lt.ne hy
  ·
    have hDtop := hnab hnc
    have hQcard : Nat.card (CFSG.pCore r L) = r ^ 3 := by
      rw [← card_top (G := CFSG.pCore r L), ← hDtop, hcard]
    have hnc' : ∃ a b : CFSG.pCore r L, a * b ≠ b * a := by
      by_contra h
      push Not at h
      apply hnc
      exact ⟨⟨fun a b => Subtype.ext (h a b)⟩⟩
    obtain ⟨hcomm, hZcard, -, -, -, -, -⟩ := nonabelian_prime_cube_central_structure hQcard hnc'
    have hQQ : ⁅CFSG.pCore r L, CFSG.pCore r L⁆ =
        (center (CFSG.pCore r L)).map (CFSG.pCore r L).subtype := by
      rw [← hcomm, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        range_subtype]
    have hZL : (center (CFSG.pCore r L)).map (CFSG.pCore r L).subtype ≤ center L := by
      rintro _ ⟨z, hz, rfl⟩
      rw [mem_center_iff]
      intro l
      have h1 := perfect_fixes_cyclic (MulAut.conjNormal : L →* MulAut (CFSG.pCore r L))
        (C := center (CFSG.pCore r L)) (isCyclic_of_prime_card hZcard)
        (fun h c hc => mem_of_characteristic (center (CFSG.pCore r L)) _ c hc) l z hz
      have h2 := congrArg Subtype.val h1
      rw [MulAut.conjNormal_apply] at h2
      rw [subtype_apply]
      calc l * (z : L) = l * z * l⁻¹ * l := by group
        _ = z * l := by rw [h2]
    have hCQ : CFSG.pCore r L ⊓ centralizer ({t} : Set L) =
        (center (CFSG.pCore r L)).map (CFSG.pCore r L).subtype := by
      apply le_antisymm
      · rintro x ⟨hxQ, hxt⟩
        have hxD : (⟨x, hxQ⟩ : CFSG.pCore r L) ∈ D := by
          rw [hDtop]
          exact mem_top _
        have h1 := hfix ⟨⟨x, hxQ⟩, hxD⟩ (hconj x hxt)
        rw [hΦ] at h1
        refine ⟨⟨x, hxQ⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, mem_center_iff]
        intro y
        have hyD : y ∈ D := by
          rw [hDtop]
          exact mem_top y
        exact congrArg Subtype.val (mem_center_iff.mp h1 ⟨y, hyD⟩)
      · intro x hx
        refine mem_inf.mpr ⟨?_, ?_⟩
        · obtain ⟨z, -, rfl⟩ := hx
          exact z.2
        · rw [mem_centralizer_singleton_iff]
          exact (mem_center_iff.mp (hZL hx) t).symm
    rw [hQQ]
    exact ⟨hCQ, hZL⟩

theorem eq_iSup_inf_pCore_of_le_fitting {L : Type*} [Group L] [Finite L] {K : Subgroup L}
    (hK : K ≤ CFSG.fittingSubgroup L) :
    K = ⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors, K ⊓ CFSG.pCore (p : ℕ) L := by
  classical
  apply le_antisymm
  · intro x hx
    have hT : (⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        K ⊓ CFSG.pCore (p : ℕ) L).subgroupOf K = ⊤ := by
      refine eq_top_of_forall_sylow_le _ fun r _ S => ?_
      intro y hy
      rw [mem_subgroupOf]
      by_cases hr : r ∣ Nat.card (CFSG.fittingSubgroup L)
      · have hyr : (y : L) ∈ CFSG.pCore r L := by
          set P : Subgroup L := (S : Subgroup K).map K.subtype with hP
          have hPF : P ≤ CFSG.fittingSubgroup L := (map_subtype_le _).trans hK
          have hPr : IsPGroup r P := S.isPGroup'.map _
          obtain ⟨S', hS'⟩ := (hPr.of_equiv (subgroupOfEquivOfLe hPF).symm :
            IsPGroup r (P.subgroupOf (CFSG.fittingSubgroup L))).exists_le_sylow
          rw [← sylow_fitting_map_eq_pCore S']
          exact ⟨⟨y, hK y.2⟩, hS' (mem_subgroupOf.mpr ⟨y, hy, rfl⟩), rfl⟩
        have hrmem : r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Fact.out, hr, Nat.card_pos.ne'⟩
        exact le_iSup (fun p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors =>
          K ⊓ CFSG.pCore (p : ℕ) L) ⟨r, hrmem⟩ (mem_inf.mpr ⟨y.2, hyr⟩)
      · have hrK : ¬ r ∣ Nat.card K := fun h => hr (h.trans (card_dvd_of_le hK))
        have h1 : (S : Subgroup K) = ⊥ := by
          rw [← card_eq_one, S.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hrK,
            pow_zero]
        rw [h1, mem_bot] at hy
        rw [hy]
        exact one_mem _
    have h1 : (⟨x, hx⟩ : K) ∈ (⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        K ⊓ CFSG.pCore (p : ℕ) L).subgroupOf K := by
      rw [hT]
      exact mem_top _
    exact h1
  · exact iSup_le fun p => inf_le_left

theorem fitting_inf_centralizer_eq_commutator {L : Type*} [Group L] [Finite L] {t : L}
    (h : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      CFSG.pCore r L ⊓ centralizer ({t} : Set L) = ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ∧
        ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ≤ center L) :
    CFSG.fittingSubgroup L ⊓ centralizer ({t} : Set L) =
        ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ∧
      ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ≤ center L := by
  classical
  set Z0 : Subgroup L := ⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
    ⁅CFSG.pCore (p : ℕ) L, CFSG.pCore (p : ℕ) L⁆ with hZ0
  have hZ0c : Z0 ≤ center L := iSup_le fun p => (h p p.2).2
  have hZ0n : Z0.Normal := ⟨fun n hn g => by
    have h1 := mem_center_iff.mp (hZ0c hn) g
    rw [h1, mul_inv_cancel_right]
    exact hn⟩
  have hFF : ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ≤ Z0 := by
    have hB : ∀ p q : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        (CFSG.pCore (q : ℕ) L).map (QuotientGroup.mk' Z0) ≤
          centralizer ((CFSG.pCore (p : ℕ) L).map (QuotientGroup.mk' Z0) : Set (L ⧸ Z0)) := by
      intro p q
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      by_cases hpq : p = q
      · subst hpq
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
        exact mk_mul_comm_of_commutator_mem Z0
          (le_iSup (fun p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors =>
            ⁅CFSG.pCore (p : ℕ) L, CFSG.pCore (p : ℕ) L⁆) p (commutator_mem_commutator hx hy))
      · have h1 := pCore_commute_fittingPrimes (L := L) hpq x y hx hy
        rw [← map_mul, ← map_mul, h1.eq]
    have hFmap : (CFSG.fittingSubgroup L).map (QuotientGroup.mk' Z0) =
        ⨆ p : (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
          (CFSG.pCore (p : ℕ) L).map (QuotientGroup.mk' Z0) := by
      rw [← Subgroup.map_iSup, ← fitting_eq_iSup_pCore_fittingPrimes]
    have hcomm : ⁅(CFSG.fittingSubgroup L).map (QuotientGroup.mk' Z0),
        (CFSG.fittingSubgroup L).map (QuotientGroup.mk' Z0)⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer, hFmap]
      refine iSup_le fun p => ?_
      rw [le_centralizer_iff]
      exact iSup_le fun q => hB p q
    have h1 : ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆.map (QuotientGroup.mk' Z0) = ⊥ := by
      rw [map_commutator, hcomm]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact h1
  have hFFc : ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ≤ center L := hFF.trans hZ0c
  refine ⟨le_antisymm ?_ ?_, hFFc⟩
  · rw [eq_iSup_inf_pCore_of_le_fitting (K := CFSG.fittingSubgroup L ⊓ centralizer ({t} : Set L))
      inf_le_left]
    refine iSup_le fun p => ?_
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have h1 : CFSG.fittingSubgroup L ⊓ centralizer ({t} : Set L) ⊓ CFSG.pCore (p : ℕ) L ≤
        CFSG.pCore (p : ℕ) L ⊓ centralizer ({t} : Set L) :=
      le_inf inf_le_right (inf_le_left.trans inf_le_right)
    rw [(h p p.2).1] at h1
    exact h1.trans (commutator_mono (CFSG.pCore_le_fitting L p) (CFSG.pCore_le_fitting L p))
  · exact le_inf (commutator_le_left _ _) (hFFc.trans (center_le_centralizer _))

theorem sylow_two_of_relIndex_two {L : Type*} [Group L] [Finite L] {F N : Subgroup L} [F.Normal]
    (hFN : F ≤ N) (hodd : Odd (Nat.card F)) (hidx : F.relIndex N = 2) {S : Subgroup L}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S N) :
    Nat.card S = 2 ∧ F ⊓ S = ⊥ ∧ N = F ⊔ S ∧ ∀ t ∈ S, t ≠ 1 → S = zpowers t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := hS
  have hcardN : Nat.card N = 2 * Nat.card F := by
    have h1 := Subgroup.relIndex_mul_card (H := F) (K := N)
    rw [inf_eq_left.mpr hFN, hidx] at h1
    exact h1.symm
  have hcardS : Nat.card ((P : Subgroup N).map N.subtype) = 2 := by
    rw [card_map_of_injective N.subtype_injective, P.card_eq_multiplicity, hcardN,
      Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd
        (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)), add_zero, pow_one]
  have hFS : F ⊓ (P : Subgroup N).map N.subtype = ⊥ := by
    have h1 : Nat.card (F ⊓ (P : Subgroup N).map N.subtype : Subgroup L) ∣ 2 := by
      have := card_dvd_of_le (inf_le_right : F ⊓ (P : Subgroup N).map N.subtype ≤
        (P : Subgroup N).map N.subtype)
      rwa [hcardS] at this
    have h2 : Nat.card (F ⊓ (P : Subgroup N).map N.subtype : Subgroup L) ∣ Nat.card F :=
      card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact card_eq_one.mp h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)
  have hsup : N = F ⊔ (P : Subgroup N).map N.subtype := by
    have hle : F ⊔ (P : Subgroup N).map N.subtype ≤ N := sup_le hFN (map_subtype_le _)
    refine (eq_of_le_of_card_ge hle ?_).symm
    have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal F
      ((P : Subgroup N).map N.subtype)
    have h2 := Subgroup.relIndex_mul_card (H := (P : Subgroup N).map N.subtype)
      (K := F ⊔ (P : Subgroup N).map N.subtype)
    have h3 := Subgroup.relIndex_mul_card (H := (P : Subgroup N).map N.subtype) (K := F)
    rw [inf_eq_left.mpr le_sup_right, h1] at h2
    rw [inf_comm, hFS, card_bot, mul_one] at h3
    rw [← h2, h3, hcardS, hcardN]
    exact le_of_eq (mul_comm _ _)
  refine ⟨hcardS, hFS, hsup, fun t ht ht1 => ?_⟩
  have hle : zpowers t ≤ (P : Subgroup N).map N.subtype := zpowers_le.mpr ht
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [hcardS, Nat.card_zpowers]
  have h1 : orderOf t ∣ 2 := by
    have := orderOf_dvd_natCard (⟨t, ht⟩ : (P : Subgroup N).map N.subtype)
    rwa [hcardS, Subgroup.orderOf_mk] at this
  have h2 : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact absurd h h2
  · exact h.ge

theorem radical_centralizer {L : Type*} [Group L] {F N S : Subgroup L} [F.Normal] {t : L}
    (hNFS : N = F ⊔ S) (hS : S = zpowers t) (hFS : F ⊓ S = ⊥)
    (hCF : F ⊓ centralizer ({t} : Set L) = ⁅F, F⁆) (hFZ : ⁅F, F⁆ ≤ center L) :
    N ⊓ centralizer ({t} : Set L) = ⁅F, F⁆ ⊔ S ∧ ⁅F, F⁆ ⊓ S = ⊥ ∧
      N ⊓ centralizer ({t} : Set L) ≤
        (center (centralizer ({t} : Set L))).map (centralizer ({t} : Set L)).subtype := by
  have hSt : S ≤ centralizer ({t} : Set L) := by
    rw [hS, zpowers_le, mem_centralizer_singleton_iff]
  have hFF : ⁅F, F⁆ ≤ F := commutator_le_left F F
  have heq : N ⊓ centralizer ({t} : Set L) = ⁅F, F⁆ ⊔ S := by
    apply le_antisymm
    · rintro x ⟨hxN, hxt⟩
      have hx : x ∈ ((F ⊔ S : Subgroup L) : Set L) := by
        rw [← hNFS]
        exact hxN
      rw [normal_mul, Set.mem_mul] at hx
      obtain ⟨f, hf, u, hu, rfl⟩ := hx
      have hft : f ∈ centralizer ({t} : Set L) := by
        have h1 : f = f * u * u⁻¹ := by group
        rw [h1]
        exact mul_mem hxt (inv_mem (hSt hu))
      have hfF' : f ∈ ⁅F, F⁆ := by
        rw [← hCF]
        exact mem_inf.mpr ⟨hf, hft⟩
      exact mul_mem (mem_sup_left hfF') (mem_sup_right hu)
    · refine sup_le (le_inf (hFF.trans ?_) (hFZ.trans (center_le_centralizer _)))
        (le_inf ?_ hSt)
      · rw [hNFS]
        exact le_sup_left
      · rw [hNFS]
        exact le_sup_right
  refine ⟨heq, ?_, ?_⟩
  · rw [eq_bot_iff, ← hFS]
    exact inf_le_inf_right S hFF
  · have h1 : ⁅F, F⁆ ⊔ S ≤ centralizer (centralizer ({t} : Set L) : Set L) := by
      refine sup_le (hFZ.trans (center_le_centralizer _)) ?_
      rw [hS, zpowers_le, mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.mp hy
    rw [heq]
    intro x hx
    have hxt : x ∈ centralizer ({t} : Set L) :=
      sup_le (hFZ.trans (center_le_centralizer _)) hSt hx
    refine ⟨⟨x, hxt⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (h1 hx) y y.2)

theorem perfect_supplement_quasisimple {L : Type*} [Group L] [Finite L] {N : Subgroup L}
    [N.Normal] (hsimple : IsSimpleGroup (L ⧸ N)) (hnab : ∃ a b : L ⧸ N, a * b ≠ b * a)
    {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s)
    (e : L ⧸ N ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))
    {J : Subgroup L} (hJ : Group.IsPerfect J) (hNJ : N ⊔ J = ⊤)
    (hcen : N.subgroupOf J ≤ center J) :
    CFSG.IsQuasisimple J ∧ center J = N.subgroupOf J ∧ Nat.card (center J) ≤ 2 ∧
      Nonempty (J ⧸ center J ≃* L ⧸ N) := by
  classical
  set f : J →* L ⧸ N := (QuotientGroup.mk' N).comp J.subtype with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ ((N ⊔ J : Subgroup L) : Set L) := by
      rw [hNJ]
      exact (mem_top x : x ∈ (⊤ : Subgroup L))
    rw [normal_mul, Set.mem_mul] at hx
    obtain ⟨n, hn, j, hj, rfl⟩ := hx
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, subtype_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hfker : f.ker = N.subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hf, MonoidHom.comp_apply, subtype_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hZN : center (L ⧸ N) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center (L ⧸ N)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hb : b ∈ center (L ⧸ N) := by
        rw [h]
        exact mem_top b
      exact mem_center_iff.mp hb a
  have hZJ : center J ≤ N.subgroupOf J := by
    intro z hz
    rw [← hfker, MonoidHom.mem_ker]
    have h1 : f z ∈ center (L ⧸ N) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hfs y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz x]
    rw [hZN, mem_bot] at h1
    exact h1
  have hZeq : center J = N.subgroupOf J := le_antisymm hZJ hcen
  set eJ : J ⧸ center J ≃* L ⧸ N :=
    (QuotientGroup.quotientMulEquivOfEq (hZeq.trans hfker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs) with heJ
  have hk : (e.toMonoidHom.comp f).ker = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hbound := CFSG.QuasithinUnique.Setup.Family.p2_central_kernel_bound hs5
    (e.toMonoidHom.comp f) (e.surjective.comp hfs) (by rw [hk, hfker, ← hZeq])
  rw [hk, hfker, ← hZeq] at hbound
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨⟨hJ, MulEquiv.isSimpleGroup eJ, eJ.symm a, eJ.symm b, fun h => hab ?_⟩, hZeq, hbound,
    ⟨eJ⟩⟩
  have h1 := congrArg eJ h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem fitting_sup_eq_top {L : Type*} [Group L] [Group.IsPerfect L] {F N S J : Subgroup L}
    [F.Normal] {t : L} (hNFS : N = F ⊔ S) (hS : S = zpowers t) (ht2 : t * t = 1)
    (hJt : J ≤ centralizer ({t} : Set L)) (hNJ : N ⊔ J = ⊤) : F ⊔ J = ⊤ := by
  set K := F ⊔ J with hK
  have hKset : (K : Set L) = (F : Set L) * J := normal_mul F J
  have htK : ∀ x ∈ K, t * x * t⁻¹ ∈ K := by
    intro x hx
    rw [← SetLike.mem_coe, hKset, Set.mem_mul] at hx
    obtain ⟨f, hf, j, hj, rfl⟩ := hx
    have hjt : t * j * t⁻¹ = j := by
      rw [← mem_centralizer_singleton_iff.mp (hJt hj), mul_inv_cancel_right]
    have e : t * (f * j) * t⁻¹ = (t * f * t⁻¹) * (t * j * t⁻¹) := by group
    rw [e, hjt]
    exact mul_mem (mem_sup_left ((inferInstance : F.Normal).conj_mem f hf t)) (mem_sup_right hj)
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  have htnorm : t ∈ normalizer (K : Set L) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨htK h, fun hh => ?_⟩
    have h1 := htK _ hh
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      rw [htinv, ← mul_assoc, ← mul_assoc, ht2, one_mul, mul_assoc, ht2, mul_one]
    rwa [e] at h1
  have hKS : K ⊔ S = ⊤ := by
    rw [eq_top_iff, ← hNJ, hNFS]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      ((le_sup_right : J ≤ K).trans le_sup_left)
  have hKn : K.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hKS]
    refine sup_le le_normalizer ?_
    rw [hS, zpowers_le]
    exact htnorm
  have hquot : ∀ x : L, ∃ n : ℤ, (x : L ⧸ K) = (t : L ⧸ K) ^ n := by
    intro x
    have hx : x ∈ ((K ⊔ S : Subgroup L) : Set L) := by
      rw [hKS]
      exact (mem_top x : x ∈ (⊤ : Subgroup L))
    rw [normal_mul, Set.mem_mul] at hx
    obtain ⟨k, hk, u, hu, rfl⟩ := hx
    rw [hS] at hu
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
    refine ⟨n, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, one_mul, QuotientGroup.mk_zpow]
  have htop : ⁅(⊤ : Subgroup L), ⊤⁆ ≤ K := by
    rw [commutator_le]
    intro x _ y _
    have h1 : QuotientGroup.mk' K ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      obtain ⟨a, ha⟩ := hquot x
      obtain ⟨b, hb⟩ := hquot y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ha, hb, ← zpow_add, ← zpow_add,
        add_comm]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    have h1 := Group.isPerfect_def.mp (inferInstance : Group.IsPerfect L)
    rwa [_root_.commutator_def] at h1
  exact eq_top_iff.mpr (hperf ▸ htop)

theorem perfect_supplement_structure {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {F N S : Subgroup L} [F.Normal] [N.Normal] {t : L} (hFN : F ≤ N) (hodd : Odd (Nat.card F))
    (hidx : F.relIndex N = 2) (hNFS : N = F ⊔ S) (hS : S = zpowers t) (hS2 : Nat.card S = 2)
    (ht2 : t * t = 1) (hCN : N ⊓ centralizer ({t} : Set L) = ⁅F, F⁆ ⊔ S)
    (hFZ : ⁅F, F⁆ ≤ center L)
    (hZ : N ⊓ centralizer ({t} : Set L) ≤
      (center (centralizer ({t} : Set L))).map (centralizer ({t} : Set L)).subtype)
    (hsimple : IsSimpleGroup (L ⧸ N)) (hnab : ∃ a b : L ⧸ N, a * b ≠ b * a) {s : ℕ}
    [Fact s.Prime] (hs5 : 5 ≤ s)
    (e : L ⧸ N ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))
    {J : Subgroup L} (hJ : Group.IsPerfect J) (hJt : J ≤ centralizer ({t} : Set L))
    (hNJ : N ⊔ J = ⊤) :
    F ⊔ J = ⊤ ∧ J ⊓ F = ⊥ ∧ CFSG.IsQuasisimple J ∧ J ⊓ N = (center J).map J.subtype ∧
      (center J).map J.subtype = S ∧ S = (CFSG.pCore 2 J).map J.subtype ∧
      Nonempty (J ⧸ CFSG.pCore 2 J ≃* L ⧸ N) ∧ Nat.card (center J) = 2 ∧
      Function.Bijective ((QuotientGroup.mk' F).comp J.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : N.subgroupOf J ≤ center J := by
    intro x hx
    rw [mem_subgroupOf] at hx
    have hxt : (x : L) ∈ N ⊓ centralizer ({t} : Set L) := mem_inf.mpr ⟨hx, hJt x.2⟩
    obtain ⟨z, hz, hzx⟩ := hZ hxt
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have h2 := congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hJt y.2⟩)
    show (y : L) * x = x * y
    rw [← hzx]
    exact h2
  obtain ⟨hJq, hZeq, hZle, ⟨eJ⟩⟩ := perfect_supplement_quasisimple hsimple hnab hs5 e hJ hNJ hcen
  have hFJ := fitting_sup_eq_top hNFS hS ht2 hJt hNJ
  have hcardJN : Nat.card (J ⊓ N : Subgroup L) = Nat.card (center J) := by
    rw [hZeq, ← card_map_of_injective J.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have hJF : J ⊓ F = ⊥ := by
    have h1 : Nat.card (J ⊓ F : Subgroup L) ∣ Nat.card (J ⊓ N : Subgroup L) :=
      card_dvd_of_le (inf_le_inf_left J hFN)
    rw [hcardJN] at h1
    have h2 : Nat.card (J ⊓ F : Subgroup L) ∣ Nat.card F := card_dvd_of_le inf_le_right
    have h3 : Nat.card (J ⊓ F : Subgroup L) ≤ 2 := (Nat.le_of_dvd Nat.card_pos h1).trans hZle
    have h4 : Odd (Nat.card (J ⊓ F : Subgroup L)) := Odd.of_dvd_nat hodd h2
    have h5 : Nat.card (J ⊓ F : Subgroup L) = 1 := by
      have h6 := Nat.card_pos (α := (J ⊓ F : Subgroup L))
      obtain ⟨k, hk⟩ := h4
      omega
    exact card_eq_one.mp h5
  have hbij : Function.Bijective ((QuotientGroup.mk' F).comp J.subtype) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      have h1 : (x : L) ∈ J ⊓ F := mem_inf.mpr ⟨x.2, hx⟩
      rw [hJF, mem_bot] at h1
      rw [mem_bot]
      exact Subtype.ext h1
    · intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective F y
      have hx : x ∈ ((F ⊔ J : Subgroup L) : Set L) := by
        rw [hFJ]
        exact (mem_top x : x ∈ (⊤ : Subgroup L))
      rw [normal_mul, Set.mem_mul] at hx
      obtain ⟨f, hf, j, hj, rfl⟩ := hx
      refine ⟨⟨j, hj⟩, ?_⟩
      rw [MonoidHom.comp_apply, subtype_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff f).mpr hf, one_mul]
  have hcardZ : Nat.card (center J) = 2 := by
    have h1 : Nat.card J = Nat.card (L ⧸ F) := Nat.card_eq_of_bijective _ hbij
    have h2 : Nat.card J = Nat.card (L ⧸ N) * Nat.card (center J) := by
      rw [← Nat.card_congr eJ.toEquiv, ← card_eq_card_quotient_mul_card_subgroup]
    have h3 : Nat.card L = Nat.card (L ⧸ F) * Nat.card F :=
      card_eq_card_quotient_mul_card_subgroup F
    have h4 : Nat.card L = Nat.card (L ⧸ N) * Nat.card N :=
      card_eq_card_quotient_mul_card_subgroup N
    have h5 : Nat.card N = 2 * Nat.card F := by
      have h6 := Subgroup.relIndex_mul_card (H := F) (K := N)
      rw [inf_eq_left.mpr hFN, hidx] at h6
      exact h6.symm
    have h6 : Nat.card (L ⧸ F) = 2 * Nat.card (L ⧸ N) := by
      have h7 : (2 * Nat.card (L ⧸ N)) * Nat.card F = Nat.card (L ⧸ F) * Nat.card F := by
        rw [← h3, h4, h5]
        ring
      exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h7).symm
    have h7 : Nat.card (L ⧸ N) * Nat.card (center J) = Nat.card (L ⧸ N) * 2 := by
      rw [← h2, h1, h6, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h7
  have hJNS : J ⊓ N ≤ S := by
    intro u hu
    have huN : u ∈ N ⊓ centralizer ({t} : Set L) :=
      mem_inf.mpr ⟨(mem_inf.mp hu).2, hJt (mem_inf.mp hu).1⟩
    rw [hCN] at huN
    have huset : u ∈ ((⁅F, F⁆ ⊔ S : Subgroup L) : Set L) := huN
    rw [normal_mul, Set.mem_mul] at huset
    obtain ⟨f, hf, v, hv, rfl⟩ := huset
    have hu2 : (f * v) ^ 2 = 1 := by
      have h1 := orderOf_dvd_natCard (⟨f * v, hu⟩ : (J ⊓ N : Subgroup L))
      rw [hcardJN, hcardZ, Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have hv2 : v ^ 2 = 1 := by
      have h1 := orderOf_dvd_natCard (⟨v, hv⟩ : S)
      rw [hS2, Subgroup.orderOf_mk] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have hf2 : f ^ 2 = 1 := by
      have hcomm : Commute f v := (mem_center_iff.mp (hFZ hf) v).symm
      rw [hcomm.mul_pow, hv2, mul_one] at hu2
      exact hu2
    have hfF : f ∈ F := commutator_le_left F F hf
    have hff : f = f⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact hf2)
    have h1 := eq_one_of_eq_inv_of_odd hodd (w := (⟨f, hfF⟩ : F)) (Subtype.ext (by
      rw [Subgroup.coe_inv]
      exact hff))
    have hf1 : f = 1 := congrArg Subtype.val h1
    rw [hf1, one_mul]
    exact hv
  have hJN : J ⊓ N = S := eq_of_le_of_card_ge hJNS (by rw [hS2, hcardJN, hcardZ])
  have hZS : (center J).map J.subtype = S := by
    rw [hZeq, subgroupOf_map_subtype, inf_comm, hJN]
  have hO2J : CFSG.pCore 2 J = center J := by
    apply le_antisymm
    · exact le_center_of_isSolvable_of_isQuasisimple hJq (CFSG.pCore 2 J) (by
        have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 J)).isNilpotent
        infer_instance)
    · exact CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance
        (IsPGroup.of_card (n := 1) (by rw [hcardZ, pow_one]))
  refine ⟨hFJ, hJF, hJq, ?_, hZS, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hO2J).trans eJ⟩,
    hcardZ, hbij⟩
  · rw [hJN, hZS]
  · rw [hO2J, hZS]

theorem two_core_free_radical_Sylow_involution_has_central_radical_centralizer
    {L : Type*}
    [Group L] [Finite L] (hSQT : CFSG.IsStronglyQuasithin L) (hO2 : CFSG.pCore 2 L = ⊥)
    (hLC : CFSG.IsCComponent (⊤ : Subgroup L)) (hq : ¬ CFSG.IsQuasisimple L) :
    CFSG.fittingSubgroup L ≠ ⊥ ∧ Odd (Nat.card (CFSG.fittingSubgroup L)) ∧
      (∃ (s : ℕ) (_ : Fact s.Prime), 5 ≤ s ∧ Nonempty (L ⧸ CFSG.solvableRadical L ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))) ∧
      ∀ S : Subgroup L, CFSG.ABGLocalTools.IsSylowOf 2 S (CFSG.solvableRadical L) →
        Nat.card S = 2 ∧ ∀ t ∈ S, t ≠ 1 →
          S = zpowers t ∧ CFSG.solvableRadical L = CFSG.fittingSubgroup L ⊔ S ∧
          CFSG.fittingSubgroup L ⊓ S = ⊥ ∧
          CFSG.fittingSubgroup L ⊓ centralizer ({t} : Set L) =
            ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ∧
          ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ≤ center L ∧
          CFSG.solvableRadical L ⊓ centralizer ({t} : Set L) =
            ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ⊔ S ∧
          ⁅CFSG.fittingSubgroup L, CFSG.fittingSubgroup L⁆ ⊓ S = ⊥ ∧
          CFSG.solvableRadical L ⊓ centralizer ({t} : Set L) ≤
            (center (centralizer ({t} : Set L))).map (centralizer ({t} : Set L)).subtype ∧
          ∀ J : Subgroup L, Group.IsPerfect J → J ≤ centralizer ({t} : Set L) →
            CFSG.solvableRadical L ⊔ J = ⊤ →
            CFSG.fittingSubgroup L ⊔ J = ⊤ ∧ J ⊓ CFSG.fittingSubgroup L = ⊥ ∧
            CFSG.IsQuasisimple J ∧ J ⊓ CFSG.solvableRadical L = (center J).map J.subtype ∧
            (center J).map J.subtype = S ∧ S = (CFSG.pCore 2 J).map J.subtype ∧
            Nonempty (J ⧸ CFSG.pCore 2 J ≃* L ⧸ CFSG.solvableRadical L) ∧
            Nat.card (center J) = 2 ∧
            Function.Bijective ((QuotientGroup.mk' (CFSG.fittingSubgroup L)).comp J.subtype) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr (by
    rw [_root_.commutator_def]
    exact hLC.2.1)
  have hNn : (CFSG.solvableRadical L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hset := radical_setup hSQT hO2 hLC hq
  obtain ⟨hFne, hodd, hFN, hNc, hidx, hsimple, hnab, hsL⟩ := hset
  refine ⟨hFne, hodd, hsL, fun S hS => ?_⟩
  have hsyl := sylow_two_of_relIndex_two hFN hodd hidx hS
  obtain ⟨hS2, hFS, hNFS, hgen⟩ := hsyl
  refine ⟨hS2, fun t ht ht1 => ?_⟩
  have hSt := hgen t ht ht1
  have htF : t ∉ CFSG.fittingSubgroup L := fun h => ht1 (by
    have h1 : t ∈ CFSG.fittingSubgroup L ⊓ S := mem_inf.mpr ⟨h, ht⟩
    rwa [hFS, mem_bot] at h1)
  have htN : t ∈ CFSG.solvableRadical L := by
    rw [hNFS]
    exact mem_sup_right ht
  have ht2 : t * t = 1 := by
    have h1 := orderOf_dvd_natCard (⟨t, ht⟩ : S)
    rw [hS2, Subgroup.orderOf_mk] at h1
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hcrit := all_prime_critical_actions_self hSQT hO2 hLC hq
  obtain ⟨-, hcrit⟩ := hcrit
  have hcores : ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
      CFSG.pCore r L ⊓ centralizer ({t} : Set L) = ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ∧
        ⁅CFSG.pCore r L, CFSG.pCore r L⁆ ≤ center L := by
    intro r hr
    have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hr))
    obtain ⟨hQL, D, hDc, hD, hker⟩ := hcrit r hr
    exact pCore_inf_centralizer_eq_commutator hr2 hodd hQL D hD hker
      (criticalAction_eq_inv hD hker htF fun l => hNc t htN l)
  obtain ⟨hCF, hFZ⟩ := fitting_inf_centralizer_eq_commutator hcores
  obtain ⟨hCN, hFS', hCNZ⟩ := radical_centralizer hNFS hSt hFS hCF hFZ
  obtain ⟨s, hs, hs5, ⟨e⟩⟩ := hsL
  refine ⟨hSt, hNFS, hFS, hCF, hFZ, hCN, hFS', hCNZ, fun J hJ hJt hNJ => ?_⟩
  exact perfect_supplement_structure hFN hodd hidx hNFS hSt hS2 ht2 hCN hFZ hCNZ hsimple hnab
    hs5 e hJ hJt hNJ

end CFSG.Quasithin.H13.NQBlock
