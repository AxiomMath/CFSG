module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourFixed

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section FourSpecial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem normConcl_of_special_four {p n : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {Y : Submodule K V}
    (hSU : UnitaryThreeInput) (hK2 : Nat.card K = 2) (hp3 : p = 3) (hn4 : n = 4)
    (S : OrbitData Q p n A Y) {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V}
    (hE : EndData p (orthDerived Q) A D a) {h : K[X]}
    (hh : h ∈ primaryFactors a.toLinearMap) (hne : h ≠ X - 1)
    (hX : D ≤ ⁅supportedBlock Q a h, supportedBlock Q a h⁆) : NormConcl p A D := by
  classical
  have hpq : p ∣ Nat.card K + 1 := by rw [hK2, hp3]
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd S.prime S.odd
  have hIso : IsoGroup (QuadraticMap.polarBilin Q) p A :=
    isoGroup_of_le S.regular S.le_omega S.elem
  have haA : a ∈ A := hE.a_mem
  have hap : a ^ p = 1 := S.elem.2 a haA
  have hx : OddOrderIsometry Q p a :=
    ⟨orthDerived_le_orthogonalGroup (S.le_omega haA), hap, hpK, fun v hv =>
      S.regular.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hself : h = reciprocalPolynomial h :=
    CFSG.LieType.SeitzGeneration.OrthBlk.selfDual_of_dvd hx hh (d := 1) (by rwa [pow_one])
  have hdeg : h.natDegree = 2 :=
    SpNS.natDegree_eq_two S.prime S.odd hpK
      (CoordSU.dvd_cyclotomic_of_dvd S.prime (irreducible_of_mem_primaryFactors hh)
        (monic_of_mem_primaryFactors hh) (by rw [C_1]; exact hx.dvd_X_pow_sub_one hh)
        (by rw [C_1]; exact hne)) hpq
  set B := QuadraticMap.polarBilin Q with hB
  have hUeq : orbitSpace a.toLinearMap h = primaryComponent a.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hc := hx.isCompl_orbit_others hh
  have horth : ∀ u ∈ orbitSpace a.toLinearMap h, ∀ r ∈ othersSpace a.toLinearMap h, B u r = 0 :=
    fun u hu r hr => by
      rw [hB, QuadraticMap.polarBilin_apply_apply]
      exact hx.polar_orbit_others hh hu hr
  have hcomm : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (TableB.IsElemAbelian.comm S.elem hg haA)
  have hUinv : ∀ g ∈ A, ∀ s ∈ orbitSpace a.toLinearMap h, g s ∈ orbitSpace a.toLinearMap h :=
    fun g hg s hs => mem_orbitSpace_of_apply (hcomm g hg) hs
  have hRinv : ∀ g ∈ A, ∀ s ∈ othersSpace a.toLinearMap h, g s ∈ othersSpace a.toLinearMap h :=
    fun g hg s hs => mem_othersSpace_of_apply (hcomm g hg) hs
  have hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0 := fun y hy y' hy' => by
    have h1 := S.singular (y + y') (Y.add_mem hy hy')
    rw [hB, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h1, S.singular y hy,
      S.singular y' hy']
    simp
  have hsplit : Y ⊓ orbitSpace a.toLinearMap h ≠ ⊥ ∨ Y ⊓ othersSpace a.toLinearMap h ≠ ⊥ :=
    inter_ne_bot_or S.ne_bot fun y hy =>
      exists_split_orbit hx (h := h) (Y := Y) (fun y hy => S.inv a haA y hy) hy
  have ha1 : a ≠ 1 := hE.a_ne
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  have hker1 : (resHom A (orbitSpace a.toLinearMap h) hUinv).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hgU : ∀ u ∈ orbitSpace a.toLinearMap h, (g : V ≃ₗ[K] V) u = u := fun u hu =>
      congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨u, hu⟩)
    have hgz : (g : V ≃ₗ[K] V) ∈ Subgroup.zpowers a := by
      refine hE.A_cent g g.2 fun d hd => ?_
      exact commute_of_fix_orbit hx hh (hcomm g g.2) hgU (commutator_self_le _ (hX hd))
    by_contra hg1
    have hg1' : (g : V ≃ₗ[K] V) ≠ 1 := fun e => hg1 (Subtype.ext e)
    have hgp : (g : V ≃ₗ[K] V) ^ p = 1 := S.elem.2 _ g.2
    have hog : orderOf (g : V ≃ₗ[K] V) = p := orderOf_eq_prime hgp hg1'
    have hzeq : Subgroup.zpowers (g : V ≃ₗ[K] V) = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hog])
    have hfix : Subgroup.zpowers (g : V ≃ₗ[K] V) ≤
        fixingSubgroup (V ≃ₗ[K] V) (orbitSpace a.toLinearMap h : Set V) :=
      Subgroup.zpowers_le.mpr ((mem_fixingSubgroup_iff _).mpr fun u hu => hgU u hu)
    have haU : ∀ u ∈ orbitSpace a.toLinearMap h, a u = u := fun u hu =>
      (mem_fixingSubgroup_iff _).mp (hfix (hzeq ▸ Subgroup.mem_zpowers a)) u hu
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hvU : v ∈ orbitSpace a.toLinearMap h := hUeq ▸ hv
    have h0 := mem_primaryComponent.mp hv
    rw [aeval_apply_of_fixed h (haU v hvU)] at h0
    exact hv0 ((smul_eq_zero.mp h0).resolve_left (eval_one_ne_zero hh hne))
  have hker0 : Nat.card (resHom A (orbitSpace a.toLinearMap h) hUinv).ker ≤ p ^ 0 := by
    rw [hker1, Subgroup.card_bot]
    simp
  have hRb : Nat.card (resHom A (othersSpace a.toLinearMap h) hRinv).range ≤ p ^ 0 :=
    card_res_comp_le S.prime hpK S.root hIso hc hUinv hRinv horth S.inv hYiso hsplit
      S.finrank_eq S.card_eq hker0
  have hRsub : Subsingleton (resHom A (othersSpace a.toLinearMap h) hRinv).range :=
    Finite.card_le_one_iff_subsingleton.mp (by simpa using hRb)
  have hgR : ∀ g : A, ∀ r ∈ othersSpace a.toLinearMap h, (g : V ≃ₗ[K] V) r = r := by
    intro g r hr
    have h1 := Subsingleton.elim (⟨resHom A (othersSpace a.toLinearMap h) hRinv g, g, rfl⟩ :
      (resHom A (othersSpace a.toLinearMap h) hRinv).range) 1
    exact congrArg Subtype.val (LinearEquiv.congr_fun (congrArg Subtype.val h1) ⟨r, hr⟩)
  have hgM : ∀ g : A, (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q a := fun g =>
    mem_isometryCentralizer.mpr
      ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (S.le_omega g.2)) v, fun v =>
        congrArg (fun f : V ≃ₗ[K] V => f v)
          (Subgroup.mem_centralizer_singleton_iff.mp (hcomm g g.2))⟩
  have hAB : A ≤ supportedBlock Q a h := fun g hg =>
    mem_supportedBlock.mpr ⟨hgM ⟨g, hg⟩, fun r hr => hgR ⟨g, hg⟩ r hr⟩
  have hAU : Nat.card A = Nat.card (resHom A (orbitSpace a.toLinearMap h) hUinv).range := by
    have := Subgroup.card_ker_mul_card_range (resHom A (orbitSpace a.toLinearMap h) hUinv)
    rw [hker1, Subgroup.card_bot, one_mul] at this
    exact this.symm
  have hUdim : n - 1 ≤ finrank K (orbitSpace a.toLinearMap h) / 2 := by
    have h1 := card_res_le S.prime hpK hIso hc hUinv horth
    rw [← hAU, S.card_eq] at h1
    exact (Nat.pow_le_pow_iff_right S.prime.one_lt).mp h1
  have hmult : n - 1 ≤ primaryMultiplicity a.toLinearMap h := by
    have h1 := finrank_primaryComponent (x := a.toLinearMap) (a := h)
    rw [hUeq] at hUdim
    rw [hdeg] at h1
    have h2 : primaryMultiplicity a.toLinearMap h =
        finrank (AdjoinRoot h) (primaryComponent a.toLinearMap h) := rfl
    omega
  have hDF : D ≤ specialBlock Q a h := fun d hd =>
    commutator_supportedBlock_le_specialBlock h (hX hd)
  by_cases h4 : 4 ≤ primaryMultiplicity a.toLinearMap h
  · have hFq := hx.isQuasisimple_specialBlock_selfDual_of_four_le S.prime
      (S.prime.odd_of_ne_two S.odd) hh hne hself h4
    set F := specialBlock Q a h with hF
    have hFM : F ≤ isometryCentralizer Q a := specialBlock_le_isometryCentralizer h
    have hFΩ : F ≤ orthDerived Q := specialBlock_le_orthDerived_of_perfect hFq.1
      (hFM.trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
    have hFn : ∀ b ∈ F, ∀ d ∈ D, b * d * b⁻¹ ∈ D := fun b hb d hd =>
      hE.D_norm b (hFΩ hb) (Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (hFM hb)).2) d hd
    have hDeq : D = F := StdSubRestThree.eq_of_le_of_quasisimple hDF hFn hFq hE.D_qs
    set φ : A →* AdjoinRoot h := (blockDet Q a h).comp (Subgroup.inclusion hAB) with hφ
    set φ' : A →* (AdjoinRoot h)ˣ := φ.toHomUnits with hφ'
    have hrange : Nat.card φ'.range ≤ p := by
      have hle : φ'.range ≤ rootsOfUnity p (AdjoinRoot h) := by
        rintro _ ⟨g, rfl⟩
        rw [mem_rootsOfUnity, ← map_pow]
        have : g ^ p = 1 := Subtype.ext (S.elem.2 _ g.2)
        rw [this, map_one]
      exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity (AdjoinRoot h) p)
    have hkerc := Subgroup.card_ker_mul_card_range φ'
    have hEA : φ'.ker.map A.subtype ≤ A := Subgroup.map_subtype_le _
    have hEF : φ'.ker.map A.subtype ≤ F := by
      rintro _ ⟨g, hg, rfl⟩
      refine mem_specialBlock.mpr ⟨hAB g.2, ?_⟩
      have h1 : φ' g = 1 := hg
      exact congrArg Units.val h1
    have hEcard : p ^ 2 ≤ Nat.card (φ'.ker.map A.subtype) := by
      have hmapcard : Nat.card (φ'.ker.map A.subtype) = Nat.card φ'.ker :=
        (Nat.card_congr (φ'.ker.equivMapOfInjective A.subtype A.subtype_injective).toEquiv).symm
      rw [hmapcard]
      have h1 : p ^ (n - 1) ≤ Nat.card φ'.ker * p := by
        rw [← S.card_eq, ← hkerc]
        exact Nat.mul_le_mul_left _ hrange
      have hn2 : n - 1 = (n - 2) + 1 := by omega
      rw [hn2, pow_succ] at h1
      have h2 : p ^ (n - 2) ≤ Nat.card φ'.ker := Nat.le_of_mul_le_mul_right h1 S.prime.pos
      exact (Nat.pow_le_pow_right S.prime.pos (by omega)).trans h2
    have hVtop : primaryComponent a.toLinearMap h = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := finrank_primaryComponent (x := a.toLinearMap) (a := h)
      rw [hdeg] at h1
      have h2 : primaryMultiplicity a.toLinearMap h =
          finrank (AdjoinRoot h) (primaryComponent a.toLinearMap h) := rfl
      have h3 := S.finrank_eq
      have h5 := Submodule.finrank_le (primaryComponent a.toLinearMap h)
      omega
    obtain ⟨U', hU'F, hU'1, hU'2, hU'A⟩ := exists_twoSubgroup_special hx
      (S.prime.odd_of_ne_two S.odd) hh hne hself (fun g hg => hgM ⟨g, hg⟩) haA S.inv S.ne_bot
      (fun y _ => by rw [hVtop]; trivial) S.singular
    have hp2 : p < p ^ 2 := by
      have := S.prime.one_lt
      nlinarith
    exact normConcl_of_card S.prime hE hEA (hDeq ▸ hEF) (lt_of_lt_of_le hp2 hEcard) hU'1
      (le_of_le_of_eq hU'F hDeq.symm) hU'2 hU'A
  · have hm3 : primaryMultiplicity a.toLinearMap h = 3 := by omega
    subst hp3
    have hsolv := hSU K hK2 V Q a hx h hh hne hself hm3
    haveI : Group.IsSolvable (specialBlock Q a h) := hsolv
    exact (not_isSolvable_of_isQuasisimple hE.D_qs
      (solvable_of_solvable_injective (Subgroup.inclusion_injective hDF))).elim

end FourSpecial

end SmallOrthUn

end CFSG.StandardType

end
