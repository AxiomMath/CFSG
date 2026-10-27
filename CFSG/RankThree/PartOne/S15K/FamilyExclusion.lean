module

public import CFSG.RankThree.PartOne.S15K.FamilyBlock
public import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.RankThree.PartOne.S15K.FamilyHerm

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial CFSG.GroupTheory.WeirSylow

section Stable

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem apply_mem_fixedSub {S : Subgroup (V ≃ₗ[K] V)} {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V))) {v : V} (hv : v ∈ fixedSubmodule S) :
    g v ∈ fixedSubmodule S := by
  intro s hs
  have hgi : g⁻¹ ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)) := inv_mem hg
  have h1 : g⁻¹ * s * g⁻¹⁻¹ ∈ S := ((Subgroup.mem_normalizer_iff.mp hgi) s).mp hs
  have h2 := hv _ h1
  have h3 : g ((g⁻¹ * s * g⁻¹⁻¹) v) = s (g v) := by
    rw [inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact g.apply_symm_apply _
  rw [← h3, h2]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem apply_mem_orthogonal_fixedSub {Q : QuadraticForm K V} {S : Subgroup (V ≃ₗ[K] V)}
    {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)))
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w : V}
    (hw : w ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSubmodule S)) :
    g w ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSubmodule S) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw ⊢
  intro f hf
  have hf' : g⁻¹ f ∈ fixedSubmodule S := apply_mem_fixedSub (inv_mem hg) hf
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (g⁻¹ f) w
  have h2 : g (g⁻¹ f) = f := by
    show g (g.symm f) = f
    exact g.apply_symm_apply f
  rw [h2] at h1
  have := hw _ hf'
  rw [QuadraticMap.polarBilin_apply_apply] at this ⊢
  rw [h1]
  exact this

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem aeval_mem_of_stable {x : V ≃ₗ[K] V} {R : Submodule K V} (hR : ∀ r ∈ R, x r ∈ R)
    (f : K[X]) {r : V} (hr : r ∈ R) : aeval x.toLinearMap f r ∈ R := by
  induction f using Polynomial.induction_on' generalizing r with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact R.add_mem (hp hr) (hq hr)
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine R.smul_mem _ ?_
    clear c
    induction n generalizing r with
    | zero => simpa using hr
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (hR r hr)

end Stable

section Card

theorem exists_third_of_card_three {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (a b : ι) :
    ∃ c, c ≠ a ∧ c ≠ b := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset ι) ⊆ {a, b} := fun c _ => by
    by_cases h1 : c = a
    · simp [h1]
    · simp [hcon c h1]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset ι).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, hι] at h1
  omega

theorem forall_eq_of_card_three {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) {a b c : ι}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : ι) : j = a ∨ j = b ∨ j = c := by
  classical
  have hs : ({a, b, c} : Finset ι) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc, hι]
  have : j ∈ ({a, b, c} : Finset ι) := by rw [hs]; exact Finset.mem_univ j
  simpa using this

theorem forall_eq_of_card_two {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2) {a b : ι}
    (hab : a ≠ b) (j : ι) : j = a ∨ j = b := by
  classical
  have hs : ({a, b} : Finset ι) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hab, hι]
  have : j ∈ ({a, b} : Finset ι) := by rw [hs]; exact Finset.mem_univ j
  simpa using this

end Card

section Main

open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem no_two_subgroup_selfDual_block (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hV : ¬ IsPlusType Q) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (hx : OddOrderIsometry Q p x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) {Γ : Type} [Group Γ] [Finite Γ]
    (hΓ : Nat.card Γ = p ^ 3) (g : Γ →* (V ≃ₗ[K] V)) (hgi : Function.Injective g)
    (hgO : ∀ e, g e ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgx : ∀ e, g e * x = x * g e)
    (hgc : ∀ e e', g e * g e' = g e' * g e) (hgp : ∀ e, g e ^ p = 1)
    {S : Subgroup (V ≃ₗ[K] V)} (hS : S ≤ supportedBlock Q x h) (hS2 : IsPGroup 2 S)
    (hxN : x ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V)))
    (hgN : ∀ e, g e ∈ Subgroup.normalizer (S : Set (V ≃ₗ[K] V))) (hSc : S ≤ ⁅S, g.range⁆) :
    S = ⊥ := by
  classical
  by_contra hSbot
  have hp3 : 3 < p := by omega
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne1).symm
  have horb : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hcompl : IsCompl (primaryComponent x.toLinearMap h) (othersSpace x.toLinearMap h) := by
    rw [← horb]
    exact hx.isCompl_orbit_others hh
  have horth : ∀ u ∈ primaryComponent x.toLinearMap h, ∀ o ∈ othersSpace x.toLinearMap h,
      QuadraticMap.polar Q u o = 0 := fun u hu o ho =>
    hx.polar_orbit_others hh (by rw [horb]; exact hu) ho
  have hSO : ∀ s ∈ S, s ∈ isometryCentralizer Q x := fun s hs =>
    supportedBlock_le_isometryCentralizer h (hS hs)
  have hSfix : ∀ s ∈ S, ∀ o ∈ othersSpace x.toLinearMap h, s o = o := fun s hs o ho =>
    (mem_supportedBlock.mp (hS hs)).2 o ho
  have hSiso : ∀ s ∈ S, ∀ u w, QuadraticMap.polar Q (s u) (s w) = QuadraticMap.polar Q u w :=
    fun s hs u w => TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (Subgroup.mem_inf.mp (hSO s hs)).1 u w
  obtain ⟨s1, hs1S, hs11⟩ : ∃ s ∈ S, s ≠ 1 := by
    obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hSbot
    exact ⟨s, hs, fun h1 => hs1 (Subtype.ext h1)⟩
  obtain ⟨r0, hr0F, hr00, hr0perp⟩ := exists_rad_fixed (B := QuadraticMap.polarBilin Q) hQ hS2
    (fun s hs u w => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
      exact hSiso s hs u w) ⟨s1, hs1S, hs11⟩
  set R : Submodule K V := fixedSubmodule S ⊓
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (fixedSubmodule S) with hR
  have hr0R : r0 ∈ R := ⟨hr0F, LinearMap.BilinForm.mem_orthogonal_iff.mpr hr0perp⟩
  have hOF : ∀ o ∈ othersSpace x.toLinearMap h, o ∈ fixedSubmodule S := fun o ho s hs => hSfix s hs o ho
  have hRVh : ∀ r ∈ R, r ∈ primaryComponent x.toLinearMap h := by
    intro r hr
    have hrperp : ∀ n ∈ fixedSubmodule S, QuadraticMap.polarBilin Q n r = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp hr.2
    obtain ⟨u, hu, o, ho, rfl⟩ := KCOrthogonal.exists_add_of_isCompl hcompl r
    have h1 : ∀ o' ∈ othersSpace x.toLinearMap h, QuadraticMap.polar Q o' o = 0 := by
      intro o' ho'
      have := hrperp o' (hOF o' ho')
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_comm Q o' u, horth u hu o' ho', zero_add] at this
      exact this
    have h2 : o = 0 := by
      refine hQ.1 o fun v => ?_
      obtain ⟨u', hu', o'', ho'', rfl⟩ := KCOrthogonal.exists_add_of_isCompl hcompl v
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_comm Q o u', horth u' hu' o ho, QuadraticMap.polar_comm Q o o'',
        h1 o'' ho'', zero_add]
    rw [h2, add_zero]
    exact hu
  have hRx : ∀ r ∈ R, x r ∈ R := fun r hr =>
    ⟨apply_mem_fixedSub hxN hr.1, apply_mem_orthogonal_fixedSub hxN hx.mem hr.2⟩
  have hRg : ∀ e, ∀ r ∈ R, g e r ∈ R := fun e r hr =>
    ⟨apply_mem_fixedSub (hgN e) hr.1, apply_mem_orthogonal_fixedSub (hgN e) (hgO e) hr.2⟩
  have hRiso : ∀ r ∈ R, ∀ r' ∈ R, QuadraticMap.polar Q r r' = 0 := fun r hr r' hr' => by
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hr'.2) r hr.1
    rwa [QuadraticMap.polarBilin_apply_apply] at this
  obtain ⟨D⟩ := nonempty_hermData hx hp hp3 hpq hh hne1
  have hpq' : p ∣ D.ℓ ^ D.f + 1 := by rw [D.card]; exact hpq
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ : IsPrimitiveRoot (AdjoinRoot.root h) p := by
    have := IsPrimitiveRoot.orderOf (AdjoinRoot.root h)
    rwa [orderOf_eq_prime hlamp hlam1] at this
  have hcomm : ∀ e, Commute (g e).toLinearMap x.toLinearMap := fun e =>
    LinearMap.ext fun v => by
      have := congrArg (fun z : V ≃ₗ[K] V => z v) (hgx e)
      simpa [Module.End.mul_apply] using this
  let T : Γ → Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) := fun e =>
    commutantRestrictHom h ⟨(g e).toLinearMap, (mem_commutant x.toLinearMap).mpr (hcomm e)⟩
  have hTapp : ∀ e (u : primaryComponent x.toLinearMap h), ((T e u : primaryComponent x.toLinearMap h) : V) =
      g e (u : V) := fun e u => rfl
  have hTmul : ∀ e e', T (e * e') = T e * T e' := fun e e' => by
    ext u
    simp only [hTapp, map_mul, Module.End.mul_apply, LinearEquiv.mul_apply]
  have hΓcomm : ∀ e e' : Γ, e * e' = e' * e := fun e e' =>
    hgi (by rw [map_mul, map_mul, hgc])
  have hTcomm : ∀ e e', Commute (T e) (T e') := fun e e' => by
    show T e * T e' = T e' * T e
    rw [← hTmul, ← hTmul, hΓcomm e e']
  have hTpowapp : ∀ (n : ℕ) e (u : primaryComponent x.toLinearMap h),
      (((T e ^ n) u : primaryComponent x.toLinearMap h) : V) = (g e ^ n) (u : V) := by
    intro n e
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, hTapp, LinearEquiv.mul_apply]
  have hTpow : ∀ e, T e ^ p = 1 := fun e => by
    ext u
    rw [hTpowapp, hgp]
    rfl
  have hTiso : ∀ e u w, D.B (T e u) (T e w) = D.B u w := by
    intro e u w
    have hsub : D.B (T e u) (T e w) - D.B u w = 0 := by
      refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot h) fun c => ?_
      rw [sub_mul, map_sub, D.trace, D.trace, ← map_smul (T e) c w, hTapp, hTapp,
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hgO e)]
      exact sub_self _
    exact sub_eq_zero.mp hsub
  let Rh : Submodule (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    { carrier := {v | (v : V) ∈ R}
      add_mem' := fun {a b} ha hb => R.add_mem ha hb
      zero_mem' := R.zero_mem
      smul_mem' := by
        intro c v hv
        obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
        show ((AdjoinRoot.mk h f • v : primaryComponent x.toLinearMap h) : V) ∈ R
        rw [coe_mk_smul_primaryComponent]
        exact aeval_mem_of_stable hRx f hv }
  have hRhne : Rh ≠ ⊥ := by
    intro hbot
    apply hr00
    have : (⟨r0, hRVh r0 hr0R⟩ : primaryComponent x.toLinearMap h) ∈ Rh := hr0R
    rw [hbot] at this
    exact congrArg Subtype.val ((Submodule.mem_bot _).mp this)
  have hRhst : ∀ e, ∀ r ∈ Rh, T e r ∈ Rh := fun e r hr => hRg e _ hr
  have hRhiso : ∀ r ∈ Rh, ∀ r' ∈ Rh, D.B r r' = 0 := by
    intro r hr r' hr'
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot h) fun c => ?_
    rw [D.trace]
    exact hRiso _ hr _ (Rh.smul_mem c hr')
  obtain ⟨b, μ, hbμ, hbo, j₁, j₂, hj12, hcoin⟩ := exists_coincident_of_isotropic_stable D.hU hζ hpq'
    D.symm D.sep T hTcomm hTpow hTiso hRhne hRhst hRhiso
  have hdeg2 : h.natDegree = 2 := by
    rw [← AdjoinRoot.powerBasis_dim hirr.ne_zero, ← (AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    exact D.finrank_eq
  have hVhdim : finrank K (primaryComponent x.toLinearMap h) =
      2 * finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := by
    rw [finrank_primaryComponent, hdeg2]
  have hmle : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) ≤ 4 := by
    have := Submodule.finrank_le (primaryComponent x.toLinearMap h)
    omega
  have hm2 : 2 ≤ finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := hm
  have hb0 : ∀ j, b j ≠ 0 := fun j => b.ne_zero j
  have hb1 : ∀ j, D.B (b j) (b j) = 1 := fun j => by simpa using hbo j j
  have hbr : ∀ i j, i ≠ j → D.B (b i) (b j) = 0 := fun i j hij => by simpa [hij] using hbo i j
  have hnk : ¬ p ∣ Nat.card K - 1 :=
    not_dvd_sub_one_of_dvd_add_one (Nat.succ_le_of_lt Finite.card_pos) (by omega) hpq
  have hPdim := fun j => D.finrank_plane (hb0 j)
  have hPreg := fun j => D.plane_regular (hb1 j)
  have hPan := fun j => D.plane_aniso hx hp hp5 hpq hne1 hh (hb1 j) (hb0 j)
  have hPorth := fun i j (hij : i ≠ j) => D.polar_plane_eq_zero (hbr i j hij)
  have hPle : ∀ j, normPlane x h (b j) ≤ primaryComponent x.toLinearMap h := fun j => by
    rintro _ ⟨c, rfl⟩
    exact (c • b j).2
  have hcomm_cent : ∀ e, g e ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun e =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hgx e)
  have hsx : ∀ s ∈ S, Commute s.toLinearMap x.toLinearMap := fun s hs =>
    LinearMap.ext fun v => by
      have := (mem_isometryCentralizer.mp (hSO s hs)).2 v
      simpa [Module.End.mul_apply] using this
  obtain hm | hm | hm : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 ∨
      finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 3 ∨
      finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 4 := by omega
  ·
    have hcard2 : Fintype.card (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h))) = 2 := by
      rw [Fintype.card_fin, hm]
    have hall : ∀ j, j = j₁ ∨ j = j₂ := forall_eq_of_card_two hcard2 hj12
    have hTscal : ∀ e, T e = μ e j₁ • LinearMap.id := by
      intro e
      refine b.ext fun j => ?_
      rw [hbμ, LinearMap.smul_apply, LinearMap.id_apply]
      rcases hall j with h1 | h1
      · rw [h1]
      · rw [h1, hcoin e]
    have hcommSg : ∀ s ∈ S, ∀ e, s * g e = g e * s := by
      intro s hs e
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, hu, o, ho, rfl⟩ := KCOrthogonal.exists_add_of_isCompl hcompl v
      simp only [LinearEquiv.mul_apply, map_add]
      congr 1
      · obtain ⟨f, hf⟩ := AdjoinRoot.mk_surjective (μ e j₁)
        have hsu : s u ∈ primaryComponent x.toLinearMap h := apply_mem_primaryComponent (hsx s hs) hu
        have h1 : g e u = aeval x.toLinearMap f u := by
          have := hTapp e ⟨u, hu⟩
          rw [hTscal e, LinearMap.smul_apply, LinearMap.id_apply, ← hf,
            coe_mk_smul_primaryComponent] at this
          exact this.symm
        have h2 : g e (s u) = aeval x.toLinearMap f (s u) := by
          have := hTapp e ⟨s u, hsu⟩
          rw [hTscal e, LinearMap.smul_apply, LinearMap.id_apply, ← hf,
            coe_mk_smul_primaryComponent] at this
          exact this.symm
        rw [h1, h2]
        exact congrArg (fun T : Module.End K V => T u) (commute_aeval (hsx s hs) f).eq
      · have hgo : g e o ∈ othersSpace x.toLinearMap h := mem_othersSpace_of_apply (hcomm_cent e) ho
        rw [hSfix s hs _ hgo, hSfix s hs o ho]
    have hcomm' : ⁅S, g.range⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      rintro s hs _ ⟨e, rfl⟩
      rw [Subgroup.mem_bot, commutatorElement_def]
      have := hcommSg s hs e
      calc s * g e * s⁻¹ * (g e)⁻¹ = g e * s * s⁻¹ * (g e)⁻¹ := by rw [this]
        _ = 1 := by group
    exact hSbot (le_bot_iff.mp (hSc.trans hcomm'))
  ·
    have hcard3 : Fintype.card
        (Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h))) = 3 := by
      rw [Fintype.card_fin, hm]
    obtain ⟨k, hk1, hk2⟩ := exists_third_of_card_three hcard3 j₁ j₂
    have hall : ∀ j, j = j₁ ∨ j = j₂ ∨ j = k :=
      forall_eq_of_card_three hcard3 hj12 (Ne.symm hk1) (Ne.symm hk2)
    have hT1 : T 1 = 1 := by
      ext u
      rw [hTapp, map_one]
      rfl
    have hμ1 : ∀ j, μ 1 j = 1 := fun j => by
      have h1 : T 1 (b j) = b j := by rw [hT1]; rfl
      rw [hbμ] at h1
      have h2 : (μ 1 j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 (hb0 j)
    have hμmul : ∀ e e' j, μ (e * e') j = μ e j * μ e' j := by
      intro e e' j
      have h1 : (μ (e * e') j) • b j = (μ e j * μ e' j) • b j := by
        rw [← hbμ, hTmul, Module.End.mul_apply, hbμ, map_smul, hbμ, smul_smul, mul_comm]
      exact smul_left_injective (AdjoinRoot h) (hb0 j) h1
    have hμpow' : ∀ (n : ℕ) e j, (T e ^ n) (b j) = μ e j ^ n • b j := by
      intro n e j
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, Module.End.mul_apply, hbμ, map_smul, ih, smul_smul, pow_succ']
    have hμpow : ∀ e j, μ e j ^ p = 1 := by
      intro e j
      have h1 := hμpow' p e j
      rw [hTpow e, Module.End.one_apply] at h1
      have h2 : (μ e j ^ p - 1) • b j = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 (hb0 j)
    have hμ0 : ∀ e j, μ e j ≠ 0 := fun e j h0 => by
      have := hμpow e j
      rw [h0, zero_pow hp.ne_zero] at this
      exact zero_ne_one this
    have hμinv : ∀ e j, μ e⁻¹ j * μ e j = 1 := fun e j => by
      rw [← hμmul, inv_mul_cancel, hμ1]
    have : Fintype Γ := Fintype.ofFinite Γ
    let Rts : Finset (AdjoinRoot h) := (Polynomial.nthRoots p (1 : AdjoinRoot h)).toFinset
    have hRts : ∀ c : AdjoinRoot h, c ^ p = 1 → c ∈ Rts := fun c hc => by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp.pos]
      exact hc
    have hRtscard : Rts.card ≤ p :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p 1)
    have hcardlt : (Rts ×ˢ Rts).card < (Finset.univ : Finset Γ).card := by
      rw [Finset.card_product, Finset.card_univ, ← Nat.card_eq_fintype_card, hΓ]
      calc Rts.card * Rts.card ≤ p * p := Nat.mul_le_mul hRtscard hRtscard
        _ = p ^ 2 := by ring
        _ < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    obtain ⟨e, -, e', -, hee', hΦ⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset Γ)) (t := Rts ×ˢ Rts) (f := fun e : Γ => (μ e j₁, μ e k)) hcardlt
      (fun e _ => Finset.mem_product.mpr ⟨hRts _ (hμpow e j₁), hRts _ (hμpow e k)⟩)
    have hΦ1 : μ e j₁ = μ e' j₁ := congrArg Prod.fst hΦ
    have hΦ2 : μ e k = μ e' k := congrArg Prod.snd hΦ
    have he''1 : e⁻¹ * e' ≠ 1 := fun h1 => hee' (inv_mul_eq_one.mp h1)
    have hμe'' : ∀ j, μ (e⁻¹ * e') j = 1 := by
      have key : ∀ j, μ e j = μ e' j → μ (e⁻¹ * e') j = 1 := fun j heq => by
        rw [hμmul, ← heq]
        exact hμinv e j
      have h1 := key j₁ hΦ1
      have h2 := key k hΦ2
      intro j
      rcases hall j with hj | hj | hj
      · rw [hj]; exact h1
      · rw [hj, ← hcoin]; exact h1
      · rw [hj]; exact h2
    have hT'' : T (e⁻¹ * e') = 1 := by
      refine b.ext fun j => ?_
      rw [hbμ, hμe'', one_smul]
      rfl
    have hgtriv : ∀ u ∈ primaryComponent x.toLinearMap h, g (e⁻¹ * e') u = u := fun u hu => by
      have := hTapp (e⁻¹ * e') ⟨u, hu⟩
      rw [hT''] at this
      exact this.symm
    have hOdim : finrank K (othersSpace x.toLinearMap h) = 2 := by
      have := Submodule.finrank_add_eq_of_isCompl hcompl
      omega
    have hOreg : ∀ v ∈ othersSpace x.toLinearMap h,
        (∀ u ∈ othersSpace x.toLinearMap h, QuadraticMap.polar Q v u = 0) → v = 0 := by
      intro v hv hperp
      refine hQ.1 v fun w => ?_
      obtain ⟨u', hu', o', ho', rfl⟩ := KCOrthogonal.exists_add_of_isCompl hcompl w
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_comm Q v u', horth u' hu' v hv, hperp o' ho', zero_add]
    have hOan : ∀ v ∈ othersSpace x.toLinearMap h, Q v = 0 → v = 0 := by
      refine eq_zero_of_singular_of_isometry (P := othersSpace x.toLinearMap h) hOdim hOreg hp
        (by omega) hnk (y := g (e⁻¹ * e'))
        (fun v => (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hgO _)) v)
        (fun v hv => mem_othersSpace_of_apply (hcomm_cent _) hv) (hgp _) ?_
      by_contra hcon
      push Not at hcon
      apply he''1
      apply hgi
      rw [map_one]
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, hu, o, ho, rfl⟩ := KCOrthogonal.exists_add_of_isCompl hcompl v
      rw [map_add, hgtriv u hu, hcon o ho]
      rfl
    exact hV (isPlusType_of_four_aniso_planes hdim (hPdim j₁) (hPdim j₂) (hPdim k) hOdim
      (hPreg j₁) (hPreg j₂) (hPreg k) hOreg (hPan j₁) (hPan j₂) (hPan k) hOan
      (hPorth j₁ j₂ hj12) (hPorth j₁ k (Ne.symm hk1)) (fun u hu w hw => horth u (hPle j₁ hu) w hw)
      (hPorth j₂ k (Ne.symm hk2)) (fun u hu w hw => horth u (hPle j₂ hu) w hw)
      (fun u hu w hw => horth u (hPle k hu) w hw))
  ·
    let idx : Fin 4 → Fin (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :=
      fun i => ⟨i.1, by have := i.2; omega⟩
    have hidx : Function.Injective idx := fun i j hij => Fin.ext (by simpa [idx] using hij)
    have hne : ∀ i j : Fin 4, i ≠ j → idx i ≠ idx j := fun i j hij h' => hij (hidx h')
    exact hV (isPlusType_of_four_aniso_planes hdim (hPdim _) (hPdim _) (hPdim _) (hPdim _)
      (hPreg _) (hPreg _) (hPreg _) (hPreg _) (hPan _) (hPan _) (hPan _) (hPan _)
      (hPorth _ _ (hne 0 1 (by decide))) (hPorth _ _ (hne 0 2 (by decide)))
      (hPorth _ _ (hne 0 3 (by decide))) (hPorth _ _ (hne 1 2 (by decide)))
      (hPorth _ _ (hne 1 3 (by decide))) (hPorth _ _ (hne 2 3 (by decide))))

end Main

section Transport

open scoped commutatorElement
open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem map_mem_normalizer_map {G H : Type*} [Group G] [Group H] (Ψ : G →* H)
    {S : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (S : Set G)) :
    Ψ t ∈ Subgroup.normalizer ((S.map Ψ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨t * s * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht s).mp hs, ?_⟩
    simp
  · rintro ⟨s', hs', hy⟩
    refine ⟨t⁻¹ * s' * t⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (inv_mem ht) s').mp hs', ?_⟩
    simp only [map_mul, map_inv, inv_inv]
    rw [hy]
    group

theorem special_selfDual_no_two_subgroup (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank K V = 8) (hV : ¬ IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {E : Type} [Group E] [Finite E] (hEcard : Nat.card E = p ^ 3)
    (a : E → ProjOrthDerived Q) (hap : ∀ e, a e ^ p = 1) (hacomm : ∀ e e', a e * a e' = a e' * a e)
    (hao : ∀ e, e ≠ 1 → orderOf (a e) = p) (hmul : ∀ e e', a (e * e') = a e * a e') (b : E)
    (x : orthDerived Q) (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a b) (hxp : orderOf x = p)
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h) {S : Subgroup (ProjOrthDerived Q)}
    (hS : S ≤ componentImage Q (x : V ≃ₗ[K] V) h) (hS2 : IsPGroup 2 S)
    (hSn : ∀ e, a e ∈ Subgroup.normalizer (S : Set (ProjOrthDerived Q)))
    (hSc : S ≤ ⁅S, (MonoidHom.mk' a hmul).range⁆) : S = ⊥ := by
  classical
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hinj := mk_injective_orth hQ
  set ρ : orthDerived Q →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  let ρe : orthDerived Q ≃* ProjOrthDerived Q := MulEquiv.ofBijective ρ ⟨hinj, hsurj⟩
  let Ψ : ProjOrthDerived Q →* (V ≃ₗ[K] V) := (orthDerived Q).subtype.comp ρe.symm.toMonoidHom
  have hΨinj : Function.Injective Ψ := Subtype.val_injective.comp ρe.symm.injective
  have hΨρ : ∀ y : orthDerived Q, Ψ (ρ y) = (y : V ≃ₗ[K] V) := fun y => by
    show ((ρe.symm (ρ y) : orthDerived Q) : V ≃ₗ[K] V) = y
    rw [show ρ y = ρe y from rfl, MulEquiv.symm_apply_apply]
  let aH : E →* ProjOrthDerived Q := MonoidHom.mk' a hmul
  have hainj : Function.Injective aH := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have h1 : a e = 1 := he
    have := hao e hne
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  let g : E →* (V ≃ₗ[K] V) := Ψ.comp aH
  have hgapp : ∀ e, g e = Ψ (a e) := fun e => rfl
  have hxΨ : Ψ (a b) = (x : V ≃ₗ[K] V) := by
    have := hΨρ x
    rw [← hxa]
    exact this
  have hxO : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hSΨ : S.map Ψ ≤ supportedBlock Q (x : V ≃ₗ[K] V) h := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨y, hy, hys⟩ := hS hs
    rw [← hys, hΨρ]
    exact specialBlock_le_supportedBlock h (Subgroup.mem_subgroupOf.mp hy)
  have hSc' : S.map Ψ ≤ ⁅S.map Ψ, g.range⁆ := by
    refine (Subgroup.map_mono hSc).trans ?_
    rw [Subgroup.map_commutator, MonoidHom.map_range]
  have := no_two_subgroup_selfDual_block hQ hdim hV hp hp5 hpq hxO hh hne1 hm (Γ := E) hEcard g
    (hΨinj.comp hainj) (fun e => orthDerived_le_orthogonalGroup (ρe.symm (a e)).2)
    (fun e => by rw [hgapp, ← hxΨ, ← map_mul, ← map_mul, hacomm])
    (fun e e' => by rw [hgapp, hgapp, ← map_mul, ← map_mul, hacomm])
    (fun e => by rw [hgapp, ← map_pow, hap, map_one]) hSΨ (hS2.map Ψ)
    (by rw [← hxΨ]; exact map_mem_normalizer_map Ψ (hSn b))
    (fun e => map_mem_normalizer_map Ψ (hSn e)) hSc'
  exact (Subgroup.map_eq_bot_iff_of_injective S hΨinj).mp this

end Transport

end CFSG.RankThree.PartOne.S15K
