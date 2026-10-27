module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FUnitary
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FAbelianPreimage
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.IrredThree
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.GorensteinLyons
open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.GroupTheory.SteinbergBK
open CFSG.Blueprint (LieModel)

theorem uc22s2114r4f_diag_range_eq_torus {p f m q : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 4 ≤ m) [Fact q.Prime] [NeZero q]
    (ζ : Kˣ) (hζ : orderOf ζ = q) (hμ : ∀ s ∈ rootsOfUnity q K, h.norm (s : K) = 1) :
    ((QuotientGroup.mk' (normOneScalars h (gramSU h
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) m)).comp
      (uc22s2114r3f_diagSU h (by omega) (rootsOfUnity q K) hμ)).range =
    (closure (Set.range (unitaryTorusFamily m 2 (by omega) h
      (hμ ζ (by
        rw [mem_rootsOfUnity]; rw [← hζ]; exact pow_orderOf_eq_one ζ))))).map
      (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h m).toMonoidHom := by
  classical
  have hζroot : IsPrimitiveRoot ζ q := by rw [← hζ]; exact IsPrimitiveRoot.orderOf ζ
  have hζmem : ζ ∈ rootsOfUnity q K := by rw [mem_rootsOfUnity, ← hζ]; exact pow_orderOf_eq_one ζ
  let δ := CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h m
  let μ := rootsOfUnity q K
  let d := (QuotientGroup.mk' (normOneScalars h (gramSU h
    ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) m)).comp
      (uc22s2114r3f_diagSU h (by omega) μ hμ)
  let c : Fin 2 → unitaryPSU h m := unitaryTorusFamily m 2 (by omega) h (hμ ζ hζmem)
  have hc : ∀ i : Fin 2, δ (c i) = d (fun j => if j = i then ⟨ζ, hζmem⟩ else 1) := by
    intro i
    rw [show c i = unitaryProj h m (unitaryDiagHom h m
      ⟨torusVec ζ ⟨i, by omega⟩ ⟨2, by omega⟩,
        torusVec_mem_normOneProdOne h (hμ ζ hζmem) _ _⟩) from rfl]
    rw [CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.psi_unitaryProj]
    congr 1
    apply Subtype.ext
    apply Units.ext
    simp only [CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.suIota_val]
    rw [coe_unitaryDiagHom, uc22s2114r3f_coe_diagSU]
    congr 1
    funext j
    have heq : ∀ k : ℕ, ∀ hk : k < m, j = (⟨k, hk⟩ : Fin m) ↔ j.val = k :=
      fun k hk => ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
    fin_cases i <;> simp [torusVec_apply, heq] <;> split_ifs <;> simp_all
  have hμcyc : ∀ a : μ, ∃ z : ℤ, (a : Kˣ) = ζ ^ z := by
    intro a
    have ha : (a : Kˣ) ∈ zpowers ζ := by rw [hζroot.zpowers_eq]; exact a.2
    obtain ⟨z, hz⟩ := mem_zpowers_iff.1 ha
    exact ⟨z, hz.symm⟩
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨a, ha⟩ := hμcyc (s 0)
    obtain ⟨b, hb⟩ := hμcyc (s 1)
    have hs : s = (fun j => if j = (0 : Fin 2) then (⟨ζ, hζmem⟩ : μ) else 1) ^ a *
        (fun j => if j = (1 : Fin 2) then (⟨ζ, hζmem⟩ : μ) else 1) ^ b := by
      funext j
      fin_cases j <;> apply Subtype.ext <;> simp [ha, hb]
    rw [hs, map_mul, map_zpow, map_zpow, ← hc, ← hc]
    exact mul_mem
      (zpow_mem (mem_map_of_mem δ.toMonoidHom
        (subset_closure (show c 0 ∈ Set.range c from ⟨0, rfl⟩))) _)
      (zpow_mem (mem_map_of_mem δ.toMonoidHom
        (subset_closure (show c 1 ∈ Set.range c from ⟨1, rfl⟩))) _)
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ d.range.comap δ.toMonoidHom := by
      apply (closure_le (d.range.comap δ.toMonoidHom)).2 ?_ hx
      rintro _ ⟨i, rfl⟩
      change δ (c i) ∈ d.range
      rw [hc]
      exact ⟨_, rfl⟩
    exact hx'

theorem uc22s2114r4f_diagonal_preimage_commutative
    {Y H : Type} [Group Y] [Group H] [Finite H] {p f m q : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hm : 4 ≤ m) (hq : q.Prime) (hq2 : q ≠ 2)
    [NeZero q] (ζ : Kˣ) (hζ : orderOf ζ = q)
    (hμ : ∀ s ∈ rootsOfUnity q K, h.norm (s : K) = 1)
    (e : Y ≃* primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    (M₀ : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    (π : H →* Y) (hπ : Function.Surjective π) (hπZ : π.ker ≤ center H) :
    let d := e.symm.toMonoidHom.comp
      ((primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) M₀).toMonoidHom.comp
        ((QuotientGroup.mk' (normOneScalars h
          (gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) m)).comp
            (uc22s2114r3f_diagSU h (by omega) (rootsOfUnity q K) hμ)))
    IsMulCommutative ↥(d.range.comap π) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hζmem : ζ ∈ rootsOfUnity q K := by rw [mem_rootsOfUnity, ← hζ]; exact pow_orderOf_eq_one ζ
  let δ := CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h m
  let α := primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) M₀
  let d₀ := (QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) m)).comp
      (uc22s2114r3f_diagSU h (by omega) (rootsOfUnity q K) hμ)
  let d := e.symm.toMonoidHom.comp (α.toMonoidHom.comp d₀)
  let π₀ := δ.symm.toMonoidHom.comp (α.symm.toMonoidHom.comp (e.toMonoidHom.comp π))
  have hπ₀ : Function.Surjective π₀ :=
    δ.symm.surjective.comp (α.symm.surjective.comp (e.surjective.comp hπ))
  have hπ₀ker : π₀.ker = π.ker := by
    ext x
    change δ.symm (α.symm (e (π x))) = 1 ↔ π x = 1
    simp
  obtain ⟨_, _, hcomm, _, _⟩ := unitary_torus_lift_conclusions.{0, 0} hq2
    (n := m) (m := 2) (by omega) h H π₀ hπ₀ (hπ₀ker ▸ hπZ) ζ (hμ ζ hζmem) hζ
  let T : Subgroup (unitaryPSU h m) := closure (Set.range (unitaryTorusFamily m 2 (by omega)
    h (hμ ζ hζmem)))
  have hd₀ : d₀.range = T.map δ.toMonoidHom :=
    uc22s2114r4f_diag_range_eq_torus h hm ζ hζ hμ
  have hmem : ∀ x : H, π x ∈ d.range → π₀ x ∈ T := by
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have h₀ : e (π x) = α (d₀ s) := by
      rw [← hs]
      simp [d]
    have hsT : d₀ s ∈ T.map δ.toMonoidHom := hd₀ ▸ ⟨s, rfl⟩
    obtain ⟨t, ht, htd⟩ := hsT
    change δ.symm (α.symm (e (π x))) ∈ T
    rw [h₀, MulEquiv.symm_apply_apply, ← htd]
    simpa using ht
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact (hcomm (x : H) (hmem x x.2) (y : H) (hmem y y.2)).eq

theorem uc22s2114r4f_exists_fpf_abelian_preimage {Y : Type} [Group Y] {m f : ℕ} (hm : 4 ≤ m)
    (hX : LieModel Y .PSU m 2 f) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrq : ¬ r ∣ 2 ^ f + 1) {θ : MulAut Y} (hθr : θ ^ r = 1)
    (hθ : θ ∉ (MulAut.conj : Y →* MulAut Y).range) :
    ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ q ∣ 2 ^ f + 1 ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Finite A), IsPGroup q A ∧ ¬ IsCyclic A ∧
        ∃ κ : A →* A, (∀ a, κ a = a → a = 1) ∧
          ∃ ι : A →* Y, Function.Injective ι ∧ (∀ a, θ (ι a) = ι (κ a)) ∧
          ∀ (H : Type) [Group H] [Finite H] (π : H →* Y), Function.Surjective π →
            π.ker ≤ center H → IsMulCommutative ↥(ι.range.comap π) := by
  obtain ⟨K, _, h, e, σ, M₀, hrf, hcard, -, hM₀⟩ :=
    uc22s2114r4f_exists_field hm hX hr (by omega) hrq hθr hθ
  have := h.finite
  have hf1 := h.one_le
  have hf5 : 5 ≤ f := hr5.trans (Nat.le_of_dvd (by omega) hrf)
  have hfr : 1 ≤ f / r := Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos
  have hfr' : f / r < f := Nat.div_lt_self (by omega) hr.one_lt
  obtain ⟨q, hq, hqd, hqprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * f) (by omega) (by omega)
  have hfac : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [show 2 * f = f * 2 by ring, pow_mul, ← Nat.sq_sub_sq (2 ^ f) 1, one_pow]
  have hqf : q ∣ 2 ^ f + 1 :=
    (hq.dvd_mul.1 (hfac ▸ hqd)).resolve_right (hqprim f (by omega) (by omega))
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact hqprim 2 (by norm_num) (by omega) (by norm_num)
  have hq5 : q ≠ 5 := by
    rintro rfl
    exact hqprim 4 (by norm_num) (by omega) (by norm_num)
  have hq4 : q ≠ 4 := by
    rintro rfl
    exact absurd hq (by decide)
  have hq6 : q ≠ 6 := by
    rintro rfl
    exact absurd hq (by decide)
  have hq7 : 7 ≤ q := by
    have := hq.two_le
    omega
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) q
    (by rw [Nat.card_units, h.card]; exact hqd)
  have hζp : IsPrimitiveRoot ζ q := by
    rw [← hζ]
    exact IsPrimitiveRoot.orderOf ζ
  have hμq : Nat.card (rootsOfUnity q K) = q := hζp.card_rootsOfUnity'
  have hμ : ∀ s ∈ rootsOfUnity q K, h.norm (s : K) = 1 := by
    intro s hs
    obtain ⟨t, ht⟩ := hqf
    have hs' : (s : K) ^ q = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity q s).1 hs, Units.val_one]
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ', ht, pow_mul, hs',
      one_pow]
  let ι : (Fin 2 → rootsOfUnity q K) →* Y := e.symm.toMonoidHom.comp
    ((primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) M₀).toMonoidHom.comp
      ((QuotientGroup.mk' (normOneScalars h (gramSU h
        ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) m)).comp
          (uc22s2114r3f_diagSU h (by omega) (rootsOfUnity q K) hμ)))
  have hι : Function.Injective ι := e.symm.injective.comp
    ((primeFormConjHom h _ M₀).injective.comp
      (uc22s2114r3f_diagSU_injective h hm (rootsOfUnity q K) hμ))
  have hθι : ∀ s, θ (ι s) = ι ((restrictRootsOfUnity σ q).compLeft (Fin 2) s) := by
    intro s
    have hac : MulAut.congr e θ * primeFormConjHom h _ M₀ =
        primeFormConjHom h _ M₀ * primeFormFieldHom h isPrimeFormGram_one σ := by
      rw [← hM₀]
      simp only [mul_assoc, mul_inv_cancel_left]
    have h1 := DFunLike.congr_fun hac ((uc22s2114r3f_diagSU h (by omega)
      (rootsOfUnity q K) hμ s : gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
        primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    rw [MulAut.mul_apply, MulAut.mul_apply,
      uc22s2114r3f_primeFormFieldHom_diagSU h (by omega) (rootsOfUnity q K) hμ
        isPrimeFormGram_one σ (restrictRootsOfUnity σ q) (fun s => restrictRootsOfUnity_coe_apply σ s),
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at h1
    apply e.injective
    simpa [ι, MonoidHom.compLeft, Function.comp_def] using h1
  obtain ⟨hAp, hAc⟩ := uc22s2114r3f_isPGroup_pi (μ := rootsOfUnity q K) hq hμq
  have : Finite (rootsOfUnity q K) := Nat.finite_of_card_ne_zero (by rw [hμq]; exact hq.ne_zero)
  have hqq0 : ¬ q ∣ (2 ^ (f / r)) ^ 2 - 1 := by
    rw [← pow_mul, mul_comm]
    exact hqprim (2 * (f / r)) (by omega) (by omega)
  refine ⟨q, hq, hq7, hqf, Fin 2 → rootsOfUnity q K, inferInstance, inferInstance, hAp, hAc,
    (restrictRootsOfUnity σ q).compLeft (Fin 2), ?_, ι, hι, hθι, ?_⟩
  · intro s hs
    funext i
    have hsi : restrictRootsOfUnity σ q (s i) = s i := congrFun hs i
    refine Subtype.ext
      (uc22s2114r3f_eq_one_of_fixed hcard hq hqq0 ((mem_rootsOfUnity q _).1 (s i).2) ?_)
    rw [← restrictRootsOfUnity_coe_apply σ (s i), hsi]
  · intro H _ _ π hπ hπZ
    exact uc22s2114r4f_diagonal_preimage_commutative h hm hq hq2 ζ hζ hμ e M₀ π hπ hπZ



theorem uc22s2114r4f_false_of_psu_odd
    {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}
    (hGA : GriessAllModelsStatement) (hSg : UC6S846.SigmaStd D)
    (h74 : F07.R74Card D) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {m f : ℕ} (hm : 8 ≤ m)
    (hX : LieModel (BarInf L) .PSU m 2 f) {b : G}
    (hbB : b ∈ c.B0) (hbL : b ∈ normalizer (L : Set G))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : orderOf b = r)
    (hrn : r ∣ 2 ^ c.n - 1) (hodd : Odd c.n)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hrq : ¬ r ∣ 2 ^ f + 1 := uc22s2114r3f_not_dvd_two_pow_add_one hodd hr hr2 hrn
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have hb : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 :=
      Subtype.ext (hbr ▸ pow_orderOf_eq_one b)
    rw [hb, map_one]
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hrZ : ¬ r ∣ Nat.card (center (Bar2 L)) := by
    intro hdvd
    have hgen : r ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSU m 2 f).1 :=
      CFSG.LocalAnalysis.RankFourTheoremC.p_dvd_genericOrders_of_lieModel hGA hr hr5 hL.2.2
        e.symm (CFSG.Models.LieModel.of_blueprint (by decide) hX) hdvd
    have hgcdr : r ∣ Nat.gcd m (2 ^ f + 1) := by
      simpa [CFSG.Blueprint.Multiplier.genericOrders] using hgen
    exact hrq (hgcdr.trans (Nat.gcd_dvd_right _ _))
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) := by
    rw [uc22s2114r3f_card_solvableRadical hL]
    intro h
    rcases hr.dvd_mul.1 h with h2 | hZ
    · obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
      rw [hk] at h2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    · exact hrZ hZ
  obtain ⟨p, hp, hp2, hpf, X, hXp, hXc, hXfix⟩ :=
    uc22s2114r4f_exists_fixed_noncyclic (by omega) hX hr hr2 hrq hθr hin
  have hpσ : p ∈ D.sig := hSg.four_mem p hp hp2
    ((uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hp hp2 (fun h => by omega) hpf).trans
      (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le))
  obtain ⟨q, hq, hq7, hqf, A, _, _, hAq, hAc, κ, hκ, ι, hι, hθι, hpre⟩ :=
    uc22s2114r4f_exists_fpf_abelian_preimage (by omega) hX hr hr5 hrq hθr hin
  have hqr : q ≠ r := fun h => hrq (h ▸ hqf)
  obtain ⟨π, hπ, hπZ, hπβ⟩ := uc22s2114r4f_exists_central_bar2_map hL
  exact uc22s2114r4f_false_of_abelian_preimage hSg h74 hH c hL hbB hbL hr hr5 hbr hrK
    hp hp2 hpσ hXp hXc hXfix π hπ (hπβ b hbL) hq hq7 hqr hAq hAc κ hκ ι hι hθι
    (hpre (Bar2 L) π hπ hπZ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
