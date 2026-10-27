module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnBlock

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

structure OrbitData {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p n : ℕ) (A : Subgroup (V ≃ₗ[K] V)) (Y : Submodule K V) : Prop where
  regular : (QuadraticMap.polarBilin Q).Nondegenerate
  prime : p.Prime
  odd : p ≠ 2
  root : ∀ c : K, c ^ p = 1 → c = 1
  finrank_eq : Module.finrank K V = 2 * n
  le_omega : A ≤ orthDerived Q
  elem : IsElemAbelian p A
  card_eq : Nat.card A = p ^ (n - 1)
  ne_bot : Y ≠ ⊥
  inv : ∀ g ∈ A, ∀ y ∈ Y, g y ∈ Y
  singular : ∀ y ∈ Y, Q y = 0

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p n : ℕ} {A : Subgroup (V ≃ₗ[K] V)}
  {Y : Submodule K V}

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) :=
  haveI : Finite V := Module.finite_of_finite K
  Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

theorem inter_ne_bot_or {U R : Submodule K V} (hY : Y ≠ ⊥)
    (hsplit : ∀ y ∈ Y, ∃ u ∈ Y ⊓ U, ∃ r ∈ Y ⊓ R, y = u + r) : Y ⊓ U ≠ ⊥ ∨ Y ⊓ R ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
  obtain ⟨u, hu, r, hr, rfl⟩ := hsplit y hy
  rw [hcon.1, Submodule.mem_bot] at hu
  rw [hcon.2, Submodule.mem_bot] at hr
  exact hy0 (by rw [hu, hr, add_zero])

theorem commutator_self_le {G : Type*} [Group G] (B : Subgroup G) : ⁅B, B⁆ ≤ B :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hg hh) (B.inv_mem hg)) (B.inv_mem hh)

theorem bigConcl_of_fixed (S : OrbitData Q p n A Y) (h5 : 5 ≤ n) {D : Subgroup (V ≃ₗ[K] V)}
    {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a)
    (hmem : (X - 1 : K[X]) ∈ primaryFactors a.toLinearMap)
    (hX : D ≤ ⁅supportedBlock Q a (X - 1), supportedBlock Q a (X - 1)⁆) : BigConcl p A D := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd S.prime S.odd
  have hIso : IsoGroup (QuadraticMap.polarBilin Q) p A :=
    isoGroup_of_le S.regular S.le_omega S.elem
  have haA : a ∈ A := hE.a_mem
  have hap : a ^ p = 1 := S.elem.2 a haA
  have hx : OddOrderIsometry Q p a :=
    ⟨orthDerived_le_orthogonalGroup (S.le_omega haA), hap, hpK, fun v hv =>
      S.regular.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  set B := QuadraticMap.polarBilin Q with hB
  obtain ⟨hc, horthP⟩ := hx.fixed_others
  have horth : ∀ u ∈ fixedSpace a, ∀ r ∈ othersSpace a.toLinearMap (X - 1), B u r = 0 :=
    fun u hu r hr => by
      rw [hB, QuadraticMap.polarBilin_apply_apply]
      exact horthP u hu r hr
  have hcomm : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (TableB.IsElemAbelian.comm S.elem hg haA)
  have hUinv : ∀ g ∈ A, ∀ s ∈ fixedSpace a, g s ∈ fixedSpace a := fun g hg s hs =>
    mem_fixedSpace_of_apply (hcomm g hg) hs
  have hRinv : ∀ g ∈ A, ∀ s ∈ othersSpace a.toLinearMap (X - 1),
      g s ∈ othersSpace a.toLinearMap (X - 1) := fun g hg s hs =>
    mem_othersSpace_of_apply (hcomm g hg) hs
  have hW : orbitSpace a.toLinearMap (X - 1) = fixedSpace a := by
    rw [orbitSpace, reciprocalPolynomial_X_sub_one, sup_idem, fixedSpace_eq_primaryComponent]
  have hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0 := fun y hy y' hy' => by
    have h1 := S.singular (y + y') (Y.add_mem hy hy')
    rw [hB, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h1, S.singular y hy,
      S.singular y' hy']
    simp
  have hsplit : Y ⊓ fixedSpace a ≠ ⊥ ∨ Y ⊓ othersSpace a.toLinearMap (X - 1) ≠ ⊥ :=
    inter_ne_bot_or S.ne_bot fun y hy => by
      have := exists_split_orbit hx (h := X - 1) (Y := Y) (fun y hy => S.inv a haA y hy) hy
      rwa [hW] at this
  have ha1 : a ≠ 1 := hE.a_ne
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  have hker : Nat.card (resHom A (fixedSpace a) hUinv).ker ≤ p ^ 1 := by
    have hsub : ∀ g : A, g ∈ (resHom A (fixedSpace a) hUinv).ker →
        (g : V ≃ₗ[K] V) ∈ Subgroup.zpowers a := by
      intro g hg
      refine hE.A_cent g g.2 fun d hd => ?_
      refine commute_of_fix_orbit hx hmem (hcomm g g.2) ?_ (commutator_self_le _ (hX hd))
      rw [hW]
      intro u hu
      exact congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨u, hu⟩)
    have hinj : Function.Injective fun g : (resHom A (fixedSpace a) hUinv).ker =>
        (⟨((g.1 : A) : V ≃ₗ[K] V), hsub g.1 g.2⟩ : Subgroup.zpowers a) := by
      intro g g' h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h1)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, hord] at this
    simpa using this
  have hRb : Nat.card (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv).range ≤ p ^ 1 :=
    card_res_comp_le S.prime hpK S.root hIso hc hUinv hRinv horth S.inv hYiso hsplit
      S.finrank_eq S.card_eq hker

  have hU1 := Subgroup.card_ker_mul_card_range (resHom A (fixedSpace a) hUinv)
  have hp1 : 1 < p := S.prime.one_lt
  have hn2 : n - 1 = (n - 2) + 1 := by omega
  have hAU : p ^ (n - 2) ≤ Nat.card (resHom A (fixedSpace a) hUinv).range := by
    have h1 : p ^ (n - 1) ≤ p * Nat.card (resHom A (fixedSpace a) hUinv).range := by
      rw [← S.card_eq, ← hU1]
      exact Nat.mul_le_mul_right _ (by simpa using hker)
    rw [hn2, pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 S.prime.pos
  have hUdim : n - 2 ≤ finrank K (fixedSpace a) / 2 := by
    have h1 := card_res_le S.prime hpK hIso hc hUinv horth
    exact (Nat.pow_le_pow_iff_right hp1).mp (hAU.trans h1)
  have h6 : 6 ≤ finrank K (fixedSpace a) := by omega
  obtain ⟨hq, -, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace a).subtype)
    hx.polarBilin_fixed_nondegenerate h6
  set F := supportedFixedDerived Q a with hF
  have hFΩ : F ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  have hFq : CFSG.IsQuasisimple F :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hq
  have hDF : D ≤ F := by
    rw [hF, hx.supportedFixedDerived_eq]
    exact hX
  have hFn : ∀ b ∈ F, ∀ d ∈ D, b * d * b⁻¹ ∈ D := fun b hb d hd =>
    hE.D_norm b (hFΩ hb) (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (supportedFixedDerived_le_isometryCentralizer hb)).2) d hd
  have hDeq : D = F := StdSubRestThree.eq_of_le_of_quasisimple hDF hFn hFq hE.D_qs
  set KR := (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv).ker with hKR
  have hEA : KR.map A.subtype ≤ A := Subgroup.map_subtype_le _
  have key : ∀ g : A, g ∈ KR → (g : V ≃ₗ[K] V) ∈ F := by
    intro g hg
    have hgR : ∀ r ∈ othersSpace a.toLinearMap (X - 1), (g : V ≃ₗ[K] V) r = r := fun r hr =>
      congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨r, hr⟩)
    have hgM : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q a := mem_isometryCentralizer.mpr
      ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (S.le_omega g.2)) v, fun v =>
        congrArg (fun f : V ≃ₗ[K] V => f v)
          (Subgroup.mem_centralizer_singleton_iff.mp (hcomm g g.2))⟩
    have hgB : (g : V ≃ₗ[K] V) ∈ supportedBlock Q a (X - 1) := mem_supportedBlock.mpr ⟨hgM, hgR⟩
    refine mem_supportedFixedDerived.mpr ⟨hgB, ?_⟩
    have hrO := restrictFixed_mem_orthogonalGroup (Q := Q) ⟨_, hgB⟩
    refine hodd _ hrO p (S.prime.odd_of_ne_two S.odd) ?_
    rw [← map_pow]
    have : (⟨(g : V ≃ₗ[K] V), hgB⟩ : ↥(supportedBlock Q a (X - 1))) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact S.elem.2 _ g.2)
    rw [this, map_one]
  have hEF : KR.map A.subtype ≤ F := by
    rintro _ ⟨g, hg, rfl⟩
    exact key g hg
  have hEcard : p ^ 3 ≤ Nat.card (KR.map A.subtype) := by
    have hmapcard : Nat.card (KR.map A.subtype) = Nat.card KR :=
      (Nat.card_congr (KR.equivMapOfInjective A.subtype A.subtype_injective).toEquiv).symm
    have hR1 := Subgroup.card_ker_mul_card_range
      (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv)
    rw [hmapcard]
    have h1 : p ^ (n - 1) ≤ Nat.card KR * p := by
      rw [← S.card_eq, ← hR1]
      exact Nat.mul_le_mul_left _ (by simpa using hRb)
    rw [hn2, pow_succ] at h1
    have h2 : p ^ (n - 2) ≤ Nat.card KR := Nat.le_of_mul_le_mul_right h1 S.prime.pos
    exact (Nat.pow_le_pow_right S.prime.pos (by omega)).trans h2
  exact ⟨KR.map A.subtype, isElemAbelian_of_le hE.A_elem hEA, hDeq ▸ hEF, hEA, hEcard⟩

end Fixed

end SmallOrthUn

end CFSG.StandardType

end
