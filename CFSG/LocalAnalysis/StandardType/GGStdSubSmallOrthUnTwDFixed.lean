module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDPlane
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnBlock

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth
  CFSG.RankThree.PartOne.K159 CFSG.GroupTheory.WeirSylow

section Concl

variable {M : Type} [Group M] [Finite M] {p : ℕ}

theorem innerConcl_of_card (hp : p.Prime) {Ω A D : Subgroup M} {a : M}
    (hE : EndData p Ω A D a) {E : Subgroup M} (hEA : E ≤ A) (hED : E ≤ D)
    (hEc : p < Nat.card E) : InnerConcl A D := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := hE.A_elem.2 a hE.a_mem
  have hord : orderOf a = p := orderOf_eq_prime hap hE.a_ne
  obtain ⟨t, htE, htz⟩ : ∃ t ∈ E, t ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective fun x : E => (⟨x.1, hall x.1 x.2⟩ : Subgroup.zpowers a) :=
      fun x y hxy => Subtype.ext (congrArg (fun z : Subgroup.zpowers a => (z : M)) hxy)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, hord] at this
    omega
  have hj : ∃ j ∈ D, t * j ≠ j * t := by
    by_contra hall
    push Not at hall
    exact htz (hE.A_cent t (hEA htE) fun d hd => hall d hd)
  obtain ⟨j, hjD, htj⟩ := hj
  exact ⟨t, hED htE, hEA htE, j, hjD, htj⟩

end Concl

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

structure FourData (Q : QuadraticForm K V) (p : ℕ) (A : Subgroup (V ≃ₗ[K] V)) : Prop where
  regular : (QuadraticMap.polarBilin Q).Nondegenerate
  prime : p.Prime
  odd : p ≠ 2
  dvd : p ∣ Nat.card K + 1
  finrank_eq : Module.finrank K V = 8
  minus : ¬ IsPlusType Q
  le_omega : A ≤ orthDerived Q
  elem : IsElemAbelian p A
  card_ge : p ^ 3 ≤ Nat.card A

theorem innerConcl_of_fixed_four (S : FourData Q p A) {D : Subgroup (V ≃ₗ[K] V)}
    {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a)
    (hmem : (X - 1 : K[X]) ∈ primaryFactors a.toLinearMap)
    (hX : D ≤ ⁅supportedBlock Q a (X - 1), supportedBlock Q a (X - 1)⁆) : InnerConcl A D := by
  classical
  have : Fact p.Prime := ⟨S.prime⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := finite_linearEquiv
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
  have hp1 : 1 < p := S.prime.one_lt
  have hU1 := Subgroup.card_ker_mul_card_range (resHom A (fixedSpace a) hUinv)
  have hAU : p ^ 2 ≤ Nat.card (resHom A (fixedSpace a) hUinv).range := by
    have h1 : p ^ 3 ≤ p * Nat.card (resHom A (fixedSpace a) hUinv).range := by
      calc p ^ 3 ≤ Nat.card A := S.card_ge
        _ = _ := hU1.symm
        _ ≤ p * Nat.card (resHom A (fixedSpace a) hUinv).range :=
          Nat.mul_le_mul_right _ (by simpa using hker)
    rw [pow_succ'] at h1
    exact Nat.le_of_mul_le_mul_left h1 S.prime.pos
  have hUdim : 2 ≤ finrank K (fixedSpace a) / 2 := by
    have h1 := card_res_le S.prime hpK hIso hc hUinv horth
    exact (Nat.pow_le_pow_iff_right hp1).mp (hAU.trans h1)
  rcases fixed_type hx S.prime S.odd S.dvd S.finrank_eq S.minus ha1 with
    h2 | ⟨h4, hm4⟩ | ⟨h6, hp6⟩
  · omega
  ·
    exfalso
    have hTO : (resHom A (fixedSpace a) hUinv).range ≤
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype) := by
      rintro _ ⟨g, rfl⟩
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun s => ?_
      change Q ((g : V ≃ₗ[K] V) (s : V)) = Q (s : V)
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (S.le_omega g.2)) s
    have hTc : ∀ g ∈ (resHom A (fixedSpace a) hUinv).range,
        ∀ h ∈ (resHom A (fixedSpace a) hUinv).range, g * h = h * g := by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hIso.comm g g.2 h h.2))
    have hTp : ∀ g ∈ (resHom A (fixedSpace a) hUinv).range, g ^ p = 1 := by
      rintro _ ⟨g, rfl⟩
      rw [← map_pow, show g ^ p = 1 from Subtype.ext (hIso.pow g g.2), map_one]
    have hle := card_le_of_four_minus hx.polarBilin_fixed_nondegenerate h4 hm4 S.prime S.odd
      _ hTO hTc hTp
    have hp2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    rw [pow_one] at hp2
    omega
  ·
    have hRdim : finrank K (othersSpace a.toLinearMap (X - 1)) = 2 := by
      have := Submodule.finrank_add_eq_of_isCompl hc
      have h8 := S.finrank_eq
      omega
    have horth' : ∀ r ∈ othersSpace a.toLinearMap (X - 1), ∀ u ∈ fixedSpace a, B r u = 0 :=
      fun r hr u hu => by
        rw [CFSG.RankThree.PartOne.LIT.alt_skew hIso.alt r u, horth u hu r hr, neg_zero]
    have hRb : Nat.card (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv).range ≤ p ^ 1 := by
      have := card_res_le S.prime hpK hIso hc.symm hRinv horth'
      rwa [show finrank K (othersSpace a.toLinearMap (X - 1)) / 2 = 1 by omega] at this
    have h6' : 6 ≤ finrank K (fixedSpace a) := by omega
    obtain ⟨hq, -, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace a).subtype)
      hx.polarBilin_fixed_nondegenerate h6'
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
      have hgB : (g : V ≃ₗ[K] V) ∈ supportedBlock Q a (X - 1) :=
        mem_supportedBlock.mpr ⟨hgM, hgR⟩
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
    have hEcard : p ^ 2 ≤ Nat.card (KR.map A.subtype) := by
      have hmapcard : Nat.card (KR.map A.subtype) = Nat.card KR :=
        (Nat.card_congr (KR.equivMapOfInjective A.subtype A.subtype_injective).toEquiv).symm
      have hR1 := Subgroup.card_ker_mul_card_range
        (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv)
      rw [hmapcard]
      have h1 : p ^ 3 ≤ Nat.card KR * p := by
        calc p ^ 3 ≤ Nat.card A := S.card_ge
          _ = _ := hR1.symm
          _ ≤ Nat.card KR * p := Nat.mul_le_mul_left _ (by simpa using hRb)
      rw [pow_succ] at h1
      exact Nat.le_of_mul_le_mul_right h1 S.prime.pos
    have hp2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    rw [pow_one] at hp2
    exact innerConcl_of_card S.prime hE hEA (hDeq ▸ hEF) (lt_of_lt_of_le hp2 hEcard)

end Fixed

end SmallOrthUn

end CFSG.StandardType

end
