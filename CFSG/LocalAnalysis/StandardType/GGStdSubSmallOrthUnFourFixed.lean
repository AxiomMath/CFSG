module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFourNorm

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

section FourFixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {a : V ≃ₗ[K] V}

theorem commutator_le_fixedDerived {p : ℕ} (hx : OddOrderIsometry Q p a) :
    ⁅supportedBlock Q a (X - 1), supportedBlock Q a (X - 1)⁆ ≤ supportedFixedDerived Q a := by
  rw [hx.supportedFixedDerived_eq]

theorem false_of_fixed_dim_four (hOm : OmegaFourInput) (hK2 : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 a) {A D : Subgroup (V ≃ₗ[K] V)}
    (hAM : ∀ g ∈ A, g ∈ isometryCentralizer Q a) (hA3 : IsElemAbelian 3 A)
    (hAΩ : A ≤ orthDerived Q) (hUinv : ∀ g ∈ A, ∀ s ∈ fixedSpace a, g s ∈ fixedSpace a)
    (hdim : finrank K (fixedSpace a) = 4)
    (hT9 : Nat.card (resHom A (fixedSpace a) hUinv).range = 9)
    (hDF : D ≤ supportedFixedDerived Q a) (hDq : CFSG.IsQuasisimple D)
    (hDn : ∀ c ∈ orthDerived Q, c * a = a * c → ∀ d ∈ D, c * d * c⁻¹ ∈ D) : False := by
  classical
  set U := fixedSpace a with hU
  set Q₀ : QuadraticForm K U := Q.comp U.subtype with hQ₀
  set T := (resHom A U hUinv).range with hT
  have hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup Q₀ := by
    rintro _ ⟨g, rfl⟩
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    exact (mem_isometryCentralizer.mp (hAM g g.2)).1 (w : V)
  have hTel : IsElemAbelian 3 T := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨g, hg⟩ := x.2
      obtain ⟨h, hh⟩ := y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hg, ← hh, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (TableB.IsElemAbelian.comm hA3 g.2 h.2))
    · obtain ⟨g, rfl⟩ := hx
      rw [← map_pow]
      have : g ^ 3 = 1 := Subtype.ext (hA3.2 _ g.2)
      rw [this, map_one]
  set B0 := supportedBlock Q a (X - 1) with hB0
  have hDB : D ≤ B0 := hDF.trans supportedFixedDerived_le_supportedBlock
  set D₃ : Subgroup ↥B0 := D.subgroupOf B0 with hD₃
  set D' : Subgroup (U ≃ₗ[K] U) := D₃.map (restrictFixed Q a) with hD'
  have hD'Ω : D' ≤ orthDerived Q₀ := by
    rintro _ ⟨g, hg, rfl⟩
    exact (mem_supportedFixedDerived.mp (hDF hg)).2
  have hD'q : CFSG.IsQuasisimple D' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hDB).symm.trans
        (D₃.equivMapOfInjective (restrictFixed Q a) (restrictFixed_injective hx))) hDq
  refine hOm K hK2 U Q₀ hdim hx.polarBilin_fixed_nondegenerate T hTO hTel hT9 D' hD'Ω hD'q ?_ ?_
  · intro c hc d' hd'
    obtain ⟨g, hg⟩ := restrictFixed_surjective hx c (orthDerived_le_orthogonalGroup hc)
    obtain ⟨d, hd, rfl⟩ := hd'
    have hgF : (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q a :=
      mem_supportedFixedDerived.mpr ⟨g.2, by rw [hg]; exact hc⟩
    have hgΩ := hx.supportedFixedDerived_le_orthDerived hgF
    have hgcomm : g.1 * a = a * g.1 := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (supportedFixedDerived_le_isometryCentralizer hgF)).2
    have hn := hDn g.1 hgΩ hgcomm d.1 hd
    refine ⟨g * d * g⁻¹, hn, ?_⟩
    rw [map_mul, map_mul, map_inv, hg]
  · intro t ht d' hd'
    obtain ⟨s, rfl⟩ := ht
    obtain ⟨d, hd, rfl⟩ := hd'
    have hat := hAM s s.2
    have hacent : (s : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp hat).2
    have hW1 : ∀ w ∈ U, (s : V ≃ₗ[K] V) w ∈ U := fun w hw => mem_fixedSpace_of_apply hacent hw
    have hW2 : ∀ w ∈ U, (s : V ≃ₗ[K] V).symm w ∈ U := fun w hw =>
      mem_fixedSpace_of_apply (symm_mem_centralizer a hacent) hw
    have hφ : resHom A U hUinv s = restrictEquiv U (s : V ≃ₗ[K] V) hW1 hW2 := rfl
    have hconj : (s : V ≃ₗ[K] V) * d.1 * (s : V ≃ₗ[K] V)⁻¹ ∈ B0 :=
      conj_mem_supportedBlock hat d.2
    have hrf : restrictFixed Q a ⟨(s : V ≃ₗ[K] V) * d.1 * (s : V ≃ₗ[K] V)⁻¹, hconj⟩ =
        resHom A U hUinv s * restrictFixed Q a d * (resHom A U hUinv s)⁻¹ := by
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      rw [coe_restrictFixed, hφ]
      simp only [LinearEquiv.mul_apply, coe_restrictEquiv, coe_restrictFixed]
      rfl
    have hn := hDn (s : V ≃ₗ[K] V) (hAΩ s.2) (Subgroup.mem_centralizer_singleton_iff.mp hacent)
      d.1 hd
    exact ⟨⟨_, hconj⟩, hn, hrf⟩

theorem normConcl_of_fixed_four {p n : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {Y : Submodule K V}
    (hOm : OmegaFourInput) (hK2 : Nat.card K = 2) (hp3 : p = 3) (hn4 : n = 4)
    (S : OrbitData Q p n A Y) {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V}
    (hE : EndData p (orthDerived Q) A D a)
    (hmem : (X - 1 : K[X]) ∈ primaryFactors a.toLinearMap)
    (hX : D ≤ ⁅supportedBlock Q a (X - 1), supportedBlock Q a (X - 1)⁆) : NormConcl p A D := by
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
  have hAM : ∀ g : A, (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q a := fun g =>
    mem_isometryCentralizer.mpr
      ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (S.le_omega g.2)) v, fun v =>
        congrArg (fun f : V ≃ₗ[K] V => f v)
          (Subgroup.mem_centralizer_singleton_iff.mp (hcomm g g.2))⟩
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  by_cases h6 : 6 ≤ finrank K (fixedSpace a)
  · obtain ⟨hq, -, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace a).subtype)
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
      have hgB : (g : V ≃ₗ[K] V) ∈ supportedBlock Q a (X - 1) :=
        mem_supportedBlock.mpr ⟨hAM g, hgR⟩
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
      have h1 : p ^ (n - 1) ≤ Nat.card KR * p := by
        rw [← S.card_eq, ← hR1]
        exact Nat.mul_le_mul_left _ (by simpa using hRb)
      rw [hn2, pow_succ] at h1
      have h2 : p ^ (n - 2) ≤ Nat.card KR := Nat.le_of_mul_le_mul_right h1 S.prime.pos
      exact (Nat.pow_le_pow_right S.prime.pos (by omega)).trans h2
    have hY0 : Y ⊓ fixedSpace a ≠ ⊥ := by
      intro hbot
      have hRY : Y ⊓ othersSpace a.toLinearMap (X - 1) ≠ ⊥ :=
        hsplit.resolve_left (not_not.mpr hbot)
      have horth' : ∀ r ∈ othersSpace a.toLinearMap (X - 1), ∀ u ∈ fixedSpace a, B r u = 0 :=
        fun r hr u hu => by
          rw [CFSG.RankThree.PartOne.LIT.alt_skew hIso.alt r u, horth u hu r hr, neg_zero]
      have hb := card_res_le_of_inter_ne_bot S.prime hpK S.root hIso hc.symm hRinv horth' hRY
        S.inv hYiso
      rw [show finrank K (othersSpace a.toLinearMap (X - 1)) / 2 - 1 = 0 by
        have := S.finrank_eq
        omega, pow_zero] at hb
      have hsub : Subsingleton (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv).range :=
        Finite.card_le_one_iff_subsingleton.mp hb
      have hgR : ∀ g : A, ∀ r ∈ othersSpace a.toLinearMap (X - 1), (g : V ≃ₗ[K] V) r = r := by
        intro g r hr
        have h1 := Subsingleton.elim (⟨resHom A (othersSpace a.toLinearMap (X - 1)) hRinv g, g,
          rfl⟩ : (resHom A (othersSpace a.toLinearMap (X - 1)) hRinv).range) 1
        exact congrArg Subtype.val (LinearEquiv.congr_fun (congrArg Subtype.val h1) ⟨r, hr⟩)
      apply ha1
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hc v
      rw [map_add, mem_fixedSpace.mp hu, hgR ⟨a, haA⟩ r hr]
      rfl
    obtain ⟨U', hU'F, hU'1, hU'2, hU'A⟩ := exists_twoSubgroup_fixed hx
      (fun g hg => hAM ⟨g, hg⟩) h6 hY0 (fun y hy => S.singular y hy.1) inf_le_right
      (fun g hg y hy => ⟨S.inv g hg y hy.1, hUinv g hg y hy.2⟩)
    have hp2 : p < p ^ 2 := by
      have := S.prime.one_lt
      nlinarith
    exact normConcl_of_card S.prime hE hEA (hDeq ▸ hEF) (lt_of_lt_of_le hp2 hEcard) hU'1
      (le_of_le_of_eq hU'F hDeq.symm) hU'2 hU'A
  ·
    have hU4 : finrank K (fixedSpace a) = 4 := by
      obtain ⟨k, hk⟩ := (hIso.res (fixedSpace a) hUinv
        (sep_res_of_isCompl hIso.sep hc horth)).even_finrank
      omega
    have hT9 : Nat.card (resHom A (fixedSpace a) hUinv).range = 9 := by
      have h1 := card_res_le S.prime hpK hIso hc hUinv horth
      rw [show finrank K (fixedSpace a) / 2 = 2 by omega] at h1
      have h2 : p ^ (n - 2) = p ^ 2 := by rw [show n - 2 = 2 by omega]
      rw [h2] at hAU
      subst hp3
      omega
    subst hp3
    exact (false_of_fixed_dim_four hOm hK2 hx (fun g hg => hAM ⟨g, hg⟩) S.elem S.le_omega hUinv
      hU4 hT9 (hX.trans (commutator_le_fixedDerived hx)) hE.D_qs hE.D_norm).elim

end FourFixed

end SmallOrthUn

end CFSG.StandardType

end
