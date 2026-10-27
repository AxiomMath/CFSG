module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66PSU
public import CFSG.SignalizerFunctorTheorem.NonLocal.UHeisenberg
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralQuotientFixed

public section

namespace CFSG.RankThree.PartOne.FieldFix

open Matrix CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

section Fixed

variable {F : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem fieldFixedPSU_eq_range {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hn : 3 ≤ n) (hdiag : ¬ p ∣ Nat.gcd n (2 ^ F + 1)) :
    fieldFixedPSU h n σ = (subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
      (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n).range := by
  classical
  have hfin := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set Z := normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n with hZ
  have hZc := normOneScalars_le_center h
    (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n
  have hβZ := map_normOneScalars_field h (isPrimeFormGram_one (n := n)) σ
  have hσp : σ ^ p = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have hβp : fieldSUHom h n σ ^ p = 1 := by
    rw [← map_pow, hσp, map_one]
  have hZcard : Nat.card Z = Nat.gcd n (2 ^ F + 1) := card_normOneScalars_one h (by omega)
  have hM : (((fieldSUHom h n σ :
        MulAut (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →*
            gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).eqLocus
              (MonoidHom.id _)).map (QuotientGroup.mk' Z) =
      (subfieldPSU h h₀ hbar n).range := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : glAut σ (g : GL (Fin n) K) = g := congrArg Subtype.val (hg : _ = g)
      obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hg'
      have hg₀S := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ g.2)
      refine ⟨((⟨g₀, hg₀S⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
      rw [subfieldPSU_mk]
      congr 1
      exact Subtype.ext hg₀
    · rintro ⟨y, rfl⟩
      induction y using QuotientGroup.induction_on with
      | H g₀ =>
        refine ⟨subfieldSU h h₀ hbar n g₀, ?_, (subfieldPSU_mk h h₀ hbar n g₀).symm⟩
        refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
        change σ ((((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))
          i j : fixSubfield σ) : K) = (((g₀ : GL (Fin n) (fixSubfield σ)) :
            Matrix (Fin n) (Fin n) (fixSubfield σ)) i j : K)
        exact (((g₀ : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2
  rw [← hM]
  obtain ⟨_, δ, -, -, -, -, -, -, -, hCQ, hMn, ε, -, hεker, -, -, hab, hexp⟩ :=
    CFSG.RankThree.GroupTheory.central_quotient_fixed_group_exact_sequence Z hZc
      (fieldSUHom h n σ) hβZ
  refine le_antisymm (fun q hq => ?_) hCQ
  have hy : ε ⟨q, hq⟩ ^ p = 1 := hexp p hβp _
  have hord1 : orderOf (ε ⟨q, hq⟩) ∣ p := orderOf_dvd_of_pow_eq_one hy
  have hord2 : orderOf (ε ⟨q, hq⟩) ∣ Nat.card Z :=
    (orderOf_dvd_natCard _).trans ((Subgroup.card_quotient_dvd_card _).trans
      (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)))
  have hcop : Nat.Coprime p (Nat.card Z) := by
    rw [hZcard]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hdiag
  have hone : orderOf (ε ⟨q, hq⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  have h1 : ε ⟨q, hq⟩ = 1 := orderOf_eq_one_iff.mp hone
  have : (⟨q, hq⟩ : _) ∈ ε.ker := h1
  rw [hεker] at this
  exact this

end Fixed


theorem psu_subfield_group {F f₀ n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) (hn3 : 3 ≤ n)
    (hff : F / p = f₀) (hf₀ : 1 ≤ f₀) (hq₀ : ¬(n = 3 ∧ 2 ^ f₀ = 2)) :
    Group.IsPerfect ↥(subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n).range ∧
      LieModel (↥(subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
          (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n).range ⧸
        Subgroup.center ↥(subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
          (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n).range) .PSU n 2 f₀ ∧
      NonLocalized (subfieldPSU h (fixSubfield_unitaryFieldData h hp hp2 hσ)
        (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) n).range := by
  classical
  subst hff
  have hfin := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hjinj := subfieldPSU_injective h h₀ hbar n (by omega)
  set N := (subfieldPSU h h₀ hbar n).range with hN
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥N := MonoidHom.ofInjective hjinj
  have hsimple := isSimpleGroup_primeFormP_one h₀ hn3 hq₀
  have hnab : ∃ x y : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)), x * y ≠ y * x := by
    have := not_commute_primeFormP_one h₀ hn3 hq₀
    push Not at this
    exact this
  have hperfX : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_of_simple_nonabelian hnab
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hZ : Subgroup.center (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) = ⊥ := center_eq_bot_of_simple' hnab
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
    (centerQuotientCongr eJ.symm).trans (centerQuotientEquivSelf hZ)
  have hXmodel : LieModel (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) .PSU n 2 (F / p) := by
    refine (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hf₀, hn3, ?_⟩,
      fixSubfield σ, inferInstance, inferInstance, ?_, ?_⟩
    · intro hc
      exact hq₀ ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩
    · rw [h₀.card, ← pow_mul, mul_comm]
    · obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h₀
        (isPrimeFormGram_one (n := n)) hn3 hq₀
      exact ⟨eT.trans (unitaryPSUEquiv h₀ (by omega))⟩
  exact ⟨hNperf, lieModel_of_mulEquiv eN.symm hXmodel,
    SignalizerFunctorTheorem.NonLocal.nonLocalized_unitarySubfield h h₀ hbar hn3 hq₀⟩

theorem fixRes_ne_bot_of_PSU {T : Type} [Group T] {n f₀ : ℕ} {α : MulAut T}
    (h : LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSU n 2 f₀) : fixRes α ≠ ⊥ := by
  intro hbot
  have hC := (lieModel_classical_iff (by decide)).mp h
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hsimple := isSimpleGroup_primeFormP_one hU hn3 hq
  have hx1 : ∀ x : ↥(fixRes α), x = 1 := fun x => by
    exact Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot (x : T) x.2)
  have : Subsingleton ↥(fixRes α) := ⟨fun a b => by rw [hx1 a, hx1 b]⟩
  have : Subsingleton (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) :=
    (QuotientGroup.mk_surjective).subsingleton
  have : Subsingleton (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    e.symm.injective.subsingleton
  exact not_subsingleton _ ‹_›

theorem fixedFacts_PSU {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : LieModel T .PSU n 2 (p * f₀)) (hf₀ : 1 ≤ f₀) (hadm₀ : StatedLieAdmissible .PSU n 2 f₀)
    (hrank : LocalRankLeTwo p T) (α₀ : MulAut T) (hα₀p : α₀ ^ p = 1) (hα₀inn : α₀ ∉ innerAut T)
    (hra₀ : LocalRankAut p T α₀)
    (hU₀ : ∃ U : Subgroup T, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ x ∈ U, α₀ x = x) (α : MulAut T)
    (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) (hra : LocalRankAut p T α)
    (hrel : ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ α * (α₀ ^ s)⁻¹ ∈ innerAut T) : FixedFacts p α := by
  classical
  have hC : StatedClassicalModel T .PSU n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  set α₀' := MulAut.congr e α₀ with hα₀'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα₀'p : α₀' ^ p = 1 := by rw [hα₀', ← map_pow, hα₀p, map_one]
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα₀'inn : α₀' ∉
      innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hα₀inn ((mem_innerAut_congr e α₀).mp hmem)
  have hα'ord : orderOf α' = p := orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ one_mem _))
  have hra' : LocalRankAut p (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) α' :=
    localRankAut_congr e hp hra
  have hra₀' : LocalRankAut p
      (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) α₀' :=
    localRankAut_congr e hp hra₀
  obtain ⟨s, hs, hrelT⟩ := hrel
  have hrel' : α' * (α₀' ^ s)⁻¹ ∈
      innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have := (mem_innerAut_congr e (α * (α₀ ^ s)⁻¹)).mpr hrelT
    rwa [map_mul, map_inv, map_zpow] at this
  have hα₀D : α' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      α₀' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro hD
    have hw := innerAut_le_primeFormD' hU hrel'
    have h1 : α₀' ^ s ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hD) hw
      simpa using this
    exact (Subgroup.zpowers_le.mpr h1) (mem_zpowers_zpow_of_pow_eq_one hp hα₀'p hs)
  have hdiag : ¬ p ∣ Nat.gcd n (2 ^ (p * f₀) + 1) := by
    intro hdvd
    have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ 2 ^ (p * f₀) + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    by_cases hn6 : 6 ≤ n
    · exact psu_torus_rank T n (p * f₀) p hp hp5 hpn hn6 hpq hC hrank
    · have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
      have hn5 : n = 5 := by omega
      have hp5' : p = 5 := by omega
      subst hn5
      subst hp5'
      by_cases hαD : α' ∈ primeFormD hU ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
      · obtain ⟨U₀, hU₀1, hU₀2, hU₀fix⟩ := hU₀
        have hU'1 : U₀.map e.toMonoidHom ≠ ⊥ := fun hbot =>
          hU₀1 ((Subgroup.map_eq_bot_iff_of_injective U₀ e.injective).mp hbot)
        have hU'α : ∀ u ∈ U₀.map e.toMonoidHom, α₀' u ∈ U₀.map e.toMonoidHom := by
          rintro _ ⟨u, hu, rfl⟩
          refine ⟨α₀ u, ?_, ?_⟩
          · rw [hU₀fix u hu]
            exact hu
          · show e (α₀ u) = MulAut.congr e α₀ (e u)
            simp [MulAut.congr_apply]
        rcases psu5_aut_classification hU α₀' hα₀'p with ⟨P, c, hc, hP5, hαP⟩ |
            ⟨φ, M, -, -, -, hnD, -⟩
        · rw [hαP] at hα₀'inn hra₀' hU'α
          exact psu5_D_case hU hpq hc hP5 hα₀'inn hU'1 (hU₀2.map _) hU'α hra₀'
        · exact hnD (hα₀D hαD)
      · exact psu5_F_case hU hpq hα'ord hαD hra'
  have hσ1 : primeFormFieldFactor hU hC1 hn3 hq α' ≠ 1 := by
    intro hσ1
    have hαD : α' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor hU hC1 hn3 hq]
      exact hσ1
    exact hα'inn (mem_innerAut_of_mem_D hU hn3 hq hp hdiag hαD hα'p)
  set σ := primeFormFieldFactor hU hC1 hn3 hq α' with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hα'p, map_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hpf, -, -, -, -, M, hMconj⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hU hn3 hq hp hp2 hp2
      α' hα'ord σ rfl hσord
  obtain ⟨f', hff'⟩ := hpf
  have hf'f₀ : f' = f₀ := Nat.eq_of_mul_eq_mul_left hp.pos hff'.symm
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  set β := primeFormFieldHom hU hC1 σ with hβ
  set ψ := (primeFormConjHom hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ with hψ
  have hψα : ψ * α' * ψ⁻¹ = β := by
    rw [hψ, inv_inv]
    exact hMconj
  have hq₀ : ¬(n = 3 ∧ 2 ^ f₀ = 2) := fun hc => hadm₀.2.2.2 (by rw [hc.1, hc.2])
  set h₀ := fixSubfield_unitaryFieldData hU hp hp2 hσord with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar hU hp hp2 hσord
  have hΓN : fixSub β = (subfieldPSU hU h₀ hbar n).range :=
    fieldFixedPSU_eq_range hU hp hp2 hσord hn3 hdiag
  obtain ⟨hNperf, hX, hNL⟩ := psu_subfield_group hU hp hp2 hσord hn3 hfdiv hf₀ hq₀
  set N := (subfieldPSU hU h₀ hbar n).range with hN
  let φ : T ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := e.trans ψ
  have hφα : MulAut.congr φ α = β := by
    have : MulAut.congr φ α = ψ * α' * ψ⁻¹ := rfl
    rw [this, hψα]
  have hΓN' : fixSub (MulAut.congr φ α) = N := by rw [hφα, hΓN]
  have hNΓ : N ≤ fixSub (MulAut.congr φ α) := hΓN'.ge
  have hnormT : ∀ W : Subgroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      W = N → (N.subgroupOf W).Normal := by
    intro W hW
    subst hW
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolvT : ∀ W : Subgroup (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      W = N → ∀ (hn : (N.subgroupOf W).Normal), Group.IsSolvable (↥W ⧸ N.subgroupOf W) := by
    intro W hW hn
    subst hW
    have : Subsingleton (↥N ⧸ N.subgroupOf N) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (x⁻¹ * y).2
    exact inferInstance
  exact fixedFacts_of_iso φ α hM hf₀ N hNΓ (hnormT _ hΓN') hNperf
    (hsolvT _ hΓN' (hnormT _ hΓN')) hNL (fun x hx _ => hΓN' ▸ hx)
    (Or.inl fun x hx _ => hΓN' ▸ hx) (Or.inl hX)

theorem tagFixedFacts_PSU : TagFixedFacts .PSU := by
  intro T _ _ p hp hp5 hrank n f₀ hf₀ hM α₀ hα₀p hα₀inn hra₀ hX₀ α hαp hαinn hra hrel
  have hadm : StatedLieAdmissible .PSU n 2 f₀ := by
    rcases admissible_of_fixModel hX₀ with h | ⟨h, -, -⟩
    · exact h
    · exact absurd h (by decide)
  have hU₀ : ∃ U : Subgroup T, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ x ∈ U, α₀ x = x := by
    rcases hX₀ with h | ⟨h, -⟩
    · exact exists_fixed_two_subgroup (fixRes_ne_bot_of_PSU h)
    · exact absurd h (by decide)
  exact fixedFacts_PSU hp hp5 hM hf₀ hadm hrank α₀ hα₀p hα₀inn hra₀ hU₀ α hαp hαinn hra hrel

end CFSG.RankThree.PartOne.FieldFix
