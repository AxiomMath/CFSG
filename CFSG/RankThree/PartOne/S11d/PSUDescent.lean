module

public import CFSG.RankThree.PartOne.S11d.FixedFactsPSU
public import CFSG.RankThree.PartOne.S11d.PSUGood

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)

theorem exists_fieldAut_model_PSU {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hM : LieModel T .PSU n 2 (p * f₀))
    (hrank : LocalRankLeTwo p T) (α : MulAut T) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T)
    (hra : LocalRankAut p T α) (hX : FixModel .PSU n f₀ α) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (p * f₀) K) (φ : T ≃* PSUn h n)
      (σ : K ≃+* K), 3 ≤ n ∧ orderOf σ = p ∧
      (∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) ∧
      MulAut.congr φ α = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ := by
  classical
  have hadm₀ : StatedLieAdmissible .PSU n 2 f₀ := by
    rcases admissible_of_fixModel hX with h | ⟨h, -, -⟩
    · exact h
    · exact absurd h (by decide)
  have hU₀ : ∃ U : Subgroup T, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ x ∈ U, α x = x := by
    rcases hX with h | ⟨h, -⟩
    · exact exists_fixed_two_subgroup (fixRes_ne_bot_of_PSU h)
    · exact absurd h (by decide)
  have hC : StatedClassicalModel T .PSU n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα'ord : orderOf α' = p := orderOf_eq_prime hα'p (fun h1 => hα'inn (h1 ▸ one_mem _))
  have hra' : LocalRankAut p (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) α' :=
    localRankAut_congr e hp hra
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
        have hU'α : ∀ u ∈ U₀.map e.toMonoidHom, α' u ∈ U₀.map e.toMonoidHom := by
          rintro _ ⟨u, hu, rfl⟩
          refine ⟨α u, ?_, ?_⟩
          · rw [hU₀fix u hu]
            exact hu
          · show e (α u) = MulAut.congr e α (e u)
            simp [MulAut.congr_apply]
        rcases psu5_aut_classification hU α' hα'p with ⟨P, c, hc, hP5, hαP⟩ |
            ⟨φ, M, -, -, -, hnD, -⟩
        · rw [hαP] at hα'inn hra' hU'α
          exact psu5_D_case hU hpq hc hP5 hα'inn hU'1 (hU₀2.map _) hU'α hra'
        · exact hnD hαD
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
  set ψ := (primeFormConjHom hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ with hψ
  have hψα : ψ * α' * ψ⁻¹ = primeFormFieldHom hU hC1 σ := by
    rw [hψ, inv_inv]
    exact hMconj
  have hdiag' : ∀ c : Kˣ, hU.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hcN hcn hcp
    by_contra hc1
    have hord : orderOf c = p := orderOf_eq_prime hcp hc1
    have hq1 : c ^ (2 ^ (p * f₀) + 1) = 1 := (pow_succ_eq_one_iff_norm hU c).mpr hcN
    have hg : c ^ Nat.gcd n (2 ^ (p * f₀) + 1) = 1 := pow_gcd_eq_one.mpr ⟨hcn, hq1⟩
    have hdvd : orderOf c ∣ Nat.gcd n (2 ^ (p * f₀) + 1) := orderOf_dvd_of_pow_eq_one hg
    rw [hord] at hdvd
    exact hdiag hdvd
  refine ⟨K, inferInstance, hU, e.trans ψ, σ, hn3, hσord, hdiag', ?_⟩
  have : MulAut.congr (e.trans ψ) α = ψ * α' * ψ⁻¹ := rfl
  rw [this, hψα]

theorem lieGoodComponentFixT_PSU : LieGoodComponentFixT .PSU := by
  intro T _ _ p hp hp5 hrank hrankT n f₀ hf₀ hM α hαp hαinn hra hX x hxp hx1 hαx y hy2 hy1 hxy
  obtain ⟨K, _, h, φ, σ, hn3, hσ, hZp, hφα⟩ :=
    exists_fieldAut_model_PSU hp hp5 hM hrank α hαp hαinn hra hX
  have hfinP : Finite (PSUn h n) := finite_primeFormP
  have hrankP : CFSG.pRank p (PSUn h n) ≤ 1 := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt φ]
    exact hrankT.le
  have hφα' : fieldAut h σ = MulAut.congr φ α := hφα.symm
  have hφx : fieldAut h σ (φ x) = φ x := by
    rw [hφα']
    simp [MulAut.congr_apply, hαx]
  have key := psu_good_conclusion h hn3 hp hp5 hf₀ rfl hσ hZp hrankP (x := φ x) (y := φ y)
    (by rw [← map_pow, hxp, map_one]) (fun e => hx1 (φ.injective (by rw [e, map_one])))
    hφx (by rw [← map_pow, hy2, map_one]) (fun e => hy1 (φ.injective (by rw [e, map_one])))
    (by rw [← map_mul, ← map_mul, hxy])
  rw [hφα'] at key
  exact GoodConclusion.of_mulEquiv φ α x key

end CFSG.RankThree.PartOne

