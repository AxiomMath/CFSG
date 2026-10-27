module

public import CFSG.LocalAnalysis.StandardType.GGLangTorusInnerDiagE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGE0E6InnNormal
public import CFSG.LocalAnalysis.StandardType.GGE0TwE6InnNormal
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToralAux2
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepTwo
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.LieType.Chevalley.SingleEdgePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public section

namespace CFSG.StandardType.Q1CenterE6Model

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
open CFSG.StandardType.TableBExc.E6Three

section Certificates


theorem centerPrime_actor_supplier
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (S : LangSetup .E6 L p₀) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : (S.D.Φ = Units.map (entrywiseHom Fr) ∧ ¬ (p = 3 ∧ 3 ∣ S.D.q - 1)) ∨
      (S.D.Φ = twistHom TwistTag.E6 L Fr ∧ ¬ (p = 3 ∧ 3 ∣ S.D.q + 1)))
    {C : Type} [Group C] {A : Subgroup (MulAut C)}
    (hZ : Subgroup.center C = ⊥)
    (hInn : A ≤ (MulAut.conj : C →* MulAut C).range)
    (hAcomm : ∀ a b : A, a * b = b * a) (hAexp : ∀ a : A, a ^ p = 1)
    (ψ : C →* ModGL .E6 L) (hψinj : Function.Injective ψ)
    (hψran : ψ.range = S.Γ)
    {x : C} (hx : MulAut.conj x ∈ A) (hx1 : x ≠ 1)
    {b : Fin Tag.E6.rank → Lˣ} (hb : rootDiagUnit .E6 b ∈ S.D.torus)
    (hbp : ∀ j, b j ^ p = 1) (hψx : ψ x = rootDiagUnit .E6 b)
    {J : Subgroup C}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup (MulAut.conj x))) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I _ θJ => GGAutsInduceOn A J θJ I) := by
  classical
  have hconjinj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  obtain ⟨ρ, hρinj, hρran, hρint, hρconj⟩ := exists_inner_model_action hZ ψ hψinj hInn
  have hρmodel : ρ.range ≤ S.D.model := by
    rintro _ ⟨a, rfl⟩
    have h : ρ a ∈ ψ.range := hρran (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
    rw [hψran] at h
    exact CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup.Γ_le_model S h
  have hρp : ∀ a : A, (ρ a) ^ p = 1 := by
    intro a
    rw [← map_pow, hAexp a, map_one]
  have hbu : rootDiagUnit .E6 b = ρ ⟨MulAut.conj x, hx⟩ := by
    rw [hρconj x hx, hψx]
  have hxu1 : MulAut.conj x ≠ 1 := by
    intro h
    exact hx1 (hconjinj (h.trans (map_one (MulAut.conj : C →* MulAut C)).symm))
  have hEC : ρ.range ≤ Subgroup.centralizer ({rootDiagUnit .E6 b} : Set (ModGL .E6 L)) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommA : a * ⟨MulAut.conj x, hx⟩ = ⟨MulAut.conj x, hx⟩ * a := hAcomm a _
    have hcommρ : ρ a * ρ ⟨MulAut.conj x, hx⟩ = ρ ⟨MulAut.conj x, hx⟩ * ρ a := by
      simpa only [map_mul] using congrArg ρ hcommA
    rw [hρconj x hx, hψx] at hcommρ
    exact hcommρ
  have hconn : ρ.range ≤ familyGroup (fun _ : Unit => b) := by
    refine langModel_le_familyGroup_E6_centerPrime (L := L) (p₀ := p₀) (p := p)
      hp hp2 S Fr hFr hΦ hb hbp ?_ hEC
    exact hρmodel
  exact Q1TwE6ThreeModel.componentMarking_of_lang_connected S ψ hψinj hψran ρ hρinj
    hρint hp hp2 hρmodel hρp hx hxu1 hbu hb hbp hconn hJ

theorem q1CenterE6Model_split_holds
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsh : ¬ (p = 3 ∧ 3 ∣ Nat.card K - 1))
    {A : Subgroup (MulAut (adjointGroup .E6 K))}
    (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : A ≤ (hatAut .E6 K).range)
    {u : MulAut (adjointGroup .E6 K)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (adjointGroup .E6 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  let n : ℕ := f
  have hqK : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hKf]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hp₀K : ¬ 5 ∣ Nat.card K := by
    rw [hqK]
    intro h
    have h2 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at h2
  have hperf : commutator ↥(adjointGroup .E6 K) = ⊤ :=
    single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl)))
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  have hZ : Subgroup.center (adjointGroup .E6 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hconjinj : Function.Injective
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  have hD : ∀ c : Fin Tag.E6.rank → Kˣ,
      AutSt.e6DiagHom K c = rootDiagAutHom .E6 K c := fun c =>
    (KGE6.rootDiagAutHom_eq_exactNormalAut c).symm
  have hrange : (AutSt.e6DiagHom K).range = (rootDiagAutHom .E6 K).range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, (hD c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, hD c⟩
  have hInn : A ≤ (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)).range := by
    intro a ha
    have hβI : a ∈ (MulAut.conj : adjointGroup .E6 K →*
        MulAut (adjointGroup .E6 K)).range ⊔ (AutSt.e6DiagHom K).range := by
      rw [hrange, ← NoOffE6Three.hatAut_range_eq_sup]
      exact hAI ha
    exact ggE0_e6_mem_inn_of_pow hp hsh hβI (hA.2 a ha)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hInn hu)
  subst u
  have hup : (MulAut.conj x) ^ p = 1 := hA.2 (MulAut.conj x) hu
  have hxp : x ^ p = 1 := by
    apply hconjinj
    rw [map_pow, hup, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    exact hu1 (by rw [h1, map_one])
  obtain ⟨S, b, ι, hSq, ⟨Fr, hFr, hΦ⟩, hb, hbp, hb1, hιinj, hιran, hιx, hιconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime_eq_frobenius (τ := Tag.E6)
      (Or.inr (Or.inr (Or.inl rfl))) hp hpK Nat.prime_five hp₀K (Or.inl le_rfl)
      hmon hperf x hxp hx1
  have hFr' : ∀ c : AlgebraicClosure K, Fr c = c ^ S.D.q := by
    intro c
    rw [hSq]
    exact hFr c
  have hsh' : ¬ (p = 3 ∧ 3 ∣ S.D.q - 1) := by
    rintro ⟨hp3, hdvd⟩
    exact hsh ⟨hp3, by rwa [hSq] at hdvd⟩
  have hAcomm : ∀ a b : A, a * b = b * a := by
    have : IsMulCommutative A := hA.1
    exact fun a b => mul_comm' a b
  have hAexp : ∀ a : A, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    exact hA.2 (a : MulAut (adjointGroup .E6 K)) a.2
  exact centerPrime_actor_supplier hp hp2 S Fr hFr' (Or.inl ⟨hΦ, hsh'⟩)
    hZ hInn hAcomm hAexp ι hιinj hιran hu hx1 hb hbp hιx hJ

theorem q1CenterE6Model_twist_holds
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsh : ¬ (p = 3 ∧ 3 ∣ 2 ^ n + 1))
    {A : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : A ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    {u : MulAut (twistedE6RootGroup K σ)} (hu : u ∈ A) (hu1 : u ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ IJ _ θJ => GGAutsInduceOn A J θJ IJ) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ := by
    change Subgroup.center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥
    exact center_graphFixedRootGroup_eq_bot σ.surjective
  have hconjinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  have hInn : A ≤ twistedE6Inn K σ := by
    intro a ha
    exact ggE0_twE6_mem_inn_of_pow hn hK hσ hp hsh (hAI ha) (hA.2 a ha)
  have hmem : u ∈ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range := hInn hu
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
  subst u
  have hup : (MulAut.conj x) ^ p = 1 := hA.2 (MulAut.conj x) hu
  have hxp : x ^ p = 1 := by
    apply hconjinj
    rw [map_pow, hup, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    exact hu1 (by rw [h1, map_one])
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, b, ι, hSq, ⟨Fr, hFr, hΦ⟩, hb, hbp, hb1, hιinj, hιran, hιx, hιconj⟩ :=
    exists_langSetup_of_inner_twE6_of_prime_eq (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ
      hp hp2 Nat.prime_five (by norm_num) (Or.inl le_rfl) hmon x hxp hx1
  have hFr' : ∀ c : AlgebraicClosure K, Fr c = c ^ S.D.q := by
    intro c
    rw [hSq]
    exact hFr c
  have hsh' : ¬ (p = 3 ∧ 3 ∣ S.D.q + 1) := by
    rintro ⟨hp3, hdvd⟩
    exact hsh ⟨hp3, by rwa [hSq] at hdvd⟩
  have hAcomm : ∀ a b : A, a * b = b * a := by
    have : IsMulCommutative A := hA.1
    exact fun a b => mul_comm' a b
  have hAexp : ∀ a : A, a ^ p = 1 := by
    intro a
    apply Subtype.ext
    exact hA.2 (a : MulAut (twistedE6RootGroup K σ)) a.2
  exact centerPrime_actor_supplier hp hp2 S Fr hFr' (Or.inr ⟨hΦ, hsh'⟩)
    hZ hInn hAcomm hAexp ι hιinj hιran hu hx1 hb hbp hιx hJ

end Certificates

end CFSG.StandardType.Q1CenterE6Model

end
