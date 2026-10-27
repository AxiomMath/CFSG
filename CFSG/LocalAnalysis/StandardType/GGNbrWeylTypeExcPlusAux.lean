module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusBump
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem

theorem ggWTEx1_weylFrame_of_excPlusModel {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (h : GGExcPlusWeylModel τ p A) :
    GGWeylFrame p A (coxeterMatrix (isFiniteType_cartan τ)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, w, hw, hact, hnorm⟩ := h
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut ↥A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) :=
    fun i a => hact i a (ρ i a) (ggConjAut_apply A (hN i) a)
  have hρsq : ∀ i, ρ i ^ 2 = 1 := fun i => by
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [pow_two, MulAut.mul_apply, hρ, hρ, torusAct_simple_involutive, MulAut.one_apply]
  have hρfix : ∀ i, Nat.card {a : A // ρ i a = a} * p = Nat.card A := fun i => by
    have hcardA : Nat.card A = p ^ τ.rank := by
      rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hcardFix : Nat.card {a : A // ρ i a = a} = Nat.card
        {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Φ.toEquiv.trans Multiplicative.toAdd) ?_)
      intro a
      change ρ i a = a ↔ TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) =
        Multiplicative.toAdd (Φ a)
      rw [← hρ]
      constructor
      · intro hh
        rw [hh]
      · intro hh
        exact Φ.injective (Multiplicative.toAdd.injective hh)
    rw [hcardFix, card_fix_torusAct_simple τ hp2 i, hcardA]
  have hiter : ∀ (n : ℕ) (i j : Fin τ.rank) (a : A),
      Multiplicative.toAdd (Φ (((ρ i * ρ j) ^ n) a)) =
        TableBExc.torusAct τ p ((simple τ i * simple τ j) ^ n)
          (Multiplicative.toAdd (Φ a)) := by
    intro n
    induction n with
    | zero =>
      intro i j a
      simp only [pow_zero, MulAut.one_apply, TableBExc.torusAct_one]
    | succ n ih =>
      intro i j a
      have hL : ((ρ i * ρ j) ^ (n + 1)) a = ((ρ i * ρ j) ^ n) ((ρ i * ρ j) a) := by
        rw [pow_succ, MulAut.mul_apply]
      have h2 : Multiplicative.toAdd (Φ ((ρ i * ρ j) a)) =
          TableBExc.torusAct τ p (simple τ i * simple τ j)
            (Multiplicative.toAdd (Φ a)) := by
        rw [MulAut.mul_apply, hρ, hρ, TableBExc.torusAct_mul]
      rw [hL, ih i j ((ρ i * ρ j) a), h2, ← TableBExc.torusAct_mul, ← pow_succ]
  have hlift : (coxeterMatrix (isFiniteType_cartan τ)).IsLiftable ρ := by
    intro i j
    refine MulEquiv.ext fun a => ?_
    have h := hiter ((coxeterMatrix (isFiniteType_cartan τ)) i j) i j a
    have hs : (simple τ i * simple τ j) ^
        ((coxeterMatrix (isFiniteType_cartan τ)) i j) = 1 :=
      (coxeterSystem τ).simple_mul_simple_pow i j
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [h, hs, TableBExc.torusAct_one, MulAut.one_apply]
  let Ψ : WeylGroup τ →* MulAut ↥A := (coxeterSystem τ).lift ⟨ρ, hlift⟩
  have hΨsimple : ∀ i, Ψ (simple τ i) = ρ i := fun i =>
    CoxeterSystem.lift_apply_simple (coxeterSystem τ) hlift i
  have hΨact : ∀ (u : WeylGroup τ) (a : A),
      Multiplicative.toAdd (Φ (Ψ u a)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ a)) := by
    intro u
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil =>
      intro a
      rw [CoxeterSystem.wordProd_nil, map_one, MulAut.one_apply, TableBExc.torusAct_one]
    | cons i ω ih =>
      intro a
      rw [CoxeterSystem.wordProd_cons, map_mul, TableBExc.torusAct_mul, MulAut.mul_apply,
        hΨsimple, hρ, ih]
  have hΨinj : Function.Injective Ψ := by
    intro u v huv
    have h1 : u * v⁻¹ = 1 := by
      apply NoOffExc.eq_one_of_torusAct hp2
      intro x
      obtain ⟨a, ha⟩ := Φ.surjective (Multiplicative.ofAdd x)
      have hx : Multiplicative.toAdd (Φ a) = x := congrArg Multiplicative.toAdd ha
      have hPsi1 : Ψ (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
      have h := hΨact (u * v⁻¹) a
      rw [hPsi1, MulAut.one_apply, hx] at h
      exact h.symm
    exact mul_inv_eq_one.mp h1
  have hρauto : ∀ i, ρ i ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := fun i =>
    Subgroup.subset_closure ⟨MulAut.conj (w i), ⟨w i, rfl⟩, hN i,
      fun b => ggConjAut_apply A (hN i) b⟩
  have hrange_le : MonoidHom.range Ψ ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    rintro φ ⟨u, rfl⟩
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil => rw [CoxeterSystem.wordProd_nil, map_one]; exact Subgroup.one_mem _
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, map_mul, hΨsimple]
      exact Subgroup.mul_mem _ (hρauto i) ih
  have hgen_sub : ggInduced (MulAut.conj : L' →* MulAut L').range A ⊆ MonoidHom.range Ψ := by
    rintro φ ⟨g, hgH, hgN, hφ⟩
    obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hgH
    obtain ⟨u, hu⟩ := hnorm n hgN
    refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [hΨact u a]
    exact (hu a (φ a) (hφ a)).symm
  have hrange_eq : MonoidHom.range Ψ =
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    le_antisymm hrange_le ((Subgroup.closure_le _).mpr hgen_sub)
  let e : WeylGroup τ ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hΨinj).trans (MulEquiv.subgroupCongr hrange_eq)
  refine ⟨w, hN, hw, fun i => ⟨hρsq i, hρfix i⟩, e, fun i => ?_⟩
  exact hΨsimple i

theorem ggWTEx1_weylTypeW_of_excPlusModel {τ : Tag} {p r : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan τ)))
    (hcard : Nat.card (coxeterMatrix (isFiniteType_cartan τ)).Group ≠ 12)
    (h : GGExcPlusWeylModelSCr τ p r R I) : GGTorusWeylTypeW p r R I :=
  ggWTF4_weylTypeW_of_frame (M := coxeterMatrix (isFiniteType_cartan τ)) hM hcard
    fun L' _ _ ψ A hA =>
      ggWTEx1_weylFrame_of_excPlusModel hp hp2 hA.2.2.2.2.2.2.2 (h L' ψ A hA)

theorem ggWTEx1_weylTypeW_of_selfCent_card {p r s : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R)
    (hbump : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → p ^ s ≤ Nat.card E)
    (h : GGTorusWeylTypeW p s R I) : GGTorusWeylTypeW p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨l, rfl⟩ := hψ x
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  exact h L' ψ A ⟨hψ, hker, hperf, hAe, hAI,
    hcardE ▸ hbump E hEab (by rw [hcardE]; exact hr) hscE, h3, hsc⟩

theorem ggWTEx1_largeEvenLabelAll_weylTypeW_excPlus_of_recipe {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∧ p ∣ 2 ^ lab.n + 1)
    (hE7 : lab.tag = .E7 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusWeylTypeW p 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K))
    (hE8 : lab.tag = .E8 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusWeylTypeW p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K))
    (hF4 : lab.tag = .F4 → ∀ {K : Type} [Field K] [Finite K] [CharP K 2], p ∣ Nat.card K + 1 →
      GGTorusWeylTypeW p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW p (ggNbrExcPlusRank lab.tag) R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hE7 hE8 hF4
  rcases htag with rfl | rfl | rfl
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hE7 rfl hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hE8 rfl hpq⟩
  · intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hF4 rfl hpq⟩

end CFSG.StandardType

end
