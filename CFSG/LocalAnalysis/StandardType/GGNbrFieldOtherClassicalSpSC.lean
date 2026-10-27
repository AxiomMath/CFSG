module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

open CFSG.Assembly

namespace SpNS

section HypPair

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V} {L : Type} [Field L] [Algebra K L]

theorem exists_isom_hypPair (hAlt : B.IsAlt) (b₀ : Module.Basis (Fin 2) K L) {p : ℕ} {ζ : L}
    (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hζω : ∀ ω : LinearMap.BilinForm K L, ω.IsAlt → ∀ x y, ω (ζ * x) (ζ * y) = ω x y)
    {a b : V} (hab : B a b = 1) :
    ∃ h : Module.End K V, (∀ u v, B (h u) (h v) = B u v) ∧ h ^ p = 1 ∧ h a ≠ a ∧
      ∀ x : Module.End K V, (∀ u v, B (x u) (x v) = B u v) → x a = a → x b = b →
        h * x = x * h := by
  set Ψ : L →ₗ[K] V := (b₀.coord 0).smulRight a + (b₀.coord 1).smulRight b
  set μ : V →ₗ[K] L :=
    (LinearMap.flip B b).smulRight (b₀ 0) - (LinearMap.flip B a).smulRight (b₀ 1)
  have hΨ : ∀ x, Ψ x = b₀.repr x 0 • a + b₀.repr x 1 • b := fun x => rfl
  have hμ : ∀ v, μ v = B v b • b₀ 0 - B v a • b₀ 1 := fun v => rfl
  have haa : B a a = 0 := hAlt.self_eq_zero a
  have hbb : B b b = 0 := hAlt.self_eq_zero b
  have hba : B b a = -1 := by rw [← hAlt.neg_eq, hab]
  have hμr0 : ∀ v, b₀.repr (μ v) 0 = B v b := fun v => by
    rw [hμ]
    simp [Finsupp.single_apply]
  have hμr1 : ∀ v, b₀.repr (μ v) 1 = -B v a := fun v => by
    rw [hμ]
    simp [Finsupp.single_apply]
  have hBΨb : ∀ x, B (Ψ x) b = b₀.repr x 0 := fun x => by
    rw [hΨ]
    simp [hab, hbb]
  have hBΨa : ∀ x, B (Ψ x) a = -b₀.repr x 1 := fun x => by
    rw [hΨ]
    simp [haa, hba]
  have hμΨ : ∀ x, μ (Ψ x) = x := fun x => by
    rw [hμ, hBΨb, hBΨa, neg_smul, sub_neg_eq_add]
    conv_rhs => rw [← b₀.sum_repr x]
    rw [Fin.sum_univ_two]
  set ω : LinearMap.BilinForm K L := B.comp Ψ Ψ
  have hω : ∀ x y, ω x y = B (Ψ x) (Ψ y) := fun x y => LinearMap.BilinForm.comp_apply B Ψ Ψ x y
  have hωalt : ω.IsAlt := fun x => by rw [hω]; exact hAlt _
  have hleft : ∀ u y, B u (Ψ y) = ω (μ u) y := fun u y => by
    rw [hω, hΨ y, hΨ (μ u), hμr0, hμr1]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hab,
      hba, haa, hbb]
    ring
  have hright : ∀ x v, B (Ψ x) v = ω x (μ v) := fun x v => by
    rw [← hAlt.neg_eq v (Ψ x), hleft, hωalt.neg_eq]
  set h : Module.End K V := LinearMap.id + Ψ ∘ₗ LinearMap.mulLeft K (ζ - 1) ∘ₗ μ
  have hh : ∀ v, h v = v + Ψ ((ζ - 1) * μ v) := fun v => rfl
  have hiso : ∀ u v, B (h u) (h v) = B u v := by
    intro u v
    rw [hh, hh, LinearMap.map_add₂, map_add, map_add, ← hω, hleft, hright]
    have e := hζω ω hωalt (μ u) (μ v)
    simp only [sub_mul, one_mul, map_sub, LinearMap.sub_apply]
    linear_combination e
  have hpow : ∀ (n : ℕ) (v : V), (h ^ n) v = v + Ψ ((ζ ^ n - 1) * μ v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, hh, map_add μ, hμΨ, add_assoc, ← map_add]
      congr 2
      ring
  have hhp : h ^ p = 1 := LinearMap.ext fun v => by
    rw [hpow, hζp, sub_self, zero_mul, map_zero, add_zero, Module.End.one_apply]
  have hμa : μ a = b₀ 0 := by rw [hμ, hab, haa, one_smul, zero_smul, sub_zero]
  have hha : h a ≠ a := by
    intro h0
    rw [hh, hμa, add_eq_left] at h0
    have h1 := congrArg μ h0
    rw [hμΨ, map_zero μ] at h1
    exact mul_ne_zero (sub_ne_zero.mpr hζ1) (b₀.ne_zero 0) h1
  refine ⟨h, hiso, hhp, hha, fun x hx hxa hxb => LinearMap.ext fun v => ?_⟩
  have hxΨ : ∀ y, x (Ψ y) = Ψ y := fun y => by
    rw [hΨ, map_add, map_smul, map_smul, hxa, hxb]
  have hxμ : μ (x v) = μ v := by
    have e1 : B (x v) b = B v b := by rw [← hx v b, hxb]
    have e2 : B (x v) a = B v a := by rw [← hx v a, hxa]
    rw [hμ, hμ, e1, e2]
  rw [Module.End.mul_apply, Module.End.mul_apply, hh, hh, map_add, hxΨ, hxμ]

end HypPair

section SelfCent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem pow_finrank_div_two_le_card_of_selfCent (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {B : LinearMap.BilinForm K V} (hAlt : B.IsAlt) (hnd : B.Nondegenerate)
    (E : Subgroup ↥(sesqUnitaryGroup B)) (hE : IsElemAbelian p E)
    (hsc : ∀ g : ↥(sesqUnitaryGroup B), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    p ^ (Module.finrank K V / 2) ≤ Nat.card E := by
  classical
  have hp2 : p ≠ 2 := ne_two_of_dvd_card_add_one hpq
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : K) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hζo := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  set S : Set (Module.End K V) :=
    {x | ∃ e ∈ E, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) = x}
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have h1 := TableB.IsElemAbelian.comm hE he he'
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    exact h2
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have h1 := hE.2 e he
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      ((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) h1
    simpa using h2
  have hSB : ∀ x ∈ S, ∀ u w, B (x u) (x w) = B u w := by
    rintro _ ⟨e, -, rfl⟩ u w
    exact mem_sesqUnitaryGroup.mp e.2 u w
  obtain ⟨s, κ, _, Φ, β, hβ, hact, hdec⟩ := exists_nframe hp hp2 hpK hgd
    (rootPB_dim_eq_two hp hp2 hpK hgd hpq) (aeval_root_pow_pred hp hpK hgd hpq) hAlt hnd S hSc hSp
    hSB
  set b : Basis (Fin 2) K (AdjoinRoot g) :=
    (CoordSL.rootPB g).basis.reindex (finCongr (rootPB_dim_eq_two hp hp2 hpK hgd hpq))
  have hζω : ∀ ω : LinearMap.BilinForm K (AdjoinRoot g), ω.IsAlt → ∀ u v,
      ω (ζ * u) (ζ * v) = ω u v := fun ω hω u v => by
    have h1 := bilin_apply_det b hω (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := hζω β hβ
  set τ := torHom (K := K) hζp hdec hζβ
  have hτinj : Function.Injective τ := torHom_injective hζp hdec hζβ hζo
  have hτapp : ∀ f x, (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (torEquiv hζp f x) := fun f x => frameUnit_apply Φ _ x
  have hEτ : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨k, hk⟩ := hact _ ⟨e, he, rfl⟩
    refine ⟨fun i => ofAdd (k i : ZMod p), Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hτapp, torEquiv_apply, hk]
    congr 2
    funext i
    rw [toAdd_ofAdd, ZMod.val_natCast, ← pow_eq_pow_mod _ hζp]
  have hτE : ∀ f, τ f ∈ E := by
    intro f
    refine hsc _ (fun e he => ?_) ?_
    · obtain ⟨f', rfl⟩ := hEτ e he
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [← map_pow]
      convert map_one τ
      funext i
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i ^ p), toAdd_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hEfix : ∀ e ∈ E, ∀ w, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ (0, w)) = Φ (0, w) := by
    intro e he w
    obtain ⟨k, hk⟩ := hact _ ⟨e, he, rfl⟩
    rw [hk]
    congr 2
    funext i
    simp
  have hκ : IsEmpty κ := by
    by_contra hne'
    rw [not_isEmpty_iff] at hne'
    obtain ⟨k₀⟩ := hne'
    set a := Φ (0, Pi.single k₀ 1) with ha
    have ha0 : a ≠ 0 := by
      intro h0
      have h1 : ((0 : Fin s → AdjoinRoot g), (Pi.single k₀ (1 : K) : κ → K)) = 0 :=
        Φ.injective (by rw [← ha, h0, map_zero])
      have h2 := congrArg (fun z : (Fin s → AdjoinRoot g) × (κ → K) => z.2 k₀) h1
      simp at h2
    obtain ⟨w', hw'⟩ : ∃ w', B a (Φ (0, w')) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ha0
      refine hnd.1 a fun y => ?_
      obtain ⟨⟨d', w''⟩, rfl⟩ := Φ.surjective y
      rw [ha, hdec]
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero, zero_add]
      exact hcon w''
    set b' := (B a (Φ (0, w')))⁻¹ • Φ (0, w') with hb'
    have hab : B a b' = 1 := by rw [hb', map_smul, smul_eq_mul, inv_mul_cancel₀ hw']
    have hEb : ∀ e ∈ E, (((e : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) b' = b' := fun e he => by rw [hb', map_smul, hEfix e he]
    obtain ⟨h, hiso, hhp, hha, hcomm⟩ := exists_isom_hypPair hAlt b hζp hζ1 hζω hab
    set u : LinearMap.GeneralLinearGroup K V := Units.ofPowEqOne h p hhp hp.ne_zero
    have huval : (u : V →ₗ[K] V) = h := Units.val_ofPowEqOne h p hhp hp.ne_zero
    have huU : u ∈ sesqUnitaryGroup B := mem_sesqUnitaryGroup.mpr fun x y => by
      rw [huval]
      exact hiso x y
    have hgE : (⟨u, huU⟩ : ↥(sesqUnitaryGroup B)) ∈ E := by
      refine hsc _ (fun e he => Subtype.ext (Units.ext ?_)) (Subtype.ext ?_)
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
        change (u : V →ₗ[K] V) * _ = _ * (u : V →ₗ[K] V)
        rw [huval]
        exact hcomm _ (mem_sesqUnitaryGroup.mp e.2) (hEfix e he _) (hEb e he)
      · rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact Units.pow_ofPowEqOne hhp hp.ne_zero
    apply hha
    have h1 := hEfix _ hgE (Pi.single k₀ 1)
    change (u : V →ₗ[K] V) a = a at h1
    rwa [huval] at h1
  have hdimL : Module.finrank K (AdjoinRoot g) = 2 := by
    rw [(CoordSL.rootPB g).finrank, rootPB_dim_eq_two hp hp2 hpK hgd hpq]
  have hfr : Module.finrank K V = s * 2 := by
    have h1 := LinearEquiv.finrank_eq Φ
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self, hdimL,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      Fintype.card_eq_zero_iff.mpr hκ] at h1
    omega
  have hbij : Function.Bijective (fun f => (⟨τ f, hτE f⟩ : E)) := by
    refine ⟨fun f f' hff' => hτinj (congrArg Subtype.val hff'), fun e => ?_⟩
    obtain ⟨f, hf⟩ := hEτ e e.2
    exact ⟨f, Subtype.ext hf⟩
  have hcard : Nat.card E = p ^ s := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  rw [hcard, hfr, Nat.mul_div_cancel _ two_pos]

end SelfCent

end SpNS

section Transfer

variable {p k : ℕ}

theorem selfCentPowLe_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : ∀ E : Subgroup R', IsElemAbelian p E →
      (∀ g : R', (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) → p ^ k ≤ Nat.card E)
    (E : Subgroup R) (hE : IsElemAbelian p E)
    (hsc : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) : p ^ k ≤ Nat.card E := by
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  rw [← hcard]
  exact h _ (TableB.isElemAbelian_map hE _) hsc'

theorem ggTorusSCRank_of_selfCent {R : Type} [Group R] {I : Set (MulAut R)} (hp : p.Prime)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R)
    (h : ∀ E : Subgroup R, IsElemAbelian p E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → p ^ k ≤ Nat.card E) :
    GGTorusSCRank p k R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hsc
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
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
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
  rw [← hcardE]
  exact h E hEab hscE

end Transfer

section Labels


theorem ggTorusSCRank_sp {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    GGTorusSCRank p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K m)) :=
    AutPSp.proj_injective (n := m) (K := K)
  set e₁ : ↥(LargeEvenSpGroup K m) ≃* LargeEvenProj (LargeEvenSpGroup K m) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K m))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  set e₂ : ↥(CFSG.Open.StatedSp m K) ≃*
      ↥(sesqUnitaryGroup (CFSG.RankThree.Classical.spForm m K)) :=
    (MonoidHom.ofInjective CFSG.RankThree.Classical.spLin_injective).trans
      (MulEquiv.subgroupCongr CFSG.RankThree.Classical.range_spLin)
  have hLS : LargeEvenSpGroup K m = CFSG.Open.StatedSp m K := rfl
  have hfr : Module.finrank K (Fin m ⊕ Fin m → K) / 2 = m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ggTorusSCRank_of_selfCent hp TableBSymp.sp_I_subset_inn TableBSymp.center_spProj_eq_bot
    (ggCenterPrime_sp hp hp2)
    (selfCentPowLe_of_mulEquiv (e₁.symm.trans ((MulEquiv.subgroupCongr hLS).trans e₂))
      fun E hE hsc => ?_)
  have h := SpNS.pow_finrank_div_two_le_card_of_selfCent hp hpq
    CFSG.RankThree.Classical.spForm_isAlt CFSG.RankThree.Classical.spForm_nondegenerate E hE hsc
  rwa [hfr] at h

theorem recipeSymplectic_torusSCRank {l n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ GGTorusSCRank p l R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusSCRank_sp hl hp hpK⟩

theorem largeEvenLabelAll_torusSCRank_spNonsplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusSCRank p lab.rank R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_torusSCRank hp hpn (one_le_two.trans hlab.2.1) hQ

end Labels

end CFSG.StandardType

end
