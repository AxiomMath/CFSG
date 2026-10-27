module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreTwo
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard

public section

namespace CFSG.StandardType

section Def

open CFSG CFSG.Assembly SpCoord Multiplicative

@[expose] def GGTorusSignedSCSp4 (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 2 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i : Fin k, ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
      ∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)

theorem ggTorusSignedSCSp4_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusSignedSCSp4 p R') : GGTorusSignedSCSp4 p R := by
  intro E hE h2 hsc
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
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm⟩ :=
    h (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _) (hcard ▸ h2) hsc'
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' h
    rw [← map_inv, ← map_mul, ← map_mul, h]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, fun i => ?_,
    fun σ => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨w, hw⟩ := hsgn i
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩

end Def

namespace SpNS

section IsomSp4

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem torusSignedSCSp4_isom (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    (hAlt : B.IsAlt) (hnd : B.Nondegenerate) : GGTorusSignedSCSp4 p ↥(sesqUnitaryGroup B) := by
  classical
  intro E hE _ hsc
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
  have hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v := fun u v => by
    have h1 := bilin_apply_det b hβ (Algebra.lmul K (AdjoinRoot g) ζ) u v
    rw [← Algebra.norm_apply, norm_root_eq_one hp hp2 hpK hgd hpq, one_mul] at h1
    exact h1
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
  refine ⟨s, τ.comp (MonoidHom.id _), hτinj, ?_, fun i => ?_, fun σ => ?_⟩
  · ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE f
    · intro he
      obtain ⟨f, hf⟩ := hEτ e he
      exact ⟨f, hf⟩
  ·
    have : Fintype K := Fintype.ofFinite K
    have hσβ : ∀ u v, β (frobL K g u) (frobL K g v) = β u v := fun u v => by
      have h1 := bilin_apply_det b hβ (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) u v
      rw [det_frobL hp hp2 hpK hgd hpq, one_mul] at h1
      exact h1
    exact torHom_sgn hζp hdec hζβ (frobL_root_mul hp hpK hgd hpq) hσβ i
  · exact torHom_perm hζp hdec hζβ σ

end IsomSp4

end SpNS

section Recipe

open CFSG.Assembly SpCoord Multiplicative CFSG.LocalAnalysis.ComponentInitial

theorem ggTorusSignedSCSp4_spNonsplit {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ}
    [NeZero m] (hp : p.Prime) (hpq : p ∣ Nat.card K + 1) :
    GGTorusSignedSCSp4 p (LargeEvenProj (LargeEvenSpGroup K m)) := by
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
  exact ggTorusSignedSCSp4_of_mulEquiv (e₁.symm.trans ((MulEquiv.subgroupCongr hLS).trans e₂))
    (SpNS.torusSignedSCSp4_isom hp hpq CFSG.RankThree.Classical.spForm_isAlt
      CFSG.RankThree.Classical.spForm_nondegenerate)

theorem ggTorusSignedSCSp4_spSplit {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGTorusSignedSCSp4 p (LargeEvenProj (LargeEvenSpGroup K 2)) := by
  classical
  intro E hE hr _
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨x, hτE, hEτ⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hE hr
  set τ : (Fin 2 → Multiplicative (ZMod p)) →* LargeEvenProj (LargeEvenSpGroup K 2) :=
    (MulAut.conj x).toMonoidHom.comp (TableBSymp.spTorus hζ)
  have hτapp : ∀ f, τ f = x * TableBSymp.spTorus hζ f * x⁻¹ := fun f => rfl
  have hconjτ : ∀ (s : LargeEvenProj (LargeEvenSpGroup K 2))
      (α : (Fin 2 → Multiplicative (ZMod p)) → (Fin 2 → Multiplicative (ZMod p))),
      (∀ f, s * TableBSymp.spTorus hζ f * s⁻¹ = TableBSymp.spTorus hζ (α f)) →
      ∀ f, (x * s * x⁻¹) * τ f * (x * s * x⁻¹)⁻¹ = τ (α f) := by
    intro s α hs f
    rw [hτapp, hτapp, ← hs f]
    group
  refine ⟨2, τ, (MulAut.conj x).injective.comp
      (TableBSymp.spTorus_injective hζ hζo (hp.odd_of_ne_two hp2)), ?_,
    fun i => ⟨_, hconjτ _ (sgnAut i) fun f => TableBSymp.spSwap_conj_spTorus hζ i f⟩,
    fun σ => ⟨_, hconjτ _ (permAut σ) (SpModel.projMk_spPermSp_conj_spTorus hζ σ)⟩⟩
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    exact hτE f
  · intro he
    obtain ⟨f, hf⟩ := hEτ e he
    exact ⟨f, hf⟩

end Recipe

section Model

open CFSG.Assembly SpCoord Multiplicative

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_signedModelSCSp4 (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedSCSp4 p R) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h2 : p ^ 2 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 2 ≤ k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i : Fin k, ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i)) ∧
      ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAut σ) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
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
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm⟩ := h E hEab (hcardE ▸ h2) hscE
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : (Fin k → Multiplicative (ZMod p)) →* ↥A := (Λ.comp τ).codRestrict A hτmem
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  have hk : 2 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A :=
      Nat.card_congr Θ.toEquiv
    rw [hcV] at h1
    rw [← h1] at h2
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hlift : ∀ (w : R) (α : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, w * τ f * w⁻¹ = τ (α f)) → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α := by
    intro w α hw
    obtain ⟨n, rfl⟩ := hψ w
    have hconjΘ : ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
        ((Θ (α f) : ↥A) : MulAut L') := by
      intro f
      rw [hΘval, hΘval, ← hΛn n, ← map_inv, ← map_mul, ← map_mul, hw f]
    have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have h1 := hconjΘ (α⁻¹ f)
      rw [MulAut.apply_inv_self, hf] at h1
      have h2 : a = MulAut.conj n * ((Θ (α⁻¹ f) : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ := h1.symm
      have e : (MulAut.conj n)⁻¹ * a * MulAut.conj n = ((Θ (α⁻¹ f) : ↥A) : MulAut L') := by
        rw [h2]
        group
      rw [e]
      exact (Θ _).2
    refine ⟨n, hn, MulEquiv.ext fun a => Subtype.ext ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [ggConjAut_apply, hconjΘ, MulAut.congr_apply]
    simp
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (hp.odd_of_ne_two hp2) τ
    fun i j => by
      obtain ⟨w, hw⟩ := hsgn i
      refine ⟨w, ?_, fun hji => ?_⟩
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_self, map_inv]
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_of_ne hji]
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ n * τ f * (ψ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ n * τ f * (ψ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ n * τ f * (ψ n)⁻¹ ∈ τ.range := hτE ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨k, Θ, hk, fun n hn => ?_, fun i => ?_, fun σ' => ?_⟩
  ·
    have hform : ∀ f, ∃ g, ∃ z ∈ ψ.ker, z ^ p = 1 ∧
        n * (MulAut.conj (σ f) n)⁻¹ = σ g * z := by
      intro f
      obtain ⟨f', hf'⟩ := hNE n hn f
      set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
      have hzk : z ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hψσ, hψσ, hf',
          inv_mul_cancel]
      have hzc := Subgroup.mem_center_iff.mp (hker hzk)
      have hzp : z ^ p = 1 := by
        have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
          rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
        have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
        rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
          ReflInner.pow_eq_one_of_zmod, map_one, one_mul] at h1
        exact h1
      refine ⟨f' * f⁻¹, z, hzk, hzp, ?_⟩
      rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
      group
    intro a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have haσ : a = MulAut.conj (σ f) := by
      rw [← hΘσ, hf]
    obtain ⟨g, z, hzk, hzp, he⟩ := hform f
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    rw [haσ, he]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [(show Commute (σ g) z from hzc (σ g)).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul, hzp]
    · obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
      have ha'σ : a' = MulAut.conj (σ f'') := by
        rw [← hΘσ, hf'']
      rw [ha'σ, MulAut.conj_apply]
      calc σ f'' * (σ g * z) * (σ f'')⁻¹ = σ g * (σ f'' * z) * (σ f'')⁻¹ := by
            rw [← mul_assoc, hσc]; group
        _ = σ g * (z * σ f'') * (σ f'')⁻¹ := by rw [hzc]
        _ = σ g * z := by group
  · obtain ⟨w, hw⟩ := hsgn i
    exact hlift w _ hw
  · obtain ⟨w, hw⟩ := hperm σ'
    exact hlift w _ hw

theorem exists_move_signedSp4 (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : 2 ≤ k)
    {f : Fin k → Multiplicative (ZMod p)} (hf : f ≠ 1) :
    ∃ α : MulAut (Fin k → Multiplicative (ZMod p)),
      ((∃ i, α = sgnAut i) ∨ ∃ σ : Equiv.Perm (Fin k), α = permAut σ) ∧
        ∀ z : ℤ, f ^ z ≠ α f := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
  rw [Pi.one_apply] at hi
  by_cases hj : ∃ j, j ≠ i ∧ f j ≠ 1
  · obtain ⟨j, hji, hfj⟩ := hj
    refine ⟨sgnAut i, Or.inl ⟨i, rfl⟩, fun z hz => ?_⟩
    have hzj := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g j)) hz
    have hzi := congrArg (fun g : Fin k → Multiplicative (ZMod p) => toAdd (g i)) hz
    simp only [sgnAut_apply, Function.update_self, Function.update_of_ne hji, Pi.pow_apply,
      toAdd_zpow, toAdd_inv, zsmul_eq_mul] at hzj hzi
    have hxj : toAdd (f j) ≠ 0 := fun h0 => hfj (toAdd_eq_zero.mp h0)
    have hxi : toAdd (f i) ≠ 0 := fun h0 => hi (toAdd_eq_zero.mp h0)
    have h1 : (z : ZMod p) = 1 := mul_right_cancel₀ hxj (by rw [hzj, one_mul])
    have h2 : (z : ZMod p) = -1 := mul_right_cancel₀ hxi (by rw [hzi, neg_one_mul])
    exact one_ne_zero (coord_eq_zero_of_eq_neg hp hp2 (h1.symm.trans h2))
  · push Not at hj
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    obtain ⟨j, hji⟩ := exists_ne i
    refine ⟨permAut (Equiv.swap i j), Or.inr ⟨_, rfl⟩, fun z hz => ?_⟩
    have hzj := congrFun hz j
    rw [Pi.pow_apply, hj j hji, one_zpow, permAut_apply, Function.comp_apply, Equiv.swap_inv,
      Equiv.swap_apply_right] at hzj
    exact hi hzj.symm

theorem ggTorusNoLineTwo_of_signedSCSp4 (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedSCSp4 p R) : GGTorusNoLineTwo p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h2 hsc
  obtain ⟨k, Θ, hk, hW, hS, hP⟩ :=
    exists_signedModelSCSp4 hp hp2 hI hZ hcp h hψ hker hperf hA hAI h2 hsc
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, fun n hn => hW n hn,
    fun _ a₀ ha₀ hne => ?_⟩
  obtain ⟨f, hf⟩ := Θ.surjective ⟨a₀, ha₀⟩
  have ha : ((Θ f : ↥A) : MulAut L') = a₀ := congrArg Subtype.val hf
  have hf1 : f ≠ 1 := by
    rintro rfl
    rw [map_one] at ha
    exact hne ha.symm
  obtain ⟨α, hα, hmove⟩ := exists_move_signedSp4 hp hp2 hk hf1
  obtain ⟨n, hn, hnα⟩ : ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ α := by
    rcases hα with ⟨i, rfl⟩ | ⟨σ, rfl⟩
    · exact hS i
    · exact hP σ
  refine ⟨n, hn, fun hmem => ?_⟩
  rw [← ha, coe_conj_of_ggConjAut_eq Θ hnα] at hmem
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine hmove z (Θ.injective (Subtype.ext ?_))
  rw [map_zpow, SubgroupClass.coe_zpow]
  exact hz

end Model

section Card

open CFSG.Assembly CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

private theorem two_dvd_card_spProj_sp4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) : 2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K n)) := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr (TableBSymp.spProjEquivSp.trans spEquiv).toEquiv]
  have hB : (spForm n K).IsAlt := spForm_isAlt
  obtain ⟨v, hv⟩ : ∃ v : Fin n ⊕ Fin n → K, v ≠ 0 :=
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, fun h => one_ne_zero (Pi.single_eq_zero_iff.mp h)⟩
  obtain ⟨w, hw⟩ : ∃ w, spForm n K v w ≠ 0 := by
    by_contra h
    exact hv (spForm_nondegenerate.1 v fun w => not_not.mp fun hw => h ⟨w, hw⟩)
  have h1 : Tsp hB v 1 ≠ 1 := by
    intro h
    have h' := congrArg (fun g : Gsp (spForm n K) => g.app w) h
    simp only [Tsp_app, one_mul, Gsp.app_one, add_eq_left, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hw (by rw [← hB.neg_eq w v, h', neg_zero])
    · exact hv h'
  have h2 : Tsp hB v 1 ^ 2 = 1 := by rw [pow_two, Tsp_mul_self]
  exact orderOf_eq_prime h2 h1 ▸ orderOf_dvd_natCard _

end Card

section Labels

open CFSG.Assembly

theorem recipeSymplectic_rowPlainTwo_sp4
    {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic 2 (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic 2 (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGNbrWeylRowPlainTwo p 0 R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hS : GGTorusSignedSCSp4 p (LargeEvenProj (LargeEvenSpGroup K 2)) := by
    rcases hpn with hpn | hpn
    · exact ggTorusSignedSCSp4_spNonsplit hp (by rw [hK]; exact hpn)
    · exact ggTorusSignedSCSp4_spSplit hp hp2 (by rw [hK]; exact hpn)
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun g => RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨g, rfl⟩,
    TypeA.ggTorusLift_zero (two_dvd_card_spProj_sp4 (K := K) (n := 2) (by norm_num)),
    fun _ _ => ggTorusNoLineTwo_of_signedSCSp4 hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot (ggCenterPrime_sp hp hp2) hS⟩

theorem largeEvenLabelAll_rowPlainTwo_sp4
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn
  subst hl
  intro Q hQ
  rcases htag with rfl | rfl <;> exact recipeSymplectic_rowPlainTwo_sp4 hp hp2 hpn hQ

end Labels

end CFSG.StandardType

end
