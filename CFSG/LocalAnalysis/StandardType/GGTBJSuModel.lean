module

public import CFSG.LocalAnalysis.StandardType.GGTBJSuDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTBRowUFrameAux

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  UCoord UModel
open InndiagSU (frameMk frameMk_surjective projU projU_surjective)
open CFSG.SectionRank.OddCover (diagHom diagHom_injective det_diagHom)

theorem ggTBJ_su_stdModel
    {K : Type} [Field K] [Finite K] {n d p r : ℕ} [NeZero p]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 4 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (h : UnitaryFieldData 2 n K)
    {I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))
    {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) I L' ψ₀ A) :
    ∃ (u : Kˣ) (hu : u ^ p = 1) (huq : u ^ (2 ^ n + 1) = 1) (hord : orderOf u = p)
      (ψP : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (σ : ↥(sumZero d p) →* L') (Θ : ↥(sumZero d p) ≃* ↥A),
      Function.Surjective ψP ∧ ψP.ker ≤ Subgroup.center ↥(unitarySU 2 n K d) ∧
      (∀ f, ψ₀ (σ f) = ψP (ggTBJSuD h hu huq hord f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A m) := by
  classical
  obtain ⟨hψ0, hker0, hperf0, hAe0, hAI0, -, h3_0, hsc0⟩ := hA
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h32
    have h1 : d = 3 := congrArg Prod.fst h32
    omega
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK (by omega) hdq
  have hcpR : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    StdSubRestU.ggCenterPrime_unitary hK hn (by omega) hdq hp hp2 hpd
  have hcpL := hcpR L' ψ₀ hψ0 hker0 hperf0
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ :
      ∃ Λ : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut L',
      (∀ {e : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))} {x : L'},
        ψ₀ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ₀ (Λ e l) = e * ψ₀ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ₀ hψ0 hker0, fun hx => ReflInner.liftConj_eq hψ0 hker0 hx,
      ReflInner.liftConj_injective hψ0 hker0 hZ, ReflInner.map_liftConj_apply hψ0 hker0⟩
  have hΛn : ∀ n : L', Λ (ψ₀ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI0 a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ₀ l) = ψ₀ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ0 r
      rw [hk, hAe0.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ₀ hker0 hperf0 fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe0 e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe0.2 _ he
  have hscE : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ0 hker0 hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker0 hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc0 n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hnp : ∀ z ∈ (projU n d K).ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    TableBUE.eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A₀, hA₀map, -, hA₀ab, -⟩ :=
    TableBUE.exists_lift_of_noTorsion (projU n d K) projU_surjective hp hnp hEab
  obtain ⟨P, hP, hPd⟩ := TableBUE.exists_conj_diag h hp hpq hA₀ab
  obtain ⟨u, hord, huq⟩ : ∃ u : Kˣ, orderOf u = p ∧ u ^ (2 ^ n + 1) = 1 := by
    have := Fact.mk hp
    have hpK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have e : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have := Nat.sq_sub_sq (2 ^ n) 1
        rwa [one_pow] at this
      rw [e]
      exact Dvd.dvd.mul_right hpq _
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hpK
    refine ⟨u, hu, ?_⟩
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, ← hu, pow_orderOf_eq_one, one_pow]
  have hu : u ^ p = 1 := hord ▸ pow_orderOf_eq_one u
  set τ : ↥(sumZero d p) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    (frameMk h P hP).comp (ggTBJSuD h hu huq hord) with hτ
  have hτapp : ∀ f, τ f = projU n d K ((TableBUE.conjSU h P hP).symm
      (ggTBJSuD h hu huq hord f)) := fun f => rfl
  have hEA : ∀ e ∈ E, ∃ y ∈ A₀, projU n d K y = e := by
    intro e he
    rw [← hA₀map] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hcommA : ∀ f, ∀ y ∈ A₀, τ f * projU n d K y = projU n d K y * τ f := by
    intro f y hy
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hc : (TableBUE.conjSU h P hP).symm (ggTBJSuD h hu huq hord f) * y =
        y * (TableBUE.conjSU h P hP).symm (ggTBJSuD h hu huq hord f) := by
      apply (TableBUE.conjSU h P hP).injective
      apply Subtype.ext
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul, hσ,
        ggTBJSuD_coe h hu huq hord, ← map_mul, ← map_mul, mul_comm]
    rw [hτapp, ← map_mul, hc, map_mul]
  have hτE1 : ∀ f, τ f ∈ E := by
    intro f
    refine hscE (τ f) (fun e he => ?_) (by rw [← map_pow, pow_p_eq_one, map_one])
    obtain ⟨y, hy, rfl⟩ := hEA e he
    exact hcommA f y hy
  have hτE2 : ∀ e ∈ E, ∃ f, τ f = e := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := hEA e he
    obtain ⟨σ, hσ⟩ := hPd y hy
    have hσp : ∀ k, σ k ^ p = 1 := by
      have h1 : (TableBUE.conjSU h P hP y) ^ p = 1 := by
        rw [← map_pow, hA₀ab.2 y hy, map_one]
      have h2 : diagHom d (σ ^ p) = 1 := by
        rw [map_pow, ← hσ, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
      have h3 : σ ^ p = 1 := diagHom_injective d (by rw [h2, map_one])
      intro k
      exact congrFun h3 k
    have hσprod : ∏ k, σ k = 1 := by
      have h1 := ((mem_unitarySU_iff h).mp (TableBUE.conjSU h P hP y).2).1
      rw [hσ, det_diagHom] at h1
      exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact h1)
    obtain ⟨f, hf⟩ := exists_uvec_eq hu hord hσp hσprod
    refine ⟨f, ?_⟩
    rw [hτapp]
    congr 1
    apply (TableBUE.conjSU h P hP).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [ggTBJSuD_coe h hu huq hord, hf, hσ]
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    rw [hτapp] at hf
    have h1 := hnp _ (MonoidHom.mem_ker.mpr hf)
      (by rw [← map_pow, ← map_pow, pow_p_eq_one, map_one, map_one])
    have h2 : ggTBJSuD h hu huq hord f = 1 := by
      have := congrArg (TableBUE.conjSU h P hP) h1
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    have h3 : uvec hu f = 1 := by
      apply diagHom_injective d
      rw [map_one, ← ggTBJSuD_coe h hu huq hord, h2, Subgroup.coe_one]
    apply uvec_injective hu hord
    rw [h3, map_one]
  have hτrange : τ.range = E := by
    ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE1 f
    · intro he
      obtain ⟨f, hf⟩ := hτE2 e he
      exact ⟨f, hf⟩
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => hτE1 f
  set Θ₀ : ↥(sumZero d p) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτrange] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : ↥(sumZero d p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  obtain ⟨σ, hσ, hσpow⟩ := exists_section_of_centerPrime hp hψ0 hker0 hcpL
    (V := ↥(sumZero d p)) pow_p_eq_one τ
  have hψσ : ∀ f, ψ₀ (σ f) = τ f := fun f => hσ f
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ₀ n * τ f * (ψ₀ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ₀ n * τ f * (ψ₀ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ₀ n * τ f * (ψ₀ n)⁻¹ ∈ τ.range := hτrange ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨u, hu, huq, hord, frameMk h P hP, σ, Θ, frameMk_surjective h P hP,
    TableBUI.ker_frameMk_le_center h P hP, ?_, hΘσ, ?_⟩
  · intro f
    change ψ₀ (σ f) = τ f
    exact hψσ f
  · intro n hn a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have has : a = MulAut.conj (σ f) := by rw [← hΘσ, hf]
    obtain ⟨f', hf'⟩ := hNE n hn f
    have hconj : n * σ f * n⁻¹ = σ f' := by
      refine eq_of_lift_pow_eq_one hp hker0 hcpL ?_ ?_ (hσpow f')
      · rw [map_mul, map_mul, map_inv, hσ, hσ, hf']
      · rw [conj_pow, hσpow, mul_one, mul_inv_cancel]
    have he : n * (a n)⁻¹ = σ (f' * f⁻¹) := by
      rw [has, MulAut.conj_apply, map_mul, map_inv, ← hconj]
      group
    rw [he]
    refine ⟨by rw [← map_pow, pow_p_eq_one, map_one], fun a' ha' => ?_⟩
    obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
    have ha's : a' = MulAut.conj (σ f'') := by rw [← hΘσ, hf'']
    have hc : σ f'' * σ (f' * f⁻¹) = σ (f' * f⁻¹) * σ f'' := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [ha's, MulAut.conj_apply, hc, mul_inv_cancel_right]

end CFSG.StandardType

end
