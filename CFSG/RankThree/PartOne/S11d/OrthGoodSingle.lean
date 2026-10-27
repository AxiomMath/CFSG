module

public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarFixed
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def ActsBySemilinear (Q : QuadraticForm K V) (S : V ≃+ V)
    (α : MulAut (ProjOrthDerived Q)) : Prop :=
  ∀ ω : orthDerived Q, ∃ ω' : orthDerived Q,
    (∀ v, (ω' : V ≃ₗ[K] V) v = S ((ω : V ≃ₗ[K] V) (S.symm v))) ∧
      α (piOrth Q ω) = piOrth Q ω'

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem ActsBySemilinear.fixed {S : V ≃+ V} {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q S α) (ω : orthDerived Q)
    (h : ∀ v, S ((ω : V ≃ₗ[K] V) v) = (ω : V ≃ₗ[K] V) (S v)) : α (piOrth Q ω) = piOrth Q ω := by
  obtain ⟨ω', h1, h2⟩ := hα ω
  rw [h2]
  congr 1
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  rw [h1 v, h (S.symm v), AddEquiv.apply_symm_apply]

theorem not_inner_fixedComponentImage_of_semilinear
    (hQ : (polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K)
    {σ : K ≃+* K} (hσ : ∃ c, σ c ≠ c) (S : V ≃+ V)
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hQS : ∀ v, Q (S v) = σ (Q v))
    {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (h4 : 4 ≤ finrank K (fixedSpace x)) :
    ∀ e ∈ fixedComponentImage Q x, ¬ ∀ g ∈ fixedComponentImage Q x,
      α g = e * g * e⁻¹ := by
  have : Nontrivial V := nontrivial_of_four_le_finrank_fixed h4
  intro e he hcon
  obtain ⟨e', _he'L, rfl⟩ := he
  set ee : V ≃ₗ[K] V := (e' : V ≃ₗ[K] V) with hee
  have heeO : ee ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup e'.2
  have hconj : ∀ f ∈ supportedFixedDerived Q x, ∀ v,
      S (f (S.symm v)) = ee (f (ee.symm v)) := by
    intro f hf v
    have hfΩ : f ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived hf
    have hfL : piOrth Q ⟨f, hfΩ⟩ ∈ fixedComponentImage Q x :=
      ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    obtain ⟨ω', h1, h2⟩ := hα ⟨f, hfΩ⟩
    have h3 := hcon _ hfL
    rw [h2, ← map_inv, ← map_mul, ← map_mul] at h3
    have h5 : (ω' : V ≃ₗ[K] V) v = ee (f (ee.symm v)) :=
      congrArg (fun a : orthDerived Q => (a : V ≃ₗ[K] V) v) (piOrth_injective hQ h3)
    rw [← h1 v, h5]
  let F : V ≃+ V := S.trans ee.symm.toAddEquiv
  have hFQ : ∀ v, Q (F v) = (1 : K) * (σ : K ≃+* K) (Q v) := fun v => by
    rw [one_mul]
    change Q (ee.symm (S v)) = _
    have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (inv_mem heeO) (S v)
    rw [show ee.symm = ee⁻¹ from rfl, this, hQS]
  have hcomm : ∀ g' ∈ supportedDerived Q (fixedSpace x), ∀ v, F (g' v) = g' (F v) := by
    intro g' hg' v
    have := hconj g' (supportedDerived_le_supportedFixedDerived hx hg') (S v)
    rw [AddEquiv.symm_apply_apply] at this
    change ee.symm (S (g' v)) = g' (ee.symm (S v))
    rw [this, LinearEquiv.symm_apply_apply]
  obtain ⟨hsing, hM⟩ := hx.fixed_scalar_data hK h4
  obtain ⟨hσc, -⟩ := scalar_restriction_of_commute F σ 1 hFQ hcomm hQ
    hx.polarBilin_fixed_nondegenerate (by omega) hsing hM (fun c v => by
      change ee.symm (S (c • v)) = σ c • ee.symm (S v)
      rw [hS, map_smul])
  obtain ⟨c, hc⟩ := hσ
  exact hc (hσc c)


theorem supportedDerived_top_eq_orthDerived {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) :
    supportedDerived Q (⊤ : Submodule K V) = orthDerived Q := by
  let e : (Q.comp (⊤ : Submodule K V).subtype).IsometryEquiv Q :=
    { Submodule.topEquiv with map_app' := fun x => rfl }
  have hmap := map_orthDerived_linConj e
  rw [← hmap]
  ext g
  rw [Subgroup.mem_map, mem_supportedDerived]
  constructor
  · rintro ⟨-, h, hh, hg⟩
    refine ⟨h, hh, ?_⟩
    ext v
    change e.toLinearEquiv (h (e.toLinearEquiv.symm v)) = g v
    rw [show e.toLinearEquiv (h (e.toLinearEquiv.symm v)) =
      ((h (e.toLinearEquiv.symm v) : (⊤ : Submodule K V)) : V) from rfl]
    rw [hg (e.toLinearEquiv.symm v)]
    rfl
  · rintro ⟨h, hh, rfl⟩
    refine ⟨?_, h, hh, fun w => ?_⟩
    · intro v hv
      have hbot : suppPerp Q (⊤ : Submodule K V) = ⊥ := by
        simpa [suppPerp] using LinearMap.BilinForm.orthogonal_top_eq_bot hQ
      rw [hbot] at hv
      simp only [Submodule.mem_bot] at hv
      simp [hv]
    · rfl

theorem not_inner_orthDerived_of_semilinear
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K)
    (hV : 4 ≤ finrank K V) {σ : K ≃+* K} (hσ : σ ≠ 1) (S : V ≃+ V)
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hQS : ∀ v, Q (S v) = σ (Q v))
    (f : MulAut (orthDerived Q))
    (hf : ∀ (g : orthDerived Q) v, (f g : V ≃ₗ[K] V) v = S ((g : V ≃ₗ[K] V) (S.symm v))) :
    f ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (orthDerived Q) := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hσ' : ∃ c, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hx1 : OddOrderIsometry Q 1 (1 : V ≃ₗ[K] V) :=
    { mem := one_mem _
      pow_eq_one := one_pow 1
      cast_ne_zero := by simpa using (one_ne_zero : (1 : K) ≠ 0)
      regular := fun v hv => hQ.1 v (by simpa only [QuadraticMap.polarBilin_apply_apply] using hv) }
  have hfix : fixedSpace (1 : V ≃ₗ[K] V) = ⊤ := by
    ext v
    simp [fixedSpace]
  have h4 : 4 ≤ finrank K (fixedSpace (1 : V ≃ₗ[K] V)) := by
    rw [hfix]
    simpa using hV
  let ee : orthDerived Q ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective (piOrth Q) ⟨piOrth_injective hQ, piOrth_surjective⟩
  set α : MulAut (ProjOrthDerived Q) := MulAut.congr ee f with hαdef
  have hα : ActsBySemilinear Q S α := by
    intro ω
    refine ⟨f ω, hf ω, ?_⟩
    rw [hαdef]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hsymm : ee.symm ((piOrth Q) ω) = ω := by
      change ee.symm (ee ω) = ω
      exact ee.symm_apply_apply ω
    rw [hsymm]
    rfl
  have hnot := not_inner_fixedComponentImage_of_semilinear hQ hK hσ' S hS hQS hα hx1 h4
  have hSF : supportedFixedDerived Q (1 : V ≃ₗ[K] V) = orthDerived Q := by
    rw [← hx1.supportedDerived_fixedSpace, hfix]
    exact supportedDerived_top_eq_orthDerived hQ
  have himg : fixedComponentImage Q (1 : V ≃ₗ[K] V) = ⊤ := by
    unfold fixedComponentImage
    rw [hSF, Subgroup.subgroupOf_self, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr piOrth_surjective
  intro hfin
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at hfin
  obtain ⟨e0, he0⟩ := hfin
  have hαconj : α = MulAut.conj (ee e0) := by
    rw [hαdef, ← he0]
    exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj ee e0
  have hmem : ee e0 ∈ fixedComponentImage Q (1 : V ≃ₗ[K] V) := by
    rw [himg]
    exact Subgroup.mem_top _
  exact (hnot (ee e0) hmem) fun g _ => by
    rw [hαconj, MulAut.conj_apply]

theorem orth_good_of_single (hQ : (polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K)
    (hodd : Odd p) {σ : K ≃+* K} (hσ : ∃ c, σ c ≠ c) (S : V ≃+ V)
    (hS : ∀ (c : K) v, S (c • v) = σ c • S v) (hQS : ∀ v, Q (S v) = σ (Q v))
    {α : MulAut (ProjOrthDerived Q)} (hα : ActsBySemilinear Q S α) {x : V ≃ₗ[K] V}
    (hxΩ : x ∈ orthDerived Q) (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1) (h4 : 4 ≤ finrank K (fixedSpace x))
    (hD : DicksonDerived (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate)
    (hq : CFSG.IsQuasisimple ↥(fixedComponentImage Q x))
    (hmodel : ∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) t' n' 2
        (p * f'))
    (hpair : ∃ t₁ ∈ supportedFixedDerived Q x, (∀ v, S (t₁ v) = t₁ (S v)) ∧ t₁ ^ 2 = 1 ∧
      ∃ t₂ ∈ supportedFixedDerived Q x, (∀ v, S (t₂ v) = t₂ (S v)) ∧ t₂ ^ 2 = 1 ∧
        t₁ * t₂ ≠ t₂ * t₁) :
    GoodConclusion p (ProjOrthDerived Q) α (piOrth Q ⟨x, hxΩ⟩) := by
  have : Nontrivial V := nontrivial_of_four_le_finrank_fixed h4
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set T := ProjOrthDerived Q with hT
  set X : Subgroup T := Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set T) with hX
  have hXN : centralizerImage Q x = X := centralizerImage_eq hQ ⟨x, hxΩ⟩
  set L := fixedComponentImage Q x with hL
  have hLX : L ≤ X := hXN ▸ fixedComponentImage_le_centralizerImage
  have hcomp : IsComponentOf X L := by
    refine ⟨hLX, hq, ?_⟩
    have h1 := hx.normal_fixedComponentImage.isSubnormal
    rw [hXN] at h1
    exact h1
  have hsolv := isSolvable_centralizer_fixedComponentImage hQ hK hx hmult h4
  rw [hXN] at hsolv
  have hdec : ∀ E, IsComponentOf X E → E = L := by
    intro E hE
    obtain ⟨_, rfl⟩ := isComponentOf_eq_of_decomposition (X := X) (fun _ : Unit => L)
      (fun _ => hcomp) (by rw [iSup_const]; exact hsolv) hE
    rfl
  have hlayer : inSubgroup layer X = L := by
    rw [inSubgroup_layer_eq_of_decomposition (X := X) (fun _ : Unit => L) (fun _ => hcomp)
      (by rw [iSup_const]; exact hsolv)]
    exact iSup_const
  refine ⟨⟨L, hcomp⟩, ?_, ?_⟩
  · intro D hD' _
    have hDL := hdec D hD'
    subst hDL
    refine ⟨?_, hmodel, ?_⟩
    · exact not_inner_fixedComponentImage_of_semilinear hQ hK hσ S hS hQS hα hx h4
    · obtain ⟨t₁, ht₁, hS₁, ht₁2, t₂, ht₂, hS₂, ht₂2, hne⟩ := hpair
      have hΩ₁ : t₁ ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived ht₁
      have hΩ₂ : t₂ ∈ orthDerived Q := hx.supportedFixedDerived_le_orthDerived ht₂
      have hsq : ∀ t (ht : t ∈ orthDerived Q), t ^ 2 = 1 → ∃ k : ℕ, orderOf (piOrth Q ⟨t, ht⟩) = 2 ^ k := by
        intro t ht h2
        have : (piOrth Q ⟨t, ht⟩) ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨t, ht⟩ : orthDerived Q) ^ 2 = 1 := Subtype.ext h2
          rw [this, map_one]
        rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one this) with h | h
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩
      refine ⟨piOrth Q ⟨t₁, hΩ₁⟩, ⟨⟨t₁, hΩ₁⟩, Subgroup.mem_subgroupOf.mpr ht₁, rfl⟩,
        hα.fixed _ hS₁, piOrth Q ⟨t₂, hΩ₂⟩, ⟨⟨t₂, hΩ₂⟩, Subgroup.mem_subgroupOf.mpr ht₂, rfl⟩,
        hα.fixed _ hS₂, hsq t₁ hΩ₁ ht₁2, hsq t₂ hΩ₂ ht₂2, ?_⟩
      intro hcomm
      apply hne
      rw [← map_mul, ← map_mul] at hcomm
      exact congrArg (fun a : orthDerived Q => (a : V ≃ₗ[K] V)) (piOrth_injective hQ hcomm)
  · intro g hg _ hg2
    rw [hlayer]
    exact mem_fixedComponentImage_of_two_pow hQ hx hodd hmult h4 hD (hXN ▸ hg) hg2

end CFSG.RankThree.PartOne
