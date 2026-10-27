module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

abbrev frameDelta (j : Fin r) : Multiplicative (Fin r → ZMod p) :=
  ofAdd (Pi.single j (1 : ZMod p) : Fin r → ZMod p)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_perp_pieces (F : SevOm.Frame Q p E r) (v : V) :
    v ∈ perp Q (⨆ j, F.U j) ↔ ∀ j, ∀ u ∈ F.U j, polar Q u v = 0 := by
  change v ∈ (⨆ j, F.U j).orthogonalBilin (polarBilin Q) ↔
    ∀ j, ∀ u ∈ F.U j, polar Q u v = 0
  rw [Submodule.orthogonalBilin_iSup, Submodule.mem_iInf]
  simpa only [Submodule.mem_orthogonalBilin, polarBilin_apply_apply]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_perp_pieces_iff_fixed (hp : p.Prime) (F : SevOm.Frame Q p E r) (v : V) :
    v ∈ perp Q (⨆ j, F.U j) ↔ ∀ c ∈ E, c v = v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun hv c hc => ?_, fun hv => (mem_perp_pieces F v).mpr fun j u hu => ?_⟩
  · obtain ⟨s, rfl⟩ := F.exists_eq hc
    exact (F.fix s v).mpr fun j _ u hu => (mem_perp_pieces F v).mp hv j u hu
  · have h1 : F.ι (frameDelta j) v = v := hv _ (F.mem _)
    have h2 : toAdd (frameDelta (p := p) j) j ≠ 0 := by
      rw [toAdd_ofAdd, Pi.single_eq_same]
      exact one_ne_zero
    exact (F.fix _ v).mp h1 j h2 u hu

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem fixedSpace_eq_perp_pieces (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hs : ∀ j, toAdd s j ≠ 0) :
    fixedSpace (F.ι s) = perp Q (⨆ j, F.U j) := by
  ext v
  rw [mem_fixedSpace, mem_perp_pieces F v, F.fix s v]
  exact ⟨fun h j u hu => h j (hs j) u hu, fun h j _ u hu => h j u hu⟩

omit [Finite K] in
theorem polarNondegOn_perpPieces (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r) :
    PolarNondegOn Q (perp Q (⨆ j, F.U j)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let s₀ : Multiplicative (Fin r → ZMod p) := ofAdd fun _ => 1
  have hs : ∀ j, toAdd s₀ j ≠ 0 := fun j => by simp [s₀]
  have hx := F.oddOrderIsometry hQ hp2 hp hEΩ s₀
  rw [← fixedSpace_eq_perp_pieces F s₀ hs]
  exact polarNondegOn_of_nondegenerate hx.polarBilin_fixed_nondegenerate

omit [Finite K] [CharP K 2] in
theorem perp_perpPieces (hQ : (polarBilin Q).Nondegenerate) (F : SevOm.Frame Q p E r) :
    perp Q (perp Q (⨆ j, F.U j)) = ⨆ j, F.U j :=
  LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl _

omit [Finite K] [CharP K 2] in
theorem commSpace_frameSingle (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r) (j : Fin r) :
    commSpace (F.ι (frameDelta j)) = F.U j := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hsj : toAdd (frameDelta (p := p) j) j ≠ 0 := by
    rw [toAdd_ofAdd, Pi.single_eq_same]; exact one_ne_zero
  have htO : F.ι (frameDelta j) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup (hEΩ (F.mem _))
  have hker : fixSpace (F.ι (frameDelta j)) = perp Q (F.U j) := by
    ext v
    rw [mem_fixSpace, mem_perp, F.fix (frameDelta j) v]
    constructor
    · intro h u hu; exact h j hsj u hu
    · intro h i hi u hu
      have hij : i = j := by
        by_contra hne
        exact hi (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
      subst hij
      exact h u hu
  have hperp : perp Q (perp Q (F.U j)) = F.U j :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl _
  have hle : commSpace (F.ι (frameDelta j)) ≤ F.U j := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [← hperp, mem_perp]
    intro u hu
    rw [← hker, mem_fixSpace] at hu
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO u v
    rw [hu] at h1
    rw [polar_sub_right, h1, sub_self]
  have hdim : finrank K (commSpace (F.ι (frameDelta j))) = finrank K (F.U j) := by
    have h1 := finrank_commSpace_add_finrank_fixSpace (F.ι (frameDelta j))
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hQ] at h1
    have h2 : finrank K (F.U j) ≤ finrank K V := Submodule.finrank_le _
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem frame_one_of_triv (F : SevOm.Frame Q p E r) {c : V ≃ₗ[K] V}
    (hc : c ∈ E) (htriv : ∀ j, ∀ u ∈ F.U j, c u = u) : c = 1 := by
  classical
  obtain ⟨s, rfl⟩ := F.exists_eq hc
  by_contra hne
  have hs : s ≠ 1 := fun h => hne (by rw [h, map_one])
  have hfun : toAdd s ≠ 0 := fun h => hs (toAdd.injective (by rw [h, toAdd_one]))
  obtain ⟨j, hj⟩ : ∃ j, toAdd s j ≠ 0 := by
    by_contra h
    push Not at h
    exact hfun (funext h)
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot j)
  exact hu0 (F.fpf s j hj u hu (htriv j u hu))

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem stable_perp_piece (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r) (j : Fin r) :
    ∀ c ∈ E, ∀ v ∈ perp Q (F.U j), c v ∈ perp Q (F.U j) := by
  intro c hc v hv
  rw [mem_perp] at hv ⊢
  intro u hu
  have hcu : c.symm u ∈ F.U j := by
    change c⁻¹ u ∈ F.U j
    obtain ⟨t, ht⟩ := F.exists_eq (E.inv_mem hc)
    rw [← ht]; exact F.mapsTo t j u hu
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (orthDerived_le_orthogonalGroup (hEΩ hc)) (c.symm u) v
  rw [c.apply_symm_apply] at h1
  rw [h1]; exact hv (c.symm u) hcu

theorem exists_pow_orderOf_eq_prime {G : Type*} [Group G] {x : G} {k : ℕ}
    (hp : p.Prime) (hx : x ^ p ^ k = 1) (hne : x ≠ 1) :
    ∃ (z : G) (m : ℕ), z = x ^ m ∧ orderOf z = p := by
  classical
  have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hjeq
    exact hne (orderOf_eq_one_iff.mp hjeq)
  have hdiv : p ∣ orderOf x := by rw [hjeq]; exact dvd_pow_self p hj
  exact ⟨x ^ (orderOf x / p), orderOf x / p, rfl,
    orderOf_pow_orderOf_div (by rw [hjeq]; exact pow_ne_zero _ hp.ne_zero) hdiv⟩

omit [Finite K] [CharP K 2] in
theorem extendId_commute_of_stable {S : Submodule K V} (hS : PolarNondegOn Q S)
    (hS1 : ∀ c ∈ E, ∀ s ∈ S, c s ∈ S) (hS2 : ∀ c ∈ E, ∀ r ∈ perp Q S, c r ∈ perp Q S)
    {a : V ≃ₗ[K] V} (haE : ∀ c ∈ E, a * c = c * a)
    (h1 : ∀ s ∈ S, a s ∈ S) (h2 : ∀ s ∈ S, a.symm s ∈ S) :
    ∀ c ∈ E, extendId hS a h1 h2 * c = c * extendId hS a h1 h2 := by
  intro c hc
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, hu, r, hr, rfl⟩ :=
    Submodule.mem_sup.mp ((isCompl_perp hS).sup_eq_top ▸ Submodule.mem_top (x := v))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add c u r,
    extendId_apply hS h1 h2 hu hr,
    extendId_apply hS h1 h2 (hS1 c hc u hu) (hS2 c hc r hr), map_add,
    add_right_cancel_iff]
  simpa [LinearEquiv.mul_apply] using congrArg (fun f : V ≃ₗ[K] V => f u) (haE c hc)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem map_commSpace_of_commute {a t : V ≃ₗ[K] V} (h : a * t = t * a) {x : V}
    (hx : x ∈ commSpace t) : a x ∈ commSpace t := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  have h1 : a (t v) = t (a v) := by
    have h2 := congrArg (fun f : V ≃ₗ[K] V => f v) h
    simpa [LinearEquiv.mul_apply] using h2
  rw [map_sub, h1]
  exact sub_mem_commSpace t (a v)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem restrictEquiv_commute {U : Submodule K V} {g t : V ≃ₗ[K] V}
    (hg1 : ∀ u ∈ U, g u ∈ U) (hg2 : ∀ u ∈ U, g.symm u ∈ U)
    (ht1 : ∀ u ∈ U, t u ∈ U) (ht2 : ∀ u ∈ U, t.symm u ∈ U) (h : g * t = t * g) :
    restrictEquiv U g hg1 hg2 * restrictEquiv U t ht1 ht2 =
      restrictEquiv U t ht1 ht2 * restrictEquiv U g hg1 hg2 := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  simp only [LinearEquiv.mul_apply, coe_restrictEquiv]
  exact congrArg (fun f : V ≃ₗ[K] V => f (u : V)) h

omit [Finite K] [FiniteDimensional K V] in
theorem restrictEquiv_not_scalar {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hne : U ≠ ⊥) {t : V ≃ₗ[K] V} (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht1 : ∀ u ∈ U, t u ∈ U) (ht2 : ∀ u ∈ U, t.symm u ∈ U)
    (hfpf : ∀ u ∈ U, t u = u → u = 0) :
    ∀ c : K, (restrictEquiv U t ht1 ht2).toLinearMap ≠ c • 1 := by
  intro c hc
  have hcu : ∀ u ∈ U, t u = c • u := by
    intro u hu
    have h := congrArg (fun f : Module.End K U => (f ⟨u, hu⟩ : V)) hc
    simpa [LinearEquiv.coe_toLinearMap, Module.End.one_apply, coe_restrictEquiv] using h
  have hex : ∃ u ∈ U, ∃ v ∈ U, polar Q u v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne ((Submodule.eq_bot_iff U).mpr fun u hu =>
      hU u hu fun v hv => h u hu v hv)
  obtain ⟨u0, hu0, v0, hv0, hpol⟩ := hex
  have h1 : polar Q (t u0) (t v0) = polar Q u0 v0 :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO u0 v0
  have h2 : polar Q (t u0) (t v0) = c ^ 2 * polar Q u0 v0 := by
    rw [hcu u0 hu0, hcu v0 hv0, polar_smul_left, polar_smul_right, smul_eq_mul, smul_eq_mul]
    ring
  have hc2 : c ^ 2 = 1 := by
    refine mul_right_cancel₀ hpol ?_
    rw [← h2, h1, one_mul]
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · rw [show (-1 : K) = 1 from CharTwo.neg_eq 1] at h
      exact h
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hne
  exact hu0 (hfpf u hu (by rw [hcu u hu, hc1, one_smul]))

omit [Finite K] [CharP K 2] in
theorem frame_preserves_piece (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r) {y : V ≃ₗ[K] V}
    (hyE : ∀ c ∈ E, y * c = c * y) :
    (∀ j, ∀ u ∈ F.U j, y u ∈ F.U j) ∧
      (∀ j, ∀ u ∈ F.U j, y.symm u ∈ F.U j) := by
  constructor
  · intro j u hu
    rw [← commSpace_frameSingle hQ hp hEΩ F j] at hu ⊢
    exact map_commSpace_of_commute (hyE _ (F.mem _)) hu
  · intro j u hu
    rw [← commSpace_frameSingle hQ hp hEΩ F j] at hu ⊢
    exact map_commSpace_of_commute (Commute.inv_left (hyE _ (F.mem _))) hu

end CFSG.StandardType.OrthTorusGen
