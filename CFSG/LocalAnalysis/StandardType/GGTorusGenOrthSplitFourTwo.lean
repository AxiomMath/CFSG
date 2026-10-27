module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthSplitFourFactors
public import CFSG.LieType.SeitzGeneration.OrthBlocks

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LayerCores CFSG.StandardType.LayerFacts
open CFSG.StandardType.SevOm
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] in
theorem fixRho_mem_orthDerived_of_orderOf {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hoddO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype),
      Odd (orderOf g) → g ∈ orthDerived (Q.comp (fixedSpace x).subtype))
    {z : V ≃ₗ[K] V} (hzX : z ∈ supportedBlock Q x (X - 1)) {e : ℕ} (hz : orderOf z = p ^ e) :
    fixRho hx ⟨z, hzX⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) ∧
      orderOf (fixRho hx ⟨z, hzX⟩) = p ^ e := by
  have hmem : fixRho hx ⟨z, hzX⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
    rw [← range_fixRho hx]
    exact ⟨⟨z, hzX⟩, rfl⟩
  have hord : orderOf (fixRho hx ⟨z, hzX⟩) = orderOf z :=
    (orderOf_injective (fixRho hx) (fixRho_injective hx) ⟨z, hzX⟩).trans
      (Subgroup.orderOf_mk z hzX)
  refine ⟨hoddO _ hmem ?_, hord.trans hz⟩
  rw [hord, hz]
  exact (hp.odd_of_ne_two hp2).pow

omit [Finite K] [CharP K 2] in
theorem pow_eq_one_of_pow_mul_pow_eq_one {U U' : Submodule K V}
    (hnd : ∀ u ∈ U, (∀ v ∈ U, polar Q v u = 0) → u = 0)
    (horth : ∀ u ∈ U, ∀ v ∈ U', polar Q u v = 0) {z z' : V ≃ₗ[K] V}
    (hz : ∀ v, (∀ u ∈ U, polar Q u v = 0) → z v = v)
    (hz' : ∀ v, (∀ u ∈ U', polar Q u v = 0) → z' v = v) (a b : ℕ)
    (h : z ^ a * z' ^ b = 1) : z ^ a = 1 := by
  have hS : PolarNondegOn Q U := fun x hx hxy =>
    hnd x hx fun y hy => by rw [polar_comm]; exact hxy y hy
  have hza : z ^ a = (z' ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hz'fix : ∀ u ∈ U, z' u = u := by
    intro u hu
    exact hz' u fun u' hu' => by rw [polar_comm]; exact horth u hu u' hu'
  have hz'pow : ∀ u ∈ U, (z' ^ b) u = u := fun u hu => by
    rw [LinearEquiv.pow_apply]
    exact Function.iterate_fixed (hz'fix u hu) b
  have hz'inv : ∀ u ∈ U, (z' ^ b)⁻¹ u = u := by
    intro u hu
    change (z' ^ b).symm u = u
    rw [LinearEquiv.symm_apply_eq]
    exact (hz'pow u hu).symm
  have hzaU : ∀ u ∈ U, (z ^ a) u = u := by
    intro u hu
    rw [hza]
    exact hz'inv u hu
  have hzaPerp : ∀ v, (∀ u ∈ U, polar Q u v = 0) → (z ^ a) v = v := by
    intro v hv
    rw [LinearEquiv.pow_apply]
    exact Function.iterate_fixed (hz v hv) a
  refine LinearEquiv.ext fun v => ?_
  have hc : IsCompl U (perp Q U) := isCompl_perp hS
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (hc.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule K V)))
  rw [map_add, hzaU u hu, hzaPerp w (mem_perp.mp hw)]
  rfl

theorem exists_pow_mul_pow_mem_of_sl2 {W : Type} [AddCommGroup W] [Module K W]
    {D T T' : Subgroup (W ≃ₗ[K] W)} (hT'D : T' ≤ D) (hsup : T ⊔ T' = D) (hinf : T ⊓ T' = ⊥)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T', x * y = y * x)
    {ψ' : SL(2, K) →* (W ≃ₗ[K] W)} (hψ' : Function.Injective ψ') (hr' : ψ'.range = T')
    {e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u v : W ≃ₗ[K] W} (huD : u ∈ D) (hvD : v ∈ D)
    (huv : u * v = v * u) (hu : orderOf u = p ^ e) (hv : orderOf v = p ^ e)
    (hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1) :
    ∃ a b : ℕ, u ^ a * v ^ b ∈ T ∧ orderOf (u ^ a * v ^ b) = p ^ e := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, hφ⟩ := exists_proj_of_isCompl hT'D hsup hinf hcommT
  let u' : ↥D := ⟨u, huD⟩
  let v' : ↥D := ⟨v, hvD⟩
  have huv' : u' * v' = v' * u' := by
    apply Subtype.ext
    simpa using huv
  have hu' : orderOf u' = p ^ e := (Subgroup.orderOf_mk u huD).trans hu
  have hv' : orderOf v' = p ^ e := (Subgroup.orderOf_mk v hvD).trans hv
  have hdvd_u : orderOf (φ u') ∣ p ^ e := hu' ▸ orderOf_map_dvd φ u'
  have hdvd_v : orderOf (φ v') ∣ p ^ e := hv' ▸ orderOf_map_dvd φ v'
  have huvφ : φ u' * φ v' = φ v' * φ u' := by
    rw [← map_mul, ← map_mul, huv']
  have hcyc := isCyclic_closure_pair_of_sl2 hT'D hψ' hr' hp2 huvφ hdvd_u hdvd_v
  have hind' : ∀ a b : ℕ, u' ^ a * v' ^ b = 1 → u' ^ a = 1 := by
    intro a b hab
    have h1 : u ^ a * v ^ b = 1 := by
      have := congrArg (fun d : ↥D => (d : W ≃ₗ[K] W)) hab
      simpa using this
    have h2 : u ^ a = 1 := hind a b h1
    apply Subtype.ext
    simpa using h2
  obtain ⟨a, b, hφab, hord⟩ := exists_pow_mul_pow_mem_ker hp φ huv' hu' hv' hind' hcyc
  have hker : ((φ (u' ^ a * v' ^ b) : ↥(T'.subgroupOf D)) : ↥D) = 1 := by
    rw [hφab]
    rfl
  have hmemT : u' ^ a * v' ^ b ∈ T.subgroupOf D := (hφ _).mp hker
  refine ⟨a, b, ?_, ?_⟩
  · simpa using (Subgroup.mem_subgroupOf.mp hmemT)
  · simpa using (Subgroup.orderOf_coe (u' ^ a * v' ^ b)).trans hord

omit [Finite K] [CharP K 2] in
theorem fixRho_commute {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {z z' : V ≃ₗ[K] V} (hz : z ∈ supportedBlock Q x (X - 1))
    (hz' : z' ∈ supportedBlock Q x (X - 1)) (h : z * z' = z' * z) :
    fixRho hx ⟨z, hz⟩ * fixRho hx ⟨z', hz'⟩ =
      fixRho hx ⟨z', hz'⟩ * fixRho hx ⟨z, hz⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

omit [Finite K] [CharP K 2] in
theorem fixRho_pow_eq_one_of_pow_mul_pow_eq_one {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {z z' : V ≃ₗ[K] V}
    (hz : z ∈ supportedBlock Q x (X - 1)) (hz' : z' ∈ supportedBlock Q x (X - 1))
    (hind : ∀ a b : ℕ, z ^ a * z' ^ b = 1 → z ^ a = 1) :
    ∀ a b : ℕ, fixRho hx ⟨z, hz⟩ ^ a * fixRho hx ⟨z', hz'⟩ ^ b = 1 →
      fixRho hx ⟨z, hz⟩ ^ a = 1 := by
  intro a b hab
  have hsub : (⟨z, hz⟩ : ↥(supportedBlock Q x (X - 1))) ^ a *
      (⟨z', hz'⟩ : ↥(supportedBlock Q x (X - 1))) ^ b = 1 := by
    apply fixRho_injective hx
    rw [map_mul, map_pow, map_pow, hab, map_one]
  have hzab : z ^ a * z' ^ b = 1 := by
    have h := congrArg (fun d : ↥(supportedBlock Q x (X - 1)) => (d : V ≃ₗ[K] V)) hsub
    simpa using h
  have hsub1 : (⟨z, hz⟩ : ↥(supportedBlock Q x (X - 1))) ^ a = 1 := by
    apply Subtype.ext
    simpa using hind a b hzab
  rw [← map_pow, hsub1, map_one]

omit [Finite K] [CharP K 2] in
theorem fixRho_pow_mul_pow {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (g g' : ↥(supportedBlock Q x (X - 1))) (a b : ℕ) :
    fixRho hx (g ^ a * g' ^ b) = fixRho hx g ^ a * fixRho hx g' ^ b ∧
      orderOf ((g ^ a * g' ^ b : ↥(supportedBlock Q x (X - 1))) : V ≃ₗ[K] V) =
        orderOf (fixRho hx g ^ a * fixRho hx g' ^ b) := by
  have hmap : fixRho hx (g ^ a * g' ^ b) = fixRho hx g ^ a * fixRho hx g' ^ b := by
    rw [map_mul, map_pow, map_pow]
  refine ⟨hmap, ?_⟩
  rw [← hmap, orderOf_injective (fixRho hx) (fixRho_injective hx) (g ^ a * g' ^ b),
    Subgroup.orderOf_coe (g ^ a * g' ^ b)]

theorem splitFour_two_coord_exists (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) →
      y * y' = y' * y)
    {e : ℕ} (hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s))
    {J : Subgroup (V ≃ₗ[K] V)} {k l : Fin r} (hk : toAdd s k = 0) (hl : toAdd s l = 0)
    (hkl : k ≠ l) {T T' : Subgroup (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hsup : T ⊔ T' = orthDerived (Q.comp (fixedSpace (F.ι s)).subtype)) (hinf : T ⊓ T' = ⊥)
    (hcommT : ∀ x ∈ T, ∀ y ∈ T', x * y = y * x)
    {ψ' : SL(2, K) →* (fixedSpace (F.ι s) ≃ₗ[K] fixedSpace (F.ι s))}
    (hψ' : Function.Injective ψ') (hr' : ψ'.range = T')
    (hoddO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace (F.ι s)).subtype),
      Odd (orderOf g) → g ∈ orthDerived (Q.comp (fixedSpace (F.ι s)).subtype))
    (hTJ : (J.subgroupOf (supportedBlock Q (F.ι s) (X - 1))).map (fixRho hx) = T) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  obtain ⟨z_k, hzkO, hzkE, hzkord, hzkfix⟩ := hz k
  obtain ⟨z_l, hzlO, hzlE, hzlord, hzlfix⟩ := hz l
  let F₀ := supportedBlock Q (F.ι s) (X - 1)
  have hzkF : z_k ∈ F₀ :=
    mem_supportedBlock_of_vanishes hQ hp hp2 hEΩ F s hk hzkO hzkE hzkfix
  have hzlF : z_l ∈ F₀ :=
    mem_supportedBlock_of_vanishes hQ hp hp2 hEΩ F s hl hzlO hzlE hzlfix
  have hzkp : z_k ^ p ^ e = 1 := by rw [← hzkord]; exact pow_orderOf_eq_one z_k
  have hzlp : z_l ^ p ^ e = 1 := by rw [← hzlord]; exact pow_orderOf_eq_one z_l
  have hzkzl : z_k * z_l = z_l * z_k :=
    hcomm z_k hzkO z_l hzlO hzkE hzlE ⟨e, hzkp⟩ ⟨e, hzlp⟩
  let g : ↥F₀ := ⟨z_k, hzkF⟩
  let g' : ↥F₀ := ⟨z_l, hzlF⟩
  obtain ⟨huD, huord⟩ := fixRho_mem_orthDerived_of_orderOf hx hp hp2 hoddO hzkF hzkord
  obtain ⟨hvD, hvord⟩ := fixRho_mem_orthDerived_of_orderOf hx hp hp2 hoddO hzlF hzlord
  have huv : fixRho hx g * fixRho hx g' = fixRho hx g' * fixRho hx g :=
    fixRho_commute hx hzkF hzlF hzkzl
  have hind : ∀ a b : ℕ, fixRho hx g ^ a * fixRho hx g' ^ b = 1 →
      fixRho hx g ^ a = 1 :=
    fixRho_pow_eq_one_of_pow_mul_pow_eq_one hx hzkF hzlF
      (pow_eq_one_of_pow_mul_pow_eq_one (F.nondeg k) (F.orth k l hkl) hzkfix hzlfix)
  obtain ⟨a, b, hyT, hyord⟩ :=
    exists_pow_mul_pow_mem_of_sl2 (hsup ▸ le_sup_right) hsup hinf hcommT hψ' hr' hp hp2
      huD hvD huv huord hvord hind
  have hyF : z_k ^ a * z_l ^ b ∈ F₀ :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hzkF a) (Subgroup.pow_mem _ hzlF b)
  have hgg : (g ^ a * g' ^ b : ↥F₀) = ⟨z_k ^ a * z_l ^ b, hyF⟩ :=
    Subtype.ext (by simp [g, g'])
  obtain ⟨hmap, hord⟩ := fixRho_pow_mul_pow hx g g' a b
  rw [hgg] at hmap
  have hyJ : z_k ^ a * z_l ^ b ∈ J :=
    splitFour_mem_of_map_mem F s hx hTJ hyF (by rw [hmap]; exact hyT)
  refine ⟨z_k ^ a * z_l ^ b, hyJ, ?_, ?_⟩
  · exact fun c hc => ((Commute.pow_left (hzkE c hc) a).mul_left
      (Commute.pow_left (hzlE c hc) b)).eq
  · have hcoe : ((g ^ a * g' ^ b : ↥F₀) : V ≃ₗ[K] V) = z_k ^ a * z_l ^ b := by
      simp [hgg]
    rw [← hcoe, hord, hyord]

end CFSG.StandardType.OrthTorusGen
