module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFix
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthKer
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnBlock
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusWitt
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock

public section

namespace CFSG.StandardType.OrthTorusGen

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] in
private theorem piece_parts_decomposition (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (j : Fin r) :
    (F.U j ⊓ orbitSpace (F.ι s).toLinearMap h) ⊔
        (F.U j ⊓ othersSpace (F.ι s).toLinearMap h) = F.U j ∧
      (F.U j ⊓ orbitSpace (F.ι s).toLinearMap h) ⊓
          (F.U j ⊓ othersSpace (F.ι s).toLinearMap h) = ⊥ ∧
        ∀ u ∈ F.U j ⊓ orbitSpace (F.ι s).toLinearMap h,
          ∀ v ∈ F.U j ⊓ othersSpace (F.ι s).toLinearMap h, polar Q u v = 0 := by
  let P1 := F.U j ⊓ orbitSpace (F.ι s).toLinearMap h
  let P2 := F.U j ⊓ othersSpace (F.ι s).toLinearMap h
  have hsup : P1 ⊔ P2 = F.U j := by
    refine le_antisymm ?_ ?_
    · exact sup_le inf_le_left inf_le_left
    · intro u hu
      obtain ⟨u1, hu1, u2, hu2, rfl⟩ :=
        SmallOrthUn.exists_split_orbit hx (fun y hy => F.mapsTo s j y hy) hu
      exact Submodule.mem_sup.mpr ⟨u1, hu1, u2, hu2, rfl⟩
  have hdisj : P1 ⊓ P2 = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    have h4 : u ∈ orbitSpace (F.ι s).toLinearMap h ⊓ othersSpace (F.ι s).toLinearMap h :=
      Submodule.mem_inf.mpr ⟨hu1.2, hu2.2⟩
    rw [(hx.isCompl_orbit_others hh).inf_eq_bot] at h4
    exact h4
  have horth : ∀ u ∈ P1, ∀ v ∈ P2, polar Q u v = 0 := by
    intro u hu v hv
    exact hx.polar_orbit_others hh hu.2 hv.2
  exact ⟨hsup, hdisj, horth⟩
omit [Finite K] [CharP K 2] in
private theorem piece_parts_nondeg (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (j : Fin r) :
    SUTB.NondegOn (polarBilin Q) (F.U j ⊓ orbitSpace (F.ι s).toLinearMap h) ∧
      SUTB.NondegOn (polarBilin Q) (F.U j ⊓ othersSpace (F.ι s).toLinearMap h) := by
  obtain ⟨-, -, horth⟩ := piece_parts_decomposition F s hx hh j
  let P1 := F.U j ⊓ orbitSpace (F.ι s).toLinearMap h
  let P2 := F.U j ⊓ othersSpace (F.ι s).toLinearMap h
  have hnd1 : SUTB.NondegOn (polarBilin Q) P1 := by
    intro u hu hperp
    refine F.nondeg j u hu.1 fun v hv => ?_
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ :=
      SmallOrthUn.exists_split_orbit hx (fun y hy => F.mapsTo s j y hy) hv
    rw [QuadraticMap.polar_add_left]
    have h1 : polar Q v1 u = 0 := hperp v1 hv1
    have h2 : polar Q v2 u = 0 := by
      rw [QuadraticMap.polar_comm]
      exact horth u hu v2 hv2
    rw [h1, h2, add_zero]
  have hnd2 : SUTB.NondegOn (polarBilin Q) P2 := by
    intro u hu hperp
    refine F.nondeg j u hu.1 fun v hv => ?_
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ :=
      SmallOrthUn.exists_split_orbit hx (fun y hy => F.mapsTo s j y hy) hv
    rw [QuadraticMap.polar_add_left]
    have h1 : polar Q v1 u = 0 := horth v1 hv1 u hu
    have h2 : polar Q v2 u = 0 := hperp v2 hv2
    rw [h1, h2, add_zero]
  exact ⟨hnd1, hnd2⟩
omit [Finite K] in
theorem piece_le_orbitSpace_or_le_othersSpace (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (j : Fin r) :
    F.U j ≤ orbitSpace (F.ι s).toLinearMap h ∨ F.U j ≤ othersSpace (F.ι s).toLinearMap h := by
  have hx : OddOrderIsometry Q p (F.ι s) := F.oddOrderIsometry hQ hp2 hp hEΩ s
  let P1 := F.U j ⊓ orbitSpace (F.ι s).toLinearMap h
  let P2 := F.U j ⊓ othersSpace (F.ι s).toLinearMap h
  obtain ⟨hsup, hdisj, -⟩ := piece_parts_decomposition F s hx hh j
  obtain ⟨hnd1, hnd2⟩ := piece_parts_nondeg F s hx hh j
  have hsup' : P1 ⊔ P2 = F.U j := hsup
  have hdisj' : P1 ⊓ P2 = ⊥ := hdisj
  have hfin : finrank K P1 + finrank K P2 = 2 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq P1 P2
    rw [hsup', hdisj', finrank_bot, add_zero] at h1
    rw [← h1, hU j]
  have heven1 : Even (finrank K P1) := OrthTorus.even_finrank_of_nondegOn hnd1
  have heven2 : Even (finrank K P2) := OrthTorus.even_finrank_of_nondegOn hnd2
  obtain ⟨k1, hk1⟩ := heven1
  obtain ⟨k2, hk2⟩ := heven2
  rw [hk1, hk2] at hfin
  have hk : k1 = 0 ∨ k2 = 0 := by omega
  rcases hk with hk | hk
  · right
    have hP1 : P1 = ⊥ := Submodule.finrank_eq_zero.mp (by rw [hk1, hk])
    rw [← hsup', hP1, bot_sup_eq]
    exact inf_le_right
  · left
    have hP2 : P2 = ⊥ := Submodule.finrank_eq_zero.mp (by rw [hk2, hk])
    rw [← hsup', hP2, sup_bot_eq]
    exact inf_le_right

omit [Finite K] [CharP K 2] in
private theorem eq_zero_of_mem_orbitSpace_of_fixed {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {w : V}
    (hw : w ∈ orbitSpace x.toLinearMap h) (hfix : x w = w) : w = 0 := by
  by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · have hne : (X - 1 : K[X]) ≠ h := fun e => hne1 e.symm
    have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne1 (by
      rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
    have hne' : (X - 1 : K[X]) ≠ reciprocalPolynomial h := fun e => hne1' e.symm
    have hwR : w ∈ othersSpace x.toLinearMap h :=
      Submodule.mem_iSup_of_mem (X - 1) (Submodule.mem_iSup_of_mem ⟨hX, hne, hne'⟩ (by
        rw [← fixedSpace_eq_primaryComponent]
        exact mem_fixedSpace.mpr hfix))
    have h1 : w ∈ orbitSpace x.toLinearMap h ⊓ othersSpace x.toLinearMap h :=
      Submodule.mem_inf.mpr ⟨hw, hwR⟩
    rw [(hx.isCompl_orbit_others hh).inf_eq_bot] at h1
    exact (Submodule.mem_bot K).mp h1
  · have hw' : w ∈ fixedSpace x := mem_fixedSpace.mpr hfix
    rw [fixedSpace_eq_bot_of_not_mem hX, Submodule.mem_bot] at hw'
    exact hw'

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem apply_eq_self_of_forall_polar_eq_zero (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) {w : V}
    (h : ∀ j, ∀ u ∈ F.U j, polar Q u w = 0) : F.ι s w = w :=
  (F.fix s w).mpr fun j _ u hu => h j u hu

omit [Finite K] in
private theorem orbitSpace_eq_bot_of_forall_not_le (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (hne1 : h ≠ X - 1)
    (hnot : ∀ j, ¬ (F.U j ≤ orbitSpace (F.ι s).toLinearMap h)) :
    orbitSpace (F.ι s).toLinearMap h = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hx := F.oddOrderIsometry hQ hp2 hp hEΩ s
  refine eq_zero_of_mem_orbitSpace_of_fixed hx hh hne1 hw ?_
  refine apply_eq_self_of_forall_polar_eq_zero F s fun j u hu => ?_
  have hUj : F.U j ≤ othersSpace (F.ι s).toLinearMap h := by
    rcases piece_le_orbitSpace_or_le_othersSpace hQ hp hp2 hEΩ F hU s hh j with h1 | h1
    · exact absurd h1 (hnot j)
    · exact h1
  rw [polar_comm]
  exact hx.polar_orbit_others hh hw (hUj hu)

omit [Finite K] in
private theorem orbitSpace_le_piece_of_unique (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (hne1 : h ≠ X - 1) {i : Fin r}
    (hi : F.U i ≤ orbitSpace (F.ι s).toLinearMap h)
    (hnot : ∀ j, j ≠ i → ¬ (F.U j ≤ orbitSpace (F.ι s).toLinearMap h)) :
    orbitSpace (F.ι s).toLinearMap h ≤ F.U i := by
  intro v hv
  obtain ⟨u, hu, w, hw, huv⟩ :=
    exists_add_of_isCompl (SevOmSmall.isCompl_orthogonal (F.nondeg i)) v
  have hx := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have hwO : w ∈ orbitSpace (F.ι s).toLinearMap h := by
    have hw_eq : w = v - u := by rw [← huv]; abel
    rw [hw_eq]
    exact Submodule.sub_mem _ hv (hi hu)
  have hw0 : w = 0 := by
    refine eq_zero_of_mem_orbitSpace_of_fixed hx hh hne1 hwO ?_
    refine apply_eq_self_of_forall_polar_eq_zero F s fun j u' hu' => ?_
    by_cases hji : j = i
    · subst hji
      exact SevOmSmall.mem_orthogonal_polar.mp hw u' hu'
    · have hUj : F.U j ≤ othersSpace (F.ι s).toLinearMap h := by
        rcases piece_le_orbitSpace_or_le_othersSpace hQ hp hp2 hEΩ F hU s hh j with h1 | h1
        · exact absurd h1 (hnot j hji)
        · exact h1
      rw [polar_comm]
      exact hx.polar_orbit_others hh hwO (hUj hu')
  rw [← huv, hw0, add_zero]
  exact hu
omit [CharP K 2] in
private theorem three_le_finrank_primaryComponent_of_selfdual {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    3 ≤ finrank K (primaryComponent x.toLinearMap h) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  obtain ⟨d, ℓ, f, hU, B, hdeg, -⟩ :=
    SevOmSmall.selfDual_unitary hx hp hp2 hh hne1 hself
  have hdeg2 : 2 ≤ h.natDegree := by
    rw [hdeg]
    have hd : 0 < d := by
      by_contra hd
      have h0 : d = 0 := by omega
      rw [h0, mul_zero] at hdeg
      exact hirr.natDegree_pos.ne' hdeg
    omega
  have hfin : 4 ≤ finrank K (primaryComponent x.toLinearMap h) := by
    rw [finrank_primaryComponent]
    nlinarith
  omega
omit [CharP K 2] [Finite K] in
private theorem three_le_finrank_orbitSpace_of_paired {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hself : h ≠ reciprocalPolynomial h) :
    3 ≤ finrank K (orbitSpace x.toLinearMap h) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have hh' : reciprocalPolynomial h ∈ primaryFactors x.toLinearMap := hx.reciprocalPolynomial_mem hh
  have hdisj : primaryComponent x.toLinearMap h ⊓
      primaryComponent x.toLinearMap (reciprocalPolynomial h) = ⊥ :=
    (disjoint_primaryComponent_of_ne hx hh hh' hself).eq_bot
  have hfin : finrank K (primaryComponent x.toLinearMap h ⊔
      primaryComponent x.toLinearMap (reciprocalPolynomial h) : Submodule K V) =
      finrank K (primaryComponent x.toLinearMap h) +
        finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (primaryComponent x.toLinearMap h)
      (primaryComponent x.toLinearMap (reciprocalPolynomial h))
    rw [hdisj, finrank_bot, add_zero] at h
    exact h
  have h1 : 2 ≤ finrank K (primaryComponent x.toLinearMap h) := by
    rw [finrank_primaryComponent]
    have h2 : 1 ≤ h.natDegree := hirr.natDegree_pos
    nlinarith
  have h2 : 1 ≤ finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) := by
    have hne' : primaryComponent x.toLinearMap (reciprocalPolynomial h) ≠ ⊥ :=
      primaryComponent_ne_bot hx.squarefree_minpoly hh'
    have : Nontrivial (primaryComponent x.toLinearMap (reciprocalPolynomial h)) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne'
    exact Module.finrank_pos
  rw [orbitSpace, hfin]
  omega
omit [CharP K 2] in
private theorem three_le_finrank_orbitSpace {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    3 ≤ finrank K (orbitSpace x.toLinearMap h) := by
  by_cases hself : h = reciprocalPolynomial h
  · rw [orbitSpace, ← hself, sup_idem]
    exact three_le_finrank_primaryComponent_of_selfdual hx hp hp2 hh hne1 hself hm
  · exact three_le_finrank_orbitSpace_of_paired hx hh hm hself
private theorem exists_two_pieces_in_orbitSpace (hQ : (polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity (F.ι s).toLinearMap h) :
    ∃ i j, i ≠ j ∧ F.U i ≤ orbitSpace (F.ι s).toLinearMap h ∧
      F.U j ≤ orbitSpace (F.ι s).toLinearMap h := by
  have hx := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have h3 := three_le_finrank_orbitSpace hx hp hp2 hh hne1 hm
  have hex : ∃ i, F.U i ≤ orbitSpace (F.ι s).toLinearMap h := by
    by_contra hcon
    push Not at hcon
    have hbot := orbitSpace_eq_bot_of_forall_not_le hQ hp hp2 hEΩ F hU s hh hne1 hcon
    rw [hbot] at h3
    simp at h3
  obtain ⟨i, hi⟩ := hex
  have hex' : ∃ j, j ≠ i ∧ F.U j ≤ orbitSpace (F.ι s).toLinearMap h := by
    by_contra hcon
    push Not at hcon
    have hle := orbitSpace_le_piece_of_unique hQ hp hp2 hEΩ F hU s hh hne1 hi hcon
    have h2 : finrank K (orbitSpace (F.ι s).toLinearMap h) ≤ 2 := by
      calc finrank K (orbitSpace (F.ι s).toLinearMap h) ≤ finrank K (F.U i) :=
            Submodule.finrank_mono hle
        _ = 2 := hU i
    omega
  obtain ⟨j, hji, hj⟩ := hex'
  exact ⟨i, j, hji.symm, hi, hj⟩
omit [Finite K] [CharP K 2] in
private theorem mem_supportedBlock_of_forall_polar_eq_zero (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) (hx : OddOrderIsometry Q p (F.ι s)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap)
    {k : Fin r} {z : V ≃ₗ[K] V} (hzΩ : z ∈ orthDerived Q)
    (hzE : ∀ c ∈ E, z * c = c * z)
    (hzFix : ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    (hk : F.U k ≤ orbitSpace (F.ι s).toLinearMap h) :
    z ∈ supportedBlock Q (F.ι s) h := by
  have hzIso : z ∈ isometryCentralizer Q (F.ι s) := by
    refine mem_isometryCentralizer.mpr ⟨?_, ?_⟩
    · intro v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup hzΩ) v
    · intro v
      exact congrArg (fun g : V ≃ₗ[K] V => g v) (hzE (F.ι s) (F.mem s))
  refine mem_supportedBlock.mpr ⟨hzIso, fun r hr => ?_⟩
  exact hzFix r fun u hu => hx.polar_orbit_others hh (hk hu) hr
omit [Finite K] [CharP K 2] in
private theorem pow_eq_one_of_pow_mul_eq_one (F : SevOm.Frame Q p E r) {i j : Fin r}
    (hij : i ≠ j) {zi zj : V ≃ₗ[K] V}
    (hziFix : ∀ v, (∀ u ∈ F.U i, polar Q u v = 0) → zi v = v)
    (hzjFix : ∀ v, (∀ u ∈ F.U j, polar Q u v = 0) → zj v = v)
    {a b : ℕ} (hab : zi ^ a * zj ^ b = 1) : zi ^ a = 1 := by
  ext w
  obtain ⟨u0, hu0, w0, hw0, huw⟩ :=
    exists_add_of_isCompl (SevOmSmall.isCompl_orthogonal (F.nondeg i)) w
  rw [← huw, map_add]
  have hfix_i : (zi ^ a) u0 = u0 := by
    have hzj_u : zj u0 = u0 := by
      refine hzjFix u0 fun u' hu' => ?_
      rw [polar_comm]
      exact F.orth i j hij u0 hu0 u' hu'
    have hzj_pow : ∀ n : ℕ, (zj ^ n) u0 = u0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hzj_u]
    have h2 : (zi ^ a * zj ^ b) u0 = u0 := by rw [hab]; rfl
    rw [LinearEquiv.mul_apply, hzj_pow b] at h2
    exact h2
  have hfix_perp : ∀ n : ℕ, (zi ^ n) w0 = w0 := by
    intro n
    have hw0' : ∀ u' ∈ F.U i, polar Q u' w0 = 0 :=
      fun u' hu' => SevOmSmall.mem_orthogonal_polar.mp hw0 u' hu'
    have hzi_w : zi w0 = w0 := hziFix w0 hw0'
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hzi_w]
  change (zi ^ a) u0 + (zi ^ a) w0 = u0 + w0
  rw [hfix_i, hfix_perp a]
omit [CharP K 2] in
private theorem isCyclic_blockDet_closure (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap)
    (u v : ↥(supportedBlock Q (F.ι s) h)) :
    IsCyclic ↥(Subgroup.closure ({(blockDet Q (F.ι s) h).toHomUnits u,
      (blockDet Q (F.ι s) h).toHomUnits v} : Set (AdjoinRoot h)ˣ)) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  infer_instance
omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
private theorem exists_mem_of_pow_mul_pow_mem_ker (F : SevOm.Frame Q p E r)
    (s : Multiplicative (Fin r → ZMod p)) {e : ℕ} {J : Subgroup (V ≃ₗ[K] V)} {h : K[X]}
    (hJeq : J = specialBlock Q (F.ι s) h)
    {u v : ↥(supportedBlock Q (F.ι s) h)} {a b : ℕ}
    (hprod : (blockDet Q (F.ι s) h).toHomUnits (u ^ a * v ^ b) = 1)
    (hord : orderOf (u ^ a * v ^ b) = p ^ e)
    (hE : ∀ c ∈ E, (u ^ a * v ^ b : V ≃ₗ[K] V) * c = c * (u ^ a * v ^ b : V ≃ₗ[K] V)) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  refine ⟨(u ^ a * v ^ b : V ≃ₗ[K] V), ?_, hE, ?_⟩
  · rw [hJeq]
    refine mem_specialBlock.mpr ⟨(u ^ a * v ^ b).2, ?_⟩
    have h1 := congrArg Units.val hprod
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at h1
  · change orderOf (↑(u ^ a * v ^ b) : V ≃ₗ[K] V) = p ^ e
    rw [Subgroup.orderOf_coe]
    exact hord
theorem exists_mem_of_ne_X_sub_one (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hEΩ : E ≤ orthDerived Q) (F : SevOm.Frame Q p E r)
    (hU : ∀ j, finrank K (F.U j) = 2) {e : ℕ}
    (hcomm : ∀ y ∈ orthDerived Q, ∀ y' ∈ orthDerived Q, (∀ c ∈ E, y * c = c * y) →
      (∀ c ∈ E, y' * c = c * y') → (∃ k : ℕ, y ^ p ^ k = 1) → (∃ k : ℕ, y' ^ p ^ k = 1) →
      y * y' = y' * y)
    (hz : ∀ k, ∃ z ∈ orthDerived Q, (∀ c ∈ E, z * c = c * z) ∧ orderOf z = p ^ e ∧
      ∀ v, (∀ u ∈ F.U k, polar Q u v = 0) → z v = v)
    (s : Multiplicative (Fin r → ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (F.ι s).toLinearMap) (hne1 : h ≠ X - 1)
    {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (isometryCentralizer Q (F.ι s)))
    (hJh : J ≤ supportedBlock Q (F.ι s) h) :
    ∃ y ∈ J, (∀ c ∈ E, y * c = c * y) ∧ orderOf y = p ^ e := by
  classical
  have hx : OddOrderIsometry Q p (F.ι s) := F.oddOrderIsometry hQ hp2 hp hEΩ s
  have hJeq : J = specialBlock Q (F.ι s) h := SevOm.free_case hx hp hp2 hh hne1 hJ hJh
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2
  have hq : CFSG.IsQuasisimple ↥(specialBlock Q (F.ι s) h) := hJeq ▸ hJq
  have hm : 2 ≤ primaryMultiplicity (F.ι s).toLinearMap h :=
    SevOmSmall.two_le_primaryMultiplicity hx hh hq
  obtain ⟨i, j, hij, hi, hj⟩ :=
    exists_two_pieces_in_orbitSpace hQ hp hp2 hEΩ F hU s hh hne1 hm
  obtain ⟨zi, hziΩ, hziE, hziOrd, hziFix⟩ := hz i
  obtain ⟨zj, hzjΩ, hzjE, hzjOrd, hzjFix⟩ := hz j
  have hziSup := mem_supportedBlock_of_forall_polar_eq_zero F s hx hh hziΩ hziE hziFix hi
  have hzjSup := mem_supportedBlock_of_forall_polar_eq_zero F s hx hh hzjΩ hzjE hzjFix hj
  set u : ↥(supportedBlock Q (F.ι s) h) := ⟨zi, hziSup⟩ with hu_def
  set v : ↥(supportedBlock Q (F.ι s) h) := ⟨zj, hzjSup⟩ with hv_def
  have hu_ord : orderOf u = p ^ e := by rw [Subgroup.orderOf_mk]; exact hziOrd
  have hv_ord : orderOf v = p ^ e := by rw [Subgroup.orderOf_mk]; exact hzjOrd
  have hziP : ∃ k : ℕ, zi ^ p ^ k = 1 :=
    ⟨e, by rw [← hziOrd]; exact pow_orderOf_eq_one zi⟩
  have hzjP : ∃ k : ℕ, zj ^ p ^ k = 1 :=
    ⟨e, by rw [← hzjOrd]; exact pow_orderOf_eq_one zj⟩
  have huv : u * v = v * u := Subtype.ext (hcomm zi hziΩ zj hzjΩ hziE hzjE hziP hzjP)
  have hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → u ^ a = 1 := by
    intro a b hab
    have h1 : zi ^ a * zj ^ b = 1 := congrArg Subtype.val hab
    apply Subtype.ext
    exact pow_eq_one_of_pow_mul_eq_one F hij hziFix hzjFix h1
  have hcyc := isCyclic_blockDet_closure F s hh u v
  obtain ⟨a, b, hprod, hord⟩ := exists_pow_mul_pow_mem_ker hp
    (blockDet Q (F.ι s) h).toHomUnits huv hu_ord hv_ord hind hcyc
  have hE : ∀ c ∈ E, (u ^ a * v ^ b : V ≃ₗ[K] V) * c = c * (u ^ a * v ^ b : V ≃ₗ[K] V) := by
    intro c hc
    change (zi ^ a * zj ^ b) * c = c * (zi ^ a * zj ^ b)
    exact (Commute.pow_left (hziE c hc) a).mul_left (Commute.pow_left (hzjE c hc) b)
  exact exists_mem_of_pow_mul_pow_mem_ker F s hJeq hprod hord hE

end CFSG.StandardType.OrthTorusGen
