module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmMoves
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Norm
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Coord
import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses

public section

namespace CFSG.StandardType.ChoiceTwoOm.OmCoord

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)}

private noncomputable def p9SignOm_piEquiv {ι : Type} {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] (p : ∀ i, Submodule K (M i)) :
    Submodule.pi Set.univ p ≃ₗ[K] (∀ i, p i) where
  toFun x i := ⟨(x : ∀ i, M i) i, (Submodule.mem_pi.mp x.2) i (Set.mem_univ i)⟩
  invFun y := ⟨fun i => y i, by
    rw [Submodule.mem_pi]
    intro i _
    exact (y i).2⟩
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl

omit [CharP K 2] in
private lemma p9SignOm_finrank_submodule_pi {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    (p : ∀ i, Submodule K (M i)) :
    finrank K (Submodule.pi Set.univ p) = ∑ i, finrank K (p i) := by
  rw [(p9SignOm_piEquiv p).finrank_eq, Module.finrank_pi_fintype]

omit [CharP K 2] in
private lemma p9SignOm_piMap_sub_one {ι : Type} {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] (f : ∀ i, M i →ₗ[K] M i) :
    LinearMap.piMap f - LinearMap.id = LinearMap.piMap (fun i => f i - LinearMap.id) := by
  apply LinearMap.ext
  intro x
  funext i
  simp [LinearMap.piMap]

omit [CharP K 2] in
private lemma p9SignOm_range_piMap {ι : Type} {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] (f : ∀ i, M i →ₗ[K] M i) :
    LinearMap.range (LinearMap.piMap f) =
      Submodule.pi Set.univ (fun i => LinearMap.range (f i)) := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_pi]
  simp only [Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun i => hy i⟩

omit [CharP K 2] in
private lemma p9SignOm_finrank_range_piMap_sub_one {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]
    (f : ∀ i, M i →ₗ[K] M i) :
    finrank K (LinearMap.range (LinearMap.piMap f - LinearMap.id)) =
      ∑ i, finrank K (LinearMap.range (f i - LinearMap.id)) := by
  rw [p9SignOm_piMap_sub_one, p9SignOm_range_piMap, p9SignOm_finrank_submodule_pi]

private lemma p9SignOm_range_sigmaL_sub :
    LinearMap.range (((σL K : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id) =
      LinearMap.range (LinearMap.inl K K K) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    refine ⟨c.2, ?_⟩
    ext <;> simp [σL_apply, add_sub_cancel_left]
  · rintro _ ⟨a, rfl⟩
    refine ⟨(0, a), ?_⟩
    ext <;> simp [σL_apply]

private lemma p9SignOm_finrank_range_sigmaL_sub :
    finrank K (LinearMap.range
      (((σL K : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id)) = 1 := by
  rw [p9SignOm_range_sigmaL_sub,
    LinearMap.finrank_range_of_inj (by intro a b h; simpa using h), finrank_self]

private lemma p9SignOm_range_zpow_sub_eq_top {a : ZMod 3} (ha : a ≠ 0) :
    LinearMap.range (((zpow a : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id) = ⊤ := by
  rw [← LinearMap.ker_eq_bot_iff_range_eq_top, LinearMap.ker_eq_bot']
  intro x hx
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, sub_eq_zero] at hx
  exact eq_zero_of_zpow_eq a ha x hx

private lemma p9SignOm_finrank_range_zpow_sub {a : ZMod 3} (ha : a ≠ 0) :
    finrank K (LinearMap.range
      (((zpow a : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id)) = 2 := by
  rw [p9SignOm_range_zpow_sub_eq_top ha, finrank_top, finrank_K_K]

private noncomputable abbrev p9SignOm_coordLin (C : OmCoord K Q A)
    (m : Fin C.s → (K × K) ≃ₗ[K] (K × K)) :
    (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K) :=
  LinearEquiv.ofLinearMap
    (LinearMap.piMap fun i => (m i).toLinearMap)
    (LinearMap.piMap fun i => (m i).symm.toLinearMap)
    (by
      apply LinearMap.ext
      intro d
      funext i
      simp [LinearMap.piMap])
    (by
      apply LinearMap.ext
      intro d
      funext i
      simp [LinearMap.piMap])

omit [FiniteDimensional K V] in
private lemma p9SignOm_finrank_range_coordLin (C : OmCoord K Q A)
    (m : Fin C.s → (K × K) ≃ₗ[K] (K × K)) :
    finrank K (LinearMap.range ((p9SignOm_coordLin C m).toLinearMap - LinearMap.id)) =
      ∑ i, finrank K (LinearMap.range ((m i).toLinearMap - LinearMap.id)) :=
  p9SignOm_finrank_range_piMap_sub_one (fun i => (m i).toLinearMap)

omit [FiniteDimensional K V] in
private lemma p9SignOm_tor_eq_lift (C : OmCoord K Q A) (f : Fin C.s → ZMod 3) :
    C.tor f = C.lift (p9SignOm_coordLin C (fun i => zpow (f i))) := by
  apply C.ext_Φ
  intro d x
  rw [C.tor_acts, C.lift_apply]
  congr 1

private lemma p9SignOm_even_finrank_commSpace_tor (C : OmCoord K Q A)
    (f : Fin C.s → ZMod 3) : Even (finrank K (commSpace (C.tor f))) := by
  rw [p9SignOm_tor_eq_lift, C.finrank_commSpace_lift,
    p9SignOm_finrank_range_coordLin C (fun i => zpow (f i))]
  have hterm : ∀ i, finrank K (LinearMap.range
      (((zpow (f i) : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id)) =
      if f i = 0 then 0 else 2 := by
    intro i
    by_cases hi : f i = 0
    · rw [if_pos hi, hi]
      simp [zpow_zero]
    · rw [if_neg hi, p9SignOm_finrank_range_zpow_sub hi]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hsum : (∑ i, if f i = 0 then 0 else 2) =
      2 * (Finset.univ.filter fun i => f i ≠ 0).card := by
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : f i = 0 <;> simp [hi]
  rw [hsum]
  exact ⟨_, two_mul _⟩

omit [FiniteDimensional K V] in
private lemma p9SignOm_tor_mem_O (C : OmCoord K Q A) (f : Fin C.s → ZMod 3) :
    C.tor f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v
  rw [C.tor_acts, C.form, C.form]
  congr 1
  exact Finset.sum_congr rfl fun i _ => nrm_zpow (f i) (d i)

omit [FiniteDimensional K V] in
private lemma p9SignOm_tor_Φ_zero (C : OmCoord K Q A) (f : Fin C.s → ZMod 3)
    (x : C.W0) : C.tor f (C.Φ (0, x)) = C.Φ (0, x) := by
  rw [C.tor_acts]
  congr 1
  apply Prod.ext
  · show torC f (0 : Fin C.s → K × K) = 0
    funext i
    simp [torC_apply]
  · rfl

private lemma p9SignOm_tor_mem_omega (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A) (f : Fin C.s → ZMod 3) : C.tor f ∈ omegaGroup Q hQ :=
  mem_omegaGroup.mpr ⟨p9SignOm_tor_mem_O C f, p9SignOm_even_finrank_commSpace_tor C f⟩

private noncomputable abbrev p9SignOm_twistLin (C : OmCoord K Q A)
    (η : Fin C.s → Bool) : (Fin C.s → K × K) ≃ₗ[K] (Fin C.s → K × K) :=
  p9SignOm_coordLin C (fun i => sgnC K (η i))

omit [FiniteDimensional K V] in
private lemma p9SignOm_monoC_one_eq_twistLin (C : OmCoord K Q A) (η : Fin C.s → Bool) :
    monoC (1 : Equiv.Perm (Fin C.s)) η = p9SignOm_twistLin C η := by
  apply LinearEquiv.ext
  intro d
  funext i
  rfl

private lemma p9SignOm_natCast_finrank_commSpace_twist (C : OmCoord K Q A)
    (η : Fin C.s → Bool) :
    (finrank K (commSpace (C.lift (monoC 1 η))) : ZMod 2) =
      ((Finset.univ.filter fun i => η i = true).card : ZMod 2) := by
  rw [show C.lift (monoC 1 η) = C.lift (p9SignOm_twistLin C η) by
    rw [p9SignOm_monoC_one_eq_twistLin C η]]
  rw [C.finrank_commSpace_lift,
    p9SignOm_finrank_range_coordLin C (fun i => sgnC K (η i))]
  have hterm : ∀ i, finrank K (LinearMap.range
      (((sgnC K (η i) : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id)) =
      if η i = true then 1 else 0 := by
    intro i
    cases h : η i
    · have hf : (sgnC K false : (K × K) ≃ₗ[K] (K × K)) = 1 := rfl
      have hzero : ((sgnC K false : (K × K) ≃ₗ[K] (K × K)).toLinearMap) - LinearMap.id =
          (0 : (K × K) →ₗ[K] (K × K)) := by
        rw [hf, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self]
      rw [hzero, LinearMap.range_zero, finrank_bot]
      simp
    · have ht : (sgnC K true : (K × K) ≃ₗ[K] (K × K)) = σL K := rfl
      rw [ht, p9SignOm_finrank_range_sigmaL_sub]
      simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hsum : (∑ i, if η i = true then 1 else 0) =
      (Finset.univ.filter fun i => η i = true).card := by
    rw [Finset.card_filter]
  rw [hsum]

private lemma p9SignOm_natCast_finrank_commSpace_move_false
    (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A)
    (π : Equiv.Perm (Fin C.s)) :
    (finrank K (commSpace (C.move π (fun _ => false))) : ZMod 2) = 0 := by
  induction π using Equiv.Perm.swap_induction_on with
  | one =>
    rw [show C.move 1 (fun _ => false) = 1 by
      rw [move, monoC_one_false, C.lift_one]]
    exact natCast_finrank_commSpace_one
  | swap_mul f x y hxy ih =>
    have hmul : C.move (Equiv.swap x y * f) (fun _ => false) =
        C.move f (fun _ => false) * C.move (Equiv.swap x y) (fun _ => false) := by
      calc C.move (Equiv.swap x y * f) (fun _ => false)
          = C.lift (monoC (Equiv.swap x y * f) (fun _ => false)) := rfl
        _ = C.lift (monoC f (fun _ => false) *
              monoC (Equiv.swap x y) (fun _ => false)) := by
            rw [monoC_mul_false (π := f) (π' := Equiv.swap x y)]
        _ = C.lift (monoC f (fun _ => false)) *
              C.lift (monoC (Equiv.swap x y) (fun _ => false)) := C.lift_mul _ _
        _ = C.move f (fun _ => false) * C.move (Equiv.swap x y) (fun _ => false) := rfl
    have hswap : (finrank K (commSpace (C.move (Equiv.swap x y) (fun _ => false))) :
        ZMod 2) = 0 := by
      rw [move, C.finrank_commSpace_lift, range_swap_sub hxy,
        LinearMap.finrank_range_of_inj (twoPlanes_injective (K := K) hxy), finrank_K_K]
      exact Nat.cast_zero
    rw [hmul, natCast_finrank_commSpace_mul hQ (C.move_mem_O f _) (C.move_mem_O _ _)]
    rw [ih, hswap, add_zero]

private lemma p9SignOm_natCast_finrank_commSpace_move
    (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A)
    (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool) :
    (finrank K (commSpace (C.move π η)) : ZMod 2) =
      ((Finset.univ.filter fun i => η i = true).card : ZMod 2) := by
  have hmul : C.move π η = C.lift (monoC 1 η) * C.move π (fun _ => false) := by
    calc C.move π η = C.lift (monoC π η) := rfl
      _ = C.lift (monoC 1 η * monoC π (fun _ => false)) := by rw [monoC_eq_mul]
      _ = C.lift (monoC 1 η) * C.lift (monoC π (fun _ => false)) := C.lift_mul _ _
      _ = C.lift (monoC 1 η) * C.move π (fun _ => false) := rfl
  rw [hmul, natCast_finrank_commSpace_mul hQ (C.lift_isom (nrm_monoC 1 η))
    (C.move_mem_O π (fun _ => false))]
  rw [p9SignOm_natCast_finrank_commSpace_twist,
    p9SignOm_natCast_finrank_commSpace_move_false hQ C π, add_zero]

omit [FiniteDimensional K V] in
private lemma p9SignOm_eq_zero_of_W0_eq_bot (C : OmCoord K Q A) (hW0 : C.W0 = ⊥)
    (x : C.W0) : x = 0 := by
  apply Subtype.ext
  have hx : (x : V) ∈ (⊥ : Submodule K V) := hW0 ▸ x.2
  simpa using hx

omit [FiniteDimensional K V] in
private lemma p9SignOm_polar_plane (C : OmCoord K Q A) {x : C.W0} {u : V}
    (hu : u = C.Φ (0, x)) (d : Fin C.s → K × K) : polar Q u (C.Φ (d, 0)) = 0 := by
  have hdec : C.Φ (d, x) = C.Φ (d, (0 : C.W0)) + u := by
    rw [hu, ← map_add]
    congr 1
    ext <;> simp
  have hQadd : Q (C.Φ (d, x)) = Q (C.Φ (d, (0 : C.W0))) + Q u +
      polar Q (C.Φ (d, (0 : C.W0))) u := by
    rw [hdec]
    exact QuadraticMap.map_add (⇑Q) _ _
  have h0 : Q (C.Φ (d, (0 : C.W0))) = ∑ i, nrm (d i) := by
    rw [C.form]
    simp [nrm]
  have hux : Q u = Q (x : V) := by
    rw [hu]
    simpa [nrm] using C.form 0 x
  rw [h0, hux, C.form d x] at hQadd
  have hzero : (∑ i, nrm (d i)) + Q (x : V) + 0 =
      (∑ i, nrm (d i)) + Q (x : V) + polar Q (C.Φ (d, (0 : C.W0))) u := by
    rw [add_zero]
    exact hQadd
  rw [polar_comm]
  exact (add_left_cancel hzero).symm

omit [FiniteDimensional K V] in
private lemma p9SignOm_polar_W0 (C : OmCoord K Q A) {x : C.W0} {u : V}
    (hu : u = C.Φ (0, x)) (hQ0 : ∀ z : C.W0, Q (z : V) = 0) (huQ : Q u = 0)
    (y : C.W0) : polar Q u (C.Φ (0, y)) = 0 := by
  have huy : u + C.Φ (0, y) = C.Φ (0, x + y) := by
    rw [hu, ← map_add]
    congr 1
    ext <;> simp
  have hQadd : Q (u + C.Φ (0, y)) = Q u + Q (C.Φ (0, y)) +
      polar Q u (C.Φ (0, y)) := QuadraticMap.map_add (⇑Q) u _
  have h0 : Q (C.Φ (0, y)) = 0 := by
    rw [C.form, hQ0 y]
    simp [nrm]
  have h1 : Q (u + C.Φ (0, y)) = 0 := by
    rw [huy, C.form, hQ0 (x + y)]
    simp [nrm]
  simpa [h0, h1, huQ] using hQadd.symm

omit [FiniteDimensional K V] in
private lemma p9SignOm_exists_Q_ne_zero_of_W0_ne_bot (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A) (hW0 : C.W0 ≠ ⊥) : ∃ x : C.W0, Q (x : V) ≠ 0 := by
  by_contra hcon
  have hQ0 : ∀ x : C.W0, Q (x : V) = 0 := fun x => by
    by_contra hx
    exact hcon ⟨x, hx⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff C.W0).mp hW0
  set x : C.W0 := ⟨y, hy⟩ with hx
  have hx0 : x ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  set u : V := C.Φ (0, x) with hu
  have hu0 : u ≠ 0 := by
    intro h
    apply hx0
    have hp : ((0 : Fin C.s → K × K), x) = 0 := by
      apply C.Φ.injective
      rw [map_zero, ← hu]
      exact h
    exact congrArg Prod.snd hp
  have huQ : Q u = 0 := by
    rw [hu, C.form, hQ0 x]
    simp [nrm]
  have horall : ∀ v, polar Q u v = 0 := by
    intro v
    obtain ⟨⟨d, z⟩, rfl⟩ := C.Φ.surjective v
    have hdec : C.Φ (d, z) = C.Φ (d, (0 : C.W0)) + C.Φ (0, z) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    rw [hdec, polar_add_right, p9SignOm_polar_plane C hu d,
      p9SignOm_polar_W0 C hu hQ0 huQ z, add_zero]
  exact hu0 (hQ.1 u fun v => by rw [polarBilin_apply_apply]; exact horall v)

omit [FiniteDimensional K V] in
private lemma p9SignOm_exists_moveExp_of_conj_tor (C : OmCoord K Q A)
    {g : V ≃ₗ[K] V} {φ : (Fin C.s → ZMod 3) → (Fin C.s → ZMod 3)}
    (hφ : ∀ f, g * C.tor f * g⁻¹ = C.tor (φ f)) :
    ∃ (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool),
      φ = ChoiceTwo.moveExp π η := by
  have hg : ∀ c ∈ A, g * c * g⁻¹ ∈ A := by
    intro c hc
    obtain ⟨f, rfl⟩ := C.mem_tor c hc
    rw [hφ f]
    exact C.tor_mem (φ f)
  obtain ⟨π, η, hgh⟩ := exists_moveExp_of_conj C hg
  refine ⟨π, η, ?_⟩
  funext f
  exact (C.tor_injective ((hgh f).symm.trans (hφ f))).symm

private lemma p9SignOm_even_card_of_mem_omega_conj (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A) (hW0 : C.W0 = ⊥)
    {g : V ≃ₗ[K] V} (hg : g ∈ omegaGroup Q hQ) {π : Equiv.Perm (Fin C.s)}
    {η : Fin C.s → Bool} (hgh : ∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f)) :
    Even (Finset.univ.filter fun i => η i = true).card := by
  set m : V ≃ₗ[K] V := C.move π η with hm
  have hmconj : ∀ f, m * C.tor f * m⁻¹ = C.tor (ChoiceTwo.moveExp π η f) := by
    intro f
    rw [hm, C.move_conj]
    group
  have hcomm : ∀ f, (m⁻¹ * g) * C.tor f = C.tor f * (m⁻¹ * g) := by
    intro f
    have hgt : g * C.tor f = C.tor (ChoiceTwo.moveExp π η f) * g := by
      rw [← hgh f]
      group
    have hmt : m * C.tor f = C.tor (ChoiceTwo.moveExp π η f) * m := by
      rw [← hmconj f]
      group
    have hmt' : m⁻¹ * C.tor (ChoiceTwo.moveExp π η f) = C.tor f * m⁻¹ := by
      calc m⁻¹ * C.tor (ChoiceTwo.moveExp π η f)
          = m⁻¹ * (C.tor (ChoiceTwo.moveExp π η f) * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * C.tor f) * m⁻¹ := by rw [← hmt]
        _ = C.tor f * m⁻¹ := by group
    calc (m⁻¹ * g) * C.tor f = m⁻¹ * (g * C.tor f) := by group
      _ = m⁻¹ * (C.tor (ChoiceTwo.moveExp π η f) * g) := by rw [hgt]
      _ = (m⁻¹ * C.tor (ChoiceTwo.moveExp π η f)) * g := by group
      _ = (C.tor f * m⁻¹) * g := by rw [hmt']
      _ = C.tor f * (m⁻¹ * g) := by group
  obtain ⟨f₀, m₀, hm₀⟩ := exists_torC_of_commute hK C hcomm
  have hg' : m⁻¹ * g = C.tor f₀ := by
    apply C.ext_Φ
    intro d x
    rw [hm₀ d x, C.tor_acts]
    have hx : x = 0 := p9SignOm_eq_zero_of_W0_eq_bot C hW0 x
    rw [hx, map_zero]
  have hmove : m = g * (C.tor f₀)⁻¹ := by
    have hgg : g = m * C.tor f₀ := by
      calc g = m * (m⁻¹ * g) := by group
        _ = m * C.tor f₀ := by rw [hg']
    rw [hgg]
    group
  have hmem : m ∈ omegaGroup Q hQ := by
    rw [hmove]
    exact mul_mem hg (inv_mem (p9SignOm_tor_mem_omega hQ C f₀))
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [← p9SignOm_natCast_finrank_commSpace_move hQ C π η, ZMod.natCast_eq_zero_iff_even]
  exact (mem_omegaGroup.mp hmem).2

private lemma p9SignOm_exists_move_conj_of_even (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A) (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool)
    (hη : Even (Finset.univ.filter fun i => η i = true).card) :
    ∃ g ∈ omegaGroup Q hQ, (∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f)) ∧
      ∀ d, g (C.Φ (d, 0)) = C.Φ (monoC π η d, 0) := by
  have hmem : C.move π η ∈ omegaGroup Q hQ := by
    refine mem_omegaGroup.mpr ⟨C.move_mem_O π η, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even, p9SignOm_natCast_finrank_commSpace_move hQ C π η,
      ZMod.natCast_eq_zero_iff_even]
    exact hη
  refine ⟨C.move π η, hmem, fun f => ?_, fun d => ?_⟩
  · rw [C.move_conj]
    group
  · exact C.move_apply π η d 0

private lemma p9SignOm_exists_reflection_move_conj_of_odd
    (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A) (hW0 : C.W0 ≠ ⊥)
    (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool)
    (hη : Odd (Finset.univ.filter fun i => η i = true).card) :
    ∃ g ∈ omegaGroup Q hQ, (∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f)) ∧
      ∀ d, g (C.Φ (d, 0)) = C.Φ (monoC π η d, 0) := by
  obtain ⟨x, hxQ⟩ := p9SignOm_exists_Q_ne_zero_of_W0_ne_bot hQ C hW0
  set u : V := C.Φ (0, x) with hu
  have huQ : Q u ≠ 0 := by
    rw [hu, C.form]
    simpa [nrm] using hxQ
  let hInv : Invertible (Q u) := invertibleOfNonzero huQ
  let r : V ≃ₗ[K] V := @TauCeti.QuadraticMap.reflection K V _ _ _ Q u hInv
  have hr : r = @TauCeti.QuadraticMap.reflection K V _ _ _ Q u hInv := rfl
  have hmO : C.move π η ∈ TauCeti.QuadraticMap.orthogonalGroup Q := C.move_mem_O π η
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hr]
    exact @TauCeti.QuadraticMap.reflection_mem_orthogonalGroup K V _ _ _ Q u hInv
  have hcomm : ∀ f, r * C.tor f = C.tor f * r := by
    intro f
    exact (@reflection_mul_comm K _ V _ _ Q (C.tor f) (p9SignOm_tor_mem_O C f) u hInv (by
      rw [hu]
      exact p9SignOm_tor_Φ_zero C f x)).symm
  have hpar : Even (finrank K (commSpace (r * C.move π η))) := by
    rw [← ZMod.natCast_eq_zero_iff_even,
      natCast_finrank_commSpace_mul hQ hrO hmO, hr,
      @finrank_commSpace_reflection K _ V _ _ _ Q hQ u hInv, Nat.cast_one,
      p9SignOm_natCast_finrank_commSpace_move hQ C π η,
      ZMod.natCast_eq_one_iff_odd.mpr hη]
    decide
  have hfix : ∀ d, r (C.Φ (d, 0)) = C.Φ (d, 0) := by
    intro d
    rw [hr]
    exact @TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero K V _ _ _ Q u hInv
      (C.Φ (d, 0)) (p9SignOm_polar_plane C hu d)
  have hmem : r * C.move π η ∈ omegaGroup Q hQ :=
    mem_omegaGroup.mpr ⟨mul_mem hrO hmO, hpar⟩
  refine ⟨r * C.move π η, hmem, fun f => ?_, fun d => ?_⟩
  · have hmt : C.move π η * C.tor f = C.tor (ChoiceTwo.moveExp π η f) * C.move π η :=
      C.move_conj π η f
    have hrt : r * C.tor (ChoiceTwo.moveExp π η f) = C.tor (ChoiceTwo.moveExp π η f) * r :=
      hcomm _
    calc (r * C.move π η) * C.tor f * (r * C.move π η)⁻¹
        = r * (C.move π η * C.tor f * (C.move π η)⁻¹) * r⁻¹ := by group
      _ = r * C.tor (ChoiceTwo.moveExp π η f) * r⁻¹ := by rw [hmt]; group
      _ = C.tor (ChoiceTwo.moveExp π η f) := by rw [hrt]; group
  · rw [LinearEquiv.mul_apply, C.move_apply, hfix]

theorem exists_omega_conj_iff_of_W0_eq_bot (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A) (hW0 : C.W0 = ⊥)
    (φ : (Fin C.s → ZMod 3) → (Fin C.s → ZMod 3)) :
    (∃ g ∈ omegaGroup Q hQ, ∀ f, g * C.tor f * g⁻¹ = C.tor (φ f)) ↔
      ∃ (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool),
        Even (Finset.univ.filter fun i => η i = true).card ∧ φ = ChoiceTwo.moveExp π η := by
  constructor
  · rintro ⟨g, hg, hφ⟩
    obtain ⟨π, η, hπφ⟩ := p9SignOm_exists_moveExp_of_conj_tor C hφ
    refine ⟨π, η, ?_, hπφ⟩
    exact p9SignOm_even_card_of_mem_omega_conj hK hQ C hW0 hg (by simpa only [hπφ] using hφ)
  · rintro ⟨π, η, hη, hπφ⟩
    obtain ⟨g, hg, hconj, -⟩ := p9SignOm_exists_move_conj_of_even hQ C π η hη
    exact ⟨g, hg, fun f => by rw [hπφ]; exact hconj f⟩

theorem exists_omega_conj_iff_of_W0_ne_bot (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A) (hW0 : C.W0 ≠ ⊥) (φ : (Fin C.s → ZMod 3) → (Fin C.s → ZMod 3)) :
    (∃ g ∈ omegaGroup Q hQ, ∀ f, g * C.tor f * g⁻¹ = C.tor (φ f)) ↔
      ∃ (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool), φ = ChoiceTwo.moveExp π η := by
  constructor
  · rintro ⟨g, -, hφ⟩
    exact p9SignOm_exists_moveExp_of_conj_tor C hφ
  · rintro ⟨π, η, hπφ⟩
    by_cases hη : Even (Finset.univ.filter fun i => η i = true).card
    · obtain ⟨g, hg, hconj, -⟩ := p9SignOm_exists_move_conj_of_even hQ C π η hη
      exact ⟨g, hg, fun f => by rw [hπφ]; exact hconj f⟩
    · obtain ⟨g, hg, hconj, -⟩ := p9SignOm_exists_reflection_move_conj_of_odd hQ C hW0 π η
        (Nat.not_even_iff_odd.mp hη)
      exact ⟨g, hg, fun f => by rw [hπφ]; exact hconj f⟩

theorem exists_omega_conj_moveExp_apply (hQ : (polarBilin Q).Nondegenerate) (C : OmCoord K Q A)
    (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool)
    (hη : Even (Finset.univ.filter fun i => η i = true).card ∨ C.W0 ≠ ⊥) :
    ∃ g ∈ omegaGroup Q hQ, (∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f)) ∧
      ∀ d, g (C.Φ (d, 0)) = C.Φ (monoC π η d, 0) := by
  rcases hη with hEven | hW0
  · exact p9SignOm_exists_move_conj_of_even hQ C π η hEven
  · by_cases hEven : Even (Finset.univ.filter fun i => η i = true).card
    · exact p9SignOm_exists_move_conj_of_even hQ C π η hEven
    · exact p9SignOm_exists_reflection_move_conj_of_odd hQ C hW0 π η
        (Nat.not_even_iff_odd.mp hEven)

private noncomputable abbrev p9SignOm_fixedLin (C : OmCoord K Q A) : C.W0 →ₗ[K] V :=
  C.Φ.toLinearMap ∘ₗ LinearMap.inr K (Fin C.s → K × K) C.W0

omit [FiniteDimensional K V] in
private lemma p9SignOm_fixedLin_injective (C : OmCoord K Q A) :
    Function.Injective (p9SignOm_fixedLin C) := by
  intro x y hxy
  have h : ((0 : Fin C.s → K × K), x) = (0, y) :=
    C.Φ.injective (by simpa [p9SignOm_fixedLin] using hxy)
  simpa using congrArg Prod.snd h

omit [FiniteDimensional K V] in
private lemma p9SignOm_Q_smul_add (C : OmCoord K Q A) {x y : C.W0}
    (hx0 : Q (x : V) = 0) (hy0 : Q (y : V) = 0)
    (hxy : polar Q (x : V) (y : V) = 1) (a b : K) :
    Q (((a • x + b • y : C.W0) : V)) = a * b := by
  have hco : ((a • x + b • y : C.W0) : V) = a • (x : V) + b • (y : V) := rfl
  rw [hco, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hx0, hy0, hxy]
  simp [smul_eq_mul]

omit [FiniteDimensional K V] in
private lemma p9SignOm_hyperbolic_li (C : OmCoord K Q A) {x y : C.W0}
    (hxy : polar Q (x : V) (y : V) = 1) : LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have hV : a • (x : V) + b • (y : V) = 0 := by
    have := congrArg (fun z : C.W0 => (z : V)) h
    simpa using this
  have hxx : polar Q (x : V) (x : V) = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hyy : polar Q (y : V) (y : V) = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  constructor
  · have h1 := congrArg (fun z : V => polar Q z (y : V)) hV
    rw [polar_add_left, polar_smul_left, polar_smul_left, hxy, hyy] at h1
    simpa [smul_eq_mul] using h1
  · have h2 := congrArg (fun z : V => polar Q z (x : V)) hV
    rw [polar_add_left, polar_smul_left, polar_smul_left, hxx,
      polar_comm Q (y : V) (x : V), hxy] at h2
    simpa [smul_eq_mul] using h2

private lemma p9SignOm_eq_add_of_Q_eq_one (hK : Nat.card K = 2)
    (C : OmCoord K Q A) {x y : C.W0} (hfin : finrank K C.W0 = 2)
    (hx0 : Q (x : V) = 0) (hy0 : Q (y : V) = 0)
    (hxy : polar Q (x : V) (y : V) = 1)
    {z : C.W0} (hz : Q (z : V) = 1) : z = x + y := by
  obtain ⟨u, -, hu_unique⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have hu1 : u = 1 := (hu_unique 1 one_ne_zero).symm
  have hK01 : ∀ a : K, a = 0 ∨ a = 1 := by
    intro a
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [hu_unique a ha, hu1]
  have hli : LinearIndependent K ![x, y] := p9SignOm_hyperbolic_li C hxy
  have hrange : (Set.range ![x, y] : Set C.W0) = {x, y} := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hw
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hspan2 : finrank K (Submodule.span K ({x, y} : Set C.W0)) = 2 := by
    have h := finrank_span_eq_card (R := K) (b := ![x, y]) hli
    rw [hrange, Fintype.card_fin] at h
    exact h
  have htop : Submodule.span K ({x, y} : Set C.W0) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hspan2, hfin])
  have hzspan : z ∈ Submodule.span K ({x, y} : Set C.W0) := by
    rw [htop]
    trivial
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzspan
  have hQ : a * b = 1 := by
    rw [← hab] at hz
    rwa [p9SignOm_Q_smul_add C hx0 hy0 hxy] at hz
  have ha1 : a = 1 := by
    rcases hK01 a with ha | ha
    · rw [ha, zero_mul] at hQ
      exact absurd hQ zero_ne_one
    · exact ha
  have hb1 : b = 1 := by
    rcases hK01 b with hb | hb
    · rw [hb, mul_zero] at hQ
      exact absurd hQ zero_ne_one
    · exact hb
  rw [← hab, ha1, hb1, one_smul, one_smul]

private lemma p9SignOm_fix_add_of_preserves (hK : Nat.card K = 2) (C : OmCoord K Q A)
    (hfin : finrank K C.W0 = 2) {x y : C.W0}
    (hx0 : Q (x : V) = 0) (hy0 : Q (y : V) = 0)
    (hxy : polar Q (x : V) (y : V) = 1) {m : C.W0 →ₗ[K] C.W0}
    (hmQ : ∀ z, Q ((m z : C.W0) : V) = Q (z : V)) : m (x + y) = x + y := by
  have hQxy : Q (((x + y : C.W0) : V)) = 1 := by
    simpa using p9SignOm_Q_smul_add C hx0 hy0 hxy (1 : K) (1 : K)
  refine p9SignOm_eq_add_of_Q_eq_one hK C hfin hx0 hy0 hxy (z := m (x + y)) ?_
  rw [hmQ (x + y)]
  exact hQxy

private lemma p9SignOm_map_Q_of_commute (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A) {g : V ≃ₗ[K] V} (hg : g ∈ omegaGroup Q hQ)
    {m : C.W0 →ₗ[K] C.W0} (hact : ∀ d x, g (C.Φ (d, x)) = C.Φ (d, m x))
    (z : C.W0) : Q ((m z : C.W0) : V) = Q (z : V) := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (mem_omegaGroup.mp hg).1
  have hpres := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO (C.Φ (0, z))
  rw [hact 0 z, C.form, C.form] at hpres
  simpa [nrm] using hpres

private lemma p9SignOm_finrank_range_sub_le_one (C : OmCoord K Q A)
    (hfin : finrank K C.W0 = 2) {m : C.W0 →ₗ[K] C.W0} {x y : C.W0}
    (hli : LinearIndependent K ![x, y]) (hfix : m (x + y) = x + y) :
    finrank K (LinearMap.range (m - 1)) ≤ 1 := by
  have hne : x + y ≠ 0 := by
    intro h0
    have hsum : (1 : K) • x + (1 : K) • y = 0 := by simpa using h0
    exact one_ne_zero (LinearIndependent.pair_iff.mp hli 1 1 hsum).1
  have hker : x + y ∈ LinearMap.ker (m - 1) := by
    rw [LinearMap.mem_ker]
    simp [hfix]
  have hle : 1 ≤ finrank K (LinearMap.ker (m - 1)) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    apply hne
    have hmem : x + y ∈ (⊥ : Submodule K C.W0) := by
      rw [← hbot]
      exact hker
    simpa using hmem
  have hrank := LinearMap.finrank_range_add_finrank_ker (m - 1)
  rw [hfin] at hrank
  omega

omit [FiniteDimensional K V] in
private lemma p9SignOm_commSpace_eq_map (C : OmCoord K Q A)
    {g' : V ≃ₗ[K] V} {m : C.W0 →ₗ[K] C.W0}
    (hact : ∀ d x, g' (C.Φ (d, x)) = C.Φ (d, m x)) :
    commSpace g' = (LinearMap.range (m - 1)).map (p9SignOm_fixedLin C) := by
  have hsub : ∀ d x, C.Φ (d, m x) - C.Φ (d, x) =
      p9SignOm_fixedLin C ((m - 1) x) := by
    intro d x
    rw [p9SignOm_fixedLin, LinearMap.comp_apply, LinearMap.inr_apply, ← map_sub]
    have hp : ((d, m x) - (d, x) : (Fin C.s → K × K) × C.W0) = (0, (m - 1) x) := by
      ext <;> simp [LinearMap.sub_apply]
    rw [hp]
    rfl
  apply le_antisymm
  · rintro v ⟨v₀, rfl⟩
    obtain ⟨⟨d, x⟩, rfl⟩ := C.Φ.surjective v₀
    refine ⟨(m - 1) x, ⟨x, rfl⟩, ?_⟩
    change p9SignOm_fixedLin C ((m - 1) x) = g' (C.Φ (d, x)) - C.Φ (d, x)
    rw [hact d x]
    exact (hsub d x).symm
  · rintro v ⟨w, ⟨x, rfl⟩, rfl⟩
    refine mem_commSpace.mpr ⟨C.Φ (0, x), ?_⟩
    rw [hact 0 x]
    simpa using hsub 0 x

omit [FiniteDimensional K V] in
private lemma p9SignOm_finrank_commSpace_eq (C : OmCoord K Q A)
    {g' : V ≃ₗ[K] V} {m : C.W0 →ₗ[K] C.W0}
    (hact : ∀ d x, g' (C.Φ (d, x)) = C.Φ (d, m x)) :
    finrank K (commSpace g') = finrank K (LinearMap.range (m - 1)) := by
  rw [p9SignOm_commSpace_eq_map C hact]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (p9SignOm_fixedLin C)
    (p9SignOm_fixedLin_injective C) (LinearMap.range (m - 1)))).symm

theorem mem_of_commute_tor (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A)
    (hW0 : C.W0 = ⊥ ∨
      (finrank K C.W0 = 2 ∧ ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1))
    {g : V ≃ₗ[K] V} (hg : g ∈ omegaGroup Q hQ) (hcomm : ∀ f, g * C.tor f = C.tor f * g) :
    g ∈ A := by
  classical
  obtain ⟨f₀, m, hm⟩ := exists_torC_of_commute hK C hcomm
  set g' : V ≃ₗ[K] V := (C.tor f₀)⁻¹ * g with hg'def
  have hg'Ω : g' ∈ omegaGroup Q hQ := by
    rw [hg'def]
    exact mul_mem (inv_mem (p9SignOm_tor_mem_omega hQ C f₀)) hg
  have hact : ∀ d x, g' (C.Φ (d, x)) = C.Φ (d, m x) := by
    intro d x
    have h1 : g' (C.Φ (d, x)) = (C.tor f₀)⁻¹ (C.Φ (torC f₀ d, m x)) := by
      rw [hg'def, LinearEquiv.mul_apply, hm d x]
    rw [h1]
    have hcomp : torC (-f₀) (torC f₀ d) = d := by
      rw [← torC_add, neg_add_cancel, torC_zero]
    have hinv : (C.tor f₀)⁻¹ = C.tor (-f₀) := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← C.tor_add, add_neg_cancel, C.tor_zero]
    rw [hinv, C.tor_acts, hcomp]
  have hg'1 : g' = 1 := by
    rcases hW0 with hbot | ⟨hfin, x, y, hx0, hy0, hxy⟩
    · apply C.ext_Φ
      intro d x
      rw [hact d x]
      have hx : x = 0 := p9SignOm_eq_zero_of_W0_eq_bot C hbot x
      rw [hx, map_zero]
      rfl
    · have hQxy : Q ((x + y : C.W0) : V) = 1 := by
        simpa using p9SignOm_Q_smul_add C hx0 hy0 hxy (1 : K) (1 : K)
      have hli : LinearIndependent K ![x, y] := p9SignOm_hyperbolic_li C hxy
      have hfix : m (x + y) = x + y :=
        p9SignOm_fix_add_of_preserves hK C hfin hx0 hy0 hxy
          (fun z => p9SignOm_map_Q_of_commute hQ C hg'Ω hact z)
      have hle : finrank K (commSpace g') ≤ 1 := by
        rw [p9SignOm_finrank_commSpace_eq C hact]
        exact p9SignOm_finrank_range_sub_le_one C hfin hli hfix
      have hzero : finrank K (commSpace g') = 0 := by
        rcases (mem_omegaGroup.mp hg'Ω).2 with ⟨n, hn⟩
        omega
      have hbot' : commSpace g' = ⊥ := Submodule.finrank_eq_zero.mp hzero
      by_contra hne
      have hpos := one_le_finrank_commSpace hne
      rw [hbot', finrank_bot] at hpos
      omega
  have hg_eq : g = C.tor f₀ := by
    calc g = C.tor f₀ * ((C.tor f₀)⁻¹ * g) := by group
      _ = C.tor f₀ * g' := by rw [hg'def]
      _ = C.tor f₀ * 1 := by rw [hg'1]
      _ = C.tor f₀ := mul_one _
  rw [hg_eq]
  exact C.tor_mem f₀

theorem even_moveExp_iff_fixes_W0
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (C : OmCoord K Q A)
    (hW0 : C.W0 = ⊥ ∨ (finrank K C.W0 = 2 ∧
      ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1))
    {g : V ≃ₗ[K] V} (hg : g ∈ omegaGroup Q hQ)
    (π : Equiv.Perm (Fin C.s)) (η : Fin C.s → Bool)
    (hconj : ∀ f, g * C.tor f * g⁻¹ = C.tor (ChoiceTwo.moveExp π η f)) :
    Even (Finset.univ.filter fun i => η i = true).card ↔
      ∀ x : C.W0, g (C.Φ (0, x)) = C.Φ (0, x) := by
  classical
  let m : V ≃ₗ[K] V := C.move π η
  have hm_conj : ∀ f, m * C.tor f * m⁻¹ = C.tor (ChoiceTwo.moveExp π η f) := by
    intro f
    dsimp only [m]
    rw [C.move_conj]
    group
  have hfix_m : ∀ x : C.W0, m (C.Φ (0, x)) = C.Φ (0, x) := by
    intro x
    dsimp only [m]
    rw [C.move_apply, map_zero]
  let r : V ≃ₗ[K] V := m⁻¹ * g
  have hcomm_r : ∀ f, r * C.tor f = C.tor f * r := by
    intro f
    have hg' : g * C.tor f = C.tor (ChoiceTwo.moveExp π η f) * g := by
      rw [← hconj f]
      group
    have hm' : m * C.tor f = C.tor (ChoiceTwo.moveExp π η f) * m := by
      rw [← hm_conj f]
      group
    have hmt' : m⁻¹ * C.tor (ChoiceTwo.moveExp π η f) = C.tor f * m⁻¹ := by
      calc m⁻¹ * C.tor (ChoiceTwo.moveExp π η f)
          = m⁻¹ * (C.tor (ChoiceTwo.moveExp π η f) * m) * m⁻¹ := by group
        _ = m⁻¹ * (m * C.tor f) * m⁻¹ := by rw [← hm']
        _ = C.tor f * m⁻¹ := by group
    calc r * C.tor f = m⁻¹ * (g * C.tor f) := by dsimp only [r]; group
      _ = m⁻¹ * (C.tor (ChoiceTwo.moveExp π η f) * g) := by rw [hg']
      _ = (m⁻¹ * C.tor (ChoiceTwo.moveExp π η f)) * g := by group
      _ = (C.tor f * m⁻¹) * g := by rw [hmt']
      _ = C.tor f * (m⁻¹ * g) := by group
      _ = C.tor f * r := by dsimp only [r]
  constructor
  · intro hEven
    have hmΩ : m ∈ omegaGroup Q hQ := by
      refine mem_omegaGroup.mpr ⟨C.move_mem_O π η, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff_even, p9SignOm_natCast_finrank_commSpace_move hQ C π η,
        ZMod.natCast_eq_zero_iff_even]
      exact hEven
    have hrΩ : r ∈ omegaGroup Q hQ := mul_mem (inv_mem hmΩ) hg
    have hrA : r ∈ A := mem_of_commute_tor hK hQ C hW0 hrΩ hcomm_r
    obtain ⟨f₀, hf₀⟩ := C.mem_tor r hrA
    have hg_eq : g = m * r := by dsimp only [r]; group
    intro x
    calc g (C.Φ (0, x)) = m (r (C.Φ (0, x))) := by
          rw [hg_eq, LinearEquiv.mul_apply]
      _ = m (C.Φ (0, x)) := by rw [← hf₀]; exact congrArg m (p9SignOm_tor_Φ_zero C f₀ x)
      _ = C.Φ (0, x) := hfix_m x
  · intro hfix
    have hfix_r : ∀ x : C.W0, r (C.Φ (0, x)) = C.Φ (0, x) := by
      intro x
      have hm_inv_fix : m⁻¹ (C.Φ (0, x)) = C.Φ (0, x) := by
        have h := congrArg (fun v => m⁻¹ v) (hfix_m x)
        simpa using h.symm
      calc r (C.Φ (0, x)) = m⁻¹ (g (C.Φ (0, x))) := by
            dsimp only [r]
            rw [LinearEquiv.mul_apply]
        _ = m⁻¹ (C.Φ (0, x)) := by rw [hfix]
        _ = C.Φ (0, x) := hm_inv_fix
    obtain ⟨f₀, m₀, hm₀⟩ := exists_torC_of_commute hK C hcomm_r
    have hm₀_one : m₀ = 1 := by
      ext x
      have h0 := hm₀ (0 : Fin C.s → K × K) x
      have h0tor : torC f₀ (0 : Fin C.s → K × K) = 0 := by
        funext i
        simp [torC_apply]
      rw [h0tor] at h0
      have hx : C.Φ (0, x) = C.Φ (0, m₀ x) := by
        rw [← hfix_r x]
        exact h0
      simpa using (congrArg Prod.snd (C.Φ.injective hx)).symm
    have hr_eq : r = C.tor f₀ := by
      apply C.ext_Φ
      intro d x
      rw [hm₀ d x, hm₀_one, Module.End.one_apply, C.tor_acts]
    have hrΩ : r ∈ omegaGroup Q hQ := by
      rw [hr_eq]
      exact p9SignOm_tor_mem_omega hQ C f₀
    have hmΩ : m ∈ omegaGroup Q hQ := by
      have hm_eq : m = g * r⁻¹ := by dsimp only [r]; group
      rw [hm_eq]
      exact mul_mem hg (inv_mem hrΩ)
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← p9SignOm_natCast_finrank_commSpace_move hQ C π η,
      ZMod.natCast_eq_zero_iff_even]
    exact (mem_omegaGroup.mp hmΩ).2

end CFSG.StandardType.ChoiceTwoOm.OmCoord
