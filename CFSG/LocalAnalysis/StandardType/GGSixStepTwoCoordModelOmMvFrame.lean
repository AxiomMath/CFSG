module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvBasic
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace OmMv

open Module QuadraticMap Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

section Ext

variable {p r s : ℕ}

@[expose] def extC (a : Fin r → Fin s) (t : Fin r → ZMod p) : Fin s → ZMod p :=
  fun i => ∑ j, if a j = i then t j else 0

theorem extC_apply_self {a : Fin r → Fin s} (ha : Function.Injective a) (t : Fin r → ZMod p)
    (j : Fin r) : extC a t (a j) = t j := by
  unfold extC
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    exact ite_eq_right_iff.mpr fun h => absurd (ha h) hk
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem extC_apply_of_forall_ne {a : Fin r → Fin s} (t : Fin r → ZMod p) {i : Fin s}
    (hi : ∀ j, a j ≠ i) : extC a t i = 0 :=
  Finset.sum_eq_zero fun j _ => ite_eq_right_iff.mpr fun h => absurd h (hi j)

theorem extC_add (a : Fin r → Fin s) (t t' : Fin r → ZMod p) :
    extC a (t + t') = extC a t + extC a t' := by
  funext i
  simp only [extC, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem extC_zero (a : Fin r → Fin s) : extC a (0 : Fin r → ZMod p) = 0 := by
  funext i
  simp [extC]

end Ext

section Coord

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s r p : ℕ} {κ : Type} (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V)

@[expose] def blkL (i : Fin s) : D →ₗ[K] V :=
  Φ.toLinearMap ∘ₗ LinearMap.inl K (Fin s → D) (κ → K) ∘ₗ LinearMap.single K (fun _ => D) i

theorem blkL_apply (i : Fin s) (y : D) : blkL Φ i y = Φ (Pi.single i y, 0) := rfl

theorem blkL_injective (i : Fin s) : Function.Injective (blkL Φ i) := by
  intro y y' h
  rw [blkL_apply, blkL_apply] at h
  have h1 := congrArg (fun x : (Fin s → D) × (κ → K) => x.1 i) (Φ.injective h)
  simpa using h1

theorem torD_single' (c : D ≃ₗ[K] D) (t : Fin s → ZMod p) (i : Fin s) (y : D) :
    CoordSpNs.torD (κ := κ) c t (Pi.single i y, 0) = (Pi.single i ((c ^ (t i).val) y), 0) := by
  rw [CoordSpNs.torD_apply]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

variable [NeZero p] {cE : D ≃ₗ[K] D}

@[expose] def coordHom (a : Fin r → Fin s) (hcp : cE ^ p = 1) :
    Multiplicative (Fin r → ZMod p) →* (V ≃ₗ[K] V) where
  toFun t := fc Φ (CoordSpNs.torD cE (extC a (toAdd t)))
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [fc_apply, CoordSpNs.torD_apply, toAdd_one, extC_zero]
    simp
  map_mul' t t' := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [LinearEquiv.mul_apply, fc_apply, fc_apply, fc_apply, CoordSpNs.torD_apply,
      CoordSpNs.torD_apply, CoordSpNs.torD_apply, toAdd_mul, extC_add]
    congr 2
    funext i
    rw [Pi.add_apply, CoordSL.pow_val_add hcp, LinearEquiv.mul_apply]

theorem coordHom_apply (a : Fin r → Fin s) (hcp : cE ^ p = 1) (t : Fin r → ZMod p)
    (d : Fin s → D) (w : κ → K) :
    coordHom Φ a hcp (ofAdd t) (Φ (d, w)) = Φ (fun i => (cE ^ (extC a t i).val) (d i), w) := by
  change fc Φ (CoordSpNs.torD (κ := κ) cE (extC a t)) (Φ (d, w)) = _
  rw [fc_apply, CoordSpNs.torD_apply]

theorem coordHom_single {a : Fin r → Fin s} (ha : Function.Injective a) (hcp : cE ^ p = 1)
    (t : Fin r → ZMod p) (j : Fin r) (y : D) :
    coordHom Φ a hcp (ofAdd t) (Φ (Pi.single (a j) y, 0)) =
      Φ (Pi.single (a j) ((cE ^ (t j).val) y), 0) := by
  change fc Φ (CoordSpNs.torD (κ := κ) cE (extC a t)) (Φ (Pi.single (a j) y, 0)) = _
  rw [fc_apply, torD_single', extC_apply_self ha]

end Coord

section Active

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s p : ℕ} {κ : Type} {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V}

@[expose] def Active (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V) (A : Subgroup (V ≃ₗ[K] V))
    (i : Fin s) : Prop :=
  ∃ b ∈ A, ∃ y : D, b (Φ (Pi.single i y, 0)) ≠ Φ (Pi.single i y, 0)

theorem orthDerived_le_O (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem powE_apply {c : D →ₗ[K] D} {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x) (m : ℕ) (x : D) :
    (cE ^ m) x = (c ^ m) x := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [CoordSpNs.pow_apply_succ, ih, hcE, pow_succ', Module.End.mul_apply]

theorem pow_fix_eq_zero [Fact p.Prime] {cE : D ≃ₗ[K] D} (hcp : cE ^ p = 1)
    (hfix : ∀ x, cE x = x → x = 0) {m : ZMod p} (hm : m ≠ 0) {y : D}
    (hy : (cE ^ m.val) y = y) : y = 0 := by
  apply hfix
  have h3 : ∀ n : ℕ, ((cE ^ m.val) ^ n) y = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [CoordSpNs.pow_apply_succ, ih, hy]
  have h4 := h3 (m⁻¹).val
  rwa [CoordSL.pow_val_pow_val hcp, mul_inv_cancel₀ hm, CoordSL.pow_val_one hcp] at h4

theorem active_inv [Fact p.Prime] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)}
    (hAO : ∀ b ∈ A, b ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : D →ₗ[K] D}
    {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x) (hcp : cE ^ p = 1)
    (hΦS : ∀ b ∈ A, ∃ k : Fin s → ℕ, ∀ d w, b (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w))
    {i : Fin s} (hi : Active Φ A i) (x : D) :
    Q (Φ (Pi.single i (cE x), 0)) = Q (Φ (Pi.single i x, 0)) := by
  obtain ⟨b, hb, y, hy⟩ := hi
  obtain ⟨k, hk⟩ := hΦS b hb
  have hbi : ∀ z, b (Φ (Pi.single i z, 0)) = Φ (Pi.single i ((cE ^ k i) z), 0) := by
    intro z
    rw [hk]
    congr 2
    funext i'
    by_cases hi' : i' = i
    · subst hi'
      rw [Pi.single_eq_same, Pi.single_eq_same, powE_apply hcE]
    · rw [Pi.single_eq_of_ne hi', Pi.single_eq_of_ne hi', map_zero]
  have hk0 : ((k i : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := (ZMod.natCast_eq_zero_iff (k i) p).mp h0
    apply hy
    rw [hbi, hn, pow_mul, hcp, one_pow]
    rfl
  have hinv : ∀ z, Q (Φ (Pi.single i ((cE ^ k i) z), 0)) = Q (Φ (Pi.single i z, 0)) := by
    intro z
    rw [← hbi]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hAO b hb) _
  have hpow : (cE ^ k i) ^ ((k i : ZMod p)⁻¹).val = cE := by
    have h1 := CoordSL.pow_val_pow_val hcp ((k i : ℕ) : ZMod p) ((k i : ZMod p)⁻¹)
    rwa [mul_inv_cancel₀ hk0, CoordSL.pow_val_one hcp, ZMod.val_natCast,
      ← pow_eq_pow_mod _ hcp] at h1
  rw [← hpow]
  exact blockQ_pow hinv _ x

end Active

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {D V : Type} [AddCommGroup D] [Module K D]
  [Nontrivial D] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {s p : ℕ} [Fact p.Prime] {κ : Type} {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V}
  {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D}

theorem exists_frame (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {c : D →ₗ[K] D} {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x) (hcp : cE ^ p = 1)
    (hfix : ∀ x, c x = x → x = 0) (hωnd : ω.Nondegenerate)
    (hΦS : ∀ b ∈ A, ∃ k : Fin s → ℕ, ∀ d w, b (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w))
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w'))) :
    ∃ (r : ℕ) (a : Fin r → Fin s) (F : SevOm.Frame Q p A r), Function.Injective a ∧
      F.ι = coordHom Φ a hcp ∧
      (∀ j x, Q (Φ (Pi.single (a j) (cE x), 0)) = Q (Φ (Pi.single (a j) x, 0))) ∧
      ∀ j, F.U j = LinearMap.range (blkL Φ (a j)) := by
  classical
  have hpp : p.Prime := Fact.out
  have hAO : ∀ b ∈ A, b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun b hb =>
    orthDerived_le_O Q (hAΩ hb)
  have hfixE : ∀ x, cE x = x → x = 0 := fun x h => hfix x (by rw [← hcE]; exact h)
  set r := Fintype.card {i // Active Φ A i} with hr
  set e : Fin r ≃ {i // Active Φ A i} := (Fintype.equivFin _).symm with he
  set a : Fin r → Fin s := fun j => (e j).1 with hadef
  have ha : Function.Injective a := fun j j' h => e.injective (Subtype.ext h)
  have hact : ∀ j, Active Φ A (a j) := fun j => (e j).2
  have hina : ∀ i, ¬ Active Φ A i → ∀ j, a j ≠ i := fun i hi j h => hi (h ▸ hact j)
  have hsurja : ∀ i, Active Φ A i → ∃ j, a j = i := fun i hi =>
    ⟨e.symm ⟨i, hi⟩, by simp only [hadef, Equiv.apply_symm_apply]⟩
  have hblk : ∀ j x, Q (Φ (Pi.single (a j) (cE x), 0)) = Q (Φ (Pi.single (a j) x, 0)) :=
    fun j => active_inv hAO hcE hcp hΦS (hact j)
  set ι := coordHom Φ a hcp with hιdef
  have hιO : ∀ t, ι t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro t
    change fc Φ (SpNS.monoEquiv (κ := κ) 1 fun i => cE ^ (extC a (toAdd t) i).val) ∈ _
    refine quad_mono hdec 1 _ fun k x => ?_
    rw [Equiv.Perm.one_apply]
    by_cases hk : Active Φ A k
    · obtain ⟨j, rfl⟩ := hsurja k hk
      exact blockQ_pow (hblk j) _ x
    · rw [extC_apply_of_forall_ne _ (hina k hk), ZMod.val_zero, pow_zero]
      rfl
  have hAι : ∀ b ∈ A, ∃ t, ι (ofAdd t) = b := by
    intro b hb
    obtain ⟨k, hk⟩ := hΦS b hb
    refine ⟨fun j => (k (a j) : ZMod p), LinearEquiv.ext fun v => ?_⟩
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hιdef, coordHom_apply, hk]
    congr 2
    funext i
    by_cases hi : Active Φ A i
    · obtain ⟨j, rfl⟩ := hsurja i hi
      simp only [extC_apply_self ha]
      rw [ZMod.val_natCast, ← pow_eq_pow_mod _ hcp, powE_apply hcE]
    · rw [extC_apply_of_forall_ne _ (hina i hi), ZMod.val_zero, pow_zero]
      have h1 : b (Φ (Pi.single i (d i), 0)) = Φ (Pi.single i (d i), 0) := by
        by_contra hne
        exact hi ⟨b, hb, d i, hne⟩
      rw [hk] at h1
      have h2 := congrArg (fun x : (Fin s → D) × (κ → K) => x.1 i) (Φ.injective h1)
      simp only [Pi.single_eq_same] at h2
      exact h2.symm
  have hιA : ∀ t, ι t ∈ A := by
    intro t
    have hιp : ι t ^ p = 1 := by
      have ht : t ^ p = 1 := by
        apply toAdd.injective
        funext i
        simp [toAdd_pow]
      rw [← map_pow, ht, map_one]
    refine hmax _ (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
      (CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hQ (hpp.odd_of_ne_two hp2) (hιO t)
        hιp)) hιp fun b hb => ?_
    obtain ⟨t', rfl⟩ := hAι b hb
    rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨r, a, {
    ι := ι
    U := fun j => LinearMap.range (blkL Φ (a j))
    inj := ?_
    range := ?_
    ne_bot := ?_
    nondeg := ?_
    orth := ?_
    mapsTo := ?_
    triv := ?_
    fpf := ?_
    fix := ?_ }, ha, rfl, hblk, fun j => rfl⟩
  ·
    rw [injective_iff_map_eq_one]
    intro t ht
    apply toAdd.injective
    funext j
    rw [toAdd_one, Pi.zero_apply]
    by_contra hne
    obtain ⟨y, hy⟩ := exists_ne (0 : D)
    have h1 : coordHom Φ a hcp (ofAdd (toAdd t)) (Φ (Pi.single (a j) y, 0)) =
        Φ (Pi.single (a j) y, 0) := LinearEquiv.congr_fun ht _
    rw [coordHom_single Φ ha hcp] at h1
    exact hy (pow_fix_eq_zero hcp hfixE hne (blkL_injective Φ (a j) h1))
  ·
    refine le_antisymm ?_ fun b hb => ?_
    · rintro _ ⟨t, rfl⟩
      exact hιA t
    · obtain ⟨t, ht⟩ := hAι b hb
      exact ⟨ofAdd t, ht⟩
  ·
    intro j h
    obtain ⟨y, hy⟩ := exists_ne (0 : D)
    have h1 : blkL Φ (a j) y ∈ LinearMap.range (blkL Φ (a j)) := LinearMap.mem_range_self _ y
    rw [h, Submodule.mem_bot] at h1
    exact hy (blkL_injective Φ (a j) (h1.trans (map_zero _).symm))
  ·
    rintro j _ ⟨y, rfl⟩ h
    have hy : y = 0 := hωnd.2 y fun y' => by
      have h1 := h (blkL Φ (a j) y') (LinearMap.mem_range_self _ y')
      rwa [blkL_apply, blkL_apply, polar_frame_single hdec, Pi.single_eq_same] at h1
    rw [hy, map_zero]
  ·
    rintro j j' hjj _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [blkL_apply, blkL_apply, polar_frame_single hdec,
      Pi.single_eq_of_ne fun h => hjj (ha h), map_zero]
  ·
    rintro t j _ ⟨y, rfl⟩
    exact ⟨(cE ^ (toAdd t j).val) y, (coordHom_single Φ ha hcp (toAdd t) j y).symm⟩
  ·
    rintro t j hj _ ⟨y, rfl⟩
    have h1 := coordHom_single Φ ha hcp (toAdd t) j y
    rw [hj, ZMod.val_zero, pow_zero] at h1
    exact h1
  ·
    rintro t j hj _ ⟨y, rfl⟩ h
    have h1 : coordHom Φ a hcp (ofAdd (toAdd t)) (Φ (Pi.single (a j) y, 0)) =
        Φ (Pi.single (a j) y, 0) := h
    rw [coordHom_single Φ ha hcp] at h1
    rw [pow_fix_eq_zero hcp hfixE hj (blkL_injective Φ (a j) h1), map_zero]
  ·
    intro t v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    have hι' : ι t (Φ (d, w)) = Φ (fun i => (cE ^ (extC a (toAdd t) i).val) (d i), w) :=
      coordHom_apply Φ a hcp (toAdd t) d w
    rw [hι', Φ.injective.eq_iff, Prod.mk.injEq, and_iff_left rfl, funext_iff]
    constructor
    · rintro h j hj _ ⟨y, rfl⟩
      have h1 := h (a j)
      rw [extC_apply_self ha] at h1
      rw [blkL_apply, polar_frame_single hdec, pow_fix_eq_zero hcp hfixE hj h1, map_zero]
    · intro h i
      by_cases hi : Active Φ A i
      · obtain ⟨j, rfl⟩ := hsurja i hi
        rw [extC_apply_self ha]
        by_cases hj : toAdd t j = 0
        · rw [hj, ZMod.val_zero, pow_zero]
          rfl
        · have h0 : d (a j) = 0 := hωnd.2 _ fun y => by
            have h1 := h j hj (blkL Φ (a j) y) (LinearMap.mem_range_self _ y)
            rwa [blkL_apply, polar_frame_single hdec] at h1
          rw [h0, map_zero]
      · rw [extC_apply_of_forall_ne _ (hina i hi), ZMod.val_zero, pow_zero]
        rfl

end Frame

end OmMv

end CFSG.StandardType
