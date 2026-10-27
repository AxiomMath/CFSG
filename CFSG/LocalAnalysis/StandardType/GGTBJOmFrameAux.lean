module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OmMv

open CFSG.RankThree.Classical2 (orthDerived)

section FrameExposed

theorem ggTBJomF_exists_frame {K : Type} [Field K] [Finite K] [CharP K 2] {D V : Type}
    [AddCommGroup D] [Module K D] [Nontrivial D] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {s p : ℕ} [Fact p.Prime] {κ : Type}
    {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V} {Q : QuadraticForm K V}
    {ω : LinearMap.BilinForm K D} (hQ : (polarBilin Q).Nondegenerate)
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
      (∀ j, F.U j = LinearMap.range (blkL Φ (a j))) ∧
      ∀ j x, Q (Φ (Prod.mk (Pi.single (a j) (cE x)) 0)) =
        Q (Φ (Prod.mk (Pi.single (a j) x) 0)) := by
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
  have hblk : ∀ j x, Q (Φ (Prod.mk (Pi.single (a j) (cE x)) 0)) =
      Q (Φ (Prod.mk (Pi.single (a j) x) 0)) :=
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
      have h1 : b (Φ (Prod.mk (Pi.single i (d i)) 0)) = Φ (Prod.mk (Pi.single i (d i)) 0) := by
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
    fix := ?_ }, ha, rfl, fun j => rfl, hblk⟩
  ·
    rw [injective_iff_map_eq_one]
    intro t ht
    apply toAdd.injective
    funext j
    rw [toAdd_one, Pi.zero_apply]
    by_contra hne
    obtain ⟨y, hy⟩ := exists_ne (0 : D)
    have h1 : coordHom Φ a hcp (ofAdd (toAdd t)) (Φ (Prod.mk (Pi.single (a j) y) 0)) =
        Φ (Prod.mk (Pi.single (a j) y) 0) := LinearEquiv.congr_fun ht _
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
    have h1 : coordHom Φ a hcp (ofAdd (toAdd t)) (Φ (Prod.mk (Pi.single (a j) y) 0)) =
        Φ (Prod.mk (Pi.single (a j) y) 0) := h
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

end FrameExposed

end OmMv

namespace OrthTorus

open SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

section Blocks

theorem ggTBJomF_ofBlock {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hApow : ∀ a ∈ A, a ^ p = 1)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hne : ∃ b ∈ A, b ≠ 1) {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [Nontrivial D] {c : D →ₗ[K] D} {cE : D ≃ₗ[K] D} (hcE : ∀ x, cE x = c x) (hcp : cE ^ p = 1)
    (hD : SpNS.SpBlockExists K p D c) (hc1 : ∀ u : D, ∃ u₀, c u₀ - u₀ = u)
    (hfix : ∀ x, c x = x → x = 0) (htr : CoordSpNs.FormTransitive K D cE)
    (hO : ∀ ω : LinearMap.BilinForm K D, ω.IsAlt → ω.Nondegenerate →
      (∀ x y, ω (cE x) (cE y) = ω x y) →
        CoordSpNs.galSigns p (Nat.card K) ≤ CoordSpNs.twistGroup ω cE hcp)
    (hdim : finrank K D = 2)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (cE x) = (cE ^ e.val) (θ x)) → e = 1 ∨ e = -1) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)) (F : SevOm.Frame Q p A r)
      (θ : Fin r → D →ₗ[K] V),
      (∀ f, τ f = F.ι (piMul r p f)) ∧ Function.Injective τ ∧ τ.range = A ∧
      finrank K D = 2 ∧ cE ^ p = 1 ∧ (∀ u, cE u = u → u = 0) ∧
      (∃ T : D ≃ₗ[K] D, T * cE * T⁻¹ = cE⁻¹) ∧
      (∀ (e : ZMod p) (θ' : D →ₗ[K] D), Function.Injective θ' →
        (∀ x, θ' (cE x) = (cE ^ e.val) (θ' x)) → e = 1 ∨ e = -1) ∧
      (∀ j, Function.Injective (θ j)) ∧ (∀ j, LinearMap.range (θ j) = F.U j) ∧
      (∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
        F.ι s (θ j d) = θ j ((cE ^ (toAdd s j).val) d)) ∧
      (∀ g : V ≃ₗ[K] V, (∀ a ∈ A, g * a * g⁻¹ ∈ A) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
          (∀ u ∈ F.U j, polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap i j) f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
          (∀ u ∈ F.U j, polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      ((∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) → ∀ i : Fin r, ∃ w ∈ orthDerived Q,
        (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
          (∀ u : V, (∀ a ∈ A, a u = u) → polar Q u v = 0) → w v = v) ∧
        ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
      (OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] → ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) ∧
      (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] → ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) := by
  classical
  have hpp : p.Prime := Fact.out
  have : Finite D := Module.finite_of_finite K
  have : Finite V := Module.finite_of_finite K
  have hAO : ∀ b ∈ A, b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun b hb =>
    OmMv.orthDerived_le_O Q (hAΩ hb)
  set S : Set (Module.End K V) := {x | ∃ b ∈ A, x = (b : V →ₗ[K] V)} with hS
  have hAlt : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    change (b : V →ₗ[K] V) * b' = b' * b
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hAcomm b hb b' hb']
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [OmMv.toLinearMap_pow, hApow b hb]
    rfl
  have hSB : ∀ x ∈ S, ∀ u w, polarBilin Q (x u) (x w) = polarBilin Q u w := by
    rintro _ ⟨b, hb, rfl⟩ u w
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO b hb) u w
  have hS1 : ∃ x ∈ S, x ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    exact ⟨b, ⟨b, hb, rfl⟩, fun h => hb1 (LinearEquiv.toLinearMap_injective h)⟩
  obtain ⟨s, κ, _, Φ, ω, hωa, hωnd, hωc, hΦS, hdec⟩ := CoordSpNs.exists_normFrame hcE hD
    hpp.one_lt.le hc1 htr hAlt hQ S hSc hSp hSB hS1
  have hΦS' : ∀ b ∈ A, ∃ k : Fin s → ℕ, ∀ d w, b (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w) :=
    fun b hb => hΦS _ ⟨b, hb, rfl⟩
  obtain ⟨r, a, F, ha, hFι, hFU, hblk⟩ :=
    OmMv.ggTBJomF_exists_frame hQ hT hp2 hAΩ hmax hcE hcp hfix hωnd hΦS' hdec
  have hc1E : ∀ u, ∃ u₀, cE u₀ - u₀ = u := fun u => by
    obtain ⟨u₀, h⟩ := hc1 u
    exact ⟨u₀, by rw [hcE]; exact h⟩
  have hfixE : ∀ x, cE x = x → x = 0 := fun x h => hfix x (by rw [← hcE]; exact h)
  set τ := coordTorus Φ hcp a with hτ
  have hτF : ∀ f, τ f = F.ι (piMul r p f) := fun f => by rw [hτ, coordTorus_eq, hFι]
  have hτinj : Function.Injective τ := fun f f' h =>
    (piMul r p).injective (F.inj (by rw [← hτF, ← hτF]; exact h))
  have hτrange : τ.range = A := by
    rw [← F.range]
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨piMul r p f, (hτF f).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨(piMul r p).symm t, by rw [hτF, MulEquiv.apply_symm_apply]⟩
  have hτA : ∀ f, τ f ∈ A := fun f => hτrange ▸ ⟨f, rfl⟩
  have hτO : ∀ f, τ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hAO _ (hτA f)
  have hτiso : ∀ f v, Q (τ f v) = Q v := fun f v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hτO f) v
  set θ : Fin r → D →ₗ[K] V := fun j => OmMv.blkL Φ (a j) with hθdef
  have hθinj : ∀ j, Function.Injective (θ j) := fun j => OmMv.blkL_injective Φ (a j)
  have hθrange : ∀ j, LinearMap.range (θ j) = F.U j := fun j => by
    rw [hθdef, hFU j]
  have hintw : ∀ (s : Multiplicative (Fin r → ZMod p)) (j : Fin r) (d : D),
      F.ι s (θ j d) = θ j ((cE ^ (toAdd s j).val) d) := by
    intro s j d
    have h2 : F.ι s = OmMv.coordHom Φ a hcp (ofAdd (toAdd s)) := by
      simp only [hFι, ofAdd_toAdd]
    rw [h2]
    change OmMv.coordHom Φ a hcp (ofAdd (toAdd s)) (OmMv.blkL Φ (a j) d) =
      OmMv.blkL Φ (a j) ((cE ^ (toAdd s j).val) d)
    rw [OmMv.blkL_apply, OmMv.coordHom_single Φ ha hcp (toAdd s) j d, OmMv.blkL_apply]
  have hconjT : ∃ T : D ≃ₗ[K] D, T * cE * T⁻¹ = cE⁻¹ := by
    obtain ⟨T, hT'⟩ := CoordSpNs.mem_twistGroup.mp
      (hO ω hωa hωnd hωc (CoordSpNs.neg_one_mem_galSigns p (Nat.card K)))
    refine ⟨T, ?_⟩
    have hval : ((-1 : (ZMod p)ˣ) : ZMod p).val = p - 1 := by
      rw [Units.val_neg, Units.val_one, CoordSpNs.val_neg_one_eq hpp.one_le]
    have hpow : cE ^ (p - 1) = cE⁻¹ := by
      have h1 : cE * cE ^ (p - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hpp.one_le, hcp]
      calc cE ^ (p - 1) = 1 * cE ^ (p - 1) := (one_mul _).symm
        _ = (cE⁻¹ * cE) * cE ^ (p - 1) := by rw [inv_mul_cancel]
        _ = cE⁻¹ * (cE * cE ^ (p - 1)) := by rw [mul_assoc]
        _ = cE⁻¹ * 1 := by rw [h1]
        _ = cE⁻¹ := mul_one _
    have h1 : T * cE⁻¹ = cE * T := by
      refine LinearEquiv.ext fun x => ?_
      have hx := hT'.2 x
      rw [hval, hpow] at hx
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      exact hx
    have h4 : T * cE⁻¹ * T⁻¹ = cE := by rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    calc T * cE * T⁻¹ = (T * cE⁻¹ * T⁻¹)⁻¹ := by group
      _ = cE⁻¹ := by rw [h4]
  have hnorm : ∀ g : V ≃ₗ[K] V, (∀ b ∈ A, g * b * g⁻¹ ∈ A) →
      ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
    intro g hg
    refine coordTorus_normalizer Φ hcp hfixE hc1E ha hτinj hroots g fun f => ?_
    have h1 : g * τ f * g⁻¹ ∈ τ.range := by
      rw [hτrange]
      exact hg _ (hτA f)
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', hf'.symm⟩
  have htrans : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
      (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
        (∀ u ∈ F.U j, polar Q u v = 0) → w v = v) ∧
      ∀ f, w * τ f * w⁻¹ = τ (permAut (Equiv.swap i j) f) := by
    intro i j hij
    set w := OmMv.fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap (a i) (a j))
      fun _ => LinearEquiv.refl K D) with hw
    have hne : a i ≠ a j := fun h => hij (ha h)
    have hwΩ : w ∈ orthDerived Q := OmMv.swap_mem_orthDerived hQ hT hdec hωa hωnd hne
      (OmMv.blockQ_eq hdec hc1E (hblk i) (hblk j))
    have hcomm : ∀ t : Fin r → ZMod p, F.ι (ofAdd t) * w =
        w * F.ι (ofAdd fun k => t (Equiv.swap i j k)) := by
      intro t
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFι, hw, OmMv.fc_apply,
        SpNS.monoEquiv_apply, OmMv.coordHom_apply, OmMv.coordHom_apply, OmMv.fc_apply,
        SpNS.monoEquiv_apply]
      congr 2
      funext k
      simp only [LinearEquiv.refl_apply]
      rw [OmMv.extC_swap ha]
    have hwsupp : ∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
        (∀ u ∈ F.U j, polar Q u v = 0) → w v = v := by
      intro v hvUi hvUj
      obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
      have hdi : d (a i) = 0 := by
        refine hωnd.2 (d (a i)) fun y => ?_
        have hy : Φ (Prod.mk (Pi.single (a i) y) 0) ∈ F.U i := by rw [hFU i]; exact ⟨y, rfl⟩
        have h1 := hvUi _ hy
        rwa [OmMv.polar_frame_single hdec] at h1
      have hdj : d (a j) = 0 := by
        refine hωnd.2 (d (a j)) fun y => ?_
        have hy : Φ (Prod.mk (Pi.single (a j) y) 0) ∈ F.U j := by rw [hFU j]; exact ⟨y, rfl⟩
        have h1 := hvUj _ hy
        rwa [OmMv.polar_frame_single hdec] at h1
      rw [hw, OmMv.fc_apply, SpNS.monoEquiv_apply]
      congr 1
      refine Prod.ext (funext fun k => ?_) rfl
      simp only [LinearEquiv.refl_apply]
      by_cases hki : k = a i
      · subst hki
        rw [Equiv.swap_apply_left, hdi, hdj]
      · by_cases hkj : k = a j
        · subst hkj
          rw [Equiv.swap_apply_right, hdi, hdj]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    refine ⟨w⁻¹, inv_mem hwΩ, ?_, ?_⟩
    · intro v hvUi hvUj
      have hwv : w v = v := hwsupp v hvUi hvUj
      calc w⁻¹ v = w⁻¹ (w v) := by rw [hwv]
        _ = v := by change w.symm (w v) = v; rw [LinearEquiv.symm_apply_apply]
    · intro f
      have h := hcomm (fun k => toAdd (f k))
      have hA : F.ι (ofAdd fun k => toAdd (f k)) = τ f := by
        exact (hτF f).symm
      have hB : F.ι (ofAdd fun k => toAdd (f (Equiv.swap i j k))) =
          τ (permAut (Equiv.swap i j) f) := by
        rw [hτF, piMul_permAut]; congr 1; funext k; simp [Equiv.symm_swap]
      rw [hA, hB] at h
      rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have htwist : ∀ i : Fin r, ∃ g' : V ≃ₗ[K] V,
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) → g' v = v) ∧
      (∀ f, g' * τ f * g'⁻¹ = τ (sgnAut i f)) := by
    intro i
    obtain ⟨T, hT'⟩ := CoordSpNs.mem_twistGroup.mp
      (hO ω hωa hωnd hωc (CoordSpNs.neg_one_mem_galSigns p (Nat.card K)))
    set g := OmMv.fc Φ (SpNS.monoEquiv (κ := κ) 1
      fun k => if k = a i then T else LinearEquiv.refl K D) with hg
    have hTc : ∀ x, T (cE x) = (cE ^ ((-1 : ZMod p).val)) (T x) := by
      intro x
      have h1 := CoordSpNs.apply_pow_of_conj hcp hT'.2 (-1 : ZMod p) x
      rw [Units.val_neg, Units.val_one, neg_mul_neg, one_mul, CoordSL.pow_val_one hcp] at h1
      exact h1
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      refine OmMv.quad_mono hdec 1 _ fun k x => ?_
      show Q (Φ (Prod.mk (Pi.single k ((if k = a i then T else LinearEquiv.refl K D) x)) 0)) =
        Q (Φ (Prod.mk (Pi.single k x) 0))
      split_ifs with hk
      · rw [hk]
        exact OmMv.blockQ_twist hdec hc1E (hblk i) hT'.1 (OmMv.blockQ_pow (hblk i) _) hTc x
      · rfl
    have hcomm : ∀ t : Fin r → ZMod p, F.ι (ofAdd t) * g =
        g * F.ι (ofAdd fun k => (CoordOm.singleTw (-1 : (ZMod p)ˣ) i k : ZMod p) * t k) := by
      intro t
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFι, hg, OmMv.fc_apply,
        SpNS.monoEquiv_apply, OmMv.coordHom_apply, OmMv.coordHom_apply, OmMv.fc_apply,
        SpNS.monoEquiv_apply]
      congr 2
      funext k
      simp only [Equiv.Perm.one_apply]
      by_cases hk : k = a i
      · rw [ite_eq_left hk, hk, OmMv.extC_apply_self ha, OmMv.extC_apply_self ha, CoordOm.singleTw,
          ite_eq_left rfl]
        exact (hT'.apply_pow hcp (t i) (d (a i))).symm
      · rw [ite_eq_right hk, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
          OmMv.extC_singleTw ha (-1) t i hk]
    have hgsupp : ∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) → g v = v := by
      intro v hv
      obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
      have hdi : d (a i) = 0 := by
        refine hωnd.2 (d (a i)) fun y => ?_
        have hy : Φ (Prod.mk (Pi.single (a i) y) 0) ∈ F.U i := by rw [hFU i]; exact ⟨y, rfl⟩
        have h1 := hv _ hy
        rwa [OmMv.polar_frame_single hdec] at h1
      rw [hg, OmMv.fc_apply, SpNS.monoEquiv_apply]
      congr 1
      refine Prod.ext (funext fun k => ?_) rfl
      simp only [Equiv.Perm.one_apply]
      by_cases hk : k = a i
      · subst hk
        rw [ite_eq_left rfl, hdi, map_zero]
      · rw [ite_eq_right hk]
        simp only [LinearEquiv.refl_apply]
    refine ⟨g⁻¹, inv_mem hgO, ?_, ?_⟩
    · intro v hv
      have hgv : g v = v := hgsupp v hv
      calc g⁻¹ v = g⁻¹ (g v) := by rw [hgv]
        _ = v := by change g.symm (g v) = v; rw [LinearEquiv.symm_apply_apply]
    · intro f
      have h := hcomm (fun k => toAdd (f k))
      have hA : F.ι (ofAdd fun k => toAdd (f k)) = τ f := by
        exact (hτF f).symm
      have hB : F.ι (ofAdd fun k =>
            (CoordOm.singleTw (-1 : (ZMod p)ˣ) i k : ZMod p) * toAdd (f k)) =
          τ (sgnAut i f) := by
        rw [hτF, piMul_sgnAut]
      rw [hA, hB] at h
      rw [inv_inv, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdinv : ∀ i j : Fin r, i ≠ j → ∃ w ∈ orthDerived Q,
      (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
        (∀ u ∈ F.U j, polar Q u v = 0) → w v = v) ∧
      ∀ f, w * τ f * w⁻¹ = τ (dinv i j f) := by
    intro i j hij
    obtain ⟨g', hg'O, hg'supp, hg'conj⟩ := htwist i
    obtain ⟨w', hw'Ω, hw'supp, hw'conj⟩ := htrans i j hij
    refine ⟨g' * w' * g'⁻¹ * w'⁻¹, ?_, ?_, ?_⟩
    · refine Subgroup.commutator_mem_commutator hg'O ?_
      exact OmMv.orthDerived_le_O Q hw'Ω
    · intro v hvUi hvUj
      have hg'v : g' v = v := hg'supp v hvUi
      have hw'v : w' v = v := hw'supp v hvUi hvUj
      have hg'invv : g'⁻¹ v = v := by
        calc g'⁻¹ v = g'⁻¹ (g' v) := by rw [hg'v]
          _ = v := by change g'.symm (g' v) = v; rw [LinearEquiv.symm_apply_apply]
      have hw'invv : w'⁻¹ v = v := by
        calc w'⁻¹ v = w'⁻¹ (w' v) := by rw [hw'v]
          _ = v := by change w'.symm (w' v) = v; rw [LinearEquiv.symm_apply_apply]
      calc (g' * w' * g'⁻¹ * w'⁻¹) v
          = g' (w' (g'⁻¹ (w'⁻¹ v))) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        _ = g' (w' (g'⁻¹ v)) := by rw [hw'invv]
        _ = g' (w' v) := by rw [hg'invv]
        _ = g' v := by rw [hw'v]
        _ = v := hg'v
    · intro f
      have h1 : g' * w' * g'⁻¹ * w'⁻¹ = ⁅g', w'⁆ := by rw [commutatorElement_def]
      rw [h1]
      have h2 := OrthNs.conj_commutator_eq (τ := τ) hg'conj (OrthNs.sgnAut_sgnAut i) hw'conj
        (fun f => by rw [← MulAut.mul_apply, OrthExcEven.permAut_swap_mul_self, MulAut.one_apply]) f
      rw [h2]
      congr 1
      exact OrthNs.sgnAut_permAut_swap hij f
  have hsgn : (∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v) → ∀ i : Fin r, ∃ w ∈ orthDerived Q,
      (∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
        (∀ u : V, (∀ a ∈ A, a u = u) → polar Q u v = 0) → w v = v) ∧
      ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f) := by
    intro hfixA i
    have hδ1 : ofAdd (1 : ZMod p) ≠ 1 := by rw [Ne, ofAdd_eq_one]; exact one_ne_zero
    obtain ⟨v₀, hv₀ne, hv₀fix⟩ := hfixA
    have hmemW : v₀ ∈ fixSub Φ a := by
      have hmem : ∀ j, (Φ.symm v₀).1 (a j) = 0 := by
        intro j
        have hfixj : coordTorus Φ hcp a (Pi.mulSingle j (ofAdd (1 : ZMod p))) v₀ = v₀ :=
          hv₀fix _ (hτA _)
        have h2 := (coordTorus_apply_eq_self_iff Φ hcp hfixE ha (Pi.mulSingle j (ofAdd 1))
          (Φ.symm v₀).1 (Φ.symm v₀).2).mp (by
            rw [LinearEquiv.apply_symm_apply]
            exact hfixj)
        exact h2 j (by rw [Pi.mulSingle_eq_same]; exact hδ1)
      rw [← LinearEquiv.apply_symm_apply Φ v₀]
      exact (frame_mem_fixSub Φ a).mpr hmem
    have hW : fixSub Φ a ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.mem_bot] at hmemW
      exact hv₀ne hmemW
    obtain ⟨u, hu, hQu⟩ := RootPlaneD4.exists_quad_ne_zero (nondegOn_fixSub Φ a hQ hdec) hW
    let : Invertible (Q u) := invertibleOfNonzero hQu
    set ρ := TauCeti.QuadraticMap.reflection Q u with hρ
    have hρO : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q u
    have hufix : ∀ a ∈ A, a u = u := by
      intro a haA
      have ha' : a ∈ τ.range := by rwa [hτrange]
      obtain ⟨f, rfl⟩ := ha'
      exact coordTorus_fixSub Φ hcp hfixE ha f hu
    have hρsupp : ∀ v : V, (∀ u : V, (∀ a ∈ A, a u = u) → polar Q u v = 0) → ρ v = v :=
      fun v hv => TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q u (hv u hufix)
    have hρc : ∀ f, ρ * τ f = τ f * ρ := by
      intro f
      refine LinearEquiv.ext fun v => ?_
      have hfu := coordTorus_fixSub Φ hcp hfixE ha f hu
      have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hτO f) u v
      rw [hfu] at h1
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρ, TauCeti.QuadraticMap.reflection_apply,
        TauCeti.QuadraticMap.reflection_apply, map_sub, map_smul, hfu, h1]
    obtain ⟨g', hg'O, hg'supp, hg'conj⟩ := htwist i
    have hg'suppW : ∀ v : V, (∀ u ∈ F.U i, polar Q u v = 0) →
        (∀ u : V, (∀ a ∈ A, a u = u) → polar Q u v = 0) → g' v = v :=
      fun v hv _ => hg'supp v hv
    by_cases he : Even (finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace g'))
    · refine ⟨g', CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
        (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hg'O, he⟩), ?_, hg'conj⟩
      exact hg'suppW
    · refine ⟨g' * ρ, CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
        (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨mul_mem hg'O hρO, ?_⟩), ?_, ?_⟩
      · rw [← ZMod.natCast_eq_zero_iff_even,
          CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hg'O hρO,
          CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ u]
        have h1 : ((finrank K
            (CFSG.RankThree.OrthogonalInvolutions.commSpace g') : ℕ) : ZMod 2) ≠ 0 := by
          rwa [Ne, ZMod.natCast_eq_zero_iff_even]
        have key : ∀ x : ZMod 2, x ≠ 0 → x + ((1 : ℕ) : ZMod 2) = 0 := by decide
        exact key _ h1
      · intro v hvUi hvW
        calc (g' * ρ) v = g' (ρ v) := LinearEquiv.mul_apply g' ρ v
          _ = g' v := by rw [hρsupp v hvW]
          _ = v := hg'suppW v hvUi hvW
      · intro f
        rw [show g' * ρ * τ f * (g' * ρ)⁻¹ = g' * (ρ * τ f * ρ⁻¹) * g'⁻¹ by group]
        rw [show ρ * τ f * ρ⁻¹ = τ f by rw [hρc f]; group]
        exact hg'conj f
  have htop := charSum_top_eq Φ a hdec (Q := Q)
  have hact := charSum_actSub_modEq Φ hcp hfixE ha hτiso
  have hr : 0 < r := by
    obtain ⟨b, hb, hb1⟩ := hne
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      rw [← hτrange] at hb
      obtain ⟨f, rfl⟩ := hb
      exact absurd (by rw [show f = 1 from funext fun i => i.elim0, map_one]) hb1
    · exact hr0
  have hone : ¬ (1 ≡ (-1 : ℤ) [ZMOD p]) := by
    intro h
    have h2 : (p : ℤ) ∣ 2 := by
      have h2' := Int.modEq_iff_dvd.mp h.symm
      simpa using h2'
    have h4 : p ∣ 2 := by exact_mod_cast h2
    have h5 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h4
    exact hp2 h5
  have hchar1 : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] → ∀ v : V, (∀ a ∈ A, a v = v) → v = 0 := by
    intro h1 v hv
    by_contra hv0
    have hδ1 : ofAdd (1 : ZMod p) ≠ 1 := by rw [Ne, ofAdd_eq_one]; exact one_ne_zero
    have hvW : v ∈ fixSub Φ a := by
      have hmem : ∀ j, (Φ.symm v).1 (a j) = 0 := by
        intro j
        have hfixj : coordTorus Φ hcp a (Pi.mulSingle j (ofAdd (1 : ZMod p))) v = v :=
          hv _ (hτA _)
        have h2 := (coordTorus_apply_eq_self_iff Φ hcp hfixE ha (Pi.mulSingle j (ofAdd 1))
          (Φ.symm v).1 (Φ.symm v).2).mp (by
            rw [LinearEquiv.apply_symm_apply]
            exact hfixj)
        exact h2 j (by rw [Pi.mulSingle_eq_same]; exact hδ1)
      rw [← LinearEquiv.apply_symm_apply Φ v]
      exact (frame_mem_fixSub Φ a).mpr hmem
    have hW : fixSub Φ a ≠ ⊥ := by
      intro hbot
      rw [hbot, Submodule.mem_bot] at hvW
      exact hv0 hvW
    have hneg := charSum_fixSub_modEq_neg_one Φ hcp hQ hfixE ha hdec hωnd hdim hτrange hAΩ hmax
      hτiso hr hW
    have htop1 : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] := by
      rw [htop]
      calc OrdPNsOm.charSum Q (actSub Φ a) * OrdPNsOm.charSum Q (fixSub Φ a)
          ≡ 1 * (-1) [ZMOD p] := hact.mul hneg
        _ = -1 := by ring
    exact hone (h1.symm.trans htop1)
  have hchar2 : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] → ∃ v : V, v ≠ 0 ∧ ∀ a ∈ A, a v = v := by
    intro h1
    by_cases hW : fixSub Φ a = ⊥
    · exfalso
      have htop1 : OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] := by
        rw [htop, hW, charSum_bot, mul_one]
        exact hact
      exact hone (htop1.symm.trans h1)
    · obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      refine ⟨v, hv0, fun a haA => ?_⟩
      have ha' : a ∈ τ.range := by rwa [hτrange]
      obtain ⟨f, rfl⟩ := ha'
      exact coordTorus_fixSub Φ hcp hfixE ha f hvW
  exact ⟨r, τ, F, θ, hτF, hτinj, hτrange, hdim, hcp, hfixE, hconjT, hroots, hθinj, hθrange,
    hintw, hnorm, htrans, hdinv, hsgn, hchar1, hchar2⟩

end Blocks

end OrthTorus

end CFSG.StandardType

end
