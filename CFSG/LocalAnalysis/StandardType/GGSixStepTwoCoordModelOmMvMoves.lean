module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMoves
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsBlock
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameBlock

public section

namespace CFSG.StandardType

namespace OmMv

open Module QuadraticMap Multiplicative Polynomial
open CFSG.RankThree.Classical2 (orthDerived)

section ExtMoves

variable {p r s : ℕ}

theorem extC_swap {a : Fin r → Fin s} (ha : Function.Injective a) (t : Fin r → ZMod p)
    (j j' : Fin r) (i : Fin s) :
    extC a (fun k => t (Equiv.swap j j' k)) (Equiv.swap (a j) (a j') i) = extC a t i := by
  by_cases hi : ∃ k, a k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [ha.swap_apply, extC_apply_self ha, extC_apply_self ha, Equiv.swap_apply_self]
  · push Not at hi
    have h1 : i ≠ a j := fun h => hi j h.symm
    have h2 : i ≠ a j' := fun h => hi j' h.symm
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, extC_apply_of_forall_ne _ hi,
      extC_apply_of_forall_ne _ hi]

theorem extC_singleTw {a : Fin r → Fin s} (ha : Function.Injective a) (u : (ZMod p)ˣ)
    (t : Fin r → ZMod p) (j : Fin r) {i : Fin s} (hi : i ≠ a j) :
    extC a (fun k => (CoordOm.singleTw u j k : ZMod p) * t k) i = extC a t i := by
  by_cases hi' : ∃ k, a k = i
  · obtain ⟨k, rfl⟩ := hi'
    have hk : k ≠ j := fun h => hi (h ▸ rfl)
    rw [extC_apply_self ha, extC_apply_self ha, CoordOm.singleTw, ite_eq_right hk, Units.val_one,
      one_mul]
  · push Not at hi'
    rw [extC_apply_of_forall_ne _ hi', extC_apply_of_forall_ne _ hi']

end ExtMoves

section Moves

variable {K : Type} [Field K] [Finite K] [CharP K 2] {D V : Type} [AddCommGroup D] [Module K D]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {s r p : ℕ} [NeZero p] {κ : Type} {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V}
  {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D} {A : Subgroup (V ≃ₗ[K] V)}
  {cE : D ≃ₗ[K] D} {a : Fin r → Fin s}

theorem realizedIn_swap [FiniteDimensional K D] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωa : ω.IsAlt) (hωnd : ω.Nondegenerate) (hcp : cE ^ p = 1)
    (hc1 : ∀ u, ∃ u₀, cE u₀ - u₀ = u) (ha : Function.Injective a) (F : SevOm.Frame Q p A r)
    (hFι : F.ι = coordHom Φ a hcp)
    (hblk : ∀ j x, Q (Φ (Pi.single (a j) (cE x), 0)) = Q (Φ (Pi.single (a j) x, 0)))
    {j j' : Fin r} (hjj : j ≠ j') :
    CoordOm.RealizedIn F (orthDerived Q) (Equiv.swap j j') 1 := by
  set w := fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap (a j) (a j'))
    fun _ => LinearEquiv.refl K D) with hw
  have hne : a j ≠ a j' := fun h => hjj (ha h)
  have hwΩ : w ∈ orthDerived Q := swap_mem_orthDerived hQ hT hdec hωa hωnd hne
    (blockQ_eq hdec hc1 (hblk j) (hblk j'))
  have hcomm : ∀ t : Fin r → ZMod p,
      F.ι (ofAdd t) * w = w * F.ι (ofAdd fun k => t (Equiv.swap j j' k)) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFι, hw, fc_apply, SpNS.monoEquiv_apply,
      coordHom_apply, coordHom_apply, fc_apply, SpNS.monoEquiv_apply]
    congr 2
    funext i
    simp only [LinearEquiv.refl_apply]
    rw [extC_swap ha]
  have hconj : ∀ t : Fin r → ZMod p, w⁻¹ * F.ι (ofAdd t) * w =
      F.ι (ofAdd fun k => ((1 : Fin r → (ZMod p)ˣ) k : ZMod p) * t (Equiv.swap j j' k)) := by
    intro t
    have e : (fun k => ((1 : Fin r → (ZMod p)ˣ) k : ZMod p) * t (Equiv.swap j j' k)) =
        fun k => t (Equiv.swap j j' k) := by
      funext k
      simp
    rw [e, mul_assoc, hcomm t, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hwΩ, ?_⟩, hconj⟩
  rw [← F.range]
  exact CoordSL.mem_normalizer_range_of_conj (Equiv.swap j j') 1 hconj

omit [Finite K] [FiniteDimensional K V] in
theorem realizedIn_twist
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hcp : cE ^ p = 1) (hc1 : ∀ u, ∃ u₀, cE u₀ - u₀ = u) (ha : Function.Injective a)
    (F : SevOm.Frame Q p A r) (hFι : F.ι = coordHom Φ a hcp)
    (hblk : ∀ j x, Q (Φ (Pi.single (a j) (cE x), 0)) = Q (Φ (Pi.single (a j) x, 0)))
    (j : Fin r) {u : (ZMod p)ˣ} {T : D ≃ₗ[K] D} (hT : CoordSpNs.IsTwist ω cE u T) :
    CoordOm.RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1 (CoordOm.singleTw u j) := by
  classical
  set w := fc Φ (SpNS.monoEquiv (κ := κ) 1
    fun i => if i = a j then T else LinearEquiv.refl K D) with hw
  have hTc : ∀ x, T (cE x) = (cE ^ ((u⁻¹ : (ZMod p)ˣ) : ZMod p).val) (T x) := by
    intro x
    have h1 := CoordSpNs.apply_pow_of_conj hcp hT.2 ((u⁻¹ : (ZMod p)ˣ) : ZMod p) x
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, CoordSL.pow_val_one hcp] at h1
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine quad_mono hdec 1 _ fun k x => ?_
    show Q (Φ (Pi.single k ((if k = a j then T else LinearEquiv.refl K D) x), 0)) =
      Q (Φ (Pi.single k x, 0))
    split_ifs with hk
    · rw [hk]
      exact blockQ_twist hdec hc1 (hblk j) (T := T.toLinearMap) hT.1 (blockQ_pow (hblk j) _) hTc x
    · rfl
  have hcomm : ∀ t : Fin r → ZMod p, F.ι (ofAdd t) * w =
      w * F.ι (ofAdd fun k => (CoordOm.singleTw u j k : ZMod p) * t k) := by
    intro t
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hFι, hw, fc_apply, SpNS.monoEquiv_apply,
      coordHom_apply, coordHom_apply, fc_apply, SpNS.monoEquiv_apply]
    congr 2
    funext i
    simp only [Equiv.Perm.one_apply]
    by_cases hi : i = a j
    · rw [ite_eq_left hi, hi, extC_apply_self ha, extC_apply_self ha, CoordOm.singleTw,
        ite_eq_left rfl]
      exact (hT.apply_pow hcp (t j) (d (a j))).symm
    · rw [ite_eq_right hi, LinearEquiv.refl_apply, LinearEquiv.refl_apply,
        extC_singleTw ha u t j hi]
  have hconj : ∀ t : Fin r → ZMod p, w⁻¹ * F.ι (ofAdd t) * w =
      F.ι (ofAdd fun k => (CoordOm.singleTw u j k : ZMod p) * t ((1 : Equiv.Perm (Fin r)) k)) := by
    intro t
    rw [mul_assoc, hcomm t, ← mul_assoc, inv_mul_cancel, one_mul]
    rfl
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hwO, ?_⟩, hconj⟩
  rw [← F.range]
  exact CoordSL.mem_normalizer_range_of_conj 1 (CoordOm.singleTw u j) hconj

end Moves

section Assembly

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

omit [Field K] in
theorem toLinearMap_pow {K : Type} [Field K] [Module K V] (b : V ≃ₗ[K] V) (n : ℕ) :
    (b : V →ₗ[K] V) ^ n = ((b ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, pow_succ, LinearEquiv.coe_toLinearMap_mul]

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

theorem exists_moves_of_block {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : QuadraticForm K V}
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
        CoordSpNs.galSigns p (Nat.card K) ≤ CoordSpNs.twistGroup ω cE hcp) :
    ∃ (r : ℕ) (F : SevOm.Frame Q p A r),
      (∀ i j : Fin r, i ≠ j → CoordOm.RealizedIn F (orthDerived Q) (Equiv.swap i j) 1) ∧
      ∀ (i : Fin r) (u : (ZMod p)ˣ), ((u : ZMod p) = Nat.card K ∨ (u : ZMod p) = -1) →
        CoordOm.RealizedIn F (TauCeti.QuadraticMap.orthogonalGroup Q) 1 (CoordOm.singleTw u i) := by
  classical
  have hpp : p.Prime := Fact.out
  have hAO : ∀ b ∈ A, b ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun b hb =>
    orthDerived_le_O Q (hAΩ hb)
  set S : Set (Module.End K V) := {x | ∃ b ∈ A, x = (b : V →ₗ[K] V)} with hS
  have hAlt : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hSc : ∀ x ∈ S, ∀ x' ∈ S, Commute x x' := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    change (b : V →ₗ[K] V) * b' = b' * b
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hAcomm b hb b' hb']
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [toLinearMap_pow, hApow b hb]
    rfl
  have hSB : ∀ x ∈ S, ∀ u w, polarBilin Q (x u) (x w) = polarBilin Q u w := by
    rintro _ ⟨b, hb, rfl⟩ u w
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO b hb) u w
  have hS1 : ∃ x ∈ S, x ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    refine ⟨b, ⟨b, hb, rfl⟩, fun h => hb1 (LinearEquiv.toLinearMap_injective h)⟩
  obtain ⟨s, κ, _, Φ, ω, hωa, hωnd, hωc, hΦS, hdec⟩ := CoordSpNs.exists_normFrame hcE hD
    hpp.one_lt.le hc1 htr hAlt hQ S hSc hSp hSB hS1
  have hΦS' : ∀ b ∈ A, ∃ k : Fin s → ℕ, ∀ d w, b (Φ (d, w)) = Φ (fun i => (c ^ k i) (d i), w) :=
    fun b hb => hΦS _ ⟨b, hb, rfl⟩
  obtain ⟨r, a, F, ha, hFι, hblk, _⟩ := exists_frame hQ hT hp2 hAΩ hmax hcE hcp hfix hωnd hΦS' hdec
  have hc1E : ∀ u, ∃ u₀, cE u₀ - u₀ = u := fun u => by
    obtain ⟨u₀, h⟩ := hc1 u
    exact ⟨u₀, by rw [hcE]; exact h⟩
  refine ⟨r, F, fun j j' hjj => realizedIn_swap hQ hT hdec hωa hωnd hcp hc1E ha F hFι hblk hjj,
    fun j u hu => ?_⟩
  obtain ⟨T, hT'⟩ := CoordSpNs.mem_twistGroup.mp (hO ω hωa hωnd hωc (Subgroup.subset_closure hu))
  exact realizedIn_twist hdec hcp hc1E ha F hFι hblk j hT'

end Assembly

end OmMv

open CFSG.RankThree.Classical2 (orthDerived)
open Polynomial

theorem ggOmFrameElemMoveInput_holds : GGOmFrameElemMoveInput := by
  intro K _ _ _ V _ _ _ p _ hp2 Q hQ hT A hAΩ hApow hAcomm hmax
  classical
  by_cases hA : ∀ b ∈ A, b = 1
  ·
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hA
    refine ⟨0, {
      ι := 1
      U := fun i => i.elim0
      inj := fun x y _ => Multiplicative.toAdd.injective (funext fun i => i.elim0)
      range := by rw [MonoidHom.range_one, hbot]
      ne_bot := fun i => i.elim0
      nondeg := fun i => i.elim0
      orth := fun i => i.elim0
      mapsTo := fun _ j => j.elim0
      triv := fun _ j => j.elim0
      fpf := fun _ j => j.elim0
      fix := fun _ v => ⟨fun _ j => j.elim0, fun _ => rfl⟩ }, fun i => i.elim0, fun i => i.elim0⟩
  push Not at hA
  have hpp : p.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h2).symm
  have hne' : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hpp]
    have := hpp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne' (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hpp hpK hgd
  have hζp : AdjoinRoot.root g ^ p = 1 := hζ.pow_eq_one
  have hζ0 : AdjoinRoot.root g ≠ 0 := hζ.ne_zero hpp.ne_zero
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζ.ne_one hpp.one_lt
  have hζ1' : AdjoinRoot.root g ^ (p - 1) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by have := hpp.two_le; omega) (by have := hpp.pos; omega)
  have hζ0' : AdjoinRoot.root g ^ (p - 1) ≠ 0 := pow_ne_zero _ hζ0
  have hfix : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ d : AdjoinRoot g, μ * d = d → d = 0 :=
    fun μ hμ d hd => by
      have h0 : (μ - 1) * d = 0 := by rw [sub_mul, hd, one_mul, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  have hsurj : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ u : AdjoinRoot g, ∃ u₀, μ * u₀ - u₀ = u :=
    fun μ hμ u => ⟨(μ - 1)⁻¹ * u, by
      rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hμ), one_mul]⟩
  by_cases hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0
  ·
    exact OmMv.exists_moves_of_block hp2 hQ hT hAΩ hApow hAcomm hmax hA
      (c := LinearMap.mulLeft K (AdjoinRoot.root g)) (cE := CoordSpNs.sdC hζ0) (fun x => rfl)
      (CoordSpNs.sdC_pow_eq_one hζ0 hζp) (SpNS.spBlockExists_selfDual hpp hp2 hpK hgd hσ)
      (hsurj _ hζ1) (fun d hd => hfix _ hζ1 d hd) (CoordSpNs.formTransitive_sd hζp hζ0)
      (fun ω hωa hωnd hωc => CoordSpNs.galSigns_le_twistGroup_sd hζp hζ hσ hζ0 hωa hωnd hωc)
  ·
    exact OmMv.exists_moves_of_block hp2 hQ hT hAΩ hApow hAcomm hmax hA
      (c := (LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft K (AdjoinRoot.root g ^ (p - 1))))
      (cE := CoordSpNs.prC hζ0 hζ0') (fun x => rfl) (CoordSpNs.prC_pow_eq_one hζ0 hζ0' hζp)
      (SpNS.spBlockExists_paired hpp hpK hgd hσ)
      (fun u => by
        obtain ⟨u₁, hu₁⟩ := hsurj _ hζ1 u.1
        obtain ⟨u₂, hu₂⟩ := hsurj _ hζ1' u.2
        exact ⟨(u₁, u₂), Prod.ext hu₁ hu₂⟩)
      (fun d hd => by
        obtain ⟨μ, ν⟩ := d
        rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
        exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
      (CoordSpNs.formTransitive_pr hζ0 hζ0' hζp hζ hσ)
      (fun ω hωa hωnd hωc => CoordSpNs.galSigns_le_twistGroup_pr hζ0 hζ0' hζp hζ hσ hωa hωnd hωc)

end CFSG.StandardType
