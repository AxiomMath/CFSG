module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoCent
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusForm

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Module QuadraticMap LayerCores LayerCores.OrthSplit
open CFSG.StandardType.TraceFrame
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem odd_card_of_isElemAbelian_three {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsElemAbelian 3 A) : Odd (Nat.card A) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hA.isPGroup.exists_card_eq
  rw [hn]
  exact (by norm_num : Odd 3).pow

private noncomputable def traceFormOf {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) (τ : M ≃+* M) : LinearMap.BilinForm K M :=
  (Algebra.traceForm K M).compl₁₂ (tauAlg (τ := τ) hK).toLinearMap LinearMap.id

private theorem traceFormOf_apply {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) (τ : M ≃+* M) (u v : M) :
    traceFormOf hK τ u v = Algebra.trace K M (τ u * v) := by
  simp [traceFormOf, Algebra.traceForm_apply, tauAlg]

private theorem trace_one_eq_zero {K M : Type} [Field K] [CharP K 2] [Field M] [Algebra K M]
    (hfr : Module.finrank K M = 2) : Algebra.trace K M 1 = 0 := by
  have h := Algebra.trace_algebraMap (R := K) (S := M) (1 : K)
  rw [map_one, hfr] at h
  rw [h]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simpa using h2

private theorem traceFormOf_isAlt {K M : Type} [Field K] [Finite K] [Field M] [Finite M]
    [CharP K 2] [Algebra K M] (hK : Nat.card K = 2) (hM : Nat.card M = 4) (τ : M ≃+* M)
    (hτ : ∀ y, τ y = y ^ 2) (hfr : Module.finrank K M = 2) :
    (traceFormOf hK τ).IsAlt := by
  intro u
  rw [traceFormOf_apply]
  by_cases hu : u = 0
  · subst hu
    simp
  · have : Fintype M := Fintype.ofFinite M
    have hu3 : u ^ 3 = 1 := by
      have h := FiniteField.pow_card_sub_one_eq_one u hu
      rwa [← Nat.card_eq_fintype_card, hM] at h
    rw [hτ u, show u ^ 2 * u = u ^ 3 by ring, hu3]
    exact trace_one_eq_zero hfr

private theorem traceFormOf_nondegenerate {K M : Type} [Field K] [Finite K] [Field M]
    [Finite M] [Algebra K M] (hK : Nat.card K = 2) (τ : M ≃+* M) :
    ∀ u, (∀ v, traceFormOf hK τ u v = 0) → u = 0 := by
  intro u hu
  have hτu : τ u = 0 := by
    refine eq_zero_of_trace_mul_eq_zero (K := K) (M := M) ?_
    intro μ
    have h := hu μ
    rw [traceFormOf_apply] at h
    rwa [mul_comm] at h
  exact τ.injective (by rw [hτu, map_zero])

theorem exists_traceFrame_of_isElemAbelian_orth {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (V ≃ₗ[K] V)} (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hA : IsElemAbelian 3 A) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra K M) (τ : M ≃+* M)
      (U : Type) (_ : AddCommGroup U) (_ : Module K U) (Φ : ((Fin n → M) × U) ≃ₗ[K] V),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧
      (∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) +
          QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))) ∧
      (∀ a ∈ A, ∃ c : Fin n → M, (∀ i, c i ^ 3 = 1) ∧
        ∀ d w, a (Φ (d, w)) = Φ (fun i => c i * d i, w)) ∧
      ∀ i, ∃ a ∈ A, a (Φ (Pi.single i 1, 0)) ≠ Φ (Pi.single i 1, 0) := by
  classical
  have : Finite (V ≃ₗ[K] V) := LayerCores.finite_linearEquiv
  have : Fintype A := Fintype.ofFinite A
  have hAodd : Odd (Fintype.card A) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_card_of_isElemAbelian_three hA
  have hA0 : (Fintype.card A : K) ≠ 0 := natCast_card_ne_zero_of_odd hAodd
  let W : Submodule K V := freeSp A
  let U : Submodule K V := fixSp A
  let B : LinearMap.BilinForm K W := LinearMap.BilinForm.restrict (polarBilin Q) W
  have hBAlt : B.IsAlt := fun w => by
    change polar Q (w : V) (w : V) = 0
    rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  have hndB : B.Nondegenerate := by
    have h := CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (polarNondegOn_freeSp hQ hA0 hAO)
    exact ⟨fun x hx => h.1 x hx, fun y hy => h.2 y hy⟩
  let A₁ : Subgroup ↥(sesqUnitaryGroup B) := (orthRestrict A A hAO le_stab).range
  have hA₁ : IsElemAbelian 3 A₁ := by
    have h := (hA.subgroupOf A).map (orthRestrict A A hAO le_stab)
    simpa [A₁, Subgroup.subgroupOf_self, MonoidHom.range_eq_map] using h
  let F : SpNS.FrameData K W B A₁ := (SpNS.exists_frame_data hK hBAlt hndB A₁ hA₁).some
  have : Fact (Irreducible F.g) := ⟨F.hg⟩
  have hfixed : ∀ w : F.κ → K, F.Φ (0, w) = 0 := by
    intro w
    have hfix : (F.Φ (0, w) : V) ∈ fixSp A := by
      rw [mem_fixSp_iff hA0]
      intro a ha
      obtain ⟨k, hk⟩ := F.hact _ (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
      have h1 := hk (0 : Fin F.s → AdjoinRoot F.g) w
      have hz : (fun i => F.ζ ^ k i * (0 : Fin F.s → AdjoinRoot F.g) i) = 0 := by
        funext i
        simp
      rw [hz] at h1
      have h2 : (restrFree A ⟨a, le_stab ha⟩ (F.Φ (0, w)) : V) = (F.Φ (0, w) : V) := by
        rw [← orthRestrict_apply A A hAO le_stab ⟨a, ha⟩ (F.Φ (0, w))]
        exact congrArg Subtype.val h1
      simpa only [coe_restrFree_apply] using h2
    have hfree : (F.Φ (0, w) : V) ∈ freeSp A := (F.Φ (0, w)).2
    exact Subtype.ext (Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA0).disjoint _
      hfix hfree)
  let M : Type := AdjoinRoot F.g
  have hfdM : FiniteDimensional K (AdjoinRoot F.g) := F.b.finiteDimensional_of_finite
  have hMfin : Finite M := Module.finite_of_finite K
  have hfrM : Module.finrank K M = 2 := by
    rw [Module.finrank_eq_card_basis F.b, Fintype.card_fin]
  have hcardM : Nat.card M = 4 := by
    have : Fintype K := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    have : Fintype M := Fintype.ofFinite M
    have h := Module.card_eq_pow_finrank (K := K) (V := M)
    rw [hK', hfrM] at h
    norm_num at h
    rw [Nat.card_eq_fintype_card]
    exact h
  have hcharM : CharP M 2 := (Algebra.charP_iff (K := K) (L := M) 2).mp inferInstance
  have hexpM : ExpChar M 2 := ExpChar.prime Nat.prime_two
  have hperfM : PerfectRing M 2 := PerfectField.toPerfectRing 2
  let τ : M ≃+* M := frobeniusEquiv M 2
  have hτapp : ∀ y : M, τ y = y ^ 2 := fun y => frobeniusEquiv_def (R := M) (p := 2) y
  let T : LinearMap.BilinForm K M := traceFormOf hK τ
  have hTalt : T.IsAlt := traceFormOf_isAlt hK hcardM τ hτapp hfrM
  have hTnd : ∀ u, (∀ v, T u v = 0) → u = 0 := traceFormOf_nondegenerate hK τ
  have hβeq : F.s ≠ 0 → F.β = T := by
    intro hs
    have hβalt : F.β.IsAlt := by
      intro u
      obtain ⟨i₀⟩ : Nonempty (Fin F.s) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hs)
      let du : Fin F.s → AdjoinRoot F.g := Pi.single i₀ u
      have h := F.hdec du du (0 : F.κ → K) (0 : F.κ → K)
      have hsum : (∑ i, F.β (du i) (du i)) = F.β u u := by
        rw [Finset.sum_eq_single i₀]
        · rw [show du i₀ = u by simp [du]]
        · intro j _ hj
          rw [show du j = 0 by simp [du, hj]]
          simp
        · intro h
          exact absurd (Finset.mem_univ i₀) h
      have h0 : F.Φ ((0 : Fin F.s → AdjoinRoot F.g), (0 : F.κ → K)) = 0 := map_zero F.Φ
      rw [hBAlt, hsum, h0] at h
      simpa using h.symm
    have hβnd : ∀ u, (∀ v, F.β u v = 0) → u = 0 := by
      intro u hu
      obtain ⟨i₀⟩ : Nonempty (Fin F.s) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hs)
      let du : Fin F.s → AdjoinRoot F.g := Pi.single i₀ u
      have horth : ∀ y : W, B (F.Φ (du, 0)) y = 0 := by
        intro y
        obtain ⟨⟨d', w'⟩, rfl⟩ := F.Φ.surjective y
        have h := F.hdec du d' (0 : F.κ → K) w'
        have hsum : (∑ i, F.β (du i) (d' i)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i = i₀
          · rw [show du i = u by simp [du, hi]]
            exact hu (d' i)
          · rw [show du i = 0 by simp [du, hi]]
            simp
        have h0 : F.Φ ((0 : Fin F.s → AdjoinRoot F.g), (0 : F.κ → K)) = 0 := map_zero F.Φ
        rw [hsum, h0] at h
        simpa using h
      have hzero : F.Φ (du, 0) = 0 := hndB.1 _ horth
      have hp : (du, (0 : F.κ → K)) = 0 := F.Φ.injective (by rw [hzero, map_zero])
      have := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.1 i₀) hp
      simpa [du] using this
    have hTne : T (F.b 0) (F.b 1) ≠ 0 := SpNS.alt_two_ne_zero F.b hTalt hTnd
    have hβne : F.β (F.b 0) (F.b 1) ≠ 0 := SpNS.alt_two_ne_zero F.b hβalt hβnd
    have hβ1 : F.β (F.b 0) (F.b 1) = 1 := by
      rcases card_two_eq_zero_or_one hK (F.β (F.b 0) (F.b 1)) with h | h
      · exact absurd h hβne
      · exact h
    have hT1 : T (F.b 0) (F.b 1) = 1 := by
      rcases card_two_eq_zero_or_one hK (T (F.b 0) (F.b 1)) with h | h
      · exact absurd h hTne
      · exact h
    have hprop := SpNS.alt_two_eq_smul F.b hβalt hTalt hTne
    simpa [hβ1, hT1] using hprop
  let Φ₀lin : (Fin F.s → M) →ₗ[K] W :=
    F.Φ.toLinearMap.comp (LinearMap.inl K (Fin F.s → M) (F.κ → K))
  have hΦ₀inj : Function.Injective Φ₀lin := by
    intro d d' h
    change F.Φ (d, 0) = F.Φ (d', 0) at h
    exact congrArg Prod.fst (F.Φ.injective h)
  have hΦ₀surj : Function.Surjective Φ₀lin := by
    intro x
    obtain ⟨⟨d, w⟩, hx⟩ := F.Φ.surjective x
    refine ⟨d, ?_⟩
    change F.Φ (d, 0) = x
    have hw : F.Φ (0, w) = 0 := hfixed w
    have h1 : F.Φ (d, 0) + F.Φ (0, w) = x := by
      rw [← map_add]
      simpa using hx
    simpa [hw] using h1
  let Φ₀ : (Fin F.s → M) ≃ₗ[K] W :=
    LinearEquiv.ofBijective Φ₀lin ⟨hΦ₀inj, hΦ₀surj⟩
  have hΦ₀apply : ∀ d : Fin F.s → M, (Φ₀ d : W) = F.Φ (d, 0) := fun d => rfl
  let Φ : ((Fin F.s → M) × U) ≃ₗ[K] V :=
    (Φ₀.prodCongr (LinearEquiv.refl K U)).trans
      (Submodule.prodEquivOfIsCompl W U (isCompl_fixSp_freeSp hA0).symm)
  have hΦ_apply : ∀ (d : Fin F.s → M) (w : U),
      (Φ (d, w) : V) = (F.Φ (d, 0) : V) + (w : V) := by
    intro d w
    change (Submodule.prodEquivOfIsCompl W U (isCompl_fixSp_freeSp hA0).symm)
      (Φ₀ d, w) = (F.Φ (d, 0) : V) + (w : V)
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  have hΦ0w : ∀ w : U, (Φ (0, w) : V) = (w : V) := by
    intro w
    rw [hΦ_apply]
    simp
  have hsumβ : ∀ d d' : Fin F.s → M,
      B (F.Φ (d, 0)) (F.Φ (d', 0)) = ∑ i, F.β (d i) (d' i) := by
    intro d d'
    have h := F.hdec d d' (0 : F.κ → K) (0 : F.κ → K)
    have h0 : F.Φ ((0 : Fin F.s → AdjoinRoot F.g), (0 : F.κ → K)) = 0 := map_zero F.Φ
    rw [h0] at h
    simpa using h
  have hsumβpolar : ∀ d d' : Fin F.s → M,
      polar Q (F.Φ (d, 0) : V) (F.Φ (d', 0) : V) = ∑ i, F.β (d i) (d' i) :=
    fun d d' => hsumβ d d'
  have hsum : ∀ d d' : Fin F.s → M,
      (∑ i, F.β (d i) (d' i)) = ∑ i, Algebra.trace K M (τ (d i) * d' i) := by
    intro d d'
    by_cases hs : F.s = 0
    · have : IsEmpty (Fin F.s) := by rw [hs]; infer_instance
      simp
    · rw [hβeq hs]
      exact Finset.sum_congr rfl fun i _ => traceFormOf_apply hK τ (d i) (d' i)
  have hpolar : ∀ d d' w w',
      QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) +
          QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w')) := by
    intro d d' w w'
    have hcross1 : polar Q (F.Φ (d, 0) : V) (w' : V) = 0 := by
      rw [polar_comm, polar_fixSp_freeSp hAO w'.2 (F.Φ (d, 0)).2]
    have hcross2 : polar Q (w : V) (F.Φ (d', 0) : V) = 0 :=
      polar_fixSp_freeSp hAO w.2 (F.Φ (d', 0)).2
    change polar Q (Φ (d, w) : V) (Φ (d', w') : V) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) +
        polar Q (Φ (0, w) : V) (Φ (0, w') : V)
    rw [hΦ_apply d w, hΦ_apply d' w', hΦ0w w, hΦ0w w']
    calc polar Q ((F.Φ (d, 0) : V) + w) ((F.Φ (d', 0) : V) + w')
        = polar Q (F.Φ (d, 0)) (F.Φ (d', 0)) + polar Q (w : V) (w' : V) := by
          simp only [polar_add_left, polar_add_right, hcross1, hcross2, zero_add, add_zero]
      _ = ∑ i, F.β (d i) (d' i) + polar Q (w : V) (w' : V) := by rw [hsumβpolar]
      _ = ∑ i, Algebra.trace K M (τ (d i) * d' i) +
            polar Q (w : V) (w' : V) := by rw [hsum]
  have hact : ∀ a ∈ A, ∃ c : Fin F.s → M, (∀ i, c i ^ 3 = 1) ∧
      ∀ d w, a (Φ (d, w)) = Φ (fun i => c i * d i, w) := by
    intro a ha
    obtain ⟨k, hk⟩ := F.hact _ (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    refine ⟨fun i => F.ζ ^ k i, ?_, ?_⟩
    · intro i
      rw [← pow_mul, mul_comm, pow_mul, F.hζp, one_pow]
    · intro d w
      have h1 := hk d (0 : F.κ → K)
      have hfree : a (F.Φ (d, 0) : V) =
          F.Φ (fun i => F.ζ ^ k i * d i, 0) := by
        have h2 : (restrFree A ⟨a, le_stab ha⟩ (F.Φ (d, 0)) : V) =
            F.Φ (fun i => F.ζ ^ k i * d i, 0) := by
          rw [← orthRestrict_apply A A hAO le_stab ⟨a, ha⟩ (F.Φ (d, 0))]
          exact congrArg Subtype.val h1
        simpa only [coe_restrFree_apply] using h2
      have hfixw : a (w : V) = (w : V) := (mem_fixSp_iff hA0).mp w.2 a ha
      rw [hΦ_apply d w, map_add, hfree, hfixw, hΦ_apply]
  have hmoved : ∀ i, ∃ a ∈ A, a (Φ (Pi.single i 1, 0)) ≠ Φ (Pi.single i 1, 0) := by
    intro i
    by_contra h
    push Not at h
    have hxfix : (Φ (Pi.single i (1 : M), 0) : V) ∈ fixSp A := by
      refine (mem_fixSp_iff hA0).mpr ?_
      intro a ha
      exact h a ha
    have hxfree : (Φ (Pi.single i (1 : M), 0) : V) ∈ freeSp A := by
      rw [hΦ_apply]
      simp
    have hzero : (Φ (Pi.single i (1 : M), 0) : V) = 0 :=
      Submodule.disjoint_def.mp (isCompl_fixSp_freeSp hA0).disjoint _ hxfix hxfree
    have hne : (Φ (Pi.single i (1 : M), 0) : V) ≠ 0 := by
      intro h0
      have h1 : F.Φ (Pi.single i (1 : M), (0 : F.κ → K)) = 0 := by
        have h2 := hΦ_apply (Pi.single i (1 : M)) (0 : U)
        rw [h2] at h0
        rw [show (↑(0 : U) : V) = (0 : V) from rfl, add_zero] at h0
        exact Subtype.coe_injective h0
      have hp : (Pi.single i (1 : M), (0 : F.κ → K)) = 0 :=
        F.Φ.injective (by rw [h1, map_zero])
      have := congrArg (fun z : (Fin F.s → AdjoinRoot F.g) × (F.κ → K) => z.1 i) hp
      simp at this
    exact hne hzero
  exact ⟨F.s, M, inferInstance, hMfin, inferInstance, τ, U, inferInstance, inferInstance, Φ,
    hcardM, hτapp, hpolar, hact, hmoved⟩

end CFSG.StandardType

end
