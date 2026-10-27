module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneModel
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCOrthogonalModel
  CFSG.ComponentClassification.OuterAutomorphisms

theorem isElementaryAbelian_map_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    (ψ : X ≃* Y) {A : Subgroup X} (hA : IsElementaryAbelian p A) :
    IsElementaryAbelian p (A.map ψ.toMonoidHom) ∧ Nat.card (A.map ψ.toMonoidHom) = Nat.card A := by
  refine ⟨?_, Subgroup.card_map_of_injective ψ.injective⟩
  let j : ↥A ≃* ↥(A.map ψ.toMonoidHom) := ψ.subgroupMap A
  exact
    { is_comm := ⟨fun a b => j.symm.injective (by
        rw [map_mul, map_mul]
        exact hA.1.1.1 (j.symm a) (j.symm b))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => j.symm.injective (by
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hA.2 (j.symm g)) }

theorem CommonLayerCentralizerTrivial.of_mulEquiv {P P' : Type} [Group P] [Group P']
    (e : P ≃* P') {p : ℕ} (h : CommonLayerCentralizerTrivial P p) :
    CommonLayerCentralizerTrivial P' p := by
  intro D' hD' A' hA'inner hA' hcard'
  rw [iInf_centralizer_layerCentralizer_eq_bot_iff]
  intro α hα
  set ψ : MulAut P' ≃* MulAut P := MulAut.congr e.symm with hψ
  have hD : inner P ≤ D'.map ψ.toMonoidHom := by
    rw [← inner_map_congr e.symm]
    exact Subgroup.map_mono hD'
  have hA : A'.map ψ.toMonoidHom ≤ inner P := by
    rw [← inner_map_congr e.symm]
    exact Subgroup.map_mono hA'inner
  obtain ⟨hAel, hAcardeq⟩ := isElementaryAbelian_map_of_mulEquiv ψ hA'
  have hres := h _ hD _ hA hAel (hAcardeq.trans hcard')
  have hpoint := (iInf_centralizer_layerCentralizer_eq_bot_iff _ _).mp hres
  have hψα : ψ α = 1 := by
    refine hpoint (ψ α) fun a ha ha1 d hd => ?_
    obtain ⟨a', ha', rfl⟩ := ha
    have ha'1 : a' ≠ 1 := by
      rintro rfl
      exact ha1 (map_one ψ)
    have hd' : d ∈ (layerCentralizer D' a').map ψ.toMonoidHom := by
      rw [map_layerCentralizer]
      exact hd
    obtain ⟨d', hd'', rfl⟩ := hd'
    have h1 := hα a' ha' ha'1 d' hd''
    show ψ d' * ψ α = ψ α * ψ d'
    rw [← map_mul, ← map_mul, h1]
  exact ψ.injective (hψα.trans (map_one ψ).symm)

section Products

open Polynomial Module CFSG.RankThree.LocalRank CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary

theorem layer_le_centralizer_core {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) :
    CFSG.layer M ≤ Subgroup.centralizer ((aschbacherSolvableCore p M : Subgroup M) : Set M) := by
  have hsolv := (solvable_prime_complement_core_characterization (H := M) hp).1
  have hsub : (aschbacherSolvableCore p M).IsSubnormal :=
    (inferInstance : (aschbacherSolvableCore p M).Normal).isSubnormal
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.LocalCores.component_solvable_centralizer hsolv hsub).2

theorem commute_layerCentralizer_of_mem_core {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime) (B : Subgroup (MulAut T)) (a : MulAut T) {s d : MulAut T}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut T))))
    (hd : d ∈ KCOrthogonalD4.layerCentralizer B a) : d * s = s * d := by
  have : Finite (MulAut T) :=
    Finite.of_injective (fun f : MulAut T => (f : T → T)) DFunLike.coe_injective
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨d', hd', rfl⟩ := hd
  have h := Subgroup.mem_centralizer_iff.mp (layer_le_centralizer_core hp hd') s' hs'
  exact congrArg Subtype.val h.symm

@[expose] def LiftMultiplicitiesCoprime {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] (p : ℕ) (Q : QuadraticForm K V) (A : Subgroup (MulAut (ProjOrthDerived Q))) :
    Prop :=
  ∀ x : orthDerived Q, orderOf x = p →
    MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A →
      MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 →
      ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orthogonal_inner_plane_planeLocalCoreInner
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hfull : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p) :
    PlaneLocalCoreInner p (ProjOrthDerived Q) (LiftMultiplicitiesCoprime p Q) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro B hB A hAinner hA hAcard hmult t htA ht1
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := center_projOrthDerived_eq_bot hQ hT
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_trivial_center hcenter
  have hfinT : Finite (ProjOrthDerived Q) := inferInstance
  have hfinAut : Finite (MulAut (ProjOrthDerived Q)) :=
    Finite.of_injective (fun f : MulAut (ProjOrthDerived Q) => (f : ProjOrthDerived Q → _))
      DFunLike.coe_injective
  set A' : Subgroup (ProjOrthDerived Q) :=
    A.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hA'
  have hmapA' : A'.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = A := by
    rw [hA', Subgroup.map_comap_eq, inf_eq_right.mpr hAinner]
  have hcardA' : Nat.card A' = p ^ 2 := by
    rw [← hAcard, ← Subgroup.card_map_of_injective hinj (K := A'), hmapA']
  have hA'el : Assembly.IsElemAbelian p A' := by
    have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
      intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      have := hA.1
      exact congrArg Subtype.val (mul_comm' (⟨MulAut.conj x, hx⟩ : A) ⟨MulAut.conj y, hy⟩)
    refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (MulAut.conj x) hx
  have hcent : ∀ a ∈ A, a ≠ 1 → ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (ProjOrthDerived Q)))),
      ∀ g ∈ A, g * s = s * g := by
    intro a haA ha1 s hs g hg
    obtain ⟨a₀, rfl⟩ : a ∈ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range :=
      hAinner haA
    obtain ⟨g₀, rfl⟩ : g ∈ (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range :=
      hAinner hg
    have ha₀A' : a₀ ∈ A' := haA
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have hord : orderOf a₀ = p := orderOf_eq_prime
      (by exact (hA'el.2 a₀ ha₀A')) ha₀1
    obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
    obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift p hp (by omega) a₀ hord
    have hpm : ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h :=
      hmult x hxp (by rw [hxa]; exact haA) (by rw [hxa]; exact ha1)
    obtain ⟨-, -, -, h4⟩ := orthogonal_inner_plane_local_core_centralization hQ hT hp hp3 hpl B
      hB A' hA'el hcardA' a₀ ha₀A' ha₀1 x hxa hxp
    exact ((h4 hpm).2 g₀ hg s hs).symm
  refine sup_eq_bot_iff.mpr ⟨?_, ?_⟩
  ·
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hcent t htA ht1 s hs g hg
  ·
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    have hpoint := (iInf_centralizer_layerCentralizer_eq_bot_iff B A).mp
      (hfull B hB A hAinner hA hAcard)
    refine hpoint α fun a haA ha1 d hd => ?_
    have hαa : α ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (ProjOrthDerived Q)))) := by
      have := hα
      unfold autThetaT at this
      rw [Subgroup.mem_iInf] at this
      have h2 := this a
      rw [Subgroup.mem_iInf] at h2
      have h3 := h2 haA
      rw [Subgroup.mem_iInf] at h3
      exact h3 ha1
    exact commute_layerCentralizer_of_mem_core hp B a hαa hd

end Products

end CFSG.RankThree.PartOne
