module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.L319.S66

@[expose] def O2 (Γ : Type) [Group Γ] : Subgroup Γ :=
  sInf {N : Subgroup Γ | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}

theorem O2_le_of_index {Γ : Type} [Group Γ] (N : Subgroup Γ) [N.Normal] {n : ℕ}
    (h : N.index = 2 ^ n) : O2 Γ ≤ N := by
  unfold O2
  exact sInf_le ⟨inferInstance, n, h⟩

theorem O2_map_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (e : Γ ≃* Γ') :
    (O2 Γ).map e.toMonoidHom = O2 Γ' := by
  have key : ∀ (A B : Type) [Group A] [Group B] (f : A ≃* B),
      (O2 A).map f.toMonoidHom ≤ O2 B := by
    intro A B _ _ f
    unfold O2
    refine le_sInf fun N hN => ?_
    obtain ⟨hNn, n, hn⟩ := hN
    haveI := hNn
    have hidx : (N.comap f.toMonoidHom).index = 2 ^ n := by
      rw [Subgroup.comap_equiv_eq_map_symm']
      exact (Subgroup.index_map_equiv (H := N) f.symm).trans hn
    rw [Subgroup.map_le_iff_le_comap]
    exact O2_le_of_index (N.comap f.toMonoidHom) hidx
  refine le_antisymm (key Γ Γ' e) ?_
  have hc : (O2 Γ).map e.toMonoidHom = (O2 Γ).comap e.symm.toMonoidHom :=
    Subgroup.map_equiv_eq_comap_symm e (O2 Γ)
  rw [hc]
  exact (Subgroup.map_le_iff_le_comap).mp (key Γ' Γ e.symm)

theorem O2_eq_of_perfect_normal {Γ : Type} [Group Γ] [Finite Γ] (Y P : Subgroup Γ) [Y.Normal]
    (hP : IsPGroup 2 ↥P) (hYP : Y ⊔ P = ⊤) (hYperf : ⁅Y, Y⁆ = Y) :
    O2 Γ = Y := by
  have hYp : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYperf
  have hsurj : Function.Surjective ((QuotientGroup.mk' Y).comp P.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Y q
    have hg : g ∈ Y ⊔ P := by rw [hYP]; exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    refine ⟨⟨z, hz⟩, ?_⟩
    have hy1 : (QuotientGroup.mk' Y) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    show (QuotientGroup.mk' Y) z = (QuotientGroup.mk' Y) (y * z)
    rw [map_mul, hy1, one_mul]
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hP.of_surjective _ hsurj)
  have hYidx : Y.index = 2 ^ n := by
    rw [Subgroup.index_eq_card]
    exact hn
  refine le_antisymm (O2_le_of_index Y hYidx) ?_
  unfold O2
  refine le_sInf fun N hN => ?_
  obtain ⟨hNn, m, hm⟩ := hN
  haveI := hNn
  have hQ : IsPGroup 2 (Γ ⧸ N) := by
    rw [IsPGroup.iff_card]
    exact ⟨m, by rw [← Subgroup.index_eq_card]; exact hm⟩
  haveI : Group.IsNilpotent (Γ ⧸ N) := hQ.isNilpotent
  have hYp' : Group.IsPerfect ↥(Y.map (QuotientGroup.mk' N)) :=
    Group.IsPerfect.map (QuotientGroup.mk' N)
  have hbot : Y.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    haveI := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent ↥(Y.map (QuotientGroup.mk' N)) inferInstance
  intro y hy
  have hmem : (QuotientGroup.mk' N) y ∈ Y.map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hy
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff y).mp hmem

theorem commutator_iSup_eq_of_perfect {Γ : Type} [Group Γ] (𝓚 : Finset (Subgroup Γ))
    (h : ∀ K ∈ 𝓚, Group.IsPerfect ↥K) :
    ⁅(⨆ K ∈ 𝓚, K), (⨆ K ∈ 𝓚, K)⁆ = ⨆ K ∈ 𝓚, K := by
  have hle : ∀ Y : Subgroup Γ, ⁅Y, Y⁆ ≤ Y := by
    intro Y
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hg₁ hg₂) (Y.inv_mem hg₁)) (Y.inv_mem hg₂)
  refine le_antisymm (hle _) ?_
  refine iSup₂_le fun K hK => ?_
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (h K hK)
  calc K = ⁅K, K⁆ := hKK.symm
    _ ≤ ⁅⨆ K ∈ 𝓚, K, ⨆ K ∈ 𝓚, K⁆ :=
        Subgroup.commutator_mono (le_iSup₂ (f := fun K (_ : K ∈ 𝓚) => K) K hK)
          (le_iSup₂ (f := fun K (_ : K ∈ 𝓚) => K) K hK)

theorem not_isPerfect_of_mulEquiv_perm {H : Type} [Group H] {m : ℕ} (hm : 2 ≤ m)
    (θ : H ≃* Equiv.Perm (Fin m)) : ¬ Group.IsPerfect H := by
  intro hH
  have hPerm : Group.IsPerfect (Equiv.Perm (Fin m)) :=
    Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective
  have hsign : Function.Surjective (Equiv.Perm.sign : Equiv.Perm (Fin m) →* ℤˣ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      exact ⟨Equiv.swap _ _, Equiv.Perm.sign_swap hne⟩
  have hZ : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective hsign
  haveI : IsMulCommutative ℤˣ := ⟨⟨fun a b => mul_comm a b⟩⟩
  haveI : Subsingleton ℤˣ := inferInstance
  have h1 : (-1 : ℤˣ) = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : ℤˣ => (u : ℤ)) h1
  norm_num at h2

end CFSG.Quasithin.H13.L319.S66

end
