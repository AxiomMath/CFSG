module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.F106.U6Three
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.StandardType
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective)

@[expose] noncomputable def outerAction {G : Type} [Group G] (L : Subgroup G) :
    normalizer (L : Set G) →* Outer L :=
  (QuotientGroup.mk' (inner L)).comp (normalizerMonoidHom L)

theorem outerAction_eq_one {G : Type} [Group G] {L : Subgroup G} (g : normalizer (L : Set G))
    (hg : (g : G) ∈ L) : outerAction L g = 1 := by
  apply (QuotientGroup.eq_one_iff _).2
  refine ⟨⟨g, hg⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
  simp [MulAut.conj_apply]

theorem outerAction_ggAutomizer {G : Type} [Group G] {L Bs : Subgroup G}
    (hN : Bs ≤ normalizer (L : Set G)) {φ : MulAut Bs} (hφ : φ ∈ ggAutomizer L Bs) (b : Bs) :
    (outerAction L).comp (inclusion hN) (φ b) = (outerAction L).comp (inclusion hN) b := by
  set ν := (outerAction L).comp (inclusion hN)
  let S : Subgroup (MulAut Bs) :=
    { carrier := {ψ | ∀ b, ν (ψ b) = ν b}
      one_mem' := fun b => rfl
      mul_mem' := fun {ψ χ} hψ hχ b => by rw [MulAut.mul_apply, hψ, hχ]
      inv_mem' := fun {ψ} hψ b => by
        have := hψ (ψ⁻¹ b)
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at this
        exact this.symm }
  have hle : ggAutomizer L Bs ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro ψ ⟨g, hgL, hgN, hψ⟩ b
    have hgN' : g ∈ normalizer (L : Set G) := le_normalizer hgL
    have e : inclusion hN (ψ b) =
        ⟨g, hgN'⟩ * inclusion hN b * (⟨g, hgN'⟩ : normalizer (L : Set G))⁻¹ :=
      Subtype.ext (by simp [hψ])
    change outerAction L (inclusion hN (ψ b)) = outerAction L (inclusion hN b)
    rw [e, map_mul, map_mul, map_inv, outerAction_eq_one _ hgL, one_mul, inv_one, mul_one]
  exact hle hφ b

theorem exists_outerAction_ne_one {G : Type} [Group G]
    [Finite G] {L Bs : Subgroup G} [Group.IsPerfect L]
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) (hBab : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 6) (hN : Bs ≤ normalizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S) :
    ∃ b : Bs, (outerAction L).comp (inclusion hN) b ≠ 1 := by
  by_contra hall
  push Not at hall
  set S := L ⧸ center L
  let ρ : Bs →* MulAut S :=
    (centerQuotientHom L).comp ((normalizerMonoidHom L).comp (inclusion hN))
  have hρ : ∀ b, ρ b ∈ (MulAut.conj : S →* MulAut S).range := fun b => by
    have h1 : normalizerMonoidHom L (inclusion hN b) ∈ inner L :=
      (QuotientGroup.eq_one_iff _).1 (hall b)
    obtain ⟨u, hu⟩ := h1
    refine ⟨QuotientGroup.mk' _ u, ?_⟩
    change MulAut.conj (QuotientGroup.mk' (center L) u) =
      centerQuotientHom L (normalizerMonoidHom L (inclusion hN b))
    rw [← hu, centerQuotient_conj]
  have hkerC : ∀ b : Bs, ρ b = 1 → (b : G) ∈ centralizer (L : Set G) := fun b hb => by
    have h := centerQuotientHom_injective L (hb.trans (map_one _).symm)
    rw [mem_centralizer_iff]
    intro y hy
    have := congrArg (fun f : MulAut L => ((f ⟨y, hy⟩ : L) : G)) h
    simp only [MulAut.one_apply] at this
    change (b : G) * y * (b : G)⁻¹ = y at this
    calc y * (b : G) = (b : G) * y * (b : G)⁻¹ * (b : G) := by rw [this]
      _ = (b : G) * y := by group
  have hC : Nat.card (Bs ⊓ centralizer (L : Set G) : Subgroup G) ≤ 3 := by
    have hc3 : ∀ c : (Bs ⊓ centralizer (L : Set G) : Subgroup G), c ^ 3 = 1 := fun c =>
      Subtype.ext (by simpa using hBab.2 c c.2.1)
    have hp : IsPGroup 3 (Bs ⊓ centralizer (L : Set G) : Subgroup G) := fun c => ⟨1, hc3 c⟩
    have hcy := hcyc _ inf_le_right hp
    have hexp : Monoid.exponent (Bs ⊓ centralizer (L : Set G) : Subgroup G) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hc3
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have hker : Nat.card ρ.ker ≤ 3 := by
    refine (Nat.card_le_card_of_injective (fun k : ρ.ker =>
      (⟨((k : Bs) : G), (k : Bs).2, hkerC k k.2⟩ : (Bs ⊓ centralizer (L : Set G) : Subgroup G)))
      fun a b hab => ?_).trans hC
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hkr := Subgroup.card_ker_mul_card_range ρ
  rw [hcard] at hkr
  have hkdvd : Nat.card ρ.ker ∣ 3 ^ 6 := ⟨_, hkr.symm⟩
  obtain ⟨j, hj, hkj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hkdvd
  have hj1 : j ≤ 1 := by
    by_contra hc
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hZ : center S = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot L
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro s t hst
    have hc : s⁻¹ * t ∈ center S := by
      rw [mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut S => f y) hst
      simp only [MulAut.conj_apply] at this
      calc y * (s⁻¹ * t) = s⁻¹ * (s * y * s⁻¹) * t := by group
        _ = s⁻¹ * (t * y * t⁻¹) * t := by rw [this]
        _ = s⁻¹ * t * y := by group
    rw [hZ, mem_bot, inv_mul_eq_one] at hc
    exact hc
  set D : Subgroup S := ρ.range.comap (MulAut.conj : S →* MulAut S)
  have hDcard : Nat.card D = Nat.card ρ.range := by
    refine Nat.card_congr (Equiv.ofBijective (fun d : D => (⟨MulAut.conj (d : S), d.2⟩ : ρ.range))
      ⟨fun a b hab => Subtype.ext (hconj (congrArg Subtype.val hab)), fun r => ?_⟩)
    obtain ⟨b, hb⟩ := r.2
    obtain ⟨s, hs⟩ := hρ b
    exact ⟨⟨s, by rw [mem_comap, hs]; exact ⟨b, rfl⟩⟩, Subtype.ext (hs.trans hb)⟩
  have hDcomm : ∀ s ∈ D, ∀ t ∈ D, s * t = t * s := fun s hs t ht => by
    obtain ⟨b, hb⟩ := hs
    obtain ⟨b', hb'⟩ := ht
    apply hconj
    rw [map_mul, map_mul, ← hb, ← hb', ← map_mul, ← map_mul]
    congr 1
    have := hBab.1.is_comm.comm ⟨b, b.2⟩ ⟨b', b'.2⟩
    exact Subtype.ext (congrArg Subtype.val this)
  have hDcube : ∀ s ∈ D, s ^ 3 = 1 := fun s hs => by
    obtain ⟨b, hb⟩ := hs
    apply hconj
    rw [map_pow, ← hb, ← map_pow, map_one]
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hBab.2 b b.2)
    rw [this, map_one]
  have h5 : 3 ^ 5 ∣ Nat.card D := by
    rw [hDcard]
    interval_cases j
    · rw [hkj, pow_zero, one_mul] at hkr
      rw [hkr]
      exact pow_dvd_pow 3 (by norm_num)
    · rw [hkj, pow_one] at hkr
      exact ⟨1, by omega⟩
  have : Finite D := inferInstance
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime 3 h5
  have hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 6 2 1 := by
    rcases hQ with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  refine CFSG.RankThree.PartOne.F106.u6_no_elemAbelian_five hmod (E.map D.subtype)
    ?_ ?_ ?_
  · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
    exact hDcomm _ a.2 _ b.2
  · rintro _ ⟨a, -, rfl⟩
    exact hDcube _ a.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hE]

end CFSG.GGQ2Prime
