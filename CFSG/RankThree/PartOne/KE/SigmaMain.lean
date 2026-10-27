module

public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KE.SigmaCentralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

@[expose] def subtorusSigma (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    (S : Set (Fin τ.rank → ℤ)) : Subgroup (ModGL τ L) :=
  twistedTorusOf n Φ ⊓ Subgroup.centralizer (rootSpan τ L S : Set (ModGL τ L))

theorem subtorusSigma_le_twistedTorusOf (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    (S : Set (Fin τ.rank → ℤ)) : subtorusSigma n Φ S ≤ twistedTorusOf n Φ :=
  inf_le_left

theorem sigma_solvable_normal_cyclic {ι' : Type}
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    [hZ : IsCyclic (subtorusSigma n Φ S)]
    (hconj : ∀ x : C, orderOf x = p →
      ∃ c : C, c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusSigma n Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ subtorusSigma n Φ S →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ S)
    (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints n Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S) :
    ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → IsCyclic V := by
  intro x hx
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hconj x hx
  set Z := subtorusSigma n Φ S with hZdef
  set Q := rootSpan τ L S with hQdef
  set H := torusGroup τ L with hHdef
  set D := Subgroup.centralizer ({x} : Set C) with hD
  let ψ : D →* ModGL τ L :=
    ((MulAut.conj g0⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)).comp D.subtype
  have hψ : ∀ y : D, ψ y = g0⁻¹ * ι (c * (y : C) * c⁻¹) * g0 := fun y => by
    simp [ψ, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψ, hψ] at hab
    have h1 := mul_right_cancel (mul_left_cancel hab)
    have h2 := hι h1
    have h3 : (a : C) = b := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hψmem : ∀ y : D, ψ y ∈ adjointGroup τ L := fun y => by
    rw [hψ]
    exact mul_mem (mul_mem (inv_mem hg0C) (hιC _)) hg0C
  have hψfix : ∀ y : D, n * Φ (ψ y) * n⁻¹ = ψ y := fun y => by
    rw [hψ, map_mul, map_mul, map_inv, hg0, hιΦ]
    group
  have hxD : x ∈ D := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set xD : D := ⟨x, hxD⟩ with hxDdef
  set h : ModGL τ L := ψ xD with hh
  have hhZ : h ∈ Z := by
    have := (mem_subtorusImage_iff ι g0 Z (c * x * c⁻¹)).1 hc
    rw [hh, hψ]
    exact this
  have hψx : h = g0⁻¹ * ι (c * x * c⁻¹) * g0 := hψ xD
  have hordh : orderOf h = p := by
    rw [hh, orderOf_injective ψ hψinj xD, ← Subgroup.orderOf_coe]
    exact hx
  have hHh : h ∈ H := (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf n Φ S hhZ)).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hHh
  have hord' : orderOf (rootDiagUnit τ a) = p := by rw [← ha]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hker := hkerZ a (by rw [← ha]; exact hhZ) hord'
  have hcommh : ∀ y : D, ψ y * rootDiagUnit τ a = rootDiagUnit τ a * ψ y := fun y => by
    rw [← ha, hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hHQ : ∀ y : D, ψ y ∈ H ⊔ Q := fun y => by
    have := mem_torus_mul_rootSpan_of_commute hp hordW hap ha1 hS hSn hker (hψmem y) (hcommh y)
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (torusGroup_le_normalizer_rootSpan hS)] at this
  set Rs := twistedFixedPoints n Φ with hRs
  have hPψ : ∀ i, P i ≤ ψ.range := by
    intro i u hu
    have huR : n * Φ u * n⁻¹ = u := hPR i hu
    set P' : Subgroup (ModGL τ L) := (P i).map (MulAut.conj g0).toMonoidHom with hP'
    have hP'adj : P' ≤ adjointGroup τ L := by
      rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hg0C (hPadj i hv)) (inv_mem hg0C)
    have hP'fix : ∀ w ∈ P', Φ w = w := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : n * Φ v * n⁻¹ = v := hPR i hv
      change Φ (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Φ v * (g0 * n)⁻¹ = g0 * (n * Φ v * n⁻¹) * g0⁻¹ := by group
        _ = g0 * v * g0⁻¹ := by rw [hvR]
    have hPperf : ⁅P i, P i⁆ = P i := Subgroup.isPerfect_iff.1 (hPq i).1
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hPperf]
    have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
    have hPfini : Finite (P i) := hPfin i
    have hP'fin : Finite P' := Finite.of_surjective
      ((MulAut.conj g0).toMonoidHom.subgroupMap (P i))
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective (P i))
    obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
    have hιx' : ι (c * x * c⁻¹) = g0 * h * g0⁻¹ := by
      rw [hψx]
      group
    have huh : u * h = h * u := Subgroup.mem_centralizer_iff.1 hhZ.2 u (hPQ i hu)
    have hcomm' : y' * (c * x * c⁻¹) = (c * x * c⁻¹) * y' := by
      apply hι
      rw [map_mul ι y' (c * x * c⁻¹), map_mul ι (c * x * c⁻¹) y', hy', hιx']
      calc g0 * u * g0⁻¹ * (g0 * h * g0⁻¹) = g0 * (u * h) * g0⁻¹ := by group
        _ = g0 * (h * u) * g0⁻¹ := by rw [huh]
        _ = g0 * h * g0⁻¹ * (g0 * u * g0⁻¹) := by group
    have hyD : c⁻¹ * y' * c ∈ D := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc c⁻¹ * y' * c * x = c⁻¹ * (y' * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y') * c := by rw [hcomm']
        _ = x * (c⁻¹ * y' * c) := by group
    refine ⟨⟨c⁻¹ * y' * c, hyD⟩, ?_⟩
    rw [hψ]
    change g0⁻¹ * ι (c * (c⁻¹ * y' * c) * c⁻¹) * g0 = u
    rw [show c * (c⁻¹ * y' * c) * c⁻¹ = y' by group, hy']
    group
  have hnorm : ∀ i, ∀ d : D, ∀ u ∈ P i, ψ d * u * (ψ d)⁻¹ ∈ P i := fun i d u hu =>
    hPnorm i (ψ d) (hHQ d) (hψfix d) u hu
  have hcent : ∀ d : D, (∀ i, ∀ u ∈ P i, ψ d * u = u * ψ d) → ψ d ∈ Z := fun d hd =>
    hPcent (ψ d) (hHQ d) (hψfix d) hd
  intro V hVn hVs
  exact solvable_normal_cyclic_of_embedding_family ψ hψinj P Z hPψ hPq hnorm hcent V

end CFSG.RankThree.PartOne.KE
