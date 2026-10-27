module

public import CFSG.RankThree.PartOne.KE.A1Quasi
public import CFSG.RankThree.PartOne.KE.A1Rank
public import CFSG.RankThree.PartOne.KE.CTSubtorus
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers
public import CFSG.RankThree.PartOne.KE.A1Centralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

@[expose] def twistedFixedPoints (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L) :
    Subgroup (ModGL τ L) :=
  ((MulAut.conj n).toMonoidHom.comp Φ).eqLocus (MonoidHom.id _)

theorem mem_twistedFixedPoints {n : ModGL τ L} {Φ : ModGL τ L →* ModGL τ L} {u : ModGL τ L} :
    u ∈ twistedFixedPoints n Φ ↔ n * Φ u * n⁻¹ = u :=
  Iff.rfl

@[expose] def subtorusA1 (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    (θ : Fin τ.rank → ℤ) : Subgroup (ModGL τ L) :=
  twistedTorusOf n Φ ⊓ Subgroup.centralizer (rootRankOneGroup τ L θ : Set (ModGL τ L))

theorem subtorusA1_le_twistedTorusOf (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    (θ : Fin τ.rank → ℤ) : subtorusA1 n Φ θ ≤ twistedTorusOf n Φ :=
  inf_le_left


theorem a1_solvable_normal_cyclic
    (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hιC : ∀ y, ι y ∈ adjointGroup τ L)
    (Φ : ModGL τ L →* ModGL τ L) (hιΦ : ∀ y, Φ (ι y) = ι y) (n g0 : ModGL τ L)
    (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    {p : ℕ} (hp : p.Prime) (hordW : ¬ p ∣ Nat.card (WeylGroup τ))
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) [hZ : IsCyclic (subtorusA1 n Φ θ)]
    (hconj : ∀ x : C, orderOf x = p →
      ∃ c : C, c * x * c⁻¹ ∈ subtorusImage ι g0 (subtorusA1 n Φ θ))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ subtorusA1 n Φ θ →
      orderOf (rootDiagUnit τ a) = p → rootCharKernel a ⊆ {θ, -θ})
    (S : Subgroup (SL2 L)) [hSfin : Finite S]
    (hS1 : ∀ B : SL2 L, n * Φ (rootSL2 τ L θ B) * n⁻¹ = rootSL2 τ L θ B ↔ B ∈ S)
    (hS2 : CFSG.IsQuasisimple S)
    (hS3 : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∀ x : C, orderOf x = p → ∀ V : Subgroup (Subgroup.centralizer ({x} : Set C)),
      V.Normal → Group.IsSolvable V → IsCyclic V := by
  intro x hx
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hconj x hx
  set Z := subtorusA1 n Φ θ with hZdef
  set Q := rootRankOneGroup τ L θ with hQdef
  set H := torusGroup τ L with hHdef
  set ρ := rootSL2 τ L θ with hρdef
  have hρinj : Function.Injective ρ := rootSL2_injective_of_field θ
  have hρadj : ∀ A, ρ A ∈ adjointGroup τ L :=
    (exceptional_Lang_root_rank_one_data τ L θ).2.2.2.2.1
  have hQrange : ∀ u ∈ Q, ∃ B, ρ B = u := fun u hu => MonoidHom.mem_range.1 hu
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
  have hHh : h ∈ H := (mem_twistedTorusOf.1 (subtorusA1_le_twistedTorusOf n Φ θ hhZ)).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hHh
  have hord' : orderOf (rootDiagUnit τ a) = p := by rw [← ha]; exact hordh
  have hap := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hker := hkerZ a (by rw [← ha]; exact hhZ) hord'
  have hcommh : ∀ y : D, ψ y * rootDiagUnit τ a = rootDiagUnit τ a * ψ y := fun y => by
    rw [← ha, hh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hHQ : ∀ y : D, ψ y ∈ (H : Set (ModGL τ L)) * (Q : Set (ModGL τ L)) := fun y =>
    mem_torus_mul_rootRankOne_of_commute hp hordW hap ha1 hθ hker (hψmem y) (hcommh y)
  have hnormQ : ∀ y : D, ∀ u ∈ Q, ψ y * u * (ψ y)⁻¹ ∈ Q := by
    intro y u hu
    have hy : ψ y ∈ H ⊔ Q := by
      have := hHQ y
      rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (torusGroup_le_normalizer_rootRankOneGroup hθ)] at this
    have hle : H ⊔ Q ≤ Subgroup.normalizer (Q : Set (ModGL τ L)) :=
      sup_le (torusGroup_le_normalizer_rootRankOneGroup hθ) Subgroup.le_normalizer
    exact ((Subgroup.mem_normalizer_iff.1 (hle hy)) u).1 hu
  set Rs := twistedFixedPoints n Φ with hRs
  set P : Subgroup (ModGL τ L) := Q ⊓ Rs with hPdef
  have hPS : P = S.map ρ := by
    ext u
    constructor
    · rintro ⟨hu, hu2⟩
      obtain ⟨B, rfl⟩ := hQrange u hu
      exact ⟨B, (hS1 B).1 hu2, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨⟨B, rfl⟩, (hS1 B).2 hB⟩
  have hPe : S ≃* P :=
    (Subgroup.equivMapOfInjective S ρ hρinj).trans (MulEquiv.subgroupCongr hPS.symm)
  have hPq : CFSG.IsQuasisimple P := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hS2
  have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hPq.1
  have hPψ : P ≤ ψ.range := by
    intro u hu
    have huR : n * Φ u * n⁻¹ = u := hu.2
    set P' : Subgroup (ModGL τ L) := P.map (MulAut.conj g0).toMonoidHom with hP'
    have hP'adj : P' ≤ adjointGroup τ L := by
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨B, rfl⟩ := hQrange v hv.1
      exact mul_mem (mul_mem hg0C (hρadj B)) (inv_mem hg0C)
    have hP'fix : ∀ w ∈ P', Φ w = w := by
      rintro _ ⟨v, hv, rfl⟩
      have hvR : n * Φ v * n⁻¹ = v := hv.2
      change Φ (g0 * v * g0⁻¹) = g0 * v * g0⁻¹
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * n * Φ v * (g0 * n)⁻¹ = g0 * (n * Φ v * n⁻¹) * g0⁻¹ := by group
        _ = g0 * v * g0⁻¹ := by rw [hvR]
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hPperf]
    have hmem : g0 * u * g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hu
    have hPfin : Finite P := Finite.of_equiv S hPe.toEquiv
    have hP'fin : Finite P' := Finite.of_surjective
      ((MulAut.conj g0).toMonoidHom.subgroupMap P)
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective P)
    obtain ⟨y', hy'⟩ := hperf P' hP'fin hP'adj hP'fix hP'perf hmem
    have hιx' : ι (c * x * c⁻¹) = g0 * h * g0⁻¹ := by
      rw [hψx]
      group
    have huh : u * h = h * u := Subgroup.mem_centralizer_iff.1 hhZ.2 u hu.1
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
  have hnorm : ∀ d : D, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P := by
    intro d u hu
    have hd : ψ d ∈ Rs := hψfix d
    have hu2 : u ∈ Rs := hu.2
    have h3 : ψ d * u * (ψ d)⁻¹ ∈ Rs := mul_mem (mul_mem hd hu2) (inv_mem hd)
    exact ⟨hnormQ d u hu.1, h3⟩
  have hcent : ∀ d : D, (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z := by
    intro d hd
    have hQc : ∀ A : SL2 L, ψ d * ρ A = ρ A * ψ d :=
      commute_rootSL2_of_commute_fixed hθ hS3 (hHQ d)
        (fun A hA => hd _ (by rw [hPS]; exact ⟨A, hA, rfl⟩))
    have hHd : ψ d ∈ H := mem_torusGroup_of_centralizes_rootSL2 hθ (hHQ d) hQc
    have hcZ : ψ d ∈ Subgroup.centralizer (Q : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨A, rfl⟩
      exact (hQc A).symm
    exact ⟨mem_twistedTorusOf.2 ⟨hHd, hψfix d⟩, hcZ⟩
  intro V hVn hVs
  exact solvable_normal_cyclic_of_embedding ψ hψinj P Z hPψ hPq hnorm hcent V

end CFSG.RankThree.PartOne.KE
