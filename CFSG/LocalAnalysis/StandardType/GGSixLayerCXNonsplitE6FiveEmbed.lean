module

public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1Untwisted
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.StandardType.E6Nonsplit

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Pointwise

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

theorem a1_centralizer_structure
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
    (hS3 : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∀ x : C, orderOf x = p →
      (CFSG.IsQuasisimple S →
        ∃ (ψ : ↥(Subgroup.centralizer ({x} : Set C)) →* ModGL τ L) (P Z : Subgroup (ModGL τ L)),
          Function.Injective ψ ∧ Nonempty (↥S ≃* ↥P) ∧ P ≤ ψ.range ∧
          (∀ d : ↥(Subgroup.centralizer ({x} : Set C)), ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) ∧
          (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧
          (∀ d : ↥(Subgroup.centralizer ({x} : Set C)),
            (∀ u ∈ P, ψ d * u = u * ψ d) → ψ d ∈ Z)) ∧
      (Group.IsSolvable S → Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set C))) := by
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
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => by
    have := (IsCyclic.commGroup : CommGroup ↥Z).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hPψ : CFSG.IsQuasisimple S → P ≤ ψ.range := by
    intro hS2
    have hPq : CFSG.IsQuasisimple P := CFSG.LocalCores.isQuasisimple_of_mulEquiv hPe hS2
    have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 hPq.1
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
  refine ⟨fun hS2 => ⟨ψ, P, Z, hψinj, ⟨hPe⟩, hPψ hS2, hnorm, hZcomm, hcent⟩, fun hSsol => ?_⟩
  have hPsol : Group.IsSolvable P := by
    haveI := hSsol
    exact Group.isSolvable_of_isSolvable_injective (f := hPe.symm.toMonoidHom) hPe.symm.injective
  set PD : Subgroup D := P.comap ψ with hPD
  haveI hPDsol : Group.IsSolvable PD := by
    haveI := hPsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (ψ.comp PD.subtype).codRestrict P (fun y => y.2)) (fun a b hab =>
        Subtype.ext (hψinj (congrArg Subtype.val hab)))
  have hHle : H ≤ Subgroup.normalizer (Q : Set (ModGL τ L)) :=
    torusGroup_le_normalizer_rootRankOneGroup hθ
  have hMle : H ⊔ Q ≤ Subgroup.normalizer (Q : Set (ModGL τ L)) :=
    sup_le hHle Subgroup.le_normalizer
  have hmemM : ∀ m : ModGL τ L, m ∈ H ⊔ Q → ∃ a ∈ H, ∃ b ∈ Q, a * b = m := fun m hm => by
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHle] at hm
    exact hm
  have hψM : ∀ y : D, ψ y ∈ H ⊔ Q := fun y => by
    have := hHQ y
    rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHle] at this
  haveI : (Q.subgroupOf (H ⊔ Q)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hMle
  let g : D →* (H ⊔ Q : Subgroup (ModGL τ L)) ⧸ Q.subgroupOf (H ⊔ Q) :=
    (QuotientGroup.mk' (Q.subgroupOf (H ⊔ Q))).comp (ψ.codRestrict (H ⊔ Q) hψM)
  have hcommq : ∀ u v : (H ⊔ Q : Subgroup (ModGL τ L)) ⧸ Q.subgroupOf (H ⊔ Q), u * v = v * u := by
    have hrep : ∀ u : (H ⊔ Q : Subgroup (ModGL τ L)) ⧸ Q.subgroupOf (H ⊔ Q),
        ∃ (a : ModGL τ L) (ha : a ∈ H),
          u = QuotientGroup.mk (⟨a, (le_sup_left : H ≤ H ⊔ Q) ha⟩ : (H ⊔ Q : Subgroup (ModGL τ L))) := by
      intro u
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨a, ha, b, hb, hab⟩ := hmemM m m.2
      refine ⟨a, ha, ?_⟩
      rw [eq_comm, QuotientGroup.eq]
      show ((a⁻¹ * (m : ModGL τ L) : ModGL τ L)) ∈ Q
      rw [← hab, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hb
    intro u v
    obtain ⟨a, ha, rfl⟩ := hrep u
    obtain ⟨a', ha', rfl⟩ := hrep v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (torusGroup_comm ha ha')
  haveI : Group.IsSolvable ((H ⊔ Q : Subgroup (ModGL τ L)) ⧸ Q.subgroupOf (H ⊔ Q)) :=
    Group.isSolvable_of_comm hcommq
  have hker : g.ker ≤ PD.subtype.range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (⟨ψ y, hψM y⟩ : (H ⊔ Q : Subgroup (ModGL τ L))) ∈ Q.subgroupOf (H ⊔ Q) :=
      (QuotientGroup.eq_one_iff _).1 hy
    have h2 : ψ y ∈ Q := h1
    rw [Subgroup.range_subtype]
    exact ⟨h2, hψfix y⟩
  exact Group.isSolvable_of_ker_le_range PD.subtype g hker

end CFSG.StandardType.E6Nonsplit
