module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open scoped commutatorElement

section Quot

variable {A B : Type} [Group A] [Group B] [Finite A]

theorem map_pCore_two_le (f : A →* B) (hf : Function.Surjective f) :
    (CFSG.pCore 2 A).map f ≤ CFSG.pCore 2 B := by
  apply le_sSup
  refine ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
  exact (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 A)).map f

theorem comap_pCore_two_le (f : A →* B) (hker : IsPGroup 2 f.ker) :
    (CFSG.pCore 2 B).comap f ≤ CFSG.pCore 2 A := by
  apply le_sSup
  refine ⟨Subgroup.Normal.comap inferInstance f, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 B)) f
    hker

theorem isType429_quot_of_surjective (f : A →* B) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (h : IsType429 (B ⧸ CFSG.pCore 2 B)) :
    IsType429 (A ⧸ CFSG.pCore 2 A) := by
  set g : A →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp f
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hkerg : g.ker = CFSG.pCore 2 A := by
    have hk : g.ker = (CFSG.pCore 2 B).comap f := by
      ext a
      simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [hk]
    refine le_antisymm (comap_pCore_two_le f hker) ?_
    intro a ha
    exact map_pCore_two_le f hf ⟨a, ha, rfl⟩
  have e : A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B :=
    (QuotientGroup.quotientMulEquivOfEq hkerg.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  exact isType429_congr e.symm h

end Quot

section Central

variable {G G' : Type} [Group G] [Group G'] [Finite G]

theorem commutatorElement_mul_central {a b z w : G} (hz : z ∈ Subgroup.center G)
    (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have hzy : ∀ y : G, z * y * z⁻¹ = y := fun y => by rw [← hz' y, mul_inv_cancel_right]
  have hwg : ∀ g : G, g * w * g⁻¹ = w := fun g => by rw [hw' g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * a⁻¹ * (a * w * a⁻¹) * (b * w)⁻¹ := by rw [hzy]; group
    _ = ⁅a, b⁆ := by rw [hwg a, commutatorElement_def]; group

theorem Good429.map_of_central (φ : G →* G') (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center G) (h2 : IsPGroup 2 φ.ker) {C : Subgroup G}
    (hC : φ.ker ≤ C) (h : Good429 C) : Good429 (C.map φ) := by
  intro K hKC hKp hKs hT
  haveI := hKp
  set Kt : Subgroup G := K.comap φ with hKt
  have hKtC : Kt ≤ C := by
    intro x hx
    obtain ⟨y, hyC, hy⟩ := hKC hx
    have : y⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
    have := C.mul_mem hyC (hC this)
    simpa using this
  have hmapKt : Kt.map φ = K := Subgroup.map_comap_eq_self_of_surjective hφ K
  set K1 : Subgroup G := ⁅Kt, Kt⁆ with hK1
  have hK1Kt : K1 ≤ Kt := Subgroup.commutator_le_self Kt
  have hmapK1 : K1.map φ = K := by
    rw [hK1, Subgroup.map_commutator, hmapKt]
    exact Subgroup.commutator_eq_self
  have hKtsup : ∀ x ∈ Kt, ∃ y ∈ K1, ∃ z ∈ φ.ker, x = y * z := by
    intro x hx
    have hφx : φ x ∈ K1.map φ := by rw [hmapK1]; exact hx
    obtain ⟨y, hy, hyx⟩ := hφx
    refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  haveI hK1p : Group.IsPerfect K1 := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le_self K1) ?_
    rw [hK1, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨a1, ha1, z, hz, rfl⟩ := hKtsup a ha
    obtain ⟨b1, hb1, w, hw, rfl⟩ := hKtsup b hb
    rw [commutatorElement_mul_central (hZ hz) (hZ hw)]
    exact Subgroup.commutator_mem_commutator ha1 hb1
  have hKts : (Kt.subgroupOf C).IsSubnormal := by
    set ψ : C →* C.map φ := φ.subgroupMap C
    have hcomap : (K.subgroupOf (C.map φ)).comap ψ = Kt.subgroupOf C := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hKt]
      rfl
    rw [← hcomap]
    exact hKs.comap ψ
  have hK1s : (K1.subgroupOf C).IsSubnormal := by
    have hle : K1.subgroupOf C ≤ Kt.subgroupOf C := fun x hx => hK1Kt hx
    refine Subgroup.IsSubnormal.trans hle ?_ hKts
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g : Kt.subgroupOf C) : C) ∈ Kt.subgroupOf C := g.2
    rw [Subgroup.mem_subgroupOf] at hg
    have hnKt : (((n : Kt.subgroupOf C) : C) : G) ∈ Kt := hK1Kt hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e : ((g : C) : G) * ((n : C) : G) * ((g : C) : G)⁻¹ =
        ⁅((g : C) : G), ((n : C) : G)⁆ * ((n : C) : G) := by
      rw [commutatorElement_def]; group
    rw [e]
    exact K1.mul_mem (Subgroup.commutator_mem_commutator hg hnKt) hn
  have hT1 : IsType429 (K1 ⧸ CFSG.pCore 2 K1) := by
    let f : K1 →* K := (φ.comp K1.subtype).codRestrict K (fun x => by
      have : φ x ∈ K1.map φ := ⟨x, x.2, rfl⟩
      rw [hmapK1] at this
      exact this)
    have hf : Function.Surjective f := by
      intro k
      have hk : (k : G') ∈ K1.map φ := by rw [hmapK1]; exact k.2
      obtain ⟨y, hy, hyk⟩ := hk
      exact ⟨⟨y, hy⟩, Subtype.ext hyk⟩
    have hker : IsPGroup 2 f.ker := by
      let ι : f.ker →* φ.ker := (K1.subtype.comp f.ker.subtype).codRestrict φ.ker (fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        exact congrArg Subtype.val hx)
      refine IsPGroup.of_injective h2 ι ?_
      intro x y hxy
      have h' := congrArg (fun t : φ.ker => (t : G)) hxy
      exact Subtype.ext (Subtype.ext h')
    exact isType429_quot_of_surjective f hf hker hT
  exact h K1 (hK1Kt.trans hKtC) hK1p hK1s hT1

end Central

section Conj

variable {S : Type} [Group S]

theorem Good429.conj_of_normalizes {P : Subgroup S} {x k : S}
    (hk : ∀ g : S, g ∈ P ↔ k * g * k⁻¹ ∈ P)
    (h : Good429 (Subgroup.centralizer ({x} : Set S) ⊓ P)) :
    Good429 (Subgroup.centralizer ({k * x * k⁻¹} : Set S) ⊓ P) := by
  have hmap : (Subgroup.centralizer ({x} : Set S) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * x * k⁻¹} : Set S) ⊓ P := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
      refine ⟨?_, (hk z).mp hzP⟩
      calc k * z * k⁻¹ * (k * x * k⁻¹) = k * (z * x) * k⁻¹ := by group
        _ = k * (x * z) * k⁻¹ := by rw [hzc]
        _ = k * x * k⁻¹ * (k * z * k⁻¹) := by group
    · rintro ⟨hwc, hwP⟩
      refine ⟨k⁻¹ * w * k, ⟨?_, (hk _).mpr (by simpa [mul_assoc] using hwP)⟩, by group⟩
      calc k⁻¹ * w * k * x = k⁻¹ * (w * (k * x * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * x * k⁻¹) * w) * k := by rw [hwc]
        _ = x * (k⁻¹ * w * k) := by group
  rw [← hmap]
  exact h.map_mulEquiv (MulAut.conj k)

end Conj

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
