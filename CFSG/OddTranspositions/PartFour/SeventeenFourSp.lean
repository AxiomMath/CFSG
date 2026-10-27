module

public import CFSG.OddTranspositions.PartFour.SeventeenFourPolar
public import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.OddTranspositions.WidthSylow
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem perpMem_image_mulEquiv (φ : X ≃* Y) (S : Set X) (u : X) :
    perpMem (φ '' S) (φ u) = φ '' perpMem S u := by
  ext y
  constructor
  · rintro ⟨⟨x, hxS, rfl⟩, hcomm⟩
    refine ⟨x, ?_, rfl⟩
    rw [mem_perpMem]
    refine ⟨hxS, ?_⟩
    apply φ.injective
    rw [map_mul, map_mul]
    exact hcomm
  · rintro ⟨x, hx, rfl⟩
    rw [mem_perpMem] at hx ⊢
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    change φ x * φ u = φ u * φ x
    rw [← map_mul, ← map_mul, hx.2]

theorem lineMem_image_mulEquiv (φ : X ≃* Y) (S : Set X) (v w : X) :
    lineMem (φ '' S) (φ v) (φ w) = φ '' lineMem S v w := by
  ext y
  constructor
  · intro hy
    rw [mem_lineMem] at hy
    obtain ⟨⟨x, hxS, rfl⟩, hsub⟩ := hy
    refine ⟨x, ?_, rfl⟩
    rw [mem_lineMem]
    refine ⟨hxS, ?_⟩
    refine (Set.image_subset_image_iff φ.injective).mp ?_
    rw [Set.image_inter φ.injective]
    simpa only [perpMem_image_mulEquiv] using hsub
  · rintro ⟨x, hx, rfl⟩
    rw [mem_lineMem] at hx ⊢
    obtain ⟨hxS, hsub⟩ := hx
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    have h2 : φ '' (perpMem S v ∩ perpMem S w) ⊆ φ '' perpMem S x :=
      (Set.image_subset_image_iff φ.injective).mpr hsub
    simpa only [Set.image_inter φ.injective, perpMem_image_mulEquiv] using h2

theorem ncard_perpMem_image_lineMem_mulEquiv (φ : X ≃* Y) (S : Set X) (v w : X) :
    (perpMem (φ '' S) '' lineMem (φ '' S) (φ v) (φ w)).ncard =
      (perpMem S '' lineMem S v w).ncard := by
  have hset : perpMem (φ '' S) '' lineMem (φ '' S) (φ v) (φ w) =
      Set.image (Set.image φ) (perpMem S '' lineMem S v w) := by
    rw [lineMem_image_mulEquiv]
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨perpMem S z, ⟨z, hz, rfl⟩, (perpMem_image_mulEquiv φ S z).symm⟩
    · rintro ⟨A, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨φ z, ⟨z, hz, rfl⟩, perpMem_image_mulEquiv φ S z⟩
  rw [hset]
  exact Set.ncard_image_of_injective _ (Set.image_injective.mpr φ.injective)

end Transport

theorem exists_lineMem_ncard_le_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {k f : ℕ} (hk : 2 ≤ k)
    (hs : IsSymplecticTransvection X (2 * k) f s) :
    ∃ v ∈ {x | IsConj s x}, ∃ w ∈ {x | IsConj s x}, Commute v w ∧
      perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w ∧
      (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 ^ f + 1 := by
  obtain ⟨k', hk', F, hF, hFfin, hFcard, e, he⟩ := hs
  obtain rfl : k' = k := by omega
  haveI : Finite F := hFfin
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : X, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  let t₀ := e (QuotientGroup.mk s)
  have ht : IsSymplecticTransvectionIn k' t₀ := by simpa [t₀] using he
  obtain ⟨v', hv', w', hw', hvw', hne', hcount'⟩ :=
    exists_lineMem_ncard_le_of_isSymplecticTransvectionIn hk ht
  let v : X := φ.symm v'
  let w : X := φ.symm w'
  have hφv : φ v = v' := φ.apply_symm_apply v'
  have hφw : φ w = w' := φ.apply_symm_apply w'
  have hclass : φ '' {x | IsConj s x} = {x | IsConj t₀ x} := by
    dsimp only [t₀]
    rw [← hφ]
    exact CFSG.Fischer.image_setOf_isConj φ s
  have hclass' : φ.symm '' {x | IsConj t₀ x} = {x | IsConj s x} := by
    dsimp only [t₀]
    rw [← hφ]
    simpa using CFSG.Fischer.image_setOf_isConj φ.symm (φ s)
  have hv : v ∈ {x | IsConj s x} := by obtain ⟨u, hu, rfl⟩ := hclass.symm ▸ hv'; simpa [v] using hu
  have hw : w ∈ {x | IsConj s x} := by obtain ⟨u, hu, rfl⟩ := hclass.symm ▸ hw'; simpa [w] using hu
  have hvw : Commute v w := by simpa [v, w] using hvw'.map φ.symm.toMonoidHom
  have hne : perpMem {x | IsConj s x} v ≠ perpMem {x | IsConj s x} w := by
    intro h
    apply hne'
    have hV : perpMem {x | IsConj s x} v = φ.symm '' perpMem {x | IsConj t₀ x} v' := by
      rw [← hφv, ← hclass, perpMem_image_mulEquiv]
      exact (CFSG.Fischer.image_symm_image φ (perpMem {x | IsConj s x} v)).symm
    have hW : perpMem {x | IsConj s x} w = φ.symm '' perpMem {x | IsConj t₀ x} w' := by
      rw [← hφw, ← hclass, perpMem_image_mulEquiv]
      exact (CFSG.Fischer.image_symm_image φ (perpMem {x | IsConj s x} w)).symm
    exact (Set.image_injective.mpr φ.symm.injective) (by rw [← hV, ← hW]; exact h)
  have hcount : (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard ≤ 2 ^ f + 1 := by
    have hEq := ncard_perpMem_image_lineMem_mulEquiv φ.symm {x | IsConj t₀ x} v' w'
    rw [hclass'] at hEq
    calc (perpMem {x | IsConj s x} '' lineMem {x | IsConj s x} v w).ncard
        = (perpMem {x | IsConj t₀ x} '' lineMem {x | IsConj t₀ x} v' w').ncard := hEq
      _ ≤ Nat.card F + 1 := hcount'
      _ = 2 ^ f + 1 := by rw [hFcard]
  exact ⟨v, hv, w, hw, hvw, hne, hcount⟩

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem center_eq_bot_quotient_H (hC : HypothesisC D) :
    Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ :=
  center_eq_bot_of_solvableRadical_eq_bot (solvableRadical_quotient_H hC)

theorem imageClass_eq_setOf_isConj (hC : HypothesisC D)
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC) :
    imageClass hC = {x | IsConj s x} := by
  obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
  rw [hd₀] at hs ⊢
  ext x
  constructor
  · intro hx
    exact hs.symm.trans hx
  · intro hx
    exact hs.trans hx

theorem blockLine_eq_insert_orbit_of_isSymplecticTransvection (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {k f : ℕ} (hk : 2 ≤ k)
    (hsp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (2 * k) f s)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hm : 2 ^ f ≤ ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard) :
    blockLine D hC.alpha β =
        insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)) ∧
      ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G)).ncard = 2 ^ f := by
  obtain ⟨v, hv, w, hw, hvw, hne, hcount⟩ :=
    exists_lineMem_ncard_le_of_isSymplecticTransvection
      (center_eq_bot_quotient_H hC) hk hsp
  rw [← imageClass_eq_setOf_isConj hC hs] at hv hw hne hcount
  exact blockLine_eq_insert_orbit_of_ncard_le h89 h113 hC hrad hW hn3 hMZ hHns
    hv hw hvw hne hcount hβ hm

end CFSG.OddTranspositions.PartFour
