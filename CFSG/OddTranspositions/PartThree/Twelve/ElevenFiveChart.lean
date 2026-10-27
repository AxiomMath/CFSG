module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocalIso
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModel

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {G G' : Type} [Group G] [Group G']

structure FiveLocalModel (D : Set G) (x : G) (k : ℕ) (ε π : Bool) where
  toMulEquiv : Subgroup.closure (commSet D x) ≃* fiveReflectionGroup k ε π
  mem_iff : ∀ y : Subgroup.closure (commSet D x),
    (y : G) ∈ commSet D x ↔
      (toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π

@[expose] def FiveLocalModel.toLocalIso {D : Set G} {x : G} {D' : Set G'} {x' : G'} {k : ℕ}
    {ε π : Bool} (c : FiveLocalModel D x k ε π) (c' : FiveLocalModel D' x' k ε π) :
    LocalIso D x D' x' where
  toMulEquiv := c.toMulEquiv.trans c'.toMulEquiv.symm
  mem_iff y := by
    have h1 := c.mem_iff y
    have h2 := c'.mem_iff (c'.toMulEquiv.symm (c.toMulEquiv y))
    rw [MulEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm

@[expose] def HasHyperplane {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    (c : FiveLocalModel D x k ε π) (s : G) : Prop :=
  ∃ z : Fin (k + 1) → ZMod 5, z ≠ 0 ∧
    (if orderOf (x * s) = 5 then fiveForm k ε z z = 0
      else fiveForm k ε z z ≠ 0 ∧ (IsSquare (fiveForm k ε z z) ↔ π = false)) ∧
    ∀ y : Subgroup.closure (commSet D x), (y : G) ∈ commSet D x →
      (Commute (y : G) s ↔
        ((c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z = z)

@[expose] def FiveHyperplaneData {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    (c : FiveLocalModel D x k ε π) : Prop :=
  ∀ s ∈ D, ¬ Commute s x → HasHyperplane c s

@[expose] def FiveLocalData (D : Set G) (k : ℕ) (ε π : Bool) : Prop :=
  ∀ x ∈ D, Nonempty (FiveLocalModel D x k ε π) ∧
    ∀ c : FiveLocalModel D x k ε π, FiveHyperplaneData c

theorem mem_commSet_conj {D : Set G} (hS : Setup G D) (g x y : G) :
    MulAut.conj g y ∈ commSet D (MulAut.conj g x) ↔ y ∈ commSet D x := by
  simp only [commSet, Set.mem_setOf_eq, MulAut.conj_apply]
  constructor
  · rintro ⟨hyD, hyc, hne⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [mul_assoc] using hS.conj_mem g⁻¹ hyD
    · rwa [← Commute.conj_iff g]
    · intro h; exact hne (by rw [h])
  · rintro ⟨hyD, hyc, hne⟩
    refine ⟨hS.conj_mem g hyD, ?_, ?_⟩
    · rwa [Commute.conj_iff g]
    · intro h; exact hne ((MulAut.conj g).injective h)

@[expose] noncomputable def conjClosureEquiv {D : Set G} (hS : Setup G D) (g x : G) :
    Subgroup.closure (commSet D x) ≃* Subgroup.closure (commSet D (MulAut.conj g x)) :=
  ((MulAut.conj g).subgroupMap (Subgroup.closure (commSet D x))).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, hzy⟩
        rw [← hzy]
        exact (mem_commSet_conj hS g x z).2 hz
      · intro hy
        refine ⟨MulAut.conj g⁻¹ y, ?_, ?_⟩
        · refine (mem_commSet_conj hS g x (MulAut.conj g⁻¹ y)).1 ?_
          rw [show MulAut.conj g (MulAut.conj g⁻¹ y) = y by
            simp [MulAut.conj_apply, mul_assoc]]
          exact hy
        · simp [MulAut.conj_apply, mul_assoc]))

theorem conjClosureEquiv_apply {D : Set G} (hS : Setup G D) (g x : G)
    (z : Subgroup.closure (commSet D x)) :
    (((conjClosureEquiv hS g x z : Subgroup.closure (commSet D (MulAut.conj g x))) : G)) =
      MulAut.conj g (z : G) :=
  rfl

@[expose] noncomputable def FiveLocalModel.congr {D : Set G} {x y : G} {k : ℕ} {ε π : Bool}
    (e : Subgroup.closure (commSet D x) ≃* Subgroup.closure (commSet D y))
    (he : ∀ z : Subgroup.closure (commSet D x),
      ((z : G) ∈ commSet D x ↔ ((e z : Subgroup.closure (commSet D y)) : G) ∈ commSet D y))
    (c : FiveLocalModel D x k ε π) : FiveLocalModel D y k ε π where
  toMulEquiv := e.symm.trans c.toMulEquiv
  mem_iff y' := by
    rw [MulEquiv.trans_apply, ← c.mem_iff]
    simpa using (he (e.symm y')).symm

@[expose] noncomputable def FiveLocalModel.conj {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    (hS : Setup G D) (g : G)
    (c : FiveLocalModel D x k ε π) : FiveLocalModel D (MulAut.conj g x) k ε π :=
  FiveLocalModel.congr (conjClosureEquiv hS g x)
    (fun z => by
      rw [conjClosureEquiv_apply]
      exact (mem_commSet_conj hS g x (z : G)).symm) c

theorem FiveLocalModel.conj_toMulEquiv {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    (hS : Setup G D) (g : G)
    (c : FiveLocalModel D x k ε π) (y' : Subgroup.closure (commSet D (MulAut.conj g x))) :
    ((FiveLocalModel.conj hS g c).toMulEquiv y' : GL (Fin (k + 1)) (ZMod 5)) =
      c.toMulEquiv ((conjClosureEquiv hS g x).symm y') :=
  rfl

theorem hasHyperplane_conj {D : Set G} {x : G} {k : ℕ} {ε π : Bool}
    (hS : Setup G D) (g : G) (c : FiveLocalModel D x k ε π) (s : G) :
    HasHyperplane (FiveLocalModel.conj hS g c) s ↔
      HasHyperplane c (MulAut.conj g⁻¹ s) := by
  have hs : MulAut.conj g (MulAut.conj g⁻¹ s) = s := by
    simp [MulAut.conj_apply, mul_assoc]
  have hord : orderOf (MulAut.conj g x * s) = orderOf (x * MulAut.conj g⁻¹ s) := by
    conv_lhs => rw [← hs, ← map_mul]
    exact MulEquiv.orderOf_eq (MulAut.conj g) (x * MulAut.conj g⁻¹ s)
  constructor
  · rintro ⟨z, hz0, hsign, hcomm⟩
    refine ⟨z, hz0, by simpa only [hord] using hsign, ?_⟩
    intro y hy
    have hy' : (((conjClosureEquiv hS g x y :
        Subgroup.closure (commSet D (MulAut.conj g x))) : G)) ∈
        commSet D (MulAut.conj g x) := by
      rw [conjClosureEquiv_apply]
      exact (mem_commSet_conj hS g x (y : G)).2 hy
    have h := hcomm (conjClosureEquiv hS g x y) hy'
    rw [FiveLocalModel.conj_toMulEquiv, MulEquiv.symm_apply_apply,
      conjClosureEquiv_apply] at h
    have hc : Commute (MulAut.conj g y) s ↔ Commute (y : G) (MulAut.conj g⁻¹ s) := by
      conv_lhs => rw [← hs]
      exact Commute.conj_iff g
    exact hc.symm.trans h
  · rintro ⟨z, hz0, hsign, hcomm⟩
    refine ⟨z, hz0, by simpa only [← hord] using hsign, ?_⟩
    intro y' hy'
    let y : Subgroup.closure (commSet D x) := (conjClosureEquiv hS g x).symm y'
    have hyy' : MulAut.conj g (y : G) = (y' : G) := by
      rw [← conjClosureEquiv_apply hS g x y, MulEquiv.apply_symm_apply]
    have hy : (y : G) ∈ commSet D x := by
      refine (mem_commSet_conj hS g x (y : G)).mp ?_
      rw [hyy']
      exact hy'
    have h := hcomm y hy
    rw [FiveLocalModel.conj_toMulEquiv]
    have hc : Commute (y' : G) s ↔ Commute (y : G) (MulAut.conj g⁻¹ s) := by
      rw [← hyy']
      conv_lhs => rw [← hs]
      exact Commute.conj_iff g
    exact hc.trans h

theorem fiveLocalData_of_pivot {D : Set G} (hS : Setup G D) {k : ℕ} {ε π : Bool} {x₀ : G}
    (hx₀ : x₀ ∈ D) (hne : Nonempty (FiveLocalModel D x₀ k ε π))
    (hhyp : ∀ c : FiveLocalModel D x₀ k ε π, FiveHyperplaneData c) :
    FiveLocalData D k ε π := by
  intro x hx
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hx₀ hx)
  have hgM : MulAut.conj g x₀ = x := by rw [MulAut.conj_apply]; exact hg
  rw [← hgM]
  constructor
  · obtain ⟨c₀⟩ := hne
    exact ⟨FiveLocalModel.conj hS g c₀⟩
  · intro c s hs hnc
    let e := conjClosureEquiv hS g x₀
    let c₀ : FiveLocalModel D x₀ k ε π :=
      { toMulEquiv := e.trans c.toMulEquiv
        mem_iff := fun y => by
          rw [MulEquiv.trans_apply, ← c.mem_iff]
          have hye : (((e y : Subgroup.closure (commSet D (MulAut.conj g x₀))) : G)) ∈
              commSet D (MulAut.conj g x₀) ↔ (y : G) ∈ commSet D x₀ := by
            rw [conjClosureEquiv_apply]
            exact mem_commSet_conj (D := D) hS g x₀ (y : G)
          exact hye.symm }
    have hs' : MulAut.conj g⁻¹ s ∈ D := by
      simpa only [MulAut.conj_apply, inv_inv] using hS.conj_mem g⁻¹ hs
    have hnc' : ¬ Commute (MulAut.conj g⁻¹ s) x₀ := by
      intro hc
      have h2 : Commute (MulAut.conj g (MulAut.conj g⁻¹ s)) (MulAut.conj g x₀) :=
        (Commute.conj_iff g).mpr hc
      have h3 : MulAut.conj g (MulAut.conj g⁻¹ s) = s := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [h3] at h2
      exact hnc h2
    have h₀ : HasHyperplane c₀ (MulAut.conj g⁻¹ s) :=
      hhyp c₀ (MulAut.conj g⁻¹ s) hs' hnc'
    have hconj : HasHyperplane (FiveLocalModel.conj hS g c₀) s :=
      (hasHyperplane_conj hS g c₀ s).mpr h₀
    have hto : (FiveLocalModel.conj hS g c₀).toMulEquiv = c.toMulEquiv := by
      ext y'
      simp only [FiveLocalModel.conj, FiveLocalModel.congr, c₀, e, MulEquiv.trans_apply,
        MulEquiv.apply_symm_apply]
    unfold HasHyperplane at hconj ⊢
    rw [hto] at hconj
    exact hconj

@[expose] def fiveProjClass (n : ℕ) (ε π : Bool) : Set (fiveProjective n ε π) :=
  {x | ∃ r : fiveReflectionGroup n ε π,
    (r : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π ∧
      (QuotientGroup.mk r : fiveProjective n ε π) = x}

theorem isFiveReflectionModel_iff_proj {n : ℕ} {ε π : Bool} {D : Set G} :
    IsFiveReflectionModel n ε π D ↔
      ∃ φ : G ≃* fiveProjective n ε π, ∀ g, g ∈ D ↔ φ g ∈ fiveProjClass n ε π := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g => ?_⟩
    rw [hφ g]
    constructor
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, e.symm⟩
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, e.symm⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, fun g => ?_⟩
    rw [hφ g]
    constructor
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, e.symm⟩
    · rintro ⟨h, hh, e⟩
      exact ⟨h, hh, e.symm⟩

end CFSG.OddTranspositions.PartThree

end
