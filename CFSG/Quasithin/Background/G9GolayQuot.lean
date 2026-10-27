module

public import CFSG.Quasithin.Background.G9GolayCorr

public section

namespace CFSG.Quasithin.G11

theorem exists_golay_quotientMap {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {T : Equiv.Perm (Fin 24)} {numS denS : Submodule (ZMod 2) GolayAmbient}
    {numer denom : Subgroup (G6.PermMod 24)} (hnum : GolayCorr T numS numer)
    (hden : GolayCorr T denS denom)
    (β : ↥(⊤ : Subgroup (Multiplicative V)) →* ↥numer ⧸ denom.subgroupOf numer)
    (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥(⊤ : Subgroup (Multiplicative V)),
      β u = 1 ↔ (u : Multiplicative V) ∈ (⊥ : Subgroup (Multiplicative V))) :
    ∃ q : ↥numS →ₗ[ZMod 2] V, Function.Surjective q ∧
      (∀ w : ↥numS, q w = 0 ↔ (w : GolayAmbient) ∈ denS) ∧
      ∀ w : ↥numS, β ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨Multiplicative.ofAdd (permAct T (w : GolayAmbient)), (hnum w).1 w.2⟩ := by
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e : ↥(⊤ : Subgroup (Multiplicative V)) ≃* (↥numer ⧸ denom.subgroupOf numer) :=
    MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  let f : ↥numS →+ V :=
    { toFun := fun w => Multiplicative.toAdd
        (((e.symm (QuotientGroup.mk
          ⟨Multiplicative.ofAdd (permAct T (w : GolayAmbient)), (hnum w).1 w.2⟩)) :
            ↥(⊤ : Subgroup (Multiplicative V))) : Multiplicative V)
      map_zero' := by
        let z : ↥numer := ⟨Multiplicative.ofAdd (permAct T ((0 : ↥numS) : GolayAmbient)),
          (hnum (0 : ↥numS)).1 (0 : ↥numS).2⟩
        change Multiplicative.toAdd
          (((e.symm (QuotientGroup.mk z)) : ↥(⊤ : Subgroup (Multiplicative V))) :
            Multiplicative V) = 0
        have hz : z = 1 := by
          apply Subtype.ext
          change Multiplicative.ofAdd (permAct T ((0 : ↥numS) : GolayAmbient)) = 1
          rw [show permAct T ((0 : ↥numS) : GolayAmbient) = (0 : GolayAmbient) from
            golay_permAct_zero T, ofAdd_zero]
        rw [hz, QuotientGroup.mk_one, map_one (e.symm)]
        simp only [Subgroup.coe_one, toAdd_one]
      map_add' := by
        intro w₁ w₂
        let a : ↥numer := ⟨Multiplicative.ofAdd (permAct T (w₁ : GolayAmbient)),
          (hnum w₁).1 w₁.2⟩
        let b : ↥numer := ⟨Multiplicative.ofAdd (permAct T (w₂ : GolayAmbient)),
          (hnum w₂).1 w₂.2⟩
        let c : ↥numer := ⟨Multiplicative.ofAdd
          (permAct T ((w₁ + w₂ : ↥numS) : GolayAmbient)),
          (hnum (w₁ + w₂)).1 (w₁ + w₂).2⟩
        change Multiplicative.toAdd
            (((e.symm (QuotientGroup.mk c)) : ↥(⊤ : Subgroup (Multiplicative V))) :
              Multiplicative V) =
          Multiplicative.toAdd
              (((e.symm (QuotientGroup.mk a)) : ↥(⊤ : Subgroup (Multiplicative V))) :
                Multiplicative V) +
          Multiplicative.toAdd
              (((e.symm (QuotientGroup.mk b)) : ↥(⊤ : Subgroup (Multiplicative V))) :
                Multiplicative V)
        have hc : c = a * b := by
          apply Subtype.ext
          change Multiplicative.ofAdd (permAct T ((w₁ + w₂ : ↥numS) : GolayAmbient)) =
            Multiplicative.ofAdd (permAct T (w₁ : GolayAmbient)) *
              Multiplicative.ofAdd (permAct T (w₂ : GolayAmbient))
          rw [show permAct T ((w₁ + w₂ : ↥numS) : GolayAmbient) =
              permAct T (w₁ : GolayAmbient) + permAct T (w₂ : GolayAmbient) from
            golay_permAct_add T (w₁ : GolayAmbient) (w₂ : GolayAmbient), ofAdd_add]
        rw [hc, QuotientGroup.mk_mul, map_mul (e.symm), Subgroup.coe_mul, toAdd_mul] }
  let q : ↥numS →ₗ[ZMod 2] V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro c x
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl <;> simp }
  have hβq : ∀ w : ↥numS, β ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ =
      QuotientGroup.mk ⟨Multiplicative.ofAdd (permAct T (w : GolayAmbient)), (hnum w).1 w.2⟩ := by
    intro w
    let y : ↥numer := ⟨Multiplicative.ofAdd (permAct T (w : GolayAmbient)), (hnum w).1 w.2⟩
    have hx : (⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Multiplicative V))) = e.symm (QuotientGroup.mk y) := by
      apply Subtype.ext
      change Multiplicative.ofAdd (q w) =
        ((e.symm (QuotientGroup.mk y)) : Multiplicative V)
      exact ofAdd_toAdd _
    calc β ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩
        = e ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ :=
          (MulEquiv.ofBijective_apply β ⟨hβinj, hβs⟩ _).symm
      _ = e (e.symm (QuotientGroup.mk y)) := by rw [hx]
      _ = QuotientGroup.mk y := MulEquiv.apply_symm_apply e _
  have hsurj : Function.Surjective q := by
    intro v
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective
      (β ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩)
    let w : GolayAmbient := permAct T⁻¹ (Multiplicative.toAdd (m : G6.PermMod 24))
    have hperm : permAct T w = Multiplicative.toAdd (m : G6.PermMod 24) :=
      golay_permAct_inv_cancel T _
    have hmem : w ∈ numS := by
      apply (hnum w).2
      rw [hperm, ofAdd_toAdd]
      exact m.2
    refine ⟨⟨w, hmem⟩, ?_⟩
    have hkey : β ⟨Multiplicative.ofAdd (q ⟨w, hmem⟩), Subgroup.mem_top _⟩ =
        β ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ := by
      rw [hβq ⟨w, hmem⟩]
      have hmy : (⟨Multiplicative.ofAdd
          (permAct T ((⟨w, hmem⟩ : ↥numS) : GolayAmbient)),
          (hnum (⟨w, hmem⟩ : ↥numS)).1 (⟨w, hmem⟩ : ↥numS).2⟩ : ↥numer) = m := by
        apply Subtype.ext
        change Multiplicative.ofAdd (permAct T w) = (m : G6.PermMod 24)
        rw [hperm, ofAdd_toAdd]
      rw [hmy, hm]
    have heq : (⟨Multiplicative.ofAdd (q ⟨w, hmem⟩), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Multiplicative V))) =
        ⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ :=
      hβinj hkey
    have hval : Multiplicative.ofAdd (q ⟨w, hmem⟩) = Multiplicative.ofAdd v :=
      Subtype.ext_iff.mp heq
    have := congrArg Multiplicative.toAdd hval
    simpa only [toAdd_ofAdd] using this
  refine ⟨q, hsurj, ?_, hβq⟩
  intro w
  have h_ofadd : q w = 0 ↔ Multiplicative.ofAdd (q w) = 1 := by
    constructor
    · intro h; rw [h, ofAdd_zero]
    · intro h
      have := congrArg Multiplicative.toAdd h
      simpa only [toAdd_ofAdd, toAdd_one] using this
  have h_sub : Multiplicative.ofAdd (q w) = 1 ↔
      (⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (Multiplicative V))) = 1 := by
    constructor
    · intro h; exact Subtype.ext h
    · intro h; simpa only [Subgroup.coe_mk, Subgroup.coe_one] using Subtype.ext_iff.mp h
  have h_beta : (⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ :
      ↥(⊤ : Subgroup (Multiplicative V))) = 1 ↔
      β ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩ = 1 := by
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact hβinj (by rw [h, map_one])
  rw [h_ofadd, h_sub, h_beta, hβq w, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact (hden (w : GolayAmbient)).symm

end CFSG.Quasithin.G11
