module

public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

private theorem s16c167_constWeight_eq_evenWeightOnes (m : ℕ) :
    CFSG.Quasithin.constWeight m = CFSG.RankThree.PartTwo.evenWeightOnes m := by
  ext x
  rw [CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro hx
    by_cases hm : Nonempty (Fin m)
    · obtain ⟨i₀⟩ := hm
      refine ⟨((x : Fin m → ZMod 2) i₀).val, funext fun i => ?_⟩
      simp [CFSG.RankThree.PartTwo.allOnes, hx i i₀]
    · refine ⟨0, funext fun i => ?_⟩
      exact absurd ⟨i⟩ hm
  · rintro ⟨k, hk⟩
    have hi : ∀ i, (x : Fin m → ZMod 2) i = (k : ZMod 2) := fun i => by
      rw [← hk]
      simp [CFSG.RankThree.PartTwo.allOnes]
    intro i j
    exact (hi i).trans (hi j).symm

private noncomputable def s16c167_heartEquivAlt (m : ℕ) :
    CFSG.Quasithin.AltHeart m ≃+ CFSG.RankThree.PartTwo.altHeart m :=
  QuotientAddGroup.quotientAddEquivOfEq (s16c167_constWeight_eq_evenWeightOnes m)

private theorem s16c167_heartEquivAlt_mk {m : ℕ}
    (x : ↥(CFSG.QuasithinUnique.evenWeight m)) :
    s16c167_heartEquivAlt m (QuotientAddGroup.mk x : CFSG.Quasithin.AltHeart m) =
      (QuotientAddGroup.mk x : CFSG.RankThree.PartTwo.altHeart m) :=
  QuotientAddGroup.quotientAddEquivOfEq_mk _ x

private theorem s16c167_heartEquivAlt_hAct {m : ℕ} (σ : Equiv.Perm (Fin m))
    (y : CFSG.Quasithin.AltHeart m) :
    s16c167_heartEquivAlt m (CFSG.Quasithin.C41Pf.AltN.hAct m σ y) =
      CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ
        (s16c167_heartEquivAlt m y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [CFSG.Quasithin.C41Pf.AltN.hAct_mk]
  simp only [s16c167_heartEquivAlt_mk, CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_mk]
  rw [show CFSG.Quasithin.permWeight m σ x =
      CFSG.RankThree.PartTwo.evenWeightPerm σ x from Subtype.ext (funext fun _ => rfl)]

theorem s16c167_endUnits_alt {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {n : ℕ} (hn : 5 ≤ n) (h : AlternatingNatural H U ⊥ n) :
    Z391.EndUnitsTrivial H U := by
  intro φ hφ
  have hn0 : 0 < n := by omega
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hsurj, -, -, hUinv, -, hsecinv, -, β, hβsurj, hβker, hβeq⟩ := hπ
  let e : (↥(G6.coreMod n) ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Multiplicative (AltHeart n) := CFSG.Quasithin.C124.altQuotEquiv n hn0
  let β' : ↥U →* Multiplicative (AltHeart n) := e.toMonoidHom.comp β
  have hstab : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := hUinv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hβ'inj : Function.Injective β' := e.injective.comp hβinj
  have hβ'surj : Function.Surjective β' := e.surjective.comp hβsurj
  let βe : ↥U ≃* Multiplicative (AltHeart n) :=
    MulEquiv.ofBijective β' ⟨hβ'inj, hβ'surj⟩
  have hβ'e : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
      βe ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (βe u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  let ψ : Multiplicative (AltHeart n) ≃* Multiplicative (AltHeart n) :=
    βe.symm.trans (φ.trans βe)
  have hψβ : ∀ u : ↥U, ψ (βe u) = βe (φ u) := by
    intro u
    change (βe.symm.trans (φ.trans βe)) (βe u) = βe (φ u)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hψe : ∀ (γ : ↥(alternatingGroup (Fin n))) (y : AltHeart n),
      Multiplicative.toAdd (ψ (Multiplicative.ofAdd
          (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n)) y))) =
        CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (ψ (Multiplicative.ofAdd y))) := by
    intro γ y
    obtain ⟨u, hu⟩ := hβ'surj (Multiplicative.ofAdd y)
    have hu' : βe u = Multiplicative.ofAdd y := hu
    have h1 : βe ⟨((π γ : ↥H) : MulAut W) (u : W), hstab (π γ) u u.2⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n)) y) := by
      have h2 := hβ'e γ u (hstab (π γ) u u.2)
      rw [hu', toAdd_ofAdd] at h2
      exact h2
    have h3 : φ ⟨((π γ : ↥H) : MulAut W) (u : W), hstab (π γ) u u.2⟩ =
        ⟨((π γ : ↥H) : MulAut W) ((φ u : ↥U) : W),
          hstab (π γ) (φ u) (φ u).2⟩ :=
      Subtype.ext ((hφ (π γ) u ⟨_, hstab (π γ) u u.2⟩ rfl).symm)
    calc Multiplicative.toAdd (ψ (Multiplicative.ofAdd
            (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n)) y)))
        = Multiplicative.toAdd (ψ (βe ⟨((π γ : ↥H) : MulAut W) (u : W),
            hstab (π γ) u u.2⟩)) := by rw [h1]
      _ = Multiplicative.toAdd (βe (φ ⟨((π γ : ↥H) : MulAut W) (u : W),
            hstab (π γ) u u.2⟩)) := by rw [hψβ]
      _ = Multiplicative.toAdd (βe ⟨((π γ : ↥H) : MulAut W) ((φ u : ↥U) : W),
            hstab (π γ) (φ u) (φ u).2⟩) := by rw [h3]
      _ = Multiplicative.toAdd (Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n
            (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (βe (φ u))))) := by
            rw [hβ'e γ (φ u) (hstab (π γ) (φ u) (φ u).2)]
      _ = CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (βe (φ u))) := by rw [toAdd_ofAdd]
      _ = CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (ψ (βe u))) := by rw [hψβ u]
      _ = CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (ψ (Multiplicative.ofAdd y))) := by rw [hu']
  let c : CFSG.Quasithin.AltHeart n ≃+ CFSG.RankThree.PartTwo.altHeart n :=
    s16c167_heartEquivAlt n
  have hc_hAct : ∀ (σ : Equiv.Perm (Fin n)) (y : CFSG.Quasithin.AltHeart n),
      c (CFSG.Quasithin.C41Pf.AltN.hAct n σ y) =
        CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ (c y) :=
    fun σ y => s16c167_heartEquivAlt_hAct σ y
  let g : CFSG.RankThree.PartTwo.altHeart n →+ CFSG.RankThree.PartTwo.altHeart n :=
    { toFun := fun a => c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm a))))
      map_zero' := by
        change c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm 0)))) = 0
        simp [map_zero]
      map_add' := by
        intro a b
        change c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm (a + b))))) =
          c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm a)))) +
            c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm b))))
        rw [map_add c.symm, ofAdd_add, map_mul, toAdd_mul, map_add] }
  have hg : ∀ σ ∈ alternatingGroup (Fin n),
      ∀ v : CFSG.RankThree.PartTwo.altHeart n,
      g (CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ v) =
        CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ (g v) := by
    intro σ hσ v
    change c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd
        (c.symm (CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ v))))) =
      CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ
        (c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm v)))))
    have hcv : c.symm (CFSG.HardMathSupport.Cooperstein.Coordinator.altAct σ v) =
        CFSG.Quasithin.C41Pf.AltN.hAct n σ (c.symm v) := by
      apply c.injective
      rw [c.apply_symm_apply]
      have h := hc_hAct σ (c.symm v)
      rw [c.apply_symm_apply] at h
      exact h.symm
    rw [hcv, hψe ⟨σ, hσ⟩ (c.symm v),
      hc_hAct σ (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm v))))]
  have hginj : Function.Injective g := by
    intro a b hab
    change c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm a)))) =
      c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd (c.symm b)))) at hab
    have h2 := c.injective hab
    have h3 := Multiplicative.toAdd.injective h2
    have h4 := ψ.injective h3
    exact c.symm.injective (Multiplicative.ofAdd.injective h4)
  haveI : Nontrivial (CFSG.RankThree.PartTwo.altHeart n) :=
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.altHeart_nontrivial (by omega : 3 ≤ n)
  have hgnz : g ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := exists_ne (0 : CFSG.RankThree.PartTwo.altHeart n)
    have h1 : g a = g 0 := by rw [h0]; simp
    exact ha (hginj h1)
  have hg2 := CFSG.HardMathSupport.Cooperstein.Coordinator.altHeart_endo_eq_zero_or_id hn g hg
  have hg1 : g = AddMonoidHom.id _ := hg2.resolve_left hgnz
  have hψ : ψ = MulEquiv.refl (Multiplicative (AltHeart n)) := by
    ext m
    apply Multiplicative.toAdd.injective
    have hgid := congrFun (congrArg DFunLike.coe hg1) (c (Multiplicative.toAdd m))
    simp only [AddMonoidHom.id_apply] at hgid
    change c (Multiplicative.toAdd (ψ (Multiplicative.ofAdd
      (c.symm (c (Multiplicative.toAdd m)))))) = c (Multiplicative.toAdd m) at hgid
    rw [c.symm_apply_apply, ofAdd_toAdd] at hgid
    exact c.injective hgid
  refine MulEquiv.ext fun u => ?_
  apply βe.injective
  have h1 : βe (φ u) = ψ (βe u) := by
    change βe (φ u) = (βe.symm.trans (φ.trans βe)) (βe u)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hψ] at h1
  simpa using h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
