module

public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSum
public import CFSG.Timmesfeld.Bridge.RootStructWTINatSum
public import CFSG.RankThree.GF2n.Tim77Prop24TwoL2

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups
open Matrix
open CFSG.QuasithinUnique.Setup.X7
open CFSG.Timmesfeld.RankOne
open CFSG.CGT.Timmesfeld75
open CFSG.Timmesfeld.Bridge.NatSum

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem lowerElt_eq_ltriElt (t : F) : lowerElt F t = ltriElt t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerElt, ltriElt]

private theorem upperElt_mem_utri (t : F) : upperElt F t ∈ utri F := by
  rw [CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent]
  exact (mem_upperUnipotent_iff F).2 ⟨t, rfl⟩

private theorem lowerElt_mem_ltri (t : F) : lowerElt F t ∈ ltri F := by
  rw [lowerElt_eq_ltriElt]
  exact ltriElt_mem_ltri t

theorem isNatSumModule_of_fixedSub
    (ρ : Representation (ZMod 2) SL(2, F) W)
    (hfix : fixedSub ρ ⊤ = ⊥)
    (hquad : ∀ a ∈ utri F, ∀ b ∈ utri F, (ρ a - 1) ∘ₗ (ρ b - 1) = 0)
    (hspan : fixedSub ρ (utri F) ⊔ fixedSub ρ (ltri F) = ⊤) :
    IsNatSumModule ρ := by
  classical
  haveI : PerfectRing F 2 := PerfectField.toPerfectRing 2
  letI : DistribMulAction SL(2, F) W := DistribMulAction.compHom W ρ
  have hquad' : ∀ (s t : F) (v : W),
      upperElt F s • (upperElt F t • v - v) = upperElt F t • v - v := by
    intro s t v
    have h := LinearMap.congr_fun
      (hquad (upperElt F s) (upperElt_mem_utri s) (upperElt F t) (upperElt_mem_utri t)) v
    change ρ (upperElt F s) (ρ (upperElt F t) v - v) = ρ (upperElt F t) v - v
    simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h
  have hfix' : ∀ v : W, (∀ x : SL(2, F), x • v = v) → v = 0 := by
    intro v hv
    have hv' : v ∈ fixedSub ρ ⊤ := mem_fixedSub.mpr fun x _ => hv x
    rw [hfix] at hv'
    simpa using hv'
  have hspan' : ∀ v : W, ∃ u ∈ fixedUpper F W, ∃ w ∈ fixedLower F W, v = u + w := by
    intro v
    have hv : v ∈ fixedSub ρ (utri F) ⊔ fixedSub ρ (ltri F) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, hvw⟩ := Submodule.mem_sup.mp hv
    refine ⟨u, ?_, w, ?_, hvw.symm⟩
    · rw [CFSG.Timmesfeld.Bridge.NatSum.mem_fixedUpper]
      intro t
      exact mem_fixedSub.mp hu (upperElt F t) (upperElt_mem_utri t)
    · rw [CFSG.Timmesfeld.Bridge.NatSum.mem_fixedLower]
      intro t
      exact mem_fixedSub.mp hw (lowerElt F t) (lowerElt_mem_ltri t)
  obtain ⟨k, θ, -, hequiv, -, hsum, hcard, -, -⟩ :=
    CFSG.Timmesfeld.Bridge.NatSum.exists_natural_sum (K := F) (V := W)
      hquad' hfix' hspan'
  let Φ : (Fin k → Fin 2 → F) →+ W :=
    { toFun := fun c => ∑ i, θ i (c i)
      map_zero' := by simp
      map_add' := fun c c' => by
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib] }
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨c, hc⟩ := hsum v
    exact ⟨c, hc.symm⟩
  have hcardDom : Nat.card (Fin k → Fin 2 → F) = Nat.card F ^ (2 * k) := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_fun, Nat.card_fin, pow_mul]
  have hbij : Function.Bijective Φ :=
    hsurj.bijective_of_nat_card_le (by rw [hcardDom, hcard])
  let φ : W ≃+ (Fin k → Fin 2 → F) := (AddEquiv.ofBijective Φ hbij).symm
  have hΦφ : ∀ w : W, Φ (φ w) = w := fun w => by simp [φ]
  have hΦ_smul : ∀ (g : SL(2, F)) (c : Fin k → Fin 2 → F),
      Φ (fun i => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ c i) = ρ g (Φ c) := by
    intro g c
    calc
      Φ (fun i => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ c i)
          = ∑ i, θ i ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ c i) := rfl
      _ = ∑ i, ρ g (θ i (c i)) :=
            Finset.sum_congr rfl fun i _ => hequiv i g (c i)
      _ = ρ g (∑ i, θ i (c i)) := (map_sum (ρ g) _ _).symm
      _ = ρ g (Φ c) := rfl
  have hφ_smul : ∀ (g : SL(2, F)) (w : W),
      φ (ρ g w) = fun i => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ w i := by
    intro g w
    apply (AddEquiv.ofBijective Φ hbij).injective
    change Φ (φ (ρ g w)) = Φ (fun i => (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ w i)
    rw [hΦφ (ρ g w), hΦ_smul g (φ w), hΦφ w]
  refine ⟨k, φ, ?_⟩
  intro g w i
  rw [hφ_smul g w]

private theorem fixedSub_comp_conj
    (ρ : Representation (ZMod 2) SL(2, F) W) (c : SL(2, F)) (S : Subgroup SL(2, F)) :
    fixedSub (ρ.comp (MulAut.conj c).toMonoidHom) S =
      fixedSub ρ (conjSubgroup c S) := by
  ext v
  rw [mem_fixedSub, mem_fixedSub]
  constructor
  · intro hv x hx
    rw [mem_conjSubgroup] at hx
    have h := hv (c⁻¹ * x * c) hx
    simpa [MulAut.conj_apply, mul_assoc] using h
  · intro hv s hs
    have hmem : c * s * c⁻¹ ∈ conjSubgroup c S := by
      rw [mem_conjSubgroup]
      simpa [show c⁻¹ * (c * s * c⁻¹) * c = s by group] using hs
    simpa [MulAut.conj_apply] using hv _ hmem

private theorem isNatSumModule_comp_conj
    (ρ : Representation (ZMod 2) SL(2, F) W) (c : SL(2, F))
    (h : IsNatSumModule (ρ.comp (MulAut.conj c).toMonoidHom)) :
    IsNatSumModule ρ := by
  classical
  obtain ⟨k, φ, hφ⟩ := h
  refine ⟨k, φ.trans (DistribMulAction.toAddEquiv (Fin k → Fin 2 → F) c), ?_⟩
  intro g w i
  have hx : ρ.comp (MulAut.conj c).toMonoidHom (c⁻¹ * g * c) = ρ g := by
    ext v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    congr 1
    group
  have h1 := hφ (c⁻¹ * g * c) w i
  rw [hx] at h1
  have h2 : φ (ρ g w) i = (c⁻¹ * g * c) • φ w i := by
    rw [h1, ← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
  simp only [AddEquiv.trans_apply, DistribMulAction.toAddEquiv_apply, Pi.smul_apply]
  rw [← Matrix.smul_eq_mulVec, ← Matrix.SpecialLinearGroup.smul_def]
  rw [h2, ← mul_smul, ← mul_smul]
  congr 1
  group

theorem isNatSumModule_of_fixedSub_conj
    (ρ : Representation (ZMod 2) SL(2, F) W)
    (hfix : fixedSub ρ ⊤ = ⊥)
    {a b : SL(2, F)}
    (hne : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F))
    (hquad : ∀ x ∈ conjSubgroup a (utri F), ∀ y ∈ conjSubgroup a (utri F),
      (ρ x - 1) ∘ₗ (ρ y - 1) = 0)
    (hspan : fixedSub ρ (conjSubgroup a (utri F)) ⊔
      fixedSub ρ (conjSubgroup b (utri F)) = ⊤) :
    IsNatSumModule ρ := by
  obtain ⟨c, hA, hB⟩ := exists_conj_utri_ltri_of_ne hne
  refine isNatSumModule_comp_conj ρ c (isNatSumModule_of_fixedSub
    (ρ.comp (MulAut.conj c).toMonoidHom) ?_ ?_ ?_)
  · rw [fixedSub_comp_conj, conjSubgroup_top, hfix]
  · intro x hx y hy
    have hx' : c * x * c⁻¹ ∈ conjSubgroup a (utri F) := by
      rw [hA, mem_conjSubgroup]
      simpa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] using hx
    have hy' : c * y * c⁻¹ ∈ conjSubgroup a (utri F) := by
      rw [hA, mem_conjSubgroup]
      simpa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] using hy
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hquad (c * x * c⁻¹) hx' (c * y * c⁻¹) hy'
  · rw [fixedSub_comp_conj, fixedSub_comp_conj, ← hA, ← hB, hspan]

end CFSG.RankThree.GF2n.Tim81.Sec2
