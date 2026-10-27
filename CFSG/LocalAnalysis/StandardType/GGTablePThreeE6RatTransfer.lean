module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTDefs

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section

private theorem e6T_prod_zpow_eq_zpow_sum {ι G : Type*} [CommGroup G] (s : Finset ι)
    (f : ι → ℤ) (x : G) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

private theorem e6T_rootChar_eq_pow_sum {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (ω : Kˣ) (e : Fin τ.rank → ℕ) (ha : ∀ i, a i = ω ^ e i) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
  simp only [rootChar]
  calc ∏ i, a i ^ γ i
      = ∏ i, (ω ^ (e i : ℤ)) ^ γ i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [ha i, zpow_natCast]
    _ = ∏ i, ω ^ ((e i : ℤ) * γ i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [zpow_mul]
    _ = ω ^ (∑ i, (e i : ℤ) * γ i) := by
        simpa using e6T_prod_zpow_eq_zpow_sum Finset.univ (fun i => (e i : ℤ) * γ i) ω

private theorem e6T_zmod_sum_val {n : ℕ} (v : Fin n → ZMod 3) (γ : Fin n → ℤ) :
    ((∑ k, ((v k).val : ℤ) * γ k : ℤ) : ZMod 3) =
      ∑ k, ((γ k : ℤ) : ZMod 3) * v k := by
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [ZMod.natCast_zmod_val]
  exact mul_comm _ _

private theorem e6T_mk_eq_mk_of_kernelRoots_subset {τ : Tag} {M M' : Type*} [CommGroup M]
    [CommGroup M'] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'} (h : kernelRoots χ ⊆ kernelRoots χ')
    {x y : kernelRoots χ} (hxy : (⟦x⟧ : KernelComponent χ) = ⟦y⟧) :
    (⟦⟨x.1, h x.2⟩⟧ : KernelComponent χ') = ⟦⟨y.1, h y.2⟩⟧ := by
  have hr : Relation.EqvGen _ x y := Quotient.exact hxy
  clear hxy
  apply Quotient.sound
  change Relation.EqvGen _ _ _
  induction hr with
  | rel a b hab => exact Relation.EqvGen.rel _ _ hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

private theorem e6T_componentRoots_eq_of_kernelRoots_eq {τ : Tag} {M M' : Type*} [CommGroup M]
    [CommGroup M'] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'} (h : kernelRoots χ = kernelRoots χ')
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) (hα' : α ∈ kernelRoots χ') :
    componentRoots χ ⟦⟨α, hα⟩⟧ = componentRoots χ' ⟦⟨α, hα'⟩⟧ := by
  ext β
  constructor
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.le hβ, e6T_mk_eq_mk_of_kernelRoots_subset h.le (x := ⟨β, hβ⟩) (y := ⟨α, hα⟩) hβα⟩
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.ge hβ, e6T_mk_eq_mk_of_kernelRoots_subset h.ge (x := ⟨β, hβ⟩) (y := ⟨α, hα'⟩) hβα⟩

end

theorem e6_kerComponent_of_component {L : Type} [Field L] {ω : L} (hω : IsPrimitiveRoot ω 3)
    {a : Fin Tag.E6.rank → Lˣ} (v : Fin Tag.E6.rank → ZMod 3)
    (hv : ∀ i, ((a i : Lˣ) : L) = ω ^ (v i).val) (i : KernelComponent (rootCharHom a)) :
    E6KerComponent v (componentRoots (rootCharHom a) i) := by
  classical
  set ω₀ : Lˣ := Units.mk0 ω (hω.ne_zero (by norm_num)) with hω₀def
  have hω₀ : IsPrimitiveRoot ω₀ 3 := by
    rw [hω₀def]
    exact IsPrimitiveRoot.coe_units_iff.1 (by simpa only [Units.val_mk0] using hω)
  have hae : ∀ i, a i = ω₀ ^ (v i).val := by
    intro i
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hv i
  have hrootChar : ∀ γ : Fin Tag.E6.rank → ℤ,
      rootChar a γ = ω₀ ^ (∑ k, ((v k).val : ℤ) * γ k) :=
    fun γ => e6T_rootChar_eq_pow_sum a ω₀ (fun k => (v k).val) hae γ
  have hkernel : kernelRoots (rootCharHom a) = kernelRoots (e6Chi v) := by
    ext γ
    rw [kernelRoots_rootCharHom]
    show (IsRoot Tag.E6 γ ∧ rootChar a γ = 1) ↔
      (IsRoot Tag.E6 γ ∧ e6Chi v (Multiplicative.ofAdd γ) = 1)
    refine and_congr_right fun _ => ?_
    have hchi : e6Chi v (Multiplicative.ofAdd γ) =
        Multiplicative.ofAdd (∑ k, ((γ k : ℤ) : ZMod 3) * v k) := rfl
    rw [hchi]
    calc rootChar a γ = 1
        ↔ ω₀ ^ (∑ k, ((v k).val : ℤ) * γ k) = 1 := by rw [hrootChar γ]
      _ ↔ (3 : ℤ) ∣ ∑ k, ((v k).val : ℤ) * γ k := hω₀.zpow_eq_one_iff_dvd _
      _ ↔ (((∑ k, ((v k).val : ℤ) * γ k) : ℤ) : ZMod 3) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).symm
      _ ↔ ∑ k, ((γ k : ℤ) : ZMod 3) * v k = 0 := by rw [e6T_zmod_sum_val]
      _ ↔ Multiplicative.ofAdd (∑ k, ((γ k : ℤ) : ZMod 3) * v k) = 1 :=
            (ofAdd_eq_one).symm
  obtain ⟨α, rfl⟩ := Quotient.exists_rep i
  have hα' : (α : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (e6Chi v) := by
    rw [← hkernel]
    exact α.2
  exact ⟨⟦⟨α.1, hα'⟩⟧, e6T_componentRoots_eq_of_kernelRoots_eq hkernel α.2 hα'⟩

end CFSG.StandardType.TablePThreeKG

end
