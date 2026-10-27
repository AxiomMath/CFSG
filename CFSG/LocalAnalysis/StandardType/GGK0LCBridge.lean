module

public import CFSG.LocalAnalysis.StandardType.GGK0LCStab
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import TauCeti.Algebra.BigOperators.ZPow

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

private theorem lk0xlcbridge_rootChar_eq_zeta_zpow {τ : Tag} {F : Type} [Field F]
    (a : Fin τ.rank → Fˣ) (ζ : Fˣ) (K : KacPt τ) (ha : ∀ i, a i = ζ ^ K.s i)
    (v : Fin τ.rank → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v = ζ ^ K.lam v := by
  show (∏ i, a i ^ v i) = ζ ^ ∑ i, (K.s i : ℤ) * v i
  calc ∏ i, a i ^ v i
      = ∏ i, ζ ^ ((K.s i : ℤ) * v i) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [ha i, ← zpow_natCast ζ (K.s i), ← zpow_mul]
    _ = ζ ^ ∑ i, (K.s i : ℤ) * v i :=
        Finset.prod_zpow_eq_zpow_sum Finset.univ ζ (fun i => (K.s i : ℤ) * v i)

private theorem lk0xlcbridge_zeta_zpow_eq_iff {F : Type} [Field F] {ζ : Fˣ} {p : ℕ}
    (hζ : orderOf ζ = p) (x y : ℤ) :
    ζ ^ x = ζ ^ y ↔ (p : ℤ) ∣ x - y := by
  rw [← hζ, orderOf_dvd_iff_zpow_eq_one, zpow_sub, ← div_eq_mul_inv]
  exact div_eq_one.symm

private theorem lk0xlcbridge_mem_stab_iff {τ : Tag} {F : Type} [Field F]
    (a : Fin τ.rank → Fˣ) (ζ : Fˣ) (K : KacPt τ)
    (hζ : orderOf ζ = K.p) (ha : ∀ i, a i = ζ ^ K.s i) (w : WeylGroup τ) :
    w ∈ rootCharStabilizerSubgroup a ↔ w ∈ K.stab := by
  rw [mem_rootCharStabilizerSubgroup]
  show (∀ v : Fin τ.rank → ℤ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a (w • v) =
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar a v) ↔
    ∀ v : Fin τ.rank → ℤ, (K.p : ℤ) ∣ K.lam (w • v) - K.lam v
  constructor
  · intro h v
    have hv := h v
    rw [lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha,
        lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha,
        lk0xlcbridge_zeta_zpow_eq_iff hζ] at hv
    exact hv
  · intro h v
    rw [lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha,
        lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha,
        lk0xlcbridge_zeta_zpow_eq_iff hζ]
    exact h v

private theorem lk0xlcbridge_rootCharKernel_eq {τ : Tag} {F : Type} [Field F]
    (a : Fin τ.rank → Fˣ) (ζ : Fˣ) (K : KacPt τ)
    (hζ : orderOf ζ = K.p) (ha : ∀ i, a i = ζ ^ K.s i) :
    rootCharKernel a = K.kerRoots := by
  ext α
  constructor
  · rintro ⟨hroot, hχ⟩
    refine ⟨hroot, ?_⟩
    rw [lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha] at hχ
    rw [← orderOf_dvd_iff_zpow_eq_one, hζ] at hχ
    exact hχ
  · rintro ⟨hroot, hdvd⟩
    refine ⟨hroot, ?_⟩
    rw [lk0xlcbridge_rootChar_eq_zeta_zpow a ζ K ha]
    have h : (orderOf ζ : ℤ) ∣ K.lam α := by rwa [← hζ] at hdvd
    exact (orderOf_dvd_iff_zpow_eq_one).mp h

private theorem lk0xlcbridge_kernelReflectionGroup_eq {τ : Tag} {F : Type} [Field F]
    (a : Fin τ.rank → Fˣ) (ζ : Fˣ) (K : KacPt τ)
    (hζ : orderOf ζ = K.p) (ha : ∀ i, a i = ζ ^ K.s i) :
    kernelReflectionGroup a = K.refl := by
  have hker := lk0xlcbridge_rootCharKernel_eq a ζ K hζ ha
  simp only [kernelReflectionGroup, KacPt.refl, hker]

theorem rootCharStabilizerSubgroup_le_kernelReflectionGroup_kac
    {τ : Tag}
    {F : Type} [Field F] (a : Fin τ.rank → Fˣ) (ζ : Fˣ) (K : KacPt τ)
    (hζ : orderOf ζ = K.p) (ha : ∀ i, a i = ζ ^ K.s i) (hT : KacBox τ) {d : ℕ}
    (hc : KacCentred τ d) (hp : K.p.Prime) (hd : ¬ K.p ∣ d) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  intro w hw
  have hstab : w ∈ K.stab := (lk0xlcbridge_mem_stab_iff a ζ K hζ ha w).mp hw
  have hrefl : w ∈ K.refl := (KacPt.stab_le_refl hT hc K hp hd) hstab
  rw [lk0xlcbridge_kernelReflectionGroup_eq a ζ K hζ ha]
  exact hrefl

end CFSG.StandardType.GGK0LC

end
