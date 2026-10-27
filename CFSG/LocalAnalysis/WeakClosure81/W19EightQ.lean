module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightBasic
public import CFSG.LocalAnalysis.WeakClosure81.W19Quad

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp197

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X E F : Subgroup G} {g : G}

theorem quadratic (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g)
    (hne : E ⊓ conjSubgroup V₀ g ≠ ⊥) :
    E ≤ conjSubgroup D.M g ∧ ⁅E, conjSubgroup V g⁆ ≤ E ⊓ conjSubgroup V g ∧
      ⁅⁅E, conjSubgroup V g⁆, conjSubgroup V g⁆ = ⊥ :=
  c.quadratic_of_inf_ne_bot h.isElemAbelian.1 h.A_le_normalizer_E hne

theorem X_inf_centralizerQuot (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h : Hyp197 D V X E F g) (hne : E ⊓ conjSubgroup V₀ g ≠ ⊥) :
    X ⊓ centralizerQuot (X ⊔ D.T) E F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxX, hxC⟩
  have hxE : ∀ e ∈ E, x * e = e * x := by
    intro e he
    set f : G := ⁅x, e⁆ with hf
    have hfF : f ∈ F := hxC.2.2 e he
    have hxF : x * f = f * x := by
      have h1 : ⁅f, x⁆ ∈ ⁅F, twoResidual (X ⊔ D.T)⁆ :=
        Subgroup.commutator_mem_commutator hfF (c.X_le_twoResidual hxX)
      rw [h.comm_F, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    have hpow : ∀ k : ℕ, x ^ k * e * (x ^ k)⁻¹ = f ^ k * e := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : x ^ (k + 1) * e * (x ^ (k + 1))⁻¹ = x * (x ^ k * e * (x ^ k)⁻¹) * x⁻¹ := by
          group
        have hk : x * f ^ k = f ^ k * x := (Commute.pow_right (show Commute x f from hxF) k).eq
        have h3 : x * e * x⁻¹ = f * e := by rw [hf, commutatorElement_def]; group
        rw [h1, ih]
        calc x * (f ^ k * e) * x⁻¹ = (x * f ^ k) * e * x⁻¹ := by group
          _ = (f ^ k * x) * e * x⁻¹ := by rw [hk]
          _ = f ^ k * (x * e * x⁻¹) := by group
          _ = f ^ (k + 1) * e := by rw [h3, pow_succ]; group
    have hfp : f ^ p = 1 := by
      have h1 := hpow p
      rw [c.hyp.exponent x hxX, one_mul, inv_one, mul_one] at h1
      exact (mul_eq_right.1 h1.symm)
    have hf2 : f ^ 2 = 1 := h.isElemAbelian.2 f (h.F_le hfF)
    have hf1 : f ∈ (⊥ : Subgroup G) :=
      E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (k := 1) (j := 1)
        (by rw [pow_one, hfp]; exact Subgroup.one_mem _)
        (by rw [pow_one, hf2]; exact Subgroup.one_mem _)
    rw [Subgroup.mem_bot, hf, commutatorElement_eq_one_iff_mul_comm] at hf1
    exact hf1
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hw1' : w ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hxw : x ∈ Subgroup.centralizer ({w} : Set G) := by
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hxE y hw.1).symm
  have hxM : x ∈ conjSubgroup D.M g := centralizer_le_conj_M c.setting c.ne_bot g hw.2 hw1' hxw
  have := h.X_inf_conj_M c h162
  rw [eq_bot_iff] at this
  exact this ⟨hxX, hxM⟩

theorem centralizerQuot_eq_pCoreOf (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h : Hyp197 D V X E F g) (hne : E ⊓ conjSubgroup V₀ g ≠ ⊥) :
    centralizerQuot (X ⊔ D.T) E F = pCoreOf 2 (X ⊔ D.T) := by
  refine le_antisymm ?_ (h.pCoreOf_le_centralizerQuot c)
  have hXC := h.X_inf_centralizerQuot c h162 hne
  haveI : Fact p.Prime := ⟨c.hyp.prime⟩
  have hnop : ¬ p ∣ Nat.card ↥(centralizerQuot (X ⊔ D.T) E F) := by
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hyG : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe, hy]
    have hP : IsPGroup p ↥(Subgroup.zpowers (y : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one, hyG])
    have hPH : Subgroup.zpowers (y : G) ≤ X ⊔ D.T :=
      (Subgroup.zpowers_le.2 y.2).trans (centralizerQuot_le _ _ _)
    obtain ⟨u, hu, hPu⟩ := c.hyp.exists_conj_le hPH hP
    have h1 : (y : G) ∈ conjSubgroup X u := hPu (Subgroup.mem_zpowers _)
    rw [mem_conjSubgroup_iff] at h1
    have h2 : u * (y : G) * u⁻¹ ∈ centralizerQuot (X ⊔ D.T) E F :=
      (Subgroup.mem_normalizer_iff.1 (h.normalizer_centralizerQuot hu) (y : G)).1 y.2
    have h3 : u * (y : G) * u⁻¹ ∈ X ⊓ centralizerQuot (X ⊔ D.T) E F := ⟨h1, h2⟩
    rw [hXC, Subgroup.mem_bot] at h3
    have h4 : (y : G) = 1 := by
      have := congrArg (fun z => u⁻¹ * z * u) h3
      simpa [mul_assoc] using this
    have h5 : y = 1 := Subtype.ext h4
    rw [h5, orderOf_one] at hy
    exact (Nat.Prime.one_lt Fact.out).ne hy
  have hC2 : IsPGroup 2 ↥(centralizerQuot (X ⊔ D.T) E F) := by
    intro x
    have hxH : (x : G) ∈ X ⊔ D.T := centralizerQuot_le _ _ _ x.2
    obtain ⟨a, b, hab⟩ := c.hyp.orderOf_eq hxH
    have hb : b = 0 := by
      by_contra hb0
      apply hnop
      have h1 : p ∣ orderOf x := by
        rw [← Subgroup.orderOf_coe, hab]
        exact Dvd.dvd.mul_left (dvd_pow_self p hb0) _
      exact h1.trans (orderOf_dvd_natCard x)
    refine ⟨a, ?_⟩
    have h1 : (x : G) ^ 2 ^ a = 1 := by
      have := pow_orderOf_eq_one (x : G)
      rwa [hab, hb, pow_zero, mul_one] at this
    exact Subtype.ext (by simpa using h1)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizerQuot_le _ _ _)
    h.normalizer_centralizerQuot hC2

end Hyp197

end CFSG.LocalAnalysis.WeakClosure81

end
