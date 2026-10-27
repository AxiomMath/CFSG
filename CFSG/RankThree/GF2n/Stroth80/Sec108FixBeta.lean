module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Phi
public import CFSG.RankThree.GF2n.Stroth80.Sec111Norm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem bV_sum_ne_zero (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0) :
    (∑ i, β i • (D.bV AM i : AM.M₀.E)) ≠ 0 := by
  intro hb
  apply hβ
  funext i
  have hzero : (∑ i, β i • D.bV AM i : ↥(AM.Vsp hc t)) = 0 := by
    apply Subtype.ext
    simpa using hb
  have hrepr := congrArg (fun v : ↥(AM.Vsp hc t) => (D.bV AM).coord i v) hzero
  simp only [map_sum, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, map_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero] at hrepr
  simpa using hrepr

private theorem phi_bV_sum_eq_self (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K}
    (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    (hAβ : (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ β = β)
    {r : G} {hr : r ∈ H0 M Z}
    (hA : ∀ j, AM.φ ⟨r, hr⟩ (D.bV AM j) =
      ∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) i j • (D.bV AM i : AM.M₀.E)) :
    AM.φ ⟨r, hr⟩ (∑ i, β i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E) := by
  calc AM.φ ⟨r, hr⟩ (∑ i, β i • (D.bV AM i : AM.M₀.E))
      = ∑ i, β i • AM.φ ⟨r, hr⟩ (D.bV AM i) := by
        rw [map_sum]
        simp only [map_smul]
    _ = ∑ i, β i • ∑ j, (A : Matrix (Fin 3) (Fin 3) AM.K) j i •
          (D.bV AM j : AM.M₀.E) := by
        simp only [hA]
    _ = ∑ i, ∑ j, (β i * (A : Matrix (Fin 3) (Fin 3) AM.K) j i) •
          (D.bV AM j : AM.M₀.E) := by
        simp only [Finset.smul_sum, smul_smul]
    _ = ∑ j, ∑ i, (β i * (A : Matrix (Fin 3) (Fin 3) AM.K) j i) •
          (D.bV AM j : AM.M₀.E) := by
        rw [Finset.sum_comm]
    _ = ∑ j, (∑ i, β i * (A : Matrix (Fin 3) (Fin 3) AM.K) j i) •
          (D.bV AM j : AM.M₀.E) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (Finset.sum_smul (s := Finset.univ)
          (f := fun i => β i * (A : Matrix (Fin 3) (Fin 3) AM.K) j i)
          (x := (D.bV AM j : AM.M₀.E))).symm
    _ = ∑ j, (∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) j i * β i) •
          (D.bV AM j : AM.M₀.E) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm (β i) _
    _ = ∑ j, ((A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ β) j •
          (D.bV AM j : AM.M₀.E) := by
        simp only [Matrix.mulVec, dotProduct]
    _ = ∑ j, β j • (D.bV AM j : AM.M₀.E) := by rw [hAβ]

private theorem fix_Bsp_of_fix_sum (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {β : Fin 3 → AM.K} (hβ : β ≠ 0)
    (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM) {r : G} {hr : r ∈ H0 M Z}
    (hfix : AM.φ ⟨r, hr⟩ (∑ i, β i • (D.bV AM i : AM.M₀.E)) =
      ∑ i, β i • (D.bV AM i : AM.M₀.E)) :
    ∀ w ∈ D.Bsp AM, AM.φ ⟨r, hr⟩ w = w := by
  have hspan : D.Bsp AM = AM.K ∙ (∑ i, β i • (D.bV AM i : AM.M₀.E)) :=
    eq_span_singleton_of_mem_of_finrank_eq_one (D.finrank_Bsp AM) hβB
      (bV_sum_ne_zero D AM hβ)
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hw)
  rw [map_smul, hfix]

private theorem mem_normalizer_sup_of_fix_Bsp (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {r : G} (hrH : r ∈ H0 M Z)
    (hfixBsp : ∀ w ∈ D.Bsp AM, AM.φ ⟨r, hrH⟩ w = w) :
    r ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  have hrM : r ∈ M := hrH.1
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨b, hbB, z, hzZ, hxeq⟩ := exists_mul_of_mem_sup_of_commute
    (fun b hb z hz => (Smith81.Z_central hc.hyp hz (hc.le hb)).symm) hx
  rw [hxeq]
  have hbQ : b ∈ Q := hc.le hbB
  have hrbQ : r * b * r⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) b).mp hbQ
  have hpib : AM.M₀.π (r * b * r⁻¹) = AM.M₀.π b := by
    rw [AM.φ_π ⟨r, hrH⟩ b hbQ]
    exact hfixBsp _ ((D.mem_Bsp AM).mpr (AM.M₀.pi_mem_img hbB hbQ))
  have hz : (r * b * r⁻¹)⁻¹ * b ∈ Z := (AM.M₀.pi_eq_iff hrbQ hbQ).mp hpib
  have hz' : b⁻¹ * (r * b * r⁻¹) ∈ Z := by
    simpa only [_root_.mul_inv_rev, inv_inv] using Z.inv_mem hz
  have hbz : r * b * r⁻¹ ∈ B ⊔ Z := by
    rw [show r * b * r⁻¹ = b * (b⁻¹ * (r * b * r⁻¹)) by group]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_left hbB) (Subgroup.mem_sup_right hz')
  have hzZ' : r * z * r⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hrM) z).mp hzZ
  rw [show r * (b * z) * r⁻¹ = (r * b * r⁻¹) * (r * z * r⁻¹) by group]
  exact (B ⊔ Z).mul_mem hbz (Subgroup.mem_sup_right hzZ')

theorem Sec108Data.exists_fix_beta (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {β : Fin 3 → AM.K} (hβ : β ≠ 0) (hβB : ∑ i, β i • (D.bV AM i : AM.M₀.E) ∈ D.Bsp AM)
    (A : Matrix.SpecialLinearGroup (Fin 3) AM.K)
    (hAβ : (A : Matrix (Fin 3) (Fin 3) AM.K) *ᵥ β = β) :
    ∃ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∃ hr : r ∈ H0 M Z,
      r ∈ Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G) ∧
      ∀ j, AM.φ ⟨r, hr⟩ (D.bV AM j) =
        ∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) i j • (D.bV AM i : AM.M₀.E) := by
  obtain ⟨r, hrRt, hrH, hA⟩ := D.bV_spec AM A
  refine ⟨r, hrRt, hrH, ?_, hA⟩
  have hfix := phi_bV_sum_eq_self D AM A hAβ hA
  have hfixBsp := fix_Bsp_of_fix_sum D AM hβ hβB hfix
  exact (stroth_11_1a hc D.hyp.width (by norm_num) hrH.1).mp
    (mem_normalizer_sup_of_fix_Bsp D AM hrH hfixBsp)

end CFSG.RankThree.GF2n.Stroth80
