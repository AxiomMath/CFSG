module

public import CFSG.Quasithin.EmptyFaithful.S153NMl3B
import CFSG.Quasithin.EmptyFaithful.S153NMl3C
import CFSG.Quasithin.EmptyFaithful.SzN15Out
import CFSG.Quasithin.EmptyFaithful.S1565M7

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial

namespace Ml3

variable {K : Type} [Field K]

private theorem fixed_conj {t u : Matrix.SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}
    (hx : ((t⁻¹ * u * t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x) :
    ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x) =
    ((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x := by
  have e1 : u * t = t * (t⁻¹ * u * t) := by group
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, e1,
    Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hx]

private theorem eq_smul_of_mulVec {t : Matrix.SpecialLinearGroup (Fin 3) K} {x : Fin 3 → K}
    (h1 : (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x) 1 = 0)
    (h2 : (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x) 2 = 0) :
    x = (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x) 0 •
      ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        (Pi.single 0 1) := by
  set y : Fin 3 → K := ((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x
    with hy
  have hy' : y = y 0 • (Pi.single 0 1 : Fin 3 → K) := by
    funext j
    fin_cases j <;> simp [h1, h2]
  calc x = ((t⁻¹ * t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x := by
        rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    _ = ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec y := by
        rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    _ = y 0 • ((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (Pi.single 0 1) := by
        conv_lhs => rw [hy']
        rw [Matrix.mulVec_smul]

end Ml3

theorem false_of_two_natural_sl3 {W : Type} [CommGroup W] [Finite W] (hW : ∀ v : W, v ^ 2 = 1)
    {Γ J : Subgroup (MulAut W)} {w : W} (hJΓ : J ≤ Γ) (hJn : (J.subgroupOf Γ).Normal)
    (hdir : ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      DirectSumOfCopies J ⊤ (fixV J) (FFModel.nat (StatedSL 3 K)) 2)
    (hw : w ∉ fixV J) (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w))
    (hS : ∃ S : Subgroup (MulAut W), IsSylowTwoOf S Γ ∧ S ≤ stabAt Γ w) : False := by
  have _ := hw
  obtain ⟨m, K, _, _, hK, I, π₀, hZI, hind, hsup, hreal₀⟩ := hdir
  obtain ⟨π, hreal⟩ : ∃ π : ↥(StatedSL 3 K) →* ↥J,
      ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia J (I i) (fixV J) π := ⟨π₀, hreal₀⟩
  have : CharP K 2 := SzN15.charP_two_of_card hK
  have hinj : Function.Injective π := natural_realizes_injective _ (hreal 0)
  have hN : ∀ i, SzN15.NatReal J (I i) (fixV J) (StatedSL 3 K) π :=
    fun i => SzN15.NatReal.of_realizesVia (hreal i)
  choose β hβs hβk hβe using fun i => (hN i).exists_β
  obtain ⟨S, hSΓ, hSw⟩ := hS
  have hΓN : Γ ≤ Subgroup.normalizer (J : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJn
  have hsup2 : (⨆ i, I i) = I 0 ⊔ I 1 :=
    le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
      (sup_le (le_iSup I 0) (le_iSup I 1))
  obtain ⟨z, hz, y, hy, hzy⟩ :=
    Subgroup.mem_sup.mp (show w ∈ fixV J ⊔ ⨆ i, I i by rw [hsup]; trivial)
  rw [hsup2] at hy
  obtain ⟨a₀, ha₀, a₁, ha₁, hya⟩ := Subgroup.mem_sup.mp hy
  have hw' : w = z * (a₀ * a₁) := by rw [← hzy, ← hya]
  have hvec : ∀ s : ↥(StatedSL 3 K), ((π s : ↥J) : MulAut W) w = w →
      natAct (StatedSL 3 K) s (β 0 ⟨a₀, ha₀⟩) = β 0 ⟨a₀, ha₀⟩ ∧
      natAct (StatedSL 3 K) s (β 1 ⟨a₁, ha₁⟩) = β 1 ⟨a₁, ha₁⟩ := by
    intro s hs
    obtain ⟨c₀, c₁⟩ := Ml3.corr_mem_of_fix hind
      (fun i γ hγ u hu => (hN i).U_inv ⟨γ, hγ⟩ u hu) (π s).2 hz ha₀ ha₁ (by rw [← hw']; exact hs)
    exact ⟨(Ml3.corr_mem_iff (hN 0) (hβk 0) (hβe 0) s ⟨a₀, ha₀⟩).1 c₀,
      (Ml3.corr_mem_iff (hN 1) (hβk 1) (hβe 1) s ⟨a₁, ha₁⟩).1 c₁⟩
  obtain ⟨Q0, hQ0⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hQ2 : IsPGroup 2 (LinearFlag.unitriangular 3 K) := by
    rw [← hQ0]
    exact Q0.isPGroup'
  set e := specialLinearGroupEquivStatedSL 3 K with he
  obtain ⟨t, ht⟩ := Ml3.exists_conj_map_le_sylow hSΓ hJΓ hΓN (π.comp e.toMonoidHom)
    ((hreal 0).1.comp e.surjective) hQ2
  have hU : ∀ u ∈ LinearFlag.unitriangular 3 K,
      ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (Multiplicative.toAdd (β 0 ⟨a₀, ha₀⟩))) =
        ((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (Multiplicative.toAdd (β 0 ⟨a₀, ha₀⟩)) ∧
      ((u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        (((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (Multiplicative.toAdd (β 1 ⟨a₁, ha₁⟩))) =
        ((t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
          (Multiplicative.toAdd (β 1 ⟨a₁, ha₁⟩)) := by
    intro u hu
    obtain ⟨h0, h1⟩ := hvec (e (t⁻¹ * u * t)) (mem_stabAt.mp (hSw (ht u hu))).2
    exact ⟨Ml3.fixed_conj (congrArg Multiplicative.toAdd h0),
      Ml3.fixed_conj (congrArg Multiplicative.toAdd h1)⟩
  obtain ⟨h01, h02⟩ := Ml3.fixed_of_unitriangular _ (fun u hu => (hU u hu).1)
  obtain ⟨h11, h12⟩ := Ml3.fixed_of_unitriangular _ (fun u hu => (hU u hu).2)
  obtain ⟨ρ, hρ1, hρ3, hρx⟩ := Ml3.exists_statedSL_order_three
    (((t⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (Pi.single 0 1 : Fin 3 → K))
  have hρ0 : ((ρ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (Multiplicative.toAdd (β 0 ⟨a₀, ha₀⟩)) = Multiplicative.toAdd (β 0 ⟨a₀, ha₀⟩) := by
    rw [Ml3.eq_smul_of_mulVec h01 h02, Matrix.mulVec_smul, hρx]
  have hρ1' : ((ρ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
      (Multiplicative.toAdd (β 1 ⟨a₁, ha₁⟩)) = Multiplicative.toAdd (β 1 ⟨a₁, ha₁⟩) := by
    rw [Ml3.eq_smul_of_mulVec h11 h12, Matrix.mulVec_smul, hρx]
  have hc₀ : ((π ρ : ↥J) : MulAut W) a₀ * a₀⁻¹ ∈ fixV J :=
    (Ml3.corr_mem_iff (hN 0) (hβk 0) (hβe 0) ρ ⟨a₀, ha₀⟩).2 (by
      show Multiplicative.ofAdd _ = _
      rw [hρ0]
      rfl)
  have hc₁ : ((π ρ : ↥J) : MulAut W) a₁ * a₁⁻¹ ∈ fixV J :=
    (Ml3.corr_mem_iff (hN 1) (hβk 1) (hβe 1) ρ ⟨a₁, ha₁⟩).2 (by
      show Multiplicative.ofAdd _ = _
      rw [hρ1']
      rfl)
  refine Ml3.false_of_order_three hW hJΓ h3 hinj hρ1 hρ3 ?_
  have hγz : ((π ρ : ↥J) : MulAut W) z = z := mem_fixV.mp hz _ (π ρ).2
  have hcalc : ((π ρ : ↥J) : MulAut W) w * w⁻¹ =
      (((π ρ : ↥J) : MulAut W) a₀ * a₀⁻¹) * (((π ρ : ↥J) : MulAut W) a₁ * a₁⁻¹) := by
    rw [hw', map_mul, map_mul, hγz, ← div_eq_mul_inv, mul_div_mul_left_eq_div, mul_div_mul_comm,
      div_eq_mul_inv, div_eq_mul_inv]
  rw [hcalc]
  exact (fixV J).mul_mem hc₀ hc₁

end CFSG.Quasithin.S153N
