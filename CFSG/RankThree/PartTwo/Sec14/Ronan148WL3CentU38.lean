module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentGen
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTorus
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentBlock
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentCases
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentCoxeter
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentU38Mono
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentU38Two
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {ι : Type*}
  {α : ι → MulAut (projImage (slPi false 3 (2 ^ 3) K))}
  {e₀ : projImage (slPi false 3 (2 ^ 3) K)}

theorem inner_of_block_lift (hK : PiField false 2 3 K)
    {γ : MulAut (projImage (slPi false 3 (2 ^ 3) K))} (hγ3 : γ ^ 3 = 1) {y : GL (Fin 3) K}
    (hy : y ∈ glPi false 3 (2 ^ 3) K) (h01 : (y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h02 : (y : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h10 : (y : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : (y : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (hγ : ∀ m, (γ m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) :
    ∃ u, γ = MulAut.conj u := by
  have hq : ModThree false (2 ^ 3) := rfl
  have hq2 : 2 < 2 ^ 3 := by norm_num
  have hU := hK.unitary
  obtain ⟨c, hc3⟩ := pow_three_mem_scalars hK hq hq2 hγ3 hγ
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have h00 : (y : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [det_fin_three, h, h01, h02]
    ring
  set a := Units.mk0 _ h00 with ha
  have hrow : ∀ (B : Matrix (Fin 3) (Fin 3) K) (j : Fin 3),
      ((y : Matrix (Fin 3) (Fin 3) K) * B) 0 j = (y : Matrix (Fin 3) (Fin 3) K) 0 0 * B 0 j := by
    intro B j
    rw [Matrix.mul_apply, Fin.sum_univ_three, h01, h02]
    ring
  have hy3 : ((y ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
      (y : Matrix (Fin 3) (Fin 3) K) 0 0 ^ 3 := by
    rw [Units.val_pow_eq_pow_val, pow_succ', pow_succ', pow_one, hrow, hrow]
    ring
  have hac : a ^ 3 = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ha, Units.val_mk0, ← hy3, ← hc3]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have haN : a ∈ rootsOfUnity (qSubPi false (2 ^ 3)) K := by
    rw [mem_rootsOfUnity']
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) ((mem_glPi_false hU).mp hy)
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h10, h20, map_zero, zero_mul, mul_zero, add_zero, Matrix.one_apply_eq, hU.bar_apply] at h
    rw [ha, Units.val_mk0]
    change (y : Matrix (Fin 3) (Fin 3) K) 0 0 ^ (2 ^ 3 + 1) = 1
    rw [pow_succ]
    exact h
  obtain ⟨s, hs, hsy⟩ := exists_slPi_mk_eq hK hq (by decide) hy haN hc3.symm hac
  refine ⟨⟨pmk y, s, hs, hsy⟩, ?_⟩
  ext m
  rw [hγ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem cycThree_pow_three_U38 : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem fieldAct_U38 {β : MulAut (projImage (slPi false 3 (2 ^ 3) K))}
    (hβ : IsFieldAct false 2 3 K β) :
    ∃ (σ : K ≃+* K) (N : ℕ), (N = 4 ∨ N = 16) ∧ (∀ c, σ c = c ^ N) ∧
      ∃ g ∈ glPi false 3 (2 ^ 3) K, ∀ s (hs : s ∈ slPi false 3 (2 ^ 3) K),
        (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s * g⁻¹) := by
  obtain ⟨f₀, hf, σ, hσ, g, hg, hgx⟩ := hβ
  have hf₀ : f₀ = 1 := by omega
  subst hf₀
  rcases hσ with hσ | hσ
  · exact ⟨σ, 4, Or.inl rfl, hσ, g, hg, hgx⟩
  · exact ⟨σ, 16, Or.inr rfl, hσ, g, hg, hgx⟩

theorem CentConfig.false_of_U38 (hK : PiField false 2 3 K) (hc : CentConfig false 2 3 K α e₀)
    (he₀1 : e₀ ≠ 1) (he₀3 : e₀ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range α)) ∣ 9)
    (hd : (∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧
        (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) ∨
      (∃ ε : Kˣ, (ε : K) ^ 3 = 1 ∧ ε ≠ 1 ∧ (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε) ∧
        ModNine false (2 ^ 3))) : False := by
  have hq : ModThree false (2 ^ 3) := rfl
  have hq2 : 2 < 2 ^ 3 := by norm_num
  have hπ : false = false → UnitaryFieldData 2 3 K := fun _ => hK.unitary
  obtain ⟨x₀, hx₀⟩ := CentConfig.exists_outer (α := α) (hc.false_of_inner hK hq hq2 he₀1 he₀3)
  set γ := α x₀ with hγdef
  have hγR : γ ∈ Subgroup.closure (Set.range α) := Subgroup.subset_closure ⟨x₀, rfl⟩
  have hgen := hc.mem_sup hK hq hq2 he₀1 he₀3 hcard hγR hx₀
  have hγ3 : γ ^ 3 = 1 := hc.pow_three x₀
  have hγe : γ e₀ = e₀ := hc.fix x₀
  rcases hc.dich x₀ with ⟨y, hy, hyx⟩ | hfield
  ·
    rcases hd with ⟨τ, hτ, hτ1, he₀⟩ | ⟨ε, hε3, hε1, he₀, -⟩
    · obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx hγe he₀
      obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [pow_zero, mul_one] at hy hyx
        obtain ⟨u, hu⟩ := inner_of_block_lift hK hγ3 hy (by simp [coe_diagUnits])
          (by simp [coe_diagUnits]) (by simp [coe_diagUnits]) (by simp [coe_diagUnits]) hyx
        exact hx₀ u hu
      · exact hc.false_of_coxeter hK hq hq2 hτ hτ1 he₀ hγ3 hγe hx₀ hgen hk1 hk hy hyx
    · obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx hγe he₀
      obtain ⟨l01, l02, l10, l20⟩ := entries_of_commute_diagE hε1
        (commute_of_conj_diagE (hK.three_ne_zero hq) hε3 hc')
      obtain ⟨u, hu⟩ := inner_of_block_lift hK hγ3 hy l01 l02 l10 l20 hyx
      exact hx₀ u hu
  ·
    obtain ⟨σ, N, hN, hσ, g, hgH, hgx⟩ := fieldAct_U38 hfield
    rcases hd with ⟨τ, hτ, hτ1, he₀⟩ | ⟨ε, hε3, hε1, he₀, -⟩
    ·
      have hστ : σ τ = τ := by
        rw [hσ]
        rcases hN with rfl | rfl
        · rw [show 4 = 3 + 1 from rfl, pow_add, hτ, one_mul, pow_one]
        · rw [show 16 = 3 * 5 + 1 from rfl, pow_add, pow_mul, hτ, one_pow, one_mul, pow_one]
      obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hgx hγe
        (diagTau_mem_slPi hπ (fun _ => hq) hτ) he₀
      rw [frobGL_diagTau σ hτ hστ] at hc'
      obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
      interval_cases k
      · simp only [pow_zero, mul_one] at hgx
        exact hc.false_of_field_diag hK hτ hτ1 he₀ hgen hN hσ hgx
      · simp only [pow_one] at hgx hgH
        exact hc.false_of_field_mono hK hτ hτ1 he₀ hγ3 hgen hN hσ hgH hgx
      ·
        set σ₂ : K ≃+* K := σ.trans σ with hσ₂
        obtain ⟨N₂, hN₂, hσ₂N⟩ : ∃ N₂, (N₂ = 4 ∨ N₂ = 16) ∧ ∀ c, σ₂ c = c ^ N₂ := by
          rcases hN with rfl | rfl
          · refine ⟨16, Or.inr rfl, fun c => ?_⟩
            rw [hσ₂, RingEquiv.trans_apply, hσ, hσ, ← pow_mul]
          · refine ⟨4, Or.inl rfl, fun c => ?_⟩
            rw [hσ₂, RingEquiv.trans_apply, hσ, hσ, ← pow_mul,
              show 16 * 16 = 64 * 4 from rfl, pow_mul, pow_sixtyfour hK]
        have hfrob₂ : ∀ A, frobGL σ₂ A = frobGL σ (frobGL σ A) := fun A => by
          apply Units.ext
          rw [coe_frobGL, coe_frobGL, coe_frobGL]
          ext i j
          rfl
        set g₂ := (diagUnits a b c' * cycThree ^ 2) * frobGL σ (diagUnits a b c' * cycThree ^ 2)
          with hg₂
        have hg₂H : g₂ ∈ glPi false 3 (2 ^ 3) K :=
          mul_mem hgH (frobGL_mem_glPi hK σ hgH)
        obtain ⟨a', b', c'', hg₂m⟩ : ∃ a' b' c'' : Kˣ, g₂ = diagUnits a' b' c'' * cycThree := by
          rw [hg₂, map_mul, map_pow, frobGL_cycThree, frobGL_diagUnits]
          obtain ⟨x, y, z, hxyz⟩ := exists_cycThree_pow_conj_diagUnits 2
            (Units.map (σ : K →* K) a) (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c')
          refine ⟨a * x, b * y, c' * z, ?_⟩
          have hc4 : (cycThree : GL (Fin 3) K) ^ 4 = cycThree := by
            rw [show 4 = 3 + 1 from rfl, pow_add, cycThree_pow_three_U38, one_mul,
              pow_one]
          calc diagUnits a b c' * cycThree ^ 2 * (diagUnits (Units.map (σ : K →* K) a)
                (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c') * cycThree ^ 2) =
              diagUnits a b c' * (cycThree ^ 2 * diagUnits (Units.map (σ : K →* K) a)
                (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c') * (cycThree ^ 2)⁻¹) *
                cycThree ^ 4 := by
                rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
                group
            _ = diagUnits (a * x) (b * y) (c' * z) * cycThree := by
                rw [hxyz, hc4, diagUnits_mul]
        have hγ₂3 : (γ ^ 2) ^ 3 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hγ3, one_pow]
        have hgen₂ : ∀ x, α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers (γ ^ 2) := by
          have hz : Subgroup.zpowers (γ ^ 2) = Subgroup.zpowers γ := by
            apply le_antisymm
            · exact Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers γ 2)
            · refine Subgroup.zpowers_le.mpr ?_
              have : (γ ^ 2) ^ 2 = γ := by
                rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hγ3, one_mul, pow_one]
              have h2 := Subgroup.npow_mem_zpowers (γ ^ 2) 2
              rwa [this] at h2
          intro x
          rw [hz]
          exact hgen x
        have hγ₂ : ∀ s (hs : s ∈ slPi false 3 (2 ^ 3) K),
            ((γ ^ 2) (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
              pmk ((diagUnits a' b' c'' * cycThree) * frobGL σ₂ s *
                (diagUnits a' b' c'' * cycThree)⁻¹) := by
          intro s hs
          have hs1 : (diagUnits a b c' * cycThree ^ 2) * frobGL σ s *
              (diagUnits a b c' * cycThree ^ 2)⁻¹ ∈ slPi false 3 (2 ^ 3) K :=
            conj_mem_slPi hπ hgH (frobGL_mem_slPi hK σ hs)
          have hγ1 : γ (projOf _ ⟨s, hs⟩) = projOf _ ⟨_, hs1⟩ :=
            Subtype.ext (by rw [hgx, coe_projOf])
          rw [pow_two, MulAut.mul_apply, hγ1, hgx, ← hg₂m, hfrob₂, hg₂]
          simp only [map_mul, map_inv]
          group
        rw [hg₂m] at hg₂H
        exact hc.false_of_field_mono hK hτ hτ1 he₀ hγ₂3 hgen₂ hN₂ hσ₂N hg₂H hγ₂
    · exact hc.false_of_field_block hK hε3 hε1 he₀ hγ3 hγe hgen hN hσ hgH hgx

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
