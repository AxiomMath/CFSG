module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUniDich
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Geo
import CFSG.GH74.Generic.BProg.B2.GenLocU4QSu4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.SubgroupLists
open CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem conj_tvSU (g : unitarySU 2 f K 3) {a b : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0)
    (hb : barVec h b ⬝ᵥ b = 0)
    (hgab : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a = b) {c : K}
    (hc : h.bar c = c) : g * tvSU h a ha hc * g⁻¹ = tvSU h b hb hc := by
  apply suToSL_injective h
  have hxa : barVec h (((suToSL h g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ a) ⬝ᵥ (((suToSL h g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ a) = 0 := by
    rw [coe_suToSL, hgab]
    exact hb
  rw [map_mul, map_mul, map_inv, suToSL_tvSU, suToSL_tvSU,
    conj_rankOneSL_bar h ⟨g, rfl⟩ ha hxa c]
  apply Subtype.ext
  rw [coe_rankOneSL, coe_rankOneSL, coe_suToSL, hgab]

theorem omega_facts [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 ∧ ω + ω ^ 2 = 1 ∧ ω ^ 4 = ω := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  refine ⟨h3, by linear_combination hω - h2, ?_⟩
  linear_combination ω * h3

theorem eq_top_of_tvSU_mem (hq : 2 ^ f ≠ 2) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hωbar : h.bar ω = ω ^ 2) (H : Subgroup (unitarySU 2 f K 3)) (d : unitarySU 2 f K 3)
    (hd : ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ω, ω ^ 2, 1])
    (hdH : d ∈ H) (P : unitarySU 2 f K 3)
    (hP : ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3CycMat) (hPH : P ∈ H)
    (ha₀ : barVec h ![1, 1, 0] ⬝ᵥ ![1, 1, 0] = 0)
    (hA : ∀ (c : K) (hc : h.bar c = c), tvSU h ![1, 1, 0] ha₀ hc ∈ H) : H = ⊤ := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hω3, hωω, hω4⟩ := omega_facts hω
  set σ₀ := barEquiv h with hσ₀def
  have hσ₀ : ∀ x, σ₀ x = h.bar x := barEquiv_apply h
  have hσU : IsUnitaryInvolution σ₀ :=
    isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hSU : SUid σ₀ 3 = unitarySU 2 f K 3 := SUid_eq_statedSU h.card_eq_sq 3
  set HG := H.map (unitarySU 2 f K 3).subtype with hHG
  have hmemG : ∀ g : unitarySU 2 f K 3, g ∈ H → (g : GL (Fin 3) K) ∈ HG :=
    fun g hg => ⟨g, hg, rfl⟩
  have hb₀ : barVec h ![ω, ω ^ 2, 0] ⬝ᵥ ![ω, ω ^ 2, 0] = 0 := by
    have e : barVec h ![ω, ω ^ 2, 0] ⬝ᵥ ![ω, ω ^ 2, 0] =
        h.bar ω * ω + h.bar (ω ^ 2) * ω ^ 2 := by
      simp [dotProduct, Fin.sum_univ_three, barVec_apply]
    rw [e, map_pow, hωbar]
    linear_combination (ω ^ 3 + 2) * hω3 + h2
  have hda : ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 1, 0] = ![ω, ω ^ 2, 0] := by
    rw [hd]
    ext i
    fin_cases i <;> simp [mulVec_diagonal]
  have hB : ∀ (c : K) (hc : h.bar c = c), tvSU h ![ω, ω ^ 2, 0] hb₀ hc ∈ H := by
    intro c hc
    rw [← conj_tvSU h d ha₀ hb₀ hda hc]
    exact H.mul_mem (H.mul_mem hdH (hA c hc)) (H.inv_mem hdH)
  have hbar_of : ∀ c : K, c + σ₀ c = 0 → h.bar c = c := by
    intro c hc
    rw [hσ₀] at hc
    linear_combination hc - c * h2
  have hblock : ∀ (v : Fin 2 → K) (hv : herm σ₀ v v = 0) (c : K) (hc : c + σ₀ c = 0)
      (w : Fin 3 → K) (hw0 : w 0 = v 0) (hw1 : w 1 = v 1) (hw2 : w 2 = 0)
      (hw3 : barVec h w ⬝ᵥ w = 0),
      blockGL3 ((tv hσU.invol hv hc : SUid σ₀ 2) : GL (Fin 2) K) =
        ((tvSU h w hw3 (hbar_of c hc) : unitarySU 2 f K 3) : GL (Fin 3) K) := by
    intro v hv c hc w hw0 hw1 hw2 hw3
    apply Units.ext
    rw [coe_blockGL3]
    show leviMat (tvMat σ₀ v c) = 1 + c • vecMulVec w (barVec h w)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [leviMat, tvMat, vecMulVec_apply, barVec_apply, hσ₀, hw0, hw1, hw2]
  have hva : herm σ₀ ![1, 1] ![1, 1] = 0 := by
    have e : herm σ₀ ![1, 1] ![1, 1] = σ₀ 1 * 1 + σ₀ 1 * 1 := by
      rw [herm_def, Fin.sum_univ_two]
      rfl
    rw [e, map_one]
    linear_combination h2
  have hvb : herm σ₀ ![ω, ω ^ 2] ![ω, ω ^ 2] = 0 := by
    have e : herm σ₀ ![ω, ω ^ 2] ![ω, ω ^ 2] = σ₀ ω * ω + σ₀ (ω ^ 2) * ω ^ 2 := by
      rw [herm_def, Fin.sum_univ_two]
      rfl
    rw [e, map_pow, hσ₀, hωbar]
    linear_combination (ω ^ 3 + 2) * hω3 + h2
  have hvab : herm σ₀ ![1, 1] ![ω, ω ^ 2] = 1 := by
    have e : herm σ₀ ![1, 1] ![ω, ω ^ 2] = σ₀ 1 * ω + σ₀ 1 * ω ^ 2 := by
      rw [herm_def, Fin.sum_univ_two]
      rfl
    rw [e, map_one]
    linear_combination hωω
  have hexp : ∀ v : Fin 2 → K, v = herm σ₀ ![ω, ω ^ 2] v • ![1, 1] +
      herm σ₀ ![1, 1] v • ![ω, ω ^ 2] := by
    intro v
    have e1 : herm σ₀ ![ω, ω ^ 2] v = ω ^ 2 * v 0 + ω ^ 4 * v 1 := by
      have e : herm σ₀ ![ω, ω ^ 2] v = σ₀ ω * v 0 + σ₀ (ω ^ 2) * v 1 := by
        rw [herm_def, Fin.sum_univ_two]
        rfl
      rw [e, map_pow, hσ₀, hωbar]
      ring
    have e2 : herm σ₀ ![1, 1] v = v 0 + v 1 := by
      have e : herm σ₀ ![1, 1] v = σ₀ 1 * v 0 + σ₀ 1 * v 1 := by
        rw [herm_def, Fin.sum_univ_two]
        rfl
      rw [e, map_one, one_mul, one_mul]
    rw [e1, e2]
    ext i
    fin_cases i
    · show v 0 = (ω ^ 2 * v 0 + ω ^ 4 * v 1) * 1 + (v 0 + v 1) * ω
      linear_combination (-v 0) * hωω - v 1 * hω4 - ω * v 1 * h2
    · show v 1 = (ω ^ 2 * v 0 + ω ^ 4 * v 1) * 1 + (v 0 + v 1) * ω ^ 2
      linear_combination (-ω ^ 2 * v 0) * h2 - v 1 * hω4 - v 1 * hωω
  have hdetP : (![1, 1] : Fin 2 → K) 0 * (![ω, ω ^ 2] : Fin 2 → K) 1 -
      (![ω, ω ^ 2] : Fin 2 → K) 0 * (![1, 1] : Fin 2 → K) 1 ≠ 0 := by
    have e : (![1, 1] : Fin 2 → K) 0 * (![ω, ω ^ 2] : Fin 2 → K) 1 -
        (![ω, ω ^ 2] : Fin 2 → K) 0 * (![1, 1] : Fin 2 → K) 1 = 1 * ω ^ 2 - ω * 1 := rfl
    rw [e]
    intro h0
    exact one_ne_zero (by linear_combination h0 - hωω + ω * h2 : (1 : K) = 0)
  set Γ := (HG.comap blockGL3).comap (SUid σ₀ 2).subtype with hΓ
  have hΓall : ∀ A : SUid σ₀ 2, A ∈ Γ := by
    intro A
    refine GH74.Generic.BProg.B2.GenLocU4QSu4.mem_of_two_tv hσU hva hvb hvab hexp hdetP Γ ?_ ?_ A
    · intro c hc
      show blockGL3 ((tv hσU.invol hva hc : SUid σ₀ 2) : GL (Fin 2) K) ∈ HG
      rw [hblock ![1, 1] hva c hc ![1, 1, 0] rfl rfl rfl ha₀]
      exact hmemG _ (hA c (hbar_of c hc))
    · intro c hc
      show blockGL3 ((tv hσU.invol hvb hc : SUid σ₀ 2) : GL (Fin 2) K) ∈ HG
      rw [hblock ![ω, ω ^ 2] hvb c hc ![ω, ω ^ 2, 0] rfl rfl rfl hb₀]
      exact hmemG _ (hB c (hbar_of c hc))
  have hstab2 : u3Stab σ₀ 2 ≤ HG := by
    rw [u3Stab_two_eq_range]
    rintro _ ⟨A, rfl⟩
    exact hΓall A
  have hPG : (u3CycGL : GL (Fin 3) K) ∈ HG := by
    have e : (P : GL (Fin 3) K) = u3CycGL := Units.ext hP
    rw [← e]
    exact hmemG P hPH
  have hconj : ∀ (k : Fin 3) (c : GL (Fin 3) K), c ∈ HG → c ∈ SUid σ₀ 3 →
      (c : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single k 1 →
      u3Stab σ₀ k ≤ HG := by
    intro k c hcH hcU hck g hg
    have hcs : c • (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single k (1 : K) := hck
    have hcs' : c⁻¹ • (Pi.single k (1 : K) : Fin 3 → K) = Pi.single 2 (1 : K) := by
      rw [inv_smul_eq_iff, hcs]
    obtain ⟨hgU, hgs⟩ := mem_u3Stab.1 hg
    have hgs' : g • (Pi.single k (1 : K) : Fin 3 → K) = Pi.single k (1 : K) := hgs
    have hg' : c⁻¹ * g * c ∈ u3Stab σ₀ 2 := by
      refine mem_u3Stab.2 ⟨mul_mem (mul_mem (inv_mem hcU) hgU) hcU, ?_⟩
      show (c⁻¹ * g * c) • (Pi.single 2 (1 : K) : Fin 3 → K) = Pi.single 2 (1 : K)
      rw [mul_smul, mul_smul, hcs, hgs', hcs']
    have e : g = c * (c⁻¹ * g * c) * c⁻¹ := by group
    rw [e]
    exact HG.mul_mem (HG.mul_mem hcH (hstab2 hg')) (HG.inv_mem hcH)
  have hstab : ∀ k, u3Stab σ₀ k ≤ HG := by
    intro k
    fin_cases k
    · exact hconj 0 u3CycGL hPG (u3CycGL_mem σ₀) u3CycGL_mulVec_two
    · refine hconj 1 (u3CycGL * u3CycGL) (HG.mul_mem hPG hPG)
        (mul_mem (u3CycGL_mem σ₀) (u3CycGL_mem σ₀)) ?_
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, u3CycGL_mulVec_two, u3CycGL_mulVec_zero]
    · exact hstab2
  have hnorm := CFSG.ClassicalGroups.Unitary.exists_norm_ne_one (p := 2) h.card_eq_sq hq
  have hall := u3_le_of_stab hσU hnorm HG hstab
  rw [eq_top_iff]
  intro g _
  have hgU : (g : GL (Fin 3) K) ∈ SUid σ₀ 3 := by rw [hSU]; exact g.2
  obtain ⟨g', hg', hgg⟩ := hall hgU
  have : g' = g := Subtype.ext hgg
  rw [← this]
  exact hg'

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
