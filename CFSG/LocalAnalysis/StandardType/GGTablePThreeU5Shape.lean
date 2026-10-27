module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeEigen
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeNe
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeComp
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.RankThree.PartOne.KF.LayerModelRow
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIso
import CFSG.GH74.KGH
import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

private theorem isHermIsometry_of_mem_statedSU {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q ^ 2) {f : ℕ} (hf : 1 ≤ f) (hq : q = 2 ^ f)
    {n : ℕ} {d : GL (Fin n) K} (hd : d ∈ CFSG.Open.StatedSU n q K) :
    IsHermIsometry q (d : Matrix (Fin n) (Fin n) K) := by
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by rw [← hq, hK]
  let h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
  have hd' : d ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f K n := by
    show d ∈ CFSG.Open.StatedSU n (2 ^ f) K
    rw [← hq]
    exact hd
  have hiso := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp hd'
  have hbar : ∀ c : K, h.bar c = c ^ q := by
    intro c; rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, hq]
  intro v w
  have hh := hiso.2 v w
  simpa only [CFSG.LinearGroups.stdHermForm_apply, hbar] using hh

private theorem omega_cube {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h
  exact sub_eq_zero.mp h.symm

private theorem cube_roots_eq {K : Type} [Field K] {ω y : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hy : y ^ 3 = 1) : y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
  have hω3 : ω ^ 3 = 1 := omega_cube hω
  have hωsum : ω + ω ^ 2 = -1 := by linear_combination hω
  have hfac : (y - 1) * (y ^ 2 + y + 1) = 0 := by
    have h : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by ring
    rw [← h, hy, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · left; linear_combination h
  · right
    have hfac2 : (y - ω) * (y - ω ^ 2) = 0 := by
      have h2 : (y - ω) * (y - ω ^ 2) = y ^ 2 + y + 1 := by
        have h3 : (y - ω) * (y - ω ^ 2) = y ^ 2 - y * (ω + ω ^ 2) + ω ^ 3 := by ring
        rw [h3, hωsum, hω3]; ring
      rw [h2]; exact h
    rcases mul_eq_zero.mp hfac2 with h1 | h2
    · left; linear_combination h1
    · right; linear_combination h2

private theorem omega_sq_ne_one {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) : ω ^ 2 ≠ 1 := by
  intro h
  have h3 : ω ^ 3 = 1 := omega_cube hω
  apply hω1
  have h4 : ω ^ 3 = ω * ω ^ 2 := by ring
  rw [h4, h, mul_one] at h3
  exact h3

private theorem omega_ne_sq {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) : ω ≠ ω ^ 2 := by
  intro h
  apply omega_sq_ne_one hω hω1
  have h3 : ω ^ 3 = 1 := omega_cube hω
  have hh : ω ^ 2 = ω ^ 3 := by
    have := congrArg (fun t => t * ω) h
    rw [pow_two, pow_succ]
    exact this
  rw [h3] at hh
  exact hh

private theorem omega_sq_cube {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (ω ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega_cube hω, one_pow]

private theorem one_ne_omega_sq {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hω1 : ω ≠ 1) : (1 : K) ≠ ω ^ 2 :=
  fun h => omega_sq_ne_one hω hω1 h.symm

private theorem no_second_block {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    {d : GL (Fin 5) K} (hdherm : IsHermIsometry q (d : Matrix (Fin 5) (Fin 5) K))
    (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg 5 K q)} (hδ : IsConjBy d δ')
    {J' : Subgroup (PSUg 5 K q)}
    (huniq : ∀ Q : Subgroup (PSUg 5 K q),
      IsComponentOf Q (ggAutFixedSubgroup δ') → Q = J')
    {α : K} (hα3 : α ^ 3 = 1) (hJα : ∀ x, x ∈ J' ↔ InCubeBlock d α x)
    (hα2 : 2 ≤ Module.finrank K (cubeEigen d α))
    {β : K} (hβ3 : β ^ 3 = 1) (hβne : β ≠ α)
    (hβ2 : 2 ≤ Module.finrank K (cubeEigen d β)) (hq4 : 4 ≤ q) : False := by
  have hβQS : CubeBlockQS q d β := Or.inl ⟨hβ2, hq4⟩
  obtain ⟨Qβ, hQβc, hQβmem, -⟩ :=
    uni_cube_block_component hK hq3 (by norm_num : 4 ≤ 5) hdherm hd3 hδ hβ3 hβQS
  have hQβJ : Qβ = J' := huniq Qβ hQβc
  exact (uni_cube_blocks_ne hK hq3 (by norm_num : 4 ≤ 5) hdherm hd3 hα3 hβ3 hβne.symm hα2 hβ2)
    (fun x => by rw [← hJα x, ← hQβJ, hQβmem x])

section Certificates

theorem uni5_shape
    {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    {d : GL (Fin 5) K} (hd : d ∈ CFSG.Open.StatedSU 5 q K) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {δ' : MulAut (PSUg 5 K q)} (hδ : IsConjBy d δ')
    {J' : Subgroup (PSUg 5 K q)} (hJc : IsComponentOf J' (ggAutFixedSubgroup δ'))
    (huniq : ∀ Q : Subgroup (PSUg 5 K q), IsComponentOf Q (ggAutFixedSubgroup δ') → Q = J')
    {F : Type} [Field F] [Finite F] {q' : ℕ} (hF : Nat.card F = q' ^ 2) (hq' : 4 ≤ q')
    (htw : Nonempty (J' ⧸ Subgroup.center J' ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) F q'))) :
    ∃ α : K, α ^ 3 = 1 ∧
      Module.finrank K (Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) α) = 3 ∧
      (∀ β : K, β ^ 3 = 1 → β ≠ α →
        Module.finrank K (Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) β) = 1) ∧
      ∀ x ∈ J', ∃ g : ↥(LargeEvenSUGroup (Fin 5) K q), LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K q) g = x ∧
        ∀ β : K, β ^ 3 = 1 → β ≠ α → ∀ v ∈ Module.End.eigenspace
          (Matrix.toLin' (d : Matrix (Fin 5) (Fin 5) K)) β,
            ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v = v := by
  obtain ⟨f, hf, hqpow⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hdherm : IsHermIsometry q (d : Matrix (Fin 5) (Fin 5) K) :=
    isHermIsometry_of_mem_statedSU hK hf hqpow hd
  obtain ⟨α, hα3, hαQS, hJα⟩ :=
    uni_cube_component_block hK hq3 (by norm_num : 4 ≤ 5) hdherm hd3 hδ hJc
  have hq2 : 2 ≤ q := by
    rw [hqpow]
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hf
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hqs : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have := Nat.sq_sub_sq q 1
      simpa using this
    rw [hqs]
    exact dvd_mul_of_dvd_left hq3 (q - 1)
  obtain ⟨ω, hω, hω1⟩ := CFSG.RankThree.PartTwo.Sec21.Hering214.exists_primitive_cube_root h3K
  have hsum := (uni_cube_eigen hK hq3 hdherm hd3).2 ω hω
  have hαmem : α = 1 ∨ α = ω ∨ α = ω ^ 2 := cube_roots_eq hω hα3
  have hk_ne2 : Module.finrank K (cubeEigen d α) ≠ 2 := by
    intro hk2eq
    have hq4 : 4 ≤ q := by rcases hαQS with ⟨-, h⟩ | h <;> omega
    rcases hαmem with hα1 | hαω | hαω2
    · rw [hα1] at hk2eq hα3 hJα
      have h2 : 2 ≤ Module.finrank K (cubeEigen d ω) ∨
          2 ≤ Module.finrank K (cubeEigen d (ω ^ 2)) := by
        rw [hk2eq] at hsum; omega
      rcases h2 with h2 | h2
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (omega_cube hω) hω1 h2 hq4
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (omega_sq_cube hω) (one_ne_omega_sq hω hω1).symm h2 hq4
    · rw [hαω] at hk2eq hα3 hJα
      have h2 : 2 ≤ Module.finrank K (cubeEigen d 1) ∨
          2 ≤ Module.finrank K (cubeEigen d (ω ^ 2)) := by
        rw [hk2eq] at hsum; omega
      rcases h2 with h2 | h2
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (by norm_num) (fun h => hω1 h.symm) h2 hq4
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (omega_sq_cube hω) (omega_ne_sq hω hω1).symm h2 hq4
    · rw [hαω2] at hk2eq hα3 hJα
      have h2 : 2 ≤ Module.finrank K (cubeEigen d 1) ∨
          2 ≤ Module.finrank K (cubeEigen d ω) := by
        rw [hk2eq] at hsum; omega
      rcases h2 with h2 | h2
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (by norm_num) (one_ne_omega_sq hω hω1) h2 hq4
      · exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by rw [hk2eq])
          (omega_cube hω) (omega_ne_sq hω hω1) h2 hq4
  have hk2' : 2 ≤ Module.finrank K (cubeEigen d α) := by
    rcases hαQS with ⟨h, -⟩ | h <;> omega
  have hk3 : Module.finrank K (cubeEigen d α) = 3 := by
    by_cases hk4 : 4 ≤ Module.finrank K (cubeEigen d α)
    · exfalso
      obtain ⟨Q, hQc, hQmem, hQquot⟩ :=
        uni_cube_block_component hK hq3 (by norm_num : 4 ≤ 5) hdherm hd3 hδ hα3 hαQS
      have hQJ : Q = J' := huniq Q hQc
      obtain ⟨eQ⟩ := hQquot
      obtain ⟨etw⟩ := htw
      have hQQ : Q ⧸ Subgroup.center Q ≃* J' ⧸ Subgroup.center J' := by
        rw [hQJ]
      have hiso : Nonempty
          (LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d α))) K q) ≃*
            LargeEvenProj (LargeEvenSUGroup (Fin 3) F q')) :=
        ⟨eQ.symm.trans (hQQ.trans etw)⟩
      subst hqpow
      have hK'' : Nat.card K = (2 ^ f) ^ 2 := hK
      have hadmX : CFSG.Open.StatedLieAdmissible .PSU
          (Module.finrank K (cubeEigen d α)) 2 f := by
        rw [CFSG.Open.StatedLieAdmissible]
        exact ⟨Nat.prime_two, hf, by omega,
          by intro h; exact absurd (congrArg Prod.fst h) (by omega)⟩
      have hscmX : CFSG.Open.StatedClassicalModel
          (LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d α))) K (2 ^ f)))
          .PSU (Module.finrank K (cubeEigen d α)) 2 f :=
        CFSG.StandardType.statedClassicalModel_unitary _ f hK'' hadmX
      have hX : CFSG.Blueprint.LieModel
          (LargeEvenProj (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d α))) K (2 ^ f)))
          .PSU (Module.finrank K (cubeEigen d α)) 2 f :=
        CFSG.RankThree.PartOne.lieModel_of_scm_psu hscmX
      obtain ⟨e⟩ := hiso
      haveI : Fintype F := Fintype.ofFinite F
      obtain ⟨p, hchar, n, hp, hcard'⟩ := FiniteField.card' (K := F)
      have hcard'' : Nat.card F = p ^ (n : ℕ) := by
        rw [Nat.card_eq_fintype_card, hcard']
      have hq'dvd : q' ∣ p ^ (n : ℕ) := by
        have hp' : p ^ (n : ℕ) = q' ^ 2 := by rw [← hcard'', hF]
        rw [hp']
        exact dvd_pow_self q' (by norm_num : 2 ≠ 0)
      obtain ⟨k, -, hkq'⟩ := (Nat.dvd_prime_pow hp).mp hq'dvd
      subst hkq'
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0; rw [pow_zero] at hq'; omega
        · exact hpos
      have hscmY2 : CFSG.Open.StatedClassicalModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (p ^ k)))
          .PSU (Module.finrank K (cubeEigen d α)) 2 f := by
        rw [CFSG.Open.StatedClassicalModel]
        refine ⟨hadmX, K, inferInstance, inferInstance, hK'', ?_⟩
        exact ⟨e.symm⟩
      have hb : CFSG.Blueprint.LieModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (p ^ k)))
          .PSU (Module.finrank K (cubeEigen d α)) 2 f :=
        CFSG.GH74.lieModel_of_statedClassicalModel (by decide) hscmY2
      have hadmY' : CFSG.Open.StatedLieAdmissible .PSU 3 p k := by
        rw [CFSG.Open.StatedLieAdmissible]
        refine ⟨hp, hk1, by norm_num, ?_⟩
        intro h
        have h2 : p ^ k = 2 := by simpa using congrArg Prod.snd h
        rw [h2] at hq'
        omega
      have hscmY' : CFSG.Open.StatedClassicalModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (p ^ k))) .PSU 3 p k := by
        rw [CFSG.Open.StatedClassicalModel]
        refine ⟨hadmY', F, inferInstance, inferInstance, hF, ?_⟩
        exact ⟨MulEquiv.refl _⟩
      have hb' : CFSG.Blueprint.LieModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (p ^ k))) .PSU 3 p k :=
        CFSG.GH74.lieModel_of_statedClassicalModel (by decide) hscmY'
      have hp2 : p = 2 := by
        by_contra hpne
        exact CFSG.LocalAnalysis.GLTheoremA.YS05NonIso.char2_absurd hb hb' hpne
          (by rintro ⟨h, -⟩; exact absurd h (by decide))
          (by rintro ⟨h, -⟩; exact absurd h (by decide))
          (by rintro ⟨-, -, h, -⟩; exact absurd h (by decide))
      haveI : CharP F 2 := by rw [← hp2]; exact hchar
      obtain ⟨f', hf', hq'pow⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hF
      rw [hq'pow] at hF hq' e
      have hF'' : Nat.card F = (2 ^ f') ^ 2 := hF
      have hadmY : CFSG.Open.StatedLieAdmissible .PSU 3 2 f' := by
        rw [CFSG.Open.StatedLieAdmissible]
        refine ⟨Nat.prime_two, hf', by norm_num, ?_⟩
        intro h
        have h2 : 2 ^ f' = 2 := by simpa using congrArg Prod.snd h
        rw [h2] at hq'
        omega
      have hscmY : CFSG.Open.StatedClassicalModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ f'))) .PSU 3 2 f' :=
        CFSG.StandardType.statedClassicalModel_unitary 3 f' hF'' hadmY
      have hY : CFSG.Blueprint.LieModel
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ f'))) .PSU 3 2 f' :=
        CFSG.RankThree.PartOne.lieModel_of_scm_psu hscmY
      have hcard : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin 3) F (2 ^ f'))) =
          Nat.card (LargeEvenProj
            (LargeEvenSUGroup (Fin (Module.finrank K (cubeEigen d α))) K (2 ^ f))) :=
        (Nat.card_congr e.toEquiv).symm
      obtain ⟨-, hn, -⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq hk4 hX hY hcard
      omega
    · omega
  have hq4 : 4 ≤ q := by rcases hαQS with ⟨-, h⟩ | h <;> omega
  have hother_le : ∀ β : K, β ^ 3 = 1 → β ≠ α →
      Module.finrank K (cubeEigen d β) ≤ 1 := by
    intro β hβ3 hβne
    by_contra h
    simp only [not_le] at h
    exact no_second_block hK hq3 hdherm hd3 hδ huniq hα3 hJα (by omega) hβ3 hβne h hq4
  have hdim : ∀ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) → μ ≠ α →
      Module.finrank K (cubeEigen d μ) = 1 := by
    intro μ hμmem hμne
    have hle : Module.finrank K (cubeEigen d μ) ≤ 1 := by
      rcases hμmem with hμ1 | hμω | hμω2
      · rw [hμ1] at hμne ⊢
        exact hother_le 1 (by norm_num) hμne
      · rw [hμω] at hμne ⊢
        exact hother_le ω (omega_cube hω) hμne
      · rw [hμω2] at hμne ⊢
        exact hother_le (ω ^ 2) (omega_sq_cube hω) hμne
    rcases hαmem with hα1 | hαω | hαω2
    · rw [hα1] at hk3
      rcases hμmem with hμ1 | hμω | hμω2
      · rw [hα1, hμ1] at hμne
        exact absurd rfl hμne
      · rw [hμω] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
          hother_le (ω ^ 2) (omega_sq_cube hω) (by rw [hα1]; exact (one_ne_omega_sq hω hω1).symm)
        omega
      · rw [hμω2] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d ω) ≤ 1 :=
          hother_le ω (omega_cube hω) (by rw [hα1]; exact hω1)
        omega
    · rw [hαω] at hk3
      rcases hμmem with hμ1 | hμω | hμω2
      · rw [hμ1] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d (ω ^ 2)) ≤ 1 :=
          hother_le (ω ^ 2) (omega_sq_cube hω) (by rw [hαω]; exact (omega_ne_sq hω hω1).symm)
        omega
      · rw [hμω] at hμne ⊢
        rw [hαω] at hμne
        exact absurd rfl hμne
      · rw [hμω2] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d 1) ≤ 1 :=
          hother_le 1 (by norm_num) (by rw [hαω]; exact fun h => hω1 h.symm)
        omega
    · rw [hαω2] at hk3
      rcases hμmem with hμ1 | hμω | hμω2
      · rw [hμ1] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d ω) ≤ 1 :=
          hother_le ω (omega_cube hω) (by rw [hαω2]; exact omega_ne_sq hω hω1)
        omega
      · rw [hμω] at hle hμne ⊢
        have hle2 : Module.finrank K (cubeEigen d 1) ≤ 1 :=
          hother_le 1 (by norm_num) (by rw [hαω2]; exact one_ne_omega_sq hω hω1)
        omega
      · rw [hμω2] at hμne ⊢
        rw [hαω2] at hμne
        exact absurd rfl hμne
  refine ⟨α, hα3, hk3, ?_, ?_⟩
  · intro β hβ3 hβne
    exact hdim β (cube_roots_eq hω hβ3) hβne
  · intro x hx
    exact (hJα x).mp hx

end Certificates

end CFSG.StandardType.TablePThreeKG

end

