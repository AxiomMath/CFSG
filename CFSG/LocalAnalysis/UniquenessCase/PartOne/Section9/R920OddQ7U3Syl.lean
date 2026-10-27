module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCountSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Root

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbedding.UnitaryModel
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
open scoped Pointwise

theorem not_dvd_sq_sub_one_mul {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (hpq : p ∣ q) :
    ¬ p ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have h1 : p ∣ 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have h2 : p ∣ (q ^ 2 - 1) + 1 := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)]
        exact dvd_pow hpq (by norm_num)
      exact (Nat.dvd_add_right h1).1 h2
    · exact (Nat.dvd_add_right (dvd_pow hpq (by norm_num : 3 ≠ 0))).1 h1
  exact hp.ne_one (Nat.dvd_one.1 h1)

theorem isSolvable_of_sylow_le_stated {L : Type} [Group L] [Finite L] {p f : ℕ} [Fact p.Prime]
    (hst : CFSG.Open.StatedClassicalModel L .PSU 3 p f) (U : Sylow p L) {H : Subgroup L}
    (hUH : (U : Subgroup L) ≤ H) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ := exists_equiv_psu hst
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  have hle : H.map e'.toMonoidHom ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
    refine le_stabilizer_pinf_of_rootGroup_le J hJ hK hfix hq ?_ ?_
    · rw [← hS, ← he']
      exact Subgroup.map_mono hUH
    · intro htop
      apply hH
      have := congrArg (Subgroup.comap e'.toMonoidHom) htop
      rwa [Subgroup.comap_map_eq_self_of_injective e'.injective, Subgroup.comap_top] at this
  haveI := isSolvable_stabilizer_pinf J hJ hK hfix
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).toMonoidHom)
    ((Subgroup.inclusion_injective hle).comp
      (Subgroup.equivMapOfInjective H e'.toMonoidHom e'.injective).injective)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem isPGroup_rootU : IsPGroup p (rootU hF) := by
  refine IsPGroup.of_card (n := 3 * f) ?_
  rw [card_rootGroup_three hF, ← pow_mul, mul_comm f 3]

theorem index_rootU : (rootU hF).index = ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have h := (rootU hF).card_mul_index
  rw [card_SU3 hF, card_rootGroup_three hF, mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos (Fact.out : p.Prime).pos f) 3) h

@[expose] noncomputable def rootSylow : Sylow p (SU (unitaryInvolution F p f) 3) :=
  (isPGroup_rootU hF).toSylow (by
    rw [index_rootU hF]
    have hf : f ≠ 0 := fun h0 => by
      have := two_le_prime_pow_of_card hF
      rw [h0, pow_zero] at this
      omega
    exact not_dvd_sq_sub_one_mul (Fact.out : p.Prime) (pow_pos (Fact.out : p.Prime).pos f)
      (dvd_pow_self p hf))

theorem exists_conj_mem_rootU {a : SU (unitaryInvolution F p f) 3} (ha : orderOf a = p) :
    ∃ g : SU (unitaryInvolution F p f) 3, g⁻¹ * a * g ∈ rootU hF := by
  have hP : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SU (unitaryInvolution F p f) 3) Q (rootSylow hF)
  have haQ : a ∈ (Q : Subgroup (SU (unitaryInvolution F p f) 3)) := hQ (Subgroup.mem_zpowers a)
  have hx' : MulAut.conj g • a ∈ MulAut.conj g • (Q : Subgroup (SU (unitaryInvolution F p f) 3)) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ haQ
  rw [← Sylow.coe_subgroup_smul, hg] at hx'
  simp only [MulAut.smul_def, MulAut.conj_apply] at hx'
  have hx'' : g * a * g⁻¹ ∈ rootU hF := hx'
  exact ⟨g⁻¹, by simpa using hx''⟩

theorem isSolvable_of_rootU_le
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f)
    {H : Subgroup (SU (unitaryInvolution F p f) 3)} (hUH : rootU hF ≤ H) (hH : H ≠ ⊤) :
    Group.IsSolvable H :=
  isSolvable_of_sylow_le_stated hst (rootSylow hF) hUH hH

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
