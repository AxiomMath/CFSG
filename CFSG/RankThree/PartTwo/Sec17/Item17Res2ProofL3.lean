module

public import CFSG.RankThree.PartTwo.Sec17.Item17ResProofL3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Heis

variable {Y : Type} [Group Y]

theorem pow_mul_pow_heis {a b δ : Y} (hab : Commute a b) (haδ : Commute a δ)
    (hδb : δ * b = a * b * δ) (m j : ℕ) : δ ^ m * b ^ j = a ^ (m * j) * b ^ j * δ ^ m := by
  have h1 : ∀ j : ℕ, δ * b ^ j = a ^ j * b ^ j * δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : b ^ j * a = a * b ^ j := ((hab.pow_right j).eq).symm
      calc δ * b ^ (j + 1) = (δ * b ^ j) * b := by rw [pow_succ, mul_assoc]
        _ = a ^ j * b ^ j * (δ * b) := by rw [ih]; simp only [mul_assoc]
        _ = a ^ j * (b ^ j * a) * b * δ := by rw [hδb]; simp only [mul_assoc]
        _ = a ^ (j + 1) * b ^ (j + 1) * δ := by
          rw [hc, pow_succ, pow_succ]; simp only [mul_assoc]
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : δ ^ m * a ^ j = a ^ j * δ ^ m := ((haδ.pow_pow j m).eq).symm
    calc δ ^ (m + 1) * b ^ j = δ ^ m * (δ * b ^ j) := by rw [pow_succ, mul_assoc]
      _ = (δ ^ m * a ^ j) * b ^ j * δ := by rw [h1]; simp only [mul_assoc]
      _ = a ^ j * (δ ^ m * b ^ j) * δ := by rw [hc]; simp only [mul_assoc]
      _ = (a ^ j * a ^ (m * j)) * b ^ j * (δ ^ m * δ) := by rw [ih]; simp only [mul_assoc]
      _ = a ^ ((m + 1) * j) * b ^ j * δ ^ (m + 1) := by
        rw [← pow_add, ← pow_succ, show j + m * j = (m + 1) * j by ring]

theorem mul_heis {a b δ : Y} (hab : Commute a b) (haδ : Commute a δ)
    (hδb : δ * b = a * b * δ) (i j m i' j' m' : ℕ) :
    (a ^ i * b ^ j * δ ^ m) * (a ^ i' * b ^ j' * δ ^ m') =
      a ^ (i + i' + m * j') * b ^ (j + j') * δ ^ (m + m') := by
  have h1 : δ ^ m * a ^ i' = a ^ i' * δ ^ m := ((haδ.pow_pow i' m).eq).symm
  have h2 : b ^ j * a ^ i' = a ^ i' * b ^ j := ((hab.pow_pow i' j).eq).symm
  have h3 : b ^ j * a ^ (m * j') = a ^ (m * j') * b ^ j := ((hab.pow_pow (m * j') j).eq).symm
  calc (a ^ i * b ^ j * δ ^ m) * (a ^ i' * b ^ j' * δ ^ m')
      = a ^ i * b ^ j * (δ ^ m * a ^ i') * b ^ j' * δ ^ m' := by simp only [mul_assoc]
    _ = a ^ i * (b ^ j * a ^ i') * (δ ^ m * b ^ j') * δ ^ m' := by
        rw [h1]; simp only [mul_assoc]
    _ = a ^ i * a ^ i' * (b ^ j * a ^ (m * j')) * b ^ j' * (δ ^ m * δ ^ m') := by
        rw [h2, pow_mul_pow_heis hab haδ hδb]; simp only [mul_assoc]
    _ = a ^ (i + i' + m * j') * b ^ (j + j') * δ ^ (m + m') := by
        rw [h3, pow_add, pow_add, pow_add, pow_add]; simp only [mul_assoc]

theorem pow_three_heis {a b δ : Y} (hab : Commute a b) (haδ : Commute a δ)
    (hδb : δ * b = a * b * δ) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hδ : δ ^ 3 = 1)
    (i j m : ℕ) : (a ^ i * b ^ j * δ ^ m) ^ 3 = 1 := by
  have hz : ∀ e₁ e₂ e₃ : ℕ, 3 ∣ e₁ → 3 ∣ e₂ → 3 ∣ e₃ → a ^ e₁ * b ^ e₂ * δ ^ e₃ = 1 := by
    rintro _ _ _ ⟨k₁, rfl⟩ ⟨k₂, rfl⟩ ⟨k₃, rfl⟩
    simp [pow_mul, ha, hb, hδ]
  rw [pow_three, mul_heis hab haδ hδb, mul_heis hab haδ hδb]
  exact hz _ _ _ ⟨i + m * j, by ring⟩ ⟨j, by ring⟩ ⟨m, by ring⟩

theorem exists_pow_eq_zpow_of_pow_three {a : Y} (ha : a ^ 3 = 1) (i : ℤ) :
    ∃ n : ℕ, a ^ i = a ^ n := by
  refine ⟨(i % 3).toNat, ?_⟩
  have h := Int.emod_add_mul_ediv i 3
  conv_lhs => rw [← h]
  rw [zpow_add, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ha, one_zpow,
    mul_one, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]

theorem pow_three_eq_one_of_mem_heis [Finite Y] {a b δ : Y} (hab : a * b = b * a)
    (haδ : a * δ = δ * a) (hδb : δ * b * δ⁻¹ = a * b) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hδ : δ ^ 3 = 1) {x : Y}
    (hx : x ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers δ) : x ^ 3 = 1 := by
  have hδa : δ * a * δ⁻¹ = a := by rw [← haδ]; group
  have hδb' : δ * b = a * b * δ := by rw [← hδb]; group
  have hN : δ ∈ Subgroup.normalizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Y) : Set Y) := by
    refine Sec13.Item138Proof.mem_normalizer_sup_zpowers ?_ ?_
    · rw [hδa]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · rw [hδb]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  obtain ⟨l, hl, m, -, rfl⟩ := CFSG.SectionRank.OddCover.exists_mul_pow_of_mem_sup_zpowers hN hx
  obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup hab hl
  obtain ⟨i', hi'⟩ := exists_pow_eq_zpow_of_pow_three ha i
  obtain ⟨j', hj'⟩ := exists_pow_eq_zpow_of_pow_three hb j
  rw [hi', hj']
  exact pow_three_heis hab haδ hδb' ha hb hδ i' j' m

end Heis


section Model

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_threeSubgroup_model (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Finite K] [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] :
    ∃ P₀ : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))), (∀ x ∈ P₀, x ^ 3 = 1) ∧
      ∃ a ∈ P₀, ∃ b ∈ P₀, a * b ≠ b * a := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set M := projImage (slPi π 3 (p ^ f) K) with hM
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have := Sec19.Item19ResProof.finite_mulAut M
  have hZ := center_projImage_eq_bot hK hq
  have hinj := Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, -, -⟩ :=
    Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  have ht := Sec19.Item19ResProof.mk_mem_normalizer_projImage hπ (phaseGL_mem_glPi hK hq hτ)
  set δ : MulAut M := M.normalizerMonoidHom ⟨_, ht⟩ with hδ
  have hδd : δ dM = dM := Subtype.ext (by
    rw [hδ, normalizerMonoidHom_apply_coe, hdM, mk_phase_diagTau])
  have hδc : δ cM = dM * cM := Subtype.ext (by
    rw [hδ, normalizerMonoidHom_apply_coe, hcM, mk_phase_cycThree, Subgroup.coe_mul, hdM, hcM])
  have hδ3 : δ ^ 3 = 1 := by
    rw [hδ, ← map_pow]
    have h1 : (⟨_, ht⟩ : Subgroup.normalizer ((M : Subgroup (ProjGenLinGroup (Fin 3) K)) :
        Set (ProjGenLinGroup (Fin 3) K))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, ← map_pow, Sec19.Item19ResProof.phaseGL_pow_three, map_one]
      rfl)
    rw [h1, map_one]
  set a : MulAut M := MulAut.conj dM with ha
  set b : MulAut M := MulAut.conj cM with hb
  have hab : a * b = b * a := by rw [ha, hb, ← map_mul, hdc, map_mul]
  have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
  have hc3 : cM ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hcM, ← map_pow, cycThree_pow_three, map_one]
    rfl)
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hd3, map_one]
  have hb3 : b ^ 3 = 1 := by rw [hb, ← map_pow, hc3, map_one]
  have hδa : δ * a * δ⁻¹ = a := by
    rw [ha, KFacts.mul_mulAutConj_mul_inv, hδd]
  have hδb : δ * b * δ⁻¹ = a * b := by
    rw [hb, KFacts.mul_mulAutConj_mul_inv, hδc, map_mul]
  have haδ : a * δ = δ * a := by
    calc a * δ = δ * a * δ⁻¹ * δ := by rw [hδa]
      _ = δ * a := by group
  refine ⟨(Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers δ,
    fun x hx => pow_three_eq_one_of_mem_heis hab haδ hδb ha3 hb3 hδ3 hx,
    δ, Subgroup.mem_sup_right (Subgroup.mem_zpowers δ),
    b, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)), ?_⟩
  intro h
  have h1 : δ * b * δ⁻¹ = b := by rw [h]; group
  rw [hδb] at h1
  have h2 : a = 1 := by
    calc a = a * b * b⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have h3 : dM = 1 := hinj (by rw [← ha, h2, map_one])
  rw [h3, orderOf_one] at hdo
  omega

end Model

theorem not_modNine_of_not_dvd {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi X p e) (h27 : ¬ 27 ∣ Nat.card X) :
    p ^ e % 9 ≠ 1 ∧ p ^ e % 9 ≠ 8 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have h81 : Sec4.ModNine π (p ^ e) → 27 ∣ Nat.card X := fun h9 => by
    have := (Sec13.modNine_iff_dvd_card hK hq).mp h9
    rw [← Nat.card_congr φ.toEquiv] at this
    exact (by norm_num : 27 ∣ 81).trans this
  cases π
  · change p ^ e % 3 = 2 at hq
    refine ⟨by omega, fun h8 => h27 (h81 ?_)⟩
    change p ^ e % 9 = 8
    exact h8
  · change p ^ e % 3 = 1 at hq
    refine ⟨fun h1 => h27 (h81 ?_), by omega⟩
    change p ^ e % 9 = 1
    exact h1

theorem pow_three_eq_one_of_sylow_bound {Y : Type*} [Group Y] [Finite Y]
    (h27 : ∀ P : Subgroup Y, IsPGroup 3 P → Nat.card P ≤ 27) {P₀ : Subgroup Y}
    (hP₀ : IsPGroup 3 P₀) (hP₀27 : Nat.card P₀ = 27) (hP₀3 : ∀ x ∈ P₀, x ^ 3 = 1) {σ : Y}
    {k : ℕ} (hσ : σ ^ 3 ^ k = 1) : σ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : IsPGroup 3 (Subgroup.zpowers σ) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (σ ^ n) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hσ,
      _root_.one_zpow]
  obtain ⟨P₁, hP₀P₁⟩ := hP₀.exists_le_sylow
  have hP₁ : (P₁ : Subgroup Y) = P₀ :=
    (Subgroup.eq_of_le_of_card_ge hP₀P₁ (by rw [hP₀27]; exact h27 _ P₁.isPGroup')).symm
  obtain ⟨P, hσP⟩ := hσ3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P₁ P
  have hσP' : σ ∈ (P : Subgroup Y) := hσP (Subgroup.mem_zpowers σ)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hσP'
  obtain ⟨x, hx, rfl⟩ := hσP'
  rw [hP₁] at hx
  rw [MulAut.smul_def, MulAut.conj_apply, conj_pow, hP₀3 x hx]
  group

theorem pow_three_eq_one_of_ne_two {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (hq2 : p ^ e ≠ 2) (h91 : p ^ e % 9 ≠ 1)
    (h98 : p ^ e % 9 ≠ 8) (σ : MulAut X) (k : ℕ) (hσ : σ ^ 3 ^ k = 1) : σ ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : p.Prime := Fact.out
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso (by omega)
  have hq2' : 2 < p ^ e := by
    have : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    omega
  have hperf : Group.IsPerfect X := by
    rcases hiso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hP, -⟩ := Sec13.isPerfect_center_projSL p e he hq
      exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    · obtain ⟨hP, -⟩ := Sec13.isPerfect_center_projSU p e he hq hq2'
      exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have := Sec19.Item19ResProof.finite_mulAut X
  have h27 := Sec19.Item19ResProof.card_le_of_isPGroup h9
    (Sec19.Item19ResProof.not_nine_dvd_card_outer he hiso hq2 h91 h98)
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Group.IsPerfect (CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ e) K)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨P₀, hP₀3, a, ha, b, hb, hab⟩ := exists_threeSubgroup_model hK hq
  set F : MulAut (CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ e) K)) →*
    MulAut X := (MulAut.congr ψ.symm).toMonoidHom with hF
  have hQ3 : ∀ x ∈ P₀.map F, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hP₀3 y hy, map_one]
  have hQp : IsPGroup 3 (P₀.map F) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hQ3 x x.2, Subgroup.coe_one])⟩
  have hQnab : ∃ x ∈ P₀.map F, ∃ y ∈ P₀.map F, x * y ≠ y * x :=
    ⟨F a, Subgroup.mem_map_of_mem F ha, F b, Subgroup.mem_map_of_mem F hb, fun h => hab
      ((MulAut.congr ψ.symm).injective (by rw [map_mul, map_mul]; exact h))⟩
  have hQ27 : Nat.card (P₀.map F) = 27 :=
    Sec19.Item19ResProof.card_eq_of_not_comm hQp (h27 _ hQp) hQnab
  exact pow_three_eq_one_of_sylow_bound h27 hQp hQ27 hQ3 hσ

end CFSG.RankThree.PartTwo.Sec17.Proof17Res2

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1721AutThreeU32 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e = 2 →
      ∀ (σ : MulAut X) (k : ℕ), σ ^ 3 ^ k = 1 → σ ^ 3 = 1

theorem ks1721AutThreeL3_of_u32 (hU : KS1721AutThreeU32) : KS1721AutThreeL3 := by
  intro X _ _ hX h27 σ k hσ
  obtain ⟨p, e, _, he, hiso⟩ := hX
  by_cases hq2 : p ^ e = 2
  · exact hU X p e he hiso hq2 σ k hσ
  · obtain ⟨h91, h98⟩ := Proof17Res2.not_modNine_of_not_dvd he hiso h27
    exact Proof17Res2.pow_three_eq_one_of_ne_two he hiso hq2 h91 h98 σ k hσ

end CFSG.RankThree.PartTwo.Sec17
