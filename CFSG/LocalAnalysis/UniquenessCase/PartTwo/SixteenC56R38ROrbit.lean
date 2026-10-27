module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

private lemma nine_not_dvd_two_pow_sub_one_of_le_four {a : ℕ} (ha1 : 1 ≤ a) (ha4 : a ≤ 4) :
    ¬ 9 ∣ 2 ^ a - 1 := by
  interval_cases a <;> decide

private lemma stabilizer_conj_eq_subgroupOf_inf_centralizer {G : Type*} [Group G]
    {P D : Subgroup G} [Subgroup.Normalizes P D] (d : ↥D) :
    MulAction.stabilizer ↥P d =
      (P ⊓ Subgroup.centralizer ({(d : G)} : Set G)).subgroupOf P := by
  ext a
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro ha
    refine ⟨a.2, ?_⟩
    have h := congrArg (Subtype.val : ↥D → G) ha
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · rintro ⟨-, ha⟩
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact mul_inv_eq_iff_eq_mul.mpr ha

private lemma card_stabilizer_conj_le_three {G : Type*} [Group G] [Finite G]
    {P D : Subgroup G} [Subgroup.Normalizes P D]
    (hP : IsElemAbelian 3 P)
    (hcon : ∀ v : G, v ∈ D → v ≠ 1 →
      CFSG.Open.pRank 3 (P ⊓ centralizer ({v} : Set G)) < 2)
    (d : ↥D) (hd : d ≠ 1) :
    Nat.card (MulAction.stabilizer ↥P d) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [stabilizer_conj_eq_subgroupOf_inf_centralizer d]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : P ⊓ Subgroup.centralizer ({(d : G)} : Set G) ≤ P)).toEquiv]
  have hle : CFSG.Open.pRank 3 (P ⊓ Subgroup.centralizer ({(d : G)} : Set G)) ≤ 1 := by
    have := hcon (d : G) d.2 (fun h => hd (Subtype.ext h))
    omega
  have hea : IsElemAbelian 3 (P ⊓ Subgroup.centralizer ({(d : G)} : Set G)) :=
    hP.mono inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hea.isPGroup
  have hk1 : k ≤ 1 := by
    have hkp := CFSG.SectionRank.le_pRank (p := 3) (G := G)
      (H := P ⊓ Subgroup.centralizer ({(d : G)} : Set G))
      (E := P ⊓ Subgroup.centralizer ({(d : G)} : Set G))
      (by norm_num : 1 < 3) le_rfl hea hk
    omega
  calc Nat.card ↥(P ⊓ Subgroup.centralizer ({(d : G)} : Set G)) = 3 ^ k := hk
    _ ≤ 3 ^ 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).2 hk1
    _ = 3 := by norm_num

theorem exists_ne_one_two_le_pRank_of_card_le_sixteen {G : Type*} [Group G] [Finite G]
    {P D : Subgroup G} (hP : IsElemAbelian 3 P) (hPcard : Nat.card P = 3 ^ 3)
    (hDn : P ≤ normalizer (D : Set G)) (hD : IsElemAbelian 2 D) (hD1 : D ≠ ⊥)
    (hDcard : Nat.card D ≤ 16) :
    ∃ v ∈ D, v ≠ 1 ∧ 2 ≤ CFSG.Open.pRank 3 (P ⊓ centralizer ({v} : Set G)) := by
  classical
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := D)).1 hD.isPGroup
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    exact hD1 ((Subgroup.eq_bot_iff_card (H := D)).2 (by rw [ha, ha0, pow_zero]))
  have ha4 : a ≤ 4 := by
    have h2 : 2 ^ a ≤ 2 ^ 4 := by
      calc 2 ^ a = Nat.card D := ha.symm
        _ ≤ 16 := hDcard
        _ = 2 ^ 4 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  by_contra hcon
  rw [not_exists] at hcon
  have hcon' : ∀ v : G, v ∈ D → v ≠ 1 →
      CFSG.Open.pRank 3 (P ⊓ centralizer ({v} : Set G)) < 2 := by
    intro v hvD hvne
    exact not_le.mp fun h2 => hcon v ⟨hvD, hvne, h2⟩
  haveI : Subgroup.Normalizes P D := ⟨hDn⟩
  let Ω : SubMulAction ↥P ↥D :=
    { carrier := {d | d ≠ 1}
      smul_mem' := by
        intro c d hd
        intro h
        exact hd (by
          have h1 : c • d = c • (1 : ↥D) := by rw [h, MulDistribMulAction.smul_one]
          exact smul_left_cancel c h1) }
  haveI : Fintype ↥P := Fintype.ofFinite _
  haveI : Fintype ↥D := Fintype.ofFinite _
  haveI : Fintype Ω := Fintype.ofFinite _
  haveI : Fintype (Quotient (MulAction.orbitRel ↥P Ω)) := Fintype.ofFinite _
  haveI : ∀ b : Ω, Fintype (MulAction.stabilizer ↥P b) := fun b => Fintype.ofFinite _
  have hΩ : Fintype.card Ω = Nat.card D - 1 := by
    have e : Ω ≃ {d : ↥D // d ≠ 1} :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun y => ⟨y.1, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    calc Fintype.card Ω = Fintype.card {d : ↥D // d ≠ 1} := Fintype.card_congr e
      _ = Fintype.card ↥D - Fintype.card {d : ↥D // d = 1} := by
            simpa using (Fintype.card_subtype_compl (fun d : ↥D => d = 1))
      _ = Fintype.card ↥D - 1 := by rw [Fintype.card_subtype_eq]
      _ = Nat.card D - 1 := by rw [Nat.card_eq_fintype_card]
  have h9Ω : 9 ∣ Fintype.card Ω := by
    rw [MulAction.card_eq_sum_card_group_div_card_stabilizer (α := ↥P) (β := Ω)]
    apply Finset.dvd_sum
    intro ω _
    have hP27 : Fintype.card ↥P = 27 := by
      rw [← Nat.card_eq_fintype_card, hPcard]
      norm_num
    have hle3_D : Nat.card (MulAction.stabilizer ↥P (ω.out : ↥D)) ≤ 3 :=
      card_stabilizer_conj_le_three hP hcon' (ω.out : ↥D) (ω.out).2
    have hle3 : Nat.card (MulAction.stabilizer ↥P ω.out) ≤ 3 := by
      rw [Nat.card_congr (Equiv.cast (congrArg (fun S : Subgroup ↥P => ↥S)
        (SubMulAction.stabilizer_of_subMul ω.out)))]
      exact hle3_D
    have hdiv : Nat.card (MulAction.stabilizer ↥P ω.out) ∣ 3 ^ 3 := by
      have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer ↥P ω.out)
      rwa [hPcard] at this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdiv
    have hk1 : k ≤ 1 := by
      have hpow : 3 ^ k ≤ 3 ^ 1 := by
        rw [← hk]
        simpa using hle3
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hpow
    have hFstab : Fintype.card (MulAction.stabilizer ↥P ω.out) = 3 ^ k := by
      rw [← Nat.card_eq_fintype_card]
      exact hk
    rw [hP27, hFstab]
    interval_cases k <;> norm_num
  have h9D : 9 ∣ Nat.card D - 1 := by
    rw [← hΩ]
    exact h9Ω
  rw [ha] at h9D
  exact nine_not_dvd_two_pow_sub_one_of_le_four ha1 ha4 h9D

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
