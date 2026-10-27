module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3Borel
public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
public import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_U34InvolCentFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsU3 X 2 → ∀ t : X, t * t = 1 →
    ∃ x : X, orderOf x = 5 ∧ x * t = t * x

theorem k_U34InvolCentFive_holds :
    K_U34InvolCentFive := by
  classical
  intro X _ _ hX t ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  obtain ⟨eU⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel le_rfl hSC
  have hB0 : CFSG.Open.fusionBenderBorel (CFSG.Open.PSU3 2 2) (2 ^ 2) 3 :=
    CFSG.Open.bender_psu3_borel_full 2 (by norm_num)
  have hB : CFSG.Open.fusionBenderBorel X (2 ^ 2) 3 := hB0.map_mulEquiv eU.symm
  have hto : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hto with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; rfl)
  obtain ⟨Q, hQ⟩ := ht2.exists_le_sylow
  have htQ : t ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers t)
  obtain ⟨hSE, -, -, hZcard, -⟩ := hB Q
  have htc : ∀ q ∈ (Q : Subgroup X), q * t = t * q := by
    intro q hq
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, one_mul]
    · have hto2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
      exact (CFSG.Timmesfeld.Connectivity.commute_of_mem_sylow Q hSE htQ hto2 hq).eq
  have hS : CFSG.Quasithin.IsSylowIn 2 (Q : Subgroup X) ⊤ := CFSG.Quasithin.isSylowIn_top Q
  have h5 : 5 ∣ ((Q : Subgroup X).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup X) : Set X))).index :=
    uc2_17_36b_dvd_index (CFSG.LocalAnalysis.UniquenessCase.UC22.U3Loss.isSU3_of_isU3 hX).1 hS
      Nat.prime_five (by norm_num) (by norm_num)
  have h5N : 5 ∣ Nat.card (Subgroup.normalizer ((Q : Subgroup X) : Set X)) :=
    h5.trans (Subgroup.index_dvd_card _)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5N
  have hyN : (y : X) ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X) := y.2
  have hyo : orderOf (y : X) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hy5 : (y : X) ^ 5 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one _
  let Z : Subgroup X := (Subgroup.center (Q : Subgroup X)).map (Q : Subgroup X).subtype
  have hZ4 : Nat.card Z = 4 := by
    rw [Subgroup.card_map_of_injective (Q : Subgroup X).subtype_injective, hZcard]
    norm_num
  have hmemZ : ∀ z : X, z ∈ Z ↔ z ∈ (Q : Subgroup X) ∧ ∀ q ∈ (Q : Subgroup X), q * z = z * q := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, fun q hq => congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨q, hq⟩)⟩
    · rintro ⟨hzQ, hz⟩
      exact ⟨⟨z, hzQ⟩, Subgroup.mem_center_iff.mpr (fun q => Subtype.ext (hz q q.2)), rfl⟩
  have hconj : ∀ g ∈ Subgroup.normalizer ((Q : Subgroup X) : Set X), ∀ z ∈ Z,
      g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    obtain ⟨hzQ, hzc⟩ := (hmemZ z).mp hz
    refine (hmemZ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ, fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ (Q : Subgroup X) := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
      simpa using h1
    have h1 := hzc _ hq'
    calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * q := by group
  let σ : Equiv.Perm Z :=
    { toFun := fun z => ⟨(y : X) * z * (y : X)⁻¹, hconj _ hyN z z.2⟩
      invFun := fun z => ⟨(y : X)⁻¹ * z * (y : X), by
        have h1 := hconj _ (Subgroup.inv_mem _ hyN) z z.2
        simpa using h1⟩
      left_inv := fun z => by ext; simp [mul_assoc]
      right_inv := fun z => by ext; simp [mul_assoc] }
  have hσpow : ∀ k : ℕ, ∀ z : Z,
      (((σ ^ k) z : Z) : X) = (y : X) ^ k * z * ((y : X) ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ', Equiv.Perm.mul_apply]
      show (y : X) * (((σ ^ k) z : Z) : X) * (y : X)⁻¹ = _
      rw [ih z, pow_succ']
      group
  have hσ5 : σ ^ 5 = 1 := by
    refine Equiv.ext fun z => Subtype.ext ?_
    rw [hσpow 5 z, hy5, one_mul, inv_one, mul_one]
    rfl
  have hσ1 : σ = 1 := by
    have h24 : σ ^ 24 = 1 := by
      have h := pow_card_eq_one' (x := σ)
      rw [Nat.card_perm, hZ4] at h
      simpa [Nat.factorial] using h
    exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 5 24)).1 ⟨hσ5, h24⟩
  have htZ : t ∈ Z := (hmemZ t).mpr ⟨htQ, htc⟩
  have hyt : (y : X) * t * (y : X)⁻¹ = t := by
    have h1 := congrArg (fun τ : Equiv.Perm Z => ((τ ⟨t, htZ⟩ : Z) : X)) hσ1
    exact h1
  refine ⟨(y : X), hyo, ?_⟩
  calc (y : X) * t = (y : X) * t * (y : X)⁻¹ * (y : X) := by group
    _ = t * (y : X) := by rw [hyt]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
