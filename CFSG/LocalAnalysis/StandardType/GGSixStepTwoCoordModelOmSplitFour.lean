module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompZero
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

namespace CFSG.StandardType

namespace CoordOm

open scoped MatrixGroups

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H N : Subgroup G}
    (hc : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h) {g : G} (hg : g ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, g = h * n := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ n ∈ N, g = h * n}
      mul_mem' := by
        rintro _ _ ⟨h, hh, n, hn, rfl⟩ ⟨h', hh', n', hn', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', n * n', N.mul_mem hn hn', ?_⟩
        calc h * n * (h' * n') = h * (n * h') * n' := by group
          _ = h * (h' * n) * n' := by rw [hc h' hh' n hn]
          _ = h * h' * (n * n') := by group
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, n⁻¹, N.inv_mem hn, ?_⟩
        rw [mul_inv_rev]
        exact (hc h⁻¹ (H.inv_mem hh) n⁻¹ (N.inv_mem hn)).symm }
  have hle : H ⊔ N ≤ S := sup_le (fun h hh => ⟨h, hh, 1, N.one_mem, by simp⟩)
    (fun n hn => ⟨1, H.one_mem, n, hn, by simp⟩)
  exact hle hg

theorem exists_pow_mul_pow_eq_one_of_isCyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} [Finite P] [IsCyclic P] {a b : G} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a * b = b * a) (hap : a ^ p = 1) (hbp : b ^ p = 1) :
    ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧ a ^ α * b ^ γ = 1 := by
  classical
  have := Fintype.ofFinite P
  have hcomm : Commute a b := hab
  have hpow : ∀ i j : ℕ, (a ^ i * b ^ j) ^ p = 1 := fun i j => by
    rw [(hcomm.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul,
      pow_mul, hap, hbp, one_pow, one_pow, one_mul]
  set f : Fin p × Fin p → {x : P // x ^ p = 1} := fun ij =>
    ⟨⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), P.mul_mem (P.pow_mem ha _) (P.pow_mem hb _)⟩,
      Subtype.ext (by simpa using hpow ij.1 ij.2)⟩ with hf
  have hcard : Fintype.card {x : P // x ^ p = 1} < Fintype.card (Fin p × Fin p) := by
    rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fin]
    have h1 := IsCyclic.card_pow_eq_one_le (α := P) hp.pos
    have h2 : p < p * p := by
      have := hp.two_le
      nlinarith
    exact lt_of_le_of_lt h1 h2
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have heq' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (i' : ℕ) * b ^ (j' : ℕ) :=
    congrArg (fun z : {x : P // x ^ p = 1} => ((z : P) : G)) heq
  refine ⟨((i : ℕ) + (p - i')) % p, ((j : ℕ) + (p - j')) % p, Nat.mod_lt _ hp.pos,
    Nat.mod_lt _ hp.pos, ?_, ?_⟩
  · by_contra h0
    push Not at h0
    obtain ⟨h1, h2⟩ := h0
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    have key : ∀ m m' : ℕ, m < p → m' < p → (m + (p - m')) % p = 0 → m = m' := by
      intro m m' hm hm' h
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c <;> omega
      · have : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc2
        omega
    exact hne (Prod.ext (Fin.ext (key _ _ hi hi' h1)) (Fin.ext (key _ _ hj hj' h2)))
  · rw [← pow_eq_pow_mod _ hap, ← pow_eq_pow_mod _ hbp, pow_add, pow_add]
    calc a ^ (i : ℕ) * a ^ (p - i') * (b ^ (j : ℕ) * b ^ (p - j')) =
        (a ^ (i : ℕ) * b ^ (j : ℕ)) * (a ^ (p - i') * b ^ (p - j')) := by
          rw [mul_assoc, mul_assoc, ← mul_assoc (a ^ (p - i')), (hcomm.pow_pow _ _).eq]
          group
      _ = (a ^ (i' : ℕ) * b ^ (j' : ℕ)) * (a ^ (p - i') * b ^ (p - j')) := by rw [heq']
      _ = a ^ ((i' : ℕ) + (p - i')) * b ^ ((j' : ℕ) + (p - j')) := by
          rw [pow_add, pow_add, mul_assoc, mul_assoc, ← mul_assoc (b ^ (j' : ℕ)),
            ← (hcomm.pow_pow _ _).eq]
          group
      _ = 1 := by
          rw [Nat.add_sub_cancel' (le_of_lt i'.isLt), Nat.add_sub_cancel' (le_of_lt j'.isLt), hap,
            hbp, one_mul]

theorem sl2_exists_pow_mul_pow_eq_one {K : Type*} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {a b : SL(2, K)} (hab : a * b = b * a) (hap : a ^ p = 1)
    (hbp : b ^ p = 1) :
    ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧ a ^ α * b ^ γ = 1 := by
  classical
  have hcomm : Commute a b := hab
  set P := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hP
  have hzc : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    exact (hcomm.zpow_zpow m n).eq
  have hPp : IsPGroup p P := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨_, ⟨m, rfl⟩, _, ⟨n, rfl⟩, hx⟩ := exists_mul_of_mem_sup_of_commute hzc x.2
    rw [pow_one, Subgroup.coe_pow, hx, ((hcomm.zpow_zpow m n)).mul_pow, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm, zpow_mul, mul_comm n, zpow_mul,
      zpow_natCast, zpow_natCast, hap, hbp, one_zpow, one_zpow, one_mul, Subgroup.coe_one]
  have : Finite P := inferInstance
  have : IsCyclic P := CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 P hPp
  exact exists_pow_mul_pow_eq_one_of_isCyclic hp.out
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hab hap hbp

theorem exists_pow_mul_pow_mem_of_sup {G : Type*} [Group G] {K : Type*} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {T₁ T₂ : Subgroup G}
    (hc : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) (hdisj : ∀ z ∈ T₁, z ∈ T₂ → z = 1)
    {ψ : SL(2, K) →* G} (hψ : Function.Injective ψ) (hψr : ψ.range = T₁) {c₁ c₂ : G}
    (h₁ : c₁ ∈ T₁ ⊔ T₂) (h₂ : c₂ ∈ T₁ ⊔ T₂) (h12 : c₁ * c₂ = c₂ * c₁) (hc₁ : c₁ ^ p = 1)
    (hc₂ : c₂ ^ p = 1) :
    ∃ α γ : ℕ, α < p ∧ γ < p ∧ (α ≠ 0 ∨ γ ≠ 0) ∧ c₁ ^ α * c₂ ^ γ ∈ T₂ := by
  obtain ⟨a₁, ha₁, n₁, hn₁, rfl⟩ := exists_mul_of_mem_sup_of_commute hc h₁
  obtain ⟨a₂, ha₂, n₂, hn₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc h₂
  have ha12 : a₁ * a₂ = a₂ * a₁ := by
    have e : (a₂ * a₁)⁻¹ * (a₁ * a₂) = (n₂ * n₁) * (n₁ * n₂)⁻¹ := by
      have h1 : a₁ * n₁ * (a₂ * n₂) = a₁ * a₂ * (n₁ * n₂) := by
        rw [mul_assoc, ← mul_assoc n₁, ← hc a₂ ha₂ n₁ hn₁]
        group
      have h2 : a₂ * n₂ * (a₁ * n₁) = a₂ * a₁ * (n₂ * n₁) := by
        rw [mul_assoc, ← mul_assoc n₂, ← hc a₁ ha₁ n₂ hn₂]
        group
      rw [h1, h2] at h12
      calc (a₂ * a₁)⁻¹ * (a₁ * a₂) = (a₂ * a₁)⁻¹ * (a₁ * a₂ * (n₁ * n₂)) * (n₁ * n₂)⁻¹ := by
            group
        _ = (a₂ * a₁)⁻¹ * (a₂ * a₁ * (n₂ * n₁)) * (n₁ * n₂)⁻¹ := by rw [h12]
        _ = (n₂ * n₁) * (n₁ * n₂)⁻¹ := by group
    have h3 := hdisj _ (T₁.mul_mem (T₁.inv_mem (T₁.mul_mem ha₂ ha₁)) (T₁.mul_mem ha₁ ha₂))
      (e ▸ T₂.mul_mem (T₂.mul_mem hn₂ hn₁) (T₂.inv_mem (T₂.mul_mem hn₁ hn₂)))
    exact (inv_inj.mp (mul_eq_one_iff_eq_inv.mp h3)).symm
  have hpow : ∀ {a n : G}, a ∈ T₁ → n ∈ T₂ → ∀ m : ℕ, (a * n) ^ m = a ^ m * n ^ m :=
    fun ha hn m => (Commute.mul_pow (hc _ ha _ hn) m)
  have hap : ∀ {a n : G}, a ∈ T₁ → n ∈ T₂ → (a * n) ^ p = 1 → a ^ p = 1 := by
    intro a n ha hn h
    rw [hpow ha hn] at h
    have h1 : a ^ p = (n ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h
    exact hdisj _ (T₁.pow_mem ha p) (h1 ▸ T₂.inv_mem (T₂.pow_mem hn p))
  have ha₁p := hap ha₁ hn₁ hc₁
  have ha₂p := hap ha₂ hn₂ hc₂
  obtain ⟨b₁, rfl⟩ : a₁ ∈ ψ.range := hψr ▸ ha₁
  obtain ⟨b₂, rfl⟩ : a₂ ∈ ψ.range := hψr ▸ ha₂
  have hb12 : b₁ * b₂ = b₂ * b₁ := hψ (by rw [map_mul, map_mul, ha12])
  have hb₁p : b₁ ^ p = 1 := hψ (by rw [map_pow, ha₁p, map_one])
  have hb₂p : b₂ ^ p = 1 := hψ (by rw [map_pow, ha₂p, map_one])
  obtain ⟨α, γ, hα, hγ, hαγ, h1⟩ := sl2_exists_pow_mul_pow_eq_one hp2 hb12 hb₁p hb₂p
  refine ⟨α, γ, hα, hγ, hαγ, ?_⟩
  have h2 : ψ b₁ ^ α * ψ b₂ ^ γ = 1 := by rw [← map_pow, ← map_pow, ← map_mul, h1, map_one]
  rw [hpow ha₁ hn₁, hpow ha₂ hn₂]
  have e : ψ b₁ ^ α * n₁ ^ α * (ψ b₂ ^ γ * n₂ ^ γ) =
      (ψ b₁ ^ α * ψ b₂ ^ γ) * (n₁ ^ α * n₂ ^ γ) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (n₁ ^ α),
      ← hc _ (T₁.pow_mem ha₂ γ) _ (T₂.pow_mem hn₁ α)]
    group
  rw [e, h2, one_mul]
  exact T₂.mul_mem (T₂.pow_mem hn₁ α) (T₂.pow_mem hn₂ γ)

end CoordOm

open scoped MatrixGroups

open CoordOm OmNonsplit CFSG.LocalAnalysis.ComponentInitial in
theorem ggOmSplitFourCentInput_holds : GGOmSplitFourCentInput := by
  intro K _ _ _ W _ _ _ R hR hsp p hp hp2 T hTq hTs c₁ c₂ hc₁ hc₂ hc₁p hc₂p h12
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.RankThree.PartOne.KFU.FlagSplit.finite_linearEquiv (K := K) (X := W)
  set OR := TauCeti.QuadraticMap.orthogonalGroup R with hOR
  obtain ⟨-, ⟨hns, -⟩ | ⟨-, hK4, -⟩⟩ := structure_of_isSubnormal hR hTq hTs
  · exact absurd hsp hns
  obtain ⟨T₁, T₂, hsup, -, -, hcomm, hc₁', hc₂', ⟨ψ₁, hψ₁, hr₁⟩, ⟨ψ₂, hψ₂, hr₂⟩, hodd⟩ :=
    SevOm.splitFour_factors hR hsp (by omega) (by omega)
  have hoddp : ∀ c : W ≃ₗ[K] W, c ∈ OR → c ^ p = 1 → c ∈ T₁ ⊔ T₂ := fun c hc hcp => by
    rw [← hsup]
    exact hodd c hc (Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hcp))
  have hcenter : ∀ {ψ : SL(2, K) →* (W ≃ₗ[K] W)}, Function.Injective ψ →
      ∀ w : SL(2, K), (∀ v : SL(2, K), ψ w * ψ v = ψ v * ψ w) → w = 1 := by
    intro ψ hψ w hw
    have hwc : w ∈ Subgroup.center (SL(2, K)) := Subgroup.mem_center_iff.mpr fun v =>
      hψ (by rw [map_mul, map_mul, hw v])
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hwc
    refine CFSG.LinearAlgebra.SteinbergBQ.eq_one_of_scalar_charTwo ?_ ?_ ?_ <;>
      · rw [← hr]
        simp
  have hdisj₁ : ∀ z ∈ T₁, z ∈ T₂ → z = 1 := by
    intro z hz₁ hz₂
    obtain ⟨w, rfl⟩ : z ∈ ψ₁.range := hr₁ ▸ hz₁
    rw [hcenter hψ₁ w fun v => (hcomm _ (hr₁ ▸ ⟨v, rfl⟩) _ hz₂).symm, map_one]
  have hdisj₂ : ∀ z ∈ T₂, z ∈ T₁ → z = 1 := fun z h2 h1 => hdisj₁ z h1 h2
  have hcomm' : ∀ x ∈ T₂, ∀ y ∈ T₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hm₁ := hoddp c₁ hc₁ hc₁p
  have hm₂ := hoddp c₂ hc₂ hc₂p
  have hTA : CFSG.Assembly.IsComponentOf T OR :=
    ⟨LayerCores.ggSubnormal_le hTs, hTs,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hTq⟩
  rcases isComponentOf_eq_or_commute hTA hc₁' with e1 | e1
  · obtain ⟨α, γ, hα, hγ, hαγ, hmem⟩ :=
      exists_pow_mul_pow_mem_of_sup hp2 hcomm hdisj₁ hψ₁ hr₁ hm₁ hm₂ h12 hc₁p hc₂p
    refine ⟨α, γ, hα, hγ, hαγ, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    rw [e1] at ht
    exact hcomm t ht _ hmem
  rcases isComponentOf_eq_or_commute hTA hc₂' with e2 | e2
  · obtain ⟨α, γ, hα, hγ, hαγ, hmem⟩ :=
      exists_pow_mul_pow_mem_of_sup hp2 hcomm' hdisj₂ hψ₂ hr₂ (sup_comm T₁ T₂ ▸ hm₁)
        (sup_comm T₁ T₂ ▸ hm₂) h12 hc₁p hc₂p
    refine ⟨α, γ, hα, hγ, hαγ, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    rw [e2] at ht
    exact hcomm' t ht _ hmem
  exfalso
  have hTc : T ≤ ⁅OR, OR⁆ := by
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hTq]
    exact Subgroup.commutator_mono (LayerCores.ggSubnormal_le hTs) (LayerCores.ggSubnormal_le hTs)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at e1 e2
  have h5 : ⁅OR, OR⁆ ≤ Subgroup.centralizer (T : Set (W ≃ₗ[K] W)) := by
    rw [hsup]
    exact sup_le e1 e2
  exact not_le_centralizer_self_of_isQuasisimple hTA.2.2 (hTc.trans h5)

end CFSG.StandardType
