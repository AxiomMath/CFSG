module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section General

variable {G : Type} [Group G]

theorem ggLe_pCoreOf_two {N Y : Subgroup G} (hYN : Y ≤ N)
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hY : IsPGroup 2 Y) : Y ≤ pCoreOf 2 N := by
  have hn : (Y.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYN).mpr hNY
  have hsub : IsPGroup 2 (Y.subgroupOf N) := hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYN).symm
  have := Dichotomy.CentralizerContainment.le_pCore_assembly hn hsub
  rw [← Subgroup.map_subgroupOf_eq_of_le hYN]
  exact Subgroup.map_mono this

theorem ggPCoreOf_two_isPGroup (N : Subgroup G) : IsPGroup 2 (pCoreOf 2 N) :=
  (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 N).map N.subtype

variable [Finite G]

theorem le_pCoreOf_of_stability {N R Q : Subgroup G} (hNR : N ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) (hC : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N)
    (hQN : Q ≤ N) (hQP : ∀ q ∈ Q, ∀ a ∈ pCoreOf 2 N, q * a * q⁻¹ * a⁻¹ ∈ R)
    (hQR : Q ≤ Subgroup.centralizer (R : Set G)) : Q ≤ pCoreOf 2 N := by
  set P := pCoreOf 2 N with hPdef
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := fun n hn => mem_normalizer_pCoreOf hn
  have hconjR : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R := fun n hn r hr =>
    (Subgroup.mem_normalizer_iff.mp (hNR hn) r).mp hr
  have hconjP : ∀ n ∈ N, ∀ a ∈ P, n * a * n⁻¹ ∈ P := fun n hn a ha =>
    (Subgroup.mem_normalizer_iff.mp (hNP hn) a).mp ha
  let Y : Subgroup G :=
    { carrier := {g | g ∈ N ∧ (∀ a ∈ P, g * a * g⁻¹ * a⁻¹ ∈ R) ∧ ∀ r ∈ R, g * r = r * g}
      mul_mem' := by
        rintro g h ⟨hgN, hgP, hgR⟩ ⟨hhN, hhP, hhR⟩
        refine ⟨N.mul_mem hgN hhN, fun a ha => ?_, fun r hr => ?_⟩
        · have h1 := hconjR g hgN _ (hhP a ha)
          have h2 := hgP a ha
          have := R.mul_mem h1 h2
          convert this using 1
          group
        · rw [mul_assoc, hhR r hr, ← mul_assoc, hgR r hr, mul_assoc]
      one_mem' := ⟨N.one_mem, fun a _ => by simp [R.one_mem], fun r _ => by simp⟩
      inv_mem' := by
        rintro g ⟨hgN, hgP, hgR⟩
        refine ⟨N.inv_mem hgN, fun a ha => ?_, fun r hr => ?_⟩
        · have hb : g⁻¹ * a * g⁻¹⁻¹ ∈ P := hconjP _ (N.inv_mem hgN) a ha
          have := R.inv_mem (hgP _ hb)
          convert this using 1
          group
        · calc g⁻¹ * r = g⁻¹ * (r * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * r) * g⁻¹ := by rw [hgR r hr]
            _ = r * g⁻¹ := by group }
  have hQY : Q ≤ Y := fun q hq => ⟨hQN hq, hQP q hq, fun r hr =>
    (Subgroup.mem_centralizer_iff.mp (hQR hq) r hr).symm⟩
  have hYN : Y ≤ N := fun g hg => hg.1
  have hNY : N ≤ Subgroup.normalizer (Y : Set G) := by
    have key : ∀ n ∈ N, ∀ g ∈ Y, n * g * n⁻¹ ∈ Y := by
      rintro n hn g ⟨hgN, hgP, hgR⟩
      refine ⟨N.mul_mem (N.mul_mem hn hgN) (N.inv_mem hn), fun a ha => ?_, fun r hr => ?_⟩
      · have hb : n⁻¹ * a * n⁻¹⁻¹ ∈ P := hconjP _ (N.inv_mem hn) a ha
        have := hconjR n hn _ (hgP _ hb)
        convert this using 1
        group
      · have hs : n⁻¹ * r * n⁻¹⁻¹ ∈ R := hconjR _ (N.inv_mem hn) r hr
        have h1 := hgR _ hs
        calc n * g * n⁻¹ * r = n * (g * (n⁻¹ * r * n⁻¹⁻¹)) * n⁻¹ := by group
          _ = n * ((n⁻¹ * r * n⁻¹⁻¹) * g) * n⁻¹ := by rw [h1]
          _ = r * (n * g * n⁻¹) := by group
    intro n hn
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨key n hn g, fun hg => ?_⟩
    have := key n⁻¹ (N.inv_mem hn) _ hg
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hRpow : ∀ c ∈ R, c ^ 2 ^ m = 1 := fun c hc => by
    have := pow_card_eq_one' (x := (⟨c, hc⟩ : ↥R))
    rw [hm] at this
    exact congrArg Subtype.val this
  have hPp : IsPGroup 2 P := ggPCoreOf_two_isPGroup N
  have hY2 : IsPGroup 2 Y := by
    rintro ⟨g, hgN, hgP, hgR⟩
    have hpow : ∀ k : ℕ, ∀ a ∈ P, g ^ k * a * (g ^ k)⁻¹ = (g * a * g⁻¹ * a⁻¹) ^ k * a := by
      intro k
      induction k with
      | zero => intro a _; simp
      | succ k ih =>
        intro a ha
        have hc : Commute g (g * a * g⁻¹ * a⁻¹) := hgR _ (hgP a ha)
        have hck : g * (g * a * g⁻¹ * a⁻¹) ^ k = (g * a * g⁻¹ * a⁻¹) ^ k * g :=
          (hc.pow_right k).eq
        calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
              rw [pow_succ']; group
          _ = g * ((g * a * g⁻¹ * a⁻¹) ^ k * a) * g⁻¹ := by rw [ih a ha]
          _ = (g * (g * a * g⁻¹ * a⁻¹) ^ k) * a * g⁻¹ := by group
          _ = (g * a * g⁻¹ * a⁻¹) ^ k * g * a * g⁻¹ := by rw [hck]
          _ = (g * a * g⁻¹ * a⁻¹) ^ (k + 1) * a := by rw [pow_succ]; group
    have hcent : g ^ 2 ^ m ∈ N ⊓ Subgroup.centralizer (P : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨N.pow_mem hgN _, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := hpow (2 ^ m) a ha
      rw [hRpow _ (hgP a ha), one_mul] at h1
      calc a * g ^ 2 ^ m = (g ^ 2 ^ m * a * (g ^ 2 ^ m)⁻¹) * g ^ 2 ^ m := by rw [h1]
        _ = g ^ 2 ^ m * a := by group
    obtain ⟨j, hj⟩ := hPp ⟨_, hC hcent⟩
    refine ⟨m + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul, this]
  exact hQY.trans (ggLe_pCoreOf_two hYN hNY hY2)

theorem ggLe_of_le_sup_of_odd {S Q C : Subgroup G} (hS : IsPGroup 2 S) (hQ : IsPGroup 2 Q)
    (hSQ : S ≤ Subgroup.normalizer (Q : Set G)) (hQC : Q ≤ Subgroup.normalizer (C : Set G))
    (hC : Odd (Nat.card C)) (hle : S ≤ Q ⊔ C) : S ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : IsPGroup 2 (Q ⊔ S : Subgroup G) := IsPGroup.to_sup_of_normal_left' hQ hS hSQ
  obtain ⟨k, hk⟩ := hQS.exists_card_eq
  have hdisj : Disjoint (Q ⊔ S) C := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hC)
  intro s hs
  have hsQC : s ∈ ((Q ⊔ C : Subgroup G) : Set G) := hle hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q C hQC] at hsQC
  obtain ⟨q, hq, c, hc, hqc⟩ := hsQC
  have hs' : s = q * c := hqc.symm
  have hcQS : c ∈ Q ⊔ S := by
    have h1 : q⁻¹ * s ∈ Q ⊔ S :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Q.inv_mem hq)) (Subgroup.mem_sup_right hs)
    rw [hs'] at h1
    simpa using h1
  have hc1 : c = 1 := (Subgroup.disjoint_def.mp hdisj) hcQS hc
  rw [hs', hc1, mul_one]
  exact hq

theorem ggLe_of_inf_normalizer_le {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hS : P ⊓ Subgroup.normalizer (Q : Set G) ≤ Q) : P ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup G := Q ⊔ P with hT
  have hTp : IsPGroup 2 T := IsPGroup.to_sup_of_normal_right' hQ hP hQP
  have hnil : Group.IsNilpotent ↥T := hTp.isNilpotent
  have hcond := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  set Q' : Subgroup ↥T := Q.subgroupOf T with hQ'
  have hself : Subgroup.normalizer (Q' : Set ↥T) = Q' := by
    refine le_antisymm (fun t ht => ?_) Subgroup.le_normalizer
    have htQ : (t : G) ∈ Subgroup.normalizer (Q : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
      · have hgT : g ∈ T := Subgroup.mem_sup_left hg
        have := (Subgroup.mem_normalizer_iff.mp ht ⟨g, hgT⟩).mp
          (Subgroup.mem_subgroupOf.mpr hg)
        exact Subgroup.mem_subgroupOf.mp this
      · have hgT : g ∈ T := by
          have h1 : (t : G)⁻¹ * ((t : G) * g * (t : G)⁻¹) * (t : G) ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem t.2) (Subgroup.mem_sup_left hg)) t.2
          simpa [mul_assoc] using h1
        have := (Subgroup.mem_normalizer_iff.mp ht ⟨g, hgT⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hg)
        exact Subgroup.mem_subgroupOf.mp this
    have htT : (t : G) ∈ ((Q ⊔ P : Subgroup G) : Set G) := t.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Q P hQP] at htT
    obtain ⟨q, hq, a, ha, hqa⟩ := htT
    have haN : a ∈ Subgroup.normalizer (Q : Set G) := by
      have : a = q⁻¹ * t := by rw [← hqa]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hq)) htQ
    have haQ := hS ⟨ha, haN⟩
    exact Subgroup.mem_subgroupOf.mpr (hqa ▸ Q.mul_mem hq haQ)
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp hcond) Q' hself
  intro a ha
  have : (⟨a, Subgroup.mem_sup_right ha⟩ : ↥T) ∈ Q' := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end General

section PQS

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev ggPR (R : Subgroup G) : Subgroup G :=
  pCoreOf 2 (Subgroup.normalizer (R : Set G))

noncomputable abbrev ggQR (p : ℕ) (B : Subgroup G) (x : G) (L D J R : Subgroup G) :
    Subgroup G :=
  pCoreOf 2 (ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G))

noncomputable abbrev ggSR (p : ℕ) (B : Subgroup G) (x : G) (L D J R : Subgroup G) :
    Subgroup G :=
  ggPR R ⊓ Subgroup.normalizer (ggQR p B x L D J R : Set G)

end PQS

end CFSG.StandardType
