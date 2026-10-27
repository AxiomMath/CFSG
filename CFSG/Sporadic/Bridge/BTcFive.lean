module

public import CFSG.Sporadic.Bridge.BTcGen
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanPRankCommuting

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native CFSG.AGLEmbedding

theorem tcGenDatum_of_data {G : Type} [Group G] [Finite G] (Q P : Subgroup G) (x h e z q u : G)
    (hP : IsPGroup 5 P) (hQP : Q ≤ P) (hz5 : z ^ 5 = 1) (hq5 : q ^ 5 = 1) (hu5 : u ^ 5 = 1)
    (hzo : orderOf z = 5) (hzq : Commute z q) (hzu : Commute z u) (hqu : Commute q u)
    (hzQ : z ∈ Q) (hqQ : q ∈ Q) (huQ : u ∈ Q)
    (hxN : x ∈ Subgroup.normalizer (Q : Set G)) (hhN : h ∈ Subgroup.normalizer (Q : Set G))
    (heq : Commute e q) (heu : Commute e u)
    (hind : ∀ a b c : ℕ, a < 5 → b < 5 → c < 5 → (b ≠ 0 ∨ c ≠ 0) → z ^ a * q ^ b * u ^ c ≠ 1)
    (hgen : Subgroup.closure ({x, h, e} : Set G) = ⊤) : TCGenDatum G 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : 1 < 5 := by norm_num
  have hker3 : ∀ a : Fin 3 → ZMod 5, a ≠ 0 →
      (List.ofFn fun i => (![z, q, u] : Fin 3 → G) i ^ (a i).val).prod ≠ 1 := by
    intro a ha h
    have h' : z ^ (a 0).val * q ^ (a 1).val * u ^ (a 2).val = 1 := by
      simpa [List.ofFn_succ, mul_assoc] using h
    by_cases hb : (a 1).val ≠ 0 ∨ (a 2).val ≠ 0
    · exact hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hb h'
    · rw [not_or, not_not, not_not] at hb
      obtain ⟨hb1, hb2⟩ := hb
      rw [hb1, hb2, pow_zero, pow_zero, mul_one, mul_one] at h'
      have hdvd : 5 ∣ (a 0).val := by
        have := orderOf_dvd_of_pow_eq_one h'
        rwa [hzo] at this
      have ha0 : a 0 = 0 :=
        (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
      apply ha
      funext i
      fin_cases i
      · exact ha0
      · exact (ZMod.val_eq_zero _).1 hb1
      · exact (ZMod.val_eq_zero _).1 hb2
  have hcomm3 : ∀ i j : Fin 3,
      Commute ((![z, q, u] : Fin 3 → G) i) ((![z, q, u] : Fin 3 → G) j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hzq
    · exact hzu
    · exact hzq.symm
    · exact Commute.refl _
    · exact hqu
    · exact hzu.symm
    · exact hqu.symm
    · exact Commute.refl _
  have hpow3 : ∀ i : Fin 3, (![z, q, u] : Fin 3 → G) i ^ 5 = 1 := by
    intro i
    fin_cases i
    · exact hz5
    · exact hq5
    · exact hu5
  have hrQ : 3 ≤ Open.pRank 5 Q :=
    le_pRank_of_commuting_pow ![z, q, u] hpow3 hcomm3 hker3 (H := Q) (by
      intro i
      fin_cases i
      · exact hzQ
      · exact hqQ
      · exact huQ)
  obtain ⟨U1, hU1⟩ : ∃ U : Subgroup G, U = Subgroup.closure ({q, u} : Set G) := ⟨_, rfl⟩
  have hqU : q ∈ U1 := by rw [hU1]; exact Subgroup.subset_closure (by simp)
  have huU : u ∈ U1 := by rw [hU1]; exact Subgroup.subset_closure (by simp)
  have hU1le : U1 ≤ Q := by
    rw [hU1, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hqQ
    · exact huQ
  have hker2 : ∀ a : Fin 2 → ZMod 5, a ≠ 0 →
      (List.ofFn fun i => (![q, u] : Fin 2 → G) i ^ (a i).val).prod ≠ 1 := by
    intro a ha h
    have h' : q ^ (a 0).val * u ^ (a 1).val = 1 := by
      simpa [List.ofFn_succ] using h
    have hne : (a 0).val ≠ 0 ∨ (a 1).val ≠ 0 := by
      by_contra hb
      rw [not_or, not_not, not_not] at hb
      apply ha
      funext i
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 hb.1
      · exact (ZMod.val_eq_zero _).1 hb.2
    exact hind 0 _ _ (by norm_num) (ZMod.val_lt _) (ZMod.val_lt _) hne (by simpa using h')
  have hr2U : 2 ≤ Open.pRank 5 U1 :=
    le_pRank_of_commuting_pow ![q, u] (fun i => by
      fin_cases i
      · exact hq5
      · exact hu5) (fun i j => by
      fin_cases i <;> fin_cases j
      · exact Commute.refl _
      · exact hqu
      · exact hqu.symm
      · exact Commute.refl _) hker2 (H := U1) (fun i => by
      fin_cases i
      · exact hqU
      · exact huU)
  have hU1z : ∀ g ∈ U1, g * z = z * g := by
    intro g hg
    have : U1 ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [hU1, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 hzu.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hg)
  have hzC : z ∈ Subgroup.centralizer (U1 : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun g hg => hU1z g hg
  have hr3U : 3 ≤ Open.pRank 5 (U1 ⊔ (P ⊓ Subgroup.centralizer (U1 : Set G))) :=
    le_pRank_of_commuting_pow ![z, q, u] hpow3 hcomm3 hker3
      (H := U1 ⊔ (P ⊓ Subgroup.centralizer (U1 : Set G))) (by
      intro i
      fin_cases i
      · exact Subgroup.mem_sup_right ⟨hQP hzQ, hzC⟩
      · exact Subgroup.mem_sup_left hqU
      · exact Subgroup.mem_sup_left huU)
  have heC : e ∈ Subgroup.centralizer (U1 : Set G) := by
    have : U1 ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [hU1, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 heq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 heu.symm
    exact Subgroup.mem_centralizer_iff.2 fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.1 (this hg)
  refine ⟨2, ![Q, U1], P, {x, h, e}, hP, ?_, ?_, hgen, ?_⟩
  · intro i
    fin_cases i
    · exact hQP
    · exact hU1le.trans hQP
  · intro i
    fin_cases i
    · exact ⟨le_trans (by norm_num) hrQ,
        le_trans hrQ (CFSG.SectionRank.pRank_mono hp5 le_sup_left)⟩
    · exact ⟨hr2U, hr3U⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨0, hxN⟩
    · exact ⟨1 - 1, hhN⟩
    · exact ⟨1, Subgroup.centralizer_le_normalizer (U1 : Set G) heC⟩

theorem tcGenDatum_B_of_facts
    (HR : List (List ℕ)) (hc : List ℕ)
    (hconjH : ∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (HR.getD i []).getD j 0).prod * zFive ^ hc.getD i 0)
    (hu5 : (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ 5 = 1)
    (huq : (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * qFive 0 =
      qFive 0 * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4))
    (hind' : ∀ a b c : ℕ, a < 5 → b < 5 → c < 5 → (b ≠ 0 ∨ c ≠ 0) →
      zFive ^ a * qFive 0 ^ b * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) ^ c ≠ 1)
    (e : NativeSporadic.B) (he0' : e * qFive 0 = qFive 0 * e)
    (heu' : e * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) =
      (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * e)
    {a b : NativeSporadic.B} (haT : a ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B))
    (hbT : b ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B))
    (G Gi : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) (h3' : G * Gi = 1)
    (h1' : genA₁ * G = G * bMat a) (h2' : genA₂ * G = G * bMat b) :
    TCGenDatum NativeSporadic.B 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, -, -, -, hq5, hz5, -⟩ := five_facts
  have hconjH_mem : ∀ i : Fin 4, hFive⁻¹ * qFive i * hFive ∈ QFive := by
    intro i
    rw [hconjH i]
    refine mul_mem (Subgroup.list_prod_mem _ fun g hg => ?_) (pow_mem zFive_mem _)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
    exact pow_mem (qFive_mem j) _
  have hhQ : ∀ g ∈ QFive, hFive⁻¹ * g * hFive ∈ QFive := fun g hg =>
    CommData.conj_mem hconjH_mem hg
  have hu_mem : qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4 ∈ QFive :=
    mul_mem (mul_mem (mul_mem (qFive_mem 1) (pow_mem (qFive_mem 2) 2)) (qFive_mem 3))
      (pow_mem zFive_mem 4)
  have hgen : Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B) = ⊤ := by
    refine closure_eq_top_of_conj haT hbT ⟨G, Gi, h3', mul_eq_one_comm.1 h3'⟩ (Units.ext ?_)
      (Units.ext ?_)
    · simpa [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_bGL] using h1'
    · simpa [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, coe_bGL] using h2'
  have hzu : zFive * (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) =
      (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4) * zFive :=
    (commData_five.commute_of_mem hu_mem (Subgroup.mem_zpowers zFive)).symm
  exact tcGenDatum_of_data QFive PFive xFive hFive e zFive (qFive 0)
    (qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4)
    (IsPGroup.of_card pinned_B_five_power_six_subgroup.2.2.2.2.2.2.2.2.1) le_sup_left hz5
    (hq5 0).1 hu5 orderOf_zFive (comm_qFive_zFive 0).symm hzu huq.symm zFive_mem (qFive_mem 0)
    hu_mem (mem_normalizer_of_conj xFive_conj_mem) (mem_normalizer_of_conj hhQ) he0'
    heu' hind' hgen

end CFSG.Sporadic.Bridge.B
