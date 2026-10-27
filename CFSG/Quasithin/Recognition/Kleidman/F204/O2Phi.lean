module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalReg
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2A5

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem Q1_le_B (F : Frame L1 L2 S D X) {q : G} (hq : q ∈ Q1 L1 L2 S) :
    q ∈ bigB L1 L2 S := F.mem_B_of_mem_S (F.Q1_le_S hq)

theorem exists_phi_Q1 (F : Frame L1 L2 S D X) :
    ∃ φ : ↥(P2 L1 L2 S) →* Alt5, (∀ p : ↥(P2 L1 L2 S), φ p = 1 ↔ (p : G) ∈ Q2 L1 L2 S) ∧
      ∃ T : Subgroup Alt5, Nat.card T = 4 ∧
        (∀ q : ↥(P2 L1 L2 S), (q : G) ∈ Q1 L1 L2 S → φ q ∈ T) ∧
        (∀ k ∈ T, ∃ q : ↥(P2 L1 L2 S), (q : G) ∈ Q1 L1 L2 S ∧ φ q = k) ∧
        ∀ p : ↥(P2 L1 L2 S), φ p ∈ Subgroup.normalizer (T : Set Alt5) ↔ (p : G) ∈ bigB L1 L2 S := by
  obtain ⟨φ, hφs, hφk⟩ := exists_phi_P2 F
  obtain ⟨T0, hT0, hlift, hN⟩ := exists_klein_phi F hφs hφk
  set Q' : Subgroup ↥(P2 L1 L2 S) := (Q1 L1 L2 S).subgroupOf (P2 L1 L2 S) with hQ'
  set T1 : Subgroup Alt5 := Q'.map φ with hT1
  have hle : T0 ≤ T1 := by
    intro k hk
    obtain ⟨q, hq, hqk⟩ := hlift k hk
    exact ⟨q, hq, hqk⟩
  have hQ'p : IsPGroup 2 Q' :=
    (pCoreOf_isPGroup 2 (P1 L1 L2 S)).comap_of_injective (P2 L1 L2 S).subtype
      (P2 L1 L2 S).subtype_injective
  have hp : IsPGroup 2 T1 := hQ'p.map φ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  have hdvd : Nat.card T1 ∣ 60 := by
    have := Subgroup.card_subgroup_dvd_card T1
    rwa [a5_card] at this
  have hn3 : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have : (2 : ℕ) ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 h3
    rw [← hn] at this
    have := this.trans hdvd
    omega
  have hcard : Nat.card T1 ≤ Nat.card T0 := by
    rw [hn, hT0]
    calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 4 := by norm_num
  have hTeq : T0 = T1 := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨φ, hφk, T0, hT0, fun q hq => ?_, hlift, hN⟩
  rw [hTeq]
  exact ⟨q, hq, rfl⟩

theorem Q1_inf_conj_le_Q2 (F : Frame L1 L2 S D X) {g q : G} (hg : g ∈ P2 L1 L2 S)
    (hgB : g ∉ bigB L1 L2 S) (hq : q ∈ Q1 L1 L2 S) (h : g⁻¹ * q * g ∈ bigB L1 L2 S) :
    q ∈ Q2 L1 L2 S := by
  obtain ⟨φ, hφk, T, hT4, hTin, -, hN⟩ := exists_phi_Q1 F
  have hqP : q ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (Q1_le_B F hq)
  have hxN : φ ⟨g, hg⟩ ∉ Subgroup.normalizer (T : Set Alt5) := fun h' => hgB ((hN _).mp h')
  have hyT : φ ⟨q, hqP⟩ ∈ T := hTin _ hq
  have hxy : (φ ⟨g, hg⟩)⁻¹ * φ ⟨q, hqP⟩ * φ ⟨g, hg⟩ ∈ Subgroup.normalizer (T : Set Alt5) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hN _).mpr h
  have := alt5_klein_free hT4 hxN hyT hxy
  exact (hφk _).mp this

theorem exists_third (F : Frame L1 L2 S D X) {y : G} (hy : y ∈ Q1 L1 L2 S)
    (hyQ : y ∉ Q2 L1 L2 S) :
    ∃ q ∈ Q1 L1 L2 S, q ∉ Q2 L1 L2 S ∧ y * q ∉ Q2 L1 L2 S ∧ y * q⁻¹ ∉ Q2 L1 L2 S := by
  obtain ⟨φ, hφk, T, hT4, hTin, hlift, -⟩ := exists_phi_Q1 F
  have hyP : y ∈ P2 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (Q1_le_B F hy)
  set y' : ↥(P2 L1 L2 S) := ⟨y, hyP⟩ with hy'
  have hyT : φ y' ∈ T := hTin _ hy
  have hy1 : φ y' ≠ 1 := fun h => hyQ ((hφk _).mp h)
  obtain ⟨k, hkT, hk1, hky⟩ : ∃ k ∈ T, k ≠ 1 ∧ k ≠ φ y' := by
    by_contra hcon
    push Not at hcon
    have hsub : (T : Set Alt5) ⊆ {1, φ y'} := by
      intro k hk
      by_cases h1 : k = 1
      · left; exact h1
      · right; exact hcon k hk h1
    have hfin : Nat.card T ≤ 2 := by
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, φ y'} : Set Alt5).ncard ≤ 2 :=
        (Set.ncard_insert_le 1 {φ y'}).trans (by simp)
      have h3 : (T : Set Alt5).ncard = Nat.card T := (Nat.card_coe_set_eq _).symm
      omega
    omega
  obtain ⟨q, hq, hqk⟩ := hlift k hkT
  have hqP : (q : G) ∈ P2 L1 L2 S := q.2
  have hkk : k * k = 1 := alt5_klein_sq hT4 hkT
  have hyy : φ y' * φ y' = 1 := alt5_klein_sq hT4 hyT
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · intro h
    exact hk1 (hqk ▸ (hφk q).mpr h)
  · intro h
    have h1 : φ (y' * q) = 1 := (hφk _).mpr h
    rw [map_mul, hqk] at h1
    apply hky
    calc k = (φ y')⁻¹ := by
          have := congrArg (fun z => (φ y')⁻¹ * z) h1
          simpa using this
      _ = φ y' := by
          rw [inv_eq_iff_mul_eq_one]; exact hyy
  · intro h
    have h1 : φ (y' * q⁻¹) = 1 := (hφk _).mpr h
    rw [map_mul, map_inv, hqk] at h1
    apply hky
    have hkinv : k⁻¹ = k := by rw [inv_eq_iff_mul_eq_one]; exact hkk
    rw [hkinv] at h1
    calc k = (φ y')⁻¹ := by
          have := congrArg (fun z => (φ y')⁻¹ * z) h1
          simpa using this
      _ = φ y' := by
          rw [inv_eq_iff_mul_eq_one]; exact hyy

end CFSG.Quasithin.Kleidman.F204
