module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] {V : Type*} [MulAction G V]

private theorem le_normalizer_inf_self {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) :
    H ≤ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
  intro h hh
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hh) x
  have h2 := Subgroup.mem_normalizer_iff.mp (hHL hh) x
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr h1 h2

theorem rank_one_dichotomy [Finite G] {P K A S : Subgroup G} {Ω : Set V} {u : V}
    (hu : u ∈ Ω) (hPΩ : ∀ g ∈ P, ∀ w ∈ Ω, g • w ∈ Ω)
    (hS2 : IsPGroup 2 S) (hSn : P ⊓ MulAction.stabilizer G u ≤ Subgroup.normalizer (S : Set G))
    (hAS : A ≤ S) (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hAK : A ≤ K) (hAP : A ≤ P)
    (hAu : ∀ a ∈ A, a • u = u)
    (htr : ∀ w ∈ Ω, ∀ w' ∈ Ω, w ≠ u → w' ≠ u → ∃ a ∈ A, a • w = w') :
    A ≤ pCoreOf 2 K ∨ ∀ w ∈ Ω, ∀ w' ∈ Ω, ∃ x ∈ K ⊓ P, x • w = w' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hfix : ∀ x ∈ K ⊓ P, x • u = u
  · left
    have hJS : K ⊓ P ≤ Subgroup.normalizer (S : Set G) := by
      intro x hx
      exact hSn (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2,
        MulAction.mem_stabilizer_iff.mpr (hfix x hx)⟩)
    have hNcore : (K ⊓ P) ⊓ S ≤ pCoreOf 2 (K ⊓ P) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_self hJS)
        (hS2.to_le inf_le_right)
    have hKnorm : K ≤ Subgroup.normalizer ((K ⊓ P : Subgroup G) : Set G) :=
      le_normalizer_inf_self hKP
    have hcore : pCoreOf 2 (K ⊓ P) ≤ pCoreOf 2 K :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (K ⊓ P)).trans inf_le_left)
        (hKnorm.trans (normalizer_le_normalizer_pCoreOf 2 (K ⊓ P)))
        (pCoreOf_isPGroup 2 (K ⊓ P))
    intro a ha
    exact hcore (hNcore (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hAK ha, hAP ha⟩, hAS ha⟩))
  · right
    push Not at hfix
    obtain ⟨j, hjJ, hju⟩ := hfix
    have hAJ : ∀ a ∈ A, a ∈ K ⊓ P := fun a ha => Subgroup.mem_inf.mpr ⟨hAK ha, hAP ha⟩
    have hjΩ : j • u ∈ Ω := hPΩ j (Subgroup.mem_inf.mp hjJ).2 u hu
    have hfromu : ∀ w' ∈ Ω, ∃ x ∈ K ⊓ P, x • u = w' := by
      intro w' hw'
      by_cases hw'u : w' = u
      · exact ⟨1, one_mem _, by rw [hw'u, one_smul]⟩
      · obtain ⟨a, ha, haw⟩ := htr (j • u) hjΩ w' hw' hju hw'u
        exact ⟨a * j, mul_mem (hAJ a ha) hjJ, by rw [mul_smul, haw]⟩
    intro w hw w' hw'
    by_cases hwu : w = u
    · rw [hwu]
      exact hfromu w' hw'
    by_cases hw'u : w' = u
    · obtain ⟨y, hyJ, hyu⟩ := hfromu w hw
      exact ⟨y⁻¹, inv_mem hyJ, by rw [hw'u, ← hyu, inv_smul_smul]⟩
    · obtain ⟨a, ha, haw⟩ := htr w hw w' hw' hwu hw'u
      exact ⟨a, hAJ a ha, haw⟩

private theorem fix_step {J M E : Subgroup G} {Ω : Set V} {u : V} {e₁ e₂ : G}
    (hu : u ∈ Ω) (hJΩ : ∀ g ∈ J, ∀ w ∈ Ω, g • w ∈ Ω)
    (hJtr : ∀ w ∈ Ω, ∀ w' ∈ Ω, ∃ x ∈ J, x • w = w')
    (hEJ : E ≤ J) (hEu : ∀ e ∈ E, e • u = u)
    (hEtr : ∀ w ∈ Ω, ∀ w' ∈ Ω, w ≠ u → w' ≠ u → ∃ e ∈ E, e • w = w')
    (hEfree : ∀ e ∈ E, ∀ w ∈ Ω, w ≠ u → e • w = w → e = 1)
    (hE2 : ∀ e ∈ E, e * e = 1) (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1)
    (he₁₂ : e₁ ≠ e₂) (hΩ2 : ∃ w ∈ Ω, w ≠ u)
    (hJM : J ≤ Subgroup.normalizer (M : Set G)) (hMΩ : ∀ m ∈ M, ∀ w ∈ Ω, m • w ∈ Ω)
    (hcomm : ∀ g ∈ M, ∀ h ∈ M, ∀ w ∈ Ω, (g * h * g⁻¹ * h⁻¹) • w = w) :
    ∀ m ∈ M, ∀ w ∈ Ω, m • w = w := by
  have h2tr : ∀ a ∈ Ω, ∀ b ∈ Ω, ∀ c ∈ Ω, ∀ d ∈ Ω, a ≠ b → c ≠ d →
      ∃ j ∈ J, j • a = c ∧ j • b = d := by
    intro a ha b hb c hc d hd hab hcd
    obtain ⟨j₁, hj₁, hj₁a⟩ := hJtr a ha u hu
    obtain ⟨j₂, hj₂, hj₂c⟩ := hJtr c hc u hu
    have hj₁b : j₁ • b ∈ Ω := hJΩ j₁ hj₁ b hb
    have hj₂d : j₂ • d ∈ Ω := hJΩ j₂ hj₂ d hd
    have hj₁b_ne : j₁ • b ≠ u := by
      intro h
      apply hab
      have h' : j₁ • b = j₁ • a := by rw [h, hj₁a]
      exact (MulAction.injective j₁ h').symm
    have hj₂d_ne : j₂ • d ≠ u := by
      intro h
      apply hcd
      have h' : j₂ • d = j₂ • c := by rw [h, hj₂c]
      exact (MulAction.injective j₂ h').symm
    obtain ⟨e, he, hee⟩ := hEtr (j₁ • b) hj₁b (j₂ • d) hj₂d hj₁b_ne hj₂d_ne
    refine ⟨j₂⁻¹ * e * j₁, J.mul_mem (J.mul_mem (J.inv_mem hj₂) (hEJ he)) hj₁, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hj₁a, hEu e he, ← hj₂c, inv_smul_smul]
    · rw [mul_smul, mul_smul, hee, inv_smul_smul]
  have hcomm' : ∀ m ∈ M, ∀ m' ∈ M, ∀ w ∈ Ω, (m * m') • w = (m' * m) • w := by
    intro m hm m' hm' w hw
    have hx : (m' * m) • w ∈ Ω := hMΩ _ (M.mul_mem hm' hm) w hw
    have h := hcomm m hm m' hm' _ hx
    rw [← mul_smul] at h
    have e1 : m * m' * m⁻¹ * m'⁻¹ * (m' * m) = m * m' := by group
    rw [e1] at h
    exact h
  by_contra hcon
  push Not at hcon
  obtain ⟨m₀, hm₀, w₀, hw₀, hne⟩ := hcon
  have htransM : ∀ v ∈ Ω, ∃ n ∈ M, n • u = v := by
    intro v hv
    by_cases hvu : v = u
    · exact ⟨1, M.one_mem, by rw [hvu, one_smul]⟩
    · obtain ⟨j, hj, hjw, hjv⟩ :=
        h2tr w₀ hw₀ (m₀ • w₀) (hMΩ m₀ hm₀ w₀ hw₀) u hu v hv (Ne.symm hne) (Ne.symm hvu)
      refine ⟨j * m₀ * j⁻¹, (Subgroup.mem_normalizer_iff.mp (hJM hj) m₀).mp hm₀, ?_⟩
      have hj' : j⁻¹ • u = w₀ := by rw [← hjw, inv_smul_smul]
      rw [mul_smul, mul_smul, hj', hjv]
  have hfixE : ∀ e ∈ E, e ≠ 1 → ∀ v ∈ Ω, ∀ n ∈ M, n • u = v → e • v = n⁻¹ • u := by
    intro e he he1 v hv n hn hnu
    have heJ : e ∈ J := hEJ he
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE2 e he)
    have hu' : e⁻¹ • u = u := hEu e⁻¹ (E.inv_mem he)
    have hn' : e * n * e⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hJM heJ) n).mp hn
    have hcM : n * (e * n * e⁻¹) ∈ M := M.mul_mem hn hn'
    have hid := hcomm' n hn (e * n * e⁻¹) hn' u hu
    have hconj : e * (n * (e * n * e⁻¹)) * e⁻¹ = e * n * e⁻¹ * n := by
      rw [heinv]
      calc e * (n * (e * n * e)) * e = e * n * e * n * (e * e) := by group
        _ = e * n * e * n := by rw [hE2 e he, mul_one]
    have h3 : (e * n * e⁻¹ * n) • u = e • ((n * (e * n * e⁻¹)) • u) := by
      rw [← hconj, mul_smul (e * (n * (e * n * e⁻¹))) e⁻¹ u,
        mul_smul e (n * (e * n * e⁻¹)) (e⁻¹ • u), hu']
    have hfixX : e • ((n * (e * n * e⁻¹)) • u) = (n * (e * n * e⁻¹)) • u := by
      rw [← h3]
      exact hid.symm
    have hXu : (n * (e * n * e⁻¹)) • u = u := by
      by_contra hne'
      exact he1 (hEfree e he _ (hMΩ _ hcM u hu) hne' hfixX)
    have hn'u : (e * n * e⁻¹) • u = e • v := by
      rw [mul_smul, mul_smul, hu', hnu]
    rw [mul_smul, hn'u] at hXu
    calc e • v = n⁻¹ • (n • (e • v)) := (inv_smul_smul n (e • v)).symm
      _ = n⁻¹ • u := by rw [hXu]
  obtain ⟨w, hw, hwu⟩ := hΩ2
  obtain ⟨n, hn, hnw⟩ := htransM w hw
  have h1 := hfixE e₁ he₁ he₁1 w hw n hn hnw
  have h2 := hfixE e₂ he₂ he₂1 w hw n hn hnw
  have hEe : e₁⁻¹ * e₂ ∈ E := E.mul_mem (E.inv_mem he₁) he₂
  have hfixw : (e₁⁻¹ * e₂) • w = w := by
    rw [mul_smul, h2, ← h1, inv_smul_smul]
  exact he₁₂ (inv_mul_eq_one.mp (hEfree _ hEe w hw hwu hfixw))

theorem fix_of_isSolvable {J R E : Subgroup G} {Ω : Set V} {u : V} {e₁ e₂ : G}
    (hu : u ∈ Ω) (hJΩ : ∀ g ∈ J, ∀ w ∈ Ω, g • w ∈ Ω)
    (hJtr : ∀ w ∈ Ω, ∀ w' ∈ Ω, ∃ x ∈ J, x • w = w')
    (hEJ : E ≤ J) (hEu : ∀ e ∈ E, e • u = u)
    (hEtr : ∀ w ∈ Ω, ∀ w' ∈ Ω, w ≠ u → w' ≠ u → ∃ e ∈ E, e • w = w')
    (hEfree : ∀ e ∈ E, ∀ w ∈ Ω, w ≠ u → e • w = w → e = 1)
    (hE2 : ∀ e ∈ E, e * e = 1) (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1)
    (he₁₂ : e₁ ≠ e₂) (hΩ2 : ∃ w ∈ Ω, w ≠ u)
    (hRJ : J ≤ Subgroup.normalizer (R : Set G)) (hRs : Group.IsSolvable R)
    (hRΩ : ∀ r ∈ R, ∀ w ∈ Ω, r • w ∈ Ω) :
    ∀ r ∈ R, ∀ w ∈ Ω, r • w = w := by
  obtain ⟨N, hN⟩ := Group.IsSolvable.solvable (G := ↥R)
  have hsucc : ∀ k, (derivedSeries ↥R (k + 1)).map R.subtype =
      ⁅(derivedSeries ↥R k).map R.subtype, (derivedSeries ↥R k).map R.subtype⁆ := by
    intro k
    rw [derivedSeries_succ]
    exact Subgroup.map_commutator _ _ R.subtype
  have hstep : ∀ k, (∀ g ∈ (derivedSeries ↥R (k + 1)).map R.subtype, ∀ w ∈ Ω, g • w = w) →
      ∀ g ∈ (derivedSeries ↥R k).map R.subtype, ∀ w ∈ Ω, g • w = w := by
    intro k hk
    exact fix_step (M := (derivedSeries ↥R k).map R.subtype) hu hJΩ hJtr hEJ hEu hEtr hEfree
      hE2 he₁ he₂ he₁1 he₂1 he₁₂ hΩ2
      (fun j hj => normalizer_le_normalizer_map_of_characteristic (derivedSeries ↥R k) (hRJ hj))
      (fun m hm w hw => hRΩ m (Subgroup.map_subtype_le _ hm) w hw)
      (fun g hg h hh w hw => hk (g * h * g⁻¹ * h⁻¹) (by
        rw [hsucc k]
        exact Subgroup.commutator_mem_commutator hg hh) w hw)
  have hall : ∀ d k, k + d = N →
      ∀ g ∈ (derivedSeries ↥R k).map R.subtype, ∀ w ∈ Ω, g • w = w := by
    intro d
    induction d with
    | zero =>
      intro k hk g hg w hw
      obtain rfl : k = N := by omega
      rw [hN, Subgroup.map_bot, Subgroup.mem_bot] at hg
      rw [hg, one_smul]
    | succ d ih =>
      intro k hk
      exact hstep k (ih (k + 1) (by omega))
  intro r hr w hw
  exact hall N 0 (by omega) r
    (Subgroup.mem_map.mpr ⟨⟨r, hr⟩, Subgroup.mem_top _, rfl⟩) w hw

end CFSG.Quasithin.RonanE114Low
