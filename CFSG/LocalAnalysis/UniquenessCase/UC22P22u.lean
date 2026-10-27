module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_exists_isMaxTwoLocal {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, IsMaxTwoLocalSubgroup N ∧ H ≤ N := by
  obtain ⟨N, hHN, hN⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hH
  exact ⟨N, ⟨hN.1, fun K hK hNK => le_antisymm (hN.2 hK hNK) hNK⟩, hHN⟩

theorem uc22p22u_isTwoLocal_centralizer {v : G} (hv1 : v ≠ 1) (hv : v ^ 2 = 1) :
    IsTwoLocal (centralizer ({v} : Set G)) := by
  have hord : orderOf v = 2 := orderOf_eq_prime hv hv1
  refine ⟨zpowers v, ?_, ?_, ?_⟩
  · intro h
    exact hv1 (by simpa using (Subgroup.zpowers_eq_bot.1 h))
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  · ext x
    simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    rw [mem_normalizer_iff]
    constructor
    · intro h y
      have hc : x * v * x⁻¹ = v := by
        calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [← h]
          _ = v := by group
      have hc' : x⁻¹ * v * x = v := by
        calc x⁻¹ * v * x = x⁻¹ * (v * x) := by group
          _ = x⁻¹ * (x * v) := by rw [h]
          _ = v := by group
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, by rw [← conj_zpow, hc]⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hy : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        have h5 : x⁻¹ * v ^ k * x = (x⁻¹ * v * x) ^ k := by
          have := conj_zpow (a := x⁻¹) (b := v) (i := k)
          simpa using this.symm
        rw [hy, ← hk, h5, hc']
    · intro h
      have h1 : x * v * x⁻¹ ∈ zpowers v := (h v).1 (mem_zpowers v)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h1
      have hk2 : v ^ k = 1 ∨ v ^ k = v := by
        rw [← zpow_mod_orderOf, hord]
        rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> simp [h0]
      rcases hk2 with h0 | h0
      · exfalso
        have : x * v * x⁻¹ = 1 := by rw [← hk, h0]
        apply hv1
        simpa using this
      · rw [h0] at hk
        have : x * v * x⁻¹ = v := hk.symm
        calc v * x = x * v * x⁻¹ * x := by rw [this]
          _ = x * v := by group

theorem uc22p22u_uniqueMax_of_calN (D : Data G) {L : Subgroup G} (hL : L ≤ D.M)
    (h : calNOf L = {D.M}) : UniqueMax D.M L := by
  unfold UniqueMax
  ext N
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hLN⟩
    haveI := D.standing.simple
    have hNtop : N ≠ ⊤ :=
      CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1
    obtain ⟨N', hN', hNN'⟩ := (eq_top_or_exists_le_coatom N).resolve_left hNtop
    have hmem : N' ∈ calNOf L := ⟨hN', hLN.trans hNN'⟩
    rw [h] at hmem
    have hNM : N ≤ D.M := by rw [← Set.mem_singleton_iff.1 hmem]; exact hNN'
    exact (hN.2 D.M D.maxLocal.1 hNM).symm
  · rintro rfl
    exact ⟨D.maxLocal, hL⟩

theorem uc22p22u_isTI_of_uniqueMax (D : Data G) {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) (hK : K ≤ centralizer (V : Set G)) (hU : UniqueMax D.M K) :
    IsTI V := by
  intro g
  by_cases hbot : V ⊓ conjSubgroup g V = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hvV : v ∈ V := hv.1
    have hv2 : v ^ 2 = 1 := hV.2 v hvV
    have hvg : g⁻¹ * v * g ∈ V := mem_conjSubgroup.1 hv.2
    obtain ⟨N, hNmax, hCN⟩ :=
      uc22p22u_exists_isMaxTwoLocal (uc22p22u_isTwoLocal_centralizer hv1' hv2)
    have hKN : K ≤ N := fun k hk => hCN (by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (mem_centralizer_iff.1 (hK hk)) v hvV)
    have hNM : N = D.M := by
      have hmem : N ∈ calMOf K := ⟨hNmax, hKN⟩
      rw [hU] at hmem
      exact hmem
    have hKg : ∀ k ∈ K, g * k * g⁻¹ ∈ N := fun k hk => hCN (by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hc : k * (g⁻¹ * v * g) = (g⁻¹ * v * g) * k :=
        (mem_centralizer_iff.1 (hK hk) _ hvg).symm
      calc v * (g * k * g⁻¹) = g * (g⁻¹ * v * g) * k * g⁻¹ := by group
        _ = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
        _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
        _ = (g * k * g⁻¹) * v := by group)
    have hconjN : uniqueFourConj g N = D.M := by
      have hmax : IsMaxTwoLocalSubgroup (uniqueFourConj g N) := UC6.isMaxTwoLocal_conj hNmax g
      have hmem : uniqueFourConj g N ∈ calMOf K := ⟨hmax, fun k hk => by
        rw [UC6.mem_uniqueFourConj_iff]
        exact hKg k hk⟩
      rw [hU] at hmem
      exact hmem
    rw [hNM] at hconjN
    have hgM : g ∈ D.M := by
      have : g ∈ normalizer (D.M : Set G) := UC6.uniqueFourConj_eq_self_iff.1 hconjN
      rwa [UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal] at this
    refine inf_eq_left.2 fun x hx => ?_
    rw [mem_conjSubgroup]
    exact (mem_normalizer_iff.1 (hMV (inv_mem hgM)) x).1 hx |> fun h => by simpa using h

theorem uc22p22u_gamma_mono {p : ℕ} {X X' : Subgroup G} (h : X' ≤ X) :
    rankThreeGamma 1 p X' ≤ rankThreeGamma 1 p X := by
  unfold rankThreeGamma GLBCore
  exact sSup_le_sSup fun N ⟨Q, hQ, hr, hN⟩ => ⟨Q, hQ.trans h, hr, hN⟩

theorem uc22p22u_uniqueMax_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXM : X ≤ D.M) (hX : IsPGroup p X)
    (hnc : ¬ IsCyclic ↥X) (hΓ : rankThreeGamma 1 p X ≤ D.M ∨ p ∈ D.sig) : UniqueMax D.M X := by
  rcases hΓ with hΓ | hsig
  · obtain ⟨E, hEX, hE, hcard⟩ := uc22p22u_exists_elemAbelian_sq hp hp2 hX hnc
    have hEM : UniqueMax D.M E :=
      h63 p hp hp2 E (hEX.trans hXM) hE hcard ((uc22p22u_gamma_mono hEX).trans hΓ)
    unfold UniqueMax at hEM ⊢
    refine Set.Subset.antisymm ?_ ?_
    · intro N hN
      have : N ∈ calMOf E := ⟨hN.1, hEX.trans hN.2⟩
      rwa [hEM] at this
    · rintro N rfl
      exact ⟨D.maxLocal, hXM⟩
  · exact h61 p hsig X hXM hX hnc

theorem uc22p22u_hyp11_W (D : Data G) {V : Subgroup G} (hV : F11.Hyp11 D ⊥ V) :
    InCalW D.M D.T V ∧ ¬ IsTI V := by
  obtain ⟨h | ⟨-, h⟩, hTI, -⟩ := hV
  · exact absurd rfl h.1.1
  · exact ⟨h, hTI⟩

theorem uc22p22u_cTilde_bot (M V : Subgroup G) : F11.CTilde M ⊥ V = M ⊓ centralizer (V : Set G) := by
  ext m
  simp only [F11.CTilde, Subgroup.mem_iInf, Subgroup.mem_inf, mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨(h 1 V.one_mem).1, fun v hv => ?_⟩
    have h3 : m * v * m⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := (h v hv).2.2
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  · rintro ⟨hm, h⟩ v hv
    refine ⟨hm, ?_, ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      simp [Subgroup.mem_bot]
    · rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact (h v hv).symm

theorem uc22p22u_isCyclic_inf_centralizer (D : Data G) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    {V : Subgroup G} (hV : F11.Hyp11 D ⊥ V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hXM : X ≤ D.M) (hX : IsPGroup p X) (hΓ : rankThreeGamma 1 p X ≤ D.M ∨ p ∈ D.sig) :
    IsCyclic ↥(X ⊓ centralizer (V : Set G)) := by
  by_contra hnc
  obtain ⟨hW, hTI⟩ := uc22p22u_hyp11_W D hV
  have hVinfo := hW.1.1
  have hU : UniqueMax D.M (X ⊓ centralizer (V : Set G)) :=
    uc22p22u_uniqueMax_of_noncyclic D h61 h63 hp hp2 (inf_le_left.trans hXM) hX.to_inf_left hnc
      (hΓ.imp_left fun h => (uc22p22u_gamma_mono inf_le_left).trans h)
  exact hTI (uc22p22u_isTI_of_uniqueMax D hVinfo.2.2.2 hVinfo.2.2.1 inf_le_right hU)

end CFSG.LocalAnalysis.UniquenessCase.UC22
