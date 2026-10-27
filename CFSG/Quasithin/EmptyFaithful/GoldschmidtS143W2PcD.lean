module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2PcC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocH

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem wOfX_mem_qOf (h : Ctx T M g A t d x) : wOfX d x ∈ qOf T := by
  have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
  have hdQ : d ∈ qOf T := (inf_le_left : dOf T M ≤ qOf T) hd
  have hu₀Q : u0Of d x ∈ qOf T := by
    rw [h.c19.a.q_eq]
    exact Subgroup.mem_sup_left (u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ)
  rw [wOfX_eq_mul_u0Of]
  exact (qOf T).mul_mem hdQ hu₀Q

theorem zpowers_w_le_pCore (h : Ctx T M g A t d x) :
    Subgroup.zpowers (wOfX d x) ≤ pCoreOf 2 (Gw d x) := by
  have hw2 := wOfX_sq h.c h.hD h.hd4 h.hx h.hx3
  have hfix : ∀ c ∈ Gw d x, ∀ y ∈ Subgroup.zpowers (wOfX d x), c * y * c⁻¹ = y := by
    intro c hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcw : Commute c (wOfX d x) := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [(Commute.zpow_right hcw k).eq, mul_inv_cancel_right]
  refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer ?_ ?_ ?_
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => by rw [hfix c hc y hy]; exact hy, fun hy => ?_⟩
    have h1 := hfix c⁻¹ (Subgroup.inv_mem _ hc) _ hy
    have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rw [e] at h1
    rw [h1]
    exact hy
  · have h2 : orderOf (wOfX d x) ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers]; exact hm)

theorem zpowers_u0_le_centralizer_w (h : Ctx T M g A t d x) :
    Subgroup.zpowers (u0Of d x) ≤
      Subgroup.centralizer (Subgroup.zpowers (wOfX d x) : Set G) := by
  have hu₀U := u0Of_mem_U h.c h.c18 h.hD h.hd4 h.hx h.hx3 h.hΓ
  have hcomm : u0Of d x * wOfX d x = wOfX d x * u0Of d x :=
    Subgroup.mem_centralizer_singleton_iff.mp (mem_K0_of_mem_U_comm h hu₀U rfl).2
  refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_left (show Commute (wOfX d x) (u0Of d x) from hcomm.symm) j).eq

theorem u0_zpowers_pCore (h : Ctx T M g A t d x) {a : G} (ha : a ∈ Subgroup.zpowers (u0Of d x))
    (haP : a ∈ pCoreOf 2 (Gw d x)) : a = 1 := by
  have hu₀z := u0Of_sq h.c h.hD h.hd4 h.hx h.hx3
  have hdd := dd_facts h.hd4
  have hnz := z_not_mem_pCore_Gw h
  have haa := (pCoreOf 2 (Gw d x)).mul_mem haP haP
  have hcz : u0Of d x * (d * d) = (d * d) * u0Of d x := by
    rw [← hu₀z]; group
  rcases mem_zpowers_four hu₀z hdd.1 ha with h1 | h1 | h1 | h1
  · exact h1
  · exact (hnz (by rwa [h1, hu₀z] at haa)).elim
  · exact (hnz (by rw [← h1]; exact haP)).elim
  · refine (hnz ?_).elim
    have e : (u0Of d x * (d * d)) * (u0Of d x * (d * d)) = d * d := by
      calc (u0Of d x * (d * d)) * (u0Of d x * (d * d))
          = u0Of d x * ((d * d) * u0Of d x) * (d * d) := by group
        _ = u0Of d x * (u0Of d x * (d * d)) * (d * d) := by rw [hcz]
        _ = (u0Of d x * u0Of d x) * ((d * d) * (d * d)) := by group
        _ = d * d := by rw [hu₀z, hdd.1, mul_one]
    rwa [h1, e] at haa

theorem pCore_inf_qOf (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) :
    pCoreOf 2 (Gw d x) ⊓ qOf T = Subgroup.zpowers (wOfX d x) := by
  refine le_antisymm ?_ fun e he => ⟨zpowers_w_le_pCore h he, ?_⟩
  · rintro e ⟨heP, heQ⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.Quasithin.mem_sup_of_commute
      (zpowers_u0_le_centralizer_w h) (hf0.Bw_inf_Q ⟨pCore_le_Bw h hf0 heP, heQ⟩)
    have hbP := zpowers_w_le_pCore h hb
    have haP : a ∈ pCoreOf 2 (Gw d x) := by
      have := (pCoreOf 2 (Gw d x)).mul_mem heP ((pCoreOf 2 (Gw d x)).inv_mem hbP)
      rwa [mul_inv_cancel_right] at this
    rw [u0_zpowers_pCore h ha haP, one_mul]
    exact hb
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (qOf T).zpow_mem (wOfX_mem_qOf h) k

theorem card_pCore_Gw_le (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) :
    Nat.card ↥(pCoreOf 2 (Gw d x)) ≤ 4 := by
  have hw2 := wOfX_sq h.c h.hD h.hd4 h.hx h.hx3
  have hmul := Subgroup.relIndex_mul_card (qOf T) (pCoreOf 2 (Gw d x))
  have hrel : (qOf T).relIndex (pCoreOf 2 (Gw d x)) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right (pCore_le_Bw h hf0) Subgroup.index_ne_zero_of_finite).trans
      hf0.Bw_relIndex
  have hinf : Nat.card ↥(qOf T ⊓ pCoreOf 2 (Gw d x)) ≤ 2 := by
    rw [inf_comm, pCore_inf_qOf h hf0, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2))
  rw [← hmul]
  nlinarith

theorem pCore_invol (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) :
    ∀ c ∈ pCoreOf 2 (Gw d x), c * c = 1 → c = 1 ∨ c = wOfX d x := by
  intro c hcP hc2
  have hcw : c ∈ Subgroup.zpowers (wOfX d x) := by
    rw [← pCore_inf_qOf h hf0]
    exact ⟨hcP, hf0.Bw_invol c (pCore_le_Bw h hf0 hcP) hc2⟩
  rcases mem_zpowers_four (wOfX_sq h.c h.hD h.hd4 h.hx h.hx3) (one_mul 1) hcw with
    h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact Or.inl h1
  · exact Or.inr (by rw [h1, mul_one])

theorem wp1_of_wp0 (h : Ctx T M g A t d x) (hf0 : Wp0 T d x) : Wp1 T d x where
  z_not_mem_P := z_not_mem_pCore_Gw h
  P_inf_K0 := pCore_inf_K0 h hf0
  P_le_Bw := pCore_le_Bw h hf0
  w_mem_P := zpowers_w_le_pCore h
  P_inf_Q := pCore_inf_qOf h hf0
  card_P := card_pCore_Gw_le h hf0
  P_invol := pCore_invol h hf0

end InspW2

end S143

end CFSG.Quasithin
