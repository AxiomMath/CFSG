module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin
  CFSG.Quasithin.FA5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem card_P1 (F : Frame L1 L2 S D X) : Nat.card (P1 L1 L2 S) = 15 * Nat.card S := by
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hBP : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hSP : S ≤ P1 L1 L2 S := hSB.trans hBP
  have h := Subgroup.relIndex_mul_relIndex S (bigB L1 L2 S) (P1 L1 L2 S) hSB hBP
  rw [F.pair.relIndex_S_bigB, F.pair.relIndex_bigB_left] at h
  have h2 := Subgroup.relIndex_mul_card (H := S) (K := P1 L1 L2 S)
  rw [inf_eq_left.mpr hSP, ← h] at h2
  rw [← h2]

theorem exists_conj_mem_D (F : Frame L1 L2 S D X) {t : G} (ht : t ∈ P1 L1 L2 S) (ht3 : t ^ 3 = 1) :
    ∃ g ∈ P1 L1 L2 S, g⁻¹ * t * g ∈ D := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hDB : D ≤ bigB L1 L2 S := F.D_le_B
  have hDP : D ≤ P1 L1 L2 S := hDB.trans le_sup_right
  set P := P1 L1 L2 S with hP
  set D' : Subgroup ↥P := D.subgroupOf P with hD'
  have hD'card : Nat.card D' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv]
    exact F.D_card
  have hD'p : IsPGroup 3 D' := IsPGroup.of_card (n := 1) (by rw [hD'card]; simp)
  obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup.exists_card_eq
  have hP15 : Nat.card P = 15 * 2 ^ k := by
    rw [hP, card_P1 F]
    congr 1
  have hle3 : ∀ Q : Sylow 3 ↥P, Nat.card (Q : Subgroup ↥P) ≤ 3 := by
    intro Q
    obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
    have hdvd : Nat.card (Q : Subgroup ↥P) ∣ Nat.card P := Subgroup.card_subgroup_dvd_card _
    rw [hn, hP15] at hdvd
    by_contra hlt
    have hn2 : 2 ≤ n := by
      by_contra h1
      have h1' : n ≤ 1 := by omega
      exact hlt (by
        rw [hn]
        calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1'
          _ = 3 := by norm_num)
    have h9 : 9 ∣ 15 * 2 ^ k :=
      (pow_dvd_pow 3 hn2 : 3 ^ 2 ∣ 3 ^ n).trans hdvd
    have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have : 9 ∣ 15 := hcop.dvd_of_dvd_mul_right h9
    omega
  obtain ⟨Q0, hQ0⟩ := hD'p.exists_le_sylow
  have hQ0D : (Q0 : Subgroup ↥P) = D' := by
    refine (Subgroup.eq_of_le_of_card_ge hQ0 ?_).symm
    rw [hD'card]
    exact hle3 Q0
  set t' : ↥P := ⟨t, ht⟩ with ht'
  have ht'3 : t' ^ 3 = 1 := Subtype.ext (by simpa using ht3)
  have hpg : IsPGroup 3 (Subgroup.zpowers t') := by
    have hdvd : orderOf t' ∣ 3 := orderOf_dvd_of_pow_eq_one ht'3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  obtain ⟨Q1', hQ1'⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P Q0 Q1'
  have hmem : t' ∈ ((g • Q0 : Sylow 3 ↥P) : Subgroup ↥P) := by
    rw [hg]; exact hQ1' (Subgroup.mem_zpowers t')
  rw [Sylow.coe_subgroup_smul, hQ0D] at hmem
  obtain ⟨s, hs, hst⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  refine ⟨(g : G), g.2, ?_⟩
  have hsD : (s : G) ∈ D := hs
  have hst' : (g : G) * (s : G) * (g : G)⁻¹ = t := by
    have := congrArg Subtype.val hst
    simpa [MulAut.smul_def] using this
  have : (g : G)⁻¹ * t * (g : G) = (s : G) := by
    rw [← hst']; group
  rw [this]
  exact hsD

omit [Finite G] in
theorem D_conj_mem_B (F : Frame L1 L2 S D X) {d p : G} (hd : d ∈ D) (hp : p ∈ P1 L1 L2 S) :
    p⁻¹ * d * p ∈ bigB L1 L2 S := by
  obtain ⟨x, hx, b, hb, rfl⟩ := F.exists_mul p hp
  have hdc : x⁻¹ * d * x = d := by
    have hc : x * d = d * x := Subgroup.mem_centralizer_iff.mp (F.D_cent hd) x hx
    calc x⁻¹ * d * x = x⁻¹ * (d * x) := by group
      _ = x⁻¹ * (x * d) := by rw [hc]
      _ = d := by group
  have : (x * b)⁻¹ * d * (x * b) = b⁻¹ * d * b := by
    calc (x * b)⁻¹ * d * (x * b) = b⁻¹ * (x⁻¹ * d * x) * b := by group
      _ = b⁻¹ * d * b := by rw [hdc]
  rw [this]
  exact (bigB L1 L2 S).mul_mem ((bigB L1 L2 S).mul_mem ((bigB L1 L2 S).inv_mem hb)
    (F.D_le_B hd)) hb

theorem three_conj_mem_B (F : Frame L1 L2 S D X) {t p : G} (ht : t ∈ P1 L1 L2 S) (ht3 : t ^ 3 = 1)
    (hp : p ∈ P1 L1 L2 S) : p⁻¹ * t * p ∈ bigB L1 L2 S := by
  obtain ⟨g, hg, hgd⟩ := exists_conj_mem_D F ht ht3
  have h1 : (g⁻¹ * p)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * p) ∈ bigB L1 L2 S :=
    D_conj_mem_B F hgd ((P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hg) hp)
  have : (g⁻¹ * p)⁻¹ * (g⁻¹ * t * g) * (g⁻¹ * p) = p⁻¹ * t * p := by group
  rwa [this] at h1

end CFSG.Quasithin.Kleidman.F204
