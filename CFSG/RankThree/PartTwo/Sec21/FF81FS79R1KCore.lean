module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KBase
public import CFSG.RankThree.PartTwo.Sec21.FF84S23

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)
open CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]
variable {b t c : G} {J : Subgroup G}

theorem FS79Hyp1.normal_le_B_decomp (h : FS79Hyp1 b t c J) {M : Subgroup G} [M.Normal]
    (hMB : M ≤ Subgroup.closure ({b, c} : Set G)) {y : G} (hy : y ∈ M) :
    ∃ p ∈ Subgroup.zpowers b, ∃ q ∈ Subgroup.zpowers c, y = p * q ∧ p ∈ M ∧ q ∈ M := by
  have hbc : Commute b c := h.bc_comm
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow hbc i j
  have hyB := hMB hy
  rw [closure_pair_eq_sup] at hyB
  obtain ⟨p, hp, q, hq, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hyB
  refine ⟨p, hp, q, hq, rfl, ?_, ?_⟩
  ·
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have htb : t * b ^ i * t⁻¹ = (b ^ i)⁻¹ := by
      have := map_zpow (MulAut.conj t) b i
      simp only [MulAut.conj_apply] at this
      rw [this, h.inv_b, inv_zpow']
      simp
    have htc : t * c ^ j * t⁻¹ = c ^ j := by
      have : t * c ^ j = c ^ j * t :=
        (Commute.zpow_right (show Commute t c from
          (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t h.c_mem)).symm) j).eq
      calc t * c ^ j * t⁻¹ = c ^ j * t * t⁻¹ := by rw [this]
        _ = c ^ j := by group
    have hty : t * (b ^ i * c ^ j) * t⁻¹ ∈ M := by
      have := (inferInstance : M.Normal).conj_mem _ hy t
      exact this
    have e1 : t * (b ^ i * c ^ j) * t⁻¹ = (b ^ i)⁻¹ * c ^ j := by
      calc t * (b ^ i * c ^ j) * t⁻¹ = (t * b ^ i * t⁻¹) * (t * c ^ j * t⁻¹) := by group
        _ = (b ^ i)⁻¹ * c ^ j := by rw [htb, htc]
    rw [e1] at hty
    have hp2 : (b ^ i) ^ 2 ∈ M := by
      have hbc' : Commute (b ^ i) (c ^ j) := Commute.zpow_zpow hbc i j
      have : (b ^ i * c ^ j) * ((b ^ i)⁻¹ * c ^ j)⁻¹ = (b ^ i) ^ 2 := by
        calc (b ^ i * c ^ j) * ((b ^ i)⁻¹ * c ^ j)⁻¹
            = b ^ i * (c ^ j * (c ^ j)⁻¹) * ((b ^ i)⁻¹)⁻¹ := by
              rw [mul_inv_rev, mul_assoc]
              group
          _ = (b ^ i) ^ 2 := by group
      rw [← this]
      exact M.mul_mem hy (M.inv_mem hty)
    have hp3 : (b ^ i) ^ 3 = 1 := by
      have e : (b ^ i) ^ (3 : ℕ) = (b ^ (3 : ℕ)) ^ i := by
        rw [← zpow_natCast, ← zpow_natCast b 3, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [e, h.b_pow_three, one_zpow]
    have : b ^ i = ((b ^ i) ^ 2) ^ 2 := by
      calc b ^ i = (b ^ i) ^ 4 * ((b ^ i) ^ 3)⁻¹ := by group
        _ = ((b ^ i) ^ 2) ^ 2 := by rw [hp3]; group
    rw [this]
    exact M.pow_mem hp2 2
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have htb : t * b ^ i * t⁻¹ = (b ^ i)⁻¹ := by
      have := map_zpow (MulAut.conj t) b i
      simp only [MulAut.conj_apply] at this
      rw [this, h.inv_b, inv_zpow']
      simp
    have htc : t * c ^ j * t⁻¹ = c ^ j := by
      have : t * c ^ j = c ^ j * t :=
        (Commute.zpow_right (show Commute t c from
          (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t h.c_mem)).symm) j).eq
      calc t * c ^ j * t⁻¹ = c ^ j * t * t⁻¹ := by rw [this]
        _ = c ^ j := by group
    have hty : t * (b ^ i * c ^ j) * t⁻¹ ∈ M := by
      have := (inferInstance : M.Normal).conj_mem _ hy t
      exact this
    have e1 : t * (b ^ i * c ^ j) * t⁻¹ = (b ^ i)⁻¹ * c ^ j := by
      calc t * (b ^ i * c ^ j) * t⁻¹ = (t * b ^ i * t⁻¹) * (t * c ^ j * t⁻¹) := by group
        _ = (b ^ i)⁻¹ * c ^ j := by rw [htb, htc]
    rw [e1] at hty
    have hbc' : Commute (b ^ i) (c ^ j) := Commute.zpow_zpow hbc i j
    have hq2 : (c ^ j) ^ 2 ∈ M := by
      have : ((b ^ i)⁻¹ * c ^ j) * (b ^ i * c ^ j) = (c ^ j) ^ 2 := by
        calc ((b ^ i)⁻¹ * c ^ j) * (b ^ i * c ^ j)
            = (b ^ i)⁻¹ * (c ^ j * b ^ i) * c ^ j := by group
          _ = (b ^ i)⁻¹ * (b ^ i * c ^ j) * c ^ j := by rw [← hbc'.eq]
          _ = (c ^ j) ^ 2 := by group
      rw [← this]
      exact M.mul_mem hty hy
    have hq3 : (c ^ j) ^ 3 = 1 := by
      have e : (c ^ j) ^ (3 : ℕ) = (c ^ (3 : ℕ)) ^ j := by
        rw [← zpow_natCast, ← zpow_natCast c 3, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [e, h.c_pow_three, one_zpow]
    have : c ^ j = ((c ^ j) ^ 2) ^ 2 := by
      calc c ^ j = (c ^ j) ^ 4 * ((c ^ j) ^ 3)⁻¹ := by group
        _ = ((c ^ j) ^ 2) ^ 2 := by rw [hq3]; group
    rw [this]
    exact M.pow_mem hq2 2

theorem FS79Hyp1.nor_top_of_normal_three_group (h : FS79Hyp1 b t c J)
    (hO : Opp 3 (⊤ : Subgroup G) = ⊥) {M : Subgroup G} [hMn : M.Normal] (hM1 : M ≠ ⊥)
    (hM3 : IsPGroup 3 M) : Nor (Subgroup.zpowers b) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbc : Commute b c := h.bc_comm
  have hMB : M ≤ Subgroup.closure ({b, c} : Set G) := by
    obtain ⟨k, -, hk⟩ := L14.exists_conj_le_sylowOf h.isSylowOf_B_top (le_top : M ≤ ⊤) hM3
    intro y hy
    have h1 := hk (k⁻¹ * y * k) (hMn.conj_mem y hy k⁻¹ |> fun hh => by simpa using hh)
    simpa [mul_assoc] using h1
  have hdec := fun {y : G} (hy : y ∈ M) => h.normal_le_B_decomp hMB hy
  have hcub : ∀ {w : G}, w ^ 3 = 1 → ∀ {p : G}, p ∈ Subgroup.zpowers w → p ∈ M → p ≠ 1 → w ∈ M := by
    intro w hw p hp hpM hp1
    by_cases hw1 : w = 1
    · rw [hw1]; exact M.one_mem
    rcases eq_or_inv_of_mem_zpowers_of_pow_three hw hw1 hp hp1 with h' | h'
    · rw [← h']; exact hpM
    · have : w = p⁻¹ := by rw [h', inv_inv]
      rw [this]; exact M.inv_mem hpM
  have hb3 := h.b_pow_three
  have hc3 := h.c_pow_three
  have hcases : ∀ {y : G}, y ∈ M → y ≠ 1 → b ∈ M ∨ c ∈ M := by
    intro y hy hy1
    obtain ⟨p, hp, q, hq, rfl, hpM, hqM⟩ := hdec hy
    by_cases hp1 : p = 1
    · right
      have hq1 : q ≠ 1 := by intro hq1; apply hy1; rw [hp1, hq1, mul_one]
      exact hcub hc3 hq hqM hq1
    · left
      exact hcub hb3 hp hpM hp1
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hM1
  have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  have hbcM := hcases x.2 hx1'
  have hMnormal : ∀ {X : Subgroup G}, X = M → Nor X = ⊤ := by
    intro X hX
    rw [hX]
    exact Subgroup.normalizer_eq_top M
  by_cases hbM : b ∈ M
  · by_cases hcM : c ∈ M
    ·
      have hBM : Subgroup.closure ({b, c} : Set G) ≤ M := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact hbM
        · exact hcM
      have hMB' : M = Subgroup.closure ({b, c} : Set G) := le_antisymm hMB hBM
      rw [eq_top_iff]
      intro g _
      refine h.mem_Nor_of_conj_b ?_
      rw [← hMB']
      exact hMn.conj_mem b hbM g
    ·
      have hMb : M = Subgroup.zpowers b := by
        apply le_antisymm
        · intro y hy
          obtain ⟨p, hp, q, hq, rfl, hpM, hqM⟩ := hdec hy
          have hq1 : q = 1 := by
            by_contra hq1
            exact hcM (hcub hc3 hq hqM hq1)
          rw [hq1, mul_one]
          exact hp
        · exact Subgroup.zpowers_le.mpr hbM
      exact hMnormal hMb.symm
  · by_cases hcM : c ∈ M
    ·
      have hMc : M = Subgroup.zpowers c := by
        apply le_antisymm
        · intro y hy
          obtain ⟨p, hp, q, hq, rfl, hpM, hqM⟩ := hdec hy
          have hp1 : p = 1 := by
            by_contra hp1
            exact hbM (hcub hb3 hp hpM hp1)
          rw [hp1, one_mul]
          exact hq
        · exact Subgroup.zpowers_le.mpr hcM
      have hNc : Nor (Subgroup.zpowers c) = ⊤ := hMnormal hMc.symm
      have hN := h.N_c
      rw [hNc, hO] at hN
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ setMul (⊥ : Subgroup G) (Nor (Subgroup.zpowers b) ⊓ ⊤) := by
        rw [hN]
        trivial
      obtain ⟨o, ho, n, hn, hgon⟩ := hg
      rw [Subgroup.mem_bot] at ho
      rw [hgon, ho, one_mul]
      exact hn.1
    · exfalso
      rcases hbcM with h1 | h1
      · exact hbM h1
      · exact hcM h1

theorem FS79Hyp1.fusion_B (h : FS79Hyp1 b t c J) {x y g : G}
    (hx : x ∈ Subgroup.closure ({b, c} : Set G)) (hy : y ∈ Subgroup.closure ({b, c} : Set G))
    (hg : g * x * g⁻¹ = y) :
    ∃ n ∈ Nor (Subgroup.closure ({b, c} : Set G)), n * x * n⁻¹ = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPs := h.isSylowOf_B_top
  have hcop' : ¬ 3 ∣ (Subgroup.closure ({b, c} : Set G)).index := by
    rw [← Subgroup.relIndex_top_right]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPs.2.2
  obtain ⟨S, hS⟩ : ∃ S : Sylow 3 G, (S : Subgroup G) = Subgroup.closure ({b, c} : Set G) :=
    ⟨hPs.2.1.toSylow hcop', IsPGroup.toSylow_coe hPs.2.1 hcop'⟩
  haveI hcomm' : IsMulCommutative (S : Subgroup G) :=
    ⟨⟨fun a c' => Subtype.ext (h.B_comm (by rw [← hS]; exact a.2) (by rw [← hS]; exact c'.2))⟩⟩
  have hxS : x ∈ (S : Subgroup G) := by rw [hS]; exact hx
  have hyS : y ∈ (S : Subgroup G) := by rw [hS]; exact hy
  obtain ⟨n, hn, hn'⟩ := S.conj_eq_normalizer_conj_of_mem x g⁻¹ hxS
    (by rw [inv_inv, hg]; exact hyS)
  refine ⟨n⁻¹, ?_, ?_⟩
  · have hn2 : n ∈ Nor (S : Subgroup G) := hn
    have := (Nor (S : Subgroup G)).inv_mem hn2
    rwa [hS] at this
  · rw [inv_inv]
    rw [inv_inv, hg] at hn'
    exact hn'.symm

theorem FS79Hyp1.B_inf_J (h : FS79Hyp1 b t c J) {y : G}
    (hy : y ∈ Subgroup.closure ({b, c} : Set G)) (hyJ : y ∈ J) : y ∈ Subgroup.zpowers c := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow h.bc_comm i j
  rw [closure_pair_eq_sup] at hy
  obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hy
  have hvJ : v ∈ J := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact J.zpow_mem h.c_mem j
  have huJ : u ∈ J := by
    have := J.mul_mem hyJ (J.inv_mem hvJ)
    simpa using this
  have : u ∈ Subgroup.zpowers b ⊓ J := ⟨hu, huJ⟩
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hv

theorem FS79Hyp1.stronglyClosed_b (h : FS79Hyp1 b t c J) :
    IsStronglyClosedIn (Subgroup.closure ({b, c} : Set G)) (Subgroup.zpowers b : Set G) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.zpow_mem _ (FS79Hyp1.b_mem_B b c) i
  · intro a ha g hg
    by_cases ha1 : a = 1
    · rw [ha1]; simp
    have hb : g⁻¹ * b * g ∈ Subgroup.closure ({b, c} : Set G) := by
      rcases eq_or_inv_of_mem_zpowers_of_pow_three h.b_pow_three h.b_ne_one ha ha1 with h1 | h1
      · rw [h1] at hg; exact hg
      · rw [h1] at hg
        have := (Subgroup.closure ({b, c} : Set G)).inv_mem hg
        simpa [mul_assoc] using this
    have hgN : g⁻¹ ∈ Nor (Subgroup.zpowers b) := by
      refine h.mem_Nor_of_conj_b ?_
      simpa using hb
    have := (Subgroup.mem_normalizer_iff.mp hgN a).mp ha
    simpa using this

theorem FS79Hyp1.stronglyClosed_c (h : FS79Hyp1 b t c J) :
    IsStronglyClosedIn (Subgroup.closure ({b, c} : Set G)) (Subgroup.zpowers c : Set G) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨i, rfl⟩ := hx
    exact Subgroup.zpow_mem _ (FS79Hyp1.c_mem_B b c) i
  · intro a ha g hg
    by_cases ha1 : a = 1
    · rw [ha1]; simp
    have haB : a ∈ Subgroup.closure ({b, c} : Set G) := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact Subgroup.zpow_mem _ (FS79Hyp1.c_mem_B b c) i
    obtain ⟨n, hnB, hn⟩ := h.fusion_B haB hg (g := g⁻¹) (by simp)
    have hnb : n * b * n⁻¹ ∈ Subgroup.closure ({b, c} : Set G) :=
      (Subgroup.mem_normalizer_iff.mp hnB b).mp (FS79Hyp1.b_mem_B b c)
    have hnN : n ∈ Nor (Subgroup.zpowers b) := h.mem_Nor_of_conj_b hnb
    obtain ⟨k, hk, y, hy, j, hj, rfl⟩ := h.nor_decomp hnN
    have haJ : a ∈ J := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact J.zpow_mem h.c_mem i
    have hconj := h.conj_eq_of_decomp hk hy hj haJ
    have hyJ : g⁻¹ * a * g ∈ J := by
      rw [← hn, hconj]
      exact J.mul_mem (J.mul_mem hj haJ) (J.inv_mem hj)
    exact h.B_inf_J hg hyJ

theorem Opp_top_le_pPrimeCore : Opp 3 (⊤ : Subgroup G) ≤ CFSG.pPrimeCore 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : (Opp 3 (⊤ : Subgroup G)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    simpa using L14.Opp_conj_mem (p := 3) (H := (⊤ : Subgroup G)) (Subgroup.mem_top g) hx
  exact le_sSup ⟨hn, L14.Opp_coprime 3 (⊤ : Subgroup G)⟩

theorem pPrimeCore_le_Opp_top : CFSG.pPrimeCore 3 G ≤ Opp 3 (⊤ : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := CFSG.pPrimeCore_normal (p := 3) (G := G)
  exact L14.le_Opp_of_normalized le_top (fun g _ x hx => (CFSG.pPrimeCore_normal (p := 3)
    (G := G)).conj_mem x hx g) (CFSG.pPrimeCore_coprime_card (p := 3) (G := G))

theorem pPrimeCore_eq_bot_iff : CFSG.pPrimeCore 3 G = ⊥ ↔ Opp 3 (⊤ : Subgroup G) = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp (Opp_top_le_pPrimeCore.trans h.le)
  · intro h
    exact le_bot_iff.mp (pPrimeCore_le_Opp_top.trans h.le)

theorem exists_minimal_normal_le {X : Subgroup G} [X.Normal] (hX : X ≠ ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ M ≠ ⊥ ∧ M ≤ X ∧
      ∀ Y : Subgroup G, Y.Normal → Y ≤ M → Y = ⊥ ∨ Y = M := by
  classical
  obtain ⟨M, ⟨hMn, hM1, hMX⟩, hmin⟩ :=
    (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥ ∧ M ≤ X}).exists_minimal
      ⟨X, inferInstance, hX, le_rfl⟩
  refine ⟨M, hMn, hM1, hMX, fun Y hY hYM => ?_⟩
  by_cases hY1 : Y = ⊥
  · exact Or.inl hY1
  · exact Or.inr (le_antisymm hYM (hmin ⟨hY, hY1, hYM.trans hMX⟩ hYM))

theorem FS79Hyp1.nor_eq_top (hKF1 : FF84KF1) (hKS : FF84KSOut)
    (hK : KCore.KGroupNonab InCatalog G) (hO : CFSG.pPrimeCore 3 G = ⊥)
    (h : FS79Hyp1 b t c J) : Nor (Subgroup.zpowers b) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOpp : Opp 3 (⊤ : Subgroup G) = ⊥ := pPrimeCore_eq_bot_iff.mp hO
  have hcard1 : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, h.ord_b]
  have hcard2 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, h.ord_c]
  have hsup : Subgroup.zpowers b ⊔ Subgroup.zpowers c = Subgroup.closure ({b, c} : Set G) :=
    (closure_pair_eq_sup b c).symm
  have hinf : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff, ← h.zpowers_inf_J]
    exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr h.c_mem)
  have hres := ff84_2_3_reduced_of hKF1 hKS G hK hO (Subgroup.closure ({b, c} : Set G))
    (Subgroup.zpowers b) (Subgroup.zpowers c) h.isSylowOf_B_top h.card_B hcard1 hcard2 hsup hinf
    h.stronglyClosed_b h.stronglyClosed_c
  set X₁ : Subgroup G := Subgroup.normalClosure (Subgroup.zpowers b : Set G) with hX₁
  set X₂ : Subgroup G := Subgroup.normalClosure (Subgroup.zpowers c : Set G) with hX₂
  have hX₂n : X₂.Normal := Subgroup.normalClosure_normal
  have hX₁n : X₁.Normal := Subgroup.normalClosure_normal
  have hcomm : ⁅X₁, X₂⁆ = ⊥ := by
    rw [eq_bot_iff, ← hres]
    exact Subgroup.commutator_le_inf X₁ X₂
  have hbX₁ : b ∈ X₁ := Subgroup.subset_normalClosure (Subgroup.mem_zpowers b)
  have hcX₂ : c ∈ X₂ := Subgroup.subset_normalClosure (Subgroup.mem_zpowers c)
  have hX₂le : X₂ ≤ Cen b := by
    intro x hx
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hbX₁
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp this x hx)
  have hX₂1 : X₂ ≠ ⊥ := by
    intro h1
    rw [h1] at hcX₂
    exact h.c_ne_one (Subgroup.mem_bot.mp hcX₂)
  obtain ⟨M, hMn, hM1, hMX, hMmin⟩ := exists_minimal_normal_le hX₂1
  haveI := hMn
  haveI hMmin' : CFSG.IsMinimalNormal M := ⟨fun Y hY hYM => hMmin Y hY hYM⟩
  haveI := h.isSolvable_cen_b
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (hMX.trans hX₂le))
  obtain ⟨p, hp, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  haveI : Fact p.Prime := ⟨hp⟩
  have hMp : IsPGroup p ↥M := IsElementaryAbelian.isPGroup p M
  by_cases hp3 : p = 3
  · subst hp3
    exact h.nor_top_of_normal_three_group hOpp hM1 hMp
  · exfalso
    obtain ⟨n, hn⟩ := hMp.exists_card_eq
    have hcop : Nat.Coprime 3 (Nat.card M) := by
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    have hle : M ≤ CFSG.pPrimeCore 3 G := le_sSup ⟨hMn, hcop⟩
    rw [hO] at hle
    exact hM1 (le_bot_iff.mp hle)

end CFSG.RankThree.PartTwo.Sec21.FF81
