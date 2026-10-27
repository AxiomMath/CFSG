module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zda

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace UC22pwtElem

variable {X Γ : Type} [Group X] [Group Γ] {ρ : Γ →* MulAut X} {τ : Γ}
  {U A₁ A₂ : Subgroup X} {C : UC22pwtCtx ρ τ U A₁ A₂} {h w₁ : X} {m a b : ℕ} {α : Set ℕ}

theorem full (El : UC22pwtElem C h w₁ m a b α) : UC22pwtElem C h w₁ m 1 m ∅ where
  h_mem := El.h_mem
  ord := El.ord
  sqf := El.sqf
  odd := El.odd
  ab := one_mul m
  cop := Nat.coprime_one_left m
  pr := fun p hp _ => iff_of_false (by simp) hp.not_dvd_one
  ex := El.ex
  Z := El.Z
  hnorm := El.hnorm
  hinv := El.hinv
  halpha := by
    intro g hg
    have hm : h ^ m = 1 := by
      rw [← El.ord]
      exact pow_orderOf_eq_one h
    simpa [hm] using (U ⊓ A₁).one_mem
  w_mem := El.w_mem
  w_sq := El.w_sq
  w_inv := El.w_inv
  w_gen := El.w_gen
  nc := El.nc

end UC22pwtElem

namespace UC22pwtPair

variable {X : Type} [Group X] [Finite X] {h h' : X} {m a b : ℕ} {α : Set ℕ}

private theorem orderOf_pow_div (P : UC22pwtPair h h' m a b α) {p : ℕ} (hpm : p ∣ m) :
    orderOf (h ^ (m / p)) = p ∧ orderOf (h' ^ (m / p)) = p := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero P.odd
  refine ⟨?_, ?_⟩
  · rw [← P.ord]
    exact orderOf_pow_orderOf_div (by rw [P.ord]; exact hm0) (by rw [P.ord]; exact hpm)
  · rw [← P.ord']
    exact orderOf_pow_orderOf_div (by rw [P.ord']; exact hm0) (by rw [P.ord']; exact hpm)

private theorem not_isCyclic_pow_div (P : UC22pwtPair h h' m a b α) {p : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) :
    ¬ IsCyclic ↥(Subgroup.zpowers (h ^ (m / p)) ⊔ Subgroup.zpowers (h' ^ (m / p))) := by
  obtain ⟨hxord, hyord⟩ := orderOf_pow_div P hpm
  intro hcyc
  let Q : Subgroup X := Subgroup.zpowers (h ^ (m / p)) ⊔ Subgroup.zpowers (h' ^ (m / p))
  have hxQ : h ^ (m / p) ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hyQ : h' ^ (m / p) ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  haveI : IsCyclic ↥Q := hcyc
  let Xq : Subgroup ↥Q := Subgroup.zpowers ⟨h ^ (m / p), hxQ⟩
  let Yq : Subgroup ↥Q := Subgroup.zpowers ⟨h' ^ (m / p), hyQ⟩
  have hXq : Nat.card Xq = p := by
    change Nat.card (Subgroup.zpowers (⟨h ^ (m / p), hxQ⟩ : ↥Q)) = p
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    simpa using hxord
  have hYq : Nat.card Yq = p := by
    change Nat.card (Subgroup.zpowers (⟨h' ^ (m / p), hyQ⟩ : ↥Q)) = p
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
    simpa using hyord
  have heq : Xq = Yq := IsCyclic.subgroup_eq_iff_card_eq.mpr (hXq.trans hYq.symm)
  have hyXq : (⟨h' ^ (m / p), hyQ⟩ : ↥Q) ∈ Xq := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hyXq
  have hyx : h' ^ (m / p) ∈ Subgroup.zpowers (h ^ (m / p)) :=
    Subgroup.mem_zpowers_iff.2 ⟨i, by simpa using congrArg Subtype.val hi⟩
  have hyh : h' ^ (m / p) ∈ Subgroup.zpowers h :=
    (Subgroup.zpowers_le.2 (Subgroup.pow_mem (Subgroup.zpowers h) (Subgroup.mem_zpowers h)
      (m / p))) hyx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hyh
  have hdisj : h ^ j = 1 := P.disj j ((m / p : ℕ) : ℤ) (by rw [hj, zpow_natCast])
  have hy1 : h' ^ (m / p) = 1 := by rw [← hj, hdisj]
  exact hp.ne_one (by rw [← hyord, hy1, orderOf_one])

theorem exists_noncyclic (P : UC22pwtPair h h' m a b α) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    ∃ Q : Subgroup X, Q ≤ uc22pwtE h h' 1 m ∧ ¬ IsCyclic ↥Q ∧ ∀ x ∈ Q, x ^ p = 1 := by
  obtain ⟨hxord, hyord⟩ := orderOf_pow_div P hpm
  set x : X := h ^ (m / p) with hx
  set y : X := h' ^ (m / p) with hy
  have hxy : Commute x y := by
    rw [hx, hy]
    exact P.comm.pow_pow (m / p) (m / p)
  have hcomm : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (hxy.zpow_zpow i j).eq
  let Q : Subgroup X := Subgroup.zpowers x ⊔ Subgroup.zpowers y
  have hQE : Q ≤ uc22pwtE h h' 1 m := by
    change Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ uc22pwtE h h' 1 m
    refine sup_le ?_ ?_
    · rw [hx]
      exact Subgroup.zpowers_le.2 (by
        simpa using Subgroup.pow_mem (uc22pwtE h h' 1 m) (uc22pwtE_ha_mem h h' 1 m) (m / p))
    · rw [hy]
      exact Subgroup.zpowers_le.2 (by
        simpa using Subgroup.pow_mem (uc22pwtE h h' 1 m) (uc22pwtE_ha'_mem h h' 1 m) (m / p))
  refine ⟨Q, hQE, ?_, ?_⟩
  · change ¬ IsCyclic ↥(Subgroup.zpowers (h ^ (m / p)) ⊔ Subgroup.zpowers (h' ^ (m / p)))
    exact not_isCyclic_pow_div P hp hpm
  · intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := uc22pwt_exists_mul_of_comm hcomm hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [(hxy.zpow_zpow i j).mul_pow]
    have e1 : (x ^ i) ^ p = 1 := by
      simpa [hxord] using zpow_pow_orderOf (x := x) (i := i)
    have e2 : (y ^ j) ^ p = 1 := by
      simpa [hyord] using zpow_pow_orderOf (x := y) (i := j)
    rw [e1, e2, one_mul]

end UC22pwtPair

theorem uc22pwt_core_full (hR1 : uc22pwCartanRankOne) {X : Type} [Group X] [Finite X] {Γ : Type}
    [Group Γ] (hΓ : IsPGroup 2 Γ) (ρ : Γ →* MulAut X) (τ : Γ) {U A₁ A₂ : Subgroup X}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    (hτ₁ : ∀ x, x ∈ A₁ ↔ ρ τ x ∈ A₂) (hτ₂ : ∀ x, x ∈ A₂ ↔ ρ τ x ∈ A₁)
    (hperm : ∀ g : Γ, ((∀ x, x ∈ A₁ ↔ ρ g x ∈ A₁) ∧ (∀ x, x ∈ A₂ ↔ ρ g x ∈ A₂)) ∨
      ((∀ x, x ∈ A₁ ↔ ρ (τ⁻¹ * g) x ∈ A₁) ∧ (∀ x, x ∈ A₂ ↔ ρ (τ⁻¹ * g) x ∈ A₂)))
    (hUinv : ∀ (g : Γ) (x : X), x ∈ U ↔ ρ g x ∈ U) (hUsplit : U ≤ (U ⊓ A₁) ⊔ (U ⊓ A₂))
    (hUsyl : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ A₁) A₁)
    (hq : CFSG.Open.IsQuasisimple ↥A₁) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz ↥A₁ n ∨ IsL2 ↥A₁ n ∨ IsSU3 ↥A₁ n)
    (hZ : ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → ¬ p ∣ Nat.card (Subgroup.center ↥A₁)) :
    ∃ (E : Subgroup X) (k : ℕ), E ≤ normalizer (U : Set X) ∧ IsMulCommutative ↥E ∧
      Odd (Nat.card E) ∧ Squarefree k ∧ (∀ x ∈ E, x ^ k = 1) ∧ piSet E = etaSet n ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card E → ∃ Q ≤ E, ¬ IsCyclic ↥Q ∧ ∀ x ∈ Q, x ^ p = 1) ∧
      (∀ g : Γ, ∀ x ∈ E, ρ g x ∈ E ⊔ U) ∧
      ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
        normalizer (U : Set X) ⊔ zpowers w = ⊤ := by
  have C : UC22pwtCtx ρ τ U A₁ A₂ := ⟨hcomm, hsup, hτ₁, hτ₂, hperm, hUinv, hUsplit⟩
  obtain ⟨e, m', hm', hnem⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  obtain ⟨h, w₁, m, a, b, El, hpr⟩ :=
    uc22pwt_elem_of_input hR1 hΓ C hUsyl hq hn hsh hZ hm' hnem
  have P := El.full.pair
  refine ⟨uc22pwtE h (ρ τ h) 1 m, m, ?_, P.isMulCommutative_E, P.odd_card_E, El.sqf, ?_, ?_, ?_,
    El.full.invariant, El.full.involution⟩
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h_norm 1)
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ El.h'_norm 1)
    · exact Subgroup.zpowers_le.2
        (mul_mem (Subgroup.pow_mem _ El.h_norm m) (Subgroup.pow_mem _ El.h'_norm m))
  · intro x hx
    exact P.pow_m_of_mem_E hx
  · rw [P.piSet_E]
    ext p
    simp only [etaSet, Set.mem_setOf_eq]
    exact ⟨fun hp => ⟨hp.1, (hpr p hp.1).1 hp.2⟩, fun hp => ⟨hp.1, (hpr p hp.1).2 hp.2⟩⟩
  · intro p hp hpd
    have hpE : p ∈ piSet (uc22pwtE h (ρ τ h) 1 m) := ⟨hp, hpd⟩
    rw [P.piSet_E] at hpE
    exact UC22pwtPair.exists_noncyclic P hp hpE.2

theorem uc22pw_full_two (hR1 : uc22pwCartanRankOne) (hu38 : uc22p20oU38Witness) (D : Data G)
    {L K K₂ : Subgroup G}
    (hL : L ∈ calL D.T D.M) (hK : K ∈ calC L) (hK₂ : K₂ ∈ calC L) (hne : K₂ ≠ K)
    (hLK : L = K ⊔ K₂) {t : G} (htT : t ∈ D.T) (ht : K₂ = uc22p20bCj t K) {n : ℕ} (hn : 2 < n)
    (hsh : IsSz (Bar2 K) n ∨ IsL2 (Bar2 K) n ∨ (n = 3 ∧ IsSU3 (Bar2 K) 3)) :
    ∃ (F : Subgroup (Bar2 L)) (k : ℕ),
      F ≤ normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ∧
      IsMulCommutative ↥F ∧ Odd (Nat.card F) ∧ Squarefree k ∧ (∀ x ∈ F, x ^ k = 1) ∧
      piSet F = etaSet n ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card F → ∃ Q ≤ F, ¬ IsCyclic ↥Q ∧ ∀ x ∈ Q, x ^ p = 1) ∧
      (∀ (s : G) (hs : s ∈ normalizer (L : Set G)), s ∈ D.T → ∀ x ∈ F,
        uc22p20uInd L s hs x ∈ F ⊔ uc22p20iSylowBar D L) ∧
      ∃ w : Bar2 L, w ^ 2 = 1 ∧ (∀ x ∈ F, w * x * w⁻¹ = x⁻¹) ∧
        normalizer ((uc22p20iSylowBar D L : Subgroup (Bar2 L)) : Set (Bar2 L)) ⊔ zpowers w = ⊤ := by
  obtain ⟨C, hUsyl, hq, hsh', hZ⟩ := uc22pw_two_ctx hu38 D hL hK hK₂ hne hLK htT ht hn hsh
  obtain ⟨E, k, hEU, hab, hodd, hsqf, hpow, hpi, hnc, hinv, hw⟩ :=
    uc22pwt_core_full hR1 D.sylowM.isPGroup (uc22pwIndHom L D.T hL.1) ⟨t, htT⟩
      C.comm C.sup C.swap₁ C.swap₂ C.perm C.Uinv C.Usplit hUsyl hq hn hsh' hZ
  refine ⟨E, k, hEU, hab, hodd, hsqf, hpow, hpi, hnc, ?_, hw⟩
  intro s hs hsT x hx
  exact hinv ⟨s, hsT⟩ x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22
