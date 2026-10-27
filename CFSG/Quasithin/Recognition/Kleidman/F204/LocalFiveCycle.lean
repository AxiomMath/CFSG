module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalBall

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_nbr_not_fixed (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {e : G} (he : e ∈ stab δ) (heQ : e ∉ Qv δ) (he5 : e ^ 5 ∈ Qv δ) :
    ∃ u ∈ nbrs δ, e ∉ stab u := by
  by_contra hcon
  have hcon' : ∀ u ∈ nbrs δ, e ∈ stab u := fun u hu => by
    by_contra hn; exact hcon ⟨u, hu, hn⟩
  have hball : e ∈ ballStab 1 δ := by
    rw [mem_ballStab]
    intro ε hε
    rcases (dist_le_one_iff rfl).mp hε with rfl | hadj
    · exact he
    · exact hcon' ε hadj
  obtain ⟨E, hEst, hE3, hEQ, hEeq⟩ := ballStab_one_false F hδ
  rw [hEeq] at hball
  have hNE : E ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    hEst.trans (le_normalizer_pCoreOf 2 (stab δ))
  obtain ⟨q, hq, d, hd, hqd⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNE).mp
    (show e ∈ Qv δ ⊔ E from hball)
  have hd3 : d ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥E) (x := ⟨d, hd⟩)
    rw [hE3] at this
    simpa using congrArg Subtype.val this
  have hnorm : ((Qv δ).subgroupOf (stab δ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreOf 2 (stab δ))
  let π := QuotientGroup.mk' ((Qv δ).subgroupOf (stab δ))
  have hqst : q ∈ stab δ := pCoreOf_le 2 _ hq
  have hdst : d ∈ stab δ := hEst hd
  let e' : ↥(stab δ) := ⟨e, he⟩
  have hπq : π ⟨q, hqst⟩ = 1 := by
    show QuotientGroup.mk' _ _ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hq
  have h1 : π e' = π ⟨d, hdst⟩ := by
    have : e' = ⟨q, hqst⟩ * ⟨d, hdst⟩ := Subtype.ext hqd
    rw [this, map_mul, hπq, one_mul]
  have h3 : π e' ^ 3 = 1 := by
    rw [h1, ← map_pow]
    have : (⟨d, hdst⟩ : ↥(stab δ)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have h5 : π e' ^ 5 = 1 := by
    rw [← map_pow]
    show QuotientGroup.mk' _ _ = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact he5
  have h1' : π e' = 1 := by
    have : π e' = ((π e' ^ 3) ^ 2) * (π e' ^ 5)⁻¹ := by group
    rw [h3, h5] at this; simpa using this
  apply heQ
  have : e' ∈ ((Qv δ).subgroupOf (stab δ)) := by
    exact (QuotientGroup.eq_one_iff e').mp h1'
  exact this

theorem exists_zpow_smul_nbr (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {e : G} (he : e ∈ stab δ) (heQ : e ∉ Qv δ) (he5 : e ^ 5 ∈ Qv δ)
    {u₁ u₂ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (h₁ : u₁ ∈ nbrs δ) (h₂ : u₂ ∈ nbrs δ) :
    ∃ g : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S), (g : G) ∈ Subgroup.zpowers e ∧ g • u₁ = u₂ := by
  have hA := Amal.of_frame F
  obtain ⟨hG0, hfix⟩ := mem_stab.mp he
  set tg : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨e, hG0⟩ with htg
  have hpres : ∀ (k : ℕ) (x : Geo (P1 L1 L2 S) (P2 L1 L2 S)), x ∈ nbrs δ → (tg ^ k) • x ∈ nbrs δ := by
    intro k x hx
    have hδk : (tg ^ k) • δ = δ := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hfix, ih]
    have := (smul_adj (tg ^ k)).mpr hx
    rwa [hδk] at this
  have hmemz : ∀ k : ℕ, ((tg ^ k : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S)) : G) ∈ Subgroup.zpowers e := by
    intro k
    rw [Subgroup.coe_pow]
    exact ⟨k, by simp [htg]⟩
  have h5fix : ∀ x ∈ nbrs δ, (tg ^ 5) • x = x := by
    intro x hx
    apply smul_eq_of_mem_stab
    rw [Subgroup.coe_pow]
    exact hA.Qv_le_stab_of_mem_nbrs hx he5
  obtain ⟨u, hu, hue⟩ := exists_nbr_not_fixed F hδ he heQ he5
  have hne : ∀ k : ℕ, 0 < k → k < 5 → (tg ^ k) • u ≠ u := by
    intro k hk0 hk5 hfixk
    apply hue
    have hmexists : ∃ m : ℕ, k * m % 5 = 1 := by
      interval_cases k
      · exact ⟨1, by norm_num⟩
      · exact ⟨3, by norm_num⟩
      · exact ⟨2, by norm_num⟩
      · exact ⟨4, by norm_num⟩
    obtain ⟨m, hm⟩ := hmexists
    have hpowfix : ∀ n : ℕ, (tg ^ (k * n)) • u = u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.mul_succ, pow_add, mul_smul, hfixk, ih]
    obtain ⟨t, ht⟩ : ∃ t, k * m = 1 + 5 * t := ⟨k * m / 5, by omega⟩
    have hexp : tg ^ (k * m) = tg * (tg ^ 5) ^ t := by
      rw [ht, pow_add, pow_one, pow_mul]
    have h5t : ∀ n : ℕ, ((tg ^ 5) ^ n) • u = u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, h5fix u hu, ih]
    have h1 := hpowfix m
    rw [hexp, mul_smul, h5t t] at h1
    exact mem_stab_of_smul_eq (g := tg) h1
  let f : Fin 5 → ↥(nbrs δ) := fun i => ⟨(tg ^ (i : ℕ)) • u, hpres i u hu⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne'
    have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hne' (Fin.ext h)
    have key : ∀ i j : ℕ, i < j → j < 5 → (tg ^ j) • u = (tg ^ i) • u → False := by
      intro i j hlt hj h
      apply hne (j - i) (by omega) (by omega)
      have hj' : tg ^ j = tg ^ i * tg ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [hj', mul_smul] at h
      exact MulAction.injective (tg ^ i) h
    have hval : (tg ^ (i : ℕ)) • u = (tg ^ (j : ℕ)) • u := congrArg Subtype.val hij
    rcases Nat.lt_or_gt_of_ne hij' with hlt | hlt
    · exact key i j hlt j.isLt hval.symm
    · exact key j i hlt i.isLt hval
  have hcard : Nat.card ↥(nbrs δ) ≤ Nat.card (Fin 5) := by
    rw [hA.card_nbrs δ]; simp
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨i, hi⟩ := hbij.2 ⟨u₁, h₁⟩
  obtain ⟨j, hj⟩ := hbij.2 ⟨u₂, h₂⟩
  have hi' : (tg ^ (i : ℕ)) • u = u₁ := congrArg Subtype.val hi
  have hj' : (tg ^ (j : ℕ)) • u = u₂ := congrArg Subtype.val hj
  refine ⟨tg ^ ((j : ℕ) + (5 - (i : ℕ))), hmemz _, ?_⟩
  rw [← hi', ← mul_smul, ← pow_add]
  have : (j : ℕ) + (5 - (i : ℕ)) + (i : ℕ) = j + 5 := by omega
  rw [this, pow_add, mul_smul, h5fix u hu, hj']

end CFSG.Quasithin.Kleidman.F204
