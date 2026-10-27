module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocInter
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocSubs

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

section Case1

variable (hM : MatFacts)
include hM

theorem V0_le_Eg {x : J} (hx : x ∈ V0) : x ∈ Eg uJ 11 := by
  obtain ⟨c, -, rfl⟩ := (mem_V0_iff hM).1 hx
  exact eta_mem_Eg 11 le_rfl c

theorem normalizer_V0_of {N : Subgroup J}
    (h1 : ∀ n ∈ N, n ∉ Hj → ∀ x, x ∈ Ig n ↔ x ∈ V0)
    (h2 : ∀ n ∈ N, n ∈ Hj → ∀ x ∈ V0, n * x * n⁻¹ ∈ V0) :
    N ≤ Subgroup.normalizer (V0 : Set J) := by
  have key : ∀ m ∈ N, ∀ x ∈ V0, m * x * m⁻¹ ∈ V0 := by
    intro m hm x hx
    by_cases hmH : m ∈ Hj
    · exact h2 m hm hmH x hx
    · have hmH' : m⁻¹ ∉ Hj := fun h => hmH (by simpa using Hj.inv_mem h)
      have hxI := (h1 m⁻¹ (N.inv_mem hm) hmH' x).2 hx
      have hxE : m * x * m⁻¹ ∈ Eg uJ 11 := by
        have := hxI.2
        rwa [inv_inv] at this
      refine (h1 m hm hmH _).1 ⟨hxE, ?_⟩
      have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
      rw [e]
      exact V0_le_Eg hM hx
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key n hn x hx
  · intro hx
    have := key n⁻¹ (N.inv_mem hn) _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this

omit hM in
theorem V0L_lt {c : ℕ} (hc : c ∈ V0L) : c < 2048 := by
  simp only [V0L, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

omit hM in
theorem inv_mem_normalizer_conj {A : Subgroup J} {n : J} (hn : n ∈ Subgroup.normalizer (A : Set J))
    {y : J} (hy : y ∈ A) : n⁻¹ * y * n ∈ A := by
  have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set J)).inv_mem hn) y).1 hy
  rwa [inv_inv] at this

omit hM in
theorem case1
    (hF : J4Facts) {A : Subgroup J} (hAE : A ≤ Eg uJ 11)
    (hn : ∀ g ∈ P0, ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set J) ≤ Hj ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.centralizer ({z0} : Set J) ∨
      Subgroup.normalizer (A : Set J) ≤ Subgroup.normalizer (V0 : Set J) := by
  have hM := hF.mat
  obtain ⟨B, hBs, hB⟩ := subs_complete hF hAE hn
  have hnd : B.Nodup := nodup_of_pairwise_lt (subs_prop hBs).2.1
  have hcard : Nat.card A = B.length := MaskList.card hM hAE hB hnd
  by_cases hsmall : B.length ≤ 2
  · rcases small_sub hBs hsmall with hB0 | hB0
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hAE hx)
      have hcB : c ∈ B := (hB c).2 ⟨hc, hx⟩
      rw [hB0] at hcB
      have : c = 0 := by simpa using hcB
      subst this
      rw [eta_zero]
      exact Subgroup.one_mem _
    · right; left
      intro n hn'
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz0 : z0 ∈ A := ((hB 1131).1 (by rw [hB0]; simp [z0L])).2
      have h1 : n * z0 * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hn' z0).1 hz0
      obtain ⟨c, hc, hcz⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hAE h1)
      have hcB : c ∈ B := (hB c).2 ⟨hc, by rw [← hcz]; exact h1⟩
      rw [hB0] at hcB
      simp only [z0L, List.mem_cons, List.not_mem_nil, or_false] at hcB
      rcases hcB with rfl | rfl
      · exfalso
        rw [eta_zero] at hcz
        have h2 : z0 = 1 := by
          have e : z0 = n⁻¹ * (n * z0 * n⁻¹) * n := by group
          rw [e, hcz]
          group
        have h3 : eta uJ 11 1131 = eta uJ 11 0 := by rw [eta_zero]; exact h2
        have := eta_inj' hM (by norm_num) (by norm_num) h3
        omega
      · calc n * z0 = (n * z0 * n⁻¹) * n := by group
          _ = z0 * n := by rw [hcz]; rfl
  · have h3 : 3 ≤ B.length := by omega
    by_cases hex : ∃ n ∈ Subgroup.normalizer (A : Set J), n ∉ Hj
    · right; right
      have hAI : ∀ n ∈ Subgroup.normalizer (A : Set J), (A : Set J) ⊆ Ig n := by
        intro n hn' y hy
        exact ⟨hAE hy, hAE (inv_mem_normalizer_conj hn' hy)⟩
      have hIg : ∀ n ∈ Subgroup.normalizer (A : Set J), n ∉ Hj → ∀ x, x ∈ Ig n ↔ x ∈ V0 := by
        intro n hn' hnH x
        rcases inter_trio hF hnH with hle | ⟨W, hW, hWc⟩
        · exfalso
          have h1 : (A : Set J).ncard ≤ 2 :=
            (Set.ncard_le_ncard (hAI n hn') (Set.toFinite _)).trans hle
          rw [← Nat.card_coe_set_eq] at h1
          have h2 : Nat.card ↥(A : Set J) = Nat.card A := rfl
          omega
        · have hBW : ∀ b ∈ B, b ∈ W := by
            intro b hb
            obtain ⟨hlt, hbA⟩ := (hB b).1 hb
            exact (hWc b hlt).1 (hAI n hn' hbA)
          have hWV : W = V0L := above hBs h3 hW hBW
          subst hWV
          constructor
          · intro hx
            obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx.1
            exact (mem_V0_iff hM).2 ⟨c, (hWc c hc).1 hx, rfl⟩
          · intro hx
            obtain ⟨c, hc, rfl⟩ := (mem_V0_iff hM).1 hx
            exact (hWc c (V0L_lt hc)).2 hc
      have hBV : ∀ b ∈ B, b ∈ V0L := by
        obtain ⟨n0, hn0, hn0H⟩ := hex
        intro b hb
        obtain ⟨hlt, hbA⟩ := (hB b).1 hb
        have h1 : eta uJ 11 b ∈ V0 := (hIg n0 hn0 hn0H _).1 (hAI n0 hn0 hbA)
        obtain ⟨c, hc, hcb⟩ := (mem_V0_iff hM).1 h1
        have : b = c := eta_inj' hM hlt (V0L_lt hc) hcb
        rw [this]
        exact hc
      have h2 : ∀ n ∈ Subgroup.normalizer (A : Set J), n ∈ Hj → ∀ x ∈ V0, n * x * n⁻¹ ∈ V0 := by
        intro n hn' hnH x hx
        obtain ⟨c, hc, rfl⟩ := (mem_V0_iff hM).1 hx
        obtain ⟨W', hW'trio, hImg⟩ := (trio_conj hM hnH).1 V0L trio_prop.1
        have hBW' : ∀ b ∈ B, b ∈ W' := by
          intro b hb
          obtain ⟨hlt, hbA⟩ := (hB b).1 hb
          have h1 : n⁻¹ * eta uJ 11 b * n ∈ A := inv_mem_normalizer_conj hn' hbA
          obtain ⟨b', hb'lt, hb'e⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hAE h1)
          have hb'B : b' ∈ B := (hB b').2 ⟨hb'lt, by rw [← hb'e]; exact h1⟩
          obtain ⟨c', hc', hc'e⟩ := hImg.1 b' (hBV b' hb'B)
          have e : n * eta uJ 11 b' * n⁻¹ = eta uJ 11 b := by rw [← hb'e]; group
          rw [e] at hc'e
          have : b = c' := eta_inj' hM hlt ((trio_prop.2 W' hW'trio).2.1 c' hc') hc'e
          rw [this]
          exact hc'
        have hW' : W' = V0L := above hBs h3 hW'trio hBW'
        subst hW'
        obtain ⟨c', hc', hc'e⟩ := hImg.1 c hc
        exact (mem_V0_iff hM).2 ⟨c', hc', hc'e⟩
      exact normalizer_V0_of hM hIg h2
    · left
      intro n hn'
      by_contra hnH
      exact hex ⟨n, hn', hnH⟩

end Case1

end CFSG.Quasithin.J4Loc
