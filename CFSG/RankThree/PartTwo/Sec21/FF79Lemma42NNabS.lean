module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NNabR
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG.Holt.General.AltRecPrim
open scoped commutatorElement
open CFSG.RankThree.PartTwo.KFacts (KPSz commutator_le_inner_of_not_three_dvd)

variable {Γ : Type} [Group Γ] [Finite Γ] {Q L : Subgroup Γ} {b : Γ}

theorem NHyp.perfect (h : NHyp Q L b) : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
  haveI := h.isSimple
  rcases (Subgroup.commutator_normal (⊤ : Subgroup L) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨x, y, hxy⟩ := h.nonab_L
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hxy hmem
  · exact ht

theorem simple_case (hSz : KPSz) (h : NHyp Q L b) (hQ : Q.Normal)
    [IsSimpleGroup Q] (hnab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) :
    Q ≤ Subgroup.centralizer (L : Set Γ) := by
  have hnab' : ∃ a c : Q, a * c ≠ c * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun e => hxy (congrArg Subtype.val e)⟩
  have hcat : CFSG.Assembly.InCatalog Q :=
    h.kgroup.catalogue_self CFSG.Assembly.inCatalog_isoInvariant hnab'
  have h3 : ¬ 3 ∣ Nat.card Q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h.coprime
  have hcomm := commutator_le_inner_of_not_three_dvd hSz hnab' hcat h3
  let ρ : L →* MulAut Q := (MulAut.conjNormal : Γ →* MulAut Q).comp L.subtype
  have hρb : ρ ⟨b, h.mem⟩ ∈ commutator (MulAut Q) := by
    have h1 : (⟨b, h.mem⟩ : L) ∈ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ := by
      rw [h.perfect]; exact Subgroup.mem_top _
    have h2 : ρ ⟨b, h.mem⟩ ∈ Subgroup.map ρ ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ :=
      Subgroup.mem_map_of_mem ρ h1
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono le_top le_top h2
  obtain ⟨q, hq⟩ := hcomm hρb
  have hbq : ∀ x : Q, (q : Γ) * x * (q : Γ)⁻¹ = b * x * b⁻¹ := by
    intro x
    have := congrArg (fun φ : MulAut Q => (φ x : Γ)) hq
    simpa [ρ, MulAut.conjNormal_apply] using this
  have hb1 : b ≠ 1 := by
    intro e
    have := h.order
    rw [e, orderOf_one] at this
    omega
  set c : Γ := (q : Γ)⁻¹ * b with hc
  have hcQ : ∀ x ∈ Q, c * x = x * c := by
    intro x hx
    have := hbq ⟨x, hx⟩
    simp only [hc]
    calc (q : Γ)⁻¹ * b * x = (q : Γ)⁻¹ * (b * x * b⁻¹) * b := by group
      _ = (q : Γ)⁻¹ * ((q : Γ) * x * (q : Γ)⁻¹) * b := by rw [← this]
      _ = x * ((q : Γ)⁻¹ * b) := by group
  by_cases hq1 : q = 1
  · have hbQ : ∀ x ∈ Q, b * x = x * b := by
      intro x hx
      have := hcQ x hx
      rw [hc, hq1] at this
      simpa using this
    exact h.centralizes_of_ne_one h.mem hb1 hbQ
  · exfalso
    have hbcq : b = (q : Γ) * c := by simp [hc]
    have hcomm' : Commute (q : Γ) c := (hcQ q q.2).symm
    have hb3 : b ^ 3 = 1 := h.order ▸ pow_orderOf_eq_one b
    have hq3 : (q : Γ) ^ 3 * c ^ 3 = 1 := by
      rw [← hcomm'.mul_pow, ← hbcq]; exact hb3
    have hq3Q : ((q ^ 3 : Q) : Γ) = ((c ^ 3)⁻¹ : Γ) := by
      rw [Subgroup.coe_pow]
      exact eq_inv_of_mul_eq_one_left hq3
    have hcentral : q ^ 3 ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hq3Q]
      have hc3 : ((c ^ 3 : Γ)) * (g : Γ) = (g : Γ) * c ^ 3 := by
        have hcg : Commute c (g : Γ) := hcQ g g.2
        exact (hcg.pow_left 3).eq
      calc (g : Γ) * (c ^ 3)⁻¹ = (c ^ 3)⁻¹ * (c ^ 3 * g) * (c ^ 3)⁻¹ := by group
        _ = (c ^ 3)⁻¹ * (g * c ^ 3) * (c ^ 3)⁻¹ := by rw [hc3]
        _ = (c ^ 3)⁻¹ * g := by group
    have hZ : Subgroup.center Q = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, c', hac⟩ := hnab'
        have : a ∈ Subgroup.center Q := h0 ▸ Subgroup.mem_top a
        exact hac (Subgroup.mem_center_iff.mp this c').symm
    rw [hZ, Subgroup.mem_bot] at hcentral
    have hord : orderOf q = 3 := by
      have hd : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hcentral
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hq1
      · exact h1
    exact h3 (hord ▸ orderOf_dvd_natCard q)

theorem nBase_nab_normal (hSz : KPSz) (h : NHyp Q L b)
    (hQ : Q.Normal) (hnab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x) (hmin : NLeast Q L) :
    Q ≤ Subgroup.centralizer (L : Set Γ) := by
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    rw [Subgroup.mem_bot] at hx hy
    subst hx; subst hy
    exact hxy (by simp)
  have hmin' : ∀ M : Subgroup Γ, M.Normal → M ≤ Q → M = ⊥ ∨ M = Q := fun M hM hMQ =>
    hmin M hMQ (fun q _ r hr => hM.conj_mem r hr q)
      (fun l _ r hr => hM.conj_mem r hr l)
  obtain ⟨F⟩ := nonempty_simpleFactors hQ hQ1 hmin' hnab
  let j : Fin F.r := ⟨0, F.one_le⟩
  have hall : ∀ l ∈ L, Cj F l j j := by
    by_cases hb : Cj F b j j
    · exact fixed_factor h hQ F j hb
    · exact (moved_factor_false h hQ F j hb).elim
  have hSQ : F.S j = Q := by
    rcases hmin (F.S j) (F.le j) (fun q hq r hr => F.conj_mem ⟨q, hq⟩ hr)
      (fun l hl r hr => (hall l hl r).mp hr) with h0 | h0
    · exfalso
      obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem F j
      rw [h0, Subgroup.mem_bot] at hx
      exact hx1 hx
    · exact h0
  haveI : IsSimpleGroup Q := hSQ ▸ F.isSimpleGroup j
  exact simple_case hSz h hQ hnab

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
