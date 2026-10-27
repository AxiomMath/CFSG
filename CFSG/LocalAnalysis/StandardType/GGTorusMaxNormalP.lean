module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.FrameRoute

private theorem tmNormP_normal_pgroup_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hQp : IsPGroup p Q)
    (P : Sylow p G) (hPH : (P : Subgroup G) ≤ H) : Q ≤ (P : Subgroup G) := by
  have hQnorm : (Q.subgroupOf H).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQn (g : G) g.2 (n : G) hn
  have hQp' : IsPGroup p (Q.subgroupOf H) :=
    IsPGroup.of_injective hQp (Q.subgroupOfEquivOfLe hQH).toMonoidHom
      (Q.subgroupOfEquivOfLe hQH).injective
  haveI := hQnorm
  have hle : Q.subgroupOf H ≤ (P.subtype hPH : Subgroup H) :=
    IsPGroup.le_sylow_of_normal hQp' (P.subtype hPH)
  have hle' : Q.subgroupOf H ≤ (P : Subgroup G).subgroupOf H := by
    simpa only [Sylow.coe_subtype] using hle
  intro q hq
  have hmem : (⟨q, hQH hq⟩ : H) ∈ Q.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]; exact hq
  have hmem' := hle' hmem
  rwa [Subgroup.mem_subgroupOf] at hmem'

theorem tmNormP_overgroup_le_normalizer {L : Type*} [Group L] [Finite L] (p : ℕ) [Fact p.Prime]
    (E : Subgroup L) (hEp : IsPGroup p E) (hE0 : E ≠ ⊥)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set L), (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hirr : ∀ F : Subgroup L, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set L), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (hsyl : ∃ P : Sylow p L, (P : Subgroup L) ≤ Subgroup.normalizer (E : Set L))
    (H Q : Subgroup L) (hMH : Subgroup.normalizer (E : Set L) ≤ H) (hQH : Q ≤ H)
    (hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hQp : IsPGroup p Q) (hQ0 : Q ≠ ⊥) :
    H ≤ Subgroup.normalizer (E : Set L) := by
  obtain ⟨P, hPM⟩ := hsyl
  have hPH : (P : Subgroup L) ≤ H := le_trans hPM hMH
  have hQM : Q ≤ Subgroup.normalizer (E : Set L) :=
    le_trans (tmNormP_normal_pgroup_le_sylow hQH hQn hQp P hPH) hPM
  have hMQ : ∀ m ∈ Subgroup.normalizer (E : Set L), ∀ q ∈ Q, m * q * m⁻¹ ∈ Q :=
    fun m hm q hq => hQn m (hMH hm) q hq
  letI : MulAction Q E := MulAction.compHom E (Subgroup.inclusion hQM)
  have hdvd : p ∣ Nat.card E := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hE0 ((Subgroup.card_eq_one).mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self p hn0
  have hfixed : (1 : E) ∈ MulAction.fixedPoints Q E := by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Subtype.ext
    show (((q • (1 : E)) : E) : L) = (((1 : E)) : L)
    rw [show (((q • (1 : E)) : E) : L) = (q : L) * ((1 : E) : L) * (q : L)⁻¹ from rfl]
    simp
  obtain ⟨b, hb, hbne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hQp E hdvd hfixed
  let F : Subgroup L := E ⊓ Subgroup.centralizer (Q : Set L)
  have hFE : F ≤ E := inf_le_left
  have hbF : (b : L) ∈ F := by
    refine Subgroup.mem_inf.mpr ⟨b.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hfix : (⟨h, hh⟩ : Q) • b = b := (MulAction.mem_fixedPoints.mp hb) ⟨h, hh⟩
    have h1 : h * (b : L) * h⁻¹ = (b : L) := by
      have hval := congrArg Subtype.val hfix
      rwa [show ((((⟨h, hh⟩ : Q) • b : E) : L)) = h * (b : L) * h⁻¹ from rfl] at hval
    have h2 : h * (b : L) = (b : L) * h := by
      have := congrArg (· * h) h1
      simpa using this
    exact h2
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hb1 : (b : L) = 1 := by
      have : (b : L) ∈ (⊥ : Subgroup L) := by rw [← hbot]; exact hbF
      simpa using this
    exact hbne (Subtype.ext (by simpa using hb1)).symm
  have hFinv : ∀ g ∈ Subgroup.normalizer (E : Set L), ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
    intro g hg f hf
    rw [Subgroup.mem_inf] at hf ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg f).mp hf.1
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hgq : g⁻¹ * q * g ∈ Q := by
        simpa using hMQ g⁻¹ (Subgroup.inv_mem _ hg) q hq
      have hfc : (g⁻¹ * q * g) * f = f * (g⁻¹ * q * g) :=
        (Subgroup.mem_centralizer_iff.mp hf.2) (g⁻¹ * q * g) hgq
      calc q * (g * f * g⁻¹) = g * (g⁻¹ * q * g) * f * g⁻¹ := by group
        _ = g * ((g⁻¹ * q * g) * f) * g⁻¹ := by group
        _ = g * (f * (g⁻¹ * q * g)) * g⁻¹ := by rw [hfc]
        _ = (g * f * g⁻¹) * q := by group
  rcases hirr F hFE hFinv with hFbot | hFEq
  · exact absurd hFbot hFne
  · have hEcent : E ≤ Subgroup.centralizer (Q : Set L) := by
      intro e he
      have : e ∈ F := by rw [hFEq]; exact he
      exact (Subgroup.mem_inf.mp this).2
    have hQleE : Q ≤ E := by
      intro q hq
      refine hcent q (hQM hq) ?_
      intro e he
      exact (Subgroup.mem_centralizer_iff.mp (hEcent he)) q hq
    have hQE : Q = E := by
      rcases hirr Q hQleE (fun g hg f hf => hMQ g hg f hf) with h | h
      · exact absurd h hQ0
      · exact h
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxE
      simpa [hQE] using hQn h hh x (by rw [hQE]; exact hxE)
    · intro hx
      have hx' : h⁻¹ * (h * x * h⁻¹) * h ∈ Q :=
        by
          simpa using hQn h⁻¹ (H.inv_mem hh) (h * x * h⁻¹) (by rw [hQE]; exact hx)
      have hxQ : x ∈ Q := by
        convert hx' using 1
        group
      exact hQE.le hxQ

end CFSG.StandardType.FrameRoute

end
