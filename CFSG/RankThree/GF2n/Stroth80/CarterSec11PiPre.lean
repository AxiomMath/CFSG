module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
  {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Z_le_Q_of_ctx (hc : Ctx M Q Z B) : Z ≤ Q := by
  rw [hc.hyp.hZ, cen_eq]
  exact inf_le_left

theorem piPre_cmComm_eq_sup_comm [Finite K]
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) :
    piPre M₀ (cmComm M Q Z B K γ M₀ φ) = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by
  have hZQ : Z ≤ Q := Z_le_Q_of_ctx hc
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxV⟩ := hx
    obtain ⟨y, hy, hπy⟩ := (mem_cmComm_iff hc hD φ hφπ (M₀.π x)).mp hxV
    have hyQ : y ∈ Q := commutator_le_Q hc hy
    have hy' : y⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hyQ) hxQ
    have hzero : M₀.π (y⁻¹ * x) = 0 := by
      rw [M₀.π_mul y⁻¹ (Q.inv_mem hyQ) x hxQ, pi_inv hyQ, hπy, neg_add_cancel]
    have hx' : x = y * (y⁻¹ * x) := by group
    have h1 : y ∈ (Z : Subgroup G) ⊔ (⁅Q, XbarPre M Q Z B⁆ : Subgroup G) :=
      Subgroup.mem_sup_right hy
    have h2 : y⁻¹ * x ∈ (Z : Subgroup G) ⊔ (⁅Q, XbarPre M Q Z B⁆ : Subgroup G) :=
      Subgroup.mem_sup_left ((M₀.π_ker (y⁻¹ * x) hy').mp hzero)
    rw [hx']
    exact ((Z : Subgroup G) ⊔ (⁅Q, XbarPre M Q Z B⁆ : Subgroup G)).mul_mem h1 h2
  · refine sup_le ?_ ?_
    · intro z hz
      exact ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]
        exact Submodule.zero_mem _⟩
    · intro c hc'
      exact ⟨commutator_le_Q hc hc',
        (mem_cmComm_iff hc hD φ hφπ (M₀.π c)).mpr ⟨c, hc', rfl⟩⟩

theorem Ctx.conjSubgroup_piPre_eq (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {V : Submodule K M₀.E}
    (hV : ∀ (s : ↥(XbarH M Q Z B)) (w : M₀.E), w ∈ V → φ s w ∈ V)
    (s : ↥(XbarPre M Q Z B)) :
    conjSubgroup (s : G) (piPre M₀ V) = piPre M₀ V := by
  have hstep : ∀ t : ↥(XbarPre M Q Z B), ∀ y : G, y ∈ piPre M₀ V →
      (t : G) * y * (t : G)⁻¹ ∈ piPre M₀ V := by
    intro t y hy
    obtain ⟨hyQ, hyV⟩ := hy
    have htH0 : (t : G) ∈ H0 M Z := XbarPre_le_H0 hc t.2
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (hc.hyp.Q_normal.2 (XbarPre_le_M hc t.2)) y).mp hyQ
    · have hmem : (⟨(t : G), htH0⟩ : ↥(H0 M Z)) ∈ XbarH M Q Z B :=
        (mem_XbarH_iff hc _).mpr t.2
      rw [hφπ ⟨(t : G), htH0⟩ y hyQ]
      exact hV ⟨⟨(t : G), htH0⟩, hmem⟩ (M₀.π y) hyV
  ext x
  constructor
  · intro hx
    rw [mem_conjSubgroup] at hx
    have h := hstep s (s⁻¹ * x * s) hx
    simpa [mul_assoc] using h
  · intro hx
    rw [mem_conjSubgroup]
    have h := hstep s⁻¹ x hx
    simpa [mul_assoc] using h

theorem piPre_top : piPre M₀ (⊤ : Submodule K M₀.E) = Q := by
  ext x
  constructor
  · rintro ⟨hxQ, -⟩
    exact hxQ
  · intro hx
    exact ⟨hx, Submodule.mem_top⟩

end CFSG.RankThree.GF2n.Stroth80
