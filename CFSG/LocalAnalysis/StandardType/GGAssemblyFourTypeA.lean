module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix SpecialLinear

@[expose] def GGTypeACompatFarExGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))

theorem ggTypeAEndBlockLExGenInput_of_compatFarExGen (h : GGTypeACompatFarExGenInput) :
    GGTypeAEndBlockLExGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, -, hφ₁, hk₁, -, -, hJ, -, -⟩ := h G p B Bs x L D J n f y K hN
  exact ⟨φ₁, hφ₁, hk₁, hJ⟩

theorem ggTypeAEndBlockKGenInput_of_compatFarExGen (h : GGTypeACompatFarExGenInput) :
    GGTypeAEndBlockKGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, φ₂, -, -, hφ₂, hk₂, hJ, hc, -⟩ := h G p B Bs x L D J n f y K hN
  exact ⟨φ₂, hφ₂, hk₂, by rw [← hc]; exact hJ⟩

theorem ggTypeAFarCommuteGenInput_of_compatFarExGen (h : GGTypeACompatFarExGenInput) :
    GGTypeAFarCommuteGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN ψ₁ ψ₂ hψL hl₁ hψK hl₂ hψJ hc' i j hi hj
  obtain ⟨-, -, -, -, hmod, -, hn, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ₁, φ₂, hφL, hk₁, hφK, hk₂, hφJ, hc, hfar⟩ := h G p B Bs x L D J n f y K hN
  have h0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h1 : n - 1 < n := Nat.sub_lt h0 Nat.one_pos
  rw [show i = ⟨0, h0⟩ from Fin.ext hi, show j = ⟨n - 1, h1⟩ from Fin.ext (by simp only; omega)]
  exact slCompat_far_of_far h2 hn hk₁ hk₂ hl₁ hl₂ (hφL.trans hψL.symm) (hφK.trans hψK.symm) hc hc'
    (hψJ.trans hφJ.symm) (hfar _ _ rfl (by simp only; omega))

theorem ggTypeACompatFarExGenInput_of_blocks (hA : GGTypeAEndBlockLExGenInput)
    (hB : GGTypeAEndBlockKGenInput) (hC : GGTypeAFarCommuteGenInput) :
    GGTypeACompatFarExGenInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨-, -, -, -, -, -, hn, -⟩ := id hN
  obtain ⟨φ₁, hφL, hk₁, hJ₁⟩ := hA G p B Bs x L D J n f y K hN
  obtain ⟨φ₂₀, hφK, hk₂, hJ₂⟩ := hB G p B Bs x L D J n f y K hN
  obtain ⟨φ₂, hφK', hk₂', hc⟩ := exists_slCompat_lift hn hk₁ hk₂ (hJ₁.trans hJ₂.symm)
  rw [hφK] at hφK'
  exact ⟨φ₁, φ₂, hφL, hk₁, hφK', hk₂', hJ₁, hc,
    hC G p B Bs x L D J n f y K hN φ₁ φ₂ hφL hk₁ hφK' hk₂' hJ₁ hc⟩

theorem ggTypeACompatFarExGenInput_iff_blocks :
    GGTypeACompatFarExGenInput ↔
      GGTypeAEndBlockLExGenInput ∧ GGTypeAEndBlockKGenInput ∧ GGTypeAFarCommuteGenInput :=
  ⟨fun h => ⟨ggTypeAEndBlockLExGenInput_of_compatFarExGen h,
      ggTypeAEndBlockKGenInput_of_compatFarExGen h, ggTypeAFarCommuteGenInput_of_compatFarExGen h⟩,
    fun h => ggTypeACompatFarExGenInput_of_blocks h.1 h.2.1 h.2.2⟩

theorem ggTypeACompatFarExInput_of_gen (h : GGTypeACompatFarExGenInput) :
    GGTypeACompatFarExInput :=
  fun G _ _ p B Bs x L D J n f y K hN => h G p B Bs x L D J n f y K hN.toNbrCfg

theorem ggTypeAJoinEndNodeInput_of_compatFarExGen (h : GGTypeACompatFarExGenInput) :
    GGTypeAJoinEndNodeInput :=
  ggTypeAJoinEndNodeInput_of_blocks (ggTypeAEndBlockLExGenInput_of_compatFarExGen h)
    (ggTypeAEndBlockKGenInput_of_compatFarExGen h) (ggTypeAFarCommuteGenInput_of_compatFarExGen h)

end CFSG.StandardType
