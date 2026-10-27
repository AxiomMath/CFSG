module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClRest
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped MatrixGroups Matrix

namespace WitSpNs

variable {K : Type} [Field K] {n : ℕ}

theorem plane_par (a : Fin n ⊕ Fin n) : plane (par a) = plane a := by
  rcases a with j | j <;> rfl

@[expose] def blockCoords (n d b : ℕ) : Set (Fin n ⊕ Fin n) :=
  {a | b * d ≤ (plane a : ℕ) ∧ (plane a : ℕ) < (b + 1) * d}

theorem parClosed_blockCoords (n d b : ℕ) : ParClosed (blockCoords n d b) := by
  intro a ha
  change b * d ≤ (plane (par a) : ℕ) ∧ (plane (par a) : ℕ) < (b + 1) * d
  rw [plane_par]
  exact ha

@[expose] def blockSwapFun (n d : ℕ) (j : Fin n) : Fin n :=
  if h : (j : ℕ) < d ∧ (j : ℕ) + d < n then ⟨j + d, h.2⟩
  else if h' : d ≤ (j : ℕ) ∧ (j : ℕ) < 2 * d then ⟨j - d, by omega⟩ else j

theorem blockSwapFun_involutive (n d : ℕ) : Function.Involutive (blockSwapFun n d) := by
  intro j
  unfold blockSwapFun
  by_cases h : (j : ℕ) < d ∧ (j : ℕ) + d < n
  · rw [dite_eq_left h, dite_eq_right (by simp only [not_and, not_lt]; omega),
      dite_eq_left (by simp; omega)]
    ext
    simp
  · rw [dite_eq_right h]
    by_cases h' : d ≤ (j : ℕ) ∧ (j : ℕ) < 2 * d
    · rw [dite_eq_left h', dite_eq_left (by simp only; omega)]
      ext
      simp only
      omega
    · rw [dite_eq_right h', dite_eq_right h, dite_eq_right h']

@[expose] def blockSwap (n d : ℕ) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm _ (blockSwapFun_involutive n d)

theorem blockSwap_apply (n d : ℕ) (j : Fin n) : blockSwap n d j = blockSwapFun n d j := rfl

theorem blockSwap_mul_self (n d : ℕ) : blockSwap n d * blockSwap n d = 1 :=
  Equiv.ext fun j => blockSwapFun_involutive n d j

theorem image_blockCoords_zero {d : ℕ} (h2d : 2 * d ≤ n) :
    Sum.map (blockSwap n d) (blockSwap n d) '' blockCoords n d 0 ⊆ blockCoords n d 1 := by
  rintro _ ⟨a, ha, rfl⟩
  have hplane : plane (Sum.map (blockSwap n d) (blockSwap n d) a) = blockSwap n d (plane a) := by
    rcases a with j | j <;> rfl
  change 1 * d ≤ (plane (Sum.map (blockSwap n d) (blockSwap n d) a) : ℕ) ∧
    (plane (Sum.map (blockSwap n d) (blockSwap n d) a) : ℕ) < (1 + 1) * d
  have ha' : (plane a : ℕ) < d := by
    have := ha.2
    simpa using this
  rw [hplane, blockSwap_apply, blockSwapFun, dite_eq_left ⟨ha', by omega⟩]
  simp only
  omega

theorem blockCoords_one_subset_compl (d : ℕ) :
    blockCoords n d 1 ⊆ (blockCoords n d 0)ᶜ := by
  intro a ha h0
  have h1 := ha.1
  have h2 := h0.2
  simp only [zero_add, one_mul] at h1 h2
  omega

theorem permSp_blockSwap_inv (n d : ℕ) :
    (permSp K (blockSwap n d))⁻¹ = permSp K (blockSwap n d) := by
  apply mat_injective
  rw [mat_permSp_inv, mat_permSp]
  have hinv : ∀ x : Fin n ⊕ Fin n,
      Sum.map (blockSwap n d) (blockSwap n d) (Sum.map (blockSwap n d) (blockSwap n d) x) = x := by
    intro x
    rcases x with j | j <;> simp [blockSwap_apply, blockSwapFun_involutive n d j]
  ext a b
  rw [Matrix.transpose_apply, spIncl_apply, spIncl_apply]
  by_cases h : b = Sum.map (blockSwap n d) (blockSwap n d) a
  · rw [ite_eq_left h, ite_eq_left (by rw [h, hinv])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', hinv]))]

theorem commute_blockSwap {d : ℕ} (h2d : 2 * d ≤ n) {X₀ w : StatedSp n K}
    (hX₀ : X₀ ∈ suppGroup (blockCoords n d 0))
    (hw : (permSp K (blockSwap n d))⁻¹ * w ∈
      suppGroup (blockCoords n d 0 ∪ blockCoords n d 1)ᶜ) :
    Commute (X₀ * (permSp K (blockSwap n d) * X₀ * (permSp K (blockSwap n d))⁻¹)) w := by
  set P := permSp K (blockSwap n d) with hP
  have hY : P * X₀ * P⁻¹ ∈ suppGroup (blockCoords n d 1) :=
    suppGroup_mono (image_blockCoords_zero h2d) (conj_permSp_mem_suppGroup _ hX₀)
  have hXY : Commute X₀ (P * X₀ * P⁻¹) :=
    commute_suppGroup_compl hX₀ (suppGroup_mono (blockCoords_one_subset_compl d) hY)
  have hsupp : X₀ * (P * X₀ * P⁻¹) ∈ suppGroup (blockCoords n d 0 ∪ blockCoords n d 1) :=
    Subgroup.mul_mem _ (suppGroup_mono Set.subset_union_left hX₀)
      (suppGroup_mono Set.subset_union_right hY)
  have hPinv : P⁻¹ = P := by rw [hP, permSp_blockSwap_inv]
  have hPP : P * P = 1 := by
    rw [← mul_inv_cancel P, hPinv]
  have hc : P * (X₀ * (P * X₀ * P⁻¹)) * P⁻¹ = X₀ * (P * X₀ * P⁻¹) := by
    calc P * (X₀ * (P * X₀ * P⁻¹)) * P⁻¹ = (P * X₀ * P⁻¹) * ((P * P) * X₀ * (P⁻¹ * P⁻¹)) := by
          group
      _ = (P * X₀ * P⁻¹) * X₀ := by rw [hPP, hPinv, hPP, one_mul, mul_one]
      _ = X₀ * (P * X₀ * P⁻¹) := hXY.eq.symm
  have hXP : Commute (X₀ * (P * X₀ * P⁻¹)) P := (mul_inv_eq_iff_eq_mul.mp hc).symm
  have := hXP.mul_right (commute_suppGroup_compl hsupp hw)
  rwa [mul_inv_cancel_left] at this

theorem mem_blockCoords_one_zero {m : ℕ} (a : Fin (m + 1) ⊕ Fin (m + 1)) :
    a ∈ blockCoords (m + 1) 1 0 ↔ a ∈ coords (0 : Fin (m + 1)) := by
  have key : ∀ j : Fin (m + 1), (0 * 1 ≤ (j : ℕ) ∧ (j : ℕ) < (0 + 1) * 1) ↔ j = 0 := by
    intro j
    rw [Fin.ext_iff, Fin.val_zero]
    omega
  rw [mem_coords]
  rcases a with j | j
  · exact (key j).trans ⟨fun h => Or.inl (by rw [h]), fun h => by
      rcases h with h | h
      · exact Sum.inl_injective h
      · exact absurd h Sum.inl_ne_inr⟩
  · exact (key j).trans ⟨fun h => Or.inr (by rw [h]), fun h => by
      rcases h with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact Sum.inr_injective h⟩

theorem mem_blockCoords_one_one {m : ℕ} (a : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) :
    a ∈ blockCoords (m + 1 + 1) 1 1 ↔ a ∈ coords (1 : Fin (m + 1 + 1)) := by
  have key : ∀ j : Fin (m + 1 + 1), (1 * 1 ≤ (j : ℕ) ∧ (j : ℕ) < (1 + 1) * 1) ↔ j = 1 := by
    intro j
    rw [Fin.ext_iff, Fin.val_one]
    omega
  rw [mem_coords]
  rcases a with j | j
  · exact (key j).trans ⟨fun h => Or.inl (by rw [h]), fun h => by
      rcases h with h | h
      · exact Sum.inl_injective h
      · exact absurd h Sum.inl_ne_inr⟩
  · exact (key j).trans ⟨fun h => Or.inr (by rw [h]), fun h => by
      rcases h with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact Sum.inr_injective h⟩

theorem blockSwap_one_zero {m : ℕ} : blockSwap (m + 1 + 1) 1 0 = 1 := by
  rw [blockSwap_apply, blockSwapFun, dite_eq_left (by simp)]
  rfl

theorem blockSwap_one_one {m : ℕ} : blockSwap (m + 1 + 1) 1 1 = 0 := by
  rw [blockSwap_apply, blockSwapFun, dite_eq_right (by simp), dite_eq_left (by simp)]
  rfl

theorem spBlockFixOrSwap_one [Finite K] [CharP K 2] {m : ℕ} (v : StatedSp (m + 1 + 1 + 1) K)
    (hv : v * v = 1) : ∃ g : StatedSp (m + 1 + 1 + 1) K,
      g * v * g⁻¹ ∈ suppGroup (blockCoords (m + 1 + 1 + 1) 1 0)ᶜ ∨
        (permSp K (blockSwap (m + 1 + 1 + 1) 1))⁻¹ * (g * v * g⁻¹) ∈
          suppGroup (blockCoords (m + 1 + 1 + 1) 1 0 ∪ blockCoords (m + 1 + 1 + 1) 1 1)ᶜ := by
  have h0 : blockCoords (m + 1 + 1 + 1) 1 0 = coords 0 := Set.ext mem_blockCoords_one_zero
  have h1 : blockCoords (m + 1 + 1 + 1) 1 1 = coords 1 := Set.ext mem_blockCoords_one_one
  obtain ⟨g, ⟨hc₁, hc₂⟩ | ⟨hc₁, hc₂, hc₃, hc₄⟩⟩ := WitClSp.exists_conj_fix_or_swap v hv
  · exact ⟨g, Or.inl (by rw [h0]; exact WitClSp.mem_suppGroup_compl_of_fix hc₁ hc₂)⟩
  refine ⟨g, Or.inr ?_⟩
  rw [h0, h1, permSp_blockSwap_inv, mem_suppGroup_iff (WitClSp.parClosed_coords_union 0 1).compl]
  have hcol : ∀ x, mat _ K (permSp K (blockSwap (m + 1 + 1 + 1) 1)) *ᵥ Pi.single x 1 =
      Pi.single (Sum.map (blockSwap _ 1) (blockSwap _ 1) x) 1 :=
    WitClSp.mat_permSp_mulVec_single _
  have hfix : ∀ x, x ∈ coords (0 : Fin (m + 1 + 1 + 1)) ∪ coords 1 →
      mat _ K (permSp K (blockSwap (m + 1 + 1 + 1) 1) * (g * v * g⁻¹)) *ᵥ Pi.single x 1 =
        Pi.single x 1 := by
    intro x hx
    simp only [Set.mem_union, mem_coords] at hx
    rw [map_mul, ← Matrix.mulVec_mulVec]
    rcases hx with (rfl | rfl) | (rfl | rfl)
    · rw [hc₁, hcol]
      simp [blockSwap_one_one]
    · rw [hc₂, hcol]
      simp [blockSwap_one_one]
    · rw [hc₃, hcol]
      simp [blockSwap_one_zero]
    · rw [hc₄, hcol]
      simp [blockSwap_one_zero]
  intro t ht r
  rw [Set.mem_compl_iff, not_not] at ht
  rw [WitClSp.mat_apply_eq_mulVec, hfix t ht, Pi.single_apply, Matrix.one_apply]

end WitSpNs

@[expose] def SpBlockFixOrSwapInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n d : ℕ), 1 ≤ d → 3 * d ≤ n →
    ∀ v : StatedSp n K, v * v = 1 → ∃ g : StatedSp n K,
      g * v * g⁻¹ ∈ suppGroup (WitSpNs.blockCoords n d 0)ᶜ ∨
        (permSp K (WitSpNs.blockSwap n d))⁻¹ * (g * v * g⁻¹) ∈
          suppGroup (WitSpNs.blockCoords n d 0 ∪ WitSpNs.blockCoords n d 1)ᶜ

section Inputs

@[expose] def GGSpBlockWitnessInputOn (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSp n f).K →* G), P n f p →
    GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ → GGSixStepOne p B Bs x L D J →
      ∃ d : ℕ, 1 ≤ d ∧ 3 * d ≤ n ∧ ∃ A₀ X₀ : StatedSp n (GaloisField 2 f),
        X₀ ∈ suppGroup (WitSpNs.blockCoords n d 0) ∧
        GGSixBstarWit p Bs (ggG0 p B x L D J) .PSp f (ψ (A₀ * X₀ * A₀⁻¹)) ∧
        GGSixBstarWit p Bs (ggG0 p B x L D J) .PSp f
          (ψ (A₀ * (X₀ * (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d) * X₀ *
            (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d))⁻¹)) * A₀⁻¹))

open WitSpNs WitClSp in
theorem ggSixRootFusionWitnessOn_PSp_of_blockWitness {P : ℕ → ℕ → ℕ → Prop}
    (hin : GGSpBlockWitnessInputOn P) (hF : SpBlockFixOrSwapInput) :
    GGSixRootFusionWitnessOn fun t n f p => t = .PSp ∧ P n f p := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r _ _ _ s hs hs2
  obtain ⟨rfl, hPn⟩ := hP
  obtain ⟨d, hd1, hd3, A₀, X₀, hX₀, h₁, h₂⟩ := hin G p B Bs x L D J n f ψ hPn hctx s1
  have hn2 : 2 ≤ n := hctx.2.2.2.1.1.2.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨ψS, hψS⟩ : ∃ ψS : StatedSp n (GaloisField 2 f) →* G, ∀ a, ψS a = ψ a :=
    ⟨ψ, fun _ => rfl⟩
  have hψS' : Function.Injective ψS := fun a c h => hψ (by rw [← hψS, ← hψS]; exact h)
  have hrangeS : ψS.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hψS a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hψS a⟩
  rw [← hrangeS] at hs
  obtain ⟨w, rfl⟩ := hs
  have hw : w * w = 1 := by
    have h2 := pow_orderOf_eq_one (ψS w)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hψS' (by rw [h2, map_one])
  have hv : (A₀⁻¹ * w * A₀) * (A₀⁻¹ * w * A₀) = 1 := by
    rw [show (A₀⁻¹ * w * A₀) * (A₀⁻¹ * w * A₀) = A₀⁻¹ * (w * w) * A₀ by group, hw, mul_one,
      inv_mul_cancel]
  have hM : ∀ g, ψS g ∈ ggM p B x L D J := fun g =>
    Subgroup.le_normalizer (hrangeS ▸ ⟨g, rfl⟩)
  obtain ⟨g, hfix | hswap⟩ := hF (GaloisField 2 f) n d hd1 hd3 _ hv
  · obtain ⟨hcomm, hconj⟩ := conj_frame_witness ψS (commute_suppGroup_compl hX₀ hfix)
    refine Or.inr (Or.inl ⟨_, hcomm, ψS (A₀ * g * A₀⁻¹), hM _, ?_⟩)
    rw [hconj, hψS]
    exact h₁.fusionWitness
  · obtain ⟨hcomm, hconj⟩ := conj_frame_witness ψS (commute_blockSwap (by omega) hX₀ hswap)
    refine Or.inr (Or.inl ⟨_, hcomm, ψS (A₀ * g * A₀⁻¹), hM _, ?_⟩)
    rw [hconj, hψS]
    exact h₂.fusionWitness

open WitSpNs in
theorem ggSpBlockWitnessInputOn_of_plane {P : ℕ → ℕ → ℕ → Prop}
    (h : GGSpPlaneWitnessInputOn P) : GGSpBlockWitnessInputOn P := by
  intro G _ _ p B Bs x L D J n f ψ hP hctx s1
  obtain ⟨hn3, A₀, T, h₁, h₂⟩ := h G p B Bs x L D J n f ψ hP hctx s1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have h0 : blockCoords (m + 1 + 1 + 1) 1 0 = coords 0 := Set.ext mem_blockCoords_one_zero
  have hconj : permSp (GaloisField 2 f) (blockSwap (m + 1 + 1 + 1) 1) *
      longBlock (GaloisField 2 f) (m + 1 + 1 + 1) 0 T *
        (permSp (GaloisField 2 f) (blockSwap (m + 1 + 1 + 1) 1))⁻¹ =
      longBlock (GaloisField 2 f) (m + 1 + 1 + 1) 1 T := by
    rw [conj_permSp_longBlock, blockSwap_one_zero]
  refine ⟨1, le_rfl, by omega, A₀, longBlock (GaloisField 2 f) _ 0 T, ?_, h₁ 0, ?_⟩
  · rw [h0]
    exact WitClSp.longBlock_mem_suppGroup 0 T
  · rw [hconj]
    exact h₂ 0 1 (by simp)

theorem ggSpBlockWitnessInputOn_nonsplit :
    GGSpBlockWitnessInputOn fun _ f p => p ∣ 2 ^ f + 1 :=
  ggSpBlockWitnessInputOn_of_plane ggSpPlaneWitnessInputOn_nonsplit

@[expose] def GGSixRootFusionWitClRest2 : Prop :=
  GGSpBlockWitnessInputOn (fun _ f p => ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1) ∧
    SpBlockFixOrSwapInput ∧
    GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus)

theorem ggSixRootFusionWitClRest_of_rest2 (h : GGSixRootFusionWitClRest2) :
    GGSixRootFusionWitClRest := by
  obtain ⟨hblk, hF, hPlus, hMinus⟩ := h
  exact ⟨ggSpPlaneWitnessInputOn_nonsplit,
    (ggSixRootFusionWitnessOn_PSp_of_blockWitness hblk hF).mono fun _ _ _ _ ht => ht,
    hPlus, hMinus⟩

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_rest2 (h : GGSixRootFusionWitClRest2) :
    GGSixRootFusionWitnessInputFor GGOtherClassicalTag :=
  ggSixRootFusionWitnessInputFor_otherClassical_of_rest (ggSixRootFusionWitClRest_of_rest2 h)

end Inputs

end CFSG.StandardType
