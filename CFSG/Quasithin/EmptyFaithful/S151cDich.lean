module

public import CFSG.Quasithin.EmptyFaithful.S151cOrbit

public section

namespace CFSG.Quasithin

open CFSG.Open

section Dich151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

@[expose] def NormalIn (X K : Subgroup (MulAut V)) : Prop := ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K

omit [Finite V] in
theorem NormalIn.le_normalizer {K : Subgroup (MulAut V)} (hn : NormalIn X K) :
    X ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hn x hx y, fun hy => ?_⟩
  have := hn x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

omit [Finite V] in
theorem NormalIn.conjBy_eq {K : Subgroup (MulAut V)} (hn : NormalIn X K) {x : MulAut V}
    (hx : x ∈ X) : conjBy x K = K :=
  conjBy_eq_of_mem_normalizer (hn.le_normalizer hx)

omit [Finite V] in
theorem NormalIn.fixV_invariant {K : Subgroup (MulAut V)} (hn : NormalIn X K) {x : MulAut V}
    (hx : x ∈ X) {u : V} (hu : u ∈ fixV K) : x u ∈ fixV K := by
  have h1 : x u ∈ fixV (conjBy x K) := by
    rw [fixV_conjBy]
    exact ⟨u, hu, rfl⟩
  rwa [hn.conjBy_eq hx] at h1

omit [Finite V] in
theorem NormalIn.commV_invariant {K : Subgroup (MulAut V)} (hn : NormalIn X K) {x : MulAut V}
    (hx : x ∈ X) {u : V} (hu : u ∈ commV K) : x u ∈ commV K := by
  have h1 : x u ∈ commV (conjBy x K) := commV_apply_of_conjBy rfl hu
  rwa [hn.conjBy_eq hx] at h1

omit [Finite V] in
theorem eq_bot_of_commV_eq_bot {K : Subgroup (MulAut V)} (h : commV K = ⊥) : K = ⊥ :=
  CFSG.Quasithin.FixVLat.eq_bot_of_commV_eq_bot h

open Classical in
theorem zpowers_mem_kRle_three (hV : ∀ v : V, v ^ 2 = 1) {c : MulAut V} {r : ℚ} (hcX : c ∈ X)
    (hc1 : c ≠ 1) (hc2 : c ^ 2 = 1) (hrk : (rk (commV (Subgroup.zpowers c)) : ℚ) ≤ r) :
    Subgroup.zpowers c ∈ kRle X 3 r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
  have hA2 : IsA2 X (Subgroup.zpowers c) := by
    refine ⟨Subgroup.zpowers_le.mpr hcX, ?_, isElemAbelian2_zpowers151c hc2⟩
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    exact hc1 h
  have hcard : rk (Subgroup.zpowers c) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hord]
    simp
  have hq := isQuadratic_zpowers hV hc2
  have hser : commSeries (Subgroup.zpowers c) 3 = ⊥ := by
    have h2 : commSeries (Subgroup.zpowers c) 2 = ⊥ := (isQuadratic_iff_commSeries_two _).mp hq
    have : commSeries (Subgroup.zpowers c) 3 = commSub (commSeries (Subgroup.zpowers c) 2)
        (Subgroup.zpowers c) := rfl
    rw [this, h2]
    exact commSub_bot_left _
  refine ⟨⟨hA2, ?_⟩, hser⟩
  unfold rAV
  rw [hcard, rkIdx_fixV_zpowers]
  simpa using hrk

open Classical in
theorem involution_mem_Jhat (hV : ∀ v : V, v ^ 2 = 1) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {c : MulAut V} (hcX : c ∈ X) (hc1 : c ≠ 1) (hc2 : c ^ 2 = 1)
    (hrk : (rk (commV (Subgroup.zpowers c)) : ℚ) ≤ r) : c ∈ Jhat X := by
  have hmem := zpowers_mem_kRle_three hV hcX hc1 hc2 hrk
  have hmin : ∀ B ∈ kRle X 3 r, B ≤ Subgroup.zpowers c → B = Subgroup.zpowers c := by
    intro B hB hBc
    have hBne : B ≠ ⊥ := hB.1.1.ne_bot
    have h1 : 1 < Nat.card B := (Subgroup.one_lt_card_iff_ne_bot B).mpr hBne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf c = 2 := orderOf_eq_prime hc2 hc1
    have h2 : Nat.card (Subgroup.zpowers c) = 2 := by rw [Nat.card_zpowers, hord]
    exact Subgroup.eq_of_le_of_card_ge hBc (by omega)
  have hQ : Subgroup.zpowers c ∈ QhatStar X := ⟨r, hr, hr2, hmem, hmin⟩
  exact le_Jhat hQ (Subgroup.mem_zpowers c)

omit [Finite V] in
theorem rk_pos_iff_ne_bot' [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} :
    0 < rk W ↔ W ≠ ⊥ := by
  constructor
  · intro h hW
    rw [hW, rk_bot] at h
    exact lt_irrefl _ h
  · intro h
    rcases Nat.eq_zero_or_pos (rk W) with h0 | h0
    · exact absurd ((rk_eq_zero_iff hV).mp h0) h
    · exact h0

theorem le_Xc_of_fixV_ne_bot (h : Setting151c X Tb Xc) {K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hn : NormalIn X K) (hfix : fixV K ≠ ⊥) : K ≤ Xc := by
  have hTbX : Tb ≤ X := h.syl.1
  have hinv : ∀ g ∈ Tb, ∀ u ∈ fixV K, g u ∈ fixV K := fun g hg u hu => hn.fixV_invariant (hTbX hg) hu
  have hpos := rk_inf_fixV_pos_of_isPGroup_two h.sq h.syl.2.1 hinv hfix
  have hne : (fixV K ⊓ fixV Tb : Subgroup V) ≠ ⊥ := (rk_pos_iff_ne_bot' h.sq).mp hpos
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hzK : z ∈ fixV K := hz.1
  have hzT : z ∈ fixV Tb := hz.2
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hZ1 : Subgroup.zpowers z ≤ fixV Tb := Subgroup.zpowers_le.mpr hzT
  have hZ1ne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1' (Subgroup.zpowers_eq_bot.mp e)
  intro k hk
  refine h.hU _ hZ1 hZ1ne ⟨hKX hk, ?_⟩
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [map_zpow, hzK k hk]

theorem not_commV_le_closure (h : Setting151c X Tb Xc) {K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hn : NormalIn X K) (hK1 : K ≠ ⊥) (hfix : fixV K ≠ ⊥) :
    ¬ commV K ≤ Subgroup.closure {x | ∃ g ∈ K, ∃ z ∈ fixV Tb ⊓ commV K, g z = x} := by
  intro hle
  have hKc : K ≤ Xc := le_Xc_of_fixV_ne_bot h hKX hn hfix
  refine h.star (commV K) (fun e => hK1 (eq_bot_of_commV_eq_bot e))
    (fun g hg w hw => hn.commV_invariant hg hw) (hle.trans (Subgroup.closure_mono ?_))
  rintro x ⟨g, hg, z, hz, rfl⟩
  exact ⟨g, hKc hg, z, hz, rfl⟩

open Classical in
@[expose] def IsComp (X : Subgroup (MulAut V)) (I : Finset (Subgroup (MulAut V)))
    (K : Subgroup (MulAut V)) : Prop :=
  (∃ L ∈ I, (∀ x ∈ X, conjBy x L = L) ∧ K = L) ∨
    (∃ L ∈ I, ∃ L₂ ∈ I, L₂ ≠ L ∧ (∃ x ∈ X, conjBy x L = L₂) ∧
      (∀ x ∈ X, conjBy x L = L ∨ conjBy x L = L₂) ∧ K = L ⊔ L₂)

open Classical in
theorem exists_comp (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : ∃ K, IsComp X I K ∧ L ≤ K := by
  by_cases hnot : ∃ x ∈ X, conjBy x L ≠ L
  · obtain ⟨L₂, hL₂, hne, hx, horb⟩ := orbit_le_two h hr hr2 hI hL hnot
    exact ⟨L ⊔ L₂, Or.inr ⟨L, hL, L₂, hL₂, hne, hx, horb, rfl⟩, le_sup_left⟩
  · push Not at hnot
    exact ⟨L, Or.inl ⟨L, hL, hnot, rfl⟩, le_rfl⟩

open Classical in
omit [Finite V] in
theorem IsComp.normalIn {I : Finset (Subgroup (MulAut V))} {K : Subgroup (MulAut V)}
    (hK : IsComp X I K) : NormalIn X K := by
  rcases hK with ⟨L, hL, hnorm, rfl⟩ | ⟨L, hL, L₂, hL₂, hne, ⟨x₂, hx₂, e₂⟩, horb, rfl⟩
  · intro x hx k hk
    have := mem_conjBy_of_mem (g := x) hk
    rwa [hnorm x hx] at this
  · intro x hx k hk
    have h1 : conjBy x L ≤ L ⊔ L₂ := by
      rcases horb x hx with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
    have h2 : conjBy x L₂ ≤ L ⊔ L₂ := by
      have : conjBy x L₂ = conjBy (x * x₂) L := by rw [← e₂, conjBy_conjBy]
      rw [this]
      rcases horb (x * x₂) (X.mul_mem hx hx₂) with h1 | h1
      · rw [h1]; exact le_sup_left
      · rw [h1]; exact le_sup_right
    have hsupeq : conjBy x (L ⊔ L₂) = conjBy x L ⊔ conjBy x L₂ := Subgroup.map_sup _ _ _
    have hsup : conjBy x (L ⊔ L₂) ≤ L ⊔ L₂ := by
      rw [hsupeq]
      exact sup_le h1 h2
    exact hsup (mem_conjBy_of_mem hk)

open Classical in
theorem IsComp.le_Jhat {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {K : Subgroup (MulAut V)} (hK : IsComp X I K) : K ≤ Jhat X := by
  rcases hK with ⟨L, hL, -, hKL⟩ | ⟨L, hL, L₂, hL₂, -, -, -, hKL⟩
  · rw [hKL]
    exact block_le_J hI hL
  · rw [hKL]
    exact sup_le (block_le_J hI hL) (block_le_J hI hL₂)

open Classical in
theorem IsComp.block_le_or_commV_le_fixV {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {K : Subgroup (MulAut V)} (hK : IsComp X I K)
    {L' : Subgroup (MulAut V)} (hL' : L' ∈ I) : L' ≤ K ∨ commV L' ≤ fixV K := by
  rcases hK with ⟨L, hL, -, hKL⟩ | ⟨L, hL, L₂, hL₂, -, -, -, hKL⟩
  · rw [hKL]
    by_cases h : L' = L
    · exact Or.inl h.le
    · exact Or.inr (hI.triv L' hL' L hL h)
  · rw [hKL]
    by_cases h1 : L' = L
    · exact Or.inl (by rw [h1]; exact le_sup_left)
    · by_cases h2 : L' = L₂
      · exact Or.inl (by rw [h2]; exact le_sup_right)
      · refine Or.inr ?_
        rw [fixV_sup]
        exact le_inf (hI.triv L' hL' L hL h1) (hI.triv L' hL' L₂ hL₂ h2)

open Classical in
theorem dich (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {K : Subgroup (MulAut V)} (hK : IsComp X I K)
    (hKne : K ≠ ⊥) :
    (Jhat X = K ∧ fixV (Jhat X) = ⊥) ∨
      (fixV K ≠ ⊥ ∧ K ≤ Xc ∧
        ¬ commV K ≤ Subgroup.closure {x | ∃ g ∈ K, ∃ z ∈ fixV Tb ⊓ commV K, g z = x}) := by
  by_cases H1 : Jhat X = K ∧ fixV (Jhat X) = ⊥
  · exact Or.inl H1
  · refine Or.inr ?_
    have hfix : fixV K ≠ ⊥ := by
      intro hfix0
      by_cases hJK : Jhat X = K
      · apply H1
        rw [hJK]
        exact ⟨rfl, hfix0⟩
      ·
        have hex : ∃ L' ∈ I, ¬ L' ≤ K := by
          by_contra hcon
          push Not at hcon
          apply hJK
          refine le_antisymm ?_ (hK.le_Jhat hI)
          rw [hI.sup_eq]
          exact iSup₂_le fun L' hL' => hcon L' hL'
        obtain ⟨L', hL', hnle⟩ := hex
        have hc := (hK.block_le_or_commV_le_fixV hI hL').resolve_left hnle
        rw [hfix0, le_bot_iff] at hc
        exact hI.ne_bot L' hL' (eq_bot_of_commV_eq_bot hc)
    have hKX : K ≤ X := (hK.le_Jhat hI).trans (Jhat_le X)
    exact ⟨hfix, le_Xc_of_fixV_ne_bot h hKX hK.normalIn hfix,
      not_commV_le_closure h hKX hK.normalIn hKne hfix⟩

end Dich151c

end CFSG.Quasithin
