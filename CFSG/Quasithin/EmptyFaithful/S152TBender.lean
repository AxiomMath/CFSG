module

public import CFSG.Quasithin.EmptyFaithful.S152SSplit
public import CFSG.Quasithin.EmptyFaithful.S146yBorelBender
public import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.ProperTwoGeneratedCore.TheoremC

namespace CFSG.Quasithin

theorem bct_center_eq_bot_of_simple_nonabelian {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, ¬ Commute a b) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have : a ∈ Subgroup.center Y := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem borelCentralizerTrivial_of_core {Y : Type} [Group Y] [Finite Y] {S₀ : Subgroup Y}
    (h₀ : IsSylowTwoOf S₀ ⊤)
    (hcore : ∀ x : Y, (∀ b ∈ Subgroup.normalizer (S₀ : Set Y), x * b = b * x) → x = 1) :
    BorelCentralizerTrivial Y := by
  intro U hUp hUidx x hx
  have hS : IsSylowTwoOf U ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hUp, hUidx⟩
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top h₀ hS
  have hN : Subgroup.normalizer (U : Set Y) =
      (Subgroup.normalizer (S₀ : Set Y)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_equiv_normalizer_eq, hg]
  have h1 : g⁻¹ * x * g = 1 := by
    apply hcore
    intro b hb
    have hb' : g * b * g⁻¹ ∈ Subgroup.normalizer (U : Set Y) := by
      rw [hN]
      exact ⟨b, hb, by simp⟩
    have := hx _ hb'
    calc g⁻¹ * x * g * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [this]
      _ = b * (g⁻¹ * x * g) := by group
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem borelCentralizerTrivial_of_benderBorelFacts {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, ¬ Commute a b)
    (h : ∀ Q : Sylow 2 Y, BenderBorelFacts Y (Q : Subgroup Y)) : BorelCentralizerTrivial Y := by
  intro U hUp hUidx x hx
  have hS : IsSylowTwoOf U ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hUp, hUidx⟩
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hS
  have facts := h Q
  have hxN : ∀ b ∈ Subgroup.normalizer ((Q : Subgroup Y) : Set Y), (MulAut.conj x) b = b := by
    intro b hb
    have h1 := hx b hb
    rw [MulAut.conj_apply]
    calc x * b * x⁻¹ = b * x * x⁻¹ := by rw [h1]
      _ = b := by group
  have hQfix : ∀ q ∈ (Q : Subgroup Y), (MulAut.conj x) q = q := fun q hq =>
    hxN q (Subgroup.le_normalizer hq)
  obtain ⟨r, hrQ, hr⟩ := facts.aut_inner (MulAut.conj x) hQfix
  obtain ⟨D, -, hDN, -, htrans, -⟩ := facts.torus
  have hrc : InCenterOf (Q : Subgroup Y) r := by
    refine ⟨hrQ, fun q hq => ?_⟩
    have h1 := hr q
    rw [hQfix q hq] at h1
    show q * r = r * q
    calc q * r = (r * q * r⁻¹) * r := by rw [← h1]
      _ = r * q := by group
  have hr1 : r = 1 := by
    by_contra hne
    have hsub : {w : Y | InCenterOf (Q : Subgroup Y) w} ⊆ {1, r} := by
      intro w hw
      by_cases hw1 : w = 1
      · simp [hw1]
      · obtain ⟨d, hd, hdw⟩ := htrans w r hw hw1 hrc hne
        have hdd : r * d * r⁻¹ = d := by rw [← hr d]; exact hxN d (hDN hd)
        have hcomm : d * r = r * d := by
          calc d * r = (r * d * r⁻¹) * r := by rw [hdd]
            _ = r * d := by group
        have : w = r := by
          calc w = d * (d⁻¹ * w * d) * d⁻¹ := by group
            _ = d * r * d⁻¹ := by rw [hdw]
            _ = r := by rw [hcomm]; group
        simp [this]
    have hcard := facts.center_card
    have h2 : Set.ncard {w : Y | InCenterOf (Q : Subgroup Y) w} ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le (1 : Y) {r}).trans (by simp))
    have h3 : Nat.card {w : Y // InCenterOf (Q : Subgroup Y) w} =
        Set.ncard {w : Y | InCenterOf (Q : Subgroup Y) w} := Nat.card_coe_set_eq _
    omega
  have hxZ : x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := hr y
    rw [hr1] at h1
    simp only [MulAut.conj_apply, inv_one, mul_one, one_mul] at h1
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  rw [bct_center_eq_bot_of_simple_nonabelian hs hna, Subgroup.mem_bot] at hxZ
  exact hxZ

theorem borelCentralizerTrivial_of_isBenderOf {n : ℕ} {Y : Type} [Group Y]
    [Finite Y] (h : E2.IsBenderOf n Y) : BorelCentralizerTrivial Y := by
  have hB := isBenderGroup_of_isBenderOf h
  exact borelCentralizerTrivial_of_benderBorelFacts
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hB)
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.exists_not_commute hB)
    fun Q => benderBorelFactsHold Y hB Q

theorem bctFamL2_proof : BCTFamL2 :=
  fun f hf _ _ _ h => borelCentralizerTrivial_of_isBenderOf (n := f) ⟨hf, Or.inl h⟩

theorem bctFamU3_proof : BCTFamU3 :=
  fun f hf _ _ _ h => borelCentralizerTrivial_of_isBenderOf (n := f) ⟨hf, Or.inr (Or.inr h)⟩

theorem bctFamSz_proof : BCTFamSz :=
  fun f _ hf3 X _ _ h => borelCentralizerTrivial_of_isBenderOf (n := f) ⟨by omega, Or.inr (Or.inl h)⟩

end CFSG.Quasithin
