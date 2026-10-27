module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.S1549D

theorem eq_top_of_index_le_five {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.factorial 5 < Nat.card G) (H : Subgroup G) (hH : H.index ≤ 5) : H = ⊤ := by
  classical
  by_contra hne
  let φ := MulAction.toPermHom G (G ⧸ H)
  have hker : φ.ker = ⊥ := by
    rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker) with h | h
    · exact h
    · exfalso
      apply hne
      refine eq_top_iff.mpr fun g _ => ?_
      have h1 : φ g = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk 1 := by
        have := congrArg (fun p : Equiv.Perm (G ⧸ H) => p (QuotientGroup.mk (1 : G))) h1
        simpa [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
      have h4 := QuotientGroup.eq.mp h2
      simpa using H.inv_mem h4
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have h1 := Nat.card_le_card_of_injective φ hinj
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (G ⧸ H)), Fintype.card_perm,
    ← Nat.card_eq_fintype_card] at h1
  have h2 : Nat.card (G ⧸ H) ≤ 5 := hH
  have h3 : (Nat.card (G ⧸ H)).factorial ≤ Nat.factorial 5 := Nat.factorial_le h2
  omega

theorem eq_or_top_of_card_24 {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) {P H : Subgroup G} (hP : Nat.card P = 24) (hPH : P ≤ H) :
    H = P ∨ H = ⊤ := by
  have hd : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
  obtain ⟨m, hm⟩ := hd
  have hmul : Nat.card H * H.index = 360 := by rw [← hG]; exact H.card_mul_index
  by_cases hidx : H.index ≤ 5
  · right
    exact eq_top_of_index_le_five (by rw [hG]; norm_num) H hidx
  · left
    push Not at hidx
    rw [hP] at hm
    rw [hm] at hmul
    obtain ⟨idx, hidx_def⟩ : ∃ idx, idx = H.index := ⟨_, rfl⟩
    rw [← hidx_def] at hmul hidx
    have h15 : m * idx = 15 := by
      have h' : 24 * (m * idx) = 360 := by rw [← hmul]; ring
      omega
    have hle : idx ≤ 15 := by
      have : idx ∣ 15 := ⟨m, by rw [mul_comm]; exact h15.symm⟩
      exact Nat.le_of_dvd (by norm_num) this
    interval_cases idx <;> try omega
    have hm1 : m = 1 := by omega
    rw [hm1] at hm
    exact (Subgroup.eq_of_le_of_card_ge hPH (by omega)).symm

theorem card_sylow_eight {Ω : Type*} [Group Ω] [Finite Ω] {T L : Subgroup Ω}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T L) (hL : Nat.card L = 360) : Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
  have h1 : (T.subgroupOf L).index * Nat.card T = Nat.card L := by
    have := (T.subgroupOf L).index_mul_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv] at this
  have hodd := hT.2.2
  rw [hL, hk] at h1
  generalize (T.subgroupOf L).index = idx at h1 hodd
  have hk8 : k ≤ 8 := by
    by_contra h
    push Not at h
    have h2 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    have hpos : 0 < idx := by
      rcases Nat.eq_zero_or_pos idx with h0 | h0
      · rw [h0] at h1; omega
      · exact h0
    nlinarith
  rw [hk]
  interval_cases k <;> norm_num at h1 ⊢ <;> omega

theorem eq_of_lt_le_card {Ω : Type*} [Group Ω] [Finite Ω] {T P₀ P : Subgroup Ω} (hT : Nat.card T = 8)
    (hP : Nat.card P = 24) (hTP₀ : T < P₀) (hP₀P : P₀ ≤ P) : P₀ = P := by
  have h1 : Nat.card T ∣ Nat.card P₀ := Subgroup.card_dvd_of_le hTP₀.le
  have h2 : Nat.card P₀ ∣ Nat.card P := Subgroup.card_dvd_of_le hP₀P
  have h3 : Nat.card T < Nat.card P₀ := by
    by_contra h
    push Not at h
    exact hTP₀.ne (Subgroup.eq_of_le_of_card_ge hTP₀.le h)
  rw [hT] at h1 h3
  rw [hP] at h2
  obtain ⟨a, ha⟩ := h1
  have hle : Nat.card P₀ ≤ 24 := Nat.le_of_dvd (by norm_num) h2
  have hcard : Nat.card P₀ = 24 := by
    have ha3 : a ≤ 3 := by omega
    have ha2 : 2 ≤ a := by omega
    interval_cases a
    · rw [ha] at h2
      norm_num at h2
    · omega
  exact Subgroup.eq_of_le_of_card_ge hP₀P (by omega)

@[expose] def stabU {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) (u : V) (C : Subgroup V)
    (hY : ∀ y ∈ Y, ∀ c ∈ C, y c ∈ C) : Subgroup (MulAut V) where
  carrier := {g | g ∈ Y ∧ g u * u⁻¹ ∈ C}
  one_mem' := ⟨Y.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.mul_mem ha hb, ?_⟩
    have e : (a * b) u * u⁻¹ = a (b u * u⁻¹) * (a u * u⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv]
      group
    rw [e]
    exact C.mul_mem (hY a ha _ hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Y.inv_mem ha, ?_⟩
    have h1 := hY a⁻¹ (Y.inv_mem ha) _ ha'
    have e : a⁻¹ (a u * u⁻¹) = (a⁻¹ u * u⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.inv_apply_self, mul_inv_rev, inv_inv]
      try group
    rw [e] at h1
    simpa using C.inv_mem h1

theorem commutator_eq_map_alt {W : Type*} [CommGroup W] {G' : Subgroup (MulAut W)}
    {π : Equiv.Perm (Fin 6) →* ↥G'} (hπ : Function.Surjective π) :
    ⁅G', G'⁆ = (alternatingGroup (Fin 6)).map (G'.subtype.comp π) := by
  have hrange : (⊤ : Subgroup (Equiv.Perm (Fin 6))).map (G'.subtype.comp π) = G' := by
    ext g
    constructor
    · rintro ⟨σ, -, rfl⟩
      exact (π σ).2
    · intro hg
      obtain ⟨σ, hσ⟩ := hπ ⟨g, hg⟩
      exact ⟨σ, trivial, by simp [hσ]⟩
  have hA : commutator (Equiv.Perm (Fin 6)) = alternatingGroup (Fin 6) :=
    alternatingGroup.commutator_perm_eq (by simp)
  calc ⁅G', G'⁆ = ⁅(⊤ : Subgroup (Equiv.Perm (Fin 6))).map (G'.subtype.comp π),
        (⊤ : Subgroup (Equiv.Perm (Fin 6))).map (G'.subtype.comp π)⁆ := by rw [hrange]
    _ = (⁅(⊤ : Subgroup (Equiv.Perm (Fin 6))), (⊤ : Subgroup (Equiv.Perm (Fin 6)))⁆).map
        (G'.subtype.comp π) :=
        (Subgroup.map_commutator _ _ _).symm
    _ = (alternatingGroup (Fin 6)).map (G'.subtype.comp π) := by
        rw [← commutator_def, hA]

end CFSG.Quasithin.S1549D
