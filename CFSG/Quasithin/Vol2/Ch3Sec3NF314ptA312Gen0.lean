module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312Aux

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312

theorem pCore_card_two_pow {Q : Type} [Group Q] [Finite Q] (B : Subgroup Q) :
    ∃ k : ℕ, Nat.card (CFSG.pCore 2 ↥B) = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := CFSG.pCore_isPGroup (p := 2) (G := ↥B)
  exact (IsPGroup.iff_card).mp hp

theorem card_eq_quot_mul {Q : Type} [Group Q] (B : Subgroup Q) :
    Nat.card ↥B = Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) * Nat.card (CFSG.pCore 2 ↥B) := by
  rw [mul_comm, ← Subgroup.card_mul_index (CFSG.pCore 2 ↥B)]
  rfl

theorem card_map_dvd {G H : Type} [Group G] [Group H] (f : G →* H) (N : Subgroup G) :
    Nat.card ↥(N.map f) ∣ Nat.card ↥N := by
  let g : ↥N →* ↥(N.map f) :=
    { toFun := fun x => ⟨f x, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  exact card_dvd_of_surj g hg

theorem odd_normal_eq_bot {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)))
    (N : Subgroup ↥B) [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  let π : ↥B →* ↥B ⧸ CFSG.pCore 2 ↥B := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  ·
    have hle : N ≤ CFSG.pCore 2 ↥B := by
      intro x hx
      have hmem : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    obtain ⟨k, hk⟩ := pCore_card_two_pow B
    have hd : Nat.card N ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exact h0
      · exfalso
        have : 2 ∣ Nat.card N := by
          rw [hj]
          exact dvd_pow_self 2 hpos.ne'
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    rw [hj0, pow_zero] at hj
    exact Subgroup.eq_bot_of_card_eq N hj
  ·
    have hd : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) ∣ Nat.card N := by
      have := card_map_dvd π N
      rw [h, Subgroup.card_top] at this
      exact this
    have h2 : 2 ∣ Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) := even_iff_two_dvd.mp heven
    have h2N : 2 ∣ Nat.card N := dvd_trans h2 hd
    exfalso
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2N)

theorem isExt_card_eq {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : CFSG.Quasithin.IsExt X PV PY) :
    ∃ (V : Subgroup X) (_ : V.Normal), PV ↥V ∧ PY (X ⧸ V) ∧
      Nat.card X = Nat.card ↥V * Nat.card (X ⧸ V) := by
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  refine ⟨V, hVn, hPV, hPY, ?_⟩
  have hm := Subgroup.card_mul_index V
  rw [Subgroup.index] at hm
  exact hm.symm

theorem card_dvd_of_injective {G H : Type} [Group G] [Group H] [Finite H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card G ∣ Nat.card H := by
  have e : G ≃ ↥f.range := (MonoidHom.ofInjective hf).toEquiv
  rw [Nat.card_congr e]
  exact Subgroup.card_subgroup_dvd_card f.range

end CFSG.Quasithin.H13.NF314ptA312
