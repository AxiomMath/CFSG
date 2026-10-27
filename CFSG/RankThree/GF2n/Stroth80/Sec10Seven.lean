module

public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenTransverse
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenCount
public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenFuse

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth107M2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec10Hyp hc n → Good103 M Q Z B t → ¬ SLMNat hc t 2

private theorem exists_minimal_degree {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    (hge3 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2)
    (hex : ∃ t : G, Good101 M Q Z B t) :
    ∃ (m : ℕ) (t : G), Good101 M Q Z B t ∧ SLMNat hc t m ∧ 3 ≤ m ∧
      ∀ (s : G) (k : ℕ), Good101 M Q Z B s → SLMNat hc s k → m ≤ k := by
  classical
  have hex' : ∃ k : ℕ, ∃ s : G, Good101 M Q Z B s ∧ SLMNat hc s k := by
    obtain ⟨t, ht⟩ := hex
    obtain ⟨k, -, hk⟩ := SLlike.exists_SLMNat (H.slLike ht)
    exact ⟨k, t, ht, hk⟩
  obtain ⟨t, ht, hm⟩ := Nat.find_spec hex'
  have hmin : ∀ (s : G) (k : ℕ), Good101 M Q Z B s → SLMNat hc s k →
      Nat.find hex' ≤ k := fun s k hs hk => Nat.find_min' hex' ⟨s, hs, hk⟩
  have hm2 : 2 ≤ Nat.find hex' := by
    obtain ⟨k, hk2, hk⟩ := SLlike.exists_SLMNat (H.slLike ht)
    have hEq := SLMNat.unique hm hk
    omega
  have hmne : Nat.find hex' ≠ 2 := fun h => hge3 t ht (h ▸ hm)
  exact ⟨Nat.find hex', t, ht, hm, by omega, hmin⟩

private theorem card_lt_card_of_bounds {C : Subgroup G} {m : ℕ}
    (hq4 : 4 ≤ Nat.card Z) (hm3 : 3 ≤ m)
    (hlow : Nat.card Z ^ m ≤ Nat.card ↥C * Nat.card Z) :
    Nat.card Z < Nat.card ↥C := by
  have hq0 : 0 < Nat.card Z := Nat.card_pos
  have hq1 : 1 < Nat.card Z := by omega
  have hpow : Nat.card Z ^ 3 ≤ Nat.card Z ^ m := Nat.pow_le_pow_right hq0 (by omega)
  have hmain : Nat.card Z ^ 2 * Nat.card Z ≤ Nat.card ↥C * Nat.card Z := by
    calc Nat.card Z ^ 2 * Nat.card Z = Nat.card Z ^ 3 := by ring
      _ ≤ Nat.card Z ^ m := hpow
      _ ≤ Nat.card ↥C * Nat.card Z := hlow
  have hle : Nat.card Z ^ 2 ≤ Nat.card ↥C := Nat.le_of_mul_le_mul_right hmain hq0
  have hlt : Nat.card Z < Nat.card Z ^ 2 := by
    have h := Nat.pow_lt_pow_right hq1 (m := 1) (n := 2) (by norm_num)
    simpa using h
  exact lt_of_lt_of_le hlt hle

private theorem n_eq_six_of_min_degree (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (h103b : Stroth103bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    (hge3 : ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) {m : ℕ} {t : G}
    (ht : Good101 M Q Z B t) (hm : SLMNat hc t m) (hm3 : 3 ≤ m)
    (hmin : ∀ (s : G) (k : ℕ), Good101 M Q Z B s → SLMNat hc s k → m ≤ k) :
    n = 6 := by
  obtain ⟨Y, hs⟩ := Good101.exists_sit hc ht
  have ht3 : Good103 M Q Z B t := ⟨ht, h103b G M Q Z B hc n H hge3 t ht⟩
  have hnft := Good103.no_fuse_of_noSL2 h34 h311a hspread H hge3 ht3
  obtain ⟨X, y, hsy, hyV, hyCt, hVX, hlow, hhigh⟩ :=
    Good103.exists_transverse h34 h311a hspread H ht3 hs hm (by omega)
  have hC : Nat.card Z < Nat.card ↥(Q ⊓ QB Y ⊓ QB X) :=
    card_lt_card_of_bounds (C := Q ⊓ QB Y ⊓ QB X) hc.hyp.q4 hm3 hlow
  obtain ⟨D₁, D₂, hD₁, hD₂, hD₁C, hD₂C, hne, hsup⟩ :=
    Good103.exists_two_roots H ht3 hs hsy hC
  have hyD₁ : y ∈ QB D₁ := Sit.mem_QB_of_le_QB hsy hD₁ (hD₁C.trans inf_le_right)
  have hyD₂ : y ∈ QB D₂ := Sit.mem_QB_of_le_QB hsy hD₂ (hD₂C.trans inf_le_right)
  obtain ⟨hnfy, hcardy, hWU, hUy⟩ :=
    Sit.root_frame_facts h34 h311a hspread h103b H hge3 hmin hsy hD₁ hD₂ hyD₁ hyD₂ hsup
  have hyZ : ∀ z ∈ Z, y * z = z * y := by
    intro z hz
    have hyH0 : y ∈ H0 M Z := (smith_1_12 hsy).1 hsy.mem
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyH0).2 z hz).symm
  have hCroot : ∀ γ ∈ (Q ⊓ QB Y ⊓ QB X : Subgroup G), γ ≠ 1 →
      ∃ D : Subgroup G, Ctx M Q Z D ∧ γ ∈ D ∧ D ≤ Q ⊓ QB Y ⊓ QB X :=
    fun γ hγ hγ1 => Good103.exists_root_le_inf H ht3 hs hsy hγ hγ1
  have hyD : ∀ D : Subgroup G, Ctx M Q Z D → D ≤ Q ⊓ QB Y ⊓ QB X → y ∈ QB D :=
    fun D hD hDC => Sit.mem_QB_of_le_QB hsy hD (hDC.trans inf_le_right)
  obtain ⟨x, -, hxV, hxC⟩ :=
    Good103.exists_comm_mem_Vt_not_mem_sup h34 h311a hspread H ht3 hs hm hnft
      (C := Q ⊓ QB Y ⊓ QB X) inf_le_left hhigh hCroot hyZ hyD hyCt hnfy hcardy hWU hUy
  exact Good101.n_eq_six_of_comm h34 h311a hspread h103b H hge3 ht hs hsy hyV hVX
    hD₁ hD₂ hD₁C hD₂C hne hxV hxC

theorem stroth_10_7_ge3 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (h103b : Stroth103bStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
      Sec10Hyp hc n → (∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2) →
        (∃ t : G, Good101 M Q Z B t) → n = 6 ∧ ∀ t : G, Good101 M Q Z B t → SLMNat hc t 3 := by
  intro G _ _ M Q Z B hc n H hge3 hex
  obtain ⟨m, t, ht, hm, hm3, hmin⟩ := exists_minimal_degree H hge3 hex
  have hn : n = 6 := n_eq_six_of_min_degree h34 h311a hspread h103b H hge3 ht hm hm3 hmin
  refine ⟨hn, fun s hs => ?_⟩
  obtain ⟨k, hk2, hk⟩ := SLlike.exists_SLMNat (H.slLike hs)
  have hs103 : Good103 M Q Z B s := ⟨hs, h103b G M Q Z B hc n H hge3 s hs⟩
  have hUeq := Good103.card_Ut_eq h34 h311a hspread H hs103 hk
  have hUle := Ctx.card_Ut_le hc H.width hs.mem_LB
  rw [hn] at hUle
  rw [hUeq] at hUle
  have hq : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hle : 2 * k + 1 ≤ 6 + 1 := (Nat.pow_le_pow_iff_right hq).mp hUle
  have hkne : k ≠ 2 := fun h2 => hge3 s hs (h2 ▸ hk)
  have hk3 : k = 3 := by omega
  exact hk3 ▸ hk

private theorem no_degree_two_of_good101 {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    (h103a : Stroth103aStatement) (h107m2 : Stroth107M2Statement) :
    ∀ s : G, Good101 M Q Z B s → ¬ SLMNat hc s 2 := by
  intro s hs hs2
  obtain ⟨y, hyQ, hy103⟩ := h103a G M Q Z B hc n s H hs hs2
  exact h107m2 G M Q Z B hc n (s * y) H hy103
    ((SLMNat.mul_of_mem_Q (hc := hc) hyQ).mpr hs2)

theorem stroth_10_7 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) (h101 : Stroth101Statement)
    (h103a : Stroth103aStatement) (h103b : Stroth103bStatement)
    (h107m2 : Stroth107M2Statement) : Stroth107Statement := by
  intro G _ _ M Q Z B hc n H
  exact stroth_10_7_ge3 h34 h311a hspread h103b G M Q Z B hc n H
    (no_degree_two_of_good101 H h103a h107m2) (h101 G M Q Z B hc n H)

end CFSG.RankThree.GF2n.Stroth80
