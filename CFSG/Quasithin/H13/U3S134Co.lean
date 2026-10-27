module

public import CFSG.Quasithin.H13.U3S134Defs
public import CFSG.Quasithin.H13.U3S1343
public import CFSG.Quasithin.H13.Sp62S6Over

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def c2perm : Perm (Fin 6) := c[0, 2, 4] * c[1, 3, 5]

@[expose] def c123 : Perm (Fin 6) := swap 1 2 * swap 2 3

theorem c2perm_props : c2perm ∈ alternatingGroup (Fin 6) ∧ c2perm ^ 3 = 1 ∧ c2perm ≠ 1 ∧
    A6.InP2 c2perm := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem c012_props : c012 ∈ alternatingGroup (Fin 6) ∧ c012 ^ 3 = 1 ∧ InA4 c012 := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem c123_props : c123 ∈ alternatingGroup (Fin 6) ∧ c123 ^ 3 = 1 ∧ InA4 c123 := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem inP2_iff : ∀ σ : Perm (Fin 6), A6.InP2 σ ↔
    (InW2 (G6.permAct 6 σ (A6.pv 0 1)) ∧ InW2 (G6.permAct 6 σ (A6.pv 2 3)) ∧
      InW2 (G6.permAct 6 σ (A6.pv 4 5))) := by
  decide +kernel

theorem inW2_of_inP2 : ∀ σ : Perm (Fin 6), A6.InP2 σ → ∀ x : A6.P6, InW2 x →
    InW2 (G6.permAct 6 σ x) := by
  decide +kernel

theorem inP2_of_inD6 : ∀ σ : Perm (Fin 6), A6.InD6 σ → A6.InP2 σ := by decide +kernel

theorem pv_W2 : (InW2 (A6.pv 0 1) ∧ A6.pv 0 1 ∈ G6.coreMod 6) ∧
    (InW2 (A6.pv 2 3) ∧ A6.pv 2 3 ∈ G6.coreMod 6) ∧
    (InW2 (A6.pv 4 5) ∧ A6.pv 4 5 ∈ G6.coreMod 6) := by
  refine ⟨⟨by decide, G6.mem_coreMod.2 (by decide)⟩, ⟨by decide, G6.mem_coreMod.2 (by decide)⟩,
    ⟨by decide, G6.mem_coreMod.2 (by decide)⟩⟩

theorem c2_moves_W2 : ∀ x : A6.P6, ∑ i, Multiplicative.toAdd x i = 0 → InW2 x → x ≠ 1 →
    x ≠ G6.allOnes 6 → G6.permAct 6 c2perm x ≠ x ∧ G6.permAct 6 c2perm x ≠ x * G6.allOnes 6 := by
  decide +kernel

theorem c2_moves_U0 : ∀ x : A6.P6, ∑ i, Multiplicative.toAdd x i = 0 → ¬ InW2 x →
    ¬ InW2 (G6.permAct 6 c2perm x * x⁻¹) := by
  decide +kernel

theorem c2_moves_U0' : ∀ x : A6.P6, ¬ InW2 x → ¬ InW2 (G6.permAct 6 c2perm x) := by
  decide +kernel

theorem c2_fix : G6.permAct 6 c2perm (G6.allOnes 6) = G6.allOnes 6 ∧
    ∀ x : A6.P6, G6.permAct 6 c2perm x = 1 → x = 1 := by
  decide +kernel

theorem card_W2sub : Nat.card ↥W2sub = 8 := by
  have : Fintype.card {y : ↥(G6.coreMod 6) // InW2 (y : A6.P6)} = 8 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

theorem allOnes_W2 : InW2 (G6.allOnes 6) := by decide

theorem c2_noncentral :
    (A6.pv 0 1 * (G6.permAct 6 c2perm (A6.pv 0 1))⁻¹ ≠ 1 ∧
      A6.pv 0 1 * (G6.permAct 6 c2perm (A6.pv 0 1))⁻¹ ≠ G6.allOnes 6) ∧
    (¬ InW2 (A6.pv 0 2 * (G6.permAct 6 c2perm (A6.pv 0 2))⁻¹) ∧ A6.pv 0 2 ∈ G6.coreMod 6) := by
  refine ⟨by decide, by decide, G6.mem_coreMod.2 (by decide)⟩

theorem four_pow_mod_three (a : ℕ) : 4 ^ a % 3 = 1 := by
  induction a with
  | zero => rfl
  | succ n ih => rw [pow_succ, Nat.mul_mod, ih]

theorem comm_c2_tau : c2perm * (swap 0 1 * swap 2 3) * c2perm⁻¹ * (swap 0 1 * swap 2 3)⁻¹ =
    swap 0 1 * swap 4 5 ∧ A6.InD6 (swap 0 1 * swap 2 3) ∧
    swap (0 : Fin 6) 1 * swap 2 3 ∈ alternatingGroup (Fin 6) := by
  simp only [Perm.mem_alternatingGroup]
  decide

theorem U0_decomp : ∀ x : A6.P6, ∑ i, Multiplicative.toAdd x i = 0 →
    ∃ y : A6.P6, ∑ i, Multiplicative.toAdd y i = 0 ∧
      (x = y * (G6.permAct 6 c2perm y)⁻¹ ∨ x = A6.pv 0 1 * (y * (G6.permAct 6 c2perm y)⁻¹)) := by
  decide +kernel

theorem pv01_eq : A6.pv 0 1 = A6.pv 0 2 * (G6.permAct 6 (swap 0 1 * swap 4 5) (A6.pv 0 2))⁻¹ := by
  decide


theorem span_e45 : ∀ y : A6.P6, ∑ i, Multiplicative.toAdd y i = 0 →
    ∃ a b c d e : Bool, y =
      (if a then A6.e45 else 1) *
      (if b then G6.permAct 6 c2perm A6.e45 else 1) *
      (if c then G6.permAct 6 c2perm (G6.permAct 6 c2perm A6.e45) else 1) *
      (if d then G6.permAct 6 c012 (G6.permAct 6 c2perm A6.e45) else 1) *
      (if e then G6.permAct 6 c2perm (G6.permAct 6 c012 (G6.permAct 6 c2perm A6.e45)) else 1) := by
  decide +kernel

theorem span_e0123 : ∀ y : A6.P6, ∑ i, Multiplicative.toAdd y i = 0 →
    ∃ a b c d e : Bool, y =
      (if a then A6.e0123 else 1) *
      (if b then G6.permAct 6 c2perm A6.e0123 else 1) *
      (if c then G6.permAct 6 c123 (G6.permAct 6 c2perm A6.e0123) else 1) *
      (if d then G6.permAct 6 c2perm (G6.permAct 6 c123 (G6.permAct 6 c2perm A6.e0123)) else 1) *
      (if e then G6.permAct 6 c012 (G6.permAct 6 c2perm (G6.permAct 6 c123
        (G6.permAct 6 c2perm A6.e0123))) else 1) := by
  decide +kernel

theorem c2_moves_V1 : G6.permAct 6 c2perm A6.e45 ≠ A6.e45 ∧
    G6.permAct 6 c2perm A6.e0123 ≠ A6.e0123 := by
  decide


variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_lift_odd (S : A6.Setting134 G T L V) {σ : Perm (Fin 6)}
    (hσA : σ ∈ alternatingGroup (Fin 6)) (hσ3 : σ ^ 3 = 1) :
    ∃ y ∈ L, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧
      ∃ hy : y ∈ normalizer (V : Set G), S.frame.ρ ⟨y, hy⟩ = σ := by
  obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L σ).2 hσA
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
  refine ⟨(g : G) ^ 4 ^ a, pow_mem hgL _, ⟨m, hm, ?_⟩, pow_mem g.2 _, ?_⟩
  · have h1 : ((g : G) ^ 4 ^ a) ^ m = ((g : G) ^ (2 ^ a * m)) ^ 2 ^ a := by
      rw [← pow_mul, ← pow_mul, show (4 : ℕ) ^ a = 2 ^ a * 2 ^ a by
        rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]]
      ring_nf
    rw [h1, ← hn, pow_orderOf_eq_one, one_pow]
  · have h1 : (⟨(g : G) ^ 4 ^ a, pow_mem g.2 _⟩ : ↥(normalizer (V : Set G))) = g ^ 4 ^ a :=
      Subtype.ext (by simp)
    rw [h1, map_pow, hgσ]
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ a = 3 * k + 1 := ⟨4 ^ a / 3, by
      have := Nat.div_add_mod (4 ^ a) 3
      rw [four_pow_mod_three] at this
      omega⟩
    rw [hk, pow_succ, pow_mul, hσ3, one_pow, one_mul]

omit [Finite G] in
theorem mem_oTwoRes_of_odd {X : Subgroup G} {y : G} (hy : y ∈ X) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) : y ∈ oTwoRes X :=
  subset_closure ⟨hy, m, hm, hym⟩

theorem s134_mem_normalizer_pre_iff (S : A6.Setting134 G T L V) (Y : Subgroup ↥(G6.coreMod 6))
    {g : G} (hg : g ∈ normalizer (V : Set G)) :
    g ∈ normalizer (S.pre Y : Set G) ↔
      ∀ y : ↥(G6.coreMod 6), y ∈ Y ↔ G6.coreAct 6 (S.frame.ρ ⟨g, hg⟩) y ∈ Y := by
  have hconj : ∀ v : ↥V, S.frame.ψ ⟨g * v * g⁻¹, (mem_normalizer_iff.mp hg v).mp v.2⟩ =
      G6.coreAct 6 (S.frame.ρ ⟨g, hg⟩) (S.frame.ψ v) := fun v => S.psi_conj ⟨g, hg⟩ v
  constructor
  · intro hN y
    obtain ⟨v, rfl⟩ := S.frame.ψ.surjective y
    have h1 := (mem_normalizer_iff.mp hN v)
    rw [S.mem_pre, S.mem_pre] at h1
    constructor
    · intro hy
      obtain ⟨h2, h3⟩ := h1.1 ⟨v.2, hy⟩
      rw [← hconj v]
      exact h3
    · intro hy
      rw [← hconj v] at hy
      obtain ⟨h2, h3⟩ := h1.2 ⟨(mem_normalizer_iff.mp hg v).mp v.2, hy⟩
      exact h3
  · intro hY
    rw [mem_normalizer_iff]
    intro x
    rw [S.mem_pre, S.mem_pre]
    constructor
    · rintro ⟨hx, hxY⟩
      refine ⟨(mem_normalizer_iff.mp hg x).mp hx, ?_⟩
      have := hconj ⟨x, hx⟩
      rw [this]
      exact (hY _).1 hxY
    · rintro ⟨hx', hxY⟩
      have hx : x ∈ V := (mem_normalizer_iff.mp hg x).mpr hx'
      refine ⟨hx, (hY _).2 ?_⟩
      rw [← hconj ⟨x, hx⟩]
      exact hxY

theorem s134_normalizer_V2_iff (S : A6.Setting134 G T L V) {g : G}
    (hg : g ∈ normalizer (V : Set G)) :
    g ∈ normalizer (v2Of S : Set G) ↔ A6.InP2 (S.frame.ρ ⟨g, hg⟩) := by
  rw [v2Of, s134_mem_normalizer_pre_iff S W2sub hg]
  obtain ⟨⟨h01, c01⟩, ⟨h23, c23⟩, ⟨h45, c45⟩⟩ := pv_W2
  constructor
  · intro h
    rw [inP2_iff]
    refine ⟨?_, ?_, ?_⟩
    · have := (h ⟨A6.pv 0 1, c01⟩).1 h01
      simpa [W2sub, G6.coreAct_coe] using this
    · have := (h ⟨A6.pv 2 3, c23⟩).1 h23
      simpa [W2sub, G6.coreAct_coe] using this
    · have := (h ⟨A6.pv 4 5, c45⟩).1 h45
      simpa [W2sub, G6.coreAct_coe] using this
  · intro hP y
    have hPinv : A6.InP2 (S.frame.ρ ⟨g, hg⟩)⁻¹ := A6.InP2.inv _ hP
    constructor
    · intro hy
      show InW2 ((G6.coreAct 6 (S.frame.ρ ⟨g, hg⟩) y : A6.P6))
      rw [G6.coreAct_coe]
      exact inW2_of_inP2 _ hP _ hy
    · intro hy
      have hy' : InW2 ((G6.coreAct 6 (S.frame.ρ ⟨g, hg⟩) y : A6.P6)) := hy
      rw [G6.coreAct_coe] at hy'
      have := inW2_of_inP2 _ hPinv _ hy'
      rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this

theorem s134_T_le_normalizer_V2 (S : A6.Setting134 G T L V) :
    T ≤ normalizer (v2Of S : Set G) := fun t ht =>
  (s134_normalizer_V2_iff S (S.frame.T_le ht)).2
    (inP2_of_inD6 _ (S.frame.T_D ⟨t, S.frame.T_le ht⟩ ht))

theorem s134_L2_le_normalizer_V2 (S : A6.Setting134 G T L V) :
    l2Of S ≤ normalizer (v2Of S : Set G) :=
  (oTwoRes_le _).trans inf_le_right

theorem s134_L2_le_L (S : A6.Setting134 G T L V) : l2Of S ≤ L :=
  (oTwoRes_le _).trans inf_le_left

theorem s134_exists_c2_mem_L2 (S : A6.Setting134 G T L V) :
    ∃ y ∈ l2Of S, ∃ hy : y ∈ normalizer (V : Set G), S.frame.ρ ⟨y, hy⟩ = c2perm := by
  obtain ⟨hA, h3, -, hP⟩ := c2perm_props
  obtain ⟨y, hyL, ⟨m, hm, hym⟩, hy, hρ⟩ := exists_lift_odd S hA h3
  refine ⟨y, mem_oTwoRes_of_odd (mem_inf.2 ⟨hyL, ?_⟩) hm hym, hy, hρ⟩
  rw [s134_normalizer_V2_iff S hy, hρ]
  exact hP

theorem s134_exists_mem_L1 (S : A6.Setting134 G T L V) {σ : Perm (Fin 6)}
    (hσA : σ ∈ alternatingGroup (Fin 6)) (hσ3 : σ ^ 3 = 1) (hσ : InA4 σ) :
    ∃ y ∈ L₁Of L (fsuV1 T V), ∃ hy : y ∈ normalizer (V : Set G), S.frame.ρ ⟨y, hy⟩ = σ := by
  obtain ⟨y, hyL, ⟨m, hm, hym⟩, hy, hρ⟩ := exists_lift_odd S hσA hσ3
  refine ⟨y, mem_oTwoRes_of_odd (mem_inf.2 ⟨hyL, ?_⟩) hm hym, hy, hρ⟩
  have hp : Pres45 (S.frame.ρ ⟨y, hy⟩) := by
    rw [hρ]
    exact Or.inl ⟨hσ.1, hσ.2.1⟩
  have hc : ∀ w ∈ fsuV1 T V, y * w * y⁻¹ = w := by
    intro w hw
    obtain ⟨hwV, hwW⟩ := S.mem_V1_iff.1 hw
    refine (S.conj_eq_iff ⟨y, hy⟩ ⟨w, hwV⟩).2 (Subtype.ext ?_)
    rw [G6.coreAct_coe]
    exact fix_W1_of_pres45 _ hp _ hwW
  refine centralizer_le_normalizer (fsuV1 T V) (mem_centralizer_iff.2 fun w hw => ?_)
  calc w * y = y * w * y⁻¹ * y := by rw [hc w hw]
    _ = y * w := by group

theorem s134_T_le_normalizer_L2 (S : A6.Setting134 G T L V) :
    T ≤ normalizer (l2Of S : Set G) := by
  intro t ht
  refine normalizer_le_normalizer_oTwoRes _ ?_
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.mp (S.T_le_NL ht) x
  have htN := s134_T_le_normalizer_V2 S ht
  have h2 : x ∈ normalizer (v2Of S : Set G) ↔ t * x * t⁻¹ ∈ normalizer (v2Of S : Set G) :=
    ⟨fun hx => mul_mem (mul_mem htN hx) (inv_mem htN), fun hx => by
      have := mul_mem (mul_mem (inv_mem htN) hx) htN
      simpa [mul_assoc] using this⟩
  simp only [mem_inf]
  exact ⟨fun ⟨a, b⟩ => ⟨h1.1 a, h2.1 b⟩, fun ⟨a, b⟩ => ⟨h1.2 a, h2.2 b⟩⟩

theorem s134_psi_comm (S : A6.Setting134 G T L V) {g : G} (hg : g ∈ normalizer (V : Set G))
    {v : G} (hv : v ∈ V) :
    ∃ h : ⁅v, g⁆ ∈ V, (S.frame.ψ ⟨⁅v, g⁆, h⟩ : A6.P6) =
      (S.frame.ψ ⟨v, hv⟩ : A6.P6) *
        (G6.permAct 6 (S.frame.ρ ⟨g, hg⟩) (S.frame.ψ ⟨v, hv⟩ : A6.P6))⁻¹ := by
  have hv' : g * v⁻¹ * g⁻¹ ∈ V := (mem_normalizer_iff.mp hg v⁻¹).mp (inv_mem hv)
  have hc : ⁅v, g⁆ ∈ V := by
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc g]
    exact mul_mem hv hv'
  refine ⟨hc, ?_⟩
  have h1 : S.frame.ψ ⟨⁅v, g⁆, hc⟩ = S.frame.ψ ⟨v, hv⟩ * S.frame.ψ ⟨g * v⁻¹ * g⁻¹, hv'⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show ⁅v, g⁆ = v * (g * v⁻¹ * g⁻¹)
    rw [commutatorElement_def]
    group
  have h2 : S.frame.ψ ⟨g * v⁻¹ * g⁻¹, hv'⟩ =
      (G6.coreAct 6 (S.frame.ρ ⟨g, hg⟩) (S.frame.ψ ⟨v, hv⟩))⁻¹ := by
    have := S.psi_conj ⟨g, hg⟩ ⟨v⁻¹, inv_mem hv⟩
    rw [show (⟨v⁻¹, inv_mem hv⟩ : ↥V) = (⟨v, hv⟩ : ↥V)⁻¹ from rfl, map_inv, map_inv] at this
    exact this
  rw [h1, h2, coe_mul, coe_inv, G6.coreAct_coe]
  rfl

theorem s134_exists_s1_mem_L2 (S : A6.Setting134 G T L V) :
    ∃ y ∈ l2Of S, ∃ hy : y ∈ normalizer (V : Set G),
      S.frame.ρ ⟨y, hy⟩ = swap 0 1 * swap 4 5 := by
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  obtain ⟨hcomm, hτD, hτA⟩ := comm_c2_tau
  obtain ⟨t, htT, htρ⟩ := S.frame.DA_T _ hτD hτA
  have htL2 := s134_T_le_normalizer_L2 S htT
  have hy : c * (t : G) * c⁻¹ * (t : G)⁻¹ ∈ l2Of S := by
    rw [show c * (t : G) * c⁻¹ * (t : G)⁻¹ = c * ((t : G) * c⁻¹ * (t : G)⁻¹) by group]
    exact mul_mem hcL2 ((mem_normalizer_iff.mp htL2 c⁻¹).mp (inv_mem hcL2))
  refine ⟨_, hy, mul_mem (mul_mem (mul_mem hcN t.2) (inv_mem hcN)) (inv_mem t.2), ?_⟩
  have e : (⟨c * (t : G) * c⁻¹ * (t : G)⁻¹, mul_mem (mul_mem (mul_mem hcN t.2) (inv_mem hcN))
      (inv_mem t.2)⟩ : ↥(normalizer (V : Set G))) = ⟨c, hcN⟩ * t * ⟨c, hcN⟩⁻¹ * t⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcρ, htρ, hcomm]

theorem s134_V_le_L2 (S : A6.Setting134 G T L V) : V ≤ l2Of S := by
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  obtain ⟨s, hsL2, hsN, hsρ⟩ := s134_exists_s1_mem_L2 S
  have hVL2 : V ≤ normalizer (l2Of S : Set G) := S.V_le_T.trans (s134_T_le_normalizer_L2 S)
  have hcomm_mem : ∀ {w y : G}, w ∈ V → y ∈ l2Of S → ⁅w, y⁆ ∈ l2Of S := by
    intro w y hw hy
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.mp (hVL2 hw) y).mp hy) (inv_mem hy)
  intro v hv
  obtain ⟨y, hy0, hyx⟩ := U0_decomp _ (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2)
  set w : G := (S.frame.ψ.symm ⟨y, G6.mem_coreMod.2 hy0⟩ : G) with hw
  have hwV : w ∈ V := (S.frame.ψ.symm _).2
  have hψw : (S.frame.ψ ⟨w, hwV⟩ : A6.P6) = y := by
    rw [show (⟨w, hwV⟩ : ↥V) = S.frame.ψ.symm ⟨y, G6.mem_coreMod.2 hy0⟩ from rfl,
      MulEquiv.apply_symm_apply]
  obtain ⟨h1, hψ1⟩ := s134_psi_comm S hcN hwV
  rw [hψw, hcρ] at hψ1
  have e02 : A6.pv 0 2 ∈ G6.coreMod 6 := G6.mem_coreMod.2 (by decide)
  set u : G := (S.frame.ψ.symm ⟨A6.pv 0 2, e02⟩ : G) with hu
  have huV : u ∈ V := (S.frame.ψ.symm _).2
  have hψu : (S.frame.ψ ⟨u, huV⟩ : A6.P6) = A6.pv 0 2 := by
    rw [show (⟨u, huV⟩ : ↥V) = S.frame.ψ.symm ⟨A6.pv 0 2, e02⟩ from rfl,
      MulEquiv.apply_symm_apply]
  obtain ⟨h2, hψ2⟩ := s134_psi_comm S hsN huV
  rw [hψu, hsρ, ← pv01_eq] at hψ2
  rcases hyx with hx | hx
  · have : (⟨v, hv⟩ : ↥V) = ⟨⁅w, c⁆, h1⟩ := S.frame.ψ.injective (Subtype.ext (by rw [hψ1, hx]))
    rw [show v = ⁅w, c⁆ from congrArg Subtype.val this]
    exact hcomm_mem hwV hcL2
  · have : (⟨v, hv⟩ : ↥V) = ⟨⁅u, s⁆, h2⟩ * ⟨⁅w, c⁆, h1⟩ :=
      S.frame.ψ.injective (Subtype.ext (by rw [map_mul, coe_mul, hψ1, hψ2, hx]))
    rw [show v = ⁅u, s⁆ * ⁅w, c⁆ from congrArg Subtype.val this]
    exact mul_mem (hcomm_mem huV hsL2) (hcomm_mem hwV hcL2)

theorem mul_mem_iff_of_card_two_mul {A B : Subgroup G} (hBA : B ≤ A)
    (hc : Nat.card ↥A = 2 * Nat.card ↥B) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b ∈ B ↔ (a ∈ B ↔ b ∈ B) := by
  have hidx : (B.subgroupOf A).index = 2 := by
    have h1 := relIndex_mul_card B A
    rw [inf_eq_left.2 hBA, hc] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have := mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simpa [mem_subgroupOf] using this

theorem s134_card_V2 (S : A6.Setting134 G T L V) : Nat.card ↥(v2Of S) = 8 := by
  rw [v2Of, S.card_pre, card_W2sub]

theorem s134_mem_V2_iff (S : A6.Setting134 G T L V) {x : G} :
    x ∈ v2Of S ↔ ∃ h : x ∈ V, InW2 (S.frame.ψ ⟨x, h⟩ : A6.P6) := by
  rw [v2Of, S.mem_pre]
  rfl

theorem s134_ZV_le_V2 (S : A6.Setting134 G T L V) : V ⊓ centralizer (L : Set G) ≤ v2Of S := by
  intro x hx
  rcases S.mem_ZV_iff.1 hx with rfl | rfl
  · exact one_mem _
  · refine (s134_mem_V2_iff S).2 ⟨S.zV_mem_V, ?_⟩
    rw [S.psi_zV]
    exact allOnes_W2

theorem s134_mem_ZV_iff_psi (S : A6.Setting134 G T L V) {x : G} (hx : x ∈ V) :
    x ∈ V ⊓ centralizer (L : Set G) ↔
      ((S.frame.ψ ⟨x, hx⟩ : A6.P6) = 1 ∨ (S.frame.ψ ⟨x, hx⟩ : A6.P6) = G6.allOnes 6) := by
  rw [S.mem_ZV_iff]
  constructor
  · rintro (rfl | rfl)
    · left
      have : (⟨1, hx⟩ : ↥V) = 1 := rfl
      rw [this, map_one]
      rfl
    · right
      rw [S.psi_zV]
  · rintro (h | h)
    · left
      have : (⟨x, hx⟩ : ↥V) = 1 := S.frame.ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      exact congrArg Subtype.val this
    · right
      have : (⟨x, hx⟩ : ↥V) = ⟨S.zV, S.zV_mem_V⟩ :=
        S.frame.ψ.injective (Subtype.ext (by rw [h, S.psi_zV]))
      exact congrArg Subtype.val this

theorem s134_V_le_pCoreOf_L2 (S : A6.Setting134 G T L V) : V ≤ pCoreOf 2 (l2Of S) := by
  have hVL2 := s134_V_le_L2 S
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 V _ hVL2 ?_
    S.isPGroup_V
  exact (normal_subgroupOf_iff_le_normalizer hVL2).2 ((s134_L2_le_L S).trans S.frame.L_le)

theorem s134_chief_L2 (S : A6.Setting134 G T L V) : HasTwoNoncentralChiefFactors (l2Of S) := by
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  have hL2V : l2Of S ≤ normalizer (V : Set G) := (s134_L2_le_L S).trans S.frame.L_le
  have hV2V : v2Of S ≤ V := S.pre_le_V _
  have hZV2 := s134_ZV_le_V2 S
  have hcZ := S.card_ZV
  have hc2 := s134_card_V2 S
  have hcV := S.card_V
  have hψc : ∀ {v : G} (hv : v ∈ V), (S.frame.ψ ⟨c * v * c⁻¹,
      (mem_normalizer_iff.mp hcN v).mp hv⟩ : A6.P6) = G6.permAct 6 c2perm (S.frame.ψ ⟨v, hv⟩) := by
    intro v hv
    rw [S.psi_conj ⟨c, hcN⟩ ⟨v, hv⟩, G6.coreAct_coe, hcρ]
  refine ⟨v2Of S, V ⊓ centralizer (L : Set G), V, v2Of S, s134_V_le_pCoreOf_L2 S,
    ⟨?_, s134_L2_le_normalizer_V2 S, ?_, ?_⟩, ⟨?_, hL2V, s134_L2_le_normalizer_V2 S, ?_⟩,
    le_rfl, ?_, ?_⟩
  ·
    refine lt_of_le_of_ne hZV2 fun h => ?_
    have := congrArg (fun X : Subgroup G => Nat.card ↥X) h
    simp only [hcZ, hc2] at this
    omega
  ·
    intro x hx
    have hxL : x ∈ L := s134_L2_le_L S hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    exact ((mem_centralizer_iff.mp (mem_inf.1 hy).2) x hxL).symm
  ·
    intro C hZC hCV hN
    have hCcard : Nat.card ↥C = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) := by
      have h1 := card_dvd_of_le hCV.le
      have h2 := card_dvd_of_le hZC.le
      have h3 : Nat.card ↥C ≠ Nat.card ↥(V ⊓ centralizer (L : Set G)) := fun h =>
        hZC.ne (eq_of_le_of_card_ge hZC.le h.le)
      have h4 : Nat.card ↥C ≠ Nat.card ↥(v2Of S) := fun h =>
        hCV.ne (eq_of_le_of_card_ge hCV.le h.ge)
      rw [hcZ] at h2 h3 ⊢
      rw [hc2] at h1 h4
      have h5 : Nat.card ↥C ∣ 8 := h1
      have h6 : Nat.card ↥C ≤ 8 := Nat.le_of_dvd (by norm_num) h5
      interval_cases h : Nat.card ↥C <;> simp_all
    obtain ⟨v, hvC, hvZ⟩ := IsConcreteLE.exists_of_lt hZC
    have hvV2 := hCV.le hvC
    obtain ⟨hvV, hvW⟩ := (s134_mem_V2_iff S).1 hvV2
    have hψv1 : (S.frame.ψ ⟨v, hvV⟩ : A6.P6) ≠ 1 := fun h =>
      hvZ ((s134_mem_ZV_iff_psi S hvV).2 (Or.inl h))
    have hψvΩ : (S.frame.ψ ⟨v, hvV⟩ : A6.P6) ≠ G6.allOnes 6 := fun h =>
      hvZ ((s134_mem_ZV_iff_psi S hvV).2 (Or.inr h))
    obtain ⟨hne1, hne2⟩ := c2_moves_W2 _ (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hvV⟩).2) hvW hψv1 hψvΩ
    have hcvC : c * v * c⁻¹ ∈ C := (mem_normalizer_iff.mp (hN hcL2) v).mp hvC
    have hcvV : c * v * c⁻¹ ∈ V := (mem_normalizer_iff.mp hcN v).mp hvV
    have hiff := mul_mem_iff_of_card_two_mul hZC.le hCcard hcvC (inv_mem hvC)
    rw [inv_mem_iff] at hiff
    by_cases h1 : c * v * c⁻¹ ∈ V ⊓ centralizer (L : Set G)
    · rcases (s134_mem_ZV_iff_psi S hcvV).1 h1 with h | h
      · rw [hψc hvV] at h
        exact hψv1 (c2_fix.2 _ h)
      · rw [hψc hvV] at h
        exact hψvΩ ((G6.permAct 6 c2perm).injective (h.trans c2_fix.1.symm))
    · have h2 : c * v * c⁻¹ * v⁻¹ ∈ V ⊓ centralizer (L : Set G) := hiff.2 (iff_of_false h1 hvZ)
      have h2V : c * v * c⁻¹ * v⁻¹ ∈ V := mul_mem hcvV (inv_mem hvV)
      have hψ2 : (S.frame.ψ ⟨c * v * c⁻¹ * v⁻¹, h2V⟩ : A6.P6) =
          G6.permAct 6 c2perm (S.frame.ψ ⟨v, hvV⟩) * (S.frame.ψ ⟨v, hvV⟩ : A6.P6)⁻¹ := by
        have e : (⟨c * v * c⁻¹ * v⁻¹, h2V⟩ : ↥V) = ⟨c * v * c⁻¹, hcvV⟩ * (⟨v, hvV⟩ : ↥V)⁻¹ := rfl
        rw [e, map_mul, map_inv, coe_mul, coe_inv, hψc hvV]
        rfl
      rcases (s134_mem_ZV_iff_psi S h2V).1 h2 with h | h
      · rw [hψ2] at h
        exact hne1 (mul_inv_eq_one.1 h)
      · rw [hψ2] at h
        exact hne2 ((mul_inv_eq_iff_eq_mul.1 h).trans (mul_comm _ _))
  ·
    refine lt_of_le_of_ne hV2V fun h => ?_
    have := congrArg (fun X : Subgroup G => Nat.card ↥X) h
    simp only [hc2, hcV] at this
    omega
  ·
    intro C hVC hCV hN
    have hCcard : Nat.card ↥C = 2 * Nat.card ↥(v2Of S) := by
      have h1 := card_dvd_of_le hCV.le
      have h2 := card_dvd_of_le hVC.le
      have h3 : Nat.card ↥C ≠ Nat.card ↥(v2Of S) := fun h =>
        hVC.ne (eq_of_le_of_card_ge hVC.le h.le)
      have h4 : Nat.card ↥C ≠ Nat.card ↥V := fun h =>
        hCV.ne (eq_of_le_of_card_ge hCV.le h.ge)
      rw [hc2] at h2 h3 ⊢
      rw [hcV] at h1 h4
      have h5 : Nat.card ↥C ∣ 32 := h1
      have h6 : Nat.card ↥C ≤ 32 := Nat.le_of_dvd (by norm_num) h5
      obtain ⟨k, hk⟩ := h2
      rw [hk] at h5 h6 h3 h4 ⊢
      have hk4 : k ≤ 4 := by omega
      interval_cases k <;> simp_all
    obtain ⟨v, hvC, hvV2⟩ := IsConcreteLE.exists_of_lt hVC
    have hvV := hCV.le hvC
    have hvW : ¬ InW2 (S.frame.ψ ⟨v, hvV⟩ : A6.P6) := fun h =>
      hvV2 ((s134_mem_V2_iff S).2 ⟨hvV, h⟩)
    have hcvC : c * v * c⁻¹ ∈ C := (mem_normalizer_iff.mp (hN hcL2) v).mp hvC
    have hcvV : c * v * c⁻¹ ∈ V := (mem_normalizer_iff.mp hcN v).mp hvV
    have hiff := mul_mem_iff_of_card_two_mul hVC.le hCcard hcvC (inv_mem hvC)
    rw [inv_mem_iff] at hiff
    by_cases h1 : c * v * c⁻¹ ∈ v2Of S
    · obtain ⟨h1V, h1W⟩ := (s134_mem_V2_iff S).1 h1
      have : (S.frame.ψ ⟨c * v * c⁻¹, h1V⟩ : A6.P6) =
          G6.permAct 6 c2perm (S.frame.ψ ⟨v, hvV⟩) := hψc hvV
      rw [this] at h1W
      exact c2_moves_U0' _ hvW h1W
    · have h2 : c * v * c⁻¹ * v⁻¹ ∈ v2Of S := hiff.2 (iff_of_false h1 hvV2)
      obtain ⟨h2V, h2W⟩ := (s134_mem_V2_iff S).1 h2
      have hψ2 : (S.frame.ψ ⟨c * v * c⁻¹ * v⁻¹, h2V⟩ : A6.P6) =
          G6.permAct 6 c2perm (S.frame.ψ ⟨v, hvV⟩) * (S.frame.ψ ⟨v, hvV⟩ : A6.P6)⁻¹ := by
        have e : (⟨c * v * c⁻¹ * v⁻¹, h2V⟩ : ↥V) = ⟨c * v * c⁻¹, hcvV⟩ * (⟨v, hvV⟩ : ↥V)⁻¹ := rfl
        rw [e, map_mul, map_inv, coe_mul, coe_inv, hψc hvV]
        rfl
      rw [hψ2] at h2W
      exact c2_moves_U0 _ (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hvV⟩).2) hvW h2W
  ·
    intro hle
    have e01 := pv_W2.1
    set v : G := (S.frame.ψ.symm ⟨A6.pv 0 1, e01.2⟩ : G) with hv
    have hvV : v ∈ V := (S.frame.ψ.symm _).2
    have hψv : (S.frame.ψ ⟨v, hvV⟩ : A6.P6) = A6.pv 0 1 := by
      rw [show (⟨v, hvV⟩ : ↥V) = S.frame.ψ.symm ⟨A6.pv 0 1, e01.2⟩ from rfl,
        MulEquiv.apply_symm_apply]
    have hvV2 : v ∈ v2Of S := (s134_mem_V2_iff S).2 ⟨hvV, by rw [hψv]; exact e01.1⟩
    have hmem := hle (commutator_mem_commutator hvV2 hcL2)
    obtain ⟨h1, hψ1⟩ := s134_psi_comm S hcN hvV
    rw [hψv, hcρ] at hψ1
    rcases (s134_mem_ZV_iff_psi S h1).1 hmem with h | h
    · rw [hψ1] at h
      exact c2_noncentral.1.1 h
    · rw [hψ1] at h
      exact c2_noncentral.1.2 h
  ·
    intro hle
    have e02 := c2_noncentral.2.2
    set v : G := (S.frame.ψ.symm ⟨A6.pv 0 2, e02⟩ : G) with hv
    have hvV : v ∈ V := (S.frame.ψ.symm _).2
    have hψv : (S.frame.ψ ⟨v, hvV⟩ : A6.P6) = A6.pv 0 2 := by
      rw [show (⟨v, hvV⟩ : ↥V) = S.frame.ψ.symm ⟨A6.pv 0 2, e02⟩ from rfl,
        MulEquiv.apply_symm_apply]
    have hmem := hle (commutator_mem_commutator hvV hcL2)
    obtain ⟨h1, hψ1⟩ := s134_psi_comm S hcN hvV
    rw [hψv, hcρ] at hψ1
    obtain ⟨h1V, h1W⟩ := (s134_mem_V2_iff S).1 hmem
    have : (S.frame.ψ ⟨⁅v, c⁆, h1V⟩ : A6.P6) = (S.frame.ψ ⟨⁅v, c⁆, h1⟩ : A6.P6) := rfl
    rw [this, hψ1] at h1W
    exact c2_noncentral.2.1 h1W

theorem s134_oTwoRes_L2T (S : A6.Setting134 G T L V) : oTwoRes (l2Of S ⊔ T) = l2Of S := by
  refine le_antisymm (oTwoRes_le_of_le_sup le_rfl (S.h13.faithful.1.1)
    (s134_T_le_normalizer_L2 S)) ?_
  calc l2Of S ≤ oTwoRes (l2Of S) := oTwoRes_le_oTwoRes _
    _ ≤ oTwoRes (l2Of S ⊔ T) := oTwoRes_mono' le_sup_left

theorem s134_cZ_L2T (S : A6.Setting134 G T L V)
    (hZ : Nat.card ↥(quasithinOmegaOneCenter T) =
      2 * Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G))) :
    cZ T (l2Of S ⊔ T) = quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) := by
  set Z := quasithinOmegaOneCenter T with hZdef
  have hle : Z ⊓ centralizer (L : Set G) ≤ cZ T (l2Of S ⊔ T) := by
    refine le_inf inf_le_left ?_
    rw [le_centralizer_iff, sup_le_iff]
    refine ⟨fun x hx => ?_, fun t ht => ?_⟩
    · rw [mem_centralizer_iff]
      intro y hy
      exact ((mem_centralizer_iff.mp (mem_inf.1 hy).2) x (s134_L2_le_L S hx)).symm
    · rw [mem_centralizer_iff]
      intro y hy
      exact ((mem_centralizer_iff.mp (s134_Z_le_center T (mem_inf.1 hy).1).2) t ht).symm
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  set z : G := (S.frame.ψ.symm ⟨A6.e45, A6.e45_mem⟩ : G) with hz
  have hzV1 : z ∈ fsuV1 T V := s134_e45_mem_V1 S
  have hzV : z ∈ V := (S.frame.ψ.symm _).2
  have hψz : (S.frame.ψ ⟨z, hzV⟩ : A6.P6) = A6.e45 := by
    rw [show (⟨z, hzV⟩ : ↥V) = S.frame.ψ.symm ⟨A6.e45, A6.e45_mem⟩ from rfl,
      MulEquiv.apply_symm_apply]
  have hzc : z ∉ cZ T (l2Of S ⊔ T) := by
    intro hzc
    have h1 : c * z = z * c :=
      (mem_centralizer_iff.mp (mem_inf.1 hzc).2) c (le_sup_left (b := T) hcL2)
    have h2 : c * z * c⁻¹ = z := by rw [h1, mul_inv_cancel_right]
    have h3 := (S.conj_eq_iff ⟨c, hcN⟩ ⟨z, hzV⟩).1 h2
    have h4 := congrArg Subtype.val h3
    rw [G6.coreAct_coe, hcρ, hψz] at h4
    exact c2_moves_V1.1 h4
  have hcZle : cZ T (l2Of S ⊔ T) ≤ Z := inf_le_left
  have h1 := relIndex_mul_relIndex (Z ⊓ centralizer (L : Set G)) (cZ T (l2Of S ⊔ T)) Z hle hcZle
  have h2 : (Z ⊓ centralizer (L : Set G)).relIndex Z = 2 := by
    have h3 := relIndex_mul_card (Z ⊓ centralizer (L : Set G)) Z
    rw [inf_eq_left.2 inf_le_left, hZ] at h3
    have hpos : 0 < Nat.card ↥(Z ⊓ centralizer (L : Set G)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  rw [h2] at h1
  have h4 : (cZ T (l2Of S ⊔ T)).relIndex Z ≠ 1 := by
    intro h
    rw [relIndex_eq_one] at h
    exact hzc (h (inf_le_right (a := V) hzV1))
  have h5 : (Z ⊓ centralizer (L : Set G)).relIndex (cZ T (l2Of S ⊔ T)) = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.1 (Dvd.intro _ h1) with h | h
    · exact h
    · exfalso
      rw [h] at h1
      omega
  rw [relIndex_eq_one] at h5
  exact le_antisymm h5 hle

theorem s134_le_centralizer_V (S : A6.Setting134 G T L V) {K : Subgroup G} {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z} : Set G)) (hL1 : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL2 : l2Of S ≤ normalizer (K : Set G)) : K ≤ centralizer (V : Set G) := by
  obtain ⟨y0, hy0L1, hy0N, hy0ρ⟩ := s134_exists_mem_L1 S c012_props.1 c012_props.2.1
    c012_props.2.2
  obtain ⟨y1, hy1L1, hy1N, hy1ρ⟩ := s134_exists_mem_L1 S c123_props.1 c123_props.2.1
    c123_props.2.2
  obtain ⟨c, hcL2, hcN, hcρ⟩ := s134_exists_c2_mem_L2 S
  set W := V ⊓ centralizer (K : Set G) with hW
  have hWn : ∀ g : G, g ∈ normalizer (V : Set G) → g ∈ normalizer (K : Set G) →
      ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hgV hgK w hw
    obtain ⟨hwV, hwK⟩ := mem_inf.1 hw
    refine mem_inf.2 ⟨(mem_normalizer_iff.mp hgV w).mp hwV, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
      simpa using this
    have h1 := (mem_centralizer_iff.mp hwK) _ hk'
    calc k * (g * w * g⁻¹) = g * ((g⁻¹ * k * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * w * g⁻¹ * k := by group
  have hy0 := hWn y0 hy0N (hL1 hy0L1)
  have hy1 := hWn y1 hy1N (hL1 hy1L1)
  have hc := hWn c hcN (hL2 hcL2)
  have hψconj : ∀ (g : G) (hg : g ∈ normalizer (V : Set G)) (w : G) (hw : w ∈ V),
      (S.frame.ψ ⟨g * w * g⁻¹, (mem_normalizer_iff.mp hg w).mp hw⟩ : A6.P6) =
        G6.permAct 6 (S.frame.ρ ⟨g, hg⟩) (S.frame.ψ ⟨w, hw⟩) := by
    intro g hg w hw
    rw [S.psi_conj ⟨g, hg⟩ ⟨w, hw⟩, G6.coreAct_coe]
  have hzV := (mem_inf.1 hz).1
  have hzW : z ∈ W := by
    refine mem_inf.2 ⟨hzV, ?_⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact (mem_centralizer_singleton_iff.mp (hKz hk))
  set P : A6.P6 → Prop := fun x => ∃ w ∈ W, ∃ hw : w ∈ V, (S.frame.ψ ⟨w, hw⟩ : A6.P6) = x
    with hPdef
  have hP1 : P 1 := ⟨1, one_mem _, one_mem _, by
    have : (⟨1, one_mem V⟩ : ↥V) = 1 := rfl
    rw [this, map_one]
    rfl⟩
  have hPmul : ∀ x y : A6.P6, P x → P y → P (x * y) := by
    rintro x y ⟨w₁, hw₁, hv₁, rfl⟩ ⟨w₂, hw₂, hv₂, rfl⟩
    refine ⟨w₁ * w₂, mul_mem hw₁ hw₂, mul_mem hv₁ hv₂, ?_⟩
    have : (⟨w₁ * w₂, mul_mem hv₁ hv₂⟩ : ↥V) = ⟨w₁, hv₁⟩ * ⟨w₂, hv₂⟩ := rfl
    rw [this, map_mul]
    rfl
  have hPif : ∀ (b : Bool) (x : A6.P6), P x → P (if b then x else 1) := by
    intro b x hx
    cases b
    · exact hP1
    · exact hx
  have hPconj : ∀ (g : G) (hg : g ∈ normalizer (V : Set G)), (∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      ∀ x : A6.P6, P x → P (G6.permAct 6 (S.frame.ρ ⟨g, hg⟩) x) := by
    rintro g hg hgW x ⟨w, hw, hwV, rfl⟩
    exact ⟨g * w * g⁻¹, hgW w hw, (mem_normalizer_iff.mp hg w).mp hwV, hψconj g hg w hwV⟩
  have hPc : ∀ x, P x → P (G6.permAct 6 c2perm x) := by
    intro x hx
    have := hPconj c hcN hc x hx
    rwa [hcρ] at this
  have hP0 : ∀ x, P x → P (G6.permAct 6 c012 x) := by
    intro x hx
    have := hPconj y0 hy0N hy0 x hx
    rwa [hy0ρ] at this
  have hPy1 : ∀ x, P x → P (G6.permAct 6 c123 x) := by
    intro x hx
    have := hPconj y1 hy1N hy1 x hx
    rwa [hy1ρ] at this
  have hall : ∀ v : G, v ∈ V → v ∈ W := by
    intro v hv
    obtain ⟨hzV', hzW1⟩ := S.mem_V1_iff.1 hz
    have hPz : P (S.frame.ψ ⟨z, hzV'⟩ : A6.P6) := ⟨z, hzW, hzV', rfl⟩
    have hψv := G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2
    have hPv : P (S.frame.ψ ⟨v, hv⟩ : A6.P6) := by
      rcases A6.W1_cases _ (S.frame.ψ ⟨z, hzV'⟩).2 hzW1 with h | h | h | h
      · exfalso
        apply hzL
        have : (⟨z, hzV'⟩ : ↥V) = 1 :=
          S.frame.ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
        rw [show z = 1 from congrArg Subtype.val this]
        exact one_mem _
      · exfalso
        apply hzL
        have : (⟨z, hzV'⟩ : ↥V) = ⟨S.zV, S.zV_mem_V⟩ :=
          S.frame.ψ.injective (Subtype.ext (by rw [h, S.psi_zV]))
        exact (S.mem_centralizer_L_iff ⟨z, hzV'⟩).2 (Or.inr this)
      · rw [h] at hPz
        obtain ⟨a, b, cc, d, e, hy⟩ := span_e0123 _ hψv
        rw [hy]
        exact hPmul _ _ (hPmul _ _ (hPmul _ _ (hPmul _ _ (hPif a _ hPz)
          (hPif b _ (hPc _ hPz))) (hPif cc _ (hPy1 _ (hPc _ hPz))))
          (hPif d _ (hPc _ (hPy1 _ (hPc _ hPz)))))
          (hPif e _ (hP0 _ (hPc _ (hPy1 _ (hPc _ hPz)))))
      · rw [h] at hPz
        obtain ⟨a, b, cc, d, e, hy⟩ := span_e45 _ hψv
        rw [hy]
        exact hPmul _ _ (hPmul _ _ (hPmul _ _ (hPmul _ _ (hPif a _ hPz)
          (hPif b _ (hPc _ hPz))) (hPif cc _ (hPc _ (hPc _ hPz))))
          (hPif d _ (hP0 _ (hPc _ hPz))))
          (hPif e _ (hPc _ (hP0 _ (hPc _ hPz))))
    obtain ⟨w, hwW, hwV, hψw⟩ := hPv
    have : (⟨w, hwV⟩ : ↥V) = ⟨v, hv⟩ := S.frame.ψ.injective (Subtype.ext hψw)
    rw [← show w = v from congrArg Subtype.val this]
    exact hwW
  intro k hk
  rw [mem_centralizer_iff]
  intro v hv
  exact ((mem_centralizer_iff.mp (mem_inf.1 (hall v hv)).2) k hk).symm

end CFSG.Quasithin.H13.U3
