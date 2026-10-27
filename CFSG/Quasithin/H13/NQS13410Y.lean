module

public import CFSG.Quasithin.H13.NQS13410V
public import CFSG.Quasithin.H13.NQS13410W

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

theorem stab45_e9 : ∀ a ∈ stab45List, ∀ b ∈ stab45List, a ^ 3 = 1 → b ^ 3 = 1 →
    ∃ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) ∧ (a ^ (i : ℕ) * b ^ (j : ℕ)) ^ 4 = 1 := by
  decide +kernel

theorem stab45_cube_or : ∀ a ∈ stab45List, a ^ 3 = 1 ∨ a ^ 4 = 1 := by decide +kernel

theorem l3_pow_four : ∀ a : L3.Γ, a ^ 8 = 1 → a ^ 4 = 1 := by decide +kernel

theorem l3_conj_pow {G : Type*} [Group G] (x y : G) (n : ℕ) :
    (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

@[expose] def pBase : L3.Vec := ![1, 0, 0]

theorem pBase_ne : pBase ≠ 0 := by decide

theorem l3Stab_e9_base : ∀ a : L3.Γ, L3.act a pBase = pBase → a ^ 3 = 1 →
    ∀ b : L3.Γ, L3.act b pBase = pBase → b ^ 3 = 1 →
    ∃ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) ∧ (a ^ (i : ℕ) * b ^ (j : ℕ)) ^ 4 = 1 := by
  decide +kernel

theorem l3Stab_cube_or_base : ∀ a : L3.Γ, L3.act a pBase = pBase → a ^ 3 = 1 ∨ a ^ 4 = 1 := by
  decide +kernel

theorem l3_eq_one_of_conj {x y : L3.Γ} (h : x⁻¹ * y * x = 1) : y = 1 :=
  calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem l3_fix_conj {x y : L3.Γ} (hy : L3.act y (L3.act x pBase) = L3.act x pBase) :
    L3.act (x⁻¹ * y * x) pBase = pBase := by
  rw [L3.act_mul, L3.act_mul, hy, L3.act_inv_act]

theorem l3_pow_conj {x y : L3.Γ} {n : ℕ} (h : y ^ n = 1) : (x⁻¹ * y * x) ^ n = 1 := by
  rw [l3_conj_pow, h, mul_one, inv_mul_cancel]

theorem l3Stab_e9 : ∀ p : L3.Vec, p ≠ 0 → ∀ a : L3.Γ, L3.act a p = p → a ^ 3 = 1 →
    ∀ b : L3.Γ, L3.act b p = p → b ^ 3 = 1 →
    ∃ i j : Fin 3, (i ≠ 0 ∨ j ≠ 0) ∧ (a ^ (i : ℕ) * b ^ (j : ℕ)) ^ 4 = 1 := by
  intro p hp a ha ha3 b hb hb3
  obtain ⟨x, rfl⟩ := L3.act_trans pBase p pBase_ne hp
  obtain ⟨i, j, hij, h⟩ := l3Stab_e9_base _ (l3_fix_conj ha) (l3_pow_conj ha3) _ (l3_fix_conj hb)
    (l3_pow_conj hb3)
  refine ⟨i, j, hij, l3_eq_one_of_conj (x := x) ?_⟩
  rw [l3_conj_pow, l3_conj_pow, show x⁻¹ * a ^ (i : ℕ) * x * (x⁻¹ * b ^ (j : ℕ) * x) =
    x⁻¹ * (a ^ (i : ℕ) * b ^ (j : ℕ)) * x by group, l3_conj_pow] at h
  exact h

theorem l3Stab_cube_or : ∀ p : L3.Vec, p ≠ 0 → ∀ a : L3.Γ, L3.act a p = p →
    a ^ 3 = 1 ∨ a ^ 4 = 1 := by
  intro p hp a ha
  obtain ⟨x, rfl⟩ := L3.act_trans pBase p pBase_ne hp
  rcases l3Stab_cube_or_base _ (l3_fix_conj ha) with h | h
  · rw [l3_conj_pow] at h
    exact Or.inl (l3_eq_one_of_conj h)
  · rw [l3_conj_pow] at h
    exact Or.inr (l3_eq_one_of_conj h)

theorem l3Stab_comm_base : ∀ γ : L3.Γ, L3.act γ pBase = pBase → γ ^ 3 = 1 → γ ≠ 1 →
    ∀ τ : L3.Γ, L3.act τ pBase = pBase → τ ^ 3 = 1 → τ ≠ 1 →
    ∀ β : L3.Γ, L3.act β pBase = pBase → (γ * β * γ⁻¹ * β⁻¹) ^ 4 = 1 →
      (β * τ * β⁻¹ * τ) ^ 4 ≠ 1 := by
  decide +kernel

theorem l3Stab_comm : ∀ p : L3.Vec, p ≠ 0 → ∀ γ : L3.Γ, L3.act γ p = p → γ ^ 3 = 1 → γ ≠ 1 →
    ∀ τ : L3.Γ, L3.act τ p = p → τ ^ 3 = 1 → τ ≠ 1 →
    ∀ β : L3.Γ, L3.act β p = p → (γ * β * γ⁻¹ * β⁻¹) ^ 4 = 1 →
      (β * τ * β⁻¹ * τ) ^ 4 ≠ 1 := by
  intro p hp γ hγ hγ3 hγ1 τ hτ hτ3 hτ1 β hβ hc hfin
  obtain ⟨x, rfl⟩ := L3.act_trans pBase p pBase_ne hp
  have hfix : ∀ y : L3.Γ, L3.act y (L3.act x pBase) = L3.act x pBase →
      L3.act (x⁻¹ * y * x) pBase = pBase :=
    fun y hy => by rw [L3.act_mul, L3.act_mul, hy, L3.act_inv_act]
  have hpow : ∀ (y : L3.Γ) (n : ℕ), y ^ n = 1 → (x⁻¹ * y * x) ^ n = 1 := fun y n h => by
    rw [l3_conj_pow, h, mul_one, inv_mul_cancel]
  have hne : ∀ y : L3.Γ, y ≠ 1 → x⁻¹ * y * x ≠ 1 := fun y hy h => hy (by
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group)
  refine l3Stab_comm_base _ (hfix γ hγ) (hpow γ 3 hγ3) (hne γ hγ1) _ (hfix τ hτ) (hpow τ 3 hτ3)
    (hne τ hτ1) _ (hfix β hβ) ?_ ?_
  · rw [show x⁻¹ * γ * x * (x⁻¹ * β * x) * (x⁻¹ * γ * x)⁻¹ * (x⁻¹ * β * x)⁻¹ =
      x⁻¹ * (γ * β * γ⁻¹ * β⁻¹) * x by group]
    exact hpow _ 4 hc
  · rw [show x⁻¹ * β * x * (x⁻¹ * τ * x) * (x⁻¹ * β * x)⁻¹ * (x⁻¹ * τ * x) =
      x⁻¹ * (β * τ * β⁻¹ * τ) * x by group]
    exact hpow _ 4 hfin

theorem pi_conj_inA4 : ∀ σ : Perm (Fin 6), U3.InA4 σ → σ ^ 3 = 1 →
    ((swap 0 1 * swap 4 5) * σ * (swap 0 1 * swap 4 5)⁻¹ * σ) ^ 2 = 1 := by
  decide +kernel

theorem pi_mem_a6D : swap (0 : Fin 6) 1 * swap 4 5 ∈ a6D := mem_a6D.2 (by decide)

theorem c012_inA4 : U3.InA4 (swap 0 1 * swap 1 2) ∧ (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 ∧
    swap (0 : Fin 6) 1 * swap 1 2 ≠ 1 := by
  decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_L1_three (S : A6.Setting134 G T L V)
    (hhat : A6.IsHatA6 L) :
    ∃ y : ↥(normalizer (V : Set G)), (y : G) ∈ L₁Of L (fsuV1 T V) ∧ (y : G) ^ 3 ^ 2 = 1 ∧
      S.frame.ρ y = swap 0 1 * swap 1 2 := by
  obtain ⟨h4, h3, h1⟩ := c012_inA4
  obtain ⟨x, hxL1, hx⟩ := U3.s134_L1_three S _ (mem_C3_of_inA4 _ h4 h3)
  obtain ⟨y, ⟨m, hm, hym⟩, hρy, k, hyk⟩ := exists_odd_part S.frame.ρ x (by rw [hx]; exact h3)
  have hyL1 : (y : G) ∈ L₁Of L (fsuV1 T V) := by
    rw [hyk]
    exact pow_mem hxL1 k
  have hyL : (y : G) ∈ L := (oTwoRes_le _).trans inf_le_left hyL1
  have ho2Z : A6.o2Z L = L ⊓ centralizer (V : Set G) := le_antisymm
    (le_inf A6.o2Z_le_L (U3.s134_o2Z_le_centralizer S)) (U3.s134_centralizer_le_o2Z S)
  have hy3 : (y : G) ^ 3 ∈ centralizer (V : Set G) := by
    have h1 : S.frame.ρ (y ^ 3) = 1 := by rw [map_pow, hρy, hx, h3]
    have := (U3.s134_rho_eq_one_iff S (y ^ 3)).1 h1
    simpa using this
  exact ⟨y, hyL1, pow_nine_eq_one (Or.inr (Or.inr (Or.inr hhat))) ho2Z hyL hm hym hy3,
    hρy.trans hx⟩

theorem mem_K_of_pow_three_of_a6 (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) {K W : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    (he6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) {x : G}
    (hx : x ∈ normalizer (K : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) : x ∈ K := by
  obtain ⟨e⟩ := he6
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 360 := by rw [Nat.card_congr e.toEquiv, h360]
  have hH : QTH13 G T K :=
    { simple := S.h13.simple
      nonabelian := S.h13.nonabelian
      qtke := S.h13.qtke
      sylow := S.h13.sylow
      faithful := hKf
      not_excluded := S.h13.not_excluded
      a5 := fun ⟨φ, hφs, hφk⟩ => by
        exfalso
        have h1 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
        rw [hφk, hc, h60] at h1
        omega }
  have hyp := U3.hyp1223_of h1332 hH hW
  have hcen : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inr ⟨e⟩))
  rcases h1228 G T K W hyp with h | h | ⟨⟨n, -, -, hz, -⟩, -⟩
  · rw [← h]
    exact subset_closure ⟨hx, k, hxk⟩
  · exfalso
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · exfalso
    rw [hcen, Subgroup.card_bot] at hz
    omega

theorem false_of_e9_perm (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K)
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (hker : ∀ g, ρ g = 1 → (g : G) ∈ centralizer (W : Set G))
    (hsign : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ K → Perm.sign (ρ g) = 1) {w₀ : G}
    (hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ → U3.Pres45 (ρ g))
    {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hxW : x ∈ normalizer (W : Set G))
    (hyW : y ∈ normalizer (W : Set G)) (hxL : x ∈ L) (hyL : y ∈ L) (hxw : x * w₀ * x⁻¹ = w₀)
    (hyw : y * w₀ * y⁻¹ = w₀) (hxV : x ∈ centralizer (V : Set G)) (hx3 : orderOf x = 3)
    (hy9 : y ^ 3 ^ 2 = 1) (hρy3 : S.frame.ρ ⟨y, S.frame.L_le hyL⟩ ^ 3 = 1)
    (hρy1 : S.frame.ρ ⟨y, S.frame.L_le hyL⟩ ≠ 1) : False := by
  set N := (K ⊓ normalizer (W : Set G)) ⊓ normalizer (V : Set G) with hN
  set φ : ↥N →* Perm (Fin 6) := ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))
  set ψ : ↥N →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion inf_le_right)
  have hφY : ∀ g : ↥N, (g : G) * w₀ * (g : G)⁻¹ = w₀ → φ g ∈ stab45List := fun g hg =>
    (mem_stab45_iff _).2 ⟨hsign _ (mem_inf.1 (mem_inf.1 g.2).1).1,
      hfix (Subgroup.inclusion (inf_le_left.trans inf_le_right) g) hg⟩
  have hker' : ∀ g : ↥N, φ g ^ 4 = 1 → ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : ((g : G) ^ 4) ∈ K ⊓ centralizer (W : Set G) := by
      refine mem_inf.2 ⟨pow_mem (mem_inf.1 (mem_inf.1 g.2).1).1 _, ?_⟩
      have h2 := hker (Subgroup.inclusion (inf_le_left.trans inf_le_right) g ^ 4) (by
        rw [map_pow]
        exact hg)
      simpa using h2
    obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hCK h1⟩
    refine ⟨s + 2, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hs
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s by ring,
      pow_mul]
    exact h3
  set xN : ↥N := ⟨x, mem_inf.2 ⟨mem_inf.2 ⟨hxK, hxW⟩, S.frame.L_le hxL⟩⟩
  set yN : ↥N := ⟨y, mem_inf.2 ⟨mem_inf.2 ⟨hyK, hyW⟩, S.frame.L_le hyL⟩⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
  have hφx3 : φ xN ^ 3 = 1 := by
    rw [← map_pow]
    have : xN ^ 3 = 1 := Subtype.ext (by simp [xN, hx3'])
    rw [this, map_one]
  have hφy3 : φ yN ^ 3 = 1 := by
    rcases stab45_cube_or _ (hφY yN hyw) with h | h
    · exact h
    · have h9 : φ yN ^ 3 ^ 2 = 1 := by
        rw [← map_pow]
        have : yN ^ 3 ^ 2 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hy9)
        rw [this, map_one]
      have hd1 := orderOf_dvd_of_pow_eq_one h
      have hd2 := orderOf_dvd_of_pow_eq_one h9
      have h1 : orderOf (φ yN) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 4 (3 ^ 2)) hd1 hd2
      rw [orderOf_eq_one_iff.1 h1, one_pow]
  have hx1 : xN ≠ 1 := fun h => by
    have : x = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hx3
    omega
  have hψx : ψ xN = 1 := (U3.s134_rho_eq_one_iff S _).2 hxV
  have hxN3 : xN ^ 3 = 1 := Subtype.ext (by simp [xN, hx3'])
  exact false_of_e9 φ ψ {σ | σ ∈ stab45List} (fun a ha b hb => stab45_e9 a ha b hb) hker'
    (hφY xN hxw) (hφY yN hyw) hφx3 hφy3 hxN3 hx1 hψx hρy3 hρy1

theorem not_a6_of_hat (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K)
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G))
    (he6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) [IsMulCommutative ↥W]
    (hmod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
        FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥))
    (hTW : T ≤ normalizer (W : Set G)) (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  obtain ⟨-, ⟨hTK, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hKW : K ≤ normalizer (W : Set G) := hW.2.2.1
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr he6))
  have hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rw [← ho2Z]
    exact o2Z_le_pCoreOf_of_center hZK
  obtain ⟨c, hcL0, hcL1, hc3, -, hcV⟩ := exists_hat_c S hhat
  obtain ⟨⟨y, hyNV⟩, hyL1, hy9, hρy⟩ := exists_L1_three S hhat
  have hc3' : c ^ 3 ^ 1 = 1 := by rw [pow_one, ← hc3, pow_orderOf_eq_one]
  have hcK : c ∈ K := mem_K_of_pow_three_of_a6 h1332 h1228 S hKf he6 hW (hL1K hcL1) hc3'
  have hyK : y ∈ K := mem_K_of_pow_three_of_a6 h1332 h1228 S hKf he6 hW (hL1K hyL1) hy9
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hred := twoReduced_R2 (K ⊔ T)
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by
    simpa using (hred.2.2.1.2 w (hW.1 w.2)))⟩
  have hNL : normalizer (W : Set G) ≤ normalizer (K : Set G) := by
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨W, hW.2.1, hW2, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
    have := huniqK M' hM' ((sup_le hKW hTW).trans hle)
    exact this ▸ hle
  have hZT : ∀ w ∈ W, w ∈ centralizer (T : Set G) → w ∈ quasithinOmegaOneCenter T := by
    intro w hw hwT
    have hwT' : w ∈ T := ((hW.1.trans (R2_le_pCoreOf (K ⊔ T))).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)) hw
    exact subset_closure ⟨⟨hwT', hwT⟩, hred.2.2.1.2 w (hW.1 hw)⟩
  have hcw : ∀ {w₀ : G}, w₀ ∈ quasithinOmegaOneCenter T → ∀ g ∈ L₁, g * w₀ * g⁻¹ = w₀ := by
    intro w₀ hw₀ g hg
    rw [← mem_centralizer_iff.mp (hL1Z hg) w₀ hw₀, mul_inv_cancel_right]
  rcases hmod with h6 | hc5
  · obtain ⟨R⟩ := exists_rawData4 hKW h6.1
    obtain ⟨F⟩ := exists_frame4 R hNL hKf.1.1 hTW hsyl
    have hfixiff : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
        (g : G) * w * (g : G)⁻¹ = w ↔ act4f (F.ρ g) (F.ψ w) = F.ψ w := by
      intro g w
      have h1 := F.equiv g w
      constructor
      · intro h
        have h2 : conjAct W g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
        rw [h2] at h1
        exact (congrArg Subtype.val h1).symm
      · intro h
        have h2 : F.ψ (conjAct W g w) = F.ψ w := by
          rw [h1]
          exact Subtype.ext h
        have h3 := congrArg Subtype.val (F.ψ.injective h2)
        rw [A5.conjAct_val] at h3
        exact h3
    set w₀ : ↥W := F.ψ.symm ⟨e0123, inW4_e0123⟩ with hw₀
    have hψw₀ : (F.ψ w₀ : P6) = e0123 := by rw [hw₀, MulEquiv.apply_symm_apply]
    have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      have hD := F.T_D ⟨t, F.T_le ht⟩ ht
      have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact act4f_e0123_of_inD6 _ hD)
      calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
        _ = w₀ * t := by rw [h1]
    have hw₀Z := hZT w₀ w₀.2 hw₀T
    have hker : ∀ g, F.ρ g = 1 → (g : G) ∈ centralizer (W : Set G) := fun g h1 =>
      mem_centralizer_iff.2 fun w hw => by
        have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1]; exact act4f_one _ (F.ψ ⟨w, hw⟩).2)
        calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
          _ = g * w := by group
    have hsign : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ K → Perm.sign (F.ρ g) = 1 :=
      fun g hg => Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, hg, rfl⟩)
    have hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ →
        U3.Pres45 (F.ρ g) := fun g hg => by
      have h1 := (hfixiff g w₀).1 hg
      rw [hψw₀] at h1
      exact pres45_of_act4f_fix _ h1
    exact false_of_e9_perm S hCK F.ρ hker hsign hfix hcK hyK (hL1W hcL1) (hL1W hyL1)
      (hL1L hcL1) (hL1L hyL1) (hcw hw₀Z c hcL1) (hcw hw₀Z y hyL1) hcV hc3 hy9
      (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyNV⟩ from
        rfl, hρy]; exact c012_inA4.2.1)
      (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyNV⟩ from
        rfl, hρy]; exact c012_inA4.2.2)
  · obtain ⟨R⟩ := exists_rawData6 hKW hc5.2.2
    obtain ⟨F⟩ := exists_frame5 R hNL hKf.1.1 hTW hsyl
    have hfixiff : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
        (g : G) * w * (g : G)⁻¹ = w ↔ G6.permAct 6 (F.ρ g) (F.ψ w) = F.ψ w := by
      intro g w
      have h1 := F.equiv g w
      constructor
      · intro h
        have h2 : conjAct W g w = w := Subtype.ext (by rw [A5.conjAct_val]; exact h)
        rw [h2] at h1
        exact (congrArg Subtype.val h1).symm
      · intro h
        have h2 : F.ψ (conjAct W g w) = F.ψ w := by
          rw [h1]
          exact Subtype.ext h
        have h3 := congrArg Subtype.val (F.ψ.injective h2)
        rw [A5.conjAct_val] at h3
        exact h3
    set w₀ : ↥W := F.ψ.symm ⟨e45, mem_coreMod_e45⟩ with hw₀
    have hψw₀ : ((F.ψ w₀ : ↥(G6.coreMod 6)) : G6.PermMod 6) = e45 := by
      rw [hw₀, MulEquiv.apply_symm_apply]
    have hw₀T : (w₀ : G) ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      have hD := F.T_D ⟨t, F.T_le ht⟩ ht
      have h1 := (hfixiff ⟨t, F.T_le ht⟩ w₀).2 (by rw [hψw₀]; exact permAct_e45_of_inD6 _ hD)
      calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
        _ = w₀ * t := by rw [h1]
    have hw₀Z := hZT w₀ w₀.2 hw₀T
    have hker : ∀ g, F.ρ g = 1 → (g : G) ∈ centralizer (W : Set G) := fun g h1 =>
      mem_centralizer_iff.2 fun w hw => by
        have h2 := (hfixiff g ⟨w, hw⟩).2 (by rw [h1, map_one]; rfl)
        calc w * g = g * w * (g : G)⁻¹ * g := by rw [h2]
          _ = g * w := by group
    have hsign : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ K → Perm.sign (F.ρ g) = 1 :=
      fun g hg => Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, hg, rfl⟩)
    have hfix : ∀ g : ↥(normalizer (W : Set G)), (g : G) * w₀ * (g : G)⁻¹ = w₀ →
        U3.Pres45 (F.ρ g) := fun g hg => by
      have h1 := (hfixiff g w₀).1 hg
      rw [hψw₀] at h1
      exact pres45_of_permAct_fix _ h1
    exact false_of_e9_perm S hCK F.ρ hker hsign hfix hcK hyK (hL1W hcL1) (hL1W hyL1)
      (hL1L hcL1) (hL1L hyL1) (hcw hw₀Z c hcL1) (hcw hw₀Z y hyL1) hcV hc3 hy9
      (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyNV⟩ from
        rfl, hρy]; exact c012_inA4.2.1)
      (by rw [show (⟨y, S.frame.L_le (hL1L hyL1)⟩ : ↥(normalizer (V : Set G))) = ⟨y, hyNV⟩ from
        rfl, hρy]; exact c012_inA4.2.2)

theorem false_of_e9_l3 (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K) (C : L3Coords K W) {p : L3.Vec}
    (hp0 : p ≠ 0) {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hxW : x ∈ normalizer (W : Set G))
    (hyW : y ∈ normalizer (W : Set G)) (hxL : x ∈ L) (hyL : y ∈ L)
    (hxp : L3.act (C.ρ ⟨x, hxW⟩) p = p) (hyp : L3.act (C.ρ ⟨y, hyW⟩) p = p)
    (hxV : x ∈ centralizer (V : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hρx3 : C.ρ ⟨x, hxW⟩ ^ 3 = 1) (hy3 : y ^ 3 = 1) (hyV : y ∉ centralizer (V : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (K ⊓ normalizer (W : Set G)) ⊓ normalizer (V : Set G) with hN
  set φ : ↥N →* L3.Γ := C.ρ.comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))
  set ψ : ↥N →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion inf_le_right)
  have hker' : ∀ g : ↥N, φ g ^ 4 = 1 → ∃ k : ℕ, g ^ 2 ^ k = 1 := by
    intro g hg
    have h1 : ((g : G) ^ 4) ∈ K ⊓ centralizer (W : Set G) := by
      refine mem_inf.2 ⟨pow_mem (mem_inf.1 (mem_inf.1 g.2).1).1 _, ?_⟩
      have h2 := (C.ker (Subgroup.inclusion (inf_le_left.trans inf_le_right) g ^ 4)).1 (by
        rw [map_pow]
        exact hg)
      simpa using h2
    obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hCK h1⟩
    refine ⟨s + 2, Subtype.ext ?_⟩
    have h3 := congrArg Subtype.val hs
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s by ring,
      pow_mul]
    exact h3
  set xN : ↥N := ⟨x, mem_inf.2 ⟨mem_inf.2 ⟨hxK, hxW⟩, S.frame.L_le hxL⟩⟩
  set yN : ↥N := ⟨y, mem_inf.2 ⟨mem_inf.2 ⟨hyK, hyW⟩, S.frame.L_le hyL⟩⟩
  have hxN3 : xN ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hx3)
  have hyN3 : yN ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hy3)
  have hxN1 : xN ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hψx : ψ xN = 1 := (U3.s134_rho_eq_one_iff S _).2 hxV
  have hψy1 : ψ yN ≠ 1 := fun h => hyV ((U3.s134_rho_eq_one_iff S _).1 h)
  have hψy3 : ψ yN ^ 3 = 1 := by rw [← map_pow, hyN3, map_one]
  have hφy3 : φ yN ^ 3 = 1 := by rw [← map_pow, hyN3, map_one]
  have hφx : φ xN = C.ρ ⟨x, hxW⟩ := rfl
  have hφy : φ yN = C.ρ ⟨y, hyW⟩ := rfl
  have hxY : φ xN ∈ {g : L3.Γ | L3.act g p = p} := by
    rw [Set.mem_ofPred_eq, hφx]
    exact hxp
  have hyY : φ yN ∈ {g : L3.Γ | L3.act g p = p} := by
    rw [Set.mem_ofPred_eq, hφy]
    exact hyp
  have hφx3 : φ xN ^ 3 = 1 := by
    rw [hφx]
    exact hρx3
  exact false_of_e9 φ ψ {g | L3.act g p = p}
    (fun a ha b hb ha3 hb3 => l3Stab_e9 p hp0 a ha ha3 b hb hb3) hker' hxY hyY hφx3 hφy3 hxN3
    hxN1 hψx hψy3 hψy1

theorem exists_odd_part_l3 (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K) (C : L3Coords K W) {p : L3.Vec}
    (hp0 : p ≠ 0) {x : G} (hxK : x ∈ K) (hxL1 : x ∈ L₁Of L (fsuV1 T V))
    (hxW : x ∈ normalizer (W : Set G)) (hxp : ∀ k : ℕ, ∀ h : x ^ k ∈ normalizer (W : Set G),
      L3.act (C.ρ ⟨x ^ k, h⟩) p = p)
    (hρLx : S.frame.ρ ⟨x, S.frame.L_le ((oTwoRes_le _).trans inf_le_left hxL1)⟩ ^ 2 = 1)
    (hρKx : C.ρ ⟨x, hxW⟩ ^ 4 ≠ 1) :
    ∃ x₀ : G, x₀ ∈ K ∧ x₀ ∈ L₁Of L (fsuV1 T V) ∧ ∃ hx₀W : x₀ ∈ normalizer (W : Set G),
      L3.act (C.ρ ⟨x₀, hx₀W⟩) p = p ∧ x₀ ∈ centralizer (V : Set G) ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧
        C.ρ ⟨x₀, hx₀W⟩ ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxV : x ∈ normalizer (V : Set G) :=
    S.frame.L_le ((oTwoRes_le _).trans inf_le_left hxL1)
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  set x₀ := x ^ 2 ^ a with hx₀
  have hx₀m : x₀ ^ m = 1 := by rw [hx₀, ← pow_mul, ← hn, pow_orderOf_eq_one]
  have hx₀W : x₀ ∈ normalizer (W : Set G) := pow_mem hxW _
  have hx₀V : x₀ ∈ normalizer (V : Set G) := pow_mem hxV _
  have hρLx₀ : S.frame.ρ ⟨x₀, hx₀V⟩ = 1 := by
    have e : (⟨x₀, hx₀V⟩ : ↥(normalizer (V : Set G))) = ⟨x, hxV⟩ ^ 2 ^ a :=
      Subtype.ext (by rw [Subgroup.coe_pow])
    have h2 : S.frame.ρ ⟨x₀, hx₀V⟩ ^ 2 = 1 := by
      rw [e, map_pow, ← pow_mul, mul_comm, pow_mul, hρLx, one_pow]
    have hm' : S.frame.ρ ⟨x₀, hx₀V⟩ ^ m = 1 := by
      rw [← map_pow]
      have : (⟨x₀, hx₀V⟩ : ↥(normalizer (V : Set G))) ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hx₀m)
      rw [this, map_one]
    have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 hm
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hm'))
  have hρKx₀ : C.ρ ⟨x₀, hx₀W⟩ ≠ 1 := by
    intro h1
    have e : (⟨x₀, hx₀W⟩ : ↥(normalizer (W : Set G))) = ⟨x, hxW⟩ ^ 2 ^ a :=
      Subtype.ext (by rw [Subgroup.coe_pow])
    rw [e, map_pow] at h1
    exact hρKx (l3_pow_four _ (l3_pow_eight (k := a) h1))
  have hx₀p : L3.act (C.ρ ⟨x₀, hx₀W⟩) p = p := hxp _ hx₀W
  have hρKx₀3 : C.ρ ⟨x₀, hx₀W⟩ ^ 3 = 1 := by
    rcases l3Stab_cube_or p hp0 _ hx₀p with h | h
    · exact h
    · exfalso
      have hm' : C.ρ ⟨x₀, hx₀W⟩ ^ m = 1 := by
        rw [← map_pow]
        have : (⟨x₀, hx₀W⟩ : ↥(normalizer (W : Set G))) ^ m = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hx₀m)
        rw [this, map_one]
      have hcop : Nat.Coprime 4 m := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
      exact hρKx₀ (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_of_pow_eq_one hm')))
  have hx₀K : x₀ ∈ K := pow_mem hxK _
  have hx₀3 : x₀ ^ 3 = 1 := by
    have h1 : x₀ ^ 3 ∈ K ⊓ centralizer (W : Set G) := by
      refine mem_inf.2 ⟨pow_mem hx₀K 3, ?_⟩
      have h2 : C.ρ (⟨x₀, hx₀W⟩ ^ 3) = 1 := by rw [map_pow, hρKx₀3]
      simpa using (C.ker _).1 h2
    obtain ⟨s, hs⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hCK h1⟩
    have hs' : (x₀ ^ 3) ^ 2 ^ s = 1 := by
      have := congrArg Subtype.val hs
      simpa using this
    have hm' : (x₀ ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx₀m, one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hx₀1 : x₀ ≠ 1 := fun h => hρKx₀ (by
    rw [show (⟨x₀, hx₀W⟩ : ↥(normalizer (W : Set G))) = 1 from Subtype.ext h, map_one])
  exact ⟨x₀, hx₀K, pow_mem hxL1 _, hx₀W, hx₀p, (U3.s134_rho_eq_one_iff S _).1 hρLx₀, hx₀3,
    hx₀1, hρKx₀3⟩

theorem exists_t_comm (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hTW : T ≤ normalizer (W : Set G)) (C : L3Coords K W) {c : G} (hcZ : c ∈ A6.o2Z L) (hcW : c ∈ normalizer (W : Set G)) :
    ∃ tV : ↥(normalizer (V : Set G)), (tV : G) ∈ T ⊓ L ∧
      S.frame.ρ tV = swap 0 1 * swap 4 5 ∧ ∃ htW : (tV : G) ∈ normalizer (W : Set G),
        (C.ρ ⟨c, hcW⟩ * C.ρ ⟨tV, htW⟩ * (C.ρ ⟨c, hcW⟩)⁻¹ * (C.ρ ⟨tV, htW⟩)⁻¹) ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨tV, htTL, hρt⟩ := exists_mem_T_inf_L S pi_mem_a6D
  have htW : (tV : G) ∈ normalizer (W : Set G) := hTW (mem_inf.1 htTL).1
  refine ⟨tV, htTL, hρt, htW, ?_⟩
  set t : G := (tV : G) with htdef
  have hct : c * t * c⁻¹ * t⁻¹ ∈ pCoreOf 2 L := by
    obtain ⟨-, h⟩ := mem_o2Z_iff.1 hcZ
    exact h t (mem_inf.1 htTL).2
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hct⟩
  have hk' : (c * t * c⁻¹ * t⁻¹) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hN : c * t * c⁻¹ * t⁻¹ ∈ normalizer (W : Set G) :=
    mul_mem (mul_mem (mul_mem hcW htW) (inv_mem hcW)) (inv_mem htW)
  have e : (⟨c * t * c⁻¹ * t⁻¹, hN⟩ : ↥(normalizer (W : Set G))) =
      ⟨c, hcW⟩ * ⟨t, htW⟩ * ⟨c, hcW⟩⁻¹ * ⟨t, htW⟩⁻¹ := rfl
  refine l3_pow_four _ (l3_pow_eight (k := k) ?_)
  have h1 : (⟨c * t * c⁻¹ * t⁻¹, hN⟩ : ↥(normalizer (W : Set G))) ^ 2 ^ k = 1 :=
    Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hk')
  have h2 := congrArg C.ρ h1
  rw [map_pow, e, map_one, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  exact h2

theorem not_l32_of_hat_of_not_mem (h1332 : Stmt13_3_2)
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1W : L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hWR : W ≤ reducedAggregate (K ⊔ T)) (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    {y : G} (hyK : y ∈ K) (hyL1 : y ∈ L₁Of L (fsuV1 T V)) (hy3 : y ^ 3 = 1)
    (hyW : y ∉ centralizer (W : Set G)) (hyV : y ∉ centralizer (V : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hCK : K ⊓ centralizer (W : Set G) ≤ pCoreOf 2 K := by
    rw [← ho2Z]
    exact o2Z_le_pCoreOf_of_center hZK
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  obtain ⟨c, hcL0, hcL1, hc3, hcZ, hcV⟩ := exists_hat_c S hhat
  by_cases hcW : c ∈ centralizer (W : Set G)
  · exact false_of_l0_le_centralizer S hhat hKM hTK hTsyl ((U3.s134_l0_le_L1 S).trans hL1K) hKW
      hTW hCK hcL0 hc3 hcW
  have hred := twoReduced_R2 (K ⊔ T)
  have hWT : W ≤ T := (hWR.trans (R2_le_pCoreOf (K ⊔ T))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hW1 : W ≠ ⊥ := by
    intro h
    have h8 := card_eq_eight_of_l32 hnat
    rw [h, Subgroup.card_bot] at h8
    omega
  obtain ⟨u, huW, huT, hu1⟩ := exists_mem_centralizer_ne_one hKf.1.1 hWT hTW hW1
  have huZ : u ∈ quasithinOmegaOneCenter T :=
    subset_closure ⟨⟨hWT huW, huT⟩, hred.2.2.1.2 u (hWR huW)⟩
  obtain ⟨C⟩ := exists_l3Coords hnat
  set uW : ↥W := ⟨u, huW⟩ with huWdef
  set p := C.c uW with hp
  have hp0 : p ≠ 0 := C.c_ne_zero (fun h => hu1 (congrArg Subtype.val h))
  have hfixp : ∀ g : ↥(normalizer (W : Set G)), (g : G) * u * (g : G)⁻¹ = u →
      L3.act (C.ρ g) p = p := fun g hg => (C.fix_iff g uW).1 hg
  have hL1u : ∀ g ∈ L₁, g * u * g⁻¹ = u := fun g hg => by
    rw [← mem_centralizer_iff.mp (hL1Z hg) u huZ, mul_inv_cancel_right]
  have hcW' : c ∈ normalizer (W : Set G) := hL1W hcL1
  obtain ⟨tV, htTL, hρt, htW, hγβ⟩ := exists_t_comm S hTW C hcZ hcW'
  set t : G := (tV : G) with htdef
  have htT : t ∈ T := (mem_inf.1 htTL).1
  have htK : t ∈ normalizer (K : Set G) := hTK htT
  have htL1 : t ∈ normalizer (L₁ : Set G) := U3.s134_T_le_normalizer_L1 S htT
  have hyW' : y ∈ normalizer (W : Set G) := hL1W hyL1
  have hc3' : c ^ 3 = 1 := by rw [← hc3, pow_orderOf_eq_one]
  have hγ3 : C.ρ ⟨c, hcW'⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcW'⟩ : ↥(normalizer (W : Set G))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hc3')
    rw [this, map_one]
  have hγ1 : C.ρ ⟨c, hcW'⟩ ≠ 1 := fun h => hcW ((C.ker _).1 h)
  have hτ3 : C.ρ ⟨y, hyW'⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyW'⟩ : ↥(normalizer (W : Set G))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hy3)
    rw [this, map_one]
  have hτ1 : C.ρ ⟨y, hyW'⟩ ≠ 1 := fun h => hyW ((C.ker _).1 h)
  have hγp := hfixp ⟨c, hcW'⟩ (hL1u c hcL1)
  have hτp := hfixp ⟨y, hyW'⟩ (hL1u y hyL1)
  have hβp : L3.act (C.ρ ⟨t, htW⟩) p = p :=
    hfixp _ (by rw [mem_centralizer_iff.mp huT t htT, mul_inv_cancel_right])
  set x := t * y * t⁻¹ * y with hxdef
  have hxL1 : x ∈ L₁ := mul_mem ((mem_normalizer_iff.mp htL1 y).mp hyL1) hyL1
  have hxK : x ∈ K := mul_mem ((mem_normalizer_iff.mp htK y).mp hyK) hyK
  have hxW : x ∈ normalizer (W : Set G) := hL1W hxL1
  have hyV' : y ∈ normalizer (V : Set G) := S.frame.L_le (hL1L hyL1)
  have hρLx : S.frame.ρ ⟨x, S.frame.L_le ((oTwoRes_le _).trans inf_le_left hxL1)⟩ ^ 2 = 1 := by
    have e : (⟨x, S.frame.L_le ((oTwoRes_le _).trans inf_le_left hxL1)⟩ :
        ↥(normalizer (V : Set G))) = tV * ⟨y, hyV'⟩ * tV⁻¹ * ⟨y, hyV'⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hρt]
    refine pi_conj_inA4 _ (U3.s134_rho_L1 S hyV' hyL1) ?_
    rw [← map_pow]
    have : (⟨y, hyV'⟩ : ↥(normalizer (V : Set G))) ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hy3)
    rw [this, map_one]
  have hρKx : C.ρ ⟨x, hxW⟩ ^ 4 ≠ 1 := by
    have e : (⟨x, hxW⟩ : ↥(normalizer (W : Set G))) =
        ⟨t, htW⟩ * ⟨y, hyW'⟩ * ⟨t, htW⟩⁻¹ * ⟨y, hyW'⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv]
    exact l3Stab_comm p hp0 _ hγp hγ3 hγ1 _ hτp hτ3 hτ1 _ hβp hγβ
  have hxp : ∀ k : ℕ, ∀ h : x ^ k ∈ normalizer (W : Set G), L3.act (C.ρ ⟨x ^ k, h⟩) p = p :=
    fun k h => hfixp _ (hL1u _ (pow_mem hxL1 k))
  obtain ⟨x₀, hx₀K, hx₀L1, hx₀W, hx₀p, hx₀V, hx₀3, hx₀1, hρx₀3⟩ :=
    exists_odd_part_l3 S hCK C hp0 hxK hxL1 hxW hxp hρLx hρKx
  exact false_of_e9_l3 S hCK C hp0 hx₀K hyK hx₀W hyW' (hL1L hx₀L1) (hL1L hyL1) hx₀p hτp hx₀V
    hx₀3 hx₀1 hρx₀3 hy3 hyV

end CFSG.Quasithin.H13.NQS134
