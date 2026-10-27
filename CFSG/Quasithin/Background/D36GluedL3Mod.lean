module

public import CFSG.Quasithin.Background.D36GluedL3Fin
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.L3Mod

open CFSG.Quasithin.L3 CFSG.Quasithin.L3Fin

theorem card_Γ : Nat.card Γ = 168 := by
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide +kernel

theorem seven_le_index (H : Subgroup Γ) (hH : H ≠ ⊤) : 7 ≤ H.index := by
  haveI : IsSimpleGroup Γ := CFSG.ClassicalInvolution.Q3.TL4.isSimpleGroup_sl3Two
  have hdvd := H.index_normalCore_dvd_factorial_index
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · rw [h, Subgroup.index_bot, card_Γ] at hdvd
    have h7 : 7 ∣ Nat.factorial H.index := Nat.dvd_trans (by norm_num) hdvd
    exact (Nat.Prime.dvd_factorial (by norm_num)).mp h7
  · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH

inductive Attain : ℕ → Prop
  | zero : Attain 0
  | add {n d : ℕ} : Attain n → d ∣ 168 → 7 ≤ d → Attain (n + d)

theorem Attain.small {n : ℕ} (h : Attain n) (h17 : n ≤ 17) :
    n = 0 ∨ n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
  induction h with
  | zero => exact Or.inl rfl
  | @add n d _ hd h7 ih =>
    have hn := ih (by omega)
    have hd17 : d ≤ 17 := by omega
    have hd' : d = 7 ∨ d = 8 ∨ d = 12 ∨ d = 14 := by
      interval_cases d <;> omega
    omega

section Action

variable {M : Type} [CommGroup M] [Finite M] [MulDistribMulAction Γ M]

theorem stab_ne_top (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1) {x : M} (hx : x ≠ 1) :
    MulAction.stabilizer Γ x ≠ ⊤ := fun h =>
  hx (hfix x fun g => by
    have : g ∈ MulAction.stabilizer Γ x := by rw [h]; trivial
    exact this)

theorem seven_le_card_orbit (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1) {x : M} (hx : x ≠ 1) :
    7 ≤ (MulAction.orbit Γ x).ncard := by
  rw [← MulAction.index_stabilizer]
  exact seven_le_index _ (stab_ne_top hfix hx)

theorem card_orbit_dvd (x : M) : (MulAction.orbit Γ x).ncard ∣ 168 := by
  rw [← MulAction.index_stabilizer, ← card_Γ]
  exact Subgroup.index_dvd_card _

theorem attain_card (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1) (R : Set M)
    (hR1 : ∀ x ∈ R, x ≠ 1) (hinv : ∀ (g : Γ), ∀ x ∈ R, g • x ∈ R) : Attain R.ncard := by
  induction' hn : R.ncard using Nat.strong_induction_on with n ih generalizing R
  by_cases hne : R.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hOR : MulAction.orbit Γ x ⊆ R := by
      rintro _ ⟨g, rfl⟩
      exact hinv g x hx
    have h7 := seven_le_card_orbit hfix (hR1 x hx)
    have hdvd := card_orbit_dvd x
    have hle : (MulAction.orbit Γ x).ncard ≤ R.ncard := Set.ncard_le_ncard hOR
    have hdiff : (R \ MulAction.orbit Γ x).ncard = R.ncard - (MulAction.orbit Γ x).ncard :=
      Set.ncard_diff hOR
    have hat := ih (R \ MulAction.orbit Γ x).ncard (by omega) (R \ MulAction.orbit Γ x)
      (fun z hz => hR1 z hz.1) (fun g z hz => by
        refine ⟨hinv g z hz.1, fun hgz => hz.2 ?_⟩
        obtain ⟨h, hh⟩ := hgz
        have hh' : h • x = g • z := hh
        exact ⟨g⁻¹ * h, by show (g⁻¹ * h) • x = z; rw [mul_smul, hh', inv_smul_smul]⟩) rfl
    have := Attain.add hat hdvd h7
    rw [← hn]
    convert this using 1
    omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [Set.ncard_empty] at hn
    rw [← hn]
    exact Attain.zero

theorem compl_attain (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1) (S : Set M)
    (hS1 : ∀ x ∈ S, x ≠ 1) (hSinv : ∀ (g : Γ), ∀ x ∈ S, g • x ∈ S) :
    S.ncard ≤ Nat.card M - 1 ∧ Attain (Nat.card M - 1 - S.ncard) := by
  have hsub : S ⊆ Set.univ \ {1} := fun x hx => ⟨Set.mem_univ x, hS1 x hx⟩
  have hc : (Set.univ \ {(1 : M)}).ncard = Nat.card M - 1 := by
    rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  have hle : S.ncard ≤ Nat.card M - 1 := by
    rw [← hc]
    exact Set.ncard_le_ncard hsub
  refine ⟨hle, ?_⟩
  have hR := attain_card hfix ((Set.univ \ {(1 : M)}) \ S) (fun x hx => hx.1.2)
    (fun g x hx => by
      refine ⟨⟨Set.mem_univ _, fun h1 => hx.1.2 ?_⟩, fun hgx => hx.2 ?_⟩
      · have : g⁻¹ • (g • x) = g⁻¹ • (1 : M) := by rw [Set.mem_singleton_iff.mp h1]
        simpa using this
      · have : g⁻¹ • (g • x) ∈ S := hSinv g⁻¹ _ hgx
        simpa using this)
  rw [Set.ncard_diff hsub, hc] at hR
  exact hR

end Action

theorem card_cases {n : ℕ} (hpow : ∃ k, n = 2 ^ k) (h8 : 8 < n) (h32 : n ≤ 32) :
    n = 16 ∨ n = 32 := by
  obtain ⟨k, rfl⟩ := hpow
  have hk : k < 6 := by
    by_contra h
    push Not at h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases k <;> revert h8 h32 <;> decide

structure Datum where
  H₁ : Subgroup Γ
  H₂ : Subgroup Γ
  hs : Fin 3 → Γ
  card₁ : Nat.card H₁ = 24
  card₂ : Nat.card H₂ = 24
  hs_zero : hs 0 = 1
  two_trans : ∀ g : Γ, g ∈ H₁ ∨ ∃ a ∈ H₁, (hs 1)⁻¹ * (a⁻¹ * g) ∈ H₁
  distinct : ∀ i j : Fin 3, (hs i)⁻¹ * hs j ∈ H₁ → i = j
  closed : ∀ q ∈ H₂, ∀ i : Fin 3, ∃ j : Fin 3, (hs j)⁻¹ * (q * hs i) ∈ H₁
  not_conj : ∀ g : Γ, ∃ a ∈ H₁, g * a * g⁻¹ ∉ H₂

def Datum.P : Datum where
  H₁ := subP
  H₂ := subQ
  hs := hsP
  card₁ := card_subP
  card₂ := card_subQ
  hs_zero := hsP_zero
  two_trans := P_two_trans
  distinct := P_distinct
  closed := fun q hq => P_closed q hq
  not_conj := fun g => by
    obtain ⟨a, ha, h⟩ := P_not_conj g
    exact ⟨a, ha, h⟩

def Datum.Q : Datum where
  H₁ := subQ
  H₂ := subP
  hs := hsQ
  card₁ := card_subQ
  card₂ := card_subP
  hs_zero := hsQ_zero
  two_trans := Q_two_trans
  distinct := Q_distinct
  closed := fun q hq => Q_closed q hq
  not_conj := fun g => by
    obtain ⟨a, ha, h⟩ := Q_not_conj g
    exact ⟨a, ha, h⟩

section Fano

variable {M : Type} [CommGroup M] [Finite M] [MulDistribMulAction Γ M]

theorem orbit_ne_one {v : M} (hv : v ≠ 1) {x : M} (hx : x ∈ MulAction.orbit Γ v) : x ≠ 1 := by
  obtain ⟨g, rfl⟩ := hx
  intro h
  apply hv
  have h' : g • v = 1 := h
  have : g • v = g • (1 : M) := by rw [smul_one]; exact h'
  exact smul_left_cancel g this

theorem smul_mem_orbit' {v x : M} (g : Γ) (hx : x ∈ MulAction.orbit Γ v) :
    g • x ∈ MulAction.orbit Γ v := by
  obtain ⟨h, rfl⟩ := hx
  exact ⟨g * h, mul_smul g h v⟩

theorem Datum.card_orbit (D : Datum) {v : M} (hstab : MulAction.stabilizer Γ v = D.H₁) :
    (MulAction.orbit Γ v).ncard = 7 := by
  rw [← MulAction.index_stabilizer, hstab]
  have := D.H₁.index_mul_card
  rw [D.card₁, card_Γ] at this
  omega

theorem Datum.line (D : Datum) (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hpow : ∃ k, Nat.card M = 2 ^ k) (h8 : 8 < Nat.card M) (h32 : Nat.card M ≤ 32)
    {v : M} (hv : v ≠ 1) (hstab : MulAction.stabilizer Γ v = D.H₁) :
    (D.hs 0 • v) * (D.hs 1 • v) * (D.hs 2 • v) = 1 := by
  have hq := card_cases hpow h8 h32
  set f : Fin 3 → M := fun i => D.hs i • v with hf
  set s : M := f 0 * f 1 * f 2 with hs
  have hfixs : ∀ q ∈ D.H₂, q • s = s := by
    intro q hq
    choose σ hσ using D.closed q hq
    have hqf : ∀ i, q • f i = f (σ i) := by
      intro i
      have hk : (D.hs (σ i))⁻¹ * (q * D.hs i) ∈ MulAction.stabilizer Γ v := by
        rw [hstab]; exact hσ i
      have hk' := MulAction.mem_stabilizer_iff.mp hk
      simp only [hf]
      rw [← mul_smul]
      calc (q * D.hs i) • v = (D.hs (σ i) * ((D.hs (σ i))⁻¹ * (q * D.hs i))) • v := by
            rw [mul_inv_cancel_left]
        _ = D.hs (σ i) • (((D.hs (σ i))⁻¹ * (q * D.hs i)) • v) := mul_smul _ _ _
        _ = D.hs (σ i) • v := by rw [hk']
    have hinj : Function.Injective σ := by
      intro i j hij
      have h1 : q • f i = q • f j := by rw [hqf, hqf, hij]
      have h2 : f i = f j := smul_left_cancel q h1
      apply D.distinct i j
      rw [← hstab, MulAction.mem_stabilizer_iff, mul_smul]
      have h2' : D.hs i • v = D.hs j • v := h2
      rw [← h2', inv_smul_smul]
    have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
    rw [hs, smul_mul', smul_mul', hqf, hqf, hqf]
    have := hbij.prod_comp f
    simp only [Fin.prod_univ_three] at this
    exact this
  show s = 1
  by_contra hne
  have hst : D.H₂ ≤ MulAction.stabilizer Γ s := fun q hq => hfixs q hq
  have hdvd1 : 24 ∣ Nat.card (MulAction.stabilizer Γ s) := by
    have := Subgroup.card_dvd_of_le hst
    rwa [D.card₂] at this
  have hdvd2 : Nat.card (MulAction.stabilizer Γ s) ∣ 168 := by
    have := Subgroup.card_subgroup_dvd_card (MulAction.stabilizer Γ s)
    rwa [card_Γ] at this
  have hne168 : Nat.card (MulAction.stabilizer Γ s) ≠ 168 := fun h => by
    apply stab_ne_top hfix hne
    apply Subgroup.eq_top_of_card_eq
    rw [h, card_Γ]
  have hcard24 : Nat.card (MulAction.stabilizer Γ s) = 24 := by
    obtain ⟨k, hk⟩ := hdvd1
    rw [hk] at hdvd2 hne168 ⊢
    have hle := Nat.le_of_dvd (by norm_num) hdvd2
    have hk7 : k ≤ 7 := by omega
    interval_cases k <;> omega
  have hsstab : D.H₂ = MulAction.stabilizer Γ s :=
    Subgroup.eq_of_le_of_card_ge hst (by rw [hcard24, D.card₂])
  have hsnot : s ∉ MulAction.orbit Γ v := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, hga⟩ := D.not_conj g
    apply hga
    rw [hsstab, MulAction.mem_stabilizer_iff]
    have hg' : g • v = s := hg
    have hav : a • v = v := by
      have : a ∈ MulAction.stabilizer Γ v := by rw [hstab]; exact ha
      exact MulAction.mem_stabilizer_iff.mp this
    calc (g * a * g⁻¹) • s = (g * a * g⁻¹) • (g • v) := by rw [hg']
      _ = (g * a) • v := by rw [← mul_smul, mul_assoc (g * a), inv_mul_cancel, mul_one]
      _ = g • (a • v) := mul_smul _ _ _
      _ = g • v := by rw [hav]
      _ = s := hg'
  have hO₁ : (MulAction.orbit Γ v).ncard = 7 := D.card_orbit hstab
  have hO₂ : (MulAction.orbit Γ s).ncard = 7 := by
    rw [← MulAction.index_stabilizer, ← hsstab]
    have := D.H₂.index_mul_card
    rw [D.card₂, card_Γ] at this
    omega
  have hdisj : Disjoint (MulAction.orbit Γ v) (MulAction.orbit Γ s) := by
    rw [Set.disjoint_left]
    rintro z ⟨g, hg⟩ ⟨h, hh⟩
    apply hsnot
    have hg' : g • v = z := hg
    have hh' : h • s = z := hh
    exact ⟨h⁻¹ * g, by show (h⁻¹ * g) • v = s; rw [mul_smul, hg', ← hh', inv_smul_smul]⟩
  have hunion : (MulAction.orbit Γ v ∪ MulAction.orbit Γ s).ncard = 14 := by
    rw [Set.ncard_union_eq hdisj, hO₁, hO₂]
  obtain ⟨hle, hat⟩ := compl_attain hfix (MulAction.orbit Γ v ∪ MulAction.orbit Γ s)
    (fun x hx => hx.elim (orbit_ne_one hv) (orbit_ne_one hne))
    (fun g x hx => hx.elim (fun h => Or.inl (smul_mem_orbit' g h))
      (fun h => Or.inr (smul_mem_orbit' g h)))
  rw [hunion] at hle hat
  rcases hq with hq | hq <;> rw [hq] at hat
  · have := hat.small (by norm_num)
    omega
  · have := hat.small (by norm_num)
    omega

theorem Datum.closed_orbit (D : Datum) (hM : ∀ x : M, x ^ 2 = 1) {v : M}
    (hstab : MulAction.stabilizer Γ v = D.H₁)
    (hline : (D.hs 0 • v) * (D.hs 1 • v) * (D.hs 2 • v) = 1) {a b : M}
    (ha : a ∈ MulAction.orbit Γ v) (hb : b ∈ MulAction.orbit Γ v) (hab : a ≠ b) :
    a * b ∈ MulAction.orbit Γ v := by
  obtain ⟨g₁, hg₁⟩ := ha
  obtain ⟨g₂, hg₂⟩ := hb
  have hg₁' : g₁ • v = a := hg₁
  have hg₂' : g₂ • v = b := hg₂
  have hmemH : ∀ k ∈ D.H₁, k • v = v := fun k hk => by
    have : k ∈ MulAction.stabilizer Γ v := by rw [hstab]; exact hk
    exact MulAction.mem_stabilizer_iff.mp this
  rcases D.two_trans (g₁⁻¹ * g₂) with h | ⟨c, hc, hk⟩
  · exfalso
    apply hab
    have h' := hmemH _ h
    rw [mul_smul, hg₂'] at h'
    rw [← hg₁', ← h', smul_inv_smul]
  · have hkv := hmemH _ hk
    have hcv := hmemH _ hc
    have hg₂eq : g₂ = (g₁ * c * D.hs 1) * ((D.hs 1)⁻¹ * (c⁻¹ * (g₁⁻¹ * g₂))) := by group
    have hb' : b = (g₁ * c * D.hs 1) • v := by
      rw [← hg₂', hg₂eq, mul_smul, hkv]
    have ha' : a = (g₁ * c) • v := by rw [← hg₁', mul_smul, hcv]
    have hl : v * (D.hs 1 • v) = D.hs 2 • v := by
      rw [D.hs_zero, one_smul] at hline
      have h1 := eq_inv_of_mul_eq_one_left hline
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hM _)
    refine ⟨g₁ * c * D.hs 2, ?_⟩
    show (g₁ * c * D.hs 2) • v = a * b
    rw [ha', hb', mul_smul (g₁ * c), mul_smul (g₁ * c) (D.hs 1), ← smul_mul', hl, mul_smul]

def Datum.orbitSubgroup (D : Datum) (hM : ∀ x : M, x ^ 2 = 1) {v : M}
    (hstab : MulAction.stabilizer Γ v = D.H₁)
    (hline : (D.hs 0 • v) * (D.hs 1 • v) * (D.hs 2 • v) = 1) : Subgroup M where
  carrier := {x | x = 1 ∨ x ∈ MulAction.orbit Γ v}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    rcases ha with rfl | ha
    · rw [one_mul]; exact hb
    rcases hb with rfl | hb
    · rw [mul_one]; exact Or.inr ha
    by_cases hab : a = b
    · subst hab
      left
      rw [← sq]
      exact hM a
    · exact Or.inr (D.closed_orbit hM hstab hline ha hb hab)
  inv_mem' := by
    intro x hx
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hM x)
    rw [this]
    exact hx

def quotAction (W : Subgroup M) (hW : ∀ (g : Γ), ∀ x ∈ W, g • x ∈ W) :
    MulAction Γ (M ⧸ W) where
  smul g := QuotientGroup.map W W (MulDistribMulAction.toMonoidHom M g) (fun x hx => hW g x hx)
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (one_smul Γ x)
  mul_smul g h q := by
    induction q using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (mul_smul g h x)

theorem trivial_on_quot (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1) (W : Subgroup M)
    (hW : ∀ (g : Γ), ∀ x ∈ W, g • x ∈ W) (hW8 : Nat.card W = 8) (h32 : Nat.card M ≤ 32)
    (g : Γ) (x : M) : (g • x) * x⁻¹ ∈ W := by
  letI : MulAction Γ (M ⧸ W) := quotAction W hW
  have hidx : W.index * 8 = Nat.card M := by
    have := W.index_mul_card
    rwa [hW8] at this
  have hle : (MulAction.orbit Γ (x : M ⧸ W)).ncard ≤ 4 := by
    have h1 : (MulAction.orbit Γ (x : M ⧸ W)).ncard ≤ Nat.card (M ⧸ W) := by
      calc (MulAction.orbit Γ (x : M ⧸ W)).ncard ≤ (Set.univ : Set (M ⧸ W)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = Nat.card (M ⧸ W) := Set.ncard_univ _
    have h2 : Nat.card (M ⧸ W) = W.index := rfl
    omega
  have hstab : MulAction.stabilizer Γ (x : M ⧸ W) = ⊤ := by
    by_contra hne
    have h7 := seven_le_index _ hne
    rw [MulAction.index_stabilizer] at h7
    omega
  have hg : g • (x : M ⧸ W) = x := by
    have : g ∈ MulAction.stabilizer Γ (x : M ⧸ W) := by rw [hstab]; trivial
    exact MulAction.mem_stabilizer_iff.mp this
  have hg' : ((g • x : M) : M ⧸ W) = (x : M ⧸ W) := hg
  have := QuotientGroup.eq.mp hg'
  have h3 := W.inv_mem this
  rwa [mul_inv_rev, inv_inv, mul_comm] at h3

theorem not_card_orbit_21 (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hq : Nat.card M = 16 ∨ Nat.card M = 32) {x : M} (hx : x ≠ 1)
    (h21 : (MulAction.orbit Γ x).ncard = 21) : False := by
  obtain ⟨hle, hat⟩ := compl_attain hfix (MulAction.orbit Γ x) (fun y hy => orbit_ne_one hx hy)
    (fun g y hy => smul_mem_orbit' g hy)
  rw [h21] at hle hat
  rcases hq with hq | hq <;> rw [hq] at hle hat
  · omega
  · have := hat.small (by norm_num)
    omega

theorem stab_eq_of_le (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hq : Nat.card M = 16 ∨ Nat.card M = 32) {x : M} (hx : x ≠ 1) {K : Subgroup Γ}
    (hK : Nat.card K = 24) (hSH : subP ⊓ subQ ≤ MulAction.stabilizer Γ x)
    (hHK : MulAction.stabilizer Γ x ≤ K) : MulAction.stabilizer Γ x = K := by
  have h1 : 8 ∣ Nat.card (MulAction.stabilizer Γ x) := by
    have := Subgroup.card_dvd_of_le hSH
    rwa [card_subS] at this
  have h2 : Nat.card (MulAction.stabilizer Γ x) ∣ 24 := by
    have := Subgroup.card_dvd_of_le hHK
    rwa [hK] at this
  obtain ⟨k, hk⟩ := h1
  rw [hk] at h2
  have hk3 : k ≤ 3 := by
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  interval_cases k
  · omega
  · exfalso
    apply not_card_orbit_21 hfix hq hx
    rw [← MulAction.index_stabilizer]
    have := (MulAction.stabilizer Γ x).index_mul_card
    rw [hk, card_Γ] at this
    omega
  · omega
  · exact Subgroup.eq_of_le_of_card_ge hHK (by rw [hK, hk])

theorem exists_stab_eq (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hpow : ∃ k, Nat.card M = 2 ^ k) (h8 : 8 < Nat.card M) (h32 : Nat.card M ≤ 32) :
    ∃ v : M, v ≠ 1 ∧ (MulAction.stabilizer Γ v = subP ∨ MulAction.stabilizer Γ v = subQ) := by
  have hq := card_cases hpow h8 h32
  have hS : IsPGroup 2 ↥(subP ⊓ subQ) := IsPGroup.of_card (n := 3) (by rw [card_subS]; norm_num)
  have hmod := hS.card_modEq_card_fixedPoints M
  have hF : (MulAction.fixedPoints ↥(subP ⊓ subQ) M).ncard % 2 = 0 := by
    have h1 : Nat.card M % 2 = 0 := by rcases hq with h | h <;> rw [h]
    have h2 := hmod
    unfold Nat.ModEq at h2
    rw [Nat.card_coe_set_eq] at h2
    omega
  have hpos : 0 < (MulAction.fixedPoints ↥(subP ⊓ subQ) M).ncard := by
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    exact ⟨1, by rw [MulAction.mem_fixedPoints]; intro g; exact smul_one _⟩
  obtain ⟨x, hxF, hx1⟩ : ∃ x ∈ MulAction.fixedPoints ↥(subP ⊓ subQ) M, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.fixedPoints ↥(subP ⊓ subQ) M ⊆ {1} := fun y hy => hcon y hy
    have := Set.ncard_le_ncard hsub (Set.finite_singleton 1)
    rw [Set.ncard_singleton] at this
    omega
  have hSH : subP ⊓ subQ ≤ MulAction.stabilizer Γ x := fun g hg =>
    MulAction.mem_stabilizer_iff.mpr ((MulAction.mem_fixedPoints.mp hxF) ⟨g, hg⟩)
  have hne : MulAction.stabilizer Γ x ≠ ⊤ := stab_ne_top hfix hx1
  refine ⟨x, hx1, ?_⟩
  rcases le_subP_or_le_subQ _ hSH hne with h | h
  · exact Or.inl (stab_eq_of_le hfix hq hx1 card_subP hSH h)
  · exact Or.inr (stab_eq_of_le hfix hq hx1 card_subQ hSH h)

theorem card_le_eight (hM : ∀ x : M, x ^ 2 = 1)
    (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hperf : ∀ N : Subgroup M, (∀ (g : Γ) (x : M), (g • x) * x⁻¹ ∈ N) → N = ⊤)
    (h32 : Nat.card M ≤ 32) : Nat.card M ≤ 8 := by
  by_contra h8
  push Not at h8
  have hpow : ∃ k, Nat.card M = 2 ^ k :=
    IsPGroup.exists_card_eq (show IsPGroup 2 M from fun x => ⟨1, by rw [pow_one]; exact hM x⟩)
  obtain ⟨v, hv, hst⟩ := exists_stab_eq hfix hpow h8 h32
  obtain ⟨D, hstab⟩ : ∃ D : Datum, MulAction.stabilizer Γ v = D.H₁ := by
    rcases hst with h | h
    · exact ⟨Datum.P, h⟩
    · exact ⟨Datum.Q, h⟩
  have hline := D.line hfix hpow h8 h32 hv hstab
  let W : Subgroup M := D.orbitSubgroup hM hstab hline
  have hWmem : ∀ x, x ∈ W ↔ x = 1 ∨ x ∈ MulAction.orbit Γ v := fun x => Iff.rfl
  have hdisj : Disjoint ({1} : Set M) (MulAction.orbit Γ v) := by
    rw [Set.disjoint_singleton_left]
    intro h1
    exact orbit_ne_one hv h1 rfl
  have hW8 : Nat.card W = 8 := by
    have hset : (W : Set M) = {1} ∪ MulAction.orbit Γ v := by
      ext x
      exact hWmem x
    show Nat.card (W : Set M) = 8
    rw [Nat.card_coe_set_eq, hset, Set.ncard_union_eq hdisj, Set.ncard_singleton,
      D.card_orbit hstab]
  have hWinv : ∀ (g : Γ), ∀ x ∈ W, g • x ∈ W := by
    intro g x hx
    rcases (hWmem x).mp hx with rfl | hx
    · exact Or.inl (smul_one g)
    · exact Or.inr (smul_mem_orbit' g hx)
  have hWtop := hperf W (trivial_on_quot hfix W hWinv hW8 h32)
  rw [hWtop, Subgroup.card_top] at hW8
  omega

theorem card_eq_eight (hM : ∀ x : M, x ^ 2 = 1)
    (hfix : ∀ x : M, (∀ g : Γ, g • x = x) → x = 1)
    (hperf : ∀ N : Subgroup M, (∀ (g : Γ) (x : M), (g • x) * x⁻¹ ∈ N) → N = ⊤)
    (h32 : Nat.card M ≤ 32) (hnt : ∃ x : M, x ≠ 1) : Nat.card M = 8 := by
  have hle := card_le_eight hM hfix hperf h32
  obtain ⟨x, hx⟩ := hnt
  have h7 := seven_le_card_orbit hfix hx
  have hsub : MulAction.orbit Γ x ⊆ Set.univ \ {1} := fun y hy =>
    ⟨Set.mem_univ y, orbit_ne_one hx hy⟩
  have h1 : (Set.univ \ {(1 : M)}).ncard = Nat.card M - 1 := by
    rw [Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  have h2 := Set.ncard_le_ncard hsub
  rw [h1] at h2
  omega

end Fano

end CFSG.Quasithin.L3Mod
