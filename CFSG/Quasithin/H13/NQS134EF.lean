module

public import CFSG.Quasithin.H13.NQS134EE
public import CFSG.Quasithin.H13.NQS134ED

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def preB (S : A6.Setting134 G T L V) (A : Subgroup G) (s : Perm (Fin 6)) :
    Subgroup G :=
  A ⊓ ((Subgroup.zpowers s).comap S.frame.ρ).map (normalizer (V : Set G)).subtype

theorem mem_preB {S : A6.Setting134 G T L V} {A : Subgroup G} {s : Perm (Fin 6)} {x : G} :
    x ∈ preB S A s ↔ x ∈ A ∧ ∃ h : x ∈ normalizer (V : Set G), S.frame.ρ ⟨x, h⟩ ∈ zpowers s := by
  unfold preB
  rw [mem_inf]
  constructor
  · rintro ⟨hxA, ⟨y, hy, rfl⟩⟩
    exact ⟨hxA, y.2, hy⟩
  · rintro ⟨hxA, h, hρ⟩
    exact ⟨hxA, ⟨⟨x, h⟩, hρ, rfl⟩⟩

theorem zpowers_of_mul_self {s σ : Perm (Fin 6)} (hs2 : s * s = 1) (hσ : σ ∈ zpowers s) :
    σ = 1 ∨ σ = s := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hσ
  have hs2' : s ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, hs2]
  rcases Int.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left
    rw [← two_mul, zpow_mul, hs2', one_zpow]
  · right
    rw [zpow_add, zpow_one, zpow_mul, hs2', one_zpow, one_mul]

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem mem_centralizer_iff_fix {X : Subgroup G} (hXN : X ≤ normalizer (V : Set G)) {x₀ : G}
    (hx₀ : x₀ ∈ X)
    (hρ : ∀ (x : G) (hx : x ∈ X), S.frame.ρ ⟨x, hXN hx⟩ = 1 ∨
      S.frame.ρ ⟨x, hXN hx⟩ = S.frame.ρ ⟨x₀, hXN hx₀⟩) {v : G} (hv : v ∈ V) :
    v ∈ centralizer (X : Set G) ↔
      G6.permAct 6 (S.frame.ρ ⟨x₀, hXN hx₀⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
  have hfix : ∀ (x : G) (hx : x ∈ X), x * v * x⁻¹ = v ↔
      G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
    intro x hx
    rw [S.conj_eq_iff ⟨x, hXN hx⟩ ⟨v, hv⟩]
    constructor
    · intro h
      have := congrArg Subtype.val h
      rwa [G6.coreAct_coe] at this
    · intro h
      exact Subtype.ext (by rw [G6.coreAct_coe]; exact h)
  constructor
  · intro hc
    have h1 : x₀ * v * x₀⁻¹ = v := by
      rw [mem_centralizer_iff.mp hc x₀ hx₀, mul_inv_cancel_right]
    exact (hfix x₀ hx₀).1 h1
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    have h2 : x * v * x⁻¹ = v := by
      rcases hρ x hx with h3 | h3
      · rw [hfix x hx, h3, map_one]
        rfl
      · rw [hfix x hx, h3]
        exact h
    calc x * v = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [h2]

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
  (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
    ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z)
include hz hzL huniq

theorem centralizer_le_normalizer_conj (h1222 : Stmt12_2_2) {g : G} {B : Subgroup G}
    (hB : B ≤ conjSub g V) (hcard : 4 < Nat.card B) :
    centralizer (B : Set G) ≤ normalizer (conjSub g V : Set G) := by
  have hB' : conjSub g⁻¹ B ≤ V := by
    rw [conjSub_le_iff, inv_inv]
    exact hB
  have hc : ¬ Nat.card (conjSub g⁻¹ B) ≤ 4 := by rw [card_conjSub']; omega
  have h : centralizer (conjSub g⁻¹ B : Set G) ≤ normalizer (L : Set G) := by
    by_contra h'
    exact hc (card_le_four S hz hzL huniq h1222 hB' h')
  have h2 := h.trans (S.normalizer_L_le h1222)
  intro x hx
  rw [conjSub_normalizer, mem_conjSub]
  apply h2
  rw [conjSub_centralizer, mem_conjSub, inv_inv]
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e]
  exact hx

theorem fix_le_normalizer (h1222 : Stmt12_2_2) {g : G} {A : Subgroup G} (hAdef : A = conjSub g V)
    (hAN : A ≤ normalizer (V : Set G)) (hCA : 4 ≤ Nat.card ↥(A ⊓ centralizer (V : Set G)))
    {a₀ : G} (ha₀ : a₀ ∈ A) (hs : S.frame.ρ ⟨a₀, hAN ha₀⟩ ≠ 1)
    (hs2 : S.frame.ρ ⟨a₀, hAN ha₀⟩ * S.frame.ρ ⟨a₀, hAN ha₀⟩ = 1) {v : G} (hv : v ∈ V)
    (hfix : G6.permAct 6 (S.frame.ρ ⟨a₀, hAN ha₀⟩) (S.frame.ψ ⟨v, hv⟩ : P6) =
      S.frame.ψ ⟨v, hv⟩) :
    v ∈ normalizer (A : Set G) := by
  set B := preB S A (S.frame.ρ ⟨a₀, hAN ha₀⟩) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hCB : A ⊓ centralizer (V : Set G) ≤ B := by
    intro x hx
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    refine mem_preB.2 ⟨hxA, hAN hxA, ?_⟩
    rw [(frame5_ker_iff S.frame ⟨x, hAN hxA⟩).2 hxC]
    exact one_mem _
  have ha₀B : a₀ ∈ B := mem_preB.2 ⟨ha₀, hAN ha₀, mem_zpowers _⟩
  have ha₀C : a₀ ∉ A ⊓ centralizer (V : Set G) := fun h =>
    hs ((frame5_ker_iff S.frame _).2 (mem_inf.1 h).2)
  have hlt : A ⊓ centralizer (V : Set G) < B := lt_of_le_of_ne hCB fun h => ha₀C (h ▸ ha₀B)
  have hB8 : 4 < Nat.card B := by
    obtain ⟨k, hk⟩ := card_dvd_of_le hCB
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hlt.ne (eq_of_le_of_card_ge hCB hk.le)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact (Nat.card_pos (α := ↥B)).ne' hk
    have : 2 * Nat.card ↥(A ⊓ centralizer (V : Set G)) ≤ Nat.card B := by
      rw [hk, mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hN := centralizer_le_normalizer_conj S hz hzL huniq h1222 (g := g) (B := B)
    (hBA.trans hAdef.le) hB8
  rw [← hAdef] at hN
  apply hN
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : b ∈ preB S A (S.frame.ρ ⟨a₀, hAN ha₀⟩) := hb
  obtain ⟨-, hbN, hbρ⟩ := mem_preB.1 hb'
  have hfixb : G6.permAct 6 (S.frame.ρ ⟨b, hbN⟩) (S.frame.ψ ⟨v, hv⟩ : P6) =
      S.frame.ψ ⟨v, hv⟩ := by
    rcases zpowers_of_mul_self hs2 hbρ with h | h
    · rw [h, map_one]
      rfl
    · rw [h]
      exact hfix
  have h1 : b * v * b⁻¹ = v :=
    (S.conj_eq_iff ⟨b, hbN⟩ ⟨v, hv⟩).2 (Subtype.ext (by rw [G6.coreAct_coe]; exact hfixb))
  calc b * v = b * v * b⁻¹ * b := by group
    _ = v * b := by rw [h1]

theorem false_of_R1 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {g : G} {A : Subgroup G}
    (hAdef : A = conjSub g V) (hAC : ¬ A ≤ centralizer (V : Set G))
    (hAN : A ≤ normalizer (V : Set G))
    (hfixN : ∀ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ ≠ 1 → ∀ (v : G) (hv : v ∈ V),
      G6.permAct 6 (S.frame.ρ ⟨a, hAN ha⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ →
        v ∈ normalizer (A : Set G))
    (h8 : ∃ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ = U3.S6Out.d6 8)
    (h6 : ∃ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ = U3.S6Out.d6 6)
    (h1 : ∃ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ = U3.S6Out.d6 1) : False := by
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha =>
    mul_self_of_mem_conj S (g := g) (by rw [← hAdef]; exact ha)
  have hne' : conjSub g⁻¹ V ≠ V := by
    intro h
    apply conj_ne_of_not_le S (g := g) (by rw [← hAdef]; exact hAC)
    calc conjSub g V = conjSub g (conjSub g⁻¹ V) := by rw [h]
      _ = V := conjSub_inv_conjSub g V
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA2 a ha)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hA2 b hb)
    have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hA2 _ (mul_mem ha hb))
    rw [mul_inv_rev, hai, hbi] at h3
    exact h3.symm
  obtain ⟨a₁, ha₁A, ha₁⟩ := h1
  have h45 : U3.S6Out.d6 1 = swap 4 5 := d6_canonical.2.2
  set B := preB S A (swap 4 5) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBN : B ≤ normalizer (V : Set G) := hBA.trans hAN
  have ha₁B : a₁ ∈ B := mem_preB.2 ⟨ha₁A, hAN ha₁A, by rw [ha₁, h45]; exact mem_zpowers _⟩
  have hρa₁ : S.frame.ρ ⟨a₁, hBN ha₁B⟩ = swap 4 5 := ha₁.trans h45
  have hρB : ∀ (x : G) (hx : x ∈ B), S.frame.ρ ⟨x, hBN hx⟩ = 1 ∨
      S.frame.ρ ⟨x, hBN hx⟩ = S.frame.ρ ⟨a₁, hBN ha₁B⟩ := by
    intro x hx
    have hx' : x ∈ preB S A (swap 4 5) := hx
    obtain ⟨-, _, hxρ⟩ := mem_preB.1 hx'
    rw [hρa₁]
    exact zpowers_of_mul_self (swap_mul_self 4 5) hxρ
  set U := V ⊓ centralizer (B : Set G) with hUdef
  have hmemU : ∀ (v : G) (hv : v ∈ V), v ∈ U ↔
      G6.permAct 6 (swap 4 5) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
    intro v hv
    rw [mem_inf, ← hρa₁]
    exact ⟨fun h => (mem_centralizer_iff_fix S hBN ha₁B hρB hv).1 h.2,
      fun h => ⟨hv, (mem_centralizer_iff_fix S hBN ha₁B hρB hv).2 h⟩⟩
  have hU16 : Nat.card U = 16 := by
    have := card_V_inf_centralizer S hBN ha₁B hρB
    rw [hρa₁, card_fix45] at this
    exact this
  have hUN : U ≤ normalizer (A : Set G) := by
    intro v hv
    have hvV := (mem_inf.1 hv).1
    refine hfixN a₁ ha₁A (by rw [ha₁, h45]; decide) v hvV ?_
    rw [ha₁, h45]
    exact (hmemU v hvV).1 hv
  have hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
    intro a ha u hu
    obtain ⟨huV, huC⟩ := mem_inf.1 hu
    refine mem_inf.2 ⟨(mem_normalizer_iff.mp (hAN ha) u).mp huV, ?_⟩
    rw [mem_centralizer_iff]
    intro b hb
    have hbA := hBA hb
    have hub : b * u = u * b := mem_centralizer_iff.1 huC b hb
    have hab : b * a = a * b := hAcomm b hbA a ha
    have hab' : b * a⁻¹ = a⁻¹ * b := by
      rw [inv_eq_of_mul_eq_one_right (hA2 a ha)]
      exact hab
    calc b * (a * u * a⁻¹) = (b * a) * u * a⁻¹ := by group
      _ = a * (b * u) * a⁻¹ := by rw [hab]; group
      _ = a * (u * b) * a⁻¹ := by rw [hub]
      _ = a * u * (b * a⁻¹) := by group
      _ = a * u * (a⁻¹ * b) := by rw [hab']
      _ = a * u * a⁻¹ * b := by group
  set X := conjSub g⁻¹ U with hXdef
  have hmemX : ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ U := fun x => by
    rw [hXdef, mem_conjSub, inv_inv]
  have hXN : X ≤ normalizer (V : Set G) := by
    intro x hx
    have h1 := hUN ((hmemX x).1 hx)
    rw [hAdef, conjSub_normalizer, mem_conjSub] at h1
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  have hXV : X ≤ conjSub g⁻¹ V := conjSub_mono _ inf_le_left
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx => mul_self_of_mem_conj S (hXV hx)
  have hw : wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 ∨ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 4 := by
    rcases psi_z_cases' S hz hzL with h | h
    · rw [h]; exact Or.inr wtP_e0123
    · rw [h]; exact Or.inl wtP_e45
  have hcomm : ∀ (x : G) (hx : x ∈ X) (v : G) (hv : v ∈ V), x * v * x⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨x, hXN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
    intro x hx v hv
    refine wt_comm_of_mem S hz hzL huniq h331 h1222 hne' (hXN hx) hv ?_
    rw [mem_conjSub, inv_inv]
    have hu := (hmemX x).1 hx
    have ha : g * v * g⁻¹ ∈ A := by
      rw [hAdef, mem_conjSub]
      simpa [mul_assoc] using hv
    have e : g * (x * v * x⁻¹ * v⁻¹) * g⁻¹ = (g * x * g⁻¹) *
        ((g * v * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * v * g⁻¹)⁻¹) := by group
    rw [e]
    exact (inf_le_left : U ≤ V) (mul_mem hu (hAU _ ha _ (inv_mem hu)))
  have hX16 : Nat.card X = 16 := by rw [hXdef, card_conjSub', hU16]
  have hXC8 : 8 ≤ Nat.card ↥(X ⊓ centralizer (V : Set G)) := by
    by_cases hex : ∃ (x₀ : G) (hx₀ : x₀ ∈ X), S.frame.ρ ⟨x₀, hXN hx₀⟩ ≠ 1
    · obtain ⟨x₀, hx₀, hx₀1⟩ := hex
      obtain ⟨hρ, -, -⟩ := rho_eq_of_comm S hXN hX2 hw hcomm hx₀ hx₀1
      have := card_inf_centralizer S hXN hx₀ hx₀1 hρ
      omega
    · push Not at hex
      have hle : X ≤ X ⊓ centralizer (V : Set G) := fun x hx =>
        mem_inf.2 ⟨hx, (frame5_ker_iff S.frame _).1 (hex x hx)⟩
      have := card_le_of_le hle
      omega
  have hconj : conjSub g (X ⊓ centralizer (V : Set G)) = U ⊓ centralizer (A : Set G) := by
    rw [conjSub_inf, hXdef, conjSub_inv_conjSub, hAdef, conjSub_centralizer]
  have hUC8 : 8 ≤ Nat.card ↥(U ⊓ centralizer (A : Set G)) := by
    rw [← hconj, card_conjSub']
    exact hXC8
  have hfixA : ∀ (v : G) (hv : v ∈ V), v ∈ centralizer (A : Set G) → ∀ (a : G) (ha : a ∈ A),
      G6.permAct 6 (S.frame.ρ ⟨a, hAN ha⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ := by
    intro v hv hvC a ha
    have h1 : a * v * a⁻¹ = v := by
      rw [mem_centralizer_iff.mp hvC a ha, mul_inv_cancel_right]
    have h2 := (S.conj_eq_iff ⟨a, hAN ha⟩ ⟨v, hv⟩).1 h1
    have h3 := congrArg Subtype.val h2
    rw [G6.coreAct_coe] at h3
    exact h3
  have hVC4 : Nat.card ↥(V ⊓ centralizer (A : Set G)) ≤ 4 := by
    obtain ⟨a₈, ha₈A, ha₈⟩ := h8
    obtain ⟨a₆, ha₆A, ha₆⟩ := h6
    let F : ↥(V ⊓ centralizer (A : Set G)) → {x : P6 // ∑ i, Multiplicative.toAdd x i = 0 ∧
        G6.permAct 6 (U3.S6Out.d6 8) x = x ∧ G6.permAct 6 (U3.S6Out.d6 6) x = x ∧
        G6.permAct 6 (U3.S6Out.d6 1) x = x} := fun v =>
      ⟨S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩,
        G6.mem_coreMod.1 (S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩).2,
        by rw [← ha₈]; exact hfixA v (mem_inf.1 v.2).1 (mem_inf.1 v.2).2 a₈ ha₈A,
        by rw [← ha₆]; exact hfixA v (mem_inf.1 v.2).1 (mem_inf.1 v.2).2 a₆ ha₆A,
        by rw [← ha₁]; exact hfixA v (mem_inf.1 v.2).1 (mem_inf.1 v.2).2 a₁ ha₁A⟩
    have hF : Function.Injective F := by
      intro v w hvw
      have h0 : ((F v : P6)) = (F w : P6) := congrArg Subtype.val hvw
      have h1 : S.frame.ψ ⟨v, (mem_inf.1 v.2).1⟩ = S.frame.ψ ⟨w, (mem_inf.1 w.2).1⟩ :=
        Subtype.ext h0
      have h2 := S.frame.ψ.injective h1
      have h3 : (v : G) = w := congrArg (fun x : ↥V => (x : G)) h2
      exact Subtype.ext h3
    calc Nat.card ↥(V ⊓ centralizer (A : Set G))
        ≤ Nat.card {x : P6 // ∑ i, Multiplicative.toAdd x i = 0 ∧
            G6.permAct 6 (U3.S6Out.d6 8) x = x ∧ G6.permAct 6 (U3.S6Out.d6 6) x = x ∧
            G6.permAct 6 (U3.S6Out.d6 1) x = x} := Nat.card_le_card_of_injective F hF
      _ = (Finset.univ.filter fun x : P6 => ∑ i, Multiplicative.toAdd x i = 0 ∧
            G6.permAct 6 (U3.S6Out.d6 8) x = x ∧ G6.permAct 6 (U3.S6Out.d6 6) x = x ∧
            G6.permAct 6 (U3.S6Out.d6 1) x = x).card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = 4 := card_fixR1
  have hle : U ⊓ centralizer (A : Set G) ≤ V ⊓ centralizer (A : Set G) :=
    inf_le_inf_right _ inf_le_left
  have := card_le_of_le hle
  omega

theorem normalizes_of_le_T (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {g : G}
    (hAT : conjSub g V ≤ T) : V ≤ normalizer (conjSub g V : Set G) := by
  classical
  by_contra hVN
  set A := conjSub g V with hAdef
  have hAN : A ≤ normalizer (V : Set G) := hAT.trans S.frame.T_le
  have hAC : ¬ A ≤ centralizer (V : Set G) := fun h =>
    hVN ((le_centralizer_iff.mp h).trans (Subgroup.centralizer_le_normalizer _))
  have hCA : Nat.card ↥(A ⊓ centralizer (V : Set G)) ≤ 4 := by
    by_contra h
    apply hVN
    refine le_trans ?_ (centralizer_le_normalizer_conj S hz hzL huniq h1222
      (inf_le_left : A ⊓ centralizer (V : Set G) ≤ A) (by omega))
    intro v hv
    rw [mem_centralizer_iff]
    intro a ha
    exact (mem_centralizer_iff.1 (mem_inf.1 ha).2 v hv).symm
  let f : ↥A →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hAN)
  have hker : f.ker = (A ⊓ centralizer (V : Set G)).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    simp only [f, MonoidHom.comp_apply]
    refine ⟨fun h => ⟨x.2, (frame5_ker_iff S.frame _).1 h⟩, fun h => ?_⟩
    exact (frame5_ker_iff S.frame (Subgroup.inclusion hAN x)).2 h.2
  have hcardker : Nat.card f.ker = Nat.card ↥(A ⊓ centralizer (V : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : A ⊓ centralizer (V : Set G) ≤ A)).toEquiv
  have h32 : Nat.card ↥(A ⊓ centralizer (V : Set G)) * Nat.card f.range = 32 := by
    rw [← hcardker, ← Subgroup.index_ker, Subgroup.card_mul_index, card_conj S g]
  have hRD : ∀ σ ∈ f.range, InD6 σ := by
    rintro _ ⟨a, rfl⟩
    exact S.frame.T_D _ (hAT a.2)
  have hinvA : ∀ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ * S.frame.ρ ⟨a, hAN ha⟩ = 1 := by
    intro a ha
    rw [← map_mul]
    have : (⟨a, hAN ha⟩ * ⟨a, hAN ha⟩ : ↥(normalizer (V : Set G))) = 1 :=
      Subtype.ext (mul_self_of_mem_conj S ha)
    rw [this, map_one]
  have hR2 : ∀ σ ∈ f.range, σ * σ = 1 := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    exact hinvA a ha
  have hR4 : 4 < Nat.card f.range := by
    by_contra h
    have h1 : Nat.card ↥(A ⊓ centralizer (V : Set G)) * Nat.card f.range ≤ 4 * 4 :=
      Nat.mul_le_mul hCA (by omega)
    omega
  obtain ⟨hR8, hcases⟩ := D_e8 hRD hR2 hR4
  have hC4 : 4 ≤ Nat.card ↥(A ⊓ centralizer (V : Set G)) := by
    by_contra h
    have h1 : Nat.card ↥(A ⊓ centralizer (V : Set G)) * Nat.card f.range ≤ 3 * 8 :=
      Nat.mul_le_mul (by omega) hR8
    omega
  have hfixN : ∀ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ ≠ 1 → ∀ (v : G) (hv : v ∈ V),
      G6.permAct 6 (S.frame.ρ ⟨a, hAN ha⟩) (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ →
        v ∈ normalizer (A : Set G) := fun a ha hs v hv hfix =>
    fix_le_normalizer S hz hzL huniq h1222 hAdef hAN hC4 ha hs (hinvA a ha) hv hfix
  have hfixN' : ∀ s ∈ f.range, s ≠ 1 → ∀ (v : G) (hv : v ∈ V),
      G6.permAct 6 s (S.frame.ψ ⟨v, hv⟩ : P6) = S.frame.ψ ⟨v, hv⟩ →
        v ∈ normalizer (A : Set G) := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩ hs v hv hfix
    exact hfixN a ha hs v hv hfix
  have hex : ∀ s ∈ f.range, ∃ (a : G) (ha : a ∈ A), S.frame.ρ ⟨a, hAN ha⟩ = s := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  have hψmul : ∀ (a b : G) (ha : a ∈ V) (hb : b ∈ V),
      (S.frame.ψ ⟨a * b, mul_mem ha hb⟩ : P6) =
        (S.frame.ψ ⟨a, ha⟩ : P6) * (S.frame.ψ ⟨b, hb⟩ : P6) := fun a b ha hb => by
    rw [show (⟨a * b, mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
    rfl
  rcases hcases with ⟨h01, h23⟩ | ⟨h8, h6, h1, -⟩
  ·
    apply hVN
    intro v hv
    obtain ⟨a, ha0, hfa, hfb⟩ := fix01_fix23 _ (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2)
    set v₁ : ↥V := S.frame.ψ.symm ⟨a, G6.mem_coreMod.2 ha0⟩ with hv₁def
    have hv₁ : (S.frame.ψ v₁ : P6) = a := by rw [hv₁def, MulEquiv.apply_symm_apply]
    have hv₂core : a * (S.frame.ψ ⟨v, hv⟩ : P6) ∈ G6.coreMod 6 :=
      mul_mem (G6.mem_coreMod.2 ha0) (S.frame.ψ ⟨v, hv⟩).2
    set v₂ : ↥V := S.frame.ψ.symm ⟨_, hv₂core⟩ with hv₂def
    have hv₂ : (S.frame.ψ v₂ : P6) = a * (S.frame.ψ ⟨v, hv⟩ : P6) := by
      rw [hv₂def, MulEquiv.apply_symm_apply]
    have hv12 : v = (v₁ : G) * (v₂ : G) := by
      have h1 : S.frame.ψ ⟨v, hv⟩ = S.frame.ψ ⟨(v₁ : G) * (v₂ : G), mul_mem v₁.2 v₂.2⟩ := by
        apply Subtype.ext
        rw [hψmul _ _ v₁.2 v₂.2]
        show (S.frame.ψ ⟨v, hv⟩ : P6) = (S.frame.ψ v₁ : P6) * (S.frame.ψ v₂ : P6)
        rw [hv₁, hv₂, ← mul_assoc, P6_mul_self, one_mul]
      exact congrArg Subtype.val (S.frame.ψ.injective h1)
    rw [hv12]
    refine mul_mem (hfixN' _ h01 (by decide) _ v₁.2 ?_) (hfixN' _ h23 (by decide) _ v₂.2 ?_)
    · show G6.permAct 6 (swap 0 1) (S.frame.ψ v₁ : P6) = S.frame.ψ v₁
      rw [hv₁]
      exact hfa
    · show G6.permAct 6 (swap 2 3) (S.frame.ψ v₂ : P6) = S.frame.ψ v₂
      rw [hv₂]
      exact hfb
  · exact false_of_R1 S hz hzL huniq h331 h1222 hAdef hAC hAN hfixN (hex _ h8) (hex _ h6)
      (hex _ h1)

theorem wt_two_of_le_T (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {g : G}
    (hAT : conjSub g V ≤ T) (hAC : ¬ conjSub g V ≤ centralizer (V : Set G)) :
    wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 ∧ ∃ i j : Fin 6, i ≠ j ∧
      ∀ (a : G) (ha : a ∈ conjSub g V), S.frame.ρ ⟨a, S.frame.T_le (hAT ha)⟩ = 1 ∨
        S.frame.ρ ⟨a, S.frame.T_le (hAT ha)⟩ = swap i j := by
  have hAN : conjSub g V ≤ normalizer (V : Set G) := hAT.trans S.frame.T_le
  have hVN := normalizes_of_le_T S hz hzL huniq h331 h1222 hAT
  have hw2 : wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 := by
    rcases psi_z_cases' S hz hzL with h | h
    · exact (false_of_normalizes_four S hz hzL huniq h331 h1222 (by rw [h]; exact wtP_e0123)
        hAN hVN hAC).elim
    · rw [h]
      exact wtP_e45
  obtain ⟨a₀, ha₀, -, hρ, -, h2⟩ := rho_of_normalizes S hz hzL huniq h331 h1222 hAN hVN hAC
  obtain ⟨i, j, hij, hsw⟩ := h2 hw2
  refine ⟨hw2, i, j, hij, fun a ha => ?_⟩
  rw [← hsw]
  exact hρ a ha

end End134

end CFSG.Quasithin.H13.NQS134
