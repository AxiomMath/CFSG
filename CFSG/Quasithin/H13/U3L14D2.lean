module

public import CFSG.Quasithin.H13.U3L14D1
public import CFSG.Quasithin.Background.F6NoncyclicCore
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.SectionRank CFSG.SectionRank.Ccomm
open scoped commutatorElement

theorem sl23_pow24 : ∀ b : Matrix (Fin 2) (Fin 2) (ZMod 3), b.det = 1 → b ^ 24 = 1 := by
  decide +kernel

theorem sl23_sq : ∀ g b : Matrix (Fin 2) (Fin 2) (ZMod 3), g * g * g = 1 → b.det = 1 →
    b ^ 8 = 1 → g * b ≠ b * g → b * b = -1 := by
  decide +kernel

theorem sl23_sq' : ∀ g b : Matrix (Fin 2) (Fin 2) (ZMod 3), g * g * g = 1 → b.det = 1 →
    b ^ 8 = 1 → g * b ≠ b * g → (g * b * (g * g)) * (g * b * (g * g)) = -1 := by
  decide +kernel

theorem sl23_sq'' : ∀ g b : Matrix (Fin 2) (Fin 2) (ZMod 3), g * g * g = 1 → b.det = 1 →
    b ^ 8 = 1 → g * b ≠ b * g →
      (b * (g * b * (g * g))) * (b * (g * b * (g * g))) = -1 := by
  decide +kernel

theorem sl23_ncomm : ∀ g b : Matrix (Fin 2) (Fin 2) (ZMod 3), g * g * g = 1 → b.det = 1 →
    b ^ 8 = 1 → g * b ≠ b * g → b * (g * b * (g * g)) ≠ (g * b * (g * g)) * b := by
  decide +kernel

theorem toAdd_zpow_eq_smul {p : ℕ} (a : Multiplicative (Fin 2 → ZMod p)) (n : ℤ) :
    Multiplicative.toAdd (a ^ n) = (n : ZMod p) • Multiplicative.toAdd a := by
  rw [toAdd_zpow]
  funext i
  simp [zsmul_eq_mul]

theorem gl23_fix : ∀ g : Matrix (Fin 2) (Fin 2) (ZMod 3), g * g * g = 1 →
    ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ Matrix.mulVec g v = v := by
  decide +kernel

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [hp : Fact p.Prime]

structure PStarData (p : ℕ) (B : Subgroup Γ) (x : Γ) (X : Subgroup Γ) : Prop where
  le : X ≤ CFSG.pCore p Γ
  normal : X.Normal
  pow : ∀ y ∈ X, y ^ p = 1
  card : Nat.card X = p ^ 2 ∨ (Nat.card X = p ^ 3 ∧ ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
  irred : ∀ Y : Subgroup Γ, ⁅X, X⁆ ≤ Y → Y ≤ X → (∀ b ∈ B, b ∈ normalizer (Y : Set Γ)) →
    Y = ⁅X, X⁆ ∨ Y = X
  act : ∃ y ∈ X, x * y * x⁻¹ * y⁻¹ ∉ ⁅X, X⁆
  rank : ∃ E : Subgroup Γ, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2
  q8 : p = 3 → ∃ b₁ ∈ B, ∃ b₂ ∈ B,
    (∀ y ∈ X, b₁ ^ 2 * y * (b₁ ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
    (∀ y ∈ X, b₂ ^ 2 * y * (b₂ ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
    (∀ y ∈ X, (b₁ * b₂) ^ 2 * y * ((b₁ * b₂) ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
    ∃ y ∈ X, ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∉ ⁅X, X⁆
  e9 : p = 3 → Nat.card X = p ^ 2

theorem exists_pStar (hp2 : p ≠ 2) (hrank : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ 2)
    {Nsub B : Subgroup Γ} (hBN : B ≤ Nsub) (hB2 : IsPGroup 2 B)
    (hBn : ∀ b ∈ B, ∀ n ∈ Nsub, n * b * n⁻¹ ∈ B) {x : Γ} (hxN : x ∈ Nsub) (hx3 : x ^ 3 = 1)
    (hNB : ∀ n ∈ Nsub, ∃ b ∈ B, ∃ k : ℕ, n = b * x ^ k)
    (hgen : Nsub ≤ closure {y : Γ | y ∈ Nsub ∧ Odd (orderOf y)})
    (hfail : ¬ B ≤ centralizer (CFSG.pCore p Γ : Set Γ)) :
    ∃ X : Subgroup Γ, PStarData p B x X := by
  classical
  set P₀ := CFSG.pCore p Γ with hP₀
  have hP₀p : IsPGroup p P₀ := CFSG.pCore_isPGroup
  let Bn : Subgroup ↥Nsub := B.subgroupOf Nsub
  let xn : ↥Nsub := ⟨x, hxN⟩
  have hBn2 : IsPGroup 2 Bn := hB2.of_equiv (subgroupOfEquivOfLe hBN).symm
  have hBnn : ∀ b ∈ Bn, ∀ n : ↥Nsub, n * b * n⁻¹ ∈ Bn := fun b hb n =>
    mem_subgroupOf.2 (by simpa using hBn b (mem_subgroupOf.1 hb) n n.2)
  have hxn3 : xn ^ 3 = 1 := Subtype.ext (by simpa [xn] using hx3)
  have hNBn : ∀ n : ↥Nsub, ∃ b ∈ Bn, ∃ k : ℕ, n = b * xn ^ k := by
    intro n
    obtain ⟨b, hb, k, hk⟩ := hNB n n.2
    have hbN : b ∈ Nsub := by
      have : b = n * (x ^ k)⁻¹ := by rw [hk]; group
      rw [this]
      exact mul_mem n.2 (inv_mem (pow_mem hxN k))
    refine ⟨⟨b, hbN⟩, mem_subgroupOf.2 hb, k, Subtype.ext ?_⟩
    simpa [xn] using hk
  have hgenN : closure {y : ↥Nsub | Odd (orderOf y)} = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have h1 : (n : Γ) ∈ (closure {y : ↥Nsub | Odd (orderOf y)}).map Nsub.subtype := by
      rw [MonoidHom.map_closure]
      refine closure_mono ?_ (hgen n.2)
      rintro y ⟨hyN, hy⟩
      exact ⟨⟨y, hyN⟩, by simpa [Subgroup.orderOf_mk] using hy, rfl⟩
    obtain ⟨m, hm, hmn⟩ := h1
    rwa [Nsub.subtype_injective hmn] at hm
  obtain ⟨b₀, hb₀B, hb₀⟩ : ∃ b ∈ B, b ∉ centralizer (P₀ : Set Γ) := by
    by_contra h
    push Not at h
    exact hfail h
  have hnt : Nontrivial ↥P₀ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hb₀
    rw [mem_centralizer_iff]
    intro y hy
    have : y = 1 := congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : ↥P₀) 1)
    rw [this, one_mul, mul_one]
  obtain ⟨X₀, hX₀, hfaith⟩ := exists_isSupercritical_faithful hp2 hP₀p
  have : X₀.Characteristic := hX₀.characteristic
  have hrank₀ : CFSG.Open.pRank p (⊤ : Subgroup ↥P₀) ≤ 2 :=
    (pRank_top_le_of_injective hp.out.one_lt P₀.subtype P₀.subtype_injective).trans hrank
  have hX₀p : IsPGroup p ↥X₀ := hP₀p.to_subgroup X₀
  have hexp' : ∀ y : ↥X₀, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using hX₀.pow_eq_one y y.2)
  have hrX : CFSG.Open.pRank p (⊤ : Subgroup ↥X₀) ≤ 2 :=
    (pRank_top_le_of_injective hp.out.one_lt X₀.subtype X₀.subtype_injective).trans
      ((pRank_mono hp.out.one_lt (by simp)).trans hrank₀)
  obtain ⟨hX₀3, hW2⟩ := rank_two_exponent_prime_order_bound hX₀p hexp' hrX
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hX₀p
  obtain ⟨k, hk⟩ := (hX₀p.to_quotient (frattini ↥X₀)).exists_card_eq
  have hkle : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hW2)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hk
  set φ : Γ →* MulAut (↥X₀ ⧸ frattini ↥X₀) := F6.frattiniConj P₀ X₀ with hφ
  have hcen : ∀ b ∈ B, φ b = 1 → b ∈ centralizer (P₀ : Set Γ) := by
    intro b hb h
    have hα : (MulAut.conjNormal b : MulAut ↥P₀) = 1 := by
      apply hfaith
      · obtain ⟨m, hm⟩ := pow_two_pow_of_mem hB2 hb
        have h1 : orderOf (MulAut.conjNormal b : MulAut ↥P₀) ∣ 2 ^ m :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hm, map_one])
        exact Nat.Coprime.coprime_dvd_left h1
          (Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)))
      · intro y hy
        exact F6.mem_ker_frattiniConj.1 (MonoidHom.mem_ker.2 h) y hy
    rw [mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun α : MulAut ↥P₀ => ((α ⟨y, hy⟩ : ↥P₀) : Γ)) hα
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc y * b = b * y * b⁻¹ * b := by rw [h2]
      _ = b * y := by group
  have hφb₀ : φ b₀ ≠ 1 := fun h => hb₀ (hcen b₀ hb₀B h)
  set ψ : ↥Nsub →* GL (Fin k) (ZMod p) :=
    (elemAutEquivGL e).toMonoidHom.comp (φ.comp Nsub.subtype) with hψ
  have hψne : ∃ b ∈ Bn, ψ b ≠ 1 := by
    refine ⟨⟨b₀, hBN hb₀B⟩, mem_subgroupOf.2 hb₀B, fun h => hφb₀ ?_⟩
    have h1 : (elemAutEquivGL e) (φ b₀) = 1 := h
    rwa [MulEquiv.map_eq_one_iff] at h1
  have hnc := gl2_not_comm ψ hBn2 hxn3 hNBn hgenN hψne
  have hk2 : k = 2 := by
    by_contra hne
    apply hnc
    intro b _
    exact gl_comm_of_le_one (by omega) _ _
  subst hk2
  set W := ↥X₀ ⧸ frattini ↥X₀ with hWdef
  set f : ↥X₀ →* Γ := P₀.subtype.comp X₀.subtype with hf
  have hf_inj : Function.Injective f := P₀.subtype_injective.comp X₀.subtype_injective
  set X : Subgroup Γ := X₀.map P₀.subtype with hX
  have hXf : X = (⊤ : Subgroup ↥X₀).map f := by
    rw [hX, hf, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmemX : ∀ y : Γ, y ∈ X ↔ ∃ z : ↥X₀, f z = y := by
    intro y
    rw [hXf]
    constructor
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, mem_top z, rfl⟩
  have hΦ : frattini ↥X₀ = commutator ↥X₀ :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hX₀p hexp'
  have hcommX : ⁅X, X⁆ = (frattini ↥X₀).map f := by
    rw [hΦ, commutator_def, Subgroup.map_commutator, ← hXf]
  have hmemC : ∀ z : ↥X₀, f z ∈ ⁅X, X⁆ ↔ z ∈ frattini ↥X₀ := by
    intro z
    rw [hcommX]
    exact Subgroup.mem_map_iff_mem hf_inj
  have hW_eq : ∀ z₁ z₂ : ↥X₀, ((z₁ : W) = (z₂ : W)) ↔ (f z₁)⁻¹ * f z₂ ∈ ⁅X, X⁆ := by
    intro z₁ z₂
    rw [QuotientGroup.eq, ← hmemC, map_mul, map_inv]
  have hφ_apply : ∀ (g : Γ) (z : ↥X₀), ∃ z' : ↥X₀, f z' = g * f z * g⁻¹ ∧
      φ g (z : W) = (z' : W) := by
    intro g z
    refine ⟨⟨MulAut.conjNormal g (z : ↥P₀),
      (MulAut.characteristic X₀ (MulAut.conjNormal g) z).2⟩, ?_, rfl⟩
    simp [hf, MulAut.conjNormal_apply]
  have hWle : Nat.card W ≤ Nat.card ↥X₀ :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hWcard : Nat.card W = p ^ 2 := hk
  have hcardX : Nat.card X = Nat.card ↥X₀ := by
    rw [hX]
    exact Subgroup.card_map_of_injective P₀.subtype_injective
  have hcard : Nat.card X = p ^ 2 ∨
      (Nat.card X = p ^ 3 ∧ ¬ ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) := by
    obtain ⟨a, ha⟩ := hX₀p.exists_card_eq
    rw [hcardX, ha]
    have h2 : 2 ≤ a := by
      have : p ^ 2 ≤ p ^ a := by rw [← hWcard, ← ha]; exact hWle
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 this
    have h3 : a ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (ha ▸ hX₀3)
    interval_cases a
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, fun hc => ?_⟩
      have hcomm : commutator ↥X₀ = ⊥ := by
        rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
        intro z₁ _
        rw [mem_centralizer_iff]
        intro z₂ _
        apply hf_inj
        rw [map_mul, map_mul]
        exact hc _ ((hmemX _).2 ⟨z₂, rfl⟩) _ ((hmemX _).2 ⟨z₁, rfl⟩)
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥X₀)
      have h0 : Nat.card ↥(frattini ↥X₀) = 1 := by rw [hΦ, hcomm, card_bot]
      rw [h0, mul_one, ha] at h1
      have : p ^ 3 = p ^ 2 := h1.trans hWcard
      exact absurd ((Nat.pow_right_injective hp.out.two_le) this) (by norm_num)
  have hirred : ∀ Y : Subgroup Γ, ⁅X, X⁆ ≤ Y → Y ≤ X →
      (∀ b ∈ B, b ∈ normalizer (Y : Set Γ)) → Y = ⁅X, X⁆ ∨ Y = X := by
    intro Y hCY hYX hBY
    set Y₀ : Subgroup ↥X₀ := Y.comap f with hY₀
    have hΦY : frattini ↥X₀ ≤ Y₀ := fun z hz => hCY ((hmemC z).2 hz)
    set Yb : Subgroup W := Y₀.map (QuotientGroup.mk' (frattini ↥X₀)) with hYb
    have hcomapYb : Yb.comap (QuotientGroup.mk' (frattini ↥X₀)) = Y₀ := by
      rw [hYb, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hΦY]
    have hdvd : Nat.card Yb ∣ p ^ 2 := hWcard ▸ Subgroup.card_subgroup_dvd_card Yb
    obtain ⟨j, hj, hYbj⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    interval_cases j
    ·
      left
      have hbot : Yb = ⊥ := Subgroup.eq_bot_of_card_eq Yb (by rw [hYbj, pow_zero])
      refine le_antisymm (fun y hy => ?_) hCY
      obtain ⟨z, rfl⟩ := (hmemX y).1 (hYX hy)
      rw [hmemC]
      have hz : z ∈ Y₀ := hy
      have : (QuotientGroup.mk' (frattini ↥X₀)) z ∈ Yb := ⟨z, hz, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    ·
      exfalso
      rw [pow_one] at hYbj
      have hcyc : IsCyclic Yb := isCyclic_of_prime_card hYbj
      obtain ⟨⟨w, hwY⟩, hgen⟩ := hcyc.exists_generator
      have hw1 : w ≠ 1 := by
        intro h1
        have : ∀ y : Yb, y = 1 := fun y => by
          obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).1 (hgen y)
          rw [← hn]
          have : (⟨w, hwY⟩ : Yb) = 1 := Subtype.ext h1
          rw [this, one_zpow]
        have hc1 : Nat.card Yb = 1 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (this a).trans
          (this b).symm⟩, ⟨1⟩⟩
        rw [hYbj] at hc1
        exact hp.out.one_lt.ne' hc1
      set v : Fin 2 → ZMod p := Multiplicative.toAdd (e w) with hv
      have hv0 : v ≠ 0 := by
        intro h0
        apply hw1
        apply e.injective
        rw [map_one]
        exact Multiplicative.toAdd.injective h0
      apply gl2_irreducible hp2 ψ hBn2 hBnn hxn3 hNBn hgenN hψne hv0
      intro b hb
      have hbB : (b : Γ) ∈ B := mem_subgroupOf.1 hb
      have hpres : φ b w ∈ Yb := by
        obtain ⟨z, hz, hzw⟩ := hwY
        obtain ⟨z', hz', hφz⟩ := hφ_apply b z
        rw [← hzw, QuotientGroup.mk'_apply, hφz]
        refine ⟨z', ?_, rfl⟩
        show f z' ∈ Y
        rw [hz']
        exact (mem_normalizer_iff.1 (hBY b hbB) (f z)).1 hz
      obtain ⟨n, hn⟩ := (Subgroup.mem_zpowers_iff).1 (hgen ⟨φ b w, hpres⟩)
      have hn' : w ^ n = φ b w := congrArg Subtype.val hn
      refine ⟨(n : ZMod p), ?_⟩
      have h1 := elemAutEquivGL_mulVec e (φ b) w
      have h2 : (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) = elemAutEquivGL e (φ b) := rfl
      rw [h2, h1, ← hn', map_zpow]
      exact toAdd_zpow_eq_smul (e w) n
    ·
      right
      have htop : Yb = ⊤ := Subgroup.eq_top_of_card_eq Yb (by rw [hYbj, hWcard])
      have hY₀top : Y₀ = ⊤ := by rw [← hcomapYb, htop, comap_top]
      refine le_antisymm hYX (fun y hy => ?_)
      obtain ⟨z, rfl⟩ := (hmemX y).1 hy
      have : z ∈ Y₀ := hY₀top ▸ mem_top z
      exact this
  have hnormal : X.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨z, rfl⟩ := (hmemX y).1 hy
    obtain ⟨z', hz', -⟩ := hφ_apply g z
    exact (hmemX _).2 ⟨z', hz'⟩
  have hCn : (⁅X, X⁆ : Subgroup Γ).Normal := Subgroup.commutator_normal X X
  have hact : ∃ y ∈ X, x * y * x⁻¹ * y⁻¹ ∉ ⁅X, X⁆ := by
    by_contra h
    push Not at h
    apply hnc
    intro b _
    have hx1 : φ x = 1 := by
      ext w
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨z', hz', hφz⟩ := hφ_apply x z
      rw [hφz, MulAut.one_apply, hW_eq, hz']
      have h1 := h (f z) ((hmemX _).2 ⟨z, rfl⟩)
      have : (x * f z * x⁻¹)⁻¹ * f z =
          ((f z)⁻¹ * (x * f z * x⁻¹ * (f z)⁻¹) * (f z)⁻¹⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem (hCn.conj_mem _ h1 _)
    have hψx : ψ xn = 1 := by
      show (elemAutEquivGL e) (φ x) = 1
      rw [hx1, map_one]
    rw [hψx, one_mul, mul_one]
  have hrank2 : ∃ E : Subgroup Γ, E ≤ X ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
    have hX₀ne : X₀ ≠ ⊥ := by
      intro hb
      have : Nat.card ↥X₀ = 1 := by rw [hb, card_bot]
      have h1 := hWle
      rw [this, hWcard] at h1
      exact absurd h1 (by have := hp.out.two_le; nlinarith)
    have hr2 : 2 ≤ CFSG.Open.pRank p X₀ := by
      by_contra hlt
      push Not at hlt
      obtain ⟨z, -, hXz, hzo⟩ :=
        exists_eq_zpowers_of_pRank_le_one hP₀p hX₀ne hX₀.pow_eq_one (by omega)
      have : Nat.card ↥X₀ = p := by rw [hXz, Nat.card_zpowers, hzo]
      have h1 := hWle
      rw [this, hWcard] at h1
      exact absurd h1 (by have := hp.out.two_le; nlinarith)
    have hr2' : CFSG.Open.pRank p X₀ ≤ 2 := (pRank_mono hp.out.one_lt le_top).trans hrank₀
    obtain ⟨E, hEX, ⟨hEc, hEp⟩, hEcard⟩ := exists_pRank hp.out.one_lt X₀
    refine ⟨E.map P₀.subtype, map_mono hEX, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
    · apply Subtype.ext
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      simp only [Subgroup.coe_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hEc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hEp a ha, map_one]
    · rw [Subgroup.card_map_of_injective P₀.subtype_injective, hEcard]
      congr 1
      omega
  have hpow : ∀ y ∈ X, y ^ p = 1 := by
    intro y hy
    obtain ⟨z, rfl⟩ := (hmemX y).1 hy
    rw [← map_pow, hexp' z, map_one]
  have hinv : ∀ c : ↥Nsub, (ψ c : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 →
      ∀ y ∈ X, (c : Γ) * y * (c : Γ)⁻¹ * y ∈ ⁅X, X⁆ := by
    intro c hc y hy
    obtain ⟨z, rfl⟩ := (hmemX y).1 hy
    have h1 : elemAutEquivGL e (φ c) = -1 :=
      Units.ext (by rw [Units.val_neg, Units.val_one]; exact hc)
    rw [elemAutEquivGL_eq_neg_one_iff] at h1
    have h2 := h1 (z : W)
    obtain ⟨z', hz', hφz⟩ := hφ_apply c z
    rw [hφz, ← QuotientGroup.mk_inv, hW_eq, map_inv, hz'] at h2
    have e1 : (c : Γ) * f z * (c : Γ)⁻¹ * f z =
        (f z)⁻¹ * (((c : Γ) * f z * (c : Γ)⁻¹)⁻¹ * (f z)⁻¹)⁻¹ * (f z)⁻¹⁻¹ := by group
    rw [e1]
    exact hCn.conj_mem _ (inv_mem h2) _
  have hnontriv : ∀ c : ↥Nsub, ψ c ≠ 1 →
      ∃ y ∈ X, (c : Γ) * y * (c : Γ)⁻¹ * y⁻¹ ∉ ⁅X, X⁆ := by
    intro c hc
    by_contra h
    push Not at h
    apply hc
    have hc1 : φ c = 1 := by
      ext w
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨z', hz', hφz⟩ := hφ_apply c z
      rw [hφz, MulAut.one_apply, hW_eq, hz']
      have h1 := h (f z) ((hmemX _).2 ⟨z, rfl⟩)
      have e1 : ((c : Γ) * f z * (c : Γ)⁻¹)⁻¹ * f z =
          ((f z)⁻¹ * ((c : Γ) * f z * (c : Γ)⁻¹ * (f z)⁻¹) * (f z)⁻¹⁻¹)⁻¹ := by group
      rw [e1]
      exact inv_mem (hCn.conj_mem _ h1 _)
    show (elemAutEquivGL e) (φ c) = 1
    rw [hc1, map_one]
  have hq8 : p = 3 → (∃ b₁ ∈ B, ∃ b₂ ∈ B,
      (∀ y ∈ X, b₁ ^ 2 * y * (b₁ ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
      (∀ y ∈ X, b₂ ^ 2 * y * (b₂ ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
      (∀ y ∈ X, (b₁ * b₂) ^ 2 * y * ((b₁ * b₂) ^ 2)⁻¹ * y ∈ ⁅X, X⁆) ∧
      ∃ y ∈ X, ⁅b₁, b₂⁆ * y * ⁅b₁, b₂⁆⁻¹ * y⁻¹ ∉ ⁅X, X⁆) ∧ Nat.card X = p ^ 2 := by
    intro hp3
    subst hp3
    obtain ⟨b, hb, hbx⟩ : ∃ b ∈ Bn, ψ xn * ψ b ≠ ψ b * ψ xn := by
      by_contra h
      push Not at h
      exact hnc h
    set g : Matrix (Fin 2) (Fin 2) (ZMod 3) := (ψ xn : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hg
    set M : Matrix (Fin 2) (Fin 2) (ZMod 3) := (ψ b : Matrix (Fin 2) (Fin 2) (ZMod 3)) with hM
    have hg3 : g * g * g = 1 := by
      rw [hg, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        show xn * xn * xn = xn ^ 3 by rw [pow_three, mul_assoc], hxn3, map_one, Units.val_one]
    obtain ⟨m, hm⟩ := pow_two_pow_of_mem hBn2 hb
    have hdet : M.det = 1 := by
      have h1 := map_eq_one_of_odd_closure (Matrix.GeneralLinearGroup.det.comp ψ) hgenN hm
      have h2 := congrArg Units.val h1
      simpa using h2
    have hM8 : M ^ 8 = 1 := by
      have h24 := sl23_pow24 M hdet
      have h2m : M ^ 2 ^ m = 1 := by
        rw [hM, ← Units.val_pow_eq_pow_val, ← map_pow, hm, map_one, Units.val_one]
      have h1 : orderOf M ∣ 24 := orderOf_dvd_of_pow_eq_one h24
      have h2 : orderOf M ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2m
      obtain ⟨j, -, hjm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
      rw [hjm] at h1
      have hj3 : j ≤ 3 := by
        by_contra h4
        push Not at h4
        have : 2 ^ 4 ∣ 24 := (Nat.pow_dvd_pow 2 h4).trans h1
        norm_num at this
      exact orderOf_dvd_iff_pow_eq_one.1 (hjm ▸ Nat.pow_dvd_pow 2 hj3)
    have hgM : g * M ≠ M * g := fun h =>
      hbx (Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h))
    have hgi : ((ψ xn⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = g * g := by
      have h1 : ψ xn⁻¹ = ψ xn * ψ xn := by
        rw [← map_mul]
        congr 1
        have : xn⁻¹ = xn ^ 2 := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hxn3]
        rw [this, sq]
      rw [h1, Units.val_mul]
    have hψb₂ : ((ψ (xn * b * xn⁻¹)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = g * M * (g * g) := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hgi]
    have hsq1 := sl23_sq g M hg3 hdet hM8 hgM
    have hsq2 := sl23_sq' g M hg3 hdet hM8 hgM
    have hsq3 := sl23_sq'' g M hg3 hdet hM8 hgM
    have hnc12 := sl23_ncomm g M hg3 hdet hM8 hgM
    have hb₂B : x * (b : Γ) * x⁻¹ ∈ B := hBn _ (mem_subgroupOf.1 hb) x hxN
    have hinv1 : ∀ y ∈ X, (b : Γ) ^ 2 * y * ((b : Γ) ^ 2)⁻¹ * y ∈ ⁅X, X⁆ := by
      have h1 := hinv (b ^ 2) (by rw [map_pow, Units.val_pow_eq_pow_val, sq, ← hM, hsq1])
      simpa using h1
    refine ⟨⟨(b : Γ), mem_subgroupOf.1 hb, x * (b : Γ) * x⁻¹, hb₂B, hinv1, ?_, ?_, ?_⟩, ?_⟩
    · have h1 := hinv ((xn * b * xn⁻¹) ^ 2)
        (by rw [map_pow, Units.val_pow_eq_pow_val, sq, hψb₂, hsq2])
      simpa [xn] using h1
    · have h1 := hinv ((b * (xn * b * xn⁻¹)) ^ 2)
        (by rw [map_pow, Units.val_pow_eq_pow_val, sq, map_mul, Units.val_mul, hψb₂, ← hM, hsq3])
      simpa [xn] using h1
    · have hne1 : ψ ⁅b, xn * b * xn⁻¹⁆ ≠ 1 := by
        intro h1
        apply hnc12
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
        have h2 : ψ b * ψ (xn * b * xn⁻¹) = ψ (xn * b * xn⁻¹) * ψ b := by
          calc ψ b * ψ (xn * b * xn⁻¹) = (ψ b * ψ (xn * b * xn⁻¹) * (ψ b)⁻¹ *
                (ψ (xn * b * xn⁻¹))⁻¹) * (ψ (xn * b * xn⁻¹) * ψ b) := by group
            _ = ψ (xn * b * xn⁻¹) * ψ b := by rw [h1, one_mul]
        have h3 := congrArg Units.val h2
        rw [Units.val_mul, Units.val_mul, hψb₂, ← hM] at h3
        exact h3
      obtain ⟨y, hy, hny⟩ := hnontriv _ hne1
      refine ⟨y, hy, ?_⟩
      simpa [xn, commutatorElement_def] using hny
    ·
      rcases hcard with h9 | ⟨h27, -⟩
      · exact h9
      exfalso
      set Φ : Subgroup Γ := ⁅X, X⁆ with hΦdef
      have hΦX : Φ ≤ X := commutator_le_left X X
      have hΦ3 : Nat.card Φ = 3 := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥X₀)
        rw [hWcard, ← hcardX, h27] at h1
        have h2 : Nat.card ↥(frattini ↥X₀) = 3 := by omega
        rw [hcommX, Subgroup.card_map_of_injective hf_inj, h2]
      have hΦcent : ∀ ζ ∈ Φ, ∀ y ∈ X, ζ * y = y * ζ := by
        intro ζ hζ y hy
        rw [hcommX] at hζ
        obtain ⟨z₁, hz₁, rfl⟩ := hζ
        obtain ⟨z₂, rfl⟩ := (hmemX y).1 hy
        have h1 : (z₁ : ↥P₀) ∈ centerOf X₀ := hX₀.frattini_le ⟨z₁, hz₁, rfl⟩
        have h2 := mem_centralizer_iff.1 h1.2 (z₂ : ↥P₀) z₂.2
        have h3 := congrArg P₀.subtype h2
        simp only [map_mul] at h3
        exact h3.symm
      obtain ⟨⟨z, hzΦ⟩, hzgen⟩ := (isCyclic_of_prime_card hΦ3).exists_generator
      have hzo : orderOf z = 3 := by
        rw [← Subgroup.orderOf_mk z hzΦ, orderOf_eq_card_of_forall_mem_zpowers hzgen, hΦ3]
      have hz3 : z ^ 3 = 1 := hzo ▸ pow_orderOf_eq_one z
      have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzo; norm_num at hzo
      have hΦel : ∀ y ∈ Φ, y = 1 ∨ y = z ∨ y = z ^ 2 := by
        intro y hy
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hzgen ⟨y, hy⟩)
        have hk' : z ^ k = y := by simpa using congrArg Subtype.val hk
        rw [← hk', ← zpow_mod_orderOf, hzo]
        have : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
        rcases this with h | h | h <;> rw [h] <;> simp
      have hsq : ∀ c : Γ, c * z * c⁻¹ = z ^ 2 → c ^ 2 * z * (c ^ 2)⁻¹ = z := by
        intro c h
        calc c ^ 2 * z * (c ^ 2)⁻¹ = c * (c * z * c⁻¹) * c⁻¹ := by rw [sq]; group
          _ = c * z ^ 2 * c⁻¹ := by rw [h]
          _ = (c * z * c⁻¹) ^ 2 := by rw [sq, sq]; group
          _ = (z ^ 2) ^ 2 := by rw [h]
          _ = z := by rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz3, one_mul,
                pow_one]
      have hconj : ∀ c : Γ, c * z * c⁻¹ = z ∨ c * z * c⁻¹ = z ^ 2 := by
        intro c
        have hm : c * z * c⁻¹ ∈ Φ := hCn.conj_mem z hzΦ c
        rcases hΦel _ hm with h | h | h
        · exfalso
          apply hz1
          have e1 : z = c⁻¹ * (c * z * c⁻¹) * c := by group
          rw [e1, h]
          group
        · exact Or.inl h
        · exact Or.inr h
      have hxz : x * z * x⁻¹ = z := by
        rcases hconj x with h | h
        · exact h
        · exfalso
          have h2 := hsq x h
          have h3 : x ^ 3 * z * (x ^ 3)⁻¹ = z ^ 2 := by
            calc x ^ 3 * z * (x ^ 3)⁻¹ = x * (x ^ 2 * z * (x ^ 2)⁻¹) * x⁻¹ := by
                  rw [pow_succ', sq]; group
              _ = x * z * x⁻¹ := by rw [h2]
              _ = z ^ 2 := h
          rw [hx3, one_mul, inv_one, mul_one] at h3
          apply hz1
          have h4 : z * z = z * 1 := by rw [← sq, ← h3, mul_one]
          exact mul_left_cancel h4
      set u : Γ := (b : Γ) ^ 2 with hu
      have huz : u * z * u⁻¹ = z := by
        rcases hconj (b : Γ) with h | h
        · calc u * z * u⁻¹ = (b : Γ) * ((b : Γ) * z * (b : Γ)⁻¹) * (b : Γ)⁻¹ := by
                rw [hu, sq]; group
            _ = z := by rw [h, h]
        · exact hsq _ h
      have hcentΦ : ∀ c : Γ, c * z * c⁻¹ = z → ∀ ζ ∈ Φ, c * ζ * c⁻¹ = ζ := by
        intro c hc ζ hζ
        rcases hΦel ζ hζ with rfl | rfl | rfl
        · group
        · exact hc
        · rw [show c * z ^ 2 * c⁻¹ = (c * z * c⁻¹) ^ 2 by rw [sq, sq]; group, hc]
      have hxΦ := hcentΦ x hxz
      have huΦ := hcentΦ u huz
      have huB : u ∈ B := pow_mem (mem_subgroupOf.1 hb) 2
      have hcB : x * u * x⁻¹ * u⁻¹ ∈ B := mul_mem (hBn u huB x hxN) (inv_mem huB)
      have hb2 : ψ (b ^ 2) = -1 :=
        Units.ext (by rw [map_pow, Units.val_pow_eq_pow_val, sq, ← hM, hsq1]; rfl)
      have hφc : φ (x * u * x⁻¹ * u⁻¹) = 1 := by
        have h1 : ψ (xn * b ^ 2 * xn⁻¹ * (b ^ 2)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hb2]
          simp
        have h2 : (elemAutEquivGL e) (φ (x * u * x⁻¹ * u⁻¹)) = 1 := h1
        rwa [MulEquiv.map_eq_one_iff] at h2
      have hxu : ∀ y ∈ X, (x * u * x⁻¹ * u⁻¹) * y = y * (x * u * x⁻¹ * u⁻¹) := by
        intro y hy
        have h1 := hcen _ hcB hφc
        exact (mem_centralizer_iff.1 h1 y (map_subtype_le _ hy)).symm
      obtain ⟨v, hv0, hgv⟩ := gl23_fix g hg3
      set w : W := e.symm (Multiplicative.ofAdd v) with hw
      have hφxw : φ x w = w := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        have h1 := elemAutEquivGL_mulVec e (φ x) w
        rw [← h1]
        have h2 : ((elemAutEquivGL e (φ x) : GL (Fin 2) (ZMod 3)) :
            Matrix (Fin 2) (Fin 2) (ZMod 3)) = g := rfl
        rw [h2, hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact hgv
      have hw1 : w ≠ 1 := by
        intro h1
        apply hv0
        have h2 : e w = 1 := by rw [h1, map_one]
        rw [hw, MulEquiv.apply_symm_apply] at h2
        exact h2
      obtain ⟨z₀, hz₀⟩ := QuotientGroup.mk_surjective w
      set a : Γ := f z₀ with ha_def
      have haX : a ∈ X := (hmemX a).2 ⟨z₀, rfl⟩
      have haΦ : a ∉ Φ := by
        intro h
        apply hw1
        rw [← hz₀]
        exact (QuotientGroup.eq_one_iff _).2 ((hmemC z₀).1 h)
      obtain ⟨z', hz', hφz⟩ := hφ_apply x z₀
      have hζ : a⁻¹ * (x * a * x⁻¹) ∈ Φ := by
        rw [← hz']
        refine (hW_eq z₀ z').1 ?_
        rw [← hφz, hz₀, hφxw]
      set ζ := a⁻¹ * (x * a * x⁻¹) with hζdef
      set ζ' := u * a * u⁻¹ * a with hζ'def
      have hζ' : ζ' ∈ Φ := hinv1 a haX
      have key : x * (u * a * u⁻¹) * x⁻¹ = u * (x * a * x⁻¹) * u⁻¹ := by
        have hmem : u * (x * a * x⁻¹) * u⁻¹ ∈ X :=
          hnormal.conj_mem _ (hnormal.conj_mem a haX x) u
        have h1 := hxu _ hmem
        calc x * (u * a * u⁻¹) * x⁻¹ = (x * u * x⁻¹ * u⁻¹) * (u * (x * a * x⁻¹) * u⁻¹) *
              (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
          _ = u * (x * a * x⁻¹) * u⁻¹ := by rw [h1]; group
      have e1 : u * a * u⁻¹ = ζ' * a⁻¹ := by rw [hζ'def]; group
      have e2 : x * a * x⁻¹ = a * ζ := by rw [hζdef]; group
      rw [e1, e2] at key
      have l1 : x * (ζ' * a⁻¹) * x⁻¹ = ζ' * (a * ζ)⁻¹ := by
        calc x * (ζ' * a⁻¹) * x⁻¹ = (x * ζ' * x⁻¹) * (x * a * x⁻¹)⁻¹ := by group
          _ = ζ' * (a * ζ)⁻¹ := by rw [hxΦ ζ' hζ', e2]
      have l2 : u * (a * ζ) * u⁻¹ = ζ' * (a⁻¹ * ζ) := by
        calc u * (a * ζ) * u⁻¹ = (u * a * u⁻¹) * (u * ζ * u⁻¹) := by group
          _ = ζ' * (a⁻¹ * ζ) := by rw [e1, huΦ ζ hζ]; group
      rw [l1, l2] at key
      have k1 : ζ⁻¹ * a⁻¹ = a⁻¹ * ζ := by
        have h1 := mul_left_cancel key
        rwa [mul_inv_rev] at h1
      have hζa : ζ * a⁻¹ = a⁻¹ * ζ := hΦcent ζ hζ a⁻¹ (inv_mem haX)
      rw [← hζa] at k1
      have hζζ : ζ⁻¹ = ζ := mul_right_cancel k1
      have hζ1 : ζ = 1 := by
        have h2 : ζ * ζ = 1 := by
          calc ζ * ζ = ζ⁻¹ * ζ := by rw [hζζ]
            _ = 1 := inv_mul_cancel ζ
        have h3 : ζ ^ 3 = 1 := hpow ζ (hΦX hζ)
        calc ζ = ζ ^ 3 * (ζ * ζ)⁻¹ := by rw [pow_succ, sq]; group
          _ = 1 := by rw [h3, h2]; group
      have hxa : a * x = x * a := by
        have h1 : x * a * x⁻¹ = a := by rw [e2, hζ1, mul_one]
        calc a * x = x * a * x⁻¹ * x := by rw [h1]
          _ = x * a := by group
      have hxX : x ∉ X := by
        intro hxX
        obtain ⟨y, hy, hny⟩ := hact
        apply hny
        have := commutator_mem_commutator hxX hy
        rwa [commutatorElement_def] at this
      have ha1 : a ≠ 1 := fun h => haΦ (h ▸ one_mem Φ)
      have hao : orderOf a = 3 := orderOf_eq_prime (hpow a haX) ha1
      have hxo : orderOf x = 3 := orderOf_eq_prime hx3 (fun h => hxX (h ▸ one_mem X))
      have hE1 : IsElemAbelian 3 (zpowers a) := by
        refine ⟨inferInstance, fun y hy => ?_⟩
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow a haX, one_zpow]
      have hza : ∀ c ∈ zpowers a, Commute c z := by
        intro c hc
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
        exact Commute.zpow_left (hΦcent z hzΦ a haX).symm k
      have hzE1 : z ∉ zpowers a := by
        intro hz
        apply haΦ
        have hle : zpowers z ≤ zpowers a := zpowers_le.2 hz
        have heq : zpowers z = zpowers a := Subgroup.eq_of_le_of_card_ge hle
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hao])
        have : a ∈ zpowers z := heq ▸ mem_zpowers a
        exact (zpowers_le.2 hzΦ) this
      obtain ⟨hE2, hE2c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE1 hzo hza hzE1
      have hE2X : zpowers a ⊔ zpowers z ≤ X :=
        sup_le (zpowers_le.2 haX) (zpowers_le.2 (hΦX hzΦ))
      have hxE2 : ∀ c ∈ zpowers a ⊔ zpowers z, Commute c x := by
        have hle : zpowers a ⊔ zpowers z ≤ centralizer ({x} : Set Γ) := by
          refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
          · rw [mem_centralizer_singleton_iff]
            exact hxa
          · rw [mem_centralizer_singleton_iff]
            calc z * x = x * z * x⁻¹ * x := by rw [hxz]
              _ = x * z := by group
        intro c hc
        exact mem_centralizer_singleton_iff.1 (hle hc)
      obtain ⟨hE3, hE3c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE2 hxo hxE2
        (fun h => hxX (hE2X h))
      have hcard27 : Nat.card ↥(zpowers a ⊔ zpowers z ⊔ zpowers x) = 3 ^ 3 := by
        rw [hE3c, hE2c, Nat.card_zpowers, hao]
        norm_num
      have h3 := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (le_top : _ ≤ (⊤ : Subgroup Γ))
        hE3 hcard27
      omega
  exact ⟨X, ⟨map_subtype_le _, hnormal, hpow, hcard, hirred, hact, hrank2,
    fun h => (hq8 h).1, fun h => (hq8 h).2⟩⟩

end CFSG.Quasithin.H13.U3
