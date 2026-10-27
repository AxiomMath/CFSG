module

public import CFSG.RankThree.GF2n.Smith81.LinCoord
public import CFSG.RankThree.GF2n.Smith81.LinOddAssembly

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

@[expose] def Lin28CondStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B X : Subgroup G) (x : G) (n : ℕ)
    (V₁ V₂ : Subgroup G), Smith1981Below (Nat.card G) → Ctx M Q Z B →
    LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → Sit M Q Z X x → Q ⊓ QB X ≠ ⊥ →
      ∃ A : Subgroup G, IsZConjugate Z A ∧ A ≤ Q ⊓ QB X

@[expose] def LinModuleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      ∀ Y : Subgroup G, IsZConjugate Z Y → Y ≠ Z →
        (Y ≤ V₁ → V₁ ≤ QB Y) ∧ (Y ≤ V₂ → V₂ ≤ QB Y)

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem lin_x_mem_Lgen (hF : LinSwapStatement) (hN : LinNonswapStatement)
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn3 : 3 ≤ n)
    (h31 : ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {X : Subgroup G} {x : G}
    (hs : Sit M Q Z X x) {A : Subgroup G} (hA : IsZConjugate Z A) (hAQ : A ≤ Q)
    (hAX : A ≤ QB X) (hAZ : A ≠ Z) : x ∈ Lgen M (LB M Q B) := by
  have H := hc.hyp
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, -, -, -, -⟩ := hS.basic
  have h12 := smith_1_12 hs
  have hxH : x ∈ H0 M Z := h12.1 hs.mem
  have hAZbot : Z ⊓ A = ⊥ := by
    obtain ⟨g, rfl⟩ := hA
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
  have hAne : A ≠ ⊥ := by
    intro h
    have h1 : Nat.card A = Nat.card Z := IsZConjugate.card_eq hA
    rw [h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haZ : a ∉ Z := fun haZ => by
    have : a ∈ Z ⊓ A := ⟨haZ, haA⟩
    rw [hAZbot, Subgroup.mem_bot] at this
    exact ha1' this
  have hcomm : x * a = a * x := hs.QB_comm_X hs.mem (hAX haA)
  have haV : a ∈ V₁ ∨ a ∈ V₂ := (h31 a (hAQ haA) ha1').mp (inZClass_of_mem_root hA haA ha1')
  have hpres : conjSubgroup x V₁ = V₁ := by
    rcases hF G M Q Z B n V₁ V₂ hc hS hn3 x hxH with h | h
    · exact h.1
    · exfalso
      apply haZ
      have hfix : x * a * x⁻¹ = a := by rw [hcomm]; group
      have hmem : a ∈ V₁ ⊓ V₂ := by
        rcases haV with hV | hV
        · refine ⟨hV, ?_⟩
          have : x * a * x⁻¹ ∈ conjSubgroup x V₁ := by
            rw [mem_conjSubgroup]; simpa [mul_assoc] using hV
          rw [hfix, h.1] at this
          exact this
        · refine ⟨?_, hV⟩
          have : x * a * x⁻¹ ∈ conjSubgroup x V₂ := by
            rw [mem_conjSubgroup]; simpa [mul_assoc] using hV
          rw [hfix, h.2] at this
          exact this
      rwa [hint] at hmem
  exact hN G M Q Z B n V₁ V₂ hc hS hn3 x hxH (by rw [hs.x_sq]; exact Q.one_mem) hpres

theorem linPair_unique (hc : Ctx M Q Z B) {V₁ V₂ V₁' V₂' : Subgroup G}
    (hS : LinSetup M Q Z B n V₁ V₂) (hS' : LinSetup M Q Z B n V₁' V₂') (hn : 3 ≤ n) :
    (V₁' = V₁ ∧ V₂' = V₂) ∨ (V₁' = V₂ ∧ V₂' = V₁) := by
  obtain ⟨hZ₁, hV₁Q, hZ₂, hV₂Q, hint, -, -, -, hc₁, hc₂⟩ := hS.basic
  obtain ⟨hZ₁', hV₁'Q, hZ₂', hV₂'Q, hint', -, hN₁', hN₂', hc₁', hc₂'⟩ := hS'.basic
  have hW := LinSetup.width hc.hyp hS
  have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨K, _, _, _, γ, M₀, φ, F, _, _, _, ρ', C, -, -, hφπ, -, -, hrange, hV₁, hV₂, -⟩ :=
    exists_linCoord hc hS hn
  have key : ∀ V : Subgroup G, Z ≤ V → V ≤ Q →
      (∀ t ∈ Lgen M (LB M Q B), t ∈ Subgroup.normalizer (V : Set G)) →
      Nat.card V = Nat.card Z ^ (n + 1) → V = V₁ ∨ V = V₂ := by
    intro V hZV hVQ hNV hcV
    have hinv : ∀ (g : ↥(Lgen M (LB M Q B))) (e : M₀.E), e ∈ M₀.img V →
        (φ.comp (Subgroup.inclusion hSH)) g e ∈ M₀.img V := by
      intro g e he
      obtain ⟨u, huV, huQ, rfl⟩ := he
      have h1 := hφπ (Subgroup.inclusion hSH g) u huQ
      have h2 : (g : G) * u * (g : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hNV g g.2) u).mp huV
      have h3 : (g : G) * u * (g : G)⁻¹ ∈ Q := hVQ h2
      show φ (Subgroup.inclusion hSH g) (M₀.π u) ∈ M₀.img V
      rw [← h1]
      exact M₀.pi_mem_img h2 h3
    rcases C.invariant_classification hn hrange (M₀.img V) hinv with h | h | h | h
    · exfalso
      have hle : V ≤ Z := by
        intro u hu
        have : M₀.π u ∈ M₀.img V := M₀.pi_mem_img hu (hVQ hu)
        rw [h] at this
        exact (M₀.π_ker u (hVQ hu)).mp this
      have := Subgroup.card_le_of_le hle
      rw [hcV] at this
      have hlt : Nat.card Z ^ 1 < Nat.card Z ^ (n + 1) :=
        Nat.pow_lt_pow_right (by omega) (by omega)
      rw [pow_one] at hlt
      omega
    · left
      have hW₁ : ∀ e, e ∈ M₀.img V ↔ e ∈ M₀.img V₁ := fun e => by
        rw [h, C.mem_W₁, hV₁ e]
      apply le_antisymm
      · intro x hx
        exact (M₀.mem_img_iff hZ₁ (hVQ hx)).mp ((hW₁ _).mp (M₀.pi_mem_img hx (hVQ hx)))
      · intro x hx
        exact (M₀.mem_img_iff hZV (hV₁Q hx)).mp ((hW₁ _).mpr (M₀.pi_mem_img hx (hV₁Q hx)))
    · right
      have hW₂ : ∀ e, e ∈ M₀.img V ↔ e ∈ M₀.img V₂ := fun e => by
        rw [h, C.mem_W₂, hV₂ e]
      apply le_antisymm
      · intro x hx
        exact (M₀.mem_img_iff hZ₂ (hVQ hx)).mp ((hW₂ _).mp (M₀.pi_mem_img hx (hVQ hx)))
      · intro x hx
        exact (M₀.mem_img_iff hZV (hV₂Q hx)).mp ((hW₂ _).mpr (M₀.pi_mem_img hx (hV₂Q hx)))
    · exfalso
      have hQV : Q ≤ V := by
        intro x hx
        exact (M₀.mem_img_iff hZV hx).mp (by rw [h]; trivial)
      have hle := Subgroup.card_le_of_le hQV
      rw [hW, hcV] at hle
      have := Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z) |>.mp hle
      omega
  have h1 := key V₁' hZ₁' hV₁'Q hN₁' hc₁'
  have h2 := key V₂' hZ₂' hV₂'Q hN₂' hc₂'
  have hne : V₁' ≠ V₂' := by
    intro h
    have : V₁' = Z := by rw [← hint', ← h, inf_idem]
    have hcard : Nat.card Z = Nat.card Z ^ (n + 1) := by rw [← hc₁', this]
    have hlt : Nat.card Z ^ 1 < Nat.card Z ^ (n + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    rw [pow_one] at hlt
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem exists_mem_ne_Z (H : StrothHyp M Q Z) {A : Subgroup G} (hA : IsZConjugate Z A)
    (hAZ : A ≠ Z) : ∃ a ∈ A, a ≠ 1 ∧ a ∉ Z := by
  have hZA : Z ⊓ A = ⊥ := by
    obtain ⟨g, rfl⟩ := hA
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
  have hAne : A ≠ ⊥ := by
    intro h
    have h1 : Nat.card A = Nat.card Z := IsZConjugate.card_eq hA
    rw [h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine ⟨a, haA, ha1', fun haZ => ?_⟩
  have : a ∈ Z ⊓ A := ⟨haZ, haA⟩
  rw [hZA, Subgroup.mem_bot] at this
  exact ha1' this

theorem OddSetup.not_mem_QB_of_dual {V V' : Subgroup G} (S : OddSetup M Q Z B V V')
    {Y : Subgroup G} (hY : IsZConjugate Z Y) (hYZ : Y ≠ Z) (hYV : Y ≤ V) {u : G}
    (huV' : u ∈ V') (huZ : u ∉ Z) : u ∉ QB Y := by
  intro huQ
  have H := S.hyp
  have hZY : Z ⊓ Y = ⊥ := by
    obtain ⟨g, rfl⟩ := hY
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hYZ
  obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Z_ne_bot H)
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  obtain ⟨g, hg⟩ := hY
  have hu1 : u ≠ 1 := fun h => huZ (h ▸ Z.one_mem)
  have hu' : g⁻¹ * u * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at huQ
    exact mem_conjSubgroup.mp huQ
  have hu'1 : g⁻¹ * u * g ≠ 1 := fun h => hu1 (by
    have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hucl : InZClass Z u := (S.p31 u (S.V'Q huV') hu1).mpr (Or.inr huV')
  have hu'cl : InZClass Z (g⁻¹ * u * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := u) g⁻¹).mpr hucl
    simpa using this
  set b : G := g * z₀ * g⁻¹ with hb
  have hbY : b ∈ Y := by
    rw [hg, mem_conjSubgroup, hb]; simpa [mul_assoc] using hz₀
  have hb1 : b ≠ 1 := fun h => hz₀1' (by
    have : z₀ = g⁻¹ * b * g := by rw [hb]; group
    rw [this, h]; group)
  have hbZ : b ∉ Z := fun h => by
    have : b ∈ Z ⊓ Y := ⟨h, hbY⟩
    rw [hZY, Subgroup.mem_bot] at this
    exact hb1 this
  have hbV : b ∈ V := hYV hbY
  have hbQ : b ∈ Q := S.VQ hbV
  have huQ' : u ∈ Q := S.V'Q huV'
  have hz₀Q : z₀ ∈ Q := H.Z_normal.1 hz₀
  have hw : g⁻¹ * (b * u) * g = z₀ * (g⁻¹ * u * g) := by rw [hb]; group
  have hw1 : z₀ * (g⁻¹ * u * g) ≠ 1 := by
    intro h
    apply huZ
    have h1 : g⁻¹ * u * g = z₀⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : u = g * z₀⁻¹ * g⁻¹ := by
      have : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      rw [this, h1]
    have h3 : u ∈ Y := by
      rw [hg, mem_conjSubgroup, h2]
      simpa [mul_assoc] using Z.inv_mem hz₀
    have : u ∈ V ⊓ V' := ⟨hYV h3, huV'⟩
    rwa [S.int] at this
  have hw2 : InZClass Z (z₀ * (g⁻¹ * u * g)) := by
    rcases (S.p31 _ hu' hu'1).mp hu'cl with h | h
    · exact (S.p31 _ (Q.mul_mem hz₀Q hu') hw1).mpr (Or.inl (V.mul_mem (S.ZV hz₀) h))
    · exact (S.p31 _ (Q.mul_mem hz₀Q hu') hw1).mpr (Or.inr (V'.mul_mem (S.ZV' hz₀) h))
  have hbu : InZClass Z (b * u) := by
    have h2 : InZClass Z (g⁻¹ * (b * u) * g) := by rw [hw]; exact hw2
    exact (inZClass_conj_iff (Z := Z) (v := b * u) g⁻¹).mp (by simpa using h2)
  have hbu1 : b * u ≠ 1 := by
    intro h
    have h1 : u = b⁻¹ := eq_inv_of_mul_eq_one_right h
    apply huZ
    have : u ∈ V ⊓ V' := ⟨by rw [h1]; exact V.inv_mem hbV, huV'⟩
    rwa [S.int] at this
  rcases (S.p31 _ (Q.mul_mem hbQ huQ') hbu1).mp hbu with h | h
  · apply huZ
    have h1 : u ∈ V := by
      have e : u = b⁻¹ * (b * u) := by group
      rw [e]; exact V.mul_mem (V.inv_mem hbV) h
    have : u ∈ V ⊓ V' := ⟨h1, huV'⟩
    rwa [S.int] at this
  · apply hbZ
    have h1 : b ∈ V' := by
      have e : b = (b * u) * u⁻¹ := by group
      rw [e]; exact V'.mul_mem h (V'.inv_mem huV')
    have : b ∈ V ⊓ V' := ⟨hbV, h1⟩
    rwa [S.int] at this

theorem c4_core {V V' : Subgroup G} (S : OddSetup M Q Z B V V') {g x z' : G} (hxQ : x ∉ Q)
    (hx'Q : g⁻¹ * x * g ∈ Q) (hx'1 : g⁻¹ * x * g ≠ 1) (hz''Q : g⁻¹ * z' * g ∈ Q)
    (hz''Z : g⁻¹ * z' * g ∉ Z) (hz''V : g⁻¹ * z' * g ∈ V)
    (hx'cl : InZClass Z (g⁻¹ * x * g)) (hwcl : InZClass Z (g⁻¹ * x * g * (g⁻¹ * z' * g)))
    (hw1 : g⁻¹ * x * g * (g⁻¹ * z' * g) ≠ 1)
    (hα : V ≤ QB (conjSubgroup g⁻¹ Z)) : False := by
  have H := S.hyp
  by_cases hx'V : g⁻¹ * x * g ∈ V
  · have h1 := hα hx'V
    rw [QB_conj_eq H g⁻¹, mem_conjSubgroup] at h1
    apply hxQ
    have e : g⁻¹⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h1
    exact h1
  · have hx'V' : g⁻¹ * x * g ∈ V' := by
      rcases (S.p31 _ hx'Q hx'1).mp hx'cl with h | h
      · exact absurd h hx'V
      · exact h
    have hwQ : g⁻¹ * x * g * (g⁻¹ * z' * g) ∈ Q := Q.mul_mem hx'Q hz''Q
    rcases (S.p31 _ hwQ hw1).mp hwcl with h | h
    · apply hx'V
      have e : g⁻¹ * x * g =
          g⁻¹ * x * g * (g⁻¹ * z' * g) * (g⁻¹ * z' * g)⁻¹ := by group
      rw [e]
      exact V.mul_mem h (V.inv_mem hz''V)
    · apply hz''Z
      have hz'V' : g⁻¹ * z' * g ∈ V' := by
        have e : g⁻¹ * z' * g =
            (g⁻¹ * x * g)⁻¹ * (g⁻¹ * x * g * (g⁻¹ * z' * g)) := by group
        rw [e]
        exact V'.mul_mem (V'.inv_mem hx'V') h
      rw [← S.int]
      exact ⟨hz''V, hz'V'⟩

theorem lin212C4_of (h28 : Lin28CondStatement) (hα : LinModuleStatement)
    (h31 : Lin31Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
        Lin212C4Prop M Q Z := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn3 X x hs hne z' hz' hcl
  by_contra hz1
  have H := hc.hyp
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := h31 G M Q Z B n V₁ V₂ hb hc hS (by omega)
  have SS := OddSetup.of_linSetup hc hS' h31'
  obtain ⟨A, hA, hAle⟩ := h28 G M Q Z B X x n V₁ V₂ hb hc hS hn3 hs hne
  have hAQ : A ≤ Q := hAle.trans inf_le_left
  have hAX : A ≤ QB X := hAle.trans inf_le_right
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have hxA : x ∈ QB A := (IsZConjugate.le_QB_iff H hA hs.conj).mpr hAX hs.mem
  have hZA : z' ∈ QB A := SS.Z_le_QB hA hAQ hz'
  have hZAbot : Z ⊓ A = ⊥ := by
    obtain ⟨g, rfl⟩ := hA
    exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
  obtain ⟨g, hg⟩ := hA
  have hx'Q : g⁻¹ * x * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hxA
    exact mem_conjSubgroup.mp hxA
  have hz''Q : g⁻¹ * z' * g ∈ Q := by
    rw [hg, QB_conj_eq H g] at hZA
    exact mem_conjSubgroup.mp hZA
  have hxQ : x ∉ Q := hs.notQ
  have hx1 : x ≠ 1 := hs.ne_one
  have hx'1 : g⁻¹ * x * g ≠ 1 := fun h => hx1 (by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''1 : g⁻¹ * z' * g ≠ 1 := fun h => hz1 (by
    have : z' = g * (g⁻¹ * z' * g) * g⁻¹ := by group
    rw [this, h]; group)
  have hz''Z : g⁻¹ * z' * g ∉ Z := by
    intro h
    apply hz''1
    have hz'A : z' ∈ A := by
      rw [hg, mem_conjSubgroup]; simpa [mul_assoc] using h
    have : z' ∈ Z ⊓ A := ⟨hz', hz'A⟩
    rw [hZAbot, Subgroup.mem_bot] at this
    rw [this]; group
  have hx'cl : InZClass Z (g⁻¹ * x * g) := by
    have := (inZClass_conj_iff (Z := Z) (v := x) g⁻¹).mpr
      (inZClass_of_mem_root hs.conj hs.mem hs.ne_one)
    simpa using this
  have hwcl : InZClass Z (g⁻¹ * x * g * (g⁻¹ * z' * g)) := by
    have := (inZClass_conj_iff (Z := Z) (v := x * z') g⁻¹).mpr hcl
    simpa [mul_assoc] using this
  have hw1 : g⁻¹ * x * g * (g⁻¹ * z' * g) ≠ 1 := by
    intro h
    have h1 : x * z' = 1 := by
      have : x * z' = g * (g⁻¹ * x * g * (g⁻¹ * z' * g)) * g⁻¹ := by group
      rw [this, h]; group
    apply hxQ
    have : x = z'⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact Q.inv_mem (H.Z_normal.1 hz')
  set Y : Subgroup G := conjSubgroup g⁻¹ Z with hYdef
  have hY : IsZConjugate Z Y := ⟨g⁻¹, rfl⟩
  have hz''Y : g⁻¹ * z' * g ∈ Y := by
    rw [hYdef, mem_conjSubgroup]; simpa [mul_assoc] using hz'
  have hYZ : Y ≠ Z := fun h => hz''Z (h ▸ hz''Y)
  have hα' := hα G M Q Z B n V₁' V₂' hb hc hS' hn3 Y hY hYZ
  rcases (SS.p31 _ hz''Q hz''1).mp (inZClass_of_mem_root hY hz''Y hz''1) with hV | hV
  · obtain ⟨hYV, -, -⟩ := SS.root_le_V hY hz''Y hV hz''Z
    exact c4_core SS hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα'.1 hYV)
  · obtain ⟨hYV, -, -⟩ := SS.symm.root_le_V hY hz''Y hV hz''Z
    exact c4_core SS.symm hxQ hx'Q hx'1 hz''Q hz''Z hV hx'cl hwcl hw1 (hα'.2 hYV)

theorem lin212Cond_of (h28 : Lin28CondStatement) (hα : LinModuleStatement)
    (h7 : Lin212C7Statement) (h31 : Lin31Statement) : Lin212CondStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn3 X x hs hne
  have H := hc.hyp
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := h31 G M Q Z B n V₁ V₂ hb hc hS (by omega)
  have hpair := linPair_unique hc hS hS' hn3
  obtain ⟨A, hA, hAle⟩ := h28 G M Q Z B X x n V₁ V₂ hb hc hS hn3 hs hne
  have hAQ : A ≤ Q := hAle.trans inf_le_left
  have hAX : A ≤ QB X := hAle.trans inf_le_right
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have c1 : x ∈ Lgen M (LB M Q B) :=
    lin_x_mem_Lgen linSwapStatement_holds linNonswapStatement_holds hc hS' hn3 h31' hs hA hAQ hAX
      hAZ
  have c4 : Lin212C4Prop M Q Z := lin212C4_of h28 hα h31 G M Q Z B n V₁ V₂ hb hc hS hn3
  suffices hh : HasDimOn V₁ Z 1 x ∧ HasDimOn V₂ Z 1 x from
    ⟨c1, hh.1, hh.2, c4 X x hs hne, h7 G M Q Z B n V₁ V₂ hb hc hS hn3 X x hs hne⟩
  have SS := OddSetup.of_linSetup hc hS' h31'
  obtain ⟨a, haA, ha1, haZ⟩ := exists_mem_ne_Z H hA hAZ
  have hAunion : (A : Set G) ⊆ (V₁' : Set G) ∪ (V₂' : Set G) := by
    intro a' ha'
    by_cases ha'1 : a' = 1
    · left; rw [ha'1]; exact V₁'.one_mem
    · exact (h31' a' (hAQ ha') ha'1).mp (inZClass_of_mem_root hA ha' ha'1)
  have hxX : x ∈ QB A := by
    have := (IsZConjugate.le_QB_iff H hA hs.conj).mpr hAX
    exact this hs.mem
  have hxQ : x ∉ Q := hs.notQ
  obtain ⟨k, hk1, hkn, hk₁, hk₂⟩ :=
    linRankBoundStatement_holds G M Q Z B n V₁' V₂' hc hS' x c1 hxQ
      (by rw [hs.x_sq]; exact Q.one_mem)
  have hle1 : ∀ W W' : Subgroup G, OddSetup M Q Z B W W' → A ≤ W →
      Nat.card ↥(⁅W, Subgroup.zpowers x⁆ ⊔ Z) ≤ Nat.card Z ^ 2 := by
    intro W W' SW hAW
    have hWA : W ≤ QB A := SW.V_le_QB c4 hA haA (hAW haA) haZ
    have hcomm : ⁅W, Subgroup.zpowers x⁆ ≤ A := by
      rw [Subgroup.commutator_le]
      intro v hv t ht
      have htA : t ∈ QB A := (Subgroup.zpowers_le.mpr hxX) ht
      exact IsZConjugate.comm_mem_QB H hA (hWA hv) htA
    have hZA : Z ⊓ A = ⊥ := by
      obtain ⟨g, rfl⟩ := hA
      exact inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ
    have h2 : Nat.card ↥(A ⊔ Z) = Nat.card Z ^ 2 := by
      rw [card_sup_of_comm_inf_bot (fun a ha z hz => (SW.abV a (hAW ha) z (SW.ZV hz)))
        (by rw [inf_comm]; exact hZA), IsZConjugate.card_eq (Z := Z) hA, pow_two]
    rw [← h2]
    exact Subgroup.card_le_of_le (sup_le_sup_right hcomm Z)
  have hk : k = 1 := by
    rcases SubgroupClass.subset_union.mp hAunion with hW | hW
    · have := hle1 V₁' V₂' SS hW
      have h3 : Nat.card ↥(⁅V₁', Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (k + 1) := hk₁
      rw [h3] at this
      have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
      have := (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z)).mp this
      omega
    · have := hle1 V₂' V₁' SS.symm hW
      have h3 : Nat.card ↥(⁅V₂', Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ (k + 1) := hk₂
      rw [h3] at this
      have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
      have := (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z)).mp this
      omega
  rw [hk] at hk₁ hk₂
  rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at hk₁; rw [e2] at hk₂; exact ⟨hk₁, hk₂⟩
  · rw [e1] at hk₁; rw [e2] at hk₂; exact ⟨hk₂, hk₁⟩

end CFSG.RankThree.GF2n.Smith81
