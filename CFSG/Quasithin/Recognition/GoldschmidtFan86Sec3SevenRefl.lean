module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SevenArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec3Seven

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mem_lineK_zpow (F : FanTree Γ G) (T : Track Γ G) (m : ℤ) {i j : ℤ} (hij : j = i + 2 * m)
    (h : G) : h ∈ lineK Γ G T.line j ↔ (T.τ ^ m)⁻¹ * h * T.τ ^ m ∈ lineK Γ G T.line i := by
  subst hij
  have := F.mem_nbrStab_smul_iff (T.τ ^ m) (T.line.vert i) (h := h)
  rwa [T.zpow_smul_vert] at this

theorem ls4_of_add_two_mul (F : FanTree Γ G) (T : Track Γ G) {b b' : ℤ} (m : ℤ)
    (hb : b' = b + 2 * m) (hL : LS4 Γ G T.line b) : LS4 Γ G T.line b' := by
  intro g g1 g2 g3
  have c1 := (mem_lineK_zpow F T m (i := b + 1) (j := b' + 1) (by omega) g).1 g1
  have c2 := (mem_lineK_zpow F T m (i := b + 2) (j := b' + 2) (by omega) g).1 g2
  have c3 := (mem_lineK_zpow F T m (i := b + 3) (j := b' + 3) (by omega) g).1 g3
  exact (mem_lineK_zpow F T m hb g).2 (hL _ c1 c2 c3)

theorem rs4_of_add_two_mul (F : FanTree Γ G) (T : Track Γ G) {b b' : ℤ} (m : ℤ)
    (hb : b' = b + 2 * m) (hR : RS4 Γ G T.line b) : RS4 Γ G T.line b' := by
  intro g g1 g2 g3
  have c1 := (mem_lineK_zpow F T m (i := b + 1) (j := b' + 1) (by omega) g).1 g1
  have c2 := (mem_lineK_zpow F T m (i := b + 2) (j := b' + 2) (by omega) g).1 g2
  have c3 := (mem_lineK_zpow F T m (i := b + 3) (j := b' + 3) (by omega) g).1 g3
  exact (mem_lineK_zpow F T m (i := b + 4) (j := b' + 4) (by omega) g).2 (hR _ c1 c2 c3)

theorem lenTwo_smul_vert {ℓ : Line Γ} {c : ℤ} {f : G} (hf : IsLenTwoReflection ℓ c f) {i : ℤ}
    (h1 : c - 2 ≤ i) (h2 : i ≤ c + 2) : f • ℓ.vert i = ℓ.vert (2 * c - i) := by
  obtain ⟨hff, h0, h1', h2'⟩ := hf
  have hinv : ∀ v : V, f • f • v = v := fun v => by rw [← mul_smul, hff, one_smul]
  have e : i = c - 2 ∨ i = c - 1 ∨ i = c ∨ i = c + 1 ∨ i = c + 2 := by omega
  rcases e with e | e | e | e | e
  · rw [e, show 2 * c - (c - 2) = c + 2 by ring]
    calc f • ℓ.vert (c - 2) = f • f • ℓ.vert (c + 2) := by rw [h2']
      _ = ℓ.vert (c + 2) := hinv _
  · rw [e, show 2 * c - (c - 1) = c + 1 by ring]
    calc f • ℓ.vert (c - 1) = f • f • ℓ.vert (c + 1) := by rw [h1']
      _ = ℓ.vert (c + 1) := hinv _
  · rw [e, show 2 * c - c = c by ring]
    exact h0
  · rw [e, show 2 * c - (c + 1) = c - 1 by ring]
    exact h1'
  · rw [e, show 2 * c - (c + 2) = c - 2 by ring]
    exact h2'

theorem mem_lineK_refl (F : FanTree Γ G) {ℓ : Line Γ} {c : ℤ} {f : G}
    (hf : IsLenTwoReflection ℓ c f) {i j : ℤ} (hij : i + j = 2 * c) (h1 : c - 2 ≤ i)
    (h2 : i ≤ c + 2) (h : G) : h ∈ lineK Γ G ℓ j ↔ f⁻¹ * h * f ∈ lineK Γ G ℓ i := by
  have hj : j = 2 * c - i := by omega
  subst hj
  have := F.mem_nbrStab_smul_iff f (ℓ.vert i) (h := h)
  rwa [lenTwo_smul_vert hf h1 h2] at this

theorem ls4_iff_rs4_refl (F : FanTree Γ G) {ℓ : Line Γ} {c : ℤ} {f : G}
    (hf : IsLenTwoReflection ℓ c f) {b b' : ℤ} (hb' : b' = 2 * c - b - 4) (hb1 : c - 2 ≤ b)
    (hb2 : b ≤ c - 1) : LS4 Γ G ℓ b ↔ RS4 Γ G ℓ b' := by
  have K : ∀ i j : ℤ, i + j = 2 * c → c - 2 ≤ i → i ≤ c + 2 → ∀ h : G,
      h ∈ lineK Γ G ℓ j ↔ f⁻¹ * h * f ∈ lineK Γ G ℓ i :=
    fun i j hij h1 h2 h => mem_lineK_refl F hf hij h1 h2 h
  constructor
  · intro H g g1 g2 g3
    have c1 := (K (b + 3) (b' + 1) (by omega) (by omega) (by omega) g).1 g1
    have c2 := (K (b + 2) (b' + 2) (by omega) (by omega) (by omega) g).1 g2
    have c3 := (K (b + 1) (b' + 3) (by omega) (by omega) (by omega) g).1 g3
    exact (K b (b' + 4) (by omega) (by omega) (by omega) g).2 (H _ c3 c2 c1)
  · intro H g g1 g2 g3
    have c1 := (K (b' + 3) (b + 1) (by omega) (by omega) (by omega) g).1 g1
    have c2 := (K (b' + 2) (b + 2) (by omega) (by omega) (by omega) g).1 g2
    have c3 := (K (b' + 1) (b + 3) (by omega) (by omega) (by omega) g).1 g3
    exact (K (b' + 4) b (by omega) (by omega) (by omega) g).2 (H _ c3 c2 c1)

theorem exists_ls4_and_rs4 (F : FanTree Γ G) (T : Track Γ G) (hT : HasLenTwoReflection Γ G T)
    {a : ℤ} (ha : LS4 Γ G T.line a ∨ RS4 Γ G T.line a) :
    ∃ b, LS4 Γ G T.line b ∧ RS4 Γ G T.line b := by
  obtain ⟨c, f, hf⟩ := hT
  obtain ⟨m, hm⟩ : ∃ m : ℤ, a = c - 2 + 2 * m ∨ a = c - 1 + 2 * m :=
    ⟨(a - c + 2) / 2, by omega⟩
  rcases ha with hL | hR
  · rcases hm with hm | hm
    · have h1 : LS4 Γ G T.line (c - 2) := ls4_of_add_two_mul F T (-m) (by omega) hL
      exact ⟨c - 2, h1, (ls4_iff_rs4_refl F hf (b := c - 2) (b' := c - 2) (by ring) (by omega)
        (by omega)).1 h1⟩
    · have h1 : LS4 Γ G T.line (c - 1) := ls4_of_add_two_mul F T (-m) (by omega) hL
      exact ⟨c - 3, ls4_of_add_two_mul F T (-1) (by omega) h1,
        (ls4_iff_rs4_refl F hf (b := c - 1) (b' := c - 3) (by ring) (by omega) (by omega)).1 h1⟩
  · rcases hm with hm | hm
    · have h1 : RS4 Γ G T.line (c - 2) := rs4_of_add_two_mul F T (-m) (by omega) hR
      exact ⟨c - 2, (ls4_iff_rs4_refl F hf (b := c - 2) (b' := c - 2) (by ring) (by omega)
        (by omega)).2 h1, h1⟩
    · have h1 : RS4 Γ G T.line (c - 3) := rs4_of_add_two_mul F T (-m - 1) (by omega) hR
      exact ⟨c - 1, (ls4_iff_rs4_refl F hf (b := c - 1) (b' := c - 3) (by ring) (by omega)
        (by omega)).2 h1, rs4_of_add_two_mul F T 1 (by omega) h1⟩

end Sec3Seven

end CFSG.Quasithin.Fan86
