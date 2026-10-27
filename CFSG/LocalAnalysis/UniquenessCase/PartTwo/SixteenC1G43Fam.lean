module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43D1
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_coset_of_card {H K : Subgroup G} (hH : Nat.card ↥H = 64)
    (hHK : Nat.card ↥(H ⊓ K) = 32) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hxK : x ∉ K)
    (hyK : y ∉ K) : x⁻¹ * y ∈ K := by
  have hcard : Nat.card ↥(K ⊓ H) = 32 := by rw [inf_comm]; exact hHK
  have hmul : K.relIndex H * Nat.card ↥(K ⊓ H) = Nat.card ↥H :=
    Subgroup.relIndex_mul_card (H := K) (K := H)
  rw [hcard, hH] at hmul
  have h2 : K.relIndex H = 2 :=
    Nat.mul_right_cancel (by decide : (0 : ℕ) < 32) (hmul.trans (by decide))
  have h2' : (H ⊓ K).relIndex H = 2 := by
    rw [Subgroup.inf_relIndex_left]; exact h2
  obtain ⟨a, _, _, ha⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and').1 h2'
  have haxK : a * x ∈ K := by
    rcases ha x hx with h | h
    · exact (Subgroup.mem_inf.1 h).2
    · exact absurd (Subgroup.mem_inf.1 h).2 hxK
  have hayK : a * y ∈ K := by
    rcases ha y hy with h | h
    · exact (Subgroup.mem_inf.1 h).2
    · exact absurd (Subgroup.mem_inf.1 h).2 hyK
  have hprod : (a * x)⁻¹ * (a * y) ∈ K := K.mul_mem (K.inv_mem haxK) hayK
  have he : (a * x)⁻¹ * (a * y) = x⁻¹ * y := by group
  rw [he] at hprod
  exact hprod

private lemma s16c1G43_conjSubgroup_eq_of_mem {L K : Subgroup G} {l : G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) (hl : l ∈ L) :
    conjSubgroup K l = K := by
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hx
    have h1 := hKnorm l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    have h2 : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x := by group
    rwa [h2] at h1
  · intro hx; exact hKnorm l hl x hx

private lemma s16c1G43_card_conj_inf {K W : Subgroup G} {l : G}
    (hKl : conjSubgroup K l = K) :
    Nat.card ↥(conjSubgroup W l ⊓ K) = Nat.card ↥(W ⊓ K) := by
  have h : conjSubgroup W l ⊓ K = conjSubgroup (W ⊓ K) l := by
    have h₁ : conjSubgroup W l ⊓ K = conjSubgroup W l ⊓ conjSubgroup K l :=
      congrArg (fun T => conjSubgroup W l ⊓ T) hKl.symm
    rw [h₁, ← conjSubgroup_inf]
  rw [h, card_conjSubgroup]

private lemma s16c1G43_conjSubgroup_le {L W : Subgroup G} {l : G} (hl : l ∈ L)
    (hWL : W ≤ L) : conjSubgroup W l ≤ L := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hxL : l * x * l⁻¹ ∈ L := hWL hx
  have hmem : l⁻¹ * (l * x * l⁻¹) * l ∈ L :=
    L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
  rw [show l⁻¹ * (l * x * l⁻¹) * l = x from by group] at hmem
  exact hmem

private lemma s16c1G43_conjSubgroup_ab {W : Subgroup G} {l : G}
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    ∀ x ∈ conjSubgroup W l, ∀ y ∈ conjSubgroup W l, x * y = y * x := by
  intro x hx y hy
  rw [mem_conjSubgroup_iff] at hx hy
  have h := hW (l * x * l⁻¹) hx (l * y * l⁻¹) hy
  calc x * y = (l⁻¹ * (l * x * l⁻¹) * l) * (l⁻¹ * (l * y * l⁻¹) * l) := by group
    _ = l⁻¹ * ((l * x * l⁻¹) * (l * y * l⁻¹)) * l := by group
    _ = l⁻¹ * ((l * y * l⁻¹) * (l * x * l⁻¹)) * l := by rw [h]
    _ = (l⁻¹ * (l * y * l⁻¹) * l) * (l⁻¹ * (l * x * l⁻¹) * l) := by group
    _ = y * x := by group

private lemma s16c1G43_conjSubgroup_sq {W : Subgroup G} {l : G}
    (hW : ∀ x ∈ W, x * x = 1) :
    ∀ x ∈ conjSubgroup W l, x * x = 1 := by
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have h := hW (l * x * l⁻¹) hx
  calc x * x = (l⁻¹ * (l * x * l⁻¹) * l) * (l⁻¹ * (l * x * l⁻¹) * l) := by group
    _ = l⁻¹ * ((l * x * l⁻¹) * (l * x * l⁻¹)) * l := by group
    _ = l⁻¹ * 1 * l := by rw [h]
    _ = 1 := by group

private lemma s16c1G43_conjSubgroup_cent {L K N W : Subgroup G} {l : G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l) (hl : l ∈ L)
    (hW : ∀ x ∈ W, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ W) :
    ∀ x ∈ conjSubgroup W l, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ conjSubgroup W l := by
  intro x hx hxK k hkK hN
  have hyW : l * x * l⁻¹ ∈ W := (mem_conjSubgroup_iff).1 hx
  have hyK : l * x * l⁻¹ ∉ K := by
    intro hy
    apply hxK
    have h1 := hKnorm l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hy
    have h2 : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ = x := by group
    rw [h2] at h1
    exact h1
  have hk' : l * k * l⁻¹ ∈ K := hKnorm l hl k hkK
  have hN' : ⁅l * k * l⁻¹, l * x * l⁻¹⁆ ∈ N := by
    have he : ⁅l * k * l⁻¹, l * x * l⁻¹⁆ = l * ⁅k, x⁆ * l⁻¹ := by
      simp only [commutatorElement_def]; group
    have hle : l * ⁅k, x⁆ * l⁻¹ = ⁅k, x⁆ := by
      rw [hNcent ⁅k, x⁆ hN l hl]; group
    rw [he, hle]
    exact hN
  have hk'W : l * k * l⁻¹ ∈ W := hW (l * x * l⁻¹) hyW hyK (l * k * l⁻¹) hk' hN'
  rw [mem_conjSubgroup_iff]
  exact hk'W

private structure S16C1G43FamData (L K N W : Subgroup G) : Prop where
  le_L : W ≤ L
  ab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x
  sq : ∀ x ∈ W, x * x = 1
  card : Nat.card ↥W = 64
  cardK : Nat.card ↥(W ⊓ K) = 32
  cent : ∀ x ∈ W, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ W

private lemma s16c1G43FamData_conj {L K N W : Subgroup G} {l : G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l) (hl : l ∈ L)
    (h : S16C1G43FamData L K N W) :
    S16C1G43FamData L K N (conjSubgroup W l) where
  le_L := s16c1G43_conjSubgroup_le hl h.le_L
  ab := s16c1G43_conjSubgroup_ab h.ab
  sq := s16c1G43_conjSubgroup_sq h.sq
  card := (card_conjSubgroup W l).trans h.card
  cardK := by
    rw [s16c1G43_card_conj_inf (s16c1G43_conjSubgroup_eq_of_mem hKnorm hl)]
    exact h.cardK
  cent := s16c1G43_conjSubgroup_cent hKnorm hNcent hl h.cent

private lemma s16c1G43FamData_eps {V : Subgroup G} {g : G} {L K N : Subgroup G} {ε l : G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l)
    (hε : ε = 1 ∨ ε = g) (hl : l ∈ L)
    (hV : S16C1G43FamData L K N V)
    (hW : S16C1G43FamData L K N (conjSubgroup V g)) :
    S16C1G43FamData L K N (conjSubgroup V (ε * l)) := by
  rcases hε with rfl | rfl
  · rw [one_mul]
    exact s16c1G43FamData_conj hKnorm hNcent hl hV
  · rw [← conjSubgroup_conjSubgroup]
    exact s16c1G43FamData_conj hKnorm hNcent hl hW

private lemma s16c1G43_commutator_mul_mem {L K : Subgroup G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    {a b k₁ k₂ : G} (haL : a ∈ L) (hbL : b ∈ L) (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hab : ⁅a, b⁆ ∈ K) : ⁅a * k₁, b * k₂⁆ ∈ K := by
  have hkb : ⁅k₁, b⁆ ∈ K := by
    have hb : b * k₁ * b⁻¹ ∈ K := hKnorm b hbL k₁ hk₁
    have he : ⁅k₁, b⁆ = k₁ * (b * k₁ * b⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [he]
    exact K.mul_mem hk₁ (K.inv_mem hb)
  have hkk : ⁅k₁, k₂⁆ ∈ K := by
    simp only [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
  have h1 : ⁅k₁, b * k₂⁆ ∈ K := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using K.mul_mem hkb (hKnorm b hbL ⁅k₁, k₂⁆ hkk)
  have h2 : ⁅a, b * k₂⁆ ∈ K := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hak : ⁅a, k₂⁆ ∈ K := by
      have ha : a * k₂ * a⁻¹ ∈ K := hKnorm a haL k₂ hk₂
      have he : ⁅a, k₂⁆ = (a * k₂ * a⁻¹) * k₂⁻¹ := by
        simp only [commutatorElement_def]
      rw [he]
      exact K.mul_mem ha (K.inv_mem hk₂)
    simpa only [mul_assoc] using K.mul_mem hab (hKnorm b hbL ⁅a, k₂⁆ hak)
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact K.mul_mem (hKnorm a haL ⁅k₁, b * k₂⁆ h1) h2

private lemma s16c1G43_commutator_mem_of_coset {L K : Subgroup G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    {a x b x' : G} (haL : a ∈ L) (hxL : x ∈ L) (hbL : b ∈ L) (hx'L : x' ∈ L)
    (hab : ⁅a, b⁆ ∈ K)
    (hx : x ∈ K ∨ a⁻¹ * x ∈ K) (hx' : x' ∈ K ∨ b⁻¹ * x' ∈ K) :
    ⁅x, x'⁆ ∈ K := by
  rcases hx with hxK | hxK
  · have hconj : x' * x * x'⁻¹ ∈ K := hKnorm x' hx'L x hxK
    have he : ⁅x, x'⁆ = x * (x' * x * x'⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [he]
    exact K.mul_mem hxK (K.inv_mem hconj)
  · rcases hx' with hx'K | hx'K
    · have hconj : x * x' * x⁻¹ ∈ K := hKnorm x hxL x' hx'K
      have he : ⁅x, x'⁆ = (x * x' * x⁻¹) * x'⁻¹ := by
        simp only [commutatorElement_def]
      rw [he]
      exact K.mul_mem hconj (K.inv_mem hx'K)
    · have hxeq : x = a * (a⁻¹ * x) := by group
      have hx'eq : x' = b * (b⁻¹ * x') := by group
      rw [hxeq, hx'eq]
      exact s16c1G43_commutator_mul_mem (L := L) (K := K) hKnorm haL hbL hxK hx'K hab

private lemma s16c1G43_not_le_K {W K : Subgroup G} (hcard : Nat.card ↥W = 64)
    (hcardK : Nat.card ↥(W ⊓ K) = 32) : ¬ W ≤ K := by
  intro hle
  have h : W ⊓ K = W := le_antisymm inf_le_left (le_inf le_rfl hle)
  rw [h, hcard] at hcardK
  exact absurd hcardK (by decide)

private lemma s16c1G43_fam_hD {V : Subgroup G} {p p' : G}
    (hTI : ∀ h : G, conjSubgroup V h ≠ V → Nat.card ↥(V ⊓ conjSubgroup V h) ≤ 4) :
    conjSubgroup V p ≠ conjSubgroup V p' →
      Nat.card ↥(conjSubgroup V p ⊓ conjSubgroup V p') ≤ 4 := by
  intro hne
  have hne' : conjSubgroup V (p' * p⁻¹) ≠ V := by
    intro heq
    apply hne
    calc conjSubgroup V p = conjSubgroup (conjSubgroup V (p' * p⁻¹)) p := by rw [heq]
      _ = conjSubgroup V p' := by
            rw [conjSubgroup_conjSubgroup]
            rw [show (p' * p⁻¹) * p = p' from by group]
  have h : conjSubgroup (V ⊓ conjSubgroup V (p' * p⁻¹)) p
      = conjSubgroup V p ⊓ conjSubgroup V p' := by
    rw [conjSubgroup_inf, conjSubgroup_conjSubgroup]
    rw [show (p' * p⁻¹) * p = p' from by group]
  rw [← h, card_conjSubgroup]
  exact hTI (p' * p⁻¹) hne'

private lemma s16c1G43_fam_aux {L K N X X' : Subgroup G}
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l)
    (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hXI : S16C1G43FamData L K N X) (hX'I : S16C1G43FamData L K N X')
    (hD : X ≠ X' → Nat.card ↥(X ⊓ X') ≤ 4)
    {a b : G} (haX : a ∈ X) (hbX' : b ∈ X') (haK : a ∉ K) (hbK : b ∉ K)
    (hab : ⁅a, b⁆ ∈ K) : a⁻¹ * b ∈ K ∧ X = X' := by
  have hC : ∀ x ∈ X, ∀ x' ∈ X', ⁅x, x'⁆ ∈ K := by
    intro x hx x' hx'
    refine s16c1G43_commutator_mem_of_coset hKnorm (hXI.le_L haX) (hXI.le_L hx)
      (hX'I.le_L hbX') (hX'I.le_L hx') hab ?_ ?_
    · by_cases hxK : x ∈ K
      · exact Or.inl hxK
      · exact Or.inr (s16c1G43_coset_of_card hXI.card hXI.cardK haX hx haK hxK)
    · by_cases hx'K : x' ∈ K
      · exact Or.inl hx'K
      · exact Or.inr (s16c1G43_coset_of_card hX'I.card hX'I.cardK hbX' hx' hbK hx'K)
  have hEq : X = X' :=
    s16c1G43_d1 hXI.le_L hX'I.le_L hKnorm hNcent hKcomm hXI.ab hXI.sq hX'I.sq
      (s16c1G43_not_le_K hXI.card hXI.cardK) (s16c1G43_not_le_K hX'I.card hX'I.cardK)
      (le_of_eq hXI.cardK.symm) hXI.cent hX'I.cent hC hD
  refine ⟨?_, hEq⟩
  have hbX : b ∈ X := by rw [← hEq] at hbX'; exact hbX'
  exact s16c1G43_coset_of_card hXI.card hXI.cardK haX hbX haK hbK

theorem s16c1G43_fam {V : Subgroup G} {g : G} {L K N : Subgroup G}
    (hVL : V ≤ L) (hWL : conjSubgroup V g ≤ L)
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l)
    (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ x ∈ V, x * x = 1)
    (hV64 : Nat.card ↥V = 64) (hVK : Nat.card ↥(V ⊓ K) = 32)
    (hWK : Nat.card ↥(conjSubgroup V g ⊓ K) = 32)
    (hBV : ∀ x ∈ V, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ V)
    (hBW : ∀ x ∈ conjSubgroup V g, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ conjSubgroup V g)
    (hTI : ∀ h : G, conjSubgroup V h ≠ V → Nat.card ↥(V ⊓ conjSubgroup V h) ≤ 4) :
    ∀ l ∈ L, ∀ l' ∈ L, ∀ ε ε' : G, (ε = 1 ∨ ε = g) → (ε' = 1 ∨ ε' = g) →
      ∀ a b : G, a ∈ conjSubgroup V (ε * l) → b ∈ conjSubgroup V (ε' * l') →
        a ∉ K → b ∉ K → ⁅a, b⁆ ∈ K →
          a⁻¹ * b ∈ K ∧ conjSubgroup V (ε * l) = conjSubgroup V (ε' * l') := by
  intro l hl l' hl' ε ε' hε hε' a b ha hb haK hbK hab
  have hVdata : S16C1G43FamData L K N V :=
    ⟨hVL, hVab, hVsq, hV64, hVK, hBV⟩
  have hVgab : ∀ x ∈ conjSubgroup V g, ∀ y ∈ conjSubgroup V g, x * y = y * x :=
    s16c1G43_conjSubgroup_ab (W := V) (l := g) hVab
  have hVgsq : ∀ x ∈ conjSubgroup V g, x * x = 1 :=
    s16c1G43_conjSubgroup_sq (W := V) (l := g) hVsq
  have hVgdata : S16C1G43FamData L K N (conjSubgroup V g) :=
    ⟨hWL, hVgab, hVgsq, (card_conjSubgroup V g).trans hV64, hWK, hBW⟩
  have hXI : S16C1G43FamData L K N (conjSubgroup V (ε * l)) :=
    s16c1G43FamData_eps hKnorm hNcent hε hl hVdata hVgdata
  have hX'I : S16C1G43FamData L K N (conjSubgroup V (ε' * l')) :=
    s16c1G43FamData_eps hKnorm hNcent hε' hl' hVdata hVgdata
  have hD : conjSubgroup V (ε * l) ≠ conjSubgroup V (ε' * l') →
      Nat.card ↥(conjSubgroup V (ε * l) ⊓ conjSubgroup V (ε' * l')) ≤ 4 :=
    s16c1G43_fam_hD (V := V) hTI
  exact s16c1G43_fam_aux hKnorm hNcent hKcomm hXI hX'I hD ha hb haK hbK hab

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
