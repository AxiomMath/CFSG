module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Refine

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

namespace TB

@[expose] def pairFam (Ω₁ Ω₂ : Set (Subgroup G)) : Set (Subgroup G) :=
  {Z | ∃ X ∈ Ω₁, ∃ Y ∈ Ω₂, Z = X ⊓ Y}

theorem map_conj_map_conj (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [mul_assoc]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [mul_assoc]⟩

theorem map_conj_one (L : Subgroup G) : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
  ext x
  simp

theorem map_conj_map_conj_inv (L : Subgroup G) (a : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = L := by
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one]

theorem map_conj_inv_map_conj (L : Subgroup G) (a : G) :
    (L.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom = L := by
  have := map_conj_map_conj_inv L a⁻¹
  rwa [inv_inv] at this

theorem map_conj_eq_of_mem_stabilizer {A N L : Subgroup G}
    (hN : A ⊓ Subgroup.normalizer (L : Set G) = N) {n : G} (hn : n ∈ N) :
    L.map (MulAut.conj n).toMonoidHom = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN ▸ hn : n ∈ A ⊓ Subgroup.normalizer (L : Set G)).2

end TB

namespace IsRegFam

variable {A W N B : Subgroup G} {Ω : Set (Subgroup G)}

theorem restrict_of_sup_eq (hΩ : IsRegFam A W Ω N) (hA : IsMulCommutative A) (hBA : B ≤ A)
    (hsup : N ⊔ B = A) : IsRegFam B W Ω (B ⊓ N) where
  isDirectProduct := hΩ.isDirectProduct
  nonempty := hΩ.nonempty
  ne_bot := hΩ.ne_bot
  map_conj_mem a ha L hL := hΩ.map_conj_mem a (hBA ha) L hL
  transitive := by
    have := hA
    have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
    intro L hL L' hL'
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive L hL L' hL'
    have ha' : a ∈ N ⊔ B := hsup ▸ ha
    obtain ⟨n, hn, b, hb, rfl⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      (hcomm x (hΩ.le_left hx) y (hBA hy) : x * y = y * x)).mp ha'
    refine ⟨b, hb, ?_⟩
    have hnb : n * b = b * n := hcomm n (hΩ.le_left hn) b (hBA hb)
    rw [hnb, ← TB.map_conj_map_conj,
      TB.map_conj_eq_of_mem_stabilizer (hΩ.stabilizer L hL) hn]
  stabilizer := by
    intro L hL
    rw [← hΩ.stabilizer L hL]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨hxB, hxN⟩ => ⟨hxB, hBA hxB, hxN⟩, fun ⟨hxB, _, hxN⟩ => ⟨hxB, hxN⟩⟩

end IsRegFam

namespace TB

variable {A W N₁ N₂ : Subgroup G} {Ω₁ Ω₂ : Set (Subgroup G)}

theorem isRegFam_pairFam [Finite G] (hA : IsMulCommutative A) (hW : ⁅W, W⁆ = W) (hW1 : W ≠ ⊥)
    (h₁ : IsRegFam A W Ω₁ N₁) (h₂ : IsRegFam A W Ω₂ N₂) (hsup : N₁ ⊔ N₂ = A) :
    IsRegFam A W (pairFam Ω₁ Ω₂) (N₁ ⊓ N₂) := by
  have := hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hdp : IsDirectProduct (pairFam Ω₁ Ω₂) W :=
    IsDirectProduct.refine_of_perfect h₁.isDirectProduct h₂.isDirectProduct hW
  have hconj : ∀ (a : G) (X Y : Subgroup G), (X ⊓ Y).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj a).toMonoidHom ⊓ Y.map (MulAut.conj a).toMonoidHom := fun a X Y =>
    Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective
  have hmem : ∀ a ∈ A, ∀ Z ∈ pairFam Ω₁ Ω₂,
      Z.map (MulAut.conj a).toMonoidHom ∈ pairFam Ω₁ Ω₂ := by
    rintro a ha _ ⟨X, hX, Y, hY, rfl⟩
    exact ⟨_, h₁.map_conj_mem a ha X hX, _, h₂.map_conj_mem a ha Y hY, hconj a X Y⟩
  have htrans : ∀ Z ∈ pairFam Ω₁ Ω₂, ∀ Z' ∈ pairFam Ω₁ Ω₂,
      ∃ a ∈ A, Z' = Z.map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨X, hX, Y, hY, rfl⟩ _ ⟨X', hX', Y', hY', rfl⟩
    obtain ⟨a₁, ha₁, rfl⟩ := h₁.transitive X hX X' hX'
    obtain ⟨a₂, ha₂, rfl⟩ := h₂.transitive Y hY Y' hY'
    have hg : a₂⁻¹ * a₁ ∈ N₁ ⊔ N₂ := by rw [hsup]; exact mul_mem (inv_mem ha₂) ha₁
    obtain ⟨n₁, hn₁, n₂, hn₂, hn⟩ := (mem_sup_iff_of_commute fun x hx y hy =>
      (hcomm x (h₁.le_left hx) y (h₂.le_left hy) : x * y = y * x)).mp hg
    have h12 : n₁ * n₂ = n₂ * n₁ := hcomm n₁ (h₁.le_left hn₁) n₂ (h₂.le_left hn₂)
    have hprod : a₁ * n₁⁻¹ = a₂ * n₂ := by
      have ha : a₁ = a₂ * (n₁ * n₂) := by rw [hn]; group
      rw [ha, h12]
      group
    refine ⟨a₁ * n₁⁻¹, mul_mem ha₁ (inv_mem (h₁.le_left hn₁)), ?_⟩
    rw [hconj]
    congr 1
    · rw [← map_conj_map_conj, map_conj_eq_of_mem_stabilizer (h₁.stabilizer X hX) (inv_mem hn₁)]
    · rw [hprod, ← map_conj_map_conj, map_conj_eq_of_mem_stabilizer (h₂.stabilizer Y hY) hn₂]
  have hne_bot : ∀ Z ∈ pairFam Ω₁ Ω₂, Z ≠ ⊥ := by
    have hex : ∃ Z ∈ pairFam Ω₁ Ω₂, Z ≠ ⊥ := by
      by_contra! hall
      apply hW1
      rw [← hdp.sSup_eq]
      exact le_antisymm (sSup_le fun Z hZ => (hall Z hZ).le) bot_le
    obtain ⟨Z₀, hZ₀, hZ₀1⟩ := hex
    intro Z hZ hbot
    obtain ⟨a, ha, hZa⟩ := htrans Z hZ Z₀ hZ₀
    exact hZ₀1 (by rw [hZa, hbot, Subgroup.map_bot])
  refine ⟨hdp, ?_, hne_bot, hmem, htrans, ?_⟩
  · obtain ⟨X, hX⟩ := h₁.nonempty
    obtain ⟨Y, hY⟩ := h₂.nonempty
    exact ⟨X ⊓ Y, X, hX, Y, hY, rfl⟩
  · rintro _ ⟨X, hX, Y, hY, rfl⟩
    apply le_antisymm
    · intro n hn
      obtain ⟨hnA, hnN⟩ := Subgroup.mem_inf.mp hn
      have hZ : (X ⊓ Y).map (MulAut.conj n).toMonoidHom = X ⊓ Y :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
      rw [hconj] at hZ
      have hne : X ⊓ Y ≠ ⊥ := hne_bot _ ⟨X, hX, Y, hY, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← h₁.stabilizer X hX]
        refine Subgroup.mem_inf.mpr ⟨hnA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
        by_contra hXn
        have hdisj : Disjoint X (X.map (MulAut.conj n).toMonoidHom) :=
          h₁.isDirectProduct.indep.pairwiseDisjoint hX (h₁.map_conj_mem n hnA X hX) (Ne.symm hXn)
        have hle : X ⊓ Y ≤ X.map (MulAut.conj n).toMonoidHom := by
          rw [← hZ]
          exact inf_le_left
        exact hne (disjoint_self.mp (Disjoint.mono inf_le_left hle hdisj))
      · rw [← h₂.stabilizer Y hY]
        refine Subgroup.mem_inf.mpr ⟨hnA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
        by_contra hYn
        have hdisj : Disjoint Y (Y.map (MulAut.conj n).toMonoidHom) :=
          h₂.isDirectProduct.indep.pairwiseDisjoint hY (h₂.map_conj_mem n hnA Y hY) (Ne.symm hYn)
        have hle : X ⊓ Y ≤ Y.map (MulAut.conj n).toMonoidHom := by
          rw [← hZ]
          exact inf_le_right
        exact hne (disjoint_self.mp (Disjoint.mono inf_le_right hle hdisj))
    · intro n hn
      obtain ⟨hn₁, hn₂⟩ := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨h₁.le_left hn₁, ?_⟩
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      show (X ⊓ Y).map (MulAut.conj n).toMonoidHom = X ⊓ Y
      rw [hconj, map_conj_eq_of_mem_stabilizer (h₁.stabilizer X hX) hn₁,
        map_conj_eq_of_mem_stabilizer (h₂.stabilizer Y hY) hn₂]

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
