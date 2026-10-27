module

public import CFSG.Quasithin.Background.Asc81cPfTri2

public section

namespace CFSG.Quasithin

namespace Asc81c

namespace Pf

variable {W : Type*} [CommGroup W] [Finite W] {G : Subgroup (MulAut W)}

section Indep

variable {ι : Type*} {L : ι → Subgroup (MulAut W)}

theorem iSupIndep_of_fixV (hW : ∀ w : W, w ^ 2 = 1) (hodd : ∀ i, Odd (Nat.card (L i)))
    (hfix : ∀ i j, i ≠ j → commSub (⊤ : Subgroup W) (L i) ≤ fixV (L j)) : iSupIndep L := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  let S : Subgroup (MulAut W) :=
    { carrier := {h | ∀ w ∈ commSub (⊤ : Subgroup W) (L i), h w = w}
      one_mem' := fun w _ => rfl
      mul_mem' := fun ha hb w hw => by rw [MulAut.mul_apply, hb w hw, ha w hw]
      inv_mem' := fun {h} ha w hw => by
        calc h⁻¹ w = h⁻¹ (h w) := by rw [ha w hw]
          _ = w := MulAut.inv_apply_self _ _ _ }
  have hle : (⨆ (j : ι) (_ : j ≠ i), L j) ≤ S :=
    iSup₂_le fun j hj z hz w hw => hfix i j (Ne.symm hj) hw z hz
  have hgS := hle hg2
  rw [Subgroup.mem_bot]
  ext v
  have hv : v ∈ fixV (L i) ⊔ commSub ⊤ (L i) := by
    rw [fixV_sup_commSub_eq_top' hW (hodd i)]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
  rw [map_mul, hc g hg1, hgS w hw, MulAut.one_apply]

theorem iSupIndep_commSub_of_fixV (hW : ∀ w : W, w ^ 2 = 1) (hodd : ∀ i, Odd (Nat.card (L i)))
    (hfix : ∀ i j, i ≠ j → commSub (⊤ : Subgroup W) (L i) ≤ fixV (L j)) :
    iSupIndep fun i => commSub (⊤ : Subgroup W) (L i) := by
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.1 hw
  have hle : (⨆ (j : ι) (_ : j ≠ i), commSub (⊤ : Subgroup W) (L j)) ≤ fixV (L i) :=
    iSup₂_le fun j hj => hfix j i hj
  have h1 : w ∈ fixV (L i) ⊓ commSub ⊤ (L i) := ⟨hle hw2, hw1⟩
  rwa [fixV_inf_commSub_eq_bot' hW (hodd i)] at h1

end Indep

section Comp

variable (Ω : Set (Subgroup (MulAut W)))

@[expose] def compL (X : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  X ⊔ ⨆ (Y : Subgroup (MulAut W)) (_ : Y ∈ Ω ∧ ¬ Commutes X Y), Y

variable {Ω}

omit [Finite W] in
theorem le_compL (X : Subgroup (MulAut W)) : X ≤ compL Ω X := le_sup_left

omit [Finite W] in
theorem compL_eq_self {X : Subgroup (MulAut W)} (h : ∀ Y ∈ Ω, Commutes X Y) : compL Ω X = X := by
  refine le_antisymm (sup_le le_rfl (iSup₂_le fun Y hY => absurd (h Y hY.1) hY.2)) le_sup_left

theorem compL_eq_sup
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X Y : Subgroup (MulAut W)}
    (hX : X ∈ Ω) (hY : Y ∈ Ω) (hXY : ¬ Commutes X Y) : compL Ω X = X ⊔ Y := by
  refine le_antisymm (sup_le le_sup_left (iSup₂_le fun Z hZ => ?_))
    (sup_le_sup_left (le_iSup₂ (f := fun Z (_ : Z ∈ Ω ∧ ¬ Commutes X Z) => Z) Y ⟨hY, hXY⟩) X)
  rw [triple_theorem hW (hΩ X hX) (hΩ Y hY) (hΩ Z hZ.1) hXY hZ.2]
  exact le_sup_right

theorem compL_eq_compL
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X Y : Subgroup (MulAut W)}
    (hX : X ∈ Ω) (hY : Y ∈ Ω) (hXY : ¬ Commutes X Y) : compL Ω X = compL Ω Y := by
  rw [compL_eq_sup hW hΩ hX hY hXY, compL_eq_sup hW hΩ hY hX (fun h => hXY h.symm), sup_comm]

theorem compL_cases
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X : Subgroup (MulAut W)} (hX : X ∈ Ω) :
    (compL Ω X = X ∧ ∀ Y ∈ Ω, Commutes X Y) ∨
      ∃ Y ∈ Ω, ¬ Commutes X Y ∧ compL Ω X = X ⊔ Y ∧ compL Ω Y = compL Ω X := by
  by_cases h : ∀ Y ∈ Ω, Commutes X Y
  · exact Or.inl ⟨compL_eq_self h, h⟩
  · push Not at h
    obtain ⟨Y, hY, hXY⟩ := h
    exact Or.inr ⟨Y, hY, hXY, compL_eq_sup hW hΩ hX hY hXY,
      (compL_eq_compL hW hΩ hX hY hXY).symm⟩

theorem commutes_compL
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X Z : Subgroup (MulAut W)}
    (hX : X ∈ Ω) (hZ : Z ∈ Ω) (hne : compL Ω X ≠ compL Ω Z) :
    Commutes (compL Ω X) (compL Ω Z) := by
  have key : ∀ A ∈ Ω, ∀ B ∈ Ω, compL Ω A = compL Ω X → compL Ω B = compL Ω Z →
      Commutes A B := by
    intro A hA B hB hAX hBZ
    by_contra hAB
    exact hne (hAX.symm.trans ((compL_eq_compL hW hΩ hA hB hAB).trans hBZ))
  have hZside : ∀ A ∈ Ω, compL Ω A = compL Ω X → Commutes A (compL Ω Z) := by
    intro A hA hAX
    rcases compL_cases hW hΩ hZ with ⟨h1, -⟩ | ⟨Z', hZ', -, h1, h2⟩
    · rw [h1]
      exact key A hA Z hZ hAX rfl
    · rw [h1]
      exact (key A hA Z hZ hAX rfl).sup (key A hA Z' hZ' hAX h2)
  rcases compL_cases hW hΩ hX with ⟨h1, -⟩ | ⟨X', hX', -, h1, h2⟩
  · rw [h1]
    exact hZside X hX rfl
  · have e1 := hZside X hX rfl
    have e2 := hZside X' hX' h2
    rw [h1]
    exact (e1.symm.sup e2.symm).symm

theorem compL_map_conj
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X)
    (hinv : ∀ g ∈ G, ∀ X ∈ Ω, X.map (MulAut.conj g).toMonoidHom ∈ Ω) {g : MulAut W} (hg : g ∈ G)
    {X : Subgroup (MulAut W)} (hX : X ∈ Ω) :
    (compL Ω X).map (MulAut.conj g).toMonoidHom = compL Ω (X.map (MulAut.conj g).toMonoidHom) := by
  have hXg := hinv g hg X hX
  rcases compL_cases hW hΩ hX with ⟨h1, h2⟩ | ⟨Y, hY, hXY, h1, -⟩
  · rw [h1, compL_eq_self]
    intro Y hY
    have hYg := hinv g⁻¹ (G.inv_mem hg) Y hY
    have h3 := (h2 _ hYg).map_conj g
    rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h3
  · have hYg := hinv g hg Y hY
    have hnc : ¬ Commutes (X.map (MulAut.conj g).toMonoidHom) (Y.map (MulAut.conj g).toMonoidHom) :=
      fun h => hXY (by
        have h3 := h.map_conj g⁻¹
        rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one, map_conj_map_conj, inv_mul_cancel,
          map_conj_one] at h3)
    rw [h1, compL_eq_sup hW hΩ hXg hYg hnc, Subgroup.map_sup]

theorem commSub_compL_le
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X Z : Subgroup (MulAut W)}
    (hX : X ∈ Ω) (hZ : Z ∈ Ω) (hne : compL Ω X ≠ compL Ω Z) :
    commSub (⊤ : Subgroup W) (compL Ω X) ≤ fixV (compL Ω Z) := by
  have key : ∀ A ∈ Ω, ∀ B ∈ Ω, compL Ω A = compL Ω X → compL Ω B = compL Ω Z →
      commSub (⊤ : Subgroup W) A ≤ fixV B := by
    intro A hA B hB hAX hBZ
    have hAB : A ≠ B := fun h => hne (hAX.symm.trans (by rw [h, hBZ]))
    have hc : Commutes A B := by
      by_contra hAB'
      exact hne (hAX.symm.trans ((compL_eq_compL hW hΩ hA hB hAB').trans hBZ))
    exact commSub_le_fixV_of_commute hW (hΩ A hA).1 (hΩ B hB).1 hAB hc
  have hside : ∀ A ∈ Ω, compL Ω A = compL Ω X → commSub (⊤ : Subgroup W) A ≤ fixV (compL Ω Z) := by
    intro A hA hAX
    rcases compL_cases hW hΩ hZ with ⟨h1, -⟩ | ⟨Z', hZ', -, h1, h2⟩
    · rw [h1]
      exact key A hA Z hZ hAX rfl
    · rw [h1, fixV_sup]
      exact le_inf (key A hA Z hZ hAX rfl) (key A hA Z' hZ' hAX h2)
  rcases compL_cases hW hΩ hX with ⟨h1, -⟩ | ⟨X', hX', -, h1, h2⟩
  · rw [h1]
    exact hside X hX rfl
  · rw [h1, commSub_sup]
    exact sup_le (hside X hX rfl) (hside X' hX' h2)

theorem compL_shape
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X : Subgroup (MulAut W)} (hX : X ∈ Ω) :
    compL Ω X = X ∨ (Nat.card ↥(compL Ω X) = 21 ∧
      ∃ a ∈ compL Ω X, ∃ b ∈ compL Ω X, a * b ≠ b * a) := by
  rcases compL_cases hW hΩ hX with ⟨h1, -⟩ | ⟨Y, hY, hXY, h1, -⟩
  · exact Or.inl h1
  · right
    rw [h1]
    refine ⟨(pair_theorem hW (hΩ X hX) (hΩ Y hY)).resolve_left hXY, ?_⟩
    by_contra hall
    push Not at hall
    exact hXY fun a ha b hb => hall a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)

theorem odd_card_compL
    (hW : ∀ w : W, w ^ 2 = 1) (hΩ : ∀ X ∈ Ω, Hyp102 G X) {X : Subgroup (MulAut W)} (hX : X ∈ Ω) :
    Odd (Nat.card ↥(compL Ω X)) := by
  rcases compL_shape hW hΩ hX with h | ⟨h, -⟩
  · rw [h]
    exact (hΩ X hX).1.2.2.2.1
  · rw [h]
    decide

end Comp

theorem thm104 : Thm104 := by
  intro W _ _ hW G Ω hΩ hinv
  classical
  have := finite_mulAut (W := W)
  have hfin : Finite (Subgroup (MulAut W)) := finite_subgroups (W := W)
  set T : Finset (Subgroup (MulAut W)) := (Set.toFinite (compL Ω '' Ω)).toFinset with hT
  have hTmem : ∀ K, K ∈ T ↔ ∃ X ∈ Ω, compL Ω X = K := fun K => by
    rw [hT, Set.Finite.mem_toFinset]
    rfl
  set Lf : Fin T.card → Subgroup (MulAut W) := fun i => (T.equivFin.symm i : Subgroup (MulAut W))
    with hLf
  have hdata : ∀ i, ∃ X ∈ Ω, compL Ω X = Lf i := fun i => (hTmem _).1 (T.equivFin.symm i).2
  have hidx : ∀ {X}, X ∈ Ω → ∃ i, Lf i = compL Ω X := fun {X} hX => by
    have hK : compL Ω X ∈ T := (hTmem _).2 ⟨X, hX, rfl⟩
    exact ⟨T.equivFin ⟨_, hK⟩, by simp [hLf]⟩
  have hne : ∀ i j, i ≠ j → Lf i ≠ Lf j :=
    fun i j hij h => hij (T.equivFin.symm.injective (Subtype.ext h))
  have hodd : ∀ i, Odd (Nat.card ↥(Lf i)) := by
    intro i
    obtain ⟨X, hX, hXK⟩ := hdata i
    rw [← hXK]
    exact odd_card_compL hW hΩ hX
  have hfix : ∀ i j, i ≠ j → commSub (⊤ : Subgroup W) (Lf i) ≤ fixV (Lf j) := by
    intro i j hij
    obtain ⟨X, hX, hXK⟩ := hdata i
    obtain ⟨Z, hZ, hZK⟩ := hdata j
    rw [← hXK, ← hZK]
    exact commSub_compL_le hW hΩ hX hZ (by rw [hXK, hZK]; exact hne i j hij)
  have hsup : (⨆ i, Lf i) = sSup Ω := by
    refine le_antisymm (iSup_le fun i => ?_) (sSup_le fun X hX => ?_)
    · obtain ⟨X, hX, hXK⟩ := hdata i
      rw [← hXK]
      exact sup_le (le_sSup hX) (iSup₂_le fun Y hY => le_sSup hY.1)
    · obtain ⟨i, hi⟩ := hidx hX
      exact (le_compL X).trans (hi ▸ le_iSup Lf i)
  refine ⟨T.card, Lf, hsup, iSupIndep_of_fixV hW hodd hfix, ?_, ?_, ?_,
    iSupIndep_commSub_of_fixV hW hodd hfix, ?_⟩
  ·
    intro i j hij a ha b hb
    obtain ⟨X, hX, hXK⟩ := hdata i
    obtain ⟨Z, hZ, hZK⟩ := hdata j
    rw [← hXK] at ha
    rw [← hZK] at hb
    exact commutes_compL hW hΩ hX hZ (by rw [hXK, hZK]; exact hne i j hij) a ha b hb
  ·
    intro g hg i
    obtain ⟨X, hX, hXK⟩ := hdata i
    obtain ⟨j, hj⟩ := hidx (hinv g hg X hX)
    refine ⟨j, ?_⟩
    rw [← hXK, compL_map_conj hW hΩ hinv hg hX, hj]
  ·
    rw [← commSub_iSup, hsup]
  ·
    intro X hX
    obtain ⟨i, hi⟩ := hidx hX
    rcases compL_shape hW hΩ hX with h | ⟨h21, a, ha, b, hb, hab⟩
    · exact Or.inl ⟨i, by rw [hi, h]⟩
    · exact Or.inr ⟨i, hi ▸ le_compL X, by rw [hi]; exact h21,
        by rw [hi]; exact ⟨a, ha, b, hb, hab⟩⟩

end Pf

end Asc81c

end CFSG.Quasithin
