module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.NearFixed
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Quotient
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Simple

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

open CFSG.SignalizerFunctorTheorem.Nonsolvable

theorem signalizerFixedSubgroup_ne_bot
    {p : ℕ} {T : Type*} [Group T] [Finite T]
    (h : signalizerMcBrideHypothesisA p T) {f : MulAut T} (hf : orderOf f = p) :
    signalizerFixedSubgroup f ≠ ⊥ := by
  obtain ⟨hp, hsimple, hnc, hcop, -, hnear | hdich⟩ := h
  · exact AChief.signalizerFixedSubgroup_ne_bot_of_model hp
      (AChief.signalizerNearSimpleModel_of_nearPSolvable hsimple hnc hnear) hcop f hf
  · intro hbot
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ≠ 1 := fun h => hab (by rw [h, one_mul, mul_one])
    have hz : Subgroup.zpowers a ≠ ⊥ := fun h => ha (Subgroup.zpowers_eq_bot.mp h)
    have hs : Group.IsSolvable (Subgroup.zpowers a) := inferInstance
    exact (hdich f hf).1 _ hz hs (by rw [hbot]; exact bot_le)

private theorem isSolvable_of_fixed_aux
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] (E Y : Subgroup Γ), Nat.card Y = n →
      IsElemAbelian p E → E ≤ Subgroup.normalizer (Y : Set Γ) →
      signalizerMcBrideHypothesisB p Y → Y ⊓ Subgroup.centralizer (E : Set Γ) = ⊥ →
      Group.IsSolvable Y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ E Y hn hE hEY hY hfix
  by_contra hns
  classical
  let P : Subgroup Γ → Prop := fun N => N ≠ ⊥ ∧ N ≤ Y ∧ (N.subgroupOf Y).Normal ∧
    E ≤ Subgroup.normalizer (N : Set Γ)
  have hY1 : Y ≠ ⊥ := fun h => hns (by rw [h]; infer_instance)
  have hPY : P Y := ⟨hY1, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance, hEY⟩
  have hex : ∃ k, ∃ N, P N ∧ Nat.card N = k := ⟨_, Y, hPY, rfl⟩
  obtain ⟨N, hPN, hNk⟩ := Nat.find_spec hex
  have hmin : ∀ M, P M → Nat.card N ≤ Nat.card M := fun M hM =>
    hNk ▸ Nat.find_min' hex ⟨M, hM, rfl⟩
  obtain ⟨hN1, hNY, hNn, hEN⟩ := hPN
  by_cases hNeq : N = Y
  ·
    subst hNeq
    have hnc : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact hns (Group.isSolvable_of_comm fun a b => Subtype.ext (hcon a a.2 b b.2))
    have hsimple : IsASimple E N := ⟨hEY, hnc, fun M hMY hMn hEM => by
      by_cases hM : M = ⊥
      · exact Or.inl hM
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge hMY (hmin M ⟨hM, hMY, hMn, hEM⟩))⟩
    obtain ⟨T, hT⟩ := hsimple.simpleComponents_nonempty
    obtain ⟨f, hf, φ, hφ⟩ := AChief.exists_fixed_embedding hp hE hsimple hY hT
    have hfix' : ∀ g : Γ, g ∈ N ⊓ Subgroup.centralizer (E : Set Γ) → g = 1 := fun g hg =>
      Subgroup.mem_bot.mp ((SetLike.ext_iff.mp hfix g).mp hg)
    have htriv : signalizerFixedSubgroup f = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h1 := hfix' _ (φ ⟨x, hx⟩).2
      have h2 : φ ⟨x, hx⟩ = φ 1 := by rw [map_one]; exact Subtype.ext h1
      exact congrArg Subtype.val (hφ h2)
    rcases hf with hf | hf
    · obtain ⟨-, -, -, x, hx, y, hy, hxy⟩ := hT
      have hx1 : (⟨x, hx⟩ : ↥T) = 1 := by
        have hmem : (⟨x, hx⟩ : ↥T) ∈ signalizerFixedSubgroup f := by
          rw [hf]; exact rfl
        rw [htriv, Subgroup.mem_bot] at hmem
        exact hmem
      have hy1 : (⟨y, hy⟩ : ↥T) = 1 := by
        have hmem : (⟨y, hy⟩ : ↥T) ∈ signalizerFixedSubgroup f := by
          rw [hf]; exact rfl
        rw [htriv, Subgroup.mem_bot] at hmem
        exact hmem
      have hx1' : x = 1 := congrArg Subtype.val hx1
      have hy1' : y = 1 := congrArg Subtype.val hy1
      exact hxy (by rw [hx1', hy1'])
    · exact signalizerFixedSubgroup_ne_bot (AChief.hypA_of_mem_simpleComponents hY hT) hf htriv
  ·
    have hNlt : Nat.card N < Nat.card Y := by
      by_contra hge
      push Not at hge
      exact hNeq (Subgroup.eq_of_le_of_card_ge hNY hge)
    have hsolN : Group.IsSolvable N := by
      refine ih (Nat.card N) (hn ▸ hNlt) E N rfl hE hEN ?_ ?_
      · exact (isSigClass_hypBClass.{u} p).mono Γ hNY hEN hY
      · rw [eq_bot_iff]
        exact (inf_le_inf_right _ hNY).trans hfix.le
    have hYN : Y ≤ AChief.nrm N := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mp hNn
    obtain ⟨π, hπ⟩ := AChief.exists_surjective_fixed hp hE hEY hEN hYN hY.2.1
    have hq : Group.IsSolvable (AChief.qimg N Y) := by
      refine ih (Nat.card (AChief.qimg N Y)) ?_ (AChief.qimg N E) (AChief.qimg N Y) rfl
        (AChief.isElemAbelian_qimg hE) (AChief.qimg_le_normalizer hEY)
        (AChief.hypB_qimg hYN hY) ?_
      · have h1 := AChief.card_qimg_mul_card hNY hYN
        have h2 : 2 ≤ Nat.card N := by
          have h3 : Nat.card N ≠ 1 := fun h => hN1 (Subgroup.eq_bot_of_card_eq N h)
          have h4 : 0 < Nat.card N := Nat.card_pos
          omega
        have h5 : 0 < Nat.card (AChief.qimg N Y) := Nat.card_pos
        rw [← hn, ← h1]
        nlinarith
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨y, hy⟩ := hπ ⟨x, hx⟩
        have h1 : (y : Γ) = 1 := Subgroup.mem_bot.mp ((SetLike.ext_iff.mp hfix _).mp y.2)
        have h2 : y = 1 := Subtype.ext h1
        have h3 : (⟨x, hx⟩ : ↥(AChief.qimg N Y ⊓ Subgroup.centralizer
            ((AChief.qimg N E : Subgroup (AChief.QG N)) : Set (AChief.QG N)))) = 1 := by
          rw [← hy, h2, map_one]
        exact Subgroup.mem_bot.mpr (congrArg Subtype.val h3)
    exact hns (AChief.isSolvable_of_qimg hNY hYN hsolN hq)

theorem isSolvable_of_inf_centralizer_eq_bot
    {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) {E Y : Subgroup Γ} (hE : IsElemAbelian p E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set Γ)) (hY : signalizerMcBrideHypothesisB p Y)
    (hfix : Y ⊓ Subgroup.centralizer (E : Set Γ) = ⊥) : Group.IsSolvable Y :=
  isSolvable_of_fixed_aux hp _ E Y rfl hE hEY hY hfix

theorem inf_centralizer_ne_bot_of_not_isSolvable
    {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) {E Y : Subgroup Γ} (hE : IsElemAbelian p E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set Γ)) (hY : signalizerMcBrideHypothesisB p Y)
    (hns : ¬ Group.IsSolvable Y) : Y ⊓ Subgroup.centralizer (E : Set Γ) ≠ ⊥ :=
  fun h => hns (isSolvable_of_inf_centralizer_eq_bot hp hE hEY hY h)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
