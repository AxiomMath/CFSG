module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC15TCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c15t_irr_inf_or_le {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)}
    {I X : Subgroup W} (hI : IsIrrOn A I ⊥) (hX : StableUnder A X) :
    I ⊓ X = ⊥ ∨ I ≤ X := by
  have hstable : StableUnder A (I ⊓ X) := fun a ha u hu =>
    ⟨hI.2.1 a ha u hu.1, hX a ha u hu.2⟩
  rcases hI.2.2.2 (I ⊓ X) hstable bot_le inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (le_of_inf_eq h)

theorem s16c15t_frame (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (hS : Case168_2Small D ⊥ V hV L)
    {J₀ J₁ : Subgroup (Vtil ⊥ V hV)}
    (hJ₀ : J₀ ∈ irrSet (lBar ⊥ V hV L)) (hJ₁ : J₁ ∈ irrSet (lBar ⊥ V hV L))
    (hinf : J₀ ⊓ J₁ = ⊥) (hsup : J₀ ⊔ J₁ = ⊤) (h4 : 4 ≤ rk ↥J₀)
    {E : Subgroup (MulAut (Vtil ⊥ V hV))} (hE : E ≤ Mbar D.M ⊥ V hV)
    (hE2 : ∀ e ∈ E, e * e = 1) (hfix : rkIdx (fixV E) ≤ 3) :
    (∀ e ∈ E, ∀ y ∈ oddBar D.M ⊥ V hV, e * y = y * e) ∧
    (∀ e ∈ E, (∀ x ∈ J₀, e x = x) → e = 1) ∧
    (∀ e ∈ E, rk ↥(commSub J₀ (Subgroup.zpowers e)) ≤ 1) ∧
    rk ↥E ≤ rk ↥J₀ - 1 := by
  classical
  obtain ⟨F, π, hFinj, hrange, hact, hπ2, htrans⟩ := s16c167_irr_three D hC hS
  have hfixL : fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix D hS.case168_2
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hirr : ∀ i : Fin 3, IsIrrOn (lBar ⊥ V hV L) (F i) ⊥ := by
    intro i
    have hi : F i ∈ irrSet (lBar ⊥ V hV L) := by
      have h : F i ∈ irrBar L ⊥ V hV := by
        rw [hrange]
        exact Set.mem_range_self i
      exact h
    have h2 := hi.2
    rwa [hfixL, inf_bot_eq] at h2
  have hmeet : ∀ i j, i ≠ j → F i ⊓ F j = ⊥ := by
    intro i j hij
    rcases s16c15t_irr_inf_or_le (hirr i) (hirr j).2.1 with h | h
    · exact h
    · exfalso
      rcases (hirr j).2.2.2 (F i) (hirr i).2.1 bot_le h with hbot | htop
      · exact absurd hbot.symm (ne_of_lt (hirr i).1)
      · exact hij (hFinj htop)
  have hcard : ∀ i j : Fin 3, Nat.card ↥(F i) = Nat.card ↥(F j) := by
    intro i j
    obtain ⟨y, -, hy⟩ := htrans i j
    have hmap : (F i).map (y : MulAut (Vtil ⊥ V hV)).toMonoidHom = F j := by
      have h := hact y i
      rwa [hy] at h
    have h1 : Nat.card ↥((F i).map (y : MulAut (Vtil ⊥ V hV)).toMonoidHom) =
        Nat.card ↥(F i) :=
      Subgroup.card_map_of_injective (f := (y : MulAut (Vtil ⊥ V hV)).toMonoidHom)
        (y : MulAut (Vtil ⊥ V hV)).injective
    rw [hmap] at h1
    exact h1.symm
  have hrank : ∀ i j : Fin 3, rk ↥(F i) = rk ↥(F j) := by
    intro i j
    have h := hcard i j
    unfold rk
    rw [h]
  have hJ₀range : J₀ ∈ Set.range F := by
    have h : J₀ ∈ irrBar L ⊥ V hV := hJ₀
    rwa [hrange] at h
  obtain ⟨a, ha⟩ := hJ₀range
  have hJ₁range : J₁ ∈ Set.range F := by
    have h : J₁ ∈ irrBar L ⊥ V hV := hJ₁
    rwa [hrange] at h
  obtain ⟨b, hb⟩ := hJ₁range
  have hab : a ≠ b := by
    intro hab
    have hJ : J₀ = J₁ := by rw [← ha, ← hb, hab]
    have hbot : J₀ = ⊥ := by
      rw [← hJ] at hinf
      simpa using hinf
    have hrk : rk ↥J₀ = 0 := by rw [hbot, rk_bot]
    omega
  have hcomplJ : rk ↥J₀ + rk ↥J₁ = rk (Vtil ⊥ V hV) :=
    s16c15t_rk_add_of_compl hinf hsup
  have hrkWi : ∀ i : Fin 3, 2 * rk ↥(F i) = rk (Vtil ⊥ V hV) := by
    intro i
    have h1 : rk ↥J₀ = rk ↥(F i) := by rw [← ha]; exact hrank a i
    have h2 : rk ↥J₁ = rk ↥(F i) := by rw [← hb]; exact hrank b i
    omega
  have hjoin : ∀ i j, i ≠ j → F i ⊔ F j = ⊤ := by
    intro i j hij
    have h := rk_sup_add_rk_inf (F i) (F j)
    rw [hmeet i j hij, rk_bot, add_zero] at h
    have hWrk : rk ↥(F i ⊔ F j) = rk (Vtil ⊥ V hV) := by
      rw [h]
      have h1 := hrkWi i
      have h2 := hrank i j
      omega
    refine eq_of_le_of_rk_le hW le_top ?_
    rw [rk_top, hWrk]
  let F' : Fin 3 → Subgroup (Vtil ⊥ V hV) := fun i => F (Equiv.swap 0 a i)
  have hF'0 : F' 0 = J₀ := by
    show F (Equiv.swap 0 a 0) = J₀
    rw [Equiv.swap_apply_left]
    exact ha
  have hmeet' : ∀ i j, i ≠ j → F' i ⊓ F' j = ⊥ := by
    intro i j hij
    exact hmeet (Equiv.swap 0 a i) (Equiv.swap 0 a j)
      (fun h => hij ((Equiv.swap 0 a).injective h))
  have hjoin' : ∀ i j, i ≠ j → F' i ⊔ F' j = ⊤ := by
    intro i j hij
    exact hjoin (Equiv.swap 0 a i) (Equiv.swap 0 a j)
      (fun h => hij ((Equiv.swap 0 a).injective h))
  have hperm' : ∀ e ∈ E, ∀ i, ∃ j,
      (F' i).map (e : MulAut (Vtil ⊥ V hV)).toMonoidHom = F' j := by
    intro e he i
    let x : ↥(Mbar D.M ⊥ V hV) := ⟨e, hE he⟩
    refine ⟨Equiv.swap 0 a (π x (Equiv.swap 0 a i)), ?_⟩
    have hx : (x : MulAut (Vtil ⊥ V hV)) = e := rfl
    have h1 : (F (Equiv.swap 0 a i)).map (e : MulAut (Vtil ⊥ V hV)).toMonoidHom =
        F (π x (Equiv.swap 0 a i)) := by
      have h := hact x (Equiv.swap 0 a i)
      rwa [hx] at h
    show (F (Equiv.swap 0 a i)).map (e : MulAut (Vtil ⊥ V hV)).toMonoidHom =
      F (Equiv.swap 0 a (Equiv.swap 0 a (π x (Equiv.swap 0 a i))))
    rw [h1, Equiv.swap_apply_self]
  obtain ⟨hstab, hfaith, hcomm, hrkE⟩ :=
    s16c15t_core hW hmeet' hjoin' hperm' (by rw [hF'0]; exact h4) hfix
  have hconj1 : ∀ e ∈ E, ∀ y ∈ oddBar D.M ⊥ V hV, e * y = y * e := by
    intro e he y hy
    let x : ↥(Mbar D.M ⊥ V hV) := ⟨e, hE he⟩
    have hx : (x : MulAut (Vtil ⊥ V hV)) = e := rfl
    have hπx : π x = 1 := by
      refine Equiv.ext fun k => ?_
      have h1 : (F k).map (x : MulAut (Vtil ⊥ V hV)).toMonoidHom = F k := by
        have h := hstab e he (Equiv.swap 0 a k)
        have h2 : F' (Equiv.swap 0 a k) = F k := by
          show F (Equiv.swap 0 a (Equiv.swap 0 a k)) = F k
          rw [Equiv.swap_apply_self]
        rw [h2] at h
        exact h
      have h3 := hact x k
      rw [h1] at h3
      exact hFinj h3.symm
    have hpow : ∃ n : ℕ, x ^ (2 ^ n) = 1 := by
      refine ⟨1, ?_⟩
      show x ^ 2 = 1
      rw [pow_two]
      exact Subtype.ext (hE2 e he)
    have hcomm' := (hπ2 x hpow).2 hπx
    exact hcomm' y hy
  refine ⟨hconj1, ?_, ?_, ?_⟩
  · intro e he hfixJ
    refine hfaith e he ?_
    rw [hF'0]
    exact hfixJ
  · intro e he
    have h := hcomm e he
    rwa [hF'0] at h
  · have h := hrkE
    rwa [hF'0] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
