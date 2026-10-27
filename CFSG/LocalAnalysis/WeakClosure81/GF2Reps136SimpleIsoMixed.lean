module

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoUnique

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

lemma w1369_ta_mixed_contra {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i)) (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    {a b c : Fin k} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcover : ∀ l : Fin k, l = a ∨ l = b ∨ l = c)
    (hsecab : SecIsoOn Λ (I a) ⊥ (I b) ⊥) (hnac : ¬ SecIsoOn Λ (I a) ⊥ (I c) ⊥)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) : False := by
  have hab_inf : I a ⊓ I b = ⊥ := by
    have hle : I b ≤ ⨆ (j : Fin k) (_ : j ≠ a), I j :=
      le_iSup_of_le b (le_iSup_of_le hab.symm le_rfl)
    exact le_bot_iff.mp ((inf_le_inf_left (I a) hle).trans (le_of_eq (hind a)))
  have hnon : ∀ j, j ≠ c → ¬ SecIsoOn Λ (I j) ⊥ (I c) ⊥ := by
    intro j hjc hisojc
    rcases hcover j with h | h | h
    · subst h
      exact hnac hisojc
    · subst h
      exact hnac (secIsoOn_trans hsecab hisojc)
    · exact absurd h hjc
  have hclaim_a : ∀ n ∈ N, ¬ SecIsoOn Λ (I c) ⊥ ((I a).map n.toMonoidHom) ⊥ := by
    intro n hn hc_na
    have hna_eq : (I a).map n.toMonoidHom = I c :=
      w1369_ta_eq_I_of_SecIsoOn_I P hstab hsimple (w1369_simple_map hnorm (hsimple a) hn)
        hc_na hnon
    have hnab' : SecIsoOn Λ ((I a).map n.toMonoidHom) ⊥ ((I b).map n.toMonoidHom) ⊥ := by
      have h1 := secIsoOn_map (X := Λ) (g := n) (fun l hl => hnorm n hn l hl)
        (fun l hl => hnorm n⁻¹ (N.inv_mem hn) l hl) hsecab
      simpa [Subgroup.map_bot] using h1
    have hnb_eq : (I b).map n.toMonoidHom = I c :=
      w1369_ta_eq_I_of_SecIsoOn_I P hstab hsimple (w1369_simple_map hnorm (hsimple b) hn)
        (secIsoOn_trans hc_na hnab') hnon
    have hbot : I a = ⊥ := by
      have h1 : I a ⊓ I b = I a := inf_eq_left.mpr (le_of_eq (w1369_ta_map_injective n
        (hna_eq.trans hnb_eq.symm)))
      rw [← h1, hab_inf]
    exact (hsimple a).1 hbot
  have hclaim_b : ∀ n ∈ N, ¬ SecIsoOn Λ (I c) ⊥ ((I b).map n.toMonoidHom) ⊥ := by
    intro n hn hc_nb
    have hnb_eq : (I b).map n.toMonoidHom = I c :=
      w1369_ta_eq_I_of_SecIsoOn_I P hstab hsimple (w1369_simple_map hnorm (hsimple b) hn)
        hc_nb hnon
    have hnab' : SecIsoOn Λ ((I b).map n.toMonoidHom) ⊥ ((I a).map n.toMonoidHom) ⊥ := by
      have hs := w1369_ta_SecIsoOn_symm hsecab
      have h1 := secIsoOn_map (X := Λ) (g := n) (fun l hl => hnorm n hn l hl)
        (fun l hl => hnorm n⁻¹ (N.inv_mem hn) l hl) hs
      simpa [Subgroup.map_bot] using h1
    have hna_eq : (I a).map n.toMonoidHom = I c :=
      w1369_ta_eq_I_of_SecIsoOn_I P hstab hsimple (w1369_simple_map hnorm (hsimple a) hn)
        (secIsoOn_trans hc_nb hnab') hnon
    have hbot : I a = ⊥ := by
      have h1 : I a ⊓ I b = I a := inf_eq_left.mpr (le_of_eq (w1369_ta_map_injective n
        (hna_eq.trans hnb_eq.symm)))
      rw [← h1, hab_inf]
    exact (hsimple a).1 hbot
  have hna_le : ∀ n ∈ N, (I a).map n.toMonoidHom ≤ I a ⊔ I b := by
    intro n hn
    refine w1369_ta_le_sup_pair P (w1369_simple_map hnorm (hsimple a) hn) hab ?_
    intro j hj
    rcases hcover j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h
      exact absurd (w1369_ta_SecIsoOn_I_of_mem_supp P hstab hsimple
        (w1369_simple_map hnorm (hsimple a) hn) hj) (hclaim_a n hn)
  have hnb_le : ∀ n ∈ N, (I b).map n.toMonoidHom ≤ I a ⊔ I b := by
    intro n hn
    refine w1369_ta_le_sup_pair P (w1369_simple_map hnorm (hsimple b) hn) hab ?_
    intro j hj
    rcases hcover j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h
      exact absurd (w1369_ta_SecIsoOn_I_of_mem_supp P hstab hsimple
        (w1369_simple_map hnorm (hsimple b) hn) hj) (hclaim_b n hn)
  have hsup_eq : (⨆ (j : Fin k) (_ : j ≠ c), I j) = I a ⊔ I b := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => iSup_le fun hjc => ?_
      rcases hcover j with h | h | h
      · subst h; exact le_sup_left
      · subst h; exact le_sup_right
      · exact absurd h hjc
    · refine sup_le ?_ ?_
      · exact le_iSup_of_le a (le_iSup_of_le hac le_rfl)
      · exact le_iSup_of_le b (le_iSup_of_le hbc le_rfl)
  have hproper : I a ⊔ I b ≠ ⊤ := by
    intro htop
    have hle : I c ≤ I a ⊔ I b := by rw [htop]; exact le_top
    have hbot : I c = ⊥ := by
      have h1 : I c ⊓ (I a ⊔ I b) = I c := inf_eq_left.mpr hle
      rw [← hsup_eq] at h1
      rw [hind c] at h1
      exact h1.symm
    exact (hsimple c).1 hbot
  have hne : I a ⊔ I b ≠ ⊥ := by
    intro hbot
    have hle : I a ≤ ⊥ := le_sup_left.trans (le_of_eq hbot)
    exact (hsimple a).1 (le_bot_iff.mp hle)
  have hstabN : StableUnder N (I a ⊔ I b) := by
    intro n hn x hx
    have hle : (I a ⊔ I b).map n.toMonoidHom ≤ I a ⊔ I b := by
      rw [Subgroup.map_sup]
      exact sup_le (hna_le n hn) (hnb_le n hn)
    exact hle (Subgroup.mem_map_of_mem n.toMonoidHom hx)
  rcases hirr (I a ⊔ I b) hstabN with h | h
  · exact hne h
  · exact hproper h

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
