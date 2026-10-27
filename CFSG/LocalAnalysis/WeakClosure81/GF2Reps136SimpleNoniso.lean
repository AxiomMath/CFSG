module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleSupport

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

lemma w1369_ta_simple_eq_I {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hnoniso : ∀ i j, i ≠ j → ¬ SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) : ∃ i, S = I i := by
  obtain ⟨i, hi⟩ := w1369_ta_supp_nonempty P hS.1
  refine ⟨i, ?_⟩
  have hzero : ∀ j, j ≠ i → w1369_ta_projHom P S j = 1 := by
    intro j hji
    by_contra hjne
    exact hnoniso i j hji.symm (w1369_ta_SecIsoOn_of_proj P hstab hsimple hS hi hjne)
  have hle : S ≤ I i := by
    intro s hs
    have hval : ∀ j, j ≠ i → (P.e j s : Q) = 1 := by
      intro j hji
      have h := congrArg (fun f : S →* I j => f ⟨s, hs⟩) (hzero j hji)
      have hq := congrArg (fun z : I j => (z : Q)) h
      rw [w1369_ta_projHom_apply] at hq
      simpa using hq
    have hs' : s = P.e i s := by
      have hprod : (∏ j : Fin k, (P.e j s : Q)) = (P.e i s : Q) :=
        Finset.prod_eq_single i (fun j _ hji => hval j hji)
          (fun hi => absurd (Finset.mem_univ i) hi)
      exact (P.e_prod s).symm.trans hprod
    rw [hs']
    exact P.e_mem i s
  rcases (hsimple i).2.2 S hS.2.1 hle with h | h
  · exact absurd h hS.1
  · exact h

lemma w1369_ta_noniso {Q : Type} [CommGroup Q] {Λ N : Subgroup (MulAut Q)}
    (hnorm : ∀ n ∈ N, ∀ l ∈ Λ, n * l * n⁻¹ ∈ Λ)
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hnoniso : ∀ i j, i ≠ j → ¬ SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hirr : ∀ M : Subgroup Q, StableUnder N M → M = ⊥ ∨ M = ⊤) :
    ∀ S₁ S₂ : Subgroup Q, w1369_ta_IsSimple Λ S₁ → w1369_ta_IsSimple Λ S₂ →
      ∃ n ∈ N, S₂ = S₁.map n.toMonoidHom := by
  intro S₁ S₂ hS₁ hS₂
  obtain ⟨i, rfl⟩ := w1369_ta_simple_eq_I P hstab hsimple hnoniso hS₁
  obtain ⟨j, rfl⟩ := w1369_ta_simple_eq_I P hstab hsimple hnoniso hS₂
  have hspan_orbit : (⨆ n : N, (I i).map ((n : MulAut Q)).toMonoidHom) = ⊤ :=
    w1369_orbit_span (Λ := Λ) hirr (hsimple i).1
  by_contra hcon
  have hmiss : ∀ n : N, (I i).map ((n : MulAut Q)).toMonoidHom ≠ I j := by
    intro n hn
    exact hcon ⟨n, n.2, hn.symm⟩
  set Mj : Subgroup Q := ⨆ (l : Fin k) (_ : l ≠ j), I l with hMj
  have hle : (⨆ n : N, (I i).map ((n : MulAut Q)).toMonoidHom) ≤ Mj := by
    apply iSup_le
    intro n
    obtain ⟨l, hl⟩ := w1369_ta_simple_eq_I P hstab hsimple hnoniso
      (w1369_simple_map hnorm (hsimple i) n.2)
    have hlne : l ≠ j := by
      intro h; exact hmiss n (by rw [hl, h])
    rw [hl]
    exact (le_iSup (fun _ : l ≠ j => I l) hlne).trans
      (le_iSup (fun l : Fin k => ⨆ (_ : l ≠ j), I l) l)
  have htop : Mj = ⊤ := by
    rw [hspan_orbit] at hle
    exact top_le_iff.mp hle
  have hMjne : Mj ≠ ⊤ := by
    intro htop'
    have hle' : I j ≤ Mj := by rw [htop']; exact le_top
    have hinf : I j ⊓ Mj = I j := inf_eq_left.mpr hle'
    have hbot : I j = ⊥ := by
      have h := hind j
      rw [← hMj] at h
      rw [hinf] at h
      exact h
    exact (hsimple j).1 hbot
  exact hMjne htop

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
