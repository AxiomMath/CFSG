module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bCase3

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2b_case3_pair_step (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (a₀ : Fin n) (η : Fin n → ℤ)
    (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1) (_h0 : levTwoS2b_D c a₀ ≠ 0)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀)
    {S : Set (Fin n → ℤ)} {b d e : Fin n} (hbd : b ≠ d) (heb : e ≠ b) (hed : e ≠ d)
    (hPhi : levTwoS2b_PhiCase3 n p c ⊆ S)
    (hx : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)))) :
    Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single e (η e) + Pi.single d (η d))) := by
  have hcl := Cl.refl
    (Cl.base (hPhi (levTwoS2b_mem_PhiCase3_sub n p c a₀ η hη hD (Ne.symm heb)))) hx
  rwa [levTwoS2b_rRefl_gen_add_gen n (by omega) (Ne.symm heb) (Ne.symm hed) (Ne.symm hbd)
    (hη b) (hη e) (hη d)] at hcl

theorem levTwoS2b_case3_long_out_all (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (a₀ : Fin n) (η : Fin n → ℤ)
    (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1) (h0 : levTwoS2b_D c a₀ ≠ 0)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀)
    {S : Set (Fin n → ℤ)} {b d : Fin n} (hbd : b ≠ d)
    (hPhi : levTwoS2b_PhiCase3 n p c ⊆ S)
    (hx : Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)))) :
    ∀ z : Fin n → ℤ, IsRt (isFiniteType_cartanB n) z → levTwoS2b_isLong n z →
      Cl (isFiniteType_cartanB n) S z := by
  have hpair : ∀ e f : Fin n, e ≠ f → Cl (isFiniteType_cartanB n) S
      (levTwoS2b_ofCoord n (Pi.single e (η e) + Pi.single f (η f))) := by
    intro e f hef
    by_cases hed : e = d
    · by_cases hfb : f = b
      · rw [hed, hfb, add_comm]; exact hx
      · have h1 := levTwoS2b_case3_pair_step n hn p hp hp2 c a₀ η hη h0 hD hbd hfb
            (fun h => hef (hed.trans h.symm)) hPhi hx
        rw [hed]
        rwa [add_comm] at h1
    · by_cases heb : e = b
      · by_cases hfd : f = d
        · rw [heb, hfd]; exact hx
        · have h1 := levTwoS2b_case3_pair_step n hn p hp hp2 c a₀ η hη h0 hD
              (Ne.symm hbd) hfd (fun h => hef (heb.trans h.symm)) hPhi
              (by rw [add_comm]; exact hx)
          rw [heb]
          rwa [add_comm] at h1
      · have h1 := levTwoS2b_case3_pair_step n hn p hp hp2 c a₀ η hη h0 hD hbd heb hed hPhi hx
        by_cases hfd : f = d
        · rw [hfd]; exact h1
        · have h2 := levTwoS2b_case3_pair_step n hn p hp hp2 c a₀ η hη h0 hD (fun h : d = e => hed h.symm) hfd
              (Ne.symm hef) hPhi (by rw [add_comm]; exact h1)
          rwa [add_comm] at h2
  intro z hz hzl
  by_cases hlam : lam c z = 0
  · exact Cl.base (hPhi ⟨hz, hzl, hlam⟩)
  · obtain ⟨b', d', u, v, hb'd', hu, hv, hcz⟩ := hzl
    have hz_eq : z = levTwoS2b_ofCoord n (Pi.single b' u + Pi.single d' v) := by
      apply levTwoS2b_coord_injective n; rw [levTwoS2b_coord_ofCoord, hcz]
    rw [hz_eq]
    have hne : u * η b' + v * η d' ≠ 0 := by
      intro hzero
      apply hlam
      rw [hz_eq, levTwoS2b_lam_add_eta n p c a₀ η hD hb'd' u v, hzero]
      simp
    have hrel : u * η b' = v * η d' :=
      levTwoS2b_pm_eq_of_ne_zero hu hv (hη b') (hη d') hne
    have hpos := hpair b' d' hb'd'
    by_cases hub : u = η b'
    · have hvd : v = η d' := by
        have h1 : u * η b' = 1 := by rw [hub]; rcases hη b' with h | h <;> simp [h]
        rw [h1] at hrel
        rcases hv with rfl | rfl <;> rcases hη d' with h2 | h2 <;> omega
      rw [hub, hvd]; exact hpos
    · have hud : u = -η b' := by
        rcases hu with rfl | rfl <;> rcases hη b' with h | h <;> omega
      have hvd : v = -η d' := by
        have h1 : u * η b' = -1 := by rw [hud]; rcases hη b' with h | h <;> simp [h]
        rw [h1] at hrel
        rcases hv with rfl | rfl <;> rcases hη d' with h2 | h2 <;> omega
      rw [hud, hvd]
      have hself := levTwoS2b_rRefl_self n (by omega)
        (β := levTwoS2b_ofCoord n (Pi.single b' (η b') + Pi.single d' (η d')))
        (levTwoS2b_isRt_ofCoord_long n hb'd' (hη b') (hη d'))
      have hcl := Cl.refl hpos hpos
      rw [hself] at hcl
      rwa [show (-levTwoS2b_ofCoord n (Pi.single b' (η b') + Pi.single d' (η d')) : Fin n → ℤ) =
        levTwoS2b_ofCoord n (Pi.single b' (-η b') + Pi.single d' (-η d')) by
          rw [← levTwoS2b_ofCoord_neg]
          congr 1
          ext k; simp only [Pi.add_apply, Pi.neg_apply, Pi.single_neg]; ring_nf] at hcl

theorem levTwoS2b_tcRoot_case3 (n : ℕ) (hn : 2 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (a₀ : Fin n) (η : Fin n → ℤ)
    (hη : ∀ a : Fin n, η a = 1 ∨ η a = -1) (h0 : levTwoS2b_D c a₀ ≠ 0)
    (hD : ∀ a : Fin n, levTwoS2b_D c a = η a * levTwoS2b_D c a₀) :
    TCRoot (isFiniteType_cartanB n) (levTwoS2b_PhiCase3 n p c) := by
  intro S hS
  classical
  have hn1 : 1 ≤ n := by omega
  by_cases hshort : ∃ x ∈ S, levTwoS2b_isShort n x
  · obtain ⟨xa, hxaS, hxas⟩ := hshort
    obtain ⟨a, u, hu, hcx⟩ := hxas
    have hxa_eq : xa = levTwoS2b_ofCoord n (Pi.single a u) := by
      apply levTwoS2b_coord_injective n; rw [levTwoS2b_coord_ofCoord, hcx]
    have hxan : Cl (isFiniteType_cartanB n) ((levTwoS2b_PhiCase3 n p c) ∪
        ({xa} : Set (Fin n → ℤ))) (levTwoS2b_ofCoord n (Pi.single a (η a))) := by
      rw [hxa_eq]
      rcases hu with rfl | rfl
      · rcases hη a with h1 | h1
        · rw [h1]; exact Cl.base (Or.inr (Set.mem_singleton _))
        · rw [h1]
          have hself := levTwoS2b_rRefl_self n hn1
            (β := levTwoS2b_ofCoord n (Pi.single a 1))
            (levTwoS2b_isRt_ofCoord_short n (Or.inl rfl))
          have hcl : Cl (isFiniteType_cartanB n) ((levTwoS2b_PhiCase3 n p c) ∪
              ({levTwoS2b_ofCoord n (Pi.single a 1)} : Set (Fin n → ℤ)))
              (weylAction (isFiniteType_cartanB n)
                (rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single a 1)))
                (levTwoS2b_ofCoord n (Pi.single a 1))) :=
            Cl.refl (Cl.base (Or.inr (Set.mem_singleton _)))
              (Cl.base (Or.inr (Set.mem_singleton _)))
          rw [hself] at hcl
          rwa [show (-levTwoS2b_ofCoord n (Pi.single a 1) : Fin n → ℤ) =
            levTwoS2b_ofCoord n (Pi.single a (-1)) by
              rw [← levTwoS2b_ofCoord_neg, Pi.single_neg]] at hcl
      · rcases hη a with h1 | h1
        · rw [h1]
          have hself := levTwoS2b_rRefl_self n hn1
            (β := levTwoS2b_ofCoord n (Pi.single a (-1)))
            (levTwoS2b_isRt_ofCoord_short n (Or.inr rfl))
          have hcl : Cl (isFiniteType_cartanB n) ((levTwoS2b_PhiCase3 n p c) ∪
              ({levTwoS2b_ofCoord n (Pi.single a (-1))} : Set (Fin n → ℤ)))
              (weylAction (isFiniteType_cartanB n)
                (rRefl (isFiniteType_cartanB n) (levTwoS2b_ofCoord n (Pi.single a (-1))))
                (levTwoS2b_ofCoord n (Pi.single a (-1)))) :=
            Cl.refl (Cl.base (Or.inr (Set.mem_singleton _)))
              (Cl.base (Or.inr (Set.mem_singleton _)))
          rw [hself] at hcl
          rwa [show (-levTwoS2b_ofCoord n (Pi.single a (-1)) : Fin n → ℤ) =
            levTwoS2b_ofCoord n (Pi.single a 1) by
              rw [← levTwoS2b_ofCoord_neg, Pi.single_neg, neg_neg]] at hcl
        · rw [h1]; exact Cl.base (Or.inr (Set.mem_singleton _))
    refine ⟨{xa}, ?_, by simp, ?_⟩
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_singleton] at hy
      subst hy
      exact hxaS
    · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_singleton] at hy
        subst hy
        exact hxaS
      · intro y hyS
        have hall := levTwoS2b_case3_all_of_xa n hn p hp hp2 c a₀ η hη h0 hD
          (S := (levTwoS2b_PhiCase3 n p c) ∪ ({xa} : Set (Fin n → ℤ))) (a := a)
          (fun z hz => Or.inl hz) hxan
        simpa [Finset.coe_singleton] using hall y (hS y hyS)
  · by_cases hlong : ∃ x ∈ S, levTwoS2b_isLong n x ∧ lam c x ≠ 0
    · obtain ⟨x, hxS, hxl, hxlam⟩ := hlong
      obtain ⟨b, d, u, v, hbd, hu, hv, hcx⟩ := hxl
      have hx_eq : x = levTwoS2b_ofCoord n (Pi.single b u + Pi.single d v) := by
        apply levTwoS2b_coord_injective n; rw [levTwoS2b_coord_ofCoord, hcx]
      have hne : u * η b + v * η d ≠ 0 := by
        intro hzero
        apply hxlam
        rw [hx_eq, levTwoS2b_lam_add_eta n p c a₀ η hD hbd u v, hzero]
        simp
      have hrel : u * η b = v * η d :=
        levTwoS2b_pm_eq_of_ne_zero hu hv (hη b) (hη d) hne
      have hxn : Cl (isFiniteType_cartanB n) ((levTwoS2b_PhiCase3 n p c) ∪
          ({x} : Set (Fin n → ℤ)))
          (levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d))) := by
        rw [hx_eq]
        by_cases hub : u = η b
        · have hvd : v = η d := by
            have h1 : u * η b = 1 := by rw [hub]; rcases hη b with h | h <;> simp [h]
            rw [h1] at hrel
            rcases hv with rfl | rfl <;> rcases hη d with h2 | h2 <;> omega
          rw [hub, hvd]
          exact Cl.base (Or.inr (Set.mem_singleton _))
        · have hud : u = -η b := by
            rcases hu with rfl | rfl <;> rcases hη b with h | h <;> omega
          have hvd : v = -η d := by
            have h1 : u * η b = -1 := by rw [hud]; rcases hη b with h | h <;> simp [h]
            rw [h1] at hrel
            rcases hv with rfl | rfl <;> rcases hη d with h2 | h2 <;> omega
          rw [hud, hvd]
          have hbase : Cl (isFiniteType_cartanB n) ((levTwoS2b_PhiCase3 n p c) ∪
              ({levTwoS2b_ofCoord n (Pi.single b (-η b) + Pi.single d (-η d))} :
                Set (Fin n → ℤ)))
              (levTwoS2b_ofCoord n (Pi.single b (-η b) + Pi.single d (-η d))) :=
            Cl.base (Or.inr (Set.mem_singleton _))
          have hself := levTwoS2b_rRefl_self n hn1
            (β := levTwoS2b_ofCoord n (Pi.single b (-η b) + Pi.single d (-η d)))
            (levTwoS2b_isRt_ofCoord_long n hbd
              (by rcases hη b with h | h <;> simp [h])
              (by rcases hη d with h | h <;> simp [h]))
          have hcl := Cl.refl hbase hbase
          rw [hself] at hcl
          rwa [show (-levTwoS2b_ofCoord n (Pi.single b (-η b) + Pi.single d (-η d)) :
              Fin n → ℤ) = levTwoS2b_ofCoord n (Pi.single b (η b) + Pi.single d (η d)) by
              rw [← levTwoS2b_ofCoord_neg]
              congr 1
              ext k; simp only [Pi.add_apply, Pi.neg_apply, Pi.single_neg]; ring_nf] at hcl
      refine ⟨{x}, ?_, by simp, ?_⟩
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_singleton] at hy
        subst hy
        exact hxS
      · apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_singleton] at hy
          subst hy
          exact hxS
        · intro y hyS
          rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
          · exact absurd ⟨y, hyS, hys⟩ hshort
          · have hset : (levTwoS2b_PhiCase3 n p c ∪
                (↑({x} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) =
                (levTwoS2b_PhiCase3 n p c ∪ ({x} : Set (Fin n → ℤ))) := by
              rw [Finset.coe_singleton]
            rw [hset]
            exact levTwoS2b_case3_long_out_all n hn p hp hp2 c a₀ η hη h0 hD hbd
                (fun z hz => Or.inl hz) hxn y (hS y hyS) hyl
    · refine ⟨∅, by simp, by simp, ?_⟩
      apply levTwoS2b_cl_eq_of_subset (isFiniteType_cartanB n)
      · simp
      · intro y hyS
        rcases levTwoS2b_isShort_or_isLong n (hS y hyS) with hys | hyl
        · exact absurd ⟨y, hyS, hys⟩ hshort
        · exact Cl.base (Or.inl ⟨hS y hyS, hyl, by
            by_contra h
            exact hlong ⟨y, hyS, hyl, h⟩⟩)


end CFSG.StandardType.LevTwo
