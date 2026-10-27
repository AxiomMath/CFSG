module

public import CFSG.Quasithin.Background.HZCode22B

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def fixData : List (ℕ × List (List ℕ)) := [
    (2, [[0, 0], [1, 0]]), (3, [[1, 0, 0], [1, 1, 0]]), (4, [[0, 0, 1], [1, 0, 1]]),
    (5, [[0, 0], [0, 1]]), (6, [[1, 0, 1], [0, 1, 1, 0]]), (7, [[0, 1, 0], [1, 1, 0]]),
    (8, [[1], [0, 0, 0, 0, 1, 0]]), (9, [[1], [0, 1, 1, 0, 0]]),
    (10, [[1, 1, 0, 0, 0], [1, 1, 0, 1, 0, 0]]), (11, [[0, 1, 1, 0], [0, 0, 0, 1, 0, 1]]),
    (12, [[1, 0], [0, 1, 0, 0, 0, 0]]), (13, [[0, 1, 0], [1, 0, 0, 0, 1]]),
    (14, [[0, 0, 0, 1, 1], [1, 1, 0, 1, 0, 1]]), (15, [[0, 1], [0, 0, 1, 0, 0, 0]]),
    (16, [[1, 1, 0], [1, 0, 0, 1, 1, 0, 0]]), (17, [[1, 0, 0], [0, 0, 1, 0, 0, 0, 0]]),
    (18, [[1], [0, 1, 0, 1, 0, 0]]), (19, [[1], [0, 0, 1, 1, 0]]),
    (20, [[0, 1, 1], [0, 1, 0, 0, 1, 1, 0]]), (21, [[0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 1, 1]]),
    (22, [[0, 0, 1], [1, 0, 1, 0, 0, 0]]), (23, [[1, 0, 1], [0, 0, 1, 0, 1, 0]])]

theorem fixData_fix : ∀ e ∈ fixData, ∀ w ∈ e.2, (wArr [lxArr, lyArr] w)[e.1]! = e.1 := by
  decide +kernel

theorem fixData_ok : ∀ e ∈ fixData, ∀ j < 24, (∀ w ∈ e.2, (wArr [lxArr, lyArr] w)[j]! = j) →
    j = 0 ∨ j = 1 ∨ j = e.1 := by
  decide +kernel

theorem fixData_cover : ∀ i < 24, 2 ≤ i → i ∈ fixData.map Prod.fst := by
  decide +kernel

theorem hasArr_L22_word (w : List ℕ) : HasArr (wPerm [lX, lY] w) (wArr [lxArr, lyArr] w) := by
  refine hasArr_wPerm (fun i => ?_) w
  rcases i with _ | _ | i
  · exact hasArr_lX
  · exact hasArr_lY
  · simpa using hasArr_one

theorem wPerm_mem_L22 (w : List ℕ) : wPerm [lX, lY] w ∈ L22 := by
  refine wPerm_mem (fun p hp => ?_) w
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lX_mem_L22
  · exact lY_mem_L22

theorem swap01_not_mem_AutPerm : Equiv.swap (0 : Fin 24) 1 ∉ AutPerm := by
  intro h
  have hc : bvec 24 4727069 ∈ C := (bvec_mem_C_iff 4727069).2 (by decide)
  have h1 : bvec 24 4727069 ∘ ⇑(Equiv.swap (0 : Fin 24) 1) ∈ C := comp_mem_of_mem_AutPerm h hc
  have h2 := C.add_mem h1 hc
  have h3 : bvec 24 4727069 ∘ ⇑(Equiv.swap (0 : Fin 24) 1) + bvec 24 4727069 = bvec 24 3 := by
    funext i
    fin_cases i <;> decide
  rw [h3, bvec_mem_C_iff] at h2
  exact absurd h2 (by decide)

theorem eq_one_of_commute_L22 {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ mog22plus)
    (hc : ∀ g ∈ L22, σ * g = g * σ) : σ = 1 := by
  have hw : ∀ w : List ℕ, ∀ j : Fin 24, wPerm [lX, lY] w (σ j) = σ (wPerm [lX, lY] w j) := by
    intro w j
    have := congrArg (fun τ : Equiv.Perm (Fin 24) => τ j) (hc _ (wPerm_mem_L22 w))
    simpa [Equiv.Perm.mul_apply] using this.symm
  have hfix : ∀ i : Fin 24, 2 ≤ (i : ℕ) → σ i = i := by
    intro i hi
    obtain ⟨e, he, he1⟩ := List.mem_map.1 (fixData_cover i i.2 hi)
    have hσi : ∀ w ∈ e.2, (wArr [lxArr, lyArr] w)[(σ i : ℕ)]! = (σ i : ℕ) := by
      intro w hwe
      rw [← hasArr_L22_word w (σ i), hw w i]
      have h1 : wPerm [lX, lY] w i = i := by
        apply Fin.ext
        rw [hasArr_L22_word w i, ← he1]
        exact fixData_fix e he w hwe
      rw [h1]
    rcases fixData_ok e he (σ i) (σ i).2 hσi with h0 | h0 | h0
    · exfalso
      have h0' : σ i = 0 := Fin.ext h0
      rcases hσ.2 with ⟨ha, -⟩ | ⟨-, hb⟩
      · have : i = 0 := σ.injective (h0'.trans ha.symm)
        rw [this] at hi
        simp at hi
      · have : i = 1 := σ.injective (h0'.trans hb.symm)
        rw [this] at hi
        simp at hi
    · exfalso
      have h0' : σ i = 1 := Fin.ext h0
      rcases hσ.2 with ⟨-, hb⟩ | ⟨ha, -⟩
      · have : i = 1 := σ.injective (h0'.trans hb.symm)
        rw [this] at hi
        simp at hi
      · have : i = 0 := σ.injective (h0'.trans ha.symm)
        rw [this] at hi
        simp at hi
    · exact Fin.ext (h0.trans he1)
  rcases hσ.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · ext j
    by_cases hj : 2 ≤ (j : ℕ)
    · rw [hfix j hj]
      rfl
    · interval_cases hjv : (j : ℕ)
      · have : j = 0 := Fin.ext hjv
        rw [this, h0]
        rfl
      · have : j = 1 := Fin.ext hjv
        rw [this, h1]
        rfl
  · exfalso
    apply swap01_not_mem_AutPerm
    have hs : σ = Equiv.swap (0 : Fin 24) 1 := by
      ext j
      by_cases hj : 2 ≤ (j : ℕ)
      · rw [hfix j hj, Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => by rw [h] at hj; simp at hj
        · exact fun h => by rw [h] at hj; simp at hj
      · interval_cases hjv : (j : ℕ)
        · have : j = 0 := Fin.ext hjv
          rw [this, h0, Equiv.swap_apply_left]
        · have : j = 1 := Fin.ext hjv
          rw [this, h1, Equiv.swap_apply_right]
    rw [← hs]
    exact hσ.1

theorem L22_le_mog22 : L22 ≤ mog22 := by
  rw [L22, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact lX_mem
  · exact lY_mem

theorem eq_one_of_commute_imgC_L22
    {q : MulAut W10} (hq : q ∈ (rhoC10 mog22plus le_rfl).range)
    (hc : ∀ p ∈ imgC L22, p * q = q * p) : q = 1 := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := hq
  have hσ1 : σ = 1 := by
    refine eq_one_of_commute_L22 hσ fun g hg => ?_
    have hg22 : g ∈ mog22 := L22_le_mog22 hg
    have hp : rhoC10 mog22plus le_rfl ⟨g, mog22_le_mog22plus hg22⟩ ∈ imgC L22 :=
      ⟨⟨g, hg22⟩, Subgroup.mem_subgroupOf.2 hg, MulEquiv.ext fun _ => rfl⟩
    have h1 := hc _ hp
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (rhoC10_mog22plus_injective h1)
    exact h2.symm
  have : (⟨σ, hσ⟩ : ↥mog22plus) = 1 := Subtype.ext hσ1
  rw [this, map_one]

theorem faith_of_code22
    {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) {z : V} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut V)} (hSH : S ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2)
    (hzS : z ∈ fixV S) :
    ∀ q ∈ Subgroup.normalizer (H : Set (MulAut V)), (∀ p ∈ parZ H z, p * q = q * p) → q = 1 := by
  obtain ⟨e, he, hez⟩ := exists_equiv_z0 h hz1 hSH hS hzS
  intro q hqN hqP
  have keyP : ∀ (A : Subgroup (MulAut W10)) (w : W10),
      A = imgC mog22 → w = z0 → parZ A w = imgC L22 := by
    rintro A w rfl rfl
    exact parZ_std
  have hP : (parZ H z).map (congrHom e) = imgC L22 := (parZ_map e H z).trans (keyP _ _ he hez)
  have hqN' : congrHom e q ∈ (rhoC10 mog22plus le_rfl).range := by
    rw [← normalizer_rhoC10_mog22, range_rhoC10_eq_imgC, ← he]
    exact Subgroup.le_normalizer_map (congrHom e) ⟨q, hqN, rfl⟩
  have h1 : congrHom e q = 1 := by
    refine eq_one_of_commute_imgC_L22 hqN' fun p hp => ?_
    rw [← hP] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    calc congrHom e p₀ * congrHom e q = congrHom e (p₀ * q) := (map_mul _ _ _).symm
      _ = congrHom e (q * p₀) := by rw [hqP p₀ hp₀]
      _ = congrHom e q * congrHom e p₀ := map_mul _ _ _
  have hinj := congrHom_injective e
  rw [← map_one (congrHom e)] at h1
  exact hinj h1

end CFSG.Quasithin.H.Code22
