module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortSUSymTorus

public section

namespace CFSG.StandardType.FrameRoute.SUSix

open CFSG.Assembly

variable {K : Type} [Field K]

private lemma inv_eq_sq {ω : Kˣ} (hω : ω ^ 3 = 1) : ω⁻¹ = ω ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hω])

private lemma inv_sq_eq {ω : Kˣ} (hω : ω ^ 3 = 1) : (ω ^ 2)⁻¹ = ω :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hω])

@[expose] def d0 (ω : Kˣ) : Fin 6 → Kˣ := ![1, 1, ω, ω ^ 2, 1, 1]

@[expose] def d1 (ω : Kˣ) : Fin 6 → Kˣ := ![1, 1, 1, 1, ω, ω ^ 2]

@[expose] def d2 (ω : Kˣ) : Fin 6 → Kˣ := ![ω, ω, ω ^ 2, ω ^ 2, 1, 1]

private def sigma2 : Equiv.Perm (Fin 6) :=
  Equiv.swap (0 : Fin 6) 2 * Equiv.swap (1 : Fin 6) 3

private lemma sigma2_sq : sigma2 ^ 2 = 1 := by
  decide

private lemma monomial_single (i : Fin 3) (ω : Kˣ) :
    monomial (Pi.mulSingle i ω) = ![d0 ω, d1 ω, d2 ω] i := by
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [monomial, d0, d1, d2, Pi.mulSingle]

lemma d0_prod (hK : Nat.card K = 4) (ω : Kˣ) :
    ∏ j, d0 ω j = 1 := by
  have h := monomial_prod hK (Pi.mulSingle 0 ω)
  rw [monomial_single 0 ω] at h
  simpa using h

lemma d1_prod (hK : Nat.card K = 4) (ω : Kˣ) :
    ∏ j, d1 ω j = 1 := by
  have h := monomial_prod hK (Pi.mulSingle 1 ω)
  rw [monomial_single 1 ω] at h
  simpa using h

lemma d2_prod (hK : Nat.card K = 4) (ω : Kˣ) :
    ∏ j, d2 ω j = 1 := by
  have h := monomial_prod hK (Pi.mulSingle 2 ω)
  rw [monomial_single 2 ω] at h
  simpa using h

lemma E_single_zero (hK : Nat.card K = 4) (ω : Kˣ) :
    E hK (Pi.mulSingle 0 ω) =
      diagSU hK (d0 ω)
        (d0_prod hK ω) := by
  apply Subtype.ext
  rw [E_apply, diagSU_coe]
  rw [monomial_single 0 ω]
  simp

lemma E_single_one (hK : Nat.card K = 4) (ω : Kˣ) :
    E hK (Pi.mulSingle 1 ω) =
      diagSU hK (d1 ω)
        (d1_prod hK ω) := by
  apply Subtype.ext
  rw [E_apply, diagSU_coe]
  rw [monomial_single 1 ω]
  simp

lemma E_single_two (hK : Nat.card K = 4) (ω : Kˣ) :
    E hK (Pi.mulSingle 2 ω) =
      diagSU hK (d2 ω)
        (d2_prod hK ω) := by
  apply Subtype.ext
  rw [E_apply, diagSU_coe]
  rw [monomial_single 2 ω]
  simp

lemma swap_fix {d : Fin 6 → Kˣ} {a b : Fin 6} (h : d a = d b) :
    (fun j => d ((Equiv.swap a b)⁻¹ j)) = d := by
  funext j
  by_cases hja : j = a
  · subst hja
    simpa using h.symm
  · by_cases hjb : j = b
    · subst hjb
      simpa using h
    · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]

lemma d0_swap23 {ω : Kˣ} (hω : ω ^ 3 = 1) :
    (fun j => d0 ω ((Equiv.swap 2 3)⁻¹ j)) =
      (d0 ω)⁻¹ := by
  funext j
  fin_cases j <;>
    simp [d0, Equiv.swap_apply_def, inv_eq_sq hω,
      inv_sq_eq hω]

lemma d1_swap45 {ω : Kˣ} (hω : ω ^ 3 = 1) :
    (fun j => d1 ω ((Equiv.swap 4 5)⁻¹ j)) =
      (d1 ω)⁻¹ := by
  funext j
  fin_cases j <;>
    simp [d1, Equiv.swap_apply_def, inv_eq_sq hω,
      inv_sq_eq hω]

private lemma d2_swap0213 {ω : Kˣ} (hω : ω ^ 3 = 1) :
    (fun j => d2 ω (sigma2⁻¹ j)) =
      (d2 ω)⁻¹ := by
  funext j
  fin_cases j <;>
    simp [d2, sigma2,
      Equiv.swap_apply_def, inv_eq_sq hω,
      inv_sq_eq hω]

@[expose] noncomputable def e (hK : Nat.card K = 4) (ω : Kˣ) :
    Fin 3 → LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2) :=
  fun i => LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
    (E hK (Pi.mulSingle i ω))

private lemma single_pow_three {ω : Kˣ} (hω : ω ^ 3 = 1)
    (i j : Fin 3) : ((Pi.mulSingle i ω : Fin 3 → Kˣ) j) ^ 3 = 1 := by
  by_cases h : j = i
  · subst h
    simpa using hω
  · rw [Pi.mulSingle_eq_of_ne h, one_pow]

lemma e_pow (hK : Nat.card K = 4) {ω : Kˣ} (hω : ω ^ 3 = 1)
    (i : Fin 3) : e hK ω i ^ 3 = 1 := by
  change LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
    (E hK (Pi.mulSingle i ω)) ^ 3 = 1
  rw [← map_pow, E_pow_three hK _
    (fun j => single_pow_three hω i j), map_one]

lemma e_commute (hK : Nat.card K = 4) (ω : Kˣ)
    (i j : Fin 3) : Commute (e hK ω i) (e hK ω j) := by
  have hEH : Commute (E hK (Pi.mulSingle i ω))
      (E hK (Pi.mulSingle j ω)) := by
    show E hK (Pi.mulSingle i ω) *
        E hK (Pi.mulSingle j ω) =
      E hK (Pi.mulSingle j ω) *
        E hK (Pi.mulSingle i ω)
    rw [← map_mul (E hK) (Pi.mulSingle i ω) (Pi.mulSingle j ω),
      ← map_mul (E hK) (Pi.mulSingle j ω) (Pi.mulSingle i ω), mul_comm]
  exact hEH.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2))

lemma e_card [Finite K] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) :
    Nat.card (Subgroup.closure (Set.range (e hK ω))) = 3 ^ 3 := by
  change Nat.card (Subgroup.closure (Set.range fun i : Fin 3 =>
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (E hK (Pi.mulSingle i ω)))) = 3 ^ 3
  rw [closure_card hK hω]
  norm_num

lemma e_inter_center (hK : Nat.card K = 4) (ω : Kˣ)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) = ⊥) :
    Subgroup.closure (Set.range (e hK ω)) ⊓
      Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) = ⊥ := by
  rw [hZ, inf_bot_eq]

private lemma comm_of_conj_eq {G : Type*} [Group G] {P D : G}
    (h : P * D * P⁻¹ = D) : Commute P D := by
  show P * D = D * P
  calc P * D = (P * D * P⁻¹) * P := by group
    _ = D * P := by rw [h]

private lemma permH_swap01_ne_one (hK : Nat.card K = 4) :
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
        (permH hK (Equiv.swap 0 1)) ≠ 1 := by
  intro h
  have hmem : permH hK (Equiv.swap 0 1) ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K 2) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK (Equiv.swap 0 1)) = 1
    exact h
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (by
    simpa only [largeEvenScalars_def] using hmem)
  have hmat := congrArg
    (fun x : GL (Fin 6) K => ((x : Matrix (Fin 6) (Fin 6) K))) hc
  rw [permH_coe, TauCeti.permutationGL_coe,
    Matrix.GeneralLinearGroup.coe_scalar] at hmat
  have h01 := congrFun (congrFun hmat 0) 1
  simp [Matrix.scalar_apply] at h01

private lemma swap01_commutes (hK : Nat.card K = 4) (ω : Kˣ)
    (i : Fin 3) :
    Commute (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
        (permH hK (Equiv.swap 0 1))) (e hK ω i) := by
    fin_cases i
    · have hfix : permH hK (Equiv.swap 0 1) *
          diagSU hK (d0 ω)
            (d0_prod hK ω) *
          (permH hK (Equiv.swap 0 1))⁻¹ =
          diagSU hK (d0 ω)
            (d0_prod hK ω) :=
        permH_conj_diagSU_fix hK _ _ _
          (fun j => congrFun (swap_fix (d := d0 ω) (by simp [d0])) j)
      have hE : Commute (permH hK (Equiv.swap 0 1))
          (E hK (Pi.mulSingle 0 ω)) := by
        rw [E_single_zero]
        exact comm_of_conj_eq hfix
      simpa [e] using
        hE.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2))
    · have hfix : permH hK (Equiv.swap 0 1) *
          diagSU hK (d1 ω)
            (d1_prod hK ω) *
          (permH hK (Equiv.swap 0 1))⁻¹ =
          diagSU hK (d1 ω)
            (d1_prod hK ω) :=
        permH_conj_diagSU_fix hK _ _ _
          (fun j => congrFun (swap_fix (d := d1 ω) (by simp [d1])) j)
      have hE : Commute (permH hK (Equiv.swap 0 1))
          (E hK (Pi.mulSingle 1 ω)) := by
        rw [E_single_one]
        exact comm_of_conj_eq hfix
      simpa [e] using
        hE.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2))
    · have hfix : permH hK (Equiv.swap 0 1) *
          diagSU hK (d2 ω)
            (d2_prod hK ω) *
          (permH hK (Equiv.swap 0 1))⁻¹ =
          diagSU hK (d2 ω)
            (d2_prod hK ω) :=
        permH_conj_diagSU_fix hK _ _ _
          (fun j => congrFun (swap_fix (d := d2 ω) (by simp [d2])) j)
      have hE : Commute (permH hK (Equiv.swap 0 1))
          (E hK (Pi.mulSingle 2 ω)) := by
        rw [E_single_two]
        exact comm_of_conj_eq hfix
      simpa [e] using
        hE.map (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2))

private lemma permH_sq (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ^ 2 = 1) :
    permH hK σ ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, permH_coe, ← map_pow, hσ, map_one,
    Subgroup.coe_one]

lemma exists_t (hK : Nat.card K = 4) (ω : Kˣ)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) = ⊥) :
    ∃ t : LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2),
      (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
        t ∉ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2)) ∧
        ∀ i, Commute t (e hK ω i) := by
  let t := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
    (permH hK (Equiv.swap 0 1))
  have ht_ne : t ≠ 1 := by
    intro h
    exact permH_swap01_ne_one hK (by simpa [t] using h)
  refine ⟨t, ⟨1, ?_⟩, ?_, ?_⟩
  · change (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK (Equiv.swap 0 1))) ^ (2 ^ 1) = 1
    rw [show 2 ^ 1 = (2 : ℕ) by norm_num, ← map_pow,
      permH_sq hK (Equiv.swap 0 1) (by rw [pow_two, Equiv.swap_mul_self]), map_one]
  · intro ht
    have : t ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2))) := by
      rw [← hZ]
      exact ht
    exact ht_ne (Subgroup.mem_bot.mp this)
  · exact fun i => swap01_commutes hK ω i

lemma map_permH_sq (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ^ 2 = 1) :
    (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK σ)) ^ 2 = 1 := by
  rw [← map_pow, permH_sq hK σ hσ, map_one]

lemma conj_fix_of (hK : Nat.card K = 4) (ω : Kˣ)
    (σ : Equiv.Perm (Fin 6)) (i : Fin 3) (d : Fin 6 → Kˣ) (hd : ∏ j, d j = 1)
    (hEi : E hK (Pi.mulSingle i ω) =
      diagSU hK d hd)
    (hfix : ∀ j, d (σ⁻¹ j) = d j) :
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
        (permH hK σ) * e hK ω i *
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
          (permH hK σ))⁻¹ =
      e hK ω i := by
  have h := permH_conj_diagSU_fix hK σ d hd hfix
  rw [← hEi] at h
  simpa [e] using
    congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)) h

lemma conj_inv_of (hK : Nat.card K = 4) (ω : Kˣ)
    (σ : Equiv.Perm (Fin 6)) (i : Fin 3) (d : Fin 6 → Kˣ) (hd : ∏ j, d j = 1)
    (hEi : E hK (Pi.mulSingle i ω) =
      diagSU hK d hd)
    (hinv : ∀ j, d (σ⁻¹ j) = (d j)⁻¹) :
    LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
        (permH hK σ) * e hK ω i *
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
          (permH hK σ))⁻¹ =
      (e hK ω i)⁻¹ := by
  have h := permH_conj_diagSU_inv hK σ d hd hinv
  rw [← hEi] at h
  simpa [e] using
    congrArg (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)) h

lemma inverts (hK : Nat.card K = 4) {ω : Kˣ} (hω : ω ^ 3 = 1)
    (i : Fin 3) :
    ∃ s : LargeEvenProj (LargeEvenSUGroup (Fin 6) K 2),
      (∃ k : ℕ, s ^ 2 ^ k = 1) ∧
        s * e hK ω i * s⁻¹ =
          (e hK ω i)⁻¹ := by
  fin_cases i
  · refine ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK (Equiv.swap 2 3)), ⟨1, ?_⟩, ?_⟩
    · simpa using map_permH_sq hK (Equiv.swap 2 3)
        (by rw [pow_two, Equiv.swap_mul_self])
    · exact conj_inv_of hK ω (Equiv.swap 2 3) 0
        (d0 ω) (d0_prod hK ω)
        (E_single_zero hK ω)
        (fun j => congrFun (d0_swap23 hω) j)
  · refine ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK (Equiv.swap 4 5)), ⟨1, ?_⟩, ?_⟩
    · simpa using map_permH_sq hK (Equiv.swap 4 5)
        (by rw [pow_two, Equiv.swap_mul_self])
    · exact conj_inv_of hK ω (Equiv.swap 4 5) 1
        (d1 ω) (d1_prod hK ω)
        (E_single_one hK ω)
        (fun j => congrFun (d1_swap45 hω) j)
  · refine ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (permH hK sigma2), ⟨1, ?_⟩, ?_⟩
    · simpa using map_permH_sq hK sigma2
        sigma2_sq
    · exact conj_inv_of hK ω sigma2 2
        (d2 ω) (d2_prod hK ω)
        (E_single_two hK ω)
        (fun j => congrFun (d2_swap0213 hω) j)

end CFSG.StandardType.FrameRoute.SUSix

end
