module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortRankSym

public section

namespace CFSG.StandardType.FrameRoute.SUSix

open CFSG.Assembly

variable {K : Type} [Field K]

private lemma card_units (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

lemma unit_cube (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have hu := pow_card_eq_one' (G := Kˣ) (x := u)
  rwa [card_units hK] at hu

lemma exists_unit_ne_one (hK : Nat.card K = 4) : ∃ u : Kˣ, u ≠ 1 := by
  by_contra h
  push Not at h
  have h1 : Nat.card Kˣ = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [h a, h b]⟩, ⟨1⟩⟩
  rw [card_units hK] at h1
  norm_num at h1

private lemma neg_one (hK : Nat.card K = 4) : (-1 : K) = 1 := by
  have hchar : CharP K 2 :=
    (show CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K from
      ⟨Nat.prime_two, le_rfl, by simpa using hK⟩).charP
  exact @CharTwo.neg_eq K _ hchar 1

@[expose] def monomial (u : Fin 3 → Kˣ) : Fin 6 → Kˣ :=
  ![u 2, u 2, u 0 * (u 2) ^ 2, (u 0) ^ 2 * (u 2) ^ 2, u 1, (u 1) ^ 2]

lemma monomial_prod (hK : Nat.card K = 4) (u : Fin 3 → Kˣ) :
    ∏ i, monomial u i = 1 := by
  rw [Fin.prod_univ_six]
  simp only [monomial]
  have h0 := unit_cube hK (u 0)
  have h1 := unit_cube hK (u 1)
  have h2 := unit_cube hK (u 2)
  have h2' : u 2 * u 2 * u 2 ^ 2 * u 2 ^ 2 = 1 := by
    have h : u 2 * u 2 * u 2 ^ 2 * u 2 ^ 2 = u 2 ^ 6 := by group
    rw [h, show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h2, one_pow]
  calc
    u 2 * u 2 * (u 0 * u 2 ^ 2) * (u 0 ^ 2 * u 2 ^ 2) * u 1 * u 1 ^ 2 =
        (u 0 * u 0 ^ 2) * (u 1 * u 1 ^ 2) * (u 2 * u 2 * u 2 ^ 2 * u 2 ^ 2) := by
      ac_rfl
    _ = (u 0 ^ 3) * (u 1 ^ 3) * (u 2 * u 2 * u 2 ^ 2 * u 2 ^ 2) := by
      rw [← pow_succ', ← pow_succ']
    _ = 1 := by rw [h0, h1, h2']; simp

@[expose] noncomputable def diagSU (hK : Nat.card K = 4)
    (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    ↥(LargeEvenSUGroup (Fin 6) K 2) :=
  ⟨TauCeti.diagGL d, by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [TauCeti.diagGL_coe, Matrix.det_diagonal]
      have h := congrArg (fun x : Kˣ => (x : K)) hd
      simpa using h
    · rw [TauCeti.diagGL_coe, Matrix.diagonal_map (by norm_num),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
      funext i
      have h3 : (d i : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, unit_cube hK (d i), Units.val_one]
      rw [show (d i : K) ^ 2 * (d i : K) = (d i : K) ^ 3 by ring, h3]
      rfl⟩

lemma diagSU_coe (hK : Nat.card K = 4) (d : Fin 6 → Kˣ)
    (hd : ∏ i, d i = 1) :
    ((diagSU hK d hd : ↥(LargeEvenSUGroup (Fin 6) K 2)) :
      GL (Fin 6) K) = TauCeti.diagGL d := rfl

@[expose] noncomputable def E (hK : Nat.card K = 4) :
    (Fin 3 → Kˣ) →* ↥(LargeEvenSUGroup (Fin 6) K 2) where
  toFun u := diagSU hK (monomial u)
    (monomial_prod hK u)
  map_one' := by
    apply Subtype.ext
    change TauCeti.diagGL (monomial 1) = 1
    rw [show monomial 1 = 1 by
      funext i
      fin_cases i <;> simp [monomial]]
    exact map_one _
  map_mul' u v := by
    apply Subtype.ext
    change TauCeti.diagGL (monomial (u * v)) =
      TauCeti.diagGL (monomial u) *
        TauCeti.diagGL (monomial v)
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;>
      simp [monomial, mul_pow, mul_assoc, mul_left_comm]

lemma E_apply (hK : Nat.card K = 4) (u : Fin 3 → Kˣ) :
    ((E hK u : ↥(LargeEvenSUGroup (Fin 6) K 2)) : GL (Fin 6) K) =
      TauCeti.diagGL (monomial u) := rfl

private lemma E_injective (hK : Nat.card K = 4) :
    Function.Injective (E hK) := by
  intro u v huv
  have hmat := congrArg
    (fun x : ↥(LargeEvenSUGroup (Fin 6) K 2) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) huv
  rw [E_apply, E_apply, TauCeti.diagGL_coe,
    TauCeti.diagGL_coe] at hmat
  have hd := Matrix.diagonal_injective hmat
  have h2 : u 2 = v 2 := Units.ext (by simpa [monomial] using congrFun hd 0)
  have h1 : u 1 = v 1 := Units.ext (by simpa [monomial] using congrFun hd 4)
  have h0 : u 0 = v 0 := by
    have h := congrFun hd 2
    simp [monomial] at h
    rw [show ((u 2 : K)) = ((v 2 : K)) from congrArg Units.val h2] at h
    exact Units.ext (mul_right_cancel₀ (pow_ne_zero 2 (Units.ne_zero (v 2))) h)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private lemma E_scalar (hK : Nat.card K = 4) {u : Fin 3 → Kˣ}
    (h : E hK u ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K 2)) :
    u = 1 := by
  rw [Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (by
    simpa only [largeEvenScalars_def] using h)
  have hmat := congrArg
    (fun x : GL (Fin 6) K => ((x : Matrix (Fin 6) (Fin 6) K))) hc
  rw [E_apply, TauCeti.diagGL_coe,
    Matrix.GeneralLinearGroup.coe_scalar] at hmat
  have h0 := congrFun (congrFun hmat 0) 0
  have h2 := congrFun (congrFun hmat 2) 2
  have h4 := congrFun (congrFun hmat 4) 4
  have h5 := congrFun (congrFun hmat 5) 5
  simp [Matrix.scalar_apply, monomial] at h0 h2 h4 h5
  have h41 : u 2 = u 1 := Units.ext (h0.symm.trans h4)
  have h51 : u 2 = (u 1) ^ 2 := Units.ext (h0.symm.trans h5)
  have hsq : u 1 = (u 1) ^ 2 := h41.symm.trans h51
  have hu1 : u 1 = 1 := by
    have h : u 1 * 1 = u 1 * u 1 := by
      rw [mul_one, ← pow_two]
      exact hsq
    exact (mul_left_cancel h).symm
  have hu2 : u 2 = 1 := by rw [h41, hu1]
  have h02 : u 2 = u 0 * (u 2) ^ 2 := Units.ext (h0.symm.trans h2)
  have hu0 : u 0 = 1 := by
    rw [hu2] at h02
    simpa using h02.symm
  funext i
  fin_cases i
  · exact hu0
  · exact hu1
  · exact hu2

lemma E_pow_three (hK : Nat.card K = 4) (u : Fin 3 → Kˣ)
    (hu : ∀ i, u i ^ 3 = 1) : E hK u ^ 3 = 1 := by
  rw [← map_pow, show u ^ 3 = 1 by
    funext i
    simpa using hu i, map_one]

private lemma exists_pow_eq [Finite K] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) (u : Kˣ) : ∃ n : ℕ, ω ^ n = u := by
  have hcard : Nat.card (Subgroup.zpowers ω) = Nat.card Kˣ := by
    rw [Nat.card_zpowers, hω, card_units hK]
  have htop : Subgroup.zpowers ω = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  have hu : u ∈ Subgroup.zpowers ω := by rw [htop]; exact Subgroup.mem_top u
  exact (Submonoid.mem_powers_iff u ω).mp ((mem_powers_iff_mem_zpowers).mpr hu)

private lemma range_E [Finite K] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) :
    (E hK).range =
      Subgroup.closure (Set.range fun i : Fin 3 =>
        E hK (Pi.mulSingle i ω)) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    choose n hn using fun i => exists_pow_eq hK hω (u i)
    have hu : u = (Pi.mulSingle 0 ω) ^ (n 0) * (Pi.mulSingle 1 ω) ^ (n 1) *
        (Pi.mulSingle 2 ω) ^ (n 2) := by
      funext j
      fin_cases j <;>
        simp [Pi.mulSingle, hn, mul_comm]
    rw [hu, map_mul, map_mul, map_pow, map_pow, map_pow]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 0)) _
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 1)) _
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self 2)) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Pi.mulSingle i ω, rfl⟩

private lemma E_card (hK : Nat.card K = 4) :
    Nat.card (E hK).range = 27 := by
  change Nat.card (Set.range (E hK)) = 27
  rw [(Nat.card_congr (Equiv.ofInjective _ (E_injective hK))).symm,
    Nat.card_fun, Nat.card_fin, card_units hK]
  norm_num

private lemma E_map_injective (hK : Nat.card K = 4) :
    Function.Injective (fun x : (E hK).range =>
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2) (x : ↥(LargeEvenSUGroup (Fin 6) K 2))) := by
  intro x y hxy
  have hxy' : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2) (x : ↥(LargeEvenSUGroup (Fin 6) K 2)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2) (y : ↥(LargeEvenSUGroup (Fin 6) K 2)) := hxy
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp x.2
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp y.2
  have hx : (x : ↥(LargeEvenSUGroup (Fin 6) K 2)) = E hK u := hu.symm
  have hy : (y : ↥(LargeEvenSUGroup (Fin 6) K 2)) = E hK v := hv.symm
  have hker : (E hK u)⁻¹ * E hK v ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K 2) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      ((E hK u)⁻¹ * E hK v) = 1
    rw [map_mul, map_inv, ← hx, ← hy, hxy', inv_mul_cancel]
  have hsub : E hK (u⁻¹ * v) ∈
      (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K 2) := by
    rw [map_mul, map_inv]
    exact hker
  have huv : u = v := by
    have h := E_scalar hK hsub
    exact inv_mul_eq_one.mp h
  exact Subtype.ext (by rw [hx, hy, huv])

private noncomputable def E_map_equiv (hK : Nat.card K = 4) :
    (E hK).range ≃
      (E hK).range.map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)) :=
  Equiv.ofBijective
    (fun x : (E hK).range =>
      ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
          (x : ↥(LargeEvenSUGroup (Fin 6) K 2)),
        Subgroup.mem_map_of_mem _ x.2⟩)
    ⟨fun x y hxy =>
        E_map_injective hK (Subtype.ext_iff.mp hxy),
      by
        rintro ⟨y, hy⟩
        rw [Subgroup.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩⟩

private lemma E_map_card (hK : Nat.card K = 4) :
    Nat.card ((E hK).range.map
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2))) = 27 := by
  rw [← Nat.card_congr (E_map_equiv hK),
    E_card hK]

lemma closure_card [Finite K] (hK : Nat.card K = 4) {ω : Kˣ}
    (hω : orderOf ω = 3) :
    Nat.card (Subgroup.closure (Set.range fun i : Fin 3 =>
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
        (E hK (Pi.mulSingle i ω)))) = 27 := by
  rw [show Set.range (fun i : Fin 3 => LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2)
      (E hK (Pi.mulSingle i ω))) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K 2) ''
        Set.range (fun i : Fin 3 => E hK (Pi.mulSingle i ω)) from
    Set.range_comp _ _]
  rw [← MonoidHom.map_closure, ← range_E hK hω]
  exact E_map_card hK

private lemma permMatrix_apply (σ : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    σ.permMatrix K i j = if σ i = j then (1 : K) else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply]
  simp [Pi.single_apply, eq_comm]

lemma permutationGL_mem (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6)) :
    TauCeti.permutationGL (k := K) σ ∈ LargeEvenSUGroup (Fin 6) K 2 := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [TauCeti.permutationGL_coe, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h]
    · simp [h, neg_one hK]
  · rw [TauCeti.permutationGL_coe,
      show ((σ⁻¹).permMatrix K).map (· ^ 2) = (σ⁻¹).permMatrix K by
        ext i j
        rw [Matrix.map_apply, permMatrix_apply]
        by_cases h : σ⁻¹ i = j <;> simp [h],
      Matrix.transpose_permMatrix, inv_inv,
      ← Matrix.permMatrix_mul (σ := σ⁻¹) (τ := σ), inv_mul_cancel, Matrix.permMatrix_one]

@[expose] noncomputable def permH (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) : ↥(LargeEvenSUGroup (Fin 6) K 2) :=
  ⟨TauCeti.permutationGL (k := K) σ, permutationGL_mem hK σ⟩

lemma permH_coe (hK : Nat.card K = 4) (σ : Equiv.Perm (Fin 6)) :
    ((permH hK σ : ↥(LargeEvenSUGroup (Fin 6) K 2)) : GL (Fin 6) K) =
      TauCeti.permutationGL (k := K) σ := rfl

private lemma permH_conj_diagSU (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    permH hK σ * diagSU hK d hd * (permH hK σ)⁻¹ =
      diagSU hK (fun j => d (σ⁻¹ j))
        (by
          rw [show (∏ j, d (σ⁻¹ j)) = ∏ j, d j from Equiv.prod_comp σ⁻¹ d, hd]) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    permH_coe, diagSU_coe, diagSU_coe, TauCeti.permutationGL_mul_diagGL_mul_inv]

lemma permH_conj_diagSU_fix (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1)
    (hfix : ∀ j, d (σ⁻¹ j) = d j) :
    permH hK σ * diagSU hK d hd *
        (permH hK σ)⁻¹ =
      diagSU hK d hd := by
  rw [permH_conj_diagSU hK σ d hd]
  apply Subtype.ext
  rw [diagSU_coe, diagSU_coe]
  congr 1
  funext j
  exact hfix j

lemma permH_conj_diagSU_inv (hK : Nat.card K = 4)
    (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1)
    (hinv : ∀ j, d (σ⁻¹ j) = (d j)⁻¹) :
    permH hK σ * diagSU hK d hd *
        (permH hK σ)⁻¹ =
      (diagSU hK d hd)⁻¹ := by
  rw [permH_conj_diagSU hK σ d hd]
  apply Subtype.ext
  rw [diagSU_coe, Subgroup.coe_inv,
    diagSU_coe, ← map_inv]
  congr 1
  funext j
  exact hinv j


end CFSG.StandardType.FrameRoute.SUSix

end
