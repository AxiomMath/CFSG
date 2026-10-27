module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelJ34Data
import CFSG.LocalAnalysis.StandardType.ZS.Basic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.PrimModel

@[expose] def j34MatFun {K : Type} [Field K] (β : K) : Fin 4 → Matrix (Fin 4) (Fin 4) K :=
  ![Matrix.blockSucc (diagSignMat 0), Matrix.blockSucc (pijMat 0 1 1),
    Matrix.blockSucc (pijMat 1 2 1), Matrix.blockSucc (j34BlockMat β)]

theorem range_j34MatFun {K : Type} [Field K] (β : K) : Set.range (j34MatFun β) = j34Mats β := by
  ext M
  simp only [Set.mem_range, j34Mats, Set.mem_image, j34BlockMats, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨diagSignMat 0, Or.inl rfl, rfl⟩
    · exact ⟨pijMat 0 1 1, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨pijMat 1 2 1, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨j34BlockMat β, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨S, (rfl | rfl | rfl | rfl), rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem ne_three_of_two_mul_sq_add_add_one_eq_zero {β : ZMod p}
    (hβ : 2 * β ^ 2 + β + 1 = 0) : p ≠ 3 := by
  rintro rfl
  revert β
  decide +revert

private theorem j34_inv_beta {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) :
    β⁻¹ = -1 - 2 * β := by
  apply inv_eq_of_mul_eq_one_right
  linear_combination -hβ

private theorem eq_blockSucc_of {K : Type} [Semiring K] {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} {D : Matrix (Fin n) (Fin n) K}
    (h1 : ∀ i j : Fin n, M i.castSucc j.castSucc = D i j)
    (h2 : ∀ i : Fin n, M i.castSucc (Fin.last n) = 0)
    (h3 : ∀ j : Fin n, M (Fin.last n) j.castSucc = 0)
    (h4 : M (Fin.last n) (Fin.last n) = 1) : M = Matrix.blockSucc D := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using h4
    | cast j => simpa using h3 j
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa using h2 i
    | cast j => simpa using h1 i j

theorem evMat_j34G (hp : p ≠ 2) {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) (k : Fin 4) :
    evMat (evalGa hβ) 1 (j34G k) = j34MatFun β k := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  have hb : β⁻¹ = -1 - 2 * β := j34_inv_beta hβ
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  fin_cases k
  · refine eq_blockSucc_of (D := diagSignMat 0) ?_ ?_ ?_ ?_
    · intro i j; fin_cases i <;> fin_cases j <;>
        simp [j34G, evMat, evalGa_qg, diagSignMat, htwo]
    · intro i; fin_cases i <;> simp [j34G, evMat, evalGa_qg]
    · intro j; fin_cases j <;> simp [j34G, evMat, evalGa_qg]
    · simp [j34G, evMat, evalGa_qg, htwo]
  · refine eq_blockSucc_of (D := pijMat 0 1 1) ?_ ?_ ?_ ?_
    · intro i j; fin_cases i <;> fin_cases j <;>
        simp [j34G, evMat, evalGa_qg, pijMat, htwo]
    · intro i; fin_cases i <;> simp [j34G, evMat, evalGa_qg]
    · intro j; fin_cases j <;> simp [j34G, evMat, evalGa_qg]
    · simp [j34G, evMat, evalGa_qg, htwo]
  · refine eq_blockSucc_of (D := pijMat 1 2 1) ?_ ?_ ?_ ?_
    · intro i j; fin_cases i <;> fin_cases j <;>
        simp [j34G, evMat, evalGa_qg, pijMat, htwo]
    · intro i; fin_cases i <;> simp [j34G, evMat, evalGa_qg]
    · intro j; fin_cases j <;> simp [j34G, evMat, evalGa_qg]
    · simp [j34G, evMat, evalGa_qg, htwo]
  · refine eq_blockSucc_of (D := j34BlockMat β) ?_ ?_ ?_ ?_
    · intro i j; fin_cases i <;> fin_cases j <;>
        simp [j34G, evMat, j34BlockMat, evalGa_qg, hb, -mul_eq_mul_left_iff,
          -mul_eq_mul_right_iff] <;>
        ring
    · intro i; fin_cases i <;> simp [j34G, evMat, evalGa_qg]
    · intro j; fin_cases j <;> simp [j34G, evMat, evalGa_qg]
    · simp [j34G, evMat, evalGa_qg, htwo]

theorem j34_basisClosure_eq (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {β : ZMod p}
    (hβ : 2 * β ^ 2 + β + 1 = 0) : basisClosure f (j34Mats β) = j34Tab.group (evalGa hβ) f := by
  rw [← range_j34MatFun β]
  exact ReflTable.basisClosure_eq_group j34Tab_valid hp fun k => by
    rw [j34Tab_gen k, evMat_j34G hp hβ k]

private theorem j34_base_span (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) :
    Submodule.span (ZMod p)
      (Set.range fun l : Fin 4 => vecR (evalGa hβ) f (j34Pt (j34Orb 0 l))) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hfi : ∀ i : Fin 4, f i ∈ Submodule.span (ZMod p)
      (Set.range fun l : Fin 4 => vecR (evalGa hβ) f (j34Pt (j34Orb 0 l))) :=
    fun i => mem_span_of_sum_smul_eq hp (evalGa hβ) f (j34Span i) i (j34_span i)
  exact (Submodule.span_le.2 (by
    rintro x hx
    rw [Set.mem_range] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfi i)) (by rw [f.span_eq]; trivial)

theorem card_basisClosure_j34Mats (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) : Nat.card (basisClosure f (j34Mats β)) = 336 := by
  have hgood : ∀ x, GoodGa x → evalGa hβ x ≠ 0 := fun x hx => evalGa_ne_zero hp hβ hx
  have hx : Function.Injective fun i : Fin 43 => vecR (evalGa hβ) f (j34Pt i) := by
    intro a b hab
    by_contra hne
    obtain ⟨l, hl⟩ := j34_pt_ne a b hne
    exact (vecR_ne_of_good hgood f ⟨l, hl⟩) hab
  have hO : Function.Injective j34Orb :=
    List.nodup_ofFn.1 (CFSG.Decide.nodup_of_bitsetNodup
      (fun t : Fin 4 → Fin 43 => CFSG.Decide.finFunKey fun l : Fin 3 => t l.castSucc) j34_orb_key)
  have hπ : ∀ (k : Fin 4) (i : Fin 43),
      j34Tab.refl (evalGa hβ) f (j34Tab.gen k) (vecR (evalGa hβ) f (j34Pt i)) =
        vecR (evalGa hβ) f (j34Pt (j34Pi k i)) :=
    fun k i => ReflTable.refl_apply_vecR j34Tab_valid hp (j := j34Tab.gen k) (j34_pt_act k i)
  have hb : ∀ h : U ≃ₗ[ZMod p] U,
      (∀ l : Fin 4, h (vecR (evalGa hβ) f (j34Pt (j34Orb 0 l))) =
        vecR (evalGa hβ) f (j34Pt (j34Orb 0 l))) → h = 1 := by
    intro h hh
    apply LinearEquiv.ext
    intro u
    have hfix : ∀ v ∈ Submodule.span (ZMod p)
        (Set.range fun l : Fin 4 => vecR (evalGa hβ) f (j34Pt (j34Orb 0 l))), h v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem w hw => rcases hw with ⟨l, rfl⟩; exact hh l
      | zero => exact map_zero h
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | smul c a _ ha => rw [map_smul, ha]
    exact hfix u (by rw [j34_base_span hp f hβ]; trivial)
  rw [j34_basisClosure_eq hp f hβ]
  refine card_closure_eq_of_orbit (g := fun k => j34Tab.refl (evalGa hβ) f (j34Tab.gen k))
    (x := fun i => vecR (evalGa hβ) f (j34Pt i)) (π := j34Pi) (O := j34Orb)
    (nxt := j34Nxt) (pred := j34Pred) (pk := j34Pk) ?_ hx hπ hO 0 hb ?_ ?_
  · exact fun k => ReflTable.refl_mul_self j34Tab_valid hp (j34Tab.gen k)
  · exact j34_orb_nxt
  · exact j34_orb_pred

private theorem j34_not_dvd_336 (hp : p ≠ 2) (hp7 : p ≠ 7) {β : ZMod p}
    (hβ : 2 * β ^ 2 + β + 1 = 0) : ¬ p ∣ 336 := by
  have hpp : Nat.Prime p := Fact.out
  have h336 : (336 : ℕ) = 2 ^ 4 * 3 * 7 := by norm_num
  rw [h336]
  intro h
  rcases hpp.dvd_mul.1 h with h | h
  · rcases hpp.dvd_mul.1 h with h | h
    · exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h))
    · exact ne_three_of_two_mul_sq_add_add_one_eq_zero hβ
        ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h)
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_seven).1 h)

theorem j34_transvectionFree (hp : p ≠ 2) (hp7 : p ≠ 7) (f : Module.Basis (Fin 4) (ZMod p) U)
    {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) :
    QTwoLin.TransvectionFree (j34Tab.group (evalGa hβ) f) := by
  rw [← j34_basisClosure_eq hp f hβ]
  refine transvectionFree_of_not_dvd_card ?_ ?_
  · rw [card_basisClosure_j34Mats hp f hβ]; norm_num
  · rw [card_basisClosure_j34Mats hp f hβ]
    exact j34_not_dvd_336 hp hp7 hβ

end CFSG.StandardType.ZS.PrimModel

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime]

open CFSG.StandardType.ZS.PrimModel in
private theorem tfJ34Model_holds_aux (p : ℕ) [Fact p.Prime] : TFJ34Model p := by
  intro W _ _ f β hp hp7 hβ h₁ z τ hh₁ hz hτ
  have hgood : ∀ x, GoodGa x → evalGa hβ x ≠ 0 := fun x hx => evalGa_ne_zero hp hβ hx
  have htv : QTwoLin.TransvectionFree (j34Tab.group (evalGa hβ) f) :=
    j34_transvectionFree hp hp7 f hβ
  have hfix := ReflTable.exists_conj_le_inf_ker j34Tab_valid hgood hp htv
    ({0, 1} : Finset (Fin 4)) 0 j34Wit j34Tab_wit
  rw [j34_basisClosure_eq hp f hβ]
  have hz_eq : z = j34Tab.refl (evalGa hβ) f 0 * j34Tab.refl (evalGa hβ) f 1 := by
    refine eq_mul_of_toMatrix_eq_mul f ?_
    rw [hz, ReflTable.toMatrix_refl (T := j34Tab) (φ := evalGa hβ) (f := f) j34Tab_valid hp
        (0 : Fin 21),
      ReflTable.toMatrix_refl (T := j34Tab) (φ := evalGa hβ) (f := f) j34Tab_valid hp
        (1 : Fin 21),
      j34Tab_diag.1, j34Tab_diag.2.1, evMat_diagZ hp (evalGa hβ) (0 : Fin 4),
      evMat_diagZ hp (evalGa hβ) (1 : Fin 4)]
  have hh₁_eq : h₁ = j34Tab.refl (evalGa hβ) f 0 := by
    refine eq_of_toMatrix_eq f ?_
    rw [hh₁, ReflTable.toMatrix_refl (T := j34Tab) (φ := evalGa hβ) (f := f) j34Tab_valid hp
        (0 : Fin 21),
      j34Tab_diag.1, evMat_diagZ hp (evalGa hβ) (0 : Fin 4)]
  have hτ_eq : τ = j34Tab.refl (evalGa hβ) f 3 := by
    refine eq_of_toMatrix_eq f ?_
    rw [hτ, ReflTable.toMatrix_refl (T := j34Tab) (φ := evalGa hβ) (f := f) j34Tab_valid hp
        (3 : Fin 21),
      j34Tab_diag.2.2, evMat_diagZ hp (evalGa hβ) (2 : Fin 4)]
  refine primFrameData_of_diagonal hp f ({0, 1} : Finset (Fin 4)) (i₁ := 0) (iτ := 2)
    (by decide) (by decide) (by decide) ?_ hh₁ hτ ?_ ?_ ?_ ?_
  · rw [hz, diagSignMat_mul_diagSignMat (K := ZMod p) (n := 4) (i := 0) (j := 1) (by decide)]
  · rw [hz_eq]
    exact mul_mem (ReflTable.refl_mem_group j34Tab_valid hp (0 : Fin 21))
      (ReflTable.refl_mem_group j34Tab_valid hp (1 : Fin 21))
  · rw [hh₁_eq]
    exact ReflTable.refl_mem_group j34Tab_valid hp (0 : Fin 21)
  · rw [hτ_eq, hh₁_eq]
    exact ReflTable.exists_conj_of_cls_eq j34Tab_valid hp (by decide)
  · intro x hxG hxr hmv
    obtain ⟨g, hgG, hgm⟩ := hfix x hxG hxr hmv
    exact ⟨g, hgG, by simpa [hh₁_eq] using hgm⟩

theorem tfJ34Model_holds : TFJ34Model p := tfJ34Model_holds_aux p

end CFSG.StandardType.ZS

end
