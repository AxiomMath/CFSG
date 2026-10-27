module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem exists_natHom {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)} {H : Subgroup (MulAut V)}
    {Z : Subgroup V} {π : ↥Γ →* ↥H} (hD : (FFModel.nat Γ).RealizesVia H ⊤ Z π) :
    ∃ B : V →* Multiplicative (Fin n → K), Function.Surjective B ∧ (∀ v, B v = 1 ↔ v ∈ Z) ∧
      ∀ (γ : ↥Γ) (v : V), B (((π γ : ↥H) : MulAut V) v) = natAct Γ γ (B v) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hD
  set e := B5.natQuotEquiv (Multiplicative (Fin n → K)) with he
  refine ⟨(e.toMonoidHom.comp β).comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu⟩ := hβs (e.symm m)
    refine ⟨u, ?_⟩
    change e (β ⟨(u : V), Subgroup.mem_top _⟩) = m
    rw [show (⟨(u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u from rfl, hu,
      MulEquiv.apply_symm_apply]
  · intro v
    change e (β ⟨v, Subgroup.mem_top v⟩) = 1 ↔ v ∈ Z
    exact (MulEquiv.map_eq_one_iff e).trans (hβk _)
  · intro γ v
    have h1 : β ⟨v, Subgroup.mem_top v⟩ =
        QuotientGroup.mk ⟨e (β ⟨v, Subgroup.mem_top v⟩), Subgroup.mem_top _⟩ := by
      apply e.injective
      rfl
    exact congrArg e (hβe γ ⟨v, Subgroup.mem_top v⟩ ⟨e (β ⟨v, Subgroup.mem_top v⟩),
      Subgroup.mem_top _⟩ (Subgroup.mem_top _) (Subgroup.mem_top _) h1)

theorem exists_induced {V W : Type*} [Group V] [Group W] (B : V →* W)
    (hB : Function.Surjective B) (f : V →* V) (hf : ∀ v, B v = 1 → B (f v) = 1) :
    ∃ Y : W →* W, ∀ v, Y (B v) = B (f v) := by
  have hwd : ∀ v w, B v = B w → B (f v) = B (f w) := by
    intro v w h
    have h1 : B (v * w⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 := hf _ h1
    rw [map_mul, map_mul, map_inv, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  set s := Function.surjInv hB with hs
  refine ⟨{ toFun := fun m => B (f (s m)), map_one' := ?_, map_mul' := ?_ }, fun v => ?_⟩
  · rw [hwd (s 1) 1 (by rw [Function.surjInv_eq hB, map_one]), map_one, map_one]
  · intro m₁ m₂
    rw [← map_mul, ← map_mul]
    exact hwd _ _ (by rw [map_mul, Function.surjInv_eq hB, Function.surjInv_eq hB,
      Function.surjInv_eq hB])
  · exact hwd _ _ (Function.surjInv_eq hB _)

variable {K : Type} [Field K]

theorem eq_smul_of_comm_trv {n : ℕ} (hn : 2 ≤ n)
    (Y : Multiplicative (Fin n → K) →* Multiplicative (Fin n → K))
    (hc : ∀ (i j : Fin n) (hij : i ≠ j) (c : K) (x : Multiplicative (Fin n → K)),
      Y (natAct (StatedSL n K) (B5.trvSL i j hij c) x) =
        natAct (StatedSL n K) (B5.trvSL i j hij c) (Y x)) :
    ∃ l : K, ∀ x, Multiplicative.toAdd (Y x) = l • Multiplicative.toAdd x := by
  set y : (Fin n → K) →+ (Fin n → K) := AddMonoidHom.toMultiplicative.symm Y with hy
  have hyv : ∀ v, y v = Multiplicative.toAdd (Y (Multiplicative.ofAdd v)) := fun v => rfl
  have h1 : ∀ (i j : Fin n) (hij : i ≠ j) (c : K),
      y (Pi.single i c) = Pi.single i (c * y (Pi.single j 1) j) := by
    intro i j hij c
    have h := congrArg Multiplicative.toAdd (hc i j hij c (Multiplicative.ofAdd (Pi.single j 1)))
    rw [B5.natAct_trvSL, B5.natAct_trvSL] at h
    simp only [toAdd_ofAdd, Pi.single_eq_same, mul_one] at h
    rw [ofAdd_add, map_mul, toAdd_mul] at h
    exact add_left_cancel h
  have hne : ∀ i : Fin n, ∃ j : Fin n, i ≠ j := by
    intro i
    by_cases hi0 : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [hi0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, hi0⟩
  have h2 : ∀ i j : Fin n, i ≠ j → y (Pi.single i 1) i = y (Pi.single j 1) j := by
    intro i j hij
    rw [h1 i j hij 1, Pi.single_eq_same, one_mul]
  set l := y (Pi.single ⟨0, by omega⟩ 1) ⟨0, by omega⟩ with hl
  have h3 : ∀ j : Fin n, y (Pi.single j 1) j = l := by
    intro j
    by_cases hj : j = ⟨0, by omega⟩
    · rw [hj]
    · exact h2 j _ hj
  have h4 : ∀ (i : Fin n) (c : K), y (Pi.single i c) = Pi.single i (c * l) := by
    intro i c
    obtain ⟨j, hij⟩ := hne i
    rw [h1 i j hij c, h3 j]
  refine ⟨l, fun x => ?_⟩
  change Multiplicative.toAdd (Y (Multiplicative.ofAdd (Multiplicative.toAdd x))) = _
  rw [← hyv]
  conv_lhs => rw [← Finset.univ_sum_single (Multiplicative.toAdd x)]
  rw [map_sum]
  conv_rhs => rw [← Finset.univ_sum_single (Multiplicative.toAdd x), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h4]
  ext k
  by_cases hk : k = i
  · subst hk
    simp [mul_comm]
  · simp [Pi.single_eq_of_ne hk]

noncomputable def torusSL (m : ℕ) (μ : Kˣ) : ↥(StatedSL (m + 2) K) :=
  ⟨Matrix.GeneralLinearGroup.mk''
      (Matrix.diagonal (Fin.cons (μ : K) (Fin.cons ((μ⁻¹ : Kˣ) : K) fun _ => 1)))
      (by rw [Matrix.det_diagonal, Fin.prod_cons, Fin.prod_cons]; simp),
    Subgroup.subset_closure (by
      show Matrix.det
        (Matrix.diagonal (Fin.cons (μ : K) (Fin.cons ((μ⁻¹ : Kˣ) : K) fun _ => 1))) = 1
      rw [Matrix.det_diagonal, Fin.prod_cons, Fin.prod_cons]
      simp)⟩

theorem natAct_torusSL (m : ℕ) (μ : Kˣ) (c : K) :
    natAct (StatedSL (m + 2) K) (torusSL m μ) (Multiplicative.ofAdd (Pi.single 0 c)) =
      Multiplicative.ofAdd (Pi.single 0 ((μ : K) * c)) := by
  unfold natAct
  congr 1
  funext k
  change Matrix.mulVec (Matrix.diagonal (Fin.cons (μ : K) (Fin.cons ((μ⁻¹ : Kˣ) : K) fun _ => 1)))
    (Pi.single 0 c) k = _
  rw [Matrix.mulVec_diagonal]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
