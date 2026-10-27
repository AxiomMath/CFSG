module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrthPlus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB SpCoord Multiplicative NbrOrth

theorem ggWTEven_reflSet_eq {p : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n) :
    ggTorusReflSet p A =
      {φ | φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧ GGIsReflection p φ} := by
  ext φ
  constructor
  · rintro ⟨n, hn, -, rfl, hrefl⟩
    exact ⟨ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn, hrefl⟩
  · rintro ⟨hφW, hrefl⟩
    obtain ⟨_, ⟨n, rfl⟩, hn, hvc⟩ := mem_ggAutomizer_iff.mp hφW
    refine ⟨n, hn, hW n hn, ?_, hrefl⟩
    exact MulEquiv.ext fun a => Subtype.ext (hvc a)

@[expose] def ggWTEven_evenLin (p k : ℕ) (b : Module.Basis (Fin k) (ZMod p) (Fin k → ZMod p)) :
    Subgroup ((Fin k → ZMod p) ≃ₗ[ZMod p] (Fin k → ZMod p)) where
  carrier := {a | ∃ (σ : Equiv.Perm (Fin k)) (c : Fin k → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧ ∀ i, a (b i) = c i • b (σ i)}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_, ?_⟩
    · intro i; left; rfl
    · simp
    · intro i; simp
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, hcprod, ha⟩ ⟨σ', c', hc', hc'prod, ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_, ?_⟩
    · intro i
      change c' i * c (σ' i) = 1 ∨ c' i * c (σ' i) = -1
      rcases hc' i with h | h <;> rcases hc (σ' i) with h2 | h2
      · left; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
    · rw [Finset.prod_mul_distrib, hc'prod]
      have hre : (∏ i, c (σ' i)) = ∏ i, c i := by
        refine Finset.prod_bij (fun i _ => σ' i) ?_ ?_ ?_ ?_
        · intro i _; exact Finset.mem_univ _
        · intro i _ j _ hij; exact σ'.injective hij
        · intro b _; exact ⟨σ'.symm b, Finset.mem_univ _, by simp⟩
        · intro i _; rfl
      rw [hre, hcprod, mul_one]
    · intro i
      rw [LinearEquiv.mul_apply, ha', map_smul, ha, Equiv.Perm.mul_apply, smul_smul]
  inv_mem' := by
    rintro a ⟨σ, c, hc, hcprod, ha⟩
    refine ⟨σ.symm, fun j => c (σ.symm j), ?_, ?_, ?_⟩
    · intro j; exact hc (σ.symm j)
    · have hre : (∏ j, c (σ.symm j)) = ∏ j, c j := by
        refine Finset.prod_bij (fun j _ => σ.symm j) ?_ ?_ ?_ ?_
        · intro j _; exact Finset.mem_univ _
        · intro i _ j _ hij; exact σ.symm.injective hij
        · intro b _; exact ⟨σ b, Finset.mem_univ _, by simp⟩
        · intro j _; rfl
      rw [hre, hcprod]
    · intro j
      change a.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq, map_smul, ha, Equiv.apply_symm_apply, smul_smul]
      have hcc : c (σ.symm j) * c (σ.symm j) = 1 := by
        rcases hc (σ.symm j) with h | h <;> rw [h] <;> ring
      rw [hcc, one_smul]

lemma ggWTEven_permAut_mul {p k : ℕ} (σ τ : Equiv.Perm (Fin k)) :
    (permAut (σ * τ) : MulAut (Fin k → Multiplicative (ZMod p))) =
      permAut σ * permAut τ := by
  ext f i
  simp [permAut_apply, MulAut.mul_apply, Equiv.Perm.mul_apply, Function.comp]

lemma ggWTEven_dinv_mulSingle_right {p m : ℕ} {i k : Fin m} (hik : i ≠ k)
    (a : Multiplicative (ZMod p)) :
    dinv i k (Pi.mulSingle k a) =
      (Pi.mulSingle k a : Fin m → Multiplicative (ZMod p))⁻¹ := by
  funext j
  simp only [dinv]
  by_cases hji : j = i
  · rw [hji]
    simp [Function.update_self, Function.update_of_ne hik, Pi.mulSingle_eq_of_ne hik]
  · by_cases hjk : j = k
    · rw [hjk]
      simp [Function.update_of_ne (Ne.symm hik), Pi.mulSingle_eq_same]
    · simp [Function.update_of_ne hji, Function.update_of_ne hjk, Pi.mulSingle_eq_of_ne hjk]

lemma ggWTEven_dinv_apply {p k : ℕ} (i j l m : Fin k) (hij : i ≠ j) :
    toAdd (dinv i j (Pi.mulSingle l (ofAdd (1 : ZMod p))) m) =
      if m = l then (if l = i ∨ l = j then (-1 : ZMod p) else 1) else 0 := by
  by_cases hli : l = i
  · rw [hli, dinv_mulSingle_self hij]
    by_cases hmi : m = i
    · rw [hmi]
      simp [Pi.inv_apply, Pi.mulSingle_eq_same, toAdd_inv]
    · rw [Pi.inv_apply, Pi.mulSingle_eq_of_ne hmi, inv_one, toAdd_one]
      simp [hmi]
  · by_cases hlj : l = j
    · rw [hlj, ggWTEven_dinv_mulSingle_right hij]
      by_cases hmj : m = j
      · rw [hmj]
        simp [Pi.inv_apply, Pi.mulSingle_eq_same, toAdd_inv]
      · rw [Pi.inv_apply, Pi.mulSingle_eq_of_ne hmj, inv_one, toAdd_one]
        simp [hmj]
    · rw [dinv_mulSingle_of_ne hli hlj]
      by_cases hml : m = l
      · rw [hml, Pi.mulSingle_eq_same, toAdd_ofAdd]
        simp [hli, hlj]
      · rw [Pi.mulSingle_eq_of_ne hml, toAdd_one]
        simp [hml]

lemma ggWTEven_prod_pair {p k : ℕ} (i j : Fin k) (hij : i ≠ j) :
    (∏ l, (if l = i ∨ l = j then (-1 : ZMod p) else 1)) = 1 := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (s := Finset.univ) (i := i)
    (f := fun l => if l = i ∨ l = j then (-1 : ZMod p) else 1) (Finset.mem_univ i)]
  have hj : j ∈ Finset.univ \ {i} := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    exact fun h => hij h.symm
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (s := Finset.univ \ {i}) (i := j)
    (f := fun x => if x = i ∨ x = j then (-1 : ZMod p) else 1) hj]
  have h1 : (if i = i ∨ i = j then (-1 : ZMod p) else 1) = -1 := by
    rw [if_pos (Or.inl rfl)]
  have h2 : (if j = i ∨ j = j then (-1 : ZMod p) else 1) = -1 := by
    rw [if_pos (Or.inr rfl)]
  have h3 : (∏ x ∈ (Finset.univ \ {i}) \ {j}, (if x = i ∨ x = j then (-1 : ZMod p) else 1)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
    rw [if_neg (fun h => h.elim hx.1.2 hx.2)]
  rw [h1, h2, h3]
  ring

lemma ggWTEven_even_card_of_prod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    (c : Fin k → ZMod p) (hc : ∀ i, c i = 1 ∨ c i = -1) (hprod : ∏ i, c i = 1) :
    Even (Finset.univ.filter (fun i => c i = -1)).card := by
  have h2p : 2 < p := by
    have := hp.two_le
    omega
  haveI : Fact (2 < p) := ⟨h2p⟩
  let S := Finset.univ.filter (fun i => c i = -1)
  have h1 : (∏ i, c i) = (-1 : ZMod p) ^ S.card := by
    have hc' : (∏ i, c i) = ∏ i, (if c i = -1 then (-1 : ZMod p) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rcases hc i with h | h <;> simp [h]
    rw [hc']
    rw [← Finset.prod_filter (s := Finset.univ) (f := fun _ => (-1 : ZMod p))
      (p := fun i => c i = -1), Finset.prod_const]
  have h2 : (-1 : ZMod p) ^ S.card = 1 := by rw [← h1, hprod]
  rcases Nat.even_or_odd S.card with he | ho
  · exact he
  · exfalso
    rw [Odd.neg_one_pow ho] at h2
    exact ZMod.neg_one_ne_one h2

lemma ggWTEven_permAut_mem_closure {p k : ℕ} (σ : Equiv.Perm (Fin k)) :
    permAut σ ∈ Subgroup.closure
      (Set.range (fun x : {x : Fin k × Fin k // x.1 ≠ x.2} =>
        (permAut (Equiv.swap x.1.1 x.1.2) : MulAut (Fin k → Multiplicative (ZMod p))))) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact Subgroup.one_mem _
  | swap_mul π x y hxy ih =>
    rw [ggWTEven_permAut_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨(x, y), hxy⟩, rfl⟩) ih

end CFSG.StandardType

end
