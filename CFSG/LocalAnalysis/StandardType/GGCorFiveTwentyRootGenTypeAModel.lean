module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestTypeA

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

section Diagonal

variable {d p : ℕ} {K : Type} [Field K]

@[expose] def pairCent (p : ℕ) (K : Type) [Field K] (i j : Fin d) :
    Subgroup (SpecialLinearGroup (Fin d) K) :=
  Subgroup.centralizer {D : SpecialLinearGroup (Fin d) K | ∃ t : Fin d → K,
    (D : Matrix (Fin d) (Fin d) K) = diagonal t ∧ t i = t j ∧ ∀ k, t k ^ p = 1}

@[expose] def IsDiagTorusModel (p : ℕ) {L' : Type} [Group L']
    (φ : SpecialLinearGroup (Fin d) K →* L') (A : Subgroup (MulAut L')) : Prop :=
  ∀ a : MulAut L', a ∈ A ↔ ∃ D : SpecialLinearGroup (Fin d) K,
    (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧ D ^ p = 1 ∧
      a = MulAut.conj (φ D)

theorem pow_eq_one_of_diagonal {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (hDp : D ^ p = 1) (i : Fin d) :
    t i ^ p = 1 := by
  have h1 : (D : Matrix (Fin d) (Fin d) K) ^ p = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hDp]
    rfl
  rw [hD, diagonal_pow] at h1
  simpa using congrFun (congrFun h1 i) i

theorem prod_eq_one_of_diagonal {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) : ∏ i, t i = 1 := by
  have h := D.2
  rw [hD, det_diagonal] at h
  exact h

theorem diag_entry_ne_zero {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (i : Fin d) : t i ≠ 0 := by
  intro h0
  have h := prod_eq_one_of_diagonal hD
  rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at h
  exact zero_ne_one h

theorem pow_eq_one_of_pow_diagonal {D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (ht : ∀ i, t i ^ p = 1) :
    D ^ p = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, hD, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
  have e : t ^ p = fun _ => (1 : K) := funext ht
  rw [e, diagonal_one]

theorem ggActsBy_conj_phi {L' : Type} [Group L'] (φ : SpecialLinearGroup (Fin d) K →* L')
    (D : SpecialLinearGroup (Fin d) K) : GGActsBy φ (MulAut.conj (φ D)) D := fun s => by
  simp only [MulAut.conj_apply, map_mul, map_inv]

end Diagonal

section Model

variable {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_isDiagTorusModel (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d)
    (hpd : Nat.Coprime p d) (hsec : SLHasSections d K) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* projectiveSL d K} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut d K), ∀ l, φa (ψ l) = ψ (a l))
    (hr : p ^ (d - 1) ≤ Nat.card A) :
    ∃ φ : SpecialLinearGroup (Fin d) K →* L', Function.Surjective φ ∧
      (∀ g, φ g = 1 → g ∈ scalars d K) ∧ IsDiagTorusModel p φ A := by
  classical
  have hd0 : 0 < d := by omega
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨φ', hφ's, hφ'ker, hdiag, hle, hfull⟩ :=
    exists_diagonal_model hp hpK hd0 hpd hperfSL hψ hker hperf hφs hφ hA hAI
  have hcardA : Nat.card A = p ^ (d - 1) := le_antisymm hle hr
  have hact : ∀ (a : MulAut L') (D : SpecialLinearGroup (Fin d) K),
      (∀ s, a (φ' s) = φ' (D * s * D⁻¹)) → a = MulAut.conj (φ' D) := by
    intro a D haD
    ext l
    obtain ⟨s, rfl⟩ := hφ's l
    rw [haD s, MulAut.conj_apply]
    simp only [map_mul, map_inv]
  refine ⟨φ', hφ's, hφ'ker, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨D, hD, hDp, haD⟩ := hdiag a ha
    exact ⟨D, hD, hDp, hact a D haD⟩
  · rintro ⟨D, ⟨t, hD⟩, hDp, rfl⟩
    obtain ⟨a, haA, D', hD', haD'⟩ := hfull hcardA t (pow_eq_one_of_diagonal hD hDp)
      (prod_eq_one_of_diagonal hD)
    have hDD' : D' = D := Subtype.ext (hD'.trans hD.symm)
    subst hDD'
    rw [← hact a D' haD']
    exact haA

section Pair

variable {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
  {A : Subgroup (MulAut L')}

omit [Finite K] [Finite L'] in
private theorem ggTorusWeylElt_permSL_gen (hM : IsDiagTorusModel p φ A)
    (σ : Equiv.Perm (Fin d)) : GGTorusWeylElt p A (φ (permSL σ)) := by
  classical
  intro a ha
  obtain ⟨D, ⟨t, hD⟩, hDp, rfl⟩ := (hM a).mp ha
  have ht : ∀ k, t k ^ p = 1 := fun k => pow_eq_one_of_diagonal hD hDp k
  set E : SpecialLinearGroup (Fin d) K := permSL σ * D * (permSL σ)⁻¹ * D⁻¹ with hE
  have hEmat : ((E : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal fun k => t (σ k) * (t k)⁻¹ := by
    rw [hE, Matrix.SpecialLinearGroup.coe_mul, coe_permSL_conj hD σ,
      coe_inv_SL_of_diagonal hD, diagonal_mul_diagonal]
    rfl
  have hEp : E ^ p = 1 := pow_eq_one_of_pow_diagonal hEmat fun k => by
    simp [mul_pow, inv_pow, ht]
  have he : φ (permSL σ) * ((MulAut.conj (φ D)) (φ (permSL σ)))⁻¹ = φ E := by
    rw [MulAut.conj_apply, hE]
    simp only [map_mul, map_inv]
    group
  refine ⟨?_, ?_⟩
  · rw [he, ← map_pow, hEp, map_one]
  · intro a' ha'
    obtain ⟨D', ⟨_, hD'⟩, _, rfl⟩ := (hM a').mp ha'
    rw [he, MulAut.conj_apply]
    have hcomm : φ D' * φ E = φ E * φ D' := by
      rw [← map_mul, ← map_mul, commute_of_diagonal hD' hEmat]
    rw [hcomm]
    group

omit [Finite K] [Finite L'] in
theorem ggTorusWeylElt_permSL (hM : IsDiagTorusModel p φ A) (i j : Fin d) :
    GGTorusWeylElt p A (φ (permSL (Equiv.swap i j))) :=
  ggTorusWeylElt_permSL_gen hM (Equiv.swap i j)

omit [Finite K] [Finite L'] in
theorem conj_permSL_mem_normalizer (hM : IsDiagTorusModel p φ A) (i j : Fin d) :
    MulAut.conj (φ (permSL (Equiv.swap i j))) ∈
      Subgroup.normalizer (A : Set (MulAut L')) := by
  classical
  set P : SpecialLinearGroup (Fin d) K := permSL (Equiv.swap i j) with hP
  set g : MulAut L' := MulAut.conj (φ P) with hg
  have hPP : P⁻¹ = P := by
    rw [hP, permSL_inv, Equiv.swap_inv]
  have hg_inv : g⁻¹ = g := by
    rw [hg, ← map_inv, ← map_inv, hPP]
  have hgg : g * g = 1 := by
    nth_rewrite 2 [hg_inv.symm]
    exact mul_inv_cancel g
  have hkey : ∀ b ∈ A, g * b * g⁻¹ ∈ A := by
    intro b hb
    obtain ⟨D, ⟨t, hD⟩, hDp, rfl⟩ := (hM b).mp hb
    have hmat : ((P * D * P⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (t ∘ Equiv.swap i j) := by
      rw [hP]
      exact coe_permSL_conj hD (Equiv.swap i j)
    have hDp' : (P * D * P⁻¹) ^ p = 1 :=
      pow_eq_one_of_pow_diagonal hmat fun k => pow_eq_one_of_diagonal hD hDp _
    refine (hM _).mpr ⟨P * D * P⁻¹, ⟨t ∘ Equiv.swap i j, hmat⟩, hDp', ?_⟩
    rw [hg, ← map_inv, ← map_mul, ← map_mul]
    rw [show (φ P * φ D) * (φ P)⁻¹ = φ (P * D * P⁻¹) from by
      simp only [map_mul, map_inv]]
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · exact hkey b
  · intro hb
    have h1 := hkey (g * b * g⁻¹) hb
    have h2 : g * (g * b * g⁻¹) * g⁻¹ = b := by
      calc g * (g * b * g⁻¹) * g⁻¹ = (g * g) * b * (g⁻¹ * g⁻¹) := by group
        _ = b := by simp [hgg, hg_inv]
    rwa [h2] at h1

theorem isReflection_conj_permSL (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hpd : Nat.Coprime p d) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hM : IsDiagTorusModel p φ A) {i j : Fin d} (hij : i ≠ j) :
    GGIsReflection p (ggConjAut A (conj_permSL_mem_normalizer hM i j)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun f : MulAut L' => (f : L' → L')) fun f g h => by
      ext x
      exact congrFun h x
  haveI : Finite ↥A := Subtype.finite
  have hd0 : 0 < d := by omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (K := K) hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  set P : SpecialLinearGroup (Fin d) K := permSL (Equiv.swap i j) with hP
  set g : MulAut L' := MulAut.conj (φ P) with hg
  have hPP : P⁻¹ = P := by rw [hP, permSL_inv, Equiv.swap_inv]
  have hginv : g⁻¹ = g := by rw [hg, ← map_inv, ← map_inv, hPP]
  have hgg : g * g = 1 := by
    nth_rewrite 2 [hginv.symm]
    exact mul_inv_cancel g
  set hN : g ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    conj_permSL_mem_normalizer hM i j with _hNdef
  set f : MulAut ↥A := ggConjAut A hN with hf
  have hf_apply : ∀ b : ↥A, ((f b : ↥A) : MulAut L') = g * (b : MulAut L') * g⁻¹ :=
    fun b => ggConjAut_apply A hN b
  have hf_inv_apply : ∀ b : ↥A, (((f b)⁻¹ : ↥A) : MulAut L') =
      g * (b : MulAut L')⁻¹ * g⁻¹ := by
    intro b
    rw [Subgroup.coe_inv, hf_apply b]
    group
  have hf2' : ggConjAut A hN ^ 2 = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_pow_apply A hN 2 b, pow_two, hgg]
    simp
  have hf2 : f ^ 2 = 1 := by rw [hf]; exact hf2'
  set t₁ : Fin d → K := ggPairVec i j ζ with ht₁
  have ht₁0 : ∀ k, t₁ k ≠ 0 := by
    intro k
    rw [ht₁, ggPairVec_apply]
    split_ifs <;> simp [hζ0]
  have ht₁p : ∀ k, t₁ k ^ p = 1 := fun k => by
    rw [ht₁]
    exact pow_ggPairVec hζ.pow_eq_one k
  have hprod₁ : ∏ k, t₁ k = 1 := by
    rw [ht₁]
    exact prod_ggPairVec ζ hζ0
  set D₁ : SpecialLinearGroup (Fin d) K :=
    ⟨diagonal t₁, by rw [Matrix.det_diagonal]; exact hprod₁⟩ with _hD₁
  have hD₁mat : (D₁ : Matrix (Fin d) (Fin d) K) = diagonal t₁ := rfl
  have hD₁p : D₁ ^ p = 1 := pow_eq_one_of_pow_diagonal hD₁mat ht₁p
  have ht₁i : t₁ i = ζ := by
    rw [ht₁, ggPairVec_apply, ite_eq_left rfl, ite_eq_right hij]
    simp
  have ht₁j : t₁ j = ζ⁻¹ := by
    rw [ht₁, ggPairVec_apply, ite_eq_right hij.symm, ite_eq_left rfl]
    simp
  set a₁ : ↥A := ⟨MulAut.conj (φ D₁), (hM _).mpr ⟨D₁, ⟨t₁, hD₁mat⟩, hD₁p, rfl⟩⟩ with _ha₁
  have ha₁coe : (a₁ : MulAut L') = MulAut.conj (φ D₁) := rfl
  have ha₁p : a₁ ^ p = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha₁coe, ← map_pow, ← map_pow, hD₁p, map_one,
      map_one]
  have hAc : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    obtain ⟨D, ⟨t, hD⟩, -, haD⟩ := (hM (a : MulAut L')).mp a.2
    obtain ⟨D', ⟨u, hD'⟩, -, hbD⟩ := (hM (b : MulAut L')).mp b.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, haD, hbD]
    simp only [← map_mul]
    rw [commute_of_diagonal hD hD']
  have hδ : ∀ a : ↥A, ∃ e : ℕ, a * (f a)⁻¹ = a₁ ^ e := by
    intro a
    obtain ⟨D, ⟨t, hD⟩, hDp, haD⟩ := (hM (a : MulAut L')).mp a.2
    have ht : ∀ k, t k ^ p = 1 := fun k => pow_eq_one_of_diagonal hD hDp k
    have ht0 : ∀ k, t k ≠ 0 := fun k => diag_entry_ne_zero hD k
    set E : SpecialLinearGroup (Fin d) K := D * (P * D * P⁻¹)⁻¹ with hE
    have hEmat : (E : Matrix (Fin d) (Fin d) K) =
        diagonal (ggPairVec i j (t i * (t j)⁻¹)) := by
      have hPDPmat : ((P * D * P⁻¹ : SpecialLinearGroup (Fin d) K) :
          Matrix (Fin d) (Fin d) K) = diagonal (t ∘ Equiv.swap i j) := by
        rw [hP]
        exact coe_permSL_conj hD (Equiv.swap i j)
      rw [hE, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hPDPmat, hD,
        diagonal_mul_diagonal]
      simp only [Function.comp_apply]
      rw [mul_inv_comp_swap ht0 hij]
    have hδcoe : (((a * (f a)⁻¹ : ↥A) : MulAut L')) = MulAut.conj (φ E) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hf_apply a, haD, hg, hE]
      simp only [map_mul, map_inv]
    have hμp : (t i * (t j)⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, ht i, ht j, inv_one, one_mul]
    obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hμp
    have hEeq : E = D₁ ^ e := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, hD₁mat, diagonal_pow, hEmat]
      congr 1
      rw [ht₁, ← he]
      exact (ggPairVec_pow i j ζ e).symm
    refine ⟨e, Subtype.ext ?_⟩
    rw [hδcoe, hEeq, Subgroup.coe_pow, ha₁coe, ← map_pow, ← map_pow]
  set E₁ : SpecialLinearGroup (Fin d) K := D₁ * (P * D₁ * P⁻¹)⁻¹ with hE₁
  have hE₁mat : (E₁ : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec i j (ζ ^ 2)) := by
    have hPDPmat : ((P * D₁ * P⁻¹ : SpecialLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (t₁ ∘ Equiv.swap i j) := by
      rw [hP]
      exact coe_permSL_conj hD₁mat (Equiv.swap i j)
    rw [hE₁, Matrix.SpecialLinearGroup.coe_mul, coe_inv_SL_of_diagonal hPDPmat, hD₁mat,
      diagonal_mul_diagonal]
    simp only [Function.comp_apply]
    rw [mul_inv_comp_swap ht₁0 hij]
    congr 1
    rw [ht₁i, ht₁j, inv_inv, ← pow_two]
  have hδ₁coe : (((a₁ * (f a₁)⁻¹ : ↥A) : MulAut L')) = MulAut.conj (φ E₁) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hf_apply a₁, ha₁coe, hg, hE₁]
    simp only [map_mul, map_inv]
  have h₁ : a₁ * (f a₁)⁻¹ ≠ 1 := by
    intro hcontra
    have hconj1 : MulAut.conj (φ E₁) = 1 := by
      rw [← hδ₁coe, hcontra]
      rfl
    have hact : GGActsBy φ (MulAut.conj (φ E₁)) E₁ := ggActsBy_conj_phi φ E₁
    rw [hconj1] at hact
    have hdiag1 : ((1 : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        diagonal (fun _ : Fin d => (1 : K)) := by
      rw [Matrix.SpecialLinearGroup.coe_one, diagonal_one]
    have hζ2p : (ζ ^ 2) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hteq : ggPairVec i j (ζ ^ 2) = fun _ : Fin d => (1 : K) :=
      GGActsBy.diag_eq hφker hpd hd0 hE₁mat hdiag1
        (fun m => pow_ggPairVec hζ2p m) (fun m => by simp) hact GGActsBy.one
    have h2 : ζ ^ 2 = 1 := by
      have h := congrFun hteq i
      rw [ggPairVec_apply] at h
      simpa [hij] using h
    have h2' : ζ * ζ = 1 := by rw [← pow_two]; exact h2
    exact hζinv (inv_eq_of_mul_eq_one_right h2').symm
  exact ⟨hf2, card_fix_mul_of_le_zpowers hp hAc f ha₁p hδ h₁⟩

omit [CharP K 2] in
private theorem mem_pair_of_swap_comp_eq (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {i j k l : Fin d} (hij : i ≠ j)
    (H1 : ∀ t : Fin d → K, (∀ x, t x ^ p = 1) → ∏ x, t x = 1 →
      t ∘ Equiv.swap i j = t ∘ Equiv.swap k l) : i ∈ ({k, l} : Finset (Fin d)) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  by_contra hi
  have hik : i ≠ k := fun h' => hi (by simp [h'])
  have hil : i ≠ l := fun h' => hi (by simp [h'])
  have ht : ∀ x, ggPairVec i k ζ x ^ p = 1 := fun x => pow_ggPairVec hζ.pow_eq_one x
  have hprod : ∏ x, ggPairVec i k ζ x = 1 := prod_ggPairVec ζ hζ0
  have heval := congrFun (H1 (ggPairVec i k ζ) ht hprod) i
  rw [Function.comp_apply, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hik hil] at heval
  have hti : ggPairVec i k ζ i = ζ := by
    rw [ggPairVec_apply, ite_eq_left rfl, ite_eq_right hik, mul_one]
  have htj : ggPairVec i k ζ j = ζ := heval.trans hti
  rw [ggPairVec_apply, ite_eq_right (Ne.symm hij), one_mul] at htj
  by_cases hjk : j = k
  · rw [ite_eq_left hjk] at htj
    exact hζinv htj.symm
  · rw [ite_eq_right hjk] at htj
    exact hζ1 htj.symm

omit [Finite L'] in
theorem pair_eq_of_ggConjAut_eq (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hpd : Nat.Coprime p d) (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hM : IsDiagTorusModel p φ A) {i j k l : Fin d} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ggConjAut A (conj_permSL_mem_normalizer hM i j) =
      ggConjAut A (conj_permSL_mem_normalizer hM k l)) :
    ({i, j} : Finset (Fin d)) = {k, l} := by
  have H1 : ∀ t : Fin d → K, (∀ x, t x ^ p = 1) → ∏ x, t x = 1 →
      t ∘ Equiv.swap i j = t ∘ Equiv.swap k l := by
    intro t ht hprod
    let D : SpecialLinearGroup (Fin d) K :=
      ⟨diagonal t, by rw [Matrix.det_diagonal]; exact hprod⟩
    have hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t := rfl
    have hDp : D ^ p = 1 := pow_eq_one_of_pow_diagonal hD ht
    have hDmem : MulAut.conj (φ D) ∈ A := (hM _).mpr ⟨D, ⟨t, hD⟩, hDp, rfl⟩
    let b : ↥A := ⟨MulAut.conj (φ D), hDmem⟩
    have hb : (b : MulAut L') = MulAut.conj (φ D) := rfl
    have hh := DFunLike.congr_fun h b
    have hEq : MulAut.conj (φ (permSL (Equiv.swap i j))) * MulAut.conj (φ D) *
          (MulAut.conj (φ (permSL (Equiv.swap i j))))⁻¹ =
        MulAut.conj (φ (permSL (Equiv.swap k l))) * MulAut.conj (φ D) *
          (MulAut.conj (φ (permSL (Equiv.swap k l))))⁻¹ := by
      have hval := congrArg (fun x : ↥A => (x : MulAut L')) hh
      rw [ggConjAut_apply, ggConjAut_apply] at hval
      simpa only [hb] using hval
    have haL := (ggActsBy_conj_phi φ D).conj (permSL (Equiv.swap i j))
    have haR : GGActsBy φ (MulAut.conj (φ (permSL (Equiv.swap i j))) *
          MulAut.conj (φ D) *
          (MulAut.conj (φ (permSL (Equiv.swap i j))))⁻¹)
        (permSL (Equiv.swap k l) * D * (permSL (Equiv.swap k l))⁻¹) := by
      rw [hEq]
      exact (ggActsBy_conj_phi φ D).conj (permSL (Equiv.swap k l))
    exact GGActsBy.diag_eq hφker hpd (Fin.pos i)
      (coe_permSL_conj (D := D) (t := t) hD (Equiv.swap i j))
      (coe_permSL_conj (D := D) (t := t) hD (Equiv.swap k l))
      (fun x => ht (Equiv.swap i j x)) (fun x => ht (Equiv.swap k l x)) haL haR
  have hi := mem_pair_of_swap_comp_eq hp hp2 hpK hij H1
  have hj : j ∈ ({k, l} : Finset (Fin d)) :=
    mem_pair_of_swap_comp_eq hp hp2 hpK hij.symm fun t ht hprod => by
      rw [Equiv.swap_comm j i]
      exact H1 t ht hprod
  have hsub : ({i, j} : Finset (Fin d)) ⊆ {k, l} := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hi
    · exact hj
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hkl, Finset.card_pair hij])
end Pair

end Model

end CFSG.StandardType.TypeA

end
