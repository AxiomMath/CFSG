module

public import CFSG.RankThree.SteinbergR3ECAEvenD4Centralizer

public section

namespace CFSG.RankThree.OddD4Centralizer

open QuadraticMap Module
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.EvenD4Centralizer
open scoped Pointwise

section Reflections

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem reflect_mul_comm {a b : V} (hab : polar Q a b = 0) :
    reflect Q a * reflect Q b = reflect Q b * reflect Q a := by
  by_cases ha : Q a = 0
  · rw [reflect_of_map_eq_zero ha, one_mul, mul_one]
  by_cases hb : Q b = 0
  · rw [reflect_of_map_eq_zero hb, one_mul, mul_one]
  have hba : polar Q b a = 0 := by rw [polar_comm, hab]
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, reflect_apply ha, reflect_apply hb, polar_sub_right,
    polar_smul_right, hab, hba, smul_eq_mul, mul_zero, sub_zero]
  abel

theorem reflect_mul_reflect_apply {u v : V} (hu : Q u = 1) (hv : Q v = 1)
    (huv : polar Q u v = 0) (x : V) :
    (reflect Q u * reflect Q v) x = x - polar Q u x • u - polar Q v x • v := by
  rw [LinearEquiv.mul_apply, reflect_apply (by rw [hu]; exact one_ne_zero),
    reflect_apply (by rw [hv]; exact one_ne_zero), hu, hv, div_one, div_one, polar_sub_right,
    polar_smul_right, huv, smul_zero, sub_zero]
  abel

theorem reflect_map_isometry (r : V ≃ₗ[K] V') (hr : ∀ x, Q' (r x) = Q x) (w x : V) :
    reflect Q' (r w) (r x) = r (reflect Q w x) := by
  by_cases hw : Q w = 0
  · rw [reflect_of_map_eq_zero hw, reflect_of_map_eq_zero (by rw [hr, hw])]
    rfl
  · rw [reflect_apply hw, reflect_apply (by rwa [hr]), polar_map_isometry r hr, hr, map_sub,
      map_smul]

end Reflections

section Embedding

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  {ι : (Fin m ⊕ Fin m → K) →ₗ[K] V}

theorem polar_map_linearIsometry (hι : ∀ c, Q (ι c) = quadPlus m K c)
    (c c' : Fin m ⊕ Fin m → K) : polar Q (ι c) (ι c') = polar (quadPlus m K) c c' := by
  rw [polar, polar, ← map_add, hι, hι, hι]

theorem injective_of_linearIsometry (hι : ∀ c, Q (ι c) = quadPlus m K c) :
    Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  refine (nondegenerate_polarBilin_quadPlus m K).1 c fun c' => ?_
  rw [polarBilin_apply_apply, ← polar_map_linearIsometry hι, LinearMap.mem_ker.mp hc,
    polar_zero_left]

theorem card_singular_le_range (hι : ∀ c, Q (ι c) = quadPlus m K c) (k : ℕ) :
    Nat.card {L // L ∈ singularSubspaces Q k ∧ L ≤ LinearMap.range ι} =
      Nat.card (singularSubspaces (quadPlus m K) k) := by
  have hinj := injective_of_linearIsometry hι
  have hmap : ∀ L : Submodule K (Fin m ⊕ Fin m → K),
      finrank K (L.map ι) = finrank K L := fun L =>
    (Submodule.equivMapOfInjective ι hinj L).finrank_eq.symm
  have hback : ∀ L : Submodule K V, L ≤ LinearMap.range ι → (L.comap ι).map ι = L := fun L hL =>
    (Submodule.map_comap_eq ι L).trans (inf_eq_right.mpr hL)
  symm
  refine Nat.card_congr
    { toFun := fun L => ⟨L.1.map ι, ⟨by rw [hmap]; exact L.2.1, ?_⟩, LinearMap.map_le_range⟩
      invFun := fun L => ⟨L.1.comap ι, ⟨?_, fun c hc => by rw [← hι]; exact L.2.1.2 _ hc⟩⟩
      left_inv := fun L => Subtype.ext (Submodule.comap_map_eq_of_injective hinj _)
      right_inv := fun L => Subtype.ext (hback L.1 L.2.2) }
  · rintro _ ⟨c, hc, rfl⟩
    rw [hι]
    exact L.2.2 c hc
  · rw [← hmap, hback L.1 L.2.2]
    exact L.2.1.1

theorem finrank_le_of_singular_le_range (hι : ∀ c, Q (ι c) = quadPlus m K c)
    {S : Submodule K V} (hS : S ≤ LinearMap.range ι) (hSs : ∀ x ∈ S, Q x = 0) :
    finrank K S ≤ m := by
  have h1 : (S.comap ι).map ι = S := (Submodule.map_comap_eq ι S).trans (inf_eq_right.mpr hS)
  have h2 := two_mul_finrank_le_of_singular (nondegenerate_polarBilin_quadPlus m K)
    (M := S.comap ι) fun c hc => by rw [← hι]; exact hSs _ hc
  have h3 : finrank K ((S.comap ι).map ι) = finrank K (S.comap ι) :=
    (Submodule.equivMapOfInjective ι (injective_of_linearIsometry hι) _).finrank_eq.symm
  rw [h1] at h3
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at h2
  omega

theorem quadPlus_hypCombination {P : Fin m → HypPair Q}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (c : Fin m ⊕ Fin m → K) :
    Q (Fintype.linearCombination K (Sum.elim (fun i => (P i).e) (fun i => (P i).f)) c) =
      quadPlus m K c := by
  rw [Fintype.linearCombination_apply, Fintype.sum_sum_type, quadPlus_apply]
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact map_sum_hyp hP (fun i => c (Sum.inl i)) (fun i => c (Sum.inr i))

end Embedding

section Involution

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {g : V ≃ₗ[K] V}
  {A B : Submodule K V}

theorem map_eq_of_eq_smul {M : Submodule K V} {c : K} (hc : c ≠ 0)
    (h : ∀ x ∈ M, g x = c • x) : M.map (g : V →ₗ[K] V) = M := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, h x hx]
    exact M.smul_mem c hx
  · intro hy
    refine ⟨c⁻¹ • y, M.smul_mem _ hy, ?_⟩
    rw [LinearEquiv.coe_coe, map_smul, h y hy, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem apply_eq_smul_of_mem_range {ι : Type*} [Fintype ι] {w : ι → V} {c : K}
    (hw : ∀ j, g (w j) = c • w j) {x : V}
    (hx : x ∈ LinearMap.range (Fintype.linearCombination K w)) : g x = c • x := by
  obtain ⟨d, rfl⟩ := hx
  rw [Fintype.linearCombination_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hw, smul_comm]

variable (h2 : (2 : K) ≠ 0) (hA : ∀ x ∈ A, g x = -x) (hB : ∀ x ∈ B, g x = x)
include h2 hA hB

theorem inf_eq_bot_of_eigen : A ⊓ B = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxA, hxB⟩
  have h : (2 : K) • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← (hA x hxA).symm.trans (hB x hxB)]
    exact neg_add_cancel x
  exact (smul_eq_zero.mp h).resolve_left h2

theorem polar_eq_zero_of_eigen {Q : QuadraticForm K V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    polar Q x y = 0 := by
  have h := polar_map_of_mem hg x y
  rw [hA x hx, hB y hy, polar_neg_left] at h
  have h' : (2 : K) * polar Q x y = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

variable (hAB : A ⊔ B = ⊤)
include hAB

theorem eq_sup_inf_of_map {M : Submodule K V} (hM : ∀ x ∈ M, g x ∈ M) :
    M = (M ⊓ A) ⊔ (M ⊓ B) := by
  refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left inf_le_left)
  have hx' : x ∈ A ⊔ B := by rw [hAB]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
  have hbM : b ∈ M := by
    have h := M.add_mem hx (hM _ hx)
    rw [map_add, hA a ha, hB b hb] at h
    have hb2 : (2 : K)⁻¹ • ((a + b) + (-a + b)) = b := by
      rw [show (a + b) + (-a + b) = (2 : K) • b by rw [two_smul]; abel, smul_smul,
        inv_mul_cancel₀ h2, one_smul]
    rw [← hb2]
    exact M.smul_mem _ h
  have haM : a ∈ M := by
    have h := M.sub_mem hx hbM
    rwa [add_sub_cancel_right] at h
  exact Submodule.add_mem_sup ⟨haM, ha⟩ ⟨hbM, hb⟩

theorem card_fixed_lines [FiniteDimensional K V] [Finite (Submodule K V)]
    {Q : QuadraticForm K V} :
    Nat.card {L // L ∈ singularSubspaces Q 1 ∧ L.map (g : V →ₗ[K] V) = L} =
      Nat.card {L // L ∈ singularSubspaces Q 1 ∧ L ≤ A} +
        Nat.card {L // L ∈ singularSubspaces Q 1 ∧ L ≤ B} := by
  have hAB0 := inf_eq_bot_of_eigen h2 hA hB
  have e1 : ∀ p : Submodule K V → Prop, Nat.card {L // p L} = ({L | p L} : Set _).ncard :=
    fun p => Nat.card_coe_set_eq _
  have hd : Disjoint ({L | L ∈ singularSubspaces Q 1 ∧ L ≤ A} : Set (Submodule K V))
      {L | L ∈ singularSubspaces Q 1 ∧ L ≤ B} := by
    refine Set.disjoint_left.2 fun L h1 h2' => ?_
    have hL : L ≤ A ⊓ B := le_inf h1.2 h2'.2
    rw [hAB0, le_bot_iff] at hL
    have := h1.1.1
    rw [hL, finrank_bot] at this
    exact zero_ne_one this
  rw [e1, e1, e1, ← Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
  congr 1
  ext L
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hL, hLg⟩
    have hM : ∀ x ∈ L, g x ∈ L := fun x hx => by
      rw [← hLg]
      exact ⟨x, hx, rfl⟩
    have hdec := eq_sup_inf_of_map h2 hA hB hAB hM
    by_cases hLA : L ⊓ A = ⊥
    · rw [hLA, bot_sup_eq] at hdec
      exact Or.inr ⟨hL, hdec ▸ inf_le_right⟩
    · have hle : L ⊓ A = L := by
        refine Submodule.eq_of_le_of_finrank_le inf_le_left ?_
        rw [hL.1]
        exact Nat.one_le_iff_ne_zero.mpr fun h0 => hLA (Submodule.finrank_eq_zero.mp h0)
      exact Or.inl ⟨hL, hle ▸ inf_le_right⟩
  · rintro (⟨hL, hLA⟩ | ⟨hL, hLB⟩)
    · exact ⟨hL, map_eq_of_eq_smul (neg_ne_zero.mpr one_ne_zero) fun x hx => by
        rw [hA x (hLA hx), neg_one_smul]⟩
    · exact ⟨hL, map_eq_of_eq_smul one_ne_zero fun x hx => by rw [hB x (hLB hx), one_smul]⟩

theorem card_fixed_sum [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a b : ℕ}
    (ha : ∀ S : Submodule K V, S ≤ A → (∀ x ∈ S, Q x = 0) → finrank K S ≤ a)
    (hb : ∀ S : Submodule K V, S ≤ B → (∀ x ∈ S, Q x = 0) → finrank K S ≤ b) :
    Nat.card {M // M ∈ singularSubspaces Q (a + b) ∧ M.map (g : V →ₗ[K] V) = M} =
      Nat.card {L // L ∈ singularSubspaces Q a ∧ L ≤ A} *
        Nat.card {N // N ∈ singularSubspaces Q b ∧ N ≤ B} := by
  have hAB0 := inf_eq_bot_of_eigen h2 hA hB
  have hdisj : ∀ {S T : Submodule K V}, S ≤ A → T ≤ B → S ⊓ T = ⊥ := fun hS hT =>
    le_bot_iff.mp (hAB0 ▸ inf_le_inf hS hT)
  have hdim : ∀ {S T : Submodule K V}, S ≤ A → T ≤ B →
      finrank K ↥(S ⊔ T) = finrank K S + finrank K T := fun {S T} hS hT => by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S T
    rw [hdisj hS hT, finrank_bot, add_zero] at h
    exact h
  have hparts : ∀ M : Submodule K V, M ∈ singularSubspaces Q (a + b) →
      M.map (g : V →ₗ[K] V) = M →
        M = (M ⊓ A) ⊔ (M ⊓ B) ∧ finrank K ↥(M ⊓ A) = a ∧ finrank K ↥(M ⊓ B) = b := by
    intro M hM hMg
    have hM' : ∀ x ∈ M, g x ∈ M := fun x hx => by
      rw [← hMg]
      exact ⟨x, hx, rfl⟩
    have hdec := eq_sup_inf_of_map h2 hA hB hAB hM'
    have hsum := hdim (S := M ⊓ A) (T := M ⊓ B) inf_le_right inf_le_right
    rw [← hdec, hM.1] at hsum
    have h1 := ha _ inf_le_right fun x hx => hM.2 x hx.1
    have h2' := hb _ inf_le_right fun x hx => hM.2 x hx.1
    exact ⟨hdec, by omega, by omega⟩
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun M => (⟨M.1 ⊓ A, ⟨(hparts M.1 M.2.1 M.2.2).2.1, fun x hx => M.2.1.2 x hx.1⟩,
        inf_le_right⟩, ⟨M.1 ⊓ B, ⟨(hparts M.1 M.2.1 M.2.2).2.2, fun x hx => M.2.1.2 x hx.1⟩,
        inf_le_right⟩)
      invFun := fun LN => ⟨LN.1.1 ⊔ LN.2.1, ⟨?_, ?_⟩, ?_⟩
      left_inv := fun M => Subtype.ext (hparts M.1 M.2.1 M.2.2).1.symm
      right_inv := fun LN => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) }
  · rw [hdim LN.1.2.2 LN.2.2.2, LN.1.2.1.1, LN.2.2.1.1]
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [QuadraticMap.map_add Q, LN.1.2.1.2 y hy, LN.2.2.1.2 z hz,
      polar_eq_zero_of_eigen h2 hA hB hg (LN.1.2.2 hy) (LN.2.2.2 hz), add_zero, add_zero]
  · rw [Submodule.map_sup, map_eq_of_eq_smul (neg_ne_zero.mpr one_ne_zero) fun x hx => by
        rw [hA x (LN.1.2.2 hx), neg_one_smul],
      map_eq_of_eq_smul one_ne_zero fun x hx => by rw [hB x (LN.2.2.2 hx), one_smul]]
  · change (LN.1.1 ⊔ LN.2.1) ⊓ A = LN.1.1
    rw [sup_inf_assoc_of_le _ LN.1.2.2, inf_comm, hdisj le_rfl LN.2.2.2, sup_bot_eq]
  · change (LN.1.1 ⊔ LN.2.1) ⊓ B = LN.2.1
    rw [sup_comm, sup_inf_assoc_of_le _ LN.2.2.2, hdisj LN.1.2.2 le_rfl, sup_bot_eq]

end Involution

section Counts

variable {K : Type} [Field K] [Finite K]

theorem card_singular_one_one : Nat.card (singularSubspaces (quadPlus 1 K) 1) = 2 := by
  have h := card_singularSubspaces_top (K := K) (r := 1) le_rfl
  simp only [Nat.sub_self, Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.prod_empty,
    mul_one] at h
  exact_mod_cast h

theorem card_singular_three_one :
    Nat.card (singularSubspaces (quadPlus 3 K) 1) =
      (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  have h := card_singularSubspaces (K := K) (r := 3) (k := 1) (by norm_num)
  have hq : (1 : ℚ) < Nat.card K := by exact_mod_cast Finite.one_lt_card
  simp only [Finset.range_one, Finset.prod_singleton, Finset.Icc_self, pow_one, Nat.sub_zero,
    show 3 - 1 = 2 from rfl] at h
  have h' : ((Nat.card (singularSubspaces (quadPlus 3 K) 1) : ℕ) : ℚ) =
      (((Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) : ℕ) : ℚ) := by
    rw [h, div_eq_iff (by linarith)]
    push_cast
    ring
  exact_mod_cast h'

theorem card_singular_three_three :
    Nat.card (singularSubspaces (quadPlus 3 K) 3) =
      2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  have h := card_singularSubspaces_top (K := K) (r := 3) (by norm_num)
  rw [show Finset.Icc 1 (3 - 1) = {1, 2} by decide, Finset.prod_pair (by norm_num), pow_one] at h
  have h' : ((Nat.card (singularSubspaces (quadPlus 3 K) 3) : ℕ) : ℚ) =
      ((2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) : ℕ) : ℚ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast h'

end Counts

section Model

variable {K : Type} [Field K]

theorem quadPlus_single_add_single {r : ℕ} (i : Fin r) :
    quadPlus r K (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1) = 1 := by
  rw [quadPlus_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem polar_single_add_single {r : ℕ} (i : Fin r) (x : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1) x =
      x (Sum.inr i) + x (Sum.inl i) := by
  rw [polar_add_left, polar_single_inl_quadPlus, polar_single_inr_quadPlus]

theorem twoReflection_apply (x : Fin 4 ⊕ Fin 4 → K) :
    (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x =
      x - (x (Sum.inr 0) + x (Sum.inl 0)) • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) -
        (x (Sum.inr 1) + x (Sum.inl 1)) •
          (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) := by
  rw [reflect_mul_reflect_apply (quadPlus_single_add_single 0) (quadPlus_single_add_single 1)
    (by rw [polar_single_add_single]; simp), polar_single_add_single, polar_single_add_single]

theorem twoReflection_mem_elementary :
    reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) ∈
        orthElementaryGroup (quadPlus 4 K) := by
  have hne : ∀ i : Fin 4,
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 : Fin 4 ⊕ Fin 4 → K) ≠ 0 :=
    fun i h0 => by
      have h := quadPlus_single_add_single (K := K) i
      rw [h0, QuadraticMap.map_zero] at h
      exact zero_ne_one h
  obtain ⟨h, hh, hhu⟩ := (orthogonal_norm_shell_transitive (nondegenerate_polarBilin_quadPlus 4 K)
    ⟨flag 4 K 2, (flag_mem_singularSubspaces (by norm_num)).1,
      (flag_mem_singularSubspaces (by norm_num)).2⟩).1 _ _ (hne 0) (hne 1)
        (by rw [quadPlus_single_add_single, quadPlus_single_add_single])
  have heq : reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) =
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) * h *
          (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1))⁻¹ *
            h⁻¹ := by
    rw [← hhu, ← reflect_conj (orthElementaryGroup_le _ hh), reflect_inv]
    group
  rw [heq]
  exact mul_mem (conj_mem_elementaryGroup (reflect_mem_orthogonalGroup _ _) hh) (inv_mem hh)

theorem twoReflection_mul_self :
    reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) *
        (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = 1 := by
  have hc := reflect_mul_comm (Q := quadPlus 4 K)
    (a := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
    (b := Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)
    (by rw [polar_single_add_single]; simp)
  rw [mul_assoc, ← mul_assoc (reflect _ _) (reflect _ _) (reflect _ _), ← hc, mul_assoc,
    reflect_mul_self, mul_one, reflect_mul_self]

theorem reflect_sub_commute_twoReflection :
    reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1) *
      (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) =
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1) := by
  have h1 : polar (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1)
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) = 0 := by
    rw [polar_single_sub_single]; simp
  have h2 : polar (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1)
      (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) = 0 := by
    rw [polar_single_sub_single]; simp
  rw [← mul_assoc, reflect_mul_comm h1, mul_assoc, reflect_mul_comm h2, ← mul_assoc]

theorem exists_line_not_fixed_twoReflection (h2 : (2 : K) ≠ 0) :
    ∃ L ∈ singularSubspaces (quadPlus 4 K) 1,
      L.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
          (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
            (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ≠ L := by
  set x : Fin 4 ⊕ Fin 4 → K := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 +
    (Pi.single (Sum.inl 2) 1 - Pi.single (Sum.inr 2) 1) with hx
  have hx0 : x ≠ 0 := fun h0 => by
    have h := congrFun h0 (Sum.inl 0)
    simp [hx] at h
  have hQx : quadPlus 4 K x = 0 := by
    simp [hx, quadPlus_apply, Fin.sum_univ_four]
  refine ⟨K ∙ x, ⟨finrank_span_singleton hx0, fun y hy => ?_⟩, fun hL => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_smul, hQx, smul_zero]
  · have hgx : (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x ∈ K ∙ x := by
      rw [← hL]
      exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgx
    have e0 := congrFun hc (Sum.inl 0)
    have e2 := congrFun hc (Sum.inl 2)
    rw [twoReflection_apply] at e0 e2
    simp [hx] at e0 e2
    apply h2
    linear_combination e0 - e2

theorem line_fixed_twoReflection :
    (K ∙ (Pi.single (Sum.inl 2) 1 : Fin 4 ⊕ Fin 4 → K)) ∈ singularSubspaces (quadPlus 4 K) 1 ∧
      (K ∙ (Pi.single (Sum.inl 2) 1 : Fin 4 ⊕ Fin 4 → K)).map
        ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
              (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        K ∙ (Pi.single (Sum.inl 2) 1 : Fin 4 ⊕ Fin 4 → K) := by
  refine ⟨⟨finrank_span_singleton (by simp), fun y hy => ?_⟩, ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [QuadraticMap.map_smul, quadPlus_single, smul_zero]
  · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, twoReflection_apply]
    simp

theorem not_map_eq_twoReflection (hsq : ¬ IsSquare (-1 : K))
    {M : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hM : M ∈ singularSubspaces (quadPlus 4 K) 4) :
    M.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
          (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ≠ M := by
  intro hMg
  have horth : ∀ x ∈ M, polar (quadPlus 4 K) x
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) = 0 := by
    intro x hx
    have hgx : (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x ∈ M := by
      rw [← hMg]
      exact ⟨x, hx, rfl⟩
    have hy := M.sub_mem hx hgx
    rw [twoReflection_apply, sub_sub, sub_sub_cancel] at hy
    have h0 := hM.2 _ hy
    have hB01 : polar (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
        (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) = 0 := by
      rw [polar_single_add_single]; simp
    rw [QuadraticMap.map_add (quadPlus 4 K), QuadraticMap.map_smul, QuadraticMap.map_smul,
      quadPlus_single_add_single, quadPlus_single_add_single, polar_smul_left, polar_smul_right,
      hB01] at h0
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at h0
    rw [polar_comm, polar_single_add_single]
    by_contra hα
    apply hsq
    refine ⟨(x (Sum.inr 1) + x (Sum.inl 1)) / (x (Sum.inr 0) + x (Sum.inl 0)), ?_⟩
    field_simp
    linear_combination -h0
  have hu := mem_of_forall_polar_eq_zero (nondegenerate_polarBilin_quadPlus 4 K) hM.2
    (by rw [hM.1, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
    horth
  have h1 := hM.2 _ hu
  rw [quadPlus_single_add_single] at h1
  exact one_ne_zero h1

theorem twoReflection_apply_comb (α β : K) :
    (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1))
        (α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
          β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) =
      -(α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
        β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) := by
  have c0 : (α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
      β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) : Fin 4 ⊕ Fin 4 → K) (Sum.inr 0) +
      (α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
        β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) : Fin 4 ⊕ Fin 4 → K)
          (Sum.inl 0) = α + α := by
    simp
  have c1 : (α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
      β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) : Fin 4 ⊕ Fin 4 → K) (Sum.inr 1) +
      (α • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
        β • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) : Fin 4 ⊕ Fin 4 → K)
          (Sum.inl 1) = β + β := by
    simp
  rw [twoReflection_apply, c0, c1]
  module

theorem twoReflection_apply_of_perp {x : Fin 4 ⊕ Fin 4 → K}
    (h0 : x (Sum.inr 0) + x (Sum.inl 0) = 0) (h1 : x (Sum.inr 1) + x (Sum.inl 1) = 0) :
    (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x = x := by
  rw [twoReflection_apply, h0, h1, zero_smul, zero_smul, sub_zero, sub_zero]

theorem card_fixed_twoReflection_of_sq [Finite K] (h2 : (2 : K) ≠ 0) {i : K}
    (hi : i * i = -1) :
    Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
              (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} =
        2 + (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) ∧
      Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
              (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        2 * (2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1)) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨ε, hε⟩ : ∃ ε : K, 4 * ε = 1 := ⟨(4 : K)⁻¹, mul_inv_cancel₀ h4⟩
  obtain ⟨Pp, hPpe, hPpf⟩ : ∃ P : HypPair (quadPlus 4 K),
      P.e = (1 : K) • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
        i • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) ∧
      P.f = ε • (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) +
        (-(ε * i)) • (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) := by
    refine ⟨⟨_, _, ?_, ?_, ?_⟩, rfl, rfl⟩
    · simp [quadPlus_apply, Fin.sum_univ_four]
      linear_combination hi
    · simp [quadPlus_apply, Fin.sum_univ_four]
      linear_combination ε ^ 2 * hi
    · simp [polar_quadPlus, Fin.sum_univ_four, quadPlus_single]
      linear_combination (-2 * ε) * hi + hε
  obtain ⟨Pw, hPwe, hPwf⟩ : ∃ P : HypPair (quadPlus 4 K),
      P.e = (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1) +
        i • (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inr 1) 1) ∧
      P.f = (-ε) • (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 0) 1) +
        (ε * i) • (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inr 1) 1) := by
    refine ⟨⟨_, _, ?_, ?_, ?_⟩, rfl, rfl⟩
    · simp [quadPlus_apply, Fin.sum_univ_four]
      linear_combination -hi
    · simp [quadPlus_apply, Fin.sum_univ_four]
      linear_combination (-ε ^ 2) * hi
    · simp [polar_quadPlus, Fin.sum_univ_four, quadPlus_single]
      linear_combination (-2 * ε) * hi + hε
  have hw2 : Pw.Orth (plusPair K 2) := ⟨by simp [hPwe, plusPair_e, polar_quadPlus_single_inl],
    by simp [hPwe, plusPair_f, polar_quadPlus_single_inr],
    by simp [hPwf, plusPair_e, polar_quadPlus_single_inl],
    by simp [hPwf, plusPair_f, polar_quadPlus_single_inr]⟩
  have hw3 : Pw.Orth (plusPair K 3) := ⟨by simp [hPwe, plusPair_e, polar_quadPlus_single_inl],
    by simp [hPwe, plusPair_f, polar_quadPlus_single_inr],
    by simp [hPwf, plusPair_e, polar_quadPlus_single_inl],
    by simp [hPwf, plusPair_f, polar_quadPlus_single_inr]⟩
  have h23 : (plusPair K (2 : Fin 4)).Orth (plusPair K 3) := plusPair_orth (by decide)
  have hPU : ∀ a b : Fin 3, a ≠ b → (![Pw, plusPair K 2, plusPair K 3] a).Orth
      (![Pw, plusPair K 2, plusPair K 3] b) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | exact absurd rfl hab
      | exact hw2 | exact hw3 | exact h23 | exact hw2.symm | exact hw3.symm | exact h23.symm
  have hιP := quadPlus_hypCombination (P := fun _ : Fin 1 => Pp)
    (fun a b hab => absurd (Subsingleton.elim a b) hab)
  have hιU := quadPlus_hypCombination hPU
  have hA : ∀ x ∈ LinearMap.range (Fintype.linearCombination K
      (Sum.elim (fun _ : Fin 1 => Pp.e) (fun _ : Fin 1 => Pp.f))),
      (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x = -x := by
    intro x hx
    rw [apply_eq_smul_of_mem_range (c := -1) (fun j => ?_) hx, neg_one_smul]
    rcases j with j | j
    · rw [Sum.elim_inl, hPpe, twoReflection_apply_comb, neg_one_smul]
    · rw [Sum.elim_inr, hPpf, twoReflection_apply_comb, neg_one_smul]
  have hB : ∀ x ∈ LinearMap.range (Fintype.linearCombination K
      (Sum.elim (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).e)
        (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).f))),
      (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x = x := by
    intro x hx
    rw [apply_eq_smul_of_mem_range (c := 1) (fun j => ?_) hx, one_smul]
    rw [one_smul]
    apply twoReflection_apply_of_perp
    all_goals rcases j with j | j <;> fin_cases j <;> simp [hPwe, hPwf, plusPair_e, plusPair_f]
  have hinjP := injective_of_linearIsometry hιP
  have hinjU := injective_of_linearIsometry hιU
  have hAB : LinearMap.range (Fintype.linearCombination K
      (Sum.elim (fun _ : Fin 1 => Pp.e) (fun _ : Fin 1 => Pp.f))) ⊔
      LinearMap.range (Fintype.linearCombination K
        (Sum.elim (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).e)
          (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).f))) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (Fintype.linearCombination K
        (Sum.elim (fun _ : Fin 1 => Pp.e) (fun _ : Fin 1 => Pp.f))))
      (LinearMap.range (Fintype.linearCombination K
        (Sum.elim (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).e)
          (fun j : Fin 3 => (![Pw, plusPair K 2, plusPair K 3] j).f))))
    rw [inf_eq_bot_of_eigen h2 hA hB, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinjP,
      LinearMap.finrank_range_of_inj hinjU] at h
    rw [h]
    simp [Module.finrank_fintype_fun_eq_card]
  have hg := orthElementaryGroup_le _ (twoReflection_mem_elementary (K := K))
  refine ⟨?_, ?_⟩
  · rw [card_fixed_lines h2 hA hB hAB, card_singular_le_range hιP, card_singular_le_range hιU,
      card_singular_one_one, card_singular_three_one]
  · have h := card_fixed_sum h2 hA hB hAB hg (a := 1) (b := 3)
      (fun S hS hSs => finrank_le_of_singular_le_range hιP hS hSs)
      (fun S hS hSs => finrank_le_of_singular_le_range hιU hS hSs)
    rw [card_singular_le_range hιP, card_singular_le_range hιU, card_singular_one_one,
      card_singular_three_three] at h
    exact h

theorem card_fixed_orbits_twoReflection_of_sq [Finite K] (h2 : (2 : K) ≠ 0) {i : K}
    (hi : i * i = -1) :
    Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) (flag 4 K 4) ∧
        M.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
              (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) ∧
      Nat.card {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K))
          (Xstar 4 K (by norm_num)) ∧
        M.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
            (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
              (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} =
        2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
  obtain ⟨-, hm⟩ := card_fixed_twoReflection_of_sq h2 hi
  have heq := card_fixed_orbit_flag_eq_Xstar (by norm_num)
    (quadPlus_single_sub_single (K := K) (0 : Fin 4)) twoReflection_mem_elementary
    reflect_sub_commute_twoReflection
  have hsum := ThreeFamily.card_fixed_maximal (K := K) (n := 4) (by norm_num)
    (reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1))
  omega

theorem not_map_eq_orbit_twoReflection (hsq : ¬ IsSquare (-1 : K))
    {Y M : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hY : Y ∈ singularSubspaces (quadPlus 4 K) 4)
    (hM : M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K)) Y) :
    M.map ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
        (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
          (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ≠ M := by
  obtain ⟨a, ha, rfl⟩ := mem_orbit_elementary.1 hM
  exact not_map_eq_twoReflection hsq
    (OrthogonalSplit.map_mem_singularSubspaces (orthElementaryGroup_le _ ha) hY)

end Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixDerived matrixProjectiveDerived matrixProjectiveImage matrixProjectiveProjection
    matrixLinearEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus projectivePointFamily projectivePointFamilyAut plusIndexEquiv
    reindexVectorEquiv reindexQuadraticForm_map coordinate_plus_family_eq_matrixImage)
open CFSG.ComponentClassification.UnbalancedCatalog.ThreeFamily

theorem odd_D4_two_reflection_full_centralizer_preserves_point_family (G : Type) [Group G]
    {ℓ f : ℕ} (hℓ : ℓ ≠ 2) (h : StatedClassicalModel G .POmegaPlus 4 ℓ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    ∃ g : matrixDerived (coordinateQuadPlus 4 K),
      matrixLinearEquiv g.val =
        reflect (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4)
          (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)) *
        reflect (coordinateQuadPlus 4 K) (reindexVectorEquiv (plusIndexEquiv 4)
          (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) ∧
      orderOf (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) = 2 ∧
      orderOf (MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)) = 2 ∧
      Subgroup.centralizer
          {MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g)} ≤
        projectivePointFamilyAut (coordinateQuadPlus 4 K) ∧
      projectivePointFamilyAut (coordinateQuadPlus 4 K) =
        matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      (IsSquare (-1 : K) →
        Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
            2 + ((ℓ ^ f) ^ 2 + 1) * ((ℓ ^ f) ^ 2 + ℓ ^ f + 1) ∧
        Nat.card {U // U ∈ plusCX 4 K ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
            2 * (ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 + 1) ∧
        Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U} =
            2 * (ℓ ^ f + 1) * ((ℓ ^ f) ^ 2 + 1)) ∧
      (¬ IsSquare (-1 : K) →
        (∃ U ∈ projectivePointFamily (coordinateQuadPlus 4 K),
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U = U) ∧
        (∀ U ∈ plusCX 4 K,
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U ≠ U) ∧
        (∀ U ∈ plusCXstar 4 K (by norm_num),
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K) g) • U ≠ U)) := by
  have hp : ℓ.Prime := h.1.1
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hp⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : ∀ x, coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) x) =
      quadPlus 4 K x := reindexQuadraticForm_map (plusIndexEquiv 4) (quadPlus 4 K)
  have h4 : 3 ≤ 4 := by norm_num
  obtain ⟨A, hA⟩ : ∃ A : StatedOmega (StatedQuadPlus 4 K), toLinEquiv _ K A.val =
      reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
        reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :=
    ⟨(plusDerivedEquiv 4 K h4).symm ⟨_, twoReflection_mem_elementary⟩,
      (plusDerivedEquiv_val 4 K h4 _).symm.trans
        (congrArg Subtype.val ((plusDerivedEquiv 4 K h4).apply_symm_apply _))⟩
  have hAA : A * A = 1 := by
    apply Subtype.ext
    apply (toLinEquiv _ K).injective
    rw [Subgroup.coe_mul, map_mul, hA, Subgroup.coe_one, map_one, twoReflection_mul_self]
  have hvec : ∀ x, matrixLinearEquiv
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A).val
        (reindexVectorEquiv (plusIndexEquiv 4) x) =
      reindexVectorEquiv (plusIndexEquiv 4)
        ((reflect (quadPlus 4 K) (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) *
          reflect (quadPlus 4 K) (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) x) := by
    intro x
    rw [statedDerivedReindexEquiv_vector, hA]
  have hc1 : MulAut.conj
      (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus 4 K))) ≠ 1 := by
    intro h1
    obtain ⟨L₀, hL₀, hL₀g⟩ := exists_line_not_fixed_twoReflection (K := K) h2
    have hst := conj_mk_smul_stabilizer A L₀
    rw [h1, one_smul, hA] at hst
    exact hL₀g (stabilizer_injOn_lines (K := K) (n := 4) h4
      (OrthogonalSplit.map_mem_singularSubspaces
        (orthElementaryGroup_le _ twoReflection_mem_elementary) hL₀) hL₀ hst.symm)
  have hc2 : MulAut.conj
      (QuotientGroup.mk' _ A : StatedProj (StatedOmega (StatedQuadPlus 4 K))) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, pow_two, hAA, map_one, map_one]
  have hψA : plusCoordinateEquiv 4 K (QuotientGroup.mk' _ A) =
      matrixProjectiveProjection (coordinateQuadPlus 4 K)
        (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A) :=
    statedProjectiveReindexEquiv_mk (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A
  have ht := conj_projection_reindex A
  have ht2 : MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) ^ 2 =
        1 := by
    rw [ht, ← map_pow, hc2, map_one]
  have ht1 : MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) ≠
        1 := by
    rw [ht]
    exact fun h1 => hc1 ((MulAut.congr (plusCoordinateEquiv 4 K)).injective
      (h1.trans (map_one _).symm))
  have hπ2 : matrixProjectiveProjection (coordinateQuadPlus 4 K)
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A) ^ 2 =
        1 := by
    rw [← hψA, ← map_pow, ← map_pow, pow_two, hAA, map_one, map_one]
  have hπ1 : matrixProjectiveProjection (coordinateQuadPlus 4 K)
      (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A) ≠ 1 :=
    fun h1 => ht1 (by rw [h1, map_one])
  obtain ⟨cP, cX, cXs⟩ := card_fixed_coordinate_families A
  rw [hA] at cP cX cXs
  obtain ⟨hXsing, hXssing, -⟩ := orthogonal_geometry_split_maximal_family_orbits (K := K) h4
  have hcounts : (IsSquare (-1 : K) →
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} = 2 + (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) ∧
      Nat.card {U // U ∈ plusCX 4 K ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} = 2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) ∧
      Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} = 2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1)) ∧
      (¬ IsSquare (-1 : K) →
        0 < Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
            (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
              U = U} ∧
        Nat.card {U // U ∈ plusCX 4 K ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
            (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
              U = U} = 0 ∧
        Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
          MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
            (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
              U = U} = 0) := by
    refine ⟨fun hsq => ?_, fun hsq => ?_⟩
    · obtain ⟨i, hi⟩ := hsq
      obtain ⟨hL, -⟩ := card_fixed_twoReflection_of_sq h2 hi.symm
      obtain ⟨hX, hXs⟩ := card_fixed_orbits_twoReflection_of_sq h2 hi.symm
      exact ⟨cP.trans hL, cX.trans hX, cXs.trans hXs⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [cP]
        exact Nat.card_pos_iff.mpr ⟨⟨⟨_, line_fixed_twoReflection⟩⟩, inferInstance⟩
      · rw [cX]
        have : IsEmpty {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K))
            (flag 4 K 4) ∧ M.map ((reflect (quadPlus 4 K)
              (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) * reflect (quadPlus 4 K)
                (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
                  (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
                    (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} :=
          ⟨fun M => not_map_eq_orbit_twoReflection hsq hXsing M.2.1 M.2.2⟩
        exact Nat.card_of_isEmpty
      · rw [cXs]
        have : IsEmpty {M // M ∈ MulAction.orbit (orthElementaryGroup (quadPlus 4 K))
            (Xstar 4 K (by norm_num)) ∧ M.map ((reflect (quadPlus 4 K)
              (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) * reflect (quadPlus 4 K)
                (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) :
                  (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :
                    (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} :=
          ⟨fun M => not_map_eq_orbit_twoReflection hsq hXssing M.2.1 M.2.2⟩
        exact Nat.card_of_isEmpty
  have hne : Nat.card {U // U ∈ plusCX 4 K ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} ≠
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} ∧
      Nat.card {U // U ∈ plusCXstar 4 K (by norm_num) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} ≠
      Nat.card {U // U ∈ projectivePointFamily (coordinateQuadPlus 4 K) ∧
        MulAut.conj (matrixProjectiveProjection (coordinateQuadPlus 4 K)
          (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A)) •
            U = U} := by
    by_cases hsq : IsSquare (-1 : K)
    · obtain ⟨eP, eX, eXs⟩ := hcounts.1 hsq
      have hq : 2 ≤ Nat.card K := Finite.one_lt_card
      have key : 2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) ≠
          2 + (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) := by
        intro hc
        have h1 : ((2 + (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 + 1) : ℕ) : ℤ) -
            ((2 * (Nat.card K + 1) * (Nat.card K ^ 2 + 1) : ℕ) : ℤ) =
              ((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) ^ 3 - 1) := by
          push_cast
          ring
        have hq' : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq
        have h3 : (0 : ℤ) < ((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) ^ 3 - 1) := by
          apply mul_pos (by linarith)
          nlinarith
        rw [hc] at h1
        linarith
      rw [eP, eX, eXs]
      exact ⟨key, key⟩
    · obtain ⟨eP, eX, eXs⟩ := hcounts.2 hsq
      rw [eX, eXs]
      exact ⟨eP.ne, eP.ne⟩
  have himage := coordinate_plus_family_eq_matrixImage h K hK e
  refine ⟨statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) A,
    ?_, orderOf_eq_prime hπ2 hπ1, orderOf_eq_prime ht2 ht1, fun α hα => ?_, himage,
    fun hsq => ?_, fun hsq => ?_⟩
  · refine LinearEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective y
    rw [hvec, LinearEquiv.mul_apply (reflect (coordinateQuadPlus 4 K) _),
      reflect_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr,
      reflect_map_isometry (reindexVectorEquiv (K := K) (plusIndexEquiv 4)) hr]
    rfl
  · rw [Subgroup.mem_centralizer_singleton_iff] at hα
    exact mem_pointFamilyAut_of_card_fixed_ne hne.1 hne.2 (mul_inv_eq_of_eq_mul hα)
  · obtain ⟨eP, eX, eXs⟩ := hcounts.1 hsq
    rw [eP, eX, eXs, hK]
    exact ⟨by ring, rfl, rfl⟩
  · obtain ⟨eP, eX, eXs⟩ := hcounts.2 hsq
    refine ⟨?_, fun U hU hfix => ?_, fun U hU hfix => ?_⟩
    · obtain ⟨⟨U, hU, hfix⟩⟩ := (Nat.card_pos_iff.mp eP).1
      exact ⟨U, hU, hfix⟩
    · exact (Finite.card_eq_zero_iff.mp eX).false ⟨U, hU, hfix⟩
    · exact (Finite.card_eq_zero_iff.mp eXs).false ⟨U, hU, hfix⟩

end CFSG.RankThree.OddD4Centralizer
