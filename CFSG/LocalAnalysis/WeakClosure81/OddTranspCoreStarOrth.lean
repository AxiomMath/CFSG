module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
import CFSG.Fischer.Classification.O4Minus2S5
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
import CFSG.LargeExtraspecial.S12InspP4Ord

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Open Matrix

section Aux

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.Fischer.Classification CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Permutation.SymmetricCoxeter

variable {G : Type} [Group G] {t : G} {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

private theorem exists_tvFamily (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) :
    ∃ T : ∀ u : ι → ZMod 2, Q u = 1 → G, (∀ u hu, IsConj t (T u hu)) ∧
      (∀ u hu u' hu', T u hu * T u' hu' = T u' hu' * T u hu ↔ polar Q u u' = 0) ∧
      ∀ u hu u' hu', T u hu = T u' hu' → u = u' := by
  obtain ⟨φ, hφ⟩ := hmod
  refine ⟨fun u hu => φ.symm ⟨orthTransvectionGL Q u, tv_mem_group hu⟩, fun u hu => ?_,
    fun u hu u' hu' => ?_, fun u hu u' hu' h => ?_⟩
  · exact (hφ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact tv_mem hu)
  · refine Iff.trans ?_ (tv_commute_iff hnd hu hu')
    show φ.symm _ * φ.symm _ = φ.symm _ * φ.symm _ ↔ _
    rw [← map_mul, ← map_mul, φ.symm.injective.eq_iff]
    exact Subtype.ext_iff
  · exact eq_of_tv_eq hnd hu hu' (congrArg Subtype.val (φ.symm.injective h))

private theorem hasCoreStar_of_vectors (hP : Pair G {x | IsConj t x})
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1))
    {v w₁ w₂ w₃ : ι → ZMod 2} (hv : Q v = 1) (h1 : Q w₁ = 1) (h2 : Q w₂ = 1)
    (h3 : Q w₃ = 1) (hv1 : polar Q v w₁ = 1) (hv2 : polar Q v w₂ = 1) (hv3 : polar Q v w₃ = 1)
    (h12 : polar Q w₁ w₂ = 0) (h13 : polar Q w₁ w₃ = 0) (h23 : polar Q w₂ w₃ = 0)
    (n12 : w₁ ≠ w₂) (n13 : w₁ ≠ w₃) (n23 : w₂ ≠ w₃) : HasCoreStar G t := by
  obtain ⟨T, hTD, hTc, hTe⟩ := exists_tvFamily hnd hmod
  have hord : ∀ u hu u' hu', polar Q u u' = 1 → orderOf (T u hu * T u' hu') = 3 :=
    fun u hu u' hu' h => CFSG.Fischer.Pair.orderOf_mul_eq_three hP (hTD u hu) (hTD u' hu')
      fun e => zero_ne_one (((hTc u hu u' hu').mp e).symm.trans h)
  exact hasCoreStar_of_center (hTD v hv) (hTD w₁ h1) (hTD w₂ h2) (hTD w₃ h3)
    (hord _ hv _ h1 hv1) (hord _ hv _ h2 hv2) (hord _ hv _ h3 hv3)
    ((hTc _ h1 _ h2).mpr h12) ((hTc _ h1 _ h3).mpr h13) ((hTc _ h2 _ h3).mpr h23)
    (fun e => n12 (hTe _ h1 _ h2 e)) (fun e => n13 (hTe _ h1 _ h3 e))
    (fun e => n23 (hTe _ h2 _ h3 e))

omit [Fintype ι] [DecidableEq ι] in
private theorem map_polar_basis {κ : Type} [Fintype κ] {F : (κ → ZMod 2) → ZMod 2}
    (b : Module.Basis κ (ZMod 2) (ι → ZMod 2)) (hb : ∀ v, Q v = F (b.equivFun v))
    (c d : κ → ZMod 2) : Q (b.equivFun.symm c) = F c ∧
      polar Q (b.equivFun.symm c) (b.equivFun.symm d) = F (c + d) - F c - F d := by
  have h : ∀ c, Q (b.equivFun.symm c) = F c := fun c => by rw [hb, LinearEquiv.apply_symm_apply]
  refine ⟨h c, ?_⟩
  rw [polar, ← map_add, h, h, h]

private def extH (k n : ℕ) (c : Fin k ⊕ Fin k → ZMod 2) : Fin n ⊕ Fin n → ZMod 2 :=
  Sum.elim (fun i => if h : (i : ℕ) < k then c (.inl ⟨i, h⟩) else 0)
    fun i => if h : (i : ℕ) < k then c (.inr ⟨i, h⟩) else 0

private theorem extH_add (k n : ℕ) (c d : Fin k ⊕ Fin k → ZMod 2) :
    extH k n (c + d) = extH k n c + extH k n d := by
  funext s
  rcases s with i | i <;> by_cases h : (i : ℕ) < k <;> simp [extH, h]

private theorem extH_injective {k n : ℕ} (hk : k ≤ n) : Function.Injective (extH k n) := by
  intro c d h
  funext s
  rcases s with i | i
  · simpa [extH] using congrFun h (.inl (Fin.castLE hk i))
  · simpa [extH] using congrFun h (.inr (Fin.castLE hk i))

private theorem qPlus_extH {k n : ℕ} (hk : k ≤ n) (c : Fin k ⊕ Fin k → ZMod 2) :
    GLAQPlus (ZMod 2) n (extH k n c) = GLAQPlus (ZMod 2) k c := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun j hj => ?_) fun i => ?_
  · have h : ¬ (j : ℕ) < k := fun h => hj ⟨⟨j, h⟩, Fin.ext rfl⟩
    simp [extH, h]
  · simp [extH]

private def extM (k n : ℕ) (c : GLAMinusIdx k → ZMod 2) : GLAMinusIdx n → ZMod 2 :=
  Sum.elim (extH k n fun s => c (.inl s)) fun j => c (.inr j)

private theorem extM_add (k n : ℕ) (c d : GLAMinusIdx k → ZMod 2) :
    extM k n (c + d) = extM k n c + extM k n d := by
  funext s
  rcases s with s | j
  · exact congrFun (extH_add k n (fun s => c (.inl s)) fun s => d (.inl s)) s
  · rfl

private theorem extM_injective {k n : ℕ} (hk : k ≤ n) : Function.Injective (extM k n) := by
  intro c d h
  funext s
  rcases s with s | j
  · have h' : extH k n (fun s => c (.inl s)) = extH k n (fun s => d (.inl s)) :=
      funext fun s' => congrFun h (.inl s')
    exact congrFun (extH_injective hk h') s
  · exact congrFun h (.inr j)

private theorem qMinus_extM {k n : ℕ} (hk : k ≤ n) (c : GLAMinusIdx k → ZMod 2) :
    GLAQMinus n (1 : ZMod 2) 1 (extM k n c) = GLAQMinus k (1 : ZMod 2) 1 c :=
  congrArg (· + c (.inr 0) ^ 2 + 1 * c (.inr 0) * c (.inr 1) + 1 * c (.inr 1) ^ 2)
    (qPlus_extH hk fun s => c (.inl s))

private theorem qPlus_three (c : Fin 3 ⊕ Fin 3 → ZMod 2) : GLAQPlus (ZMod 2) 3 c =
    c (.inl 0) * c (.inr 0) + c (.inl 1) * c (.inr 1) + c (.inl 2) * c (.inr 2) :=
  Fin.sum_univ_three fun i => c (.inl i) * c (.inr i)

private theorem qPlus_four (c : Fin 4 ⊕ Fin 4 → ZMod 2) : GLAQPlus (ZMod 2) 4 c =
    c (.inl 0) * c (.inr 0) + c (.inl 1) * c (.inr 1) + c (.inl 2) * c (.inr 2) +
      c (.inl 3) * c (.inr 3) :=
  Fin.sum_univ_four fun i => c (.inl i) * c (.inr i)

private theorem qMinus_two (c : GLAMinusIdx 2 → ZMod 2) : GLAQMinus 2 (1 : ZMod 2) 1 c =
    c (.inl (.inl 0)) * c (.inl (.inr 0)) + c (.inl (.inl 1)) * c (.inl (.inr 1)) +
      c (.inr 0) ^ 2 + 1 * c (.inr 0) * c (.inr 1) + 1 * c (.inr 1) ^ 2 :=
  congrArg (· + c (.inr 0) ^ 2 + 1 * c (.inr 0) * c (.inr 1) + 1 * c (.inr 1) ^ 2)
    (Fin.sum_univ_two fun i => c (.inl (.inl i)) * c (.inl (.inr i)))

private theorem hasCoreStar_of_plus (hP : Pair G {x | IsConj t x})
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) {m : ℕ} (hm : 4 ≤ m)
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) (ι → ZMod 2))
    (hb : ∀ v, Q v = GLAQPlus (ZMod 2) m (b.equivFun v)) : HasCoreStar G t := by
  have hQ : ∀ c, Q (b.equivFun.symm (extH 4 m c)) = GLAQPlus (ZMod 2) 4 c := fun c => by
    rw [(map_polar_basis (F := GLAQPlus (ZMod 2) m) b hb _ 0).1, qPlus_extH hm]
  have hB : ∀ c d, polar Q (b.equivFun.symm (extH 4 m c)) (b.equivFun.symm (extH 4 m d)) =
      GLAQPlus (ZMod 2) 4 (c + d) - GLAQPlus (ZMod 2) 4 c - GLAQPlus (ZMod 2) 4 d :=
    fun c d => by
      rw [(map_polar_basis (F := GLAQPlus (ZMod 2) m) b hb _ _).2, ← extH_add, qPlus_extH hm,
        qPlus_extH hm, qPlus_extH hm]
  have hinj : ∀ c d, c ≠ d → b.equivFun.symm (extH 4 m c) ≠ b.equivFun.symm (extH 4 m d) :=
    fun c d h e => h (extH_injective hm (b.equivFun.symm.injective e))
  refine hasCoreStar_of_vectors hP hnd hmod
    (v := b.equivFun.symm (extH 4 m (Sum.elim ![1, 1, 1, 1] ![0, 0, 0, 1])))
    (w₁ := b.equivFun.symm (extH 4 m (Sum.elim ![1, 0, 0, 0] ![1, 0, 0, 0])))
    (w₂ := b.equivFun.symm (extH 4 m (Sum.elim ![0, 1, 0, 0] ![0, 1, 0, 0])))
    (w₃ := b.equivFun.symm (extH 4 m (Sum.elim ![0, 0, 1, 0] ![0, 0, 1, 0])))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (rw [hQ, qPlus_four]; decide)
    | (rw [hB]; simp only [qPlus_four]; decide)
    | exact hinj _ _ (by decide)

private theorem hasCoreStar_of_minus (hP : Pair G {x | IsConj t x})
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) {n : ℕ} (hn : 2 ≤ n)
    (b : Module.Basis (GLAMinusIdx n) (ZMod 2) (ι → ZMod 2))
    (hb : ∀ v, Q v = GLAQMinus n (1 : ZMod 2) 1 (b.equivFun v)) : HasCoreStar G t := by
  have hQ : ∀ c, Q (b.equivFun.symm (extM 2 n c)) = GLAQMinus 2 (1 : ZMod 2) 1 c := fun c => by
    rw [(map_polar_basis (F := GLAQMinus n (1 : ZMod 2) 1) b hb _ 0).1, qMinus_extM hn]
  have hB : ∀ c d, polar Q (b.equivFun.symm (extM 2 n c)) (b.equivFun.symm (extM 2 n d)) =
      GLAQMinus 2 (1 : ZMod 2) 1 (c + d) - GLAQMinus 2 (1 : ZMod 2) 1 c -
        GLAQMinus 2 (1 : ZMod 2) 1 d := fun c d => by
    rw [(map_polar_basis (F := GLAQMinus n (1 : ZMod 2) 1) b hb _ _).2, ← extM_add,
      qMinus_extM hn, qMinus_extM hn, qMinus_extM hn]
  have hinj : ∀ c d, c ≠ d → b.equivFun.symm (extM 2 n c) ≠ b.equivFun.symm (extM 2 n d) :=
    fun c d h e => h (extM_injective hn (b.equivFun.symm.injective e))
  refine hasCoreStar_of_vectors hP hnd hmod
    (v := b.equivFun.symm (extM 2 n (Sum.elim (Sum.elim ![1, 1] ![0, 0]) ![0, 1])))
    (w₁ := b.equivFun.symm (extM 2 n (Sum.elim (Sum.elim ![1, 0] ![1, 0]) ![0, 0])))
    (w₂ := b.equivFun.symm (extM 2 n (Sum.elim (Sum.elim ![0, 1] ![0, 1]) ![0, 0])))
    (w₃ := b.equivFun.symm (extM 2 n (Sum.elim (Sum.elim ![0, 0] ![0, 0]) ![1, 0])))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (rw [hQ, qMinus_two]; decide)
    | (rw [hB]; simp only [qMinus_two]; decide)
    | exact hinj _ _ (by decide)

private def chainC : Fin 7 → Fin 3 ⊕ Fin 3 → ZMod 2 :=
  ![Sum.elim ![0, 0, 1] ![0, 0, 1], Sum.elim ![0, 1, 0] ![0, 1, 1],
    Sum.elim ![0, 0, 1] ![1, 0, 1], Sum.elim ![1, 0, 0] ![1, 0, 0],
    Sum.elim ![0, 0, 1] ![1, 1, 1], Sum.elim ![0, 1, 0] ![0, 1, 0],
    Sum.elim ![0, 0, 1] ![0, 1, 1]]

private theorem chainC_q (i : Fin 7) : GLAQPlus (ZMod 2) 3 (chainC i) = 1 := by
  rw [qPlus_three]
  revert i
  decide

private theorem chainC_polar (i j : Fin 7) :
    GLAQPlus (ZMod 2) 3 (chainC i + chainC j) - GLAQPlus (ZMod 2) 3 (chainC i) -
      GLAQPlus (ZMod 2) 3 (chainC j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 := by
  simp only [qPlus_three]
  revert i j
  decide

private theorem chainC_inj (i j : Fin 7) (h : chainC i = chainC j) : i = j := by
  revert i j
  decide

private theorem perm_eight_of_plus (hP : Pair G {x | IsConj t x})
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1))
    (b : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (Fin (2 * 3) → ZMod 2))
    (hb : ∀ v, Q v = GLAQPlus (ZMod 2) 3 (b.equivFun v)) :
    ∃ n : ℕ, ∃ e : G ≃* Equiv.Perm (Fin n), (e t).IsSwap := by
  obtain ⟨T, hTD, hTc, hTe⟩ := exists_tvFamily hnd hmod
  have hQ : ∀ i, Q (b.equivFun.symm (chainC i)) = 1 := fun i => by
    rw [(map_polar_basis (F := GLAQPlus (ZMod 2) 3) b hb _ 0).1]
    exact chainC_q i
  have hB : ∀ i j (hi : i < 7) (hj : j < 7),
      polar Q (b.equivFun.symm (chainC ⟨i, hi⟩)) (b.equivFun.symm (chainC ⟨j, hj⟩)) =
        if i + 1 = j ∨ j + 1 = i then 1 else 0 := fun i j hi hj => by
    rw [(map_polar_basis (F := GLAQPlus (ZMod 2) 3) b hb _ _).2]
    exact chainC_polar ⟨i, hi⟩ ⟨j, hj⟩
  let x : ℕ → G := fun i => if h : i < 7 then T _ (hQ ⟨i, h⟩) else 1
  have hx : ∀ i (h : i < 7), x i = T _ (hQ ⟨i, h⟩) := fun i h => dif_pos h
  have hxD : ∀ i, i < 7 → IsConj t (x i) := fun i h => by
    rw [hx i h]
    exact hTD _ _
  have hsq : ∀ i, i < 7 → x i * x i = 1 := fun i h => CFSG.Fischer.Pair.mul_self hP (hxD i h)
  have hadj : ∀ i, i + 1 < 7 → (x i * x (i + 1)) ^ 3 = 1 := fun i h => by
    have hne : x i * x (i + 1) ≠ x (i + 1) * x i := fun e => by
      rw [hx i (by omega), hx (i + 1) h] at e
      have h0 := (hTc _ _ _ _).mp e
      rw [hB i (i + 1) (by omega) h, if_pos (Or.inl rfl)] at h0
      exact one_ne_zero h0
    rw [← CFSG.Fischer.Pair.orderOf_mul_eq_three hP (hxD i (by omega)) (hxD (i + 1) h) hne,
      pow_orderOf_eq_one]
  have hcomm : ∀ i j, i + 2 ≤ j → j < 7 → x i * x j = x j * x i := fun i j hij hj => by
    rw [hx i (by omega), hx j hj]
    exact (hTc _ _ _ _).mpr (by rw [hB i j (by omega) hj, if_neg (by omega)])
  have hne : ∀ i j, i < 7 → j < 7 → i ≠ j → x i ≠ x j := fun i j hi hj hij e => by
    rw [hx i hi, hx j hj] at e
    exact hij (congrArg Fin.val (chainC_inj _ _ (b.equivFun.symm.injective (hTe _ _ _ _ e))))
  obtain ⟨e, he⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_mulEquiv_of_pow_three (n := 7)
    (by norm_num) hsq hadj hcomm hne
  have hcl : Nat.card ↥(Subgroup.closure (x '' Set.Iio 7)) = 40320 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hG : Nat.card G = 40320 ∨ Nat.card G = 51840 := by
    rw [CFSG.LargeExtraspecial.S12Insp4P.card_eq_card_orthogonalGroup_of_model hmod]
    exact CFSG.LargeExtraspecial.S12Insp4P.card_orthogonalGroup_six hnd
  have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.closure (x '' Set.Iio 7))
  rw [hcl] at hdvd
  have hG8 : Nat.card G = 40320 := by
    rcases hG with h | h
    · exact h
    · rw [h] at hdvd
      exact absurd hdvd (by decide)
  have : Finite ↥(Subgroup.closure (x '' Set.Iio 7)) :=
    Nat.finite_of_card_ne_zero (by rw [hcl]; decide)
  have htop : Subgroup.closure (x '' Set.Iio 7) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (hcl.trans hG8.symm)
  let f : Equiv.Perm (Fin (7 + 1)) →* G :=
    (Subgroup.closure (x '' Set.Iio 7)).subtype.comp e.toMonoidHom
  have hf : Function.Bijective f := by
    refine ⟨Subtype.val_injective.comp e.injective, fun g => ?_⟩
    have hg : g ∈ Subgroup.closure (x '' Set.Iio 7) := by
      rw [htop]
      exact Subgroup.mem_top g
    exact ⟨e.symm ⟨g, hg⟩, by simp [f]⟩
  let ψ : Equiv.Perm (Fin (7 + 1)) ≃* G := MulEquiv.ofBijective f hf
  have hψ : ψ (adjSwap 7 0) = x 0 := he 0 (by norm_num)
  have hconj : IsConj (adjSwap 7 0) (ψ.symm t) := by
    have h1 := ψ.symm.toMonoidHom.map_isConj (hxD 0 (by norm_num)).symm
    rw [← hψ] at h1
    simpa using h1
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  refine ⟨7 + 1, ψ.symm, ?_⟩
  rw [← hg, adjSwap_of_lt (by norm_num : 0 < 7), ← Equiv.swap_apply_apply]
  exact ⟨_, _, g.injective.ne (by simp), rfl⟩

private theorem permOrStar_of_orthModel_aux (hP : Pair G {x | IsConj t x}) {m : ℕ} (hm : 2 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (polar Q) fun v => Q v = 1)) :
    (∃ n : ℕ, ∃ e : G ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨ HasCoreStar G t := by
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  ·
    left
    let Q4 : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) := Q
    have hM4 : fischerLinearModel {x : G | IsConj t x}
        (fischerMatrixGroup fun A => ∀ x, Q4 (A *ᵥ x) = Q4 x)
        (fischerTransvections (polar Q4) fun v => Q4 v = 1) := hmod
    obtain ⟨φ, hφ⟩ := hM4
    obtain ⟨e, he⟩ := o4minus2_equiv_s5 (Q := Q4) hnd (hex rfl)
    have h1 : e (φ t) ∈ e '' transvectionSet Q4 :=
      Set.mem_image_of_mem e ((hφ t).mp (IsConj.refl t))
    rw [he] at h1
    exact ⟨5, φ.trans e, h1⟩
  · have hQ : (polarBilin Q).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall hnd
    rcases CFSG.HardMathSupport.Solomon.Coordinator.mclt_exists_basis_quadratic Q hQ
        (by omega : 1 ≤ m) (Module.finrank_fin_fun _) with ⟨b, hb⟩ | ⟨b, hb⟩
    · rcases (by omega : m = 3 ∨ 4 ≤ m) with rfl | hm4
      · exact Or.inl (perm_eight_of_plus hP hnd hmod b hb)
      · exact Or.inr (hasCoreStar_of_plus hP hnd hmod hm4 b hb)
    · exact Or.inr (hasCoreStar_of_minus hP hnd hmod (by omega : 2 ≤ m - 1) b hb)

end Aux

theorem permOrStar_of_orthModel {G : Type} [Group G] {t : G}
    (hP : Pair G {x | IsConj t x}) {m : ℕ} (hm : 2 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : fischerLinearModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    (∃ n : ℕ, ∃ e : G ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨ HasCoreStar G t :=
  permOrStar_of_orthModel_aux hP hm hnd hex hmod

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
