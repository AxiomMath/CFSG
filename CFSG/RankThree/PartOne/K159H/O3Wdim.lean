module

public import CFSG.RankThree.PartOne.K159H.O3Wsub
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  (S : Subgroup (Fin r → Kˣ))

@[expose] noncomputable def nNontriv : ℕ := Nat.card {c : Fin r ⊕ Fin r // ¬ TrivOn S c}

@[expose] noncomputable def nPairs : ℕ := Nat.card {k : Fin r // ¬ TrivOn S (Sum.inl k)}

theorem nNontriv_eq : nNontriv S = 2 * nPairs S := by
  classical
  unfold nNontriv nPairs
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype,
    Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  have : ∀ a : Fin r, (if ¬ TrivOn S (Sum.inr a) then 1 else 0) =
      (if ¬ TrivOn S (Sum.inl a) then 1 else 0) := by
    intro a
    have h : TrivOn S (Sum.inr a) ↔ TrivOn S (Sum.inl a) := trivOn_swap_iff S (Sum.inl a)
    simp only [h]
  simp only [this]
  ring


@[expose] def coordNt : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ({c : Fin r ⊕ Fin r // ¬ TrivOn S c} → K) :=
  LinearMap.pi fun c => (LinearMap.proj c.1).comp (LinearMap.fst K (Fin r ⊕ Fin r → K) A)

variable {S}

theorem coordNt_apply (v : (Fin r ⊕ Fin r → K) × A) (c : {c : Fin r ⊕ Fin r // ¬ TrivOn S c}) :
    coordNt S v c = v.1 c.1 := rfl

theorem ker_coordNt : LinearMap.ker (coordNt (K := K) (A := A) S) = Wsub S := by
  ext v
  simp only [LinearMap.mem_ker, mem_Wsub]
  constructor
  · intro h c hc
    exact congrFun h ⟨c, hc⟩
  · intro h
    funext c
    exact h c.1 c.2

theorem coordNt_surjective : Function.Surjective (coordNt (K := K) (A := A) S) := by
  classical
  intro a
  refine ⟨((fun c => if h : ¬ TrivOn S c then a ⟨c, h⟩ else 0), 0), ?_⟩
  funext c
  rw [coordNt_apply]
  simp [c.2]

theorem finrank_Wsub [FiniteDimensional K A] :
    nNontriv S + finrank K (Wsub (K := K) (A := A) S) = 2 * r + finrank K A := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (coordNt (K := K) (A := A) S)
  rw [LinearMap.range_eq_top.mpr coordNt_surjective, finrank_top, ker_coordNt, finrank_tailSpace,
    Module.finrank_fintype_fun_eq_card] at h
  unfold nNontriv
  rw [Nat.card_eq_fintype_card]
  exact h


variable (S)

open _root_.Classical in
@[expose] def embedNe : ({k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) →ₗ[K] (Fin r ⊕ Fin r → K) × A where
  toFun a := (Sum.elim (fun k => if h : ¬ TrivOn S (Sum.inl k) then a ⟨k, h⟩ else 0) (fun _ => 0), 0)
  map_add' a b := by
    refine Prod.ext (funext fun c => ?_) (by simp)
    rcases c with k | k
    · by_cases h : ¬ TrivOn S (Sum.inl k)
      · simp only [Prod.fst_add, Pi.add_apply, Sum.elim_inl, dite_eq_left h]
      · simp only [Prod.fst_add, Pi.add_apply, Sum.elim_inl, dite_eq_right h, add_zero]
    · simp
  map_smul' t a := by
    refine Prod.ext (funext fun c => ?_) (by simp)
    rcases c with k | k
    · by_cases h : ¬ TrivOn S (Sum.inl k)
      · simp only [Prod.smul_fst, Pi.smul_apply, Sum.elim_inl, dite_eq_left h, smul_eq_mul, RingHom.id_apply]
      · simp only [Prod.smul_fst, Pi.smul_apply, Sum.elim_inl, dite_eq_right h, smul_zero, RingHom.id_apply]
    · simp

variable {S}

theorem embedNe_snd (a : {k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) : (embedNe (A := A) S a).2 = 0 := rfl

theorem embedNe_fst_inr (a : {k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) (k : Fin r) :
    (embedNe (A := A) S a).1 (Sum.inr k) = 0 := rfl

open _root_.Classical in
theorem embedNe_fst_inl (a : {k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) (k : Fin r) :
    (embedNe (A := A) S a).1 (Sum.inl k) = if h : ¬ TrivOn S (Sum.inl k) then a ⟨k, h⟩ else 0 := rfl

theorem embedNe_injective : Function.Injective (embedNe (K := K) (A := A) S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext k
  have := congrFun (congrArg Prod.fst ha) (Sum.inl k.1)
  rw [embedNe_fst_inl, dite_eq_left k.2] at this
  exact this

theorem quadTail_embedNe (a : {k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) :
    quadTail r qA (embedNe (A := A) S a) = 0 := by
  rw [quadTail_apply, quadPlus_apply, embedNe_snd, QuadraticMap.map_zero, add_zero]
  exact Finset.sum_eq_zero fun i _ => by rw [embedNe_fst_inr, mul_zero]

theorem polar_embedNe {x : (Fin r ⊕ Fin r → K) × A} (hx : x ∈ Wsub (K := K) (A := A) S)
    (a : {k : Fin r // ¬ TrivOn S (Sum.inl k)} → K) :
    polar (quadTail r qA) x (embedNe (A := A) S a) = 0 := by
  rw [polar_quadTail, embedNe_snd, polar_zero_right, add_zero, polar_quadPlus]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [embedNe_fst_inr, mul_zero, zero_add]
  by_cases h : TrivOn S (Sum.inl i)
  · rw [embedNe_fst_inl, dite_eq_right (not_not.mpr h), zero_mul]
  · have : x.1 (Sum.inr i) = 0 := hx _ (fun h' => h ((trivOn_swap_iff S (Sum.inl i)).1 h'))
    rw [this, mul_zero]

theorem finrank_totSing_Wsub [FiniteDimensional K A] (hani : qA.Anisotropic)
    {U : Submodule K (Wsub (K := K) (A := A) S)}
    (hU : ∀ u ∈ U, quadTail r qA (u : (Fin r ⊕ Fin r → K) × A) = 0) :
    finrank K U + nPairs S ≤ r := by
  classical
  set Ne : Submodule K ((Fin r ⊕ Fin r → K) × A) := LinearMap.range (embedNe (A := A) S) with hNe
  set U' : Submodule K ((Fin r ⊕ Fin r → K) × A) := U.map (Wsub (K := K) (A := A) S).subtype with hU'
  have hdisj : Disjoint U' Ne := by
    rw [Submodule.disjoint_def]
    rintro x ⟨u, -, rfl⟩ ⟨a, ha⟩
    have hW : (u : (Fin r ⊕ Fin r → K) × A) ∈ Wsub (K := K) (A := A) S := u.2
    have ha0 : a = 0 := by
      funext k
      have h1 := congrFun (congrArg Prod.fst ha) (Sum.inl k.1)
      rw [embedNe_fst_inl, dite_eq_left k.2] at h1
      have h2 : ((Wsub (K := K) (A := A) S).subtype u).1 (Sum.inl k.1) = 0 := hW (Sum.inl k.1) k.2
      rw [h2] at h1
      exact h1
    rw [ha0, map_zero] at ha
    exact ha.symm
  have hsing : ∀ x ∈ U' ⊔ Ne, quadTail r qA x = 0 := by
    intro x hx
    obtain ⟨y, ⟨u, hu, rfl⟩, e, ⟨a, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
    rw [QuadraticMap.map_add (quadTail r qA), Submodule.subtype_apply, hU u hu, quadTail_embedNe, polar_embedNe u.2, add_zero, add_zero]
  have h1 := finrank_le_of_totSing_tail hani hsing
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq U' Ne
  rw [hdisj.eq_bot, finrank_bot, add_zero] at h2
  have h3 : finrank K U' = finrank K U := Submodule.finrank_map_subtype_eq _ U
  have h4 : finrank K Ne = nPairs S := by
    rw [hNe, LinearMap.finrank_range_of_inj embedNe_injective, Module.finrank_fintype_fun_eq_card]
    unfold nPairs
    rw [Nat.card_eq_fintype_card]
  omega

theorem hts_Wsub [FiniteDimensional K A] (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (U : Submodule K (Wsub (K := K) (A := A) S))
    (hU : finrank K U = finrank K (Wsub (K := K) (A := A) S) / 2) :
    ∃ u ∈ U, ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := finrank_totSing_Wsub hani (S := S) (U := U) (fun u hu => hcon u hu)
  have h2 := finrank_Wsub (K := K) (A := A) (S := S)
  rw [nNontriv_eq, hdim] at h2
  omega

end CFSG.RankThree.PartOne.K159H
