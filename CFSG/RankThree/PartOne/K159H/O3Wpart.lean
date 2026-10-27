module

public import CFSG.RankThree.PartOne.K159H.O3Wdim
public import CFSG.RankThree.PartOne.K159H.O3DE
public import CFSG.ClassicalGroups.Orthogonal.RootCenters
public import CFSG.RankThree.PartOne.K159H.O3Omega
public import CFSG.RankThree.PartOne.K159H.O3Restrict

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {S : Subgroup (Fin r → Kˣ)}

theorem coordIdx_eq_cases {j c : Fin r ⊕ Fin r} (h : coordIdx j = coordIdx c) : j = c ∨ j = c.swap := by
  rcases j with k | k <;> rcases c with k' | k' <;> simp_all [coordIdx]

@[expose] def RcSub (qA : QuadraticForm K A) (S : Subgroup (Fin r → Kˣ)) (c₀ : Fin r ⊕ Fin r) :
    AddSubgroup ((Fin r ⊕ Fin r → K) × A) where
  carrier := {w | polar (quadTail r qA) (hypVec K A c₀) w = 0 ∧
    eichler (quadTail r qA) (hypVec K A c₀) w ∈ Rts qA S}
  zero_mem' := ⟨polar_zero_right _ _, by rw [eichler_zero_right]; exact one_mem _⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨by rw [polar_add_right, ha1, hb1, add_zero], ?_⟩
    rw [← eichler_mul ha1 hb1]
    exact mul_mem ha2 hb2
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨by rw [polar_neg_right, ha1, neg_zero], ?_⟩
    rw [← eichler_inv ha1]
    exact inv_mem ha2

theorem smul_hypVec_mem_RcSub {c₀ j : Fin r ⊕ Fin r} (hc₀ : TrivOn S c₀) (hj : TrivOn S j)
    (hne : coordIdx j ≠ coordIdx c₀) (t : K) : t • hypVec K A j ∈ RcSub qA S c₀ := by
  have hj' : j ≠ c₀.swap := fun h => hne (by rw [h, coordIdx_swap])
  refine ⟨?_, ?_⟩
  · rw [polar_smul_right_eq, polar_hypVec_hypVec, ite_eq_right hj', mul_zero]
  · have : eichler (quadTail r qA) (hypVec K A c₀) (t • hypVec K A j) = rEl qA t j c₀.swap := by
      unfold rEl
      rw [Sum.swap_swap]
    rw [this]
    exact rEl_mem_Rts (by rw [coordIdx_swap]; exact hne) (fun d hd => by rw [hj d hd, wt_swap, hc₀ d hd]; simp)

theorem smul_self_mem_RcSub {c₀ : Fin r ⊕ Fin r} (t : K) : t • hypVec K A c₀ ∈ RcSub qA S c₀ := by
  have hu : quadTail r qA (hypVec K A c₀) = 0 := quadTail_hypVec _
  refine ⟨?_, ?_⟩
  · rw [polar_smul_right_eq, polar_self_eq_zero hu, mul_zero]
  · have := eichler_add_smul_self hu 0 t
    rw [zero_add, eichler_zero_right] at this
    rw [this]
    exact one_mem _

theorem tail_mem_RcSub {c₀ : Fin r ⊕ Fin r} (hc₀ : TrivOn S c₀) (a : A) :
    ((0 : Fin r ⊕ Fin r → K), a) ∈ RcSub qA S c₀ :=
  ⟨polar_hypVec_tail c₀ a, eichler_tail_mem_Rts hc₀ a⟩

theorem eichler_mem_Rts_of_Wsub {c₀ : Fin r ⊕ Fin r} (hc₀ : TrivOn S c₀) {w : (Fin r ⊕ Fin r → K) × A}
    (hw : w ∈ Wsub (K := K) (A := A) S) (hpol : polar (quadTail r qA) (hypVec K A c₀) w = 0) :
    eichler (quadTail r qA) (hypVec K A c₀) w ∈ Rts qA S := by
  have hw1 : w.1 c₀.swap = 0 := by
    rw [polar_comm, polar_hypVec] at hpol
    exact hpol
  have hmem : w ∈ RcSub qA S c₀ := by
    rw [vec_expand w]
    refine add_mem (AddSubgroup.sum_mem _ fun j _ => ?_) (tail_mem_RcSub hc₀ w.2)
    by_cases hj : TrivOn S j
    · by_cases hcj : coordIdx j = coordIdx c₀
      · rcases coordIdx_eq_cases hcj with rfl | rfl
        · exact smul_self_mem_RcSub _
        · rw [hw1, zero_smul]
          exact zero_mem _
      · exact smul_hypVec_mem_RcSub hc₀ hj hcj _
    · rw [hw j hj, zero_smul]
      exact zero_mem _
  exact hmem.2

variable (qA S) in
@[expose] def Hsub : Subgroup (↥(Wsub (K := K) (A := A) S) ≃ₗ[K] ↥(Wsub (K := K) (A := A) S)) where
  carrier := {g' | ∃ h ∈ Rts qA S, (∀ x : Wsub (K := K) (A := A) S, h x = g' x) ∧
    ∀ z, (∀ x ∈ Wsub (K := K) (A := A) S, polar (quadTail r qA) z x = 0) → h z = z}
  one_mem' := ⟨1, one_mem _, fun x => rfl, fun z _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨h₁, hh₁, hx₁, hz₁⟩ ⟨h₂, hh₂, hx₂, hz₂⟩
    refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, fun x => ?_, fun z hz => ?_⟩
    · rw [LinearEquiv.mul_apply, hx₂ x]
      exact hx₁ (b x)
    · rw [LinearEquiv.mul_apply, hz₂ z hz, hz₁ z hz]
  inv_mem' := by
    rintro a ⟨h, hh, hx, hz⟩
    refine ⟨h⁻¹, inv_mem hh, fun x => ?_, fun z hz' => ?_⟩
    · have : h ((a⁻¹ x : Wsub (K := K) (A := A) S) : (Fin r ⊕ Fin r → K) × A) =
          (x : (Fin r ⊕ Fin r → K) × A) := by
        rw [hx]
        exact congrArg Subtype.val (LinearEquiv.apply_inv_apply' a x)
      conv_lhs => rw [← this]
      exact LinearEquiv.inv_apply_apply' h _
    · have := hz z hz'
      conv_lhs => rw [← this]
      exact LinearEquiv.inv_apply_apply' h z

theorem Hsub_le_orth : Hsub qA S ≤
    TauCeti.QuadraticMap.orthogonalGroup ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) := by
  rintro g' ⟨h, hh, hx, -⟩
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  show quadTail r qA (g' x : (Fin r ⊕ Fin r → K) × A) = quadTail r qA (x : (Fin r ⊕ Fin r → K) × A)
  rw [← hx x]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (mem_CO.1 (Rts_le_CO hh)).1 _

theorem isRootCenter_Hsub {c₀ : Fin r ⊕ Fin r} (hc₀ : TrivOn S c₀) :
    IsRootCenter ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) (Hsub qA S)
      ⟨hypVec K A c₀, hypVec_mem_Wsub hc₀⟩ := by
  have hu : quadTail r qA (hypVec K A c₀) = 0 := quadTail_hypVec c₀
  refine ⟨?_, hu, fun w' hw' => ?_⟩
  · intro h
    have := congrFun (congrArg Prod.fst (congrArg Subtype.val h)) c₀
    simp [hypVec_fst] at this
  · have hpol : polar (quadTail r qA) (hypVec K A c₀) (w' : (Fin r ⊕ Fin r → K) × A) = 0 := by
      rw [polar_restrict] at hw'
      exact hw'
    refine ⟨eichler (quadTail r qA) (hypVec K A c₀) (w' : (Fin r ⊕ Fin r → K) × A),
      eichler_mem_Rts_of_Wsub hc₀ w'.2 hpol, fun x => ?_, fun z hz => ?_⟩
    · have hu' : ((quadTail r qA).restrict (Wsub (K := K) (A := A) S))
          ⟨hypVec K A c₀, hypVec_mem_Wsub hc₀⟩ = 0 := hu
      rw [eichler_apply hu hpol, eichler_apply (Q := (quadTail r qA).restrict (Wsub (K := K) (A := A) S)) hu' hw']
      simp [polar_restrict]
    · exact eichler_apply_of_polar_eq_zero (hz _ (hypVec_mem_Wsub hc₀)) (hz _ w'.2)

theorem exists_pair_trivial (htr : ∃ j, TrivOn S j) : ∃ i : Fin r, TrivOn S (Sum.inl i) := by
  obtain ⟨j, hj⟩ := htr
  rcases j with i | i
  · exact ⟨i, hj⟩
  · exact ⟨i, (trivOn_swap_iff S (Sum.inl i)).1 hj⟩

theorem one_le_nPairs (hnt : ∃ j, ¬ TrivOn S j) : 1 ≤ nPairs S := by
  obtain ⟨j, hj⟩ := hnt
  have : ∃ k : Fin r, ¬ TrivOn S (Sum.inl k) := by
    rcases j with k | k
    · exact ⟨k, hj⟩
    · exact ⟨k, fun h => hj ((trivOn_swap_iff S (Sum.inl k)).2 h)⟩
  obtain ⟨k, hk⟩ := this
  have : Nonempty {k : Fin r // ¬ TrivOn S (Sum.inl k)} := ⟨⟨k, hk⟩⟩
  exact Nat.card_pos

theorem nPairs_lt (htr : ∃ j, TrivOn S j) : nPairs S < r := by
  obtain ⟨i, hi⟩ := exists_pair_trivial htr
  have := Finite.card_subtype_lt (α := Fin r) (p := fun k => ¬ TrivOn S (Sum.inl k)) (x := i) (not_not.mpr hi)
  simpa [nPairs] using this

theorem finrank_Wsub_cases [FiniteDimensional K A] (hdim : finrank K A = 2) (hr : r = 3)
    (hnt : ∃ j, ¬ TrivOn S j) (htr : ∃ j, TrivOn S j) :
    finrank K (Wsub (K := K) (A := A) S) = 4 ∨ finrank K (Wsub (K := K) (A := A) S) = 6 := by
  have h2 := finrank_Wsub (K := K) (A := A) (S := S)
  rw [nNontriv_eq, hdim] at h2
  have h3 := one_le_nPairs hnt
  have h4 := nPairs_lt htr
  omega

theorem exists_nontrivial_eichler_Wsub [FiniteDimensional K A] (hdim : finrank K A = 2) {i : Fin r}
    (hi : TrivOn S (Sum.inl i)) :
    ∃ u w : Wsub (K := K) (A := A) S, ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) u = 0 ∧
      polar ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) u w = 0 ∧
      eichler ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) u w ≠ 1 := by
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
    have : Nontrivial A := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    exact exists_ne 0
  have hi' : TrivOn S (Sum.inr i) := hi.swap S
  refine ⟨⟨hypVec K A (Sum.inl i), hypVec_mem_Wsub hi⟩, ⟨((0 : Fin r ⊕ Fin r → K), a), tail_mem_Wsub a⟩,
    quadTail_hypVec _, ?_, fun h => ?_⟩
  · rw [polar_restrict]
    exact polar_hypVec_tail _ a
  · have hu : quadTail r qA (hypVec K A (Sum.inl i)) = 0 := quadTail_hypVec _
    have hw : polar (quadTail r qA) (hypVec K A (Sum.inl i)) ((0 : Fin r ⊕ Fin r → K), a) = 0 :=
      polar_hypVec_tail _ a
    have h1 := coe_eichler_restrict hu hw (hypVec_mem_Wsub hi) (tail_mem_Wsub a)
      ⟨hypVec K A (Sum.inr i), hypVec_mem_Wsub hi'⟩
    rw [h] at h1
    have h1' : hypVec K A (Sum.inr i) = eichler (quadTail r qA) (hypVec K A (Sum.inl i))
        ((0 : Fin r ⊕ Fin r → K), a) (hypVec K A (Sum.inr i)) := h1
    rw [eichler_apply hu hw] at h1'
    have h2 := congrArg Prod.snd h1'
    simp [hypVec_snd] at h2
    have h3 : polar (quadTail r qA) (hypVec K A (Sum.inr i)) (hypVec K A (Sum.inl i)) = 1 := by
      rw [polar_hypVec_hypVec]
      simp
    rw [h3, one_smul] at h2
    exact ha h2.symm

variable (qA S) in
@[expose] def hypPairW {i : Fin r} (hi : TrivOn S (Sum.inl i)) :
    HypPair ((quadTail r qA).restrict (Wsub (K := K) (A := A) S)) where
  e := ⟨hypVec K A (Sum.inl i), hypVec_mem_Wsub hi⟩
  f := ⟨hypVec K A (Sum.inr i), hypVec_mem_Wsub (hi.swap S)⟩
  Q_e := quadTail_hypVec _
  Q_f := quadTail_hypVec _
  polar_ef := by
    rw [polar_restrict]
    exact (hypPairT r qA i).polar_ef

variable [Finite K] [CharP K 2] [FiniteDimensional K A]

theorem mem_Rts_of_fix_nontriv (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (hr : r = 3) (hnt : ∃ j, ¬ TrivOn S j) (htr : ∃ j, TrivOn S j)
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} (hg : g ∈ Om qA r)
    (hgf : ∀ j, ¬ TrivOn S j → g (hypVec K A j) = hypVec K A j) : g ∈ Rts qA S := by
  have hr3 : 3 ≤ r := by omega
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have hS := nondegenerate_polarBilin_restrict (polarNondegOn_Wsub (S := S) hreg)
  have hgO := Om_le_orth hg
  have hgΩ : g ∈ omegaGroup (quadTail r qA) hQ := by
    rw [← Om_eq_omega hreg hr3]
    exact hg
  have hEΩ : elementaryGroup (quadTail r qA) ≤ omegaGroup (quadTail r qA) hQ := by
    rw [← Om_eq_omega hreg hr3, ← Om_eq_elementary hreg hr3]
  obtain ⟨i, hi⟩ := exists_pair_trivial htr
  have hgW := supp_Wsub (S := S) hgO hgf
  have hfix : ∀ z, (∀ x ∈ Wsub (K := K) (A := A) S, polar (quadTail r qA) z x = 0) → g z = z :=
    fun z hz => fix_perp_Wsub hreg hgf hz
  have hg'Ω := resAut_mem_omega hS hgΩ hgW hfix
  have hEΩ' := elementary_restrict_le_omega hS hEΩ
  have hDE := omega_le_elementary_small hS (finrank_Wsub_cases hdim hr hnt htr)
    (fun U hU => hts_Wsub hani hdim U hU) hEΩ' (exists_nontrivial_eichler_Wsub hdim hi)
  have hg'E := hDE hg'Ω
  have he := isRootCenter_Hsub (qA := qA) hi
  have hf := isRootCenter_Hsub (qA := qA) (hi.swap S)
  have hH := elementaryGroup_le_of_hypPair hS Hsub_le_orth (hypPairW qA S hi) he hf
  obtain ⟨h, hh, hx, hz⟩ := hH hg'E
  have : g = h := eq_of_agree_on' hS (fun x hx' => (hx ⟨x, hx'⟩).symm) hfix hz
  rw [this]
  exact hh

end CFSG.RankThree.PartOne.K159H
