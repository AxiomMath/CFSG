module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LieType.Universal.SymplecticExtras.Unipotent
public import CFSG.LieType.Universal.SymplecticExtras.Torus
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations
import all CFSG.LieType.Universal.SymplecticRoots
import all CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
open scoped Pointwise

namespace GGRootSp

variable {n : ℕ} {F : Type} [Field F]

theorem lvl_injective : Function.Injective (lvl (n := n)) := by
  rintro (i | i) (j | j) h <;> simp only [lvl] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := j.isLt
    omega
  · have := i.isLt
    omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem bruhatExtras : BruhatExtras (rootDatum n F) (torus n F) := by
  have hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix (rootDatum n F).isFiniteType).toCoxeterSystem
      (weylAction (rootDatum n F).isFiniteType) (rootDatum n F).roots (rootDatum n F).rootGroup
      (weylRep n F) (torus n F) := isCTGroupDatum n F
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have hneg : IdBelow (fun a => (-1 : ℤ) * lvl a) 1 (mat n F x) :=
    idBelow_of_mem_iSup (-1) _ (fun γ hγ => ⟨hγ.1, by
      have h : ht (ι := Fin n) γ < 0 := hγ.2
      omega⟩) hxN
  obtain ⟨t, htT, u, hu, rfl⟩ := (Set.ext_iff.1 (coe_borel hct) x).1 hxB
  obtain ⟨d, rfl⟩ := exists_diagonal_of_mem_iSup_torus (n := n) htT
  have hu' : IdBelow (fun a => (1 : ℤ) * lvl a) 1 (mat n F u) :=
    idBelow_of_mem_iSup 1 _ (fun γ hγ => ⟨hγ.1, by
      have h : 0 < ht (ι := Fin n) γ := hγ.2
      omega⟩) hu
  refine eq_one_of_idBelow (fun a b hab => ?_) hneg
  have hmat : mat n F (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal d) * u) =
      Matrix.diagonal (Sum.elim (fun i => (d i : F)) (fun i => (((d i)⁻¹ : Fˣ) : F))) *
        mat n F u := by
    rw [map_mul, mat_equiv_diagonal]
  rw [hmat, Matrix.diagonal_mul]
  rcases lt_or_eq_of_le (show lvl b ≤ lvl a by linarith) with h | h
  · rw [hu' a b (by linarith), Matrix.one_apply_ne (fun e => by rw [e] at h; exact lt_irrefl _ h),
      mul_zero]
  · obtain rfl : b = a := lvl_injective h
    have h1 := hneg b b (by simp)
    rw [hmat, Matrix.diagonal_mul] at h1
    exact h1

theorem isPGroup_rootGroup [CharP F 2] {γ : Fin (rootDatum n F).rank → ℤ}
    (hγ : γ ∈ (rootDatum n F).roots) : IsPGroup 2 ((rootDatum n F).rootGroup γ) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  change IsPGroup 2 (rootGroup n F γ)
  rw [rootGroup_eq_range hr]
  exact isPGroup_two_range_of_charTwo _

theorem rootGroup_mul_comm {γ : Fin (rootDatum n F).rank → ℤ}
    (hγ : γ ∈ (rootDatum n F).roots) :
    ∀ x ∈ (rootDatum n F).rootGroup γ, ∀ y ∈ (rootDatum n F).rootGroup γ, x * y = y * x := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  change ∀ x ∈ rootGroup n F γ, ∀ y ∈ rootGroup n F γ, x * y = y * x
  rw [rootGroup_eq_range hr]
  exact range_mul_comm _

theorem coprime_two_card_torus [Finite F] [CharP F 2] :
    Nat.Coprime 2 (Nat.card (⨆ i, torus n F i : Subgroup (StatedSp n F))) := by
  refine coprime_two_card_of_sq_eq_one _ fun g hg hg2 => ?_
  obtain ⟨d, rfl⟩ := exists_diagonal_of_mem_iSup_torus (n := n) hg
  have h1 : TauCeti.GLSymplecticFin.diagonal (d ^ 2) = 1 := by
    apply (equivStatedSp n F).injective
    rw [map_pow, map_pow, map_one]
    exact hg2
  have h2 : d ^ 2 = 1 := TauCeti.GLSymplecticFin.diagonal_injective (by rw [h1, map_one])
  have h3 : d = 1 := by
    funext i
    have hi := congrFun h2 i
    refine Units.ext (GGRootSL.eq_one_of_mul_self_eq_one ?_)
    have := congrArg (fun u : Fˣ => (u : F)) hi
    simpa [pow_two] using this
  rw [h3, map_one, map_one]

theorem exists_root_toStd_eq (r : RootSubgroupIndex n) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, toStd n γ = stdVec r := by
  obtain ⟨w, k, h⟩ := isStdOrbit_stdVec n r
  exact ⟨_, Or.inl ⟨w, k, rfl⟩, h⟩

theorem lv_stdVec_le (r : RootSubgroupIndex n) : lv n (stdVec r) ≤ 2 * (2 * n - 1) := by
  cases r with
  | positiveLong i =>
    have := i.isLt
    rw [stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    omega
  | negativeLong i =>
    have := i.isLt
    rw [stdVec, map_neg, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    omega
  | difference i j hij =>
    have := i.isLt
    have := j.isLt
    simp only [stdVec, map_sub, lv_single]
    omega
  | positiveSum i j hij =>
    have := i.isLt
    have := j.isLt
    simp only [stdVec, map_add, lv_single]
    omega
  | negativeSum i j hij =>
    have := i.isLt
    have := j.isLt
    simp only [stdVec, map_neg, map_add, lv_single]
    omega

theorem stdVec_eq_of_lv_lt (hn : 2 ≤ n) (r : RootSubgroupIndex n)
    (h : 4 * (n : ℤ) - 4 < lv n (stdVec r)) :
    stdVec r = stdVec (RootSubgroupIndex.positiveLong ⟨0, by omega⟩) := by
  cases r with
  | positiveLong i =>
    have hi : i = ⟨0, by omega⟩ := by
      have := i.isLt
      rw [stdVec, map_nsmul, lv_single, nsmul_eq_mul] at h
      push_cast at h
      exact Fin.ext (by simp only; omega)
    rw [hi]
  | negativeLong i =>
    have := i.isLt
    rw [stdVec, map_neg, map_nsmul, lv_single, nsmul_eq_mul] at h
    push_cast at h
    omega
  | difference i j hij =>
    have := i.isLt
    have := j.isLt
    simp only [stdVec, map_sub, lv_single] at h
    omega
  | positiveSum i j hij =>
    have := i.isLt
    have := j.isLt
    have hij' : i.val < j.val := hij
    simp only [stdVec, map_add, lv_single] at h
    omega
  | negativeSum i j hij =>
    have := i.isLt
    have := j.isLt
    simp only [stdVec, map_neg, map_add, lv_single] at h
    omega

@[expose] def AllEven (e : Fin n → ℤ) : Prop := ∀ a, Even (e a)

private theorem allEven_stdRefl_iff (k : Fin n) (e : Fin n → ℤ) :
    AllEven (stdRefl n k e) ↔ AllEven e := by
  by_cases h : k.val + 1 < n
  · rw [stdRefl_of_lt n h]
    refine ⟨fun he a => ?_, fun he a => he _⟩
    have := he (Equiv.swap k ⟨k.val + 1, h⟩ a)
    simpa [Function.comp_apply, Equiv.swap_apply_self] using this
  · rw [stdRefl_of_not_lt n h]
    refine ⟨fun he a => ?_, fun he a => ?_⟩
    · have := he a
      simp only at this
      split_ifs at this with ha
      · simpa using this
      · simpa using this
    · simp only
      split_ifs
      · simpa using he a
      · simpa using he a

theorem allEven_toStd_weylAction_iff (w : (coxeterMatrix (isFiniteType_cartanC n)).Group)
    (v : Fin n → ℤ) :
    AllEven (toStd n (weylAction (isFiniteType_cartanC n) w v)) ↔ AllEven (toStd n v) := by
  induction w using (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple_induction_left
    with
  | one => rw [map_one, Module.End.one_apply]
  | mul_simple_left w l ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection, allEven_stdRefl_iff, ih]

theorem allEven_toStd_single_iff (k : Fin n) :
    AllEven (toStd n (Pi.single k 1)) ↔ ¬ k.val + 1 < n := by
  by_cases h : k.val + 1 < n
  · rw [toStd_single_of_lt n h]
    refine iff_of_false (fun he => ?_) (not_not.2 h)
    have := he k
    have hne : k ≠ ⟨k.val + 1, h⟩ := Fin.ne_of_val_ne (by simp)
    simp [hne] at this
  · rw [toStd_single_of_not_lt n h]
    refine iff_of_true (fun a => ?_) h
    by_cases ha : a = k
    · subst ha
      simp
    · simp [ha]

theorem ggSimpleConj_short {k k' : Fin (rootDatum n F).rank} (hk : k.val + 1 < n)
    (hk' : k'.val + 1 < n) : GGSimpleConj (rootDatum n F) k k' := by
  have hr : (rootDatum n F).rank = n := rfl
  have hadj : ∀ j : ℕ, ∀ hj : j + 2 < n,
      GGSimpleConj (rootDatum n F) ⟨j, by omega⟩ ⟨j + 1, by omega⟩ := fun j hj =>
    ggSimpleConj_of_cartan_eq
      (show cartanC n ⟨j, by omega⟩ ⟨j + 1, by omega⟩ = -1 by
        rw [cartanC_of_succ n rfl, ite_eq_right (by simp only; omega)])
      (show cartanC n ⟨j + 1, by omega⟩ ⟨j, by omega⟩ = -1 from cartanC_of_pred n rfl)
  have h0 : ∀ j : ℕ, ∀ hj : j + 1 < n,
      GGSimpleConj (rootDatum n F) ⟨0, by omega⟩ ⟨j, by omega⟩ := by
    intro j
    induction j with
    | zero => exact fun _ => GGSimpleConj.refl _
    | succ j ih => exact fun hj => (ih (by omega)).trans (hadj j hj)
  exact (h0 k.val hk).symm.trans (h0 k'.val hk')

theorem exists_weylAction_theta_or_thetaS {θ θs γ : Fin (rootDatum n F).rank → ℤ}
    (hθ : θ ∈ (rootDatum n F).roots) (hθs : θs ∈ (rootDatum n F).roots)
    (hθe : AllEven (toStd n θ)) (hθso : ¬ AllEven (toStd n θs)) (hγ : γ ∈ (rootDatum n F).roots) :
    ∃ w, ∃ c ∈ ({θ, θs} : Set (Fin (rootDatum n F).rank → ℤ)),
      γ = weylAction (rootDatum n F).isFiniteType w c := by
  rcases hθ with ⟨wθ, kθ, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  rcases hθs with ⟨ws, ks, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  rcases hγ with ⟨w, k, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hkθ : ¬ kθ.val + 1 < n :=
    (allEven_toStd_single_iff kθ).1 ((allEven_toStd_weylAction_iff wθ _).1 hθe)
  have hks : ks.val + 1 < n := by
    by_contra h
    exact hθso ((allEven_toStd_weylAction_iff ws _).2 ((allEven_toStd_single_iff ks).2 h))
  by_cases hk : k.val + 1 < n
  · obtain ⟨v, hv⟩ := ggSimpleConj_short (F := F) hks hk
    refine ⟨w * v * ws⁻¹, _, Or.inr rfl, ?_⟩
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply, hv]
  · have hr : (rootDatum n F).rank = n := rfl
    obtain rfl : k = kθ := Fin.ext (by have := k.isLt; have := kθ.isLt; omega)
    refine ⟨w * wθ⁻¹, _, Or.inl rfl, ?_⟩
    rw [weylAction_mul_apply, weylAction_inv_apply_apply]

theorem commute_elt_difference_positiveSum [CharP F 2] {i j : Fin n} (hij : i < j) (a b : F) :
    elt (.difference i j hij.ne) a * elt (.positiveSum i j hij) b =
      elt (.positiveSum i j hij) b * elt (.difference i j hij.ne) a := by
  have h := commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit (R := F) hij.ne a b
  have h2 : (2 : F) * a * b = 0 := by rw [CharTwo.two_eq_zero, zero_mul, zero_mul]
  have h0 : positiveLongRootTransvectionUnit (R := F) i 0 = 1 := by
    have h' := positiveLongRootTransvectionUnit_add (R := F) i 0 0
    rw [add_zero] at h'
    exact mul_left_cancel (h'.symm.trans (mul_one _).symm)
  rw [h2, h0, commutatorElement_eq_one_iff_mul_comm] at h
  simp only [elt, RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_positiveSum,
    differenceShortRootHom_apply, positiveSumShortRootHom_apply, toAdd_ofAdd]
  rw [← map_mul, h, map_mul]

private theorem ht_nsmul_add (a b : ℕ) (v w : Fin n → ℤ) :
    ht (a • v + b • w) = a * ht v + b * ht w := by
  simp [ht, Finset.sum_add_distrib, Finset.mul_sum]

theorem ggRootSylowCentral_symplectic [Finite F] [CharP F 2] (hn : 2 ≤ n) (t : StatedLieTag) :
    GGRootSylowCentral (rootDatum n F) t := by
  have hr : (rootDatum n F).rank = n := rfl
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have h01 : i0 < i1 := by rw [Fin.lt_def]; simp [i0, i1]
  obtain ⟨θ, hθ, hθstd⟩ := exists_root_toStd_eq (n := n) (.positiveLong i0)
  obtain ⟨θs, hθs, hθsstd⟩ := exists_root_toStd_eq (n := n) (.positiveSum i0 i1 h01)
  have hlv0 : lv n (Pi.single i0 1) = 2 * n - 1 := by rw [lv_single]; simp [i0]
  have hlv1 : lv n (Pi.single i1 1) = 2 * n - 3 := by rw [lv_single]; simp [i1]; ring
  have hhtθ : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, hlv0, nsmul_eq_mul]
    push_cast
    ring
  have hhtθs : 2 * ht θs = 4 * n - 4 := by
    rw [two_mul_ht, hθsstd, stdVec, map_add, hlv0, hlv1]
    ring
  have hmax : ∀ δ : Fin n → ℤ, δ ∈ roots (isFiniteType_cartanC n) ∅ → ht δ ≤ ht θ := by
    intro δ hδ
    obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hδ
    have h1 := two_mul_ht (n := n) δ
    rw [← hr'] at h1
    have h2 := lv_stdVec_le r
    omega
  have hnext : ∀ ε : Fin n → ℤ, ε ∈ roots (isFiniteType_cartanC n) ∅ → ht θs < ht ε →
      ε = θ := by
    intro ε hε hlt
    obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hε
    have h1 := two_mul_ht (n := n) ε
    rw [← hr'] at h1
    have h3 := stdVec_eq_of_lv_lt hn r (by omega)
    exact toStd_inj (by rw [← hr', hθstd, h3])
  have hθspos : 0 < ht θs := by omega
  have hspec : ∀ δ : Fin n → ℤ, δ ∈ roots (isFiniteType_cartanC n) ∅ → 0 < ht δ →
      (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ θ = a • θs + b • δ) →
      ∀ x ∈ rootGroup n F θs, ∀ y ∈ rootGroup n F δ, x * y = y * x := by
    rintro δ hδ hδpos ⟨a, b, ha, hb, hab⟩ x hx y hy
    have hht := congrArg (ht (ι := Fin n)) hab
    rw [ht_nsmul_add] at hht
    have ha1 : a = 1 := by
      by_contra ha1
      have : (2 : ℤ) ≤ a := by omega
      have : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    subst ha1
    have hb1 : b = 1 := by
      have h1 : (b : ℤ) * ht δ = 1 := by push_cast at hht; linarith
      exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h1
    subst hb1
    have hδstd : toStd n δ = stdVec (.difference i0 i1 h01.ne) := by
      have := congrArg (toStd n) hab
      rw [one_smul, one_smul, toStd_add', hθstd, hθsstd] at this
      simp only [stdVec] at this ⊢
      rw [eq_sub_of_add_eq' this.symm]
      abel
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hθsstd.symm).1 hx
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff hδstd.symm).1 hy
    exact (commute_elt_difference_positiveSum h01 d c).symm
  refine ggRootSylowCentral_of_orbit (isCTGroupDatum n F) (steinbergExtras n F) bruhatExtras
    (fun _ hγ => isPGroup_rootGroup hγ) coprime_two_card_torus (C := {θ, θs}) ?_ ?_
  · rintro c (rfl | rfl)
    · exact ⟨hθ, ht_pos_of_maxHeight hθ hmax,
        posUnipotent_le_centralizer_of_maxHeight (steinbergExtras n F) hθ hmax
          (rootGroup_mul_comm hθ)
          fun _ hδ e => absurd e (not_eq_two_smul_of_divisible_eq_empty rfl hδ hθ)⟩
    · exact ⟨hθs, hθspos, posUnipotent_le_centralizer_of_nextHeight (steinbergExtras n F) rfl
        hθs hθspos hnext (rootGroup_mul_comm hθs) hspec⟩
  · intro γ hγ
    refine exists_weylAction_theta_or_thetaS hθ hθs ?_ ?_ hγ.1
    · rw [hθstd]
      intro a
      simp only [stdVec, Pi.smul_apply, Pi.single_apply]
      split_ifs <;> simp
    · rw [hθsstd]
      intro h
      have := h i0
      simp [stdVec, ne_of_lt h01] at this

end GGRootSp

end CFSG.StandardType
