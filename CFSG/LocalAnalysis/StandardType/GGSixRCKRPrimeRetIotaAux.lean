module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxNormTwo
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Timmesfeld

theorem rckIo_cartan_diag_E6 (i : Fin Tag.E6.rank) : Tag.E6.cartan i i = 2 := by
  fin_cases i <;> decide

theorem rckIo_cartan_offDiag_E6 (i j : Fin Tag.E6.rank) (h : i ≠ j) :
    Tag.E6.cartan i j ≤ 0 := by
  fin_cases i <;> fin_cases j <;> (first | exact absurd rfl h | decide)

theorem rckIo_cartan_edge_E6 (c d : Fin Tag.E6.rank) (h : edgeE 6 c d) :
    Tag.E6.cartan c d = -1 := by
  fin_cases c <;> fin_cases d <;> (first | decide | simp_all [edgeE])

theorem rckIo_cartan_nonedge_E6 (c d : Fin Tag.E6.rank) (hcd : c ≠ d)
    (h : ¬ edgeE 6 c d) (h' : ¬ edgeE 6 d c) : Tag.E6.cartan c d = 0 := by
  fin_cases c <;> fin_cases d <;> (first | decide | simp_all [edgeE])

theorem rckIo_cartan_comm_E6 (c d : Fin Tag.E6.rank) : Tag.E6.cartan c d = Tag.E6.cartan d c := by
  fin_cases c <;> fin_cases d <;> rfl

theorem rckIo_symmetrizer_diag_E6 (i : Fin Tag.E6.rank) : Tag.E6.symmetrizer i i = 1 := by
  simp [Tag.symmetrizer]

theorem rckIo_symmetrizedCartan_eq_E6 (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
  simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem rckIo_iform_single_left_eq_E6
    (i : Fin Tag.E6.rank) (u : Fin Tag.E6.rank → ℤ) :
    iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) u = ∑ j, Tag.E6.cartan i j * u j := by
  rw [iform_single_left, rckIo_symmetrizer_diag_E6, one_mul]

theorem rckIo_iform_single_single_eq_E6
    (i : Fin Tag.E6.rank) :
    iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single i 1) = 2 := by
  rw [iform_single_single, rckIo_symmetrizer_diag_E6]
  ring

theorem rckIo_iform_self_eq_sum_E6
    (u : Fin Tag.E6.rank → ℤ) :
    iform u u = ∑ i, u i * ∑ j, Tag.E6.cartan i j * u j := by
  simp only [iform, rckIo_symmetrizedCartan_eq_E6, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rckIo_iform_self_nonneg
    {τ : Tag} (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem rckIo_even_iform_self_E6
    (v : Fin Tag.E6.rank → ℤ) : Even (iform v v) := by
  classical
  have key : ∀ S : Finset (Fin Tag.E6.rank),
      Even (iform (∑ i ∈ S, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
        (∑ i ∈ S, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [iform]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      set x : Fin Tag.E6.rank → ℤ := ∑ i ∈ S, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
        with hx
      set y : Fin Tag.E6.rank → ℤ := v a • (Pi.single a 1 : Fin Tag.E6.rank → ℤ) with hy
      have h1 : iform (y + x) (y + x) = iform y y + 2 * iform y x + iform x x := by
        rw [iform_add_left, iform_add_right, iform_add_right, iform_comm x y]
        ring
      have h2 : iform y y = 2 * (v a * v a) := by
        rw [hy, iform_smul_left, iform_smul_right, rckIo_iform_single_single_eq_E6]
        ring
      rw [h1, h2]
      exact ((even_two_mul _).add (even_two_mul _)).add ih
  have hv : ∑ i ∈ (Finset.univ : Finset (Fin Tag.E6.rank)),
      v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [hv] at this

theorem rckIo_isRoot_of_nonneg_iform_eq_two_E6 :
    ∀ (n : ℕ) (u : Fin Tag.E6.rank → ℤ), (∀ i, 0 ≤ u i) → iform u u = 2 →
      ∑ i, u i = n → IsRoot Tag.E6 u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu0 hu2 hun
    classical
    have hsum : ∑ i, u i * ∑ j, Tag.E6.cartan i j * u j = 2 := by
      rw [← rckIo_iform_self_eq_sum_E6 u]
      exact hu2
    obtain ⟨i, hi⟩ : ∃ i, 0 < u i * ∑ j, Tag.E6.cartan i j * u j := by
      by_contra h
      push Not at h
      have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
      omega
    have hui : 0 < u i := by
      rcases (hu0 i).lt_or_eq with h | h
      · exact h
      · rw [← h] at hi
        simp at hi
    have hk : 0 < ∑ j, Tag.E6.cartan i j * u j := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (hu0 i) h
      omega
    set k : ℤ := ∑ j, Tag.E6.cartan i j * u j with hkdef
    have hpair : iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) u = k :=
      rckIo_iform_single_left_eq_E6 i u
    have hrefl : reflect Tag.E6 i u = u - k • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := rfl
    by_cases hcase : k ≤ u i
    · have hv0 : ∀ j, 0 ≤ reflect Tag.E6 i u j := by
        intro j
        rw [hrefl]
        by_cases hj : j = i
        · subst hj
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, if_true, smul_eq_mul, mul_one]
          omega
        · simp [Pi.single_apply, hj, hu0 j]
      have hv2 : iform (reflect Tag.E6 i u) (reflect Tag.E6 i u) = 2 := by
        rw [iform_reflect, hu2]
      have hvsum : ∑ j, reflect Tag.E6 i u j = (n : ℤ) - k := by
        rw [hrefl]
        simp [Finset.sum_sub_distrib, hun, Pi.single_apply]
      have hvnn : 0 ≤ ∑ j, reflect Tag.E6 i u j := Finset.sum_nonneg fun j _ => hv0 j
      have hlt : (∑ j, reflect Tag.E6 i u j).toNat < n := by omega
      have hroot := ih _ hlt (reflect Tag.E6 i u) hv0 hv2 (Int.toNat_of_nonneg hvnn).symm
      have := IsRoot.reflect i hroot
      rwa [reflect_reflect] at this
    · push Not at hcase
      have hk2 : 2 ≤ k := by omega
      set w : Fin Tag.E6.rank → ℤ := u - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) with hw
      have hww : iform w w = 4 - 2 * k := by
        rw [hw, iform_sub_left, iform_sub_right, iform_sub_right,
          iform_comm u (Pi.single i 1), hpair, hu2, rckIo_iform_single_single_eq_E6]
        ring
      have hnn := rckIo_iform_self_nonneg w
      have hk2' : k = 2 := by omega
      have hw0 : w = 0 := by
        by_contra hne
        have := iform_self_pos hne
        omega
      have : u = Pi.single i 1 := by
        rw [hw] at hw0
        exact sub_eq_zero.1 hw0
      rw [this]
      exact IsRoot.basis i

theorem rckIo_isRoot_E6_of_iform_self_eq_two
    {u : Fin Tag.E6.rank → ℤ} (hu : iform u u = 2) :
    IsRoot Tag.E6 u := by
  classical
  obtain ⟨up, um, hu_eq, hup0, hum0, hdisj⟩ : ∃ up um : Fin Tag.E6.rank → ℤ, u = up - um ∧
      (∀ i, 0 ≤ up i) ∧ (∀ i, 0 ≤ um i) ∧ ∀ i, up i * um i = 0 := by
    refine ⟨fun i => ((u i).toNat : ℤ), fun i => ((-u i).toNat : ℤ), ?_, fun i => by simp,
      fun i => by simp, fun i => ?_⟩
    · ext i
      simp only [Pi.sub_apply]
      omega
    · rcases le_total 0 (u i) with h | h
      · have : (-u i).toNat = 0 := by omega
        simp [this]
      · have : (u i).toNat = 0 := by omega
        simp [this]
  subst hu_eq
  have hcross : iform up um ≤ 0 := by
    unfold iform
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    rw [rckIo_symmetrizedCartan_eq_E6]
    by_cases hij : i = j
    · subst hij
      rw [rckIo_cartan_diag_E6]
      have := hdisj i
      nlinarith
    · have h1 : 0 ≤ up i * um j := mul_nonneg (hup0 i) (hum0 j)
      have h2 := rckIo_cartan_offDiag_E6 i j hij
      nlinarith
  have hexp : iform (up - um) (up - um) = iform up up + iform um um - 2 * iform up um := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm um up]
    ring
  rw [hexp] at hu
  have hor : up = 0 ∨ um = 0 := by
    by_contra h
    push Not at h
    have h1 := iform_self_pos h.1
    have h2 := iform_self_pos h.2
    obtain ⟨a, ha⟩ := rckIo_even_iform_self_E6 up
    obtain ⟨b, hb⟩ := rckIo_even_iform_self_E6 um
    omega
  rcases hor with h | h
  · subst h
    have hn : iform um um = 2 := by
      have : iform (0 : Fin Tag.E6.rank → ℤ) 0 = 0 := by simp [iform]
      have h0 : iform (0 : Fin Tag.E6.rank → ℤ) um = 0 := by simp [iform]
      rw [this, h0] at hu
      linarith
    have := rckIo_isRoot_of_nonneg_iform_eq_two_E6 (∑ i, um i).toNat um hum0 hn
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hum0 i)).symm
    have h2 := IsRoot.neg this
    simpa using h2
  · subst h
    have hn : iform up up = 2 := by
      have : iform (0 : Fin Tag.E6.rank → ℤ) 0 = 0 := by simp [iform]
      have h0 : iform up (0 : Fin Tag.E6.rank → ℤ) = 0 := by simp [iform]
      rw [this, h0] at hu
      linarith
    have := rckIo_isRoot_of_nonneg_iform_eq_two_E6 (∑ i, up i).toNat up hup0 hn
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hup0 i)).symm
    simpa using this

theorem rckIo_iform_self_eq_two_sl
    {τ : Tag} (hτ : CFSG.HardMathSupport.Timmesfeld.LangTorus.SimplyLacedTag τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rw [hj, CFSG.HardMathSupport.Timmesfeld.LangTorus.symmetrizer_eq_one_of_simplyLaced hτ]
  norm_num

@[expose] def rckIo_L {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (v : Fin Tag.E6.rank → ℤ) :
    Fin τ.rank → ℤ :=
  ∑ k, v k • β k

theorem rckIo_L_single {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (c : Fin Tag.E6.rank) :
    rckIo_L β (Pi.single c 1) = β c := by
  rw [rckIo_L, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem rckIo_L_add {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (u v : Fin Tag.E6.rank → ℤ) :
    rckIo_L β (u + v) = rckIo_L β u + rckIo_L β v := by
  ext i
  simp only [rckIo_L, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem rckIo_L_neg {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (u : Fin Tag.E6.rank → ℤ) :
    rckIo_L β (-u) = -rckIo_L β u := by
  ext i
  simp only [rckIo_L, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem rckIo_L_sub {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (u v : Fin Tag.E6.rank → ℤ) :
    rckIo_L β (u - v) = rckIo_L β u - rckIo_L β v := by
  rw [sub_eq_add_neg, rckIo_L_add, rckIo_L_neg, sub_eq_add_neg]

theorem rckIo_L_smul {τ : Tag} (β : Fin Tag.E6.rank → Fin τ.rank → ℤ) (c : ℤ)
    (v : Fin Tag.E6.rank → ℤ) :
    rckIo_L β (c • v) = c • rckIo_L β v := by
  rw [rckIo_L, rckIo_L, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

theorem rckIo_iform_E6_eq
    (u v : Fin Tag.E6.rank → ℤ) :
    (CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) u v) =
      ∑ i, ∑ j, u i * Tag.E6.cartan i j * v j := by
  simp only [iform, rckIo_symmetrizedCartan_eq_E6, Finset.mul_sum]

theorem rckIo_L_iform {τ : Tag}
    {β : Fin Tag.E6.rank → Fin τ.rank → ℤ}
    (hgram : ∀ c d : Fin Tag.E6.rank, iform (β c) (β d) = Tag.E6.cartan c d)
    (u v : Fin Tag.E6.rank → ℤ) :
    iform (rckIo_L β u) (rckIo_L β v) =
      (CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) u v) := by
  rw [rckIo_L, rckIo_L]
  calc iform (∑ c, u c • β c) (∑ d, v d • β d)
      = ∑ c, iform (u c • β c) (∑ d, v d • β d) := by
        rw [iform_finset_sum_left]
    _ = ∑ c, ∑ d, iform (u c • β c) (v d • β d) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [iform_finset_sum_right]
    _ = ∑ c, ∑ d, u c * (v d * iform (β c) (β d)) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [iform_smul_left, iform_smul_right]
    _ = ∑ c, ∑ d, u c * Tag.E6.cartan c d * v d := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [hgram c d]
        ring
    _ = (CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6) u v) := by
        rw [rckIo_iform_E6_eq]

theorem rckIo_L_inj {τ : Tag}
    {β : Fin Tag.E6.rank → Fin τ.rank → ℤ}
    (hgram : ∀ c d : Fin Tag.E6.rank, iform (β c) (β d) = Tag.E6.cartan c d)
    {u v : Fin Tag.E6.rank → ℤ}
    (h : rckIo_L β u = rckIo_L β v) : u = v := by
  have hw : rckIo_L β (u - v) = 0 := by
    rw [rckIo_L_sub, h, sub_self]
  have h0 : iform (rckIo_L β (u - v)) (rckIo_L β (u - v)) = 0 := by
    rw [hw]; simp [iform]
  rw [rckIo_L_iform hgram] at h0
  have huv : u - v = 0 := by
    by_contra hne
    exact absurd h0 (ne_of_gt (iform_self_pos hne))
  exact sub_eq_zero.1 huv

theorem rckIo_coord_rootDiagUnit
    {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) : rckTorusCoord (rootDiagUnit τ a) = a := by
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective ?_
  exact Function.invFun_eq (f := rootDiagUnitHom τ L) ⟨a, rfl⟩

theorem rckIo_rootChar_smul {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (n : ℤ)
    (v : Fin τ.rank → ℤ) : rootChar a (n • v) = rootChar a v ^ n := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul, mul_comm]

theorem rckIo_rootChar_sum {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    {ι : Type} (s : Finset ι) (n : ι → ℤ) (v : ι → Fin τ.rank → ℤ) :
    rootChar a (∑ k ∈ s, n k • v k) = ∏ k ∈ s, (rootChar a (v k)) ^ (n k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootChar_zero]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, rootChar_add, rckIo_rootChar_smul, ih]

theorem rckIo_rootChar_single {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (k : Fin τ.rank) : rootChar a (Pi.single k 1) = a k := by
  simpa using rootChar_nsmul_single a k 1

theorem rckIo_sum_single {κ : Type} [Fintype κ] [DecidableEq κ] (n : κ → ℤ) :
    (∑ k, n k • (Pi.single k 1 : κ → ℤ)) = n := by
  ext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CFSG.StandardType.RCKRP

end
