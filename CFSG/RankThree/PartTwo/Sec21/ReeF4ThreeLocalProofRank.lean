module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofWeyl
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofF4
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.RankThree.PartOne.BRANCH.RankArith
public import CFSG.RankThree.PartOne.BRANCH.RankSylow
public import CFSG.RankThree.PartOne.N143X.ReeRank

public section

namespace CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.BRANCH
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.LargeReeOrder
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Certs


@[expose] def sOf (a : ℕ) : ℤ := if Even a then 1 else 2

theorem sOf_mem (a : ℕ) : sOf a = 1 ∨ sOf a = 2 := by
  unfold sOf
  split_ifs <;> simp

theorem three_dvd_two_pow_sub_sOf (a : ℕ) : (3 : ℤ) ∣ 2 ^ a - sOf a := by
  have h := CFSG.RankThree.PartOne.BRANCH.two_pow_mod_three a
  unfold sOf
  rcases h with ⟨h1, he⟩ | ⟨h2, ho⟩
  · simp only [he, ↓reduceIte]
    have : ((2 ^ a : ℕ) : ℤ) % 3 = 1 := by exact_mod_cast h1
    push_cast at this
    exact Int.dvd_iff_emod_eq_zero.2 (by omega)
  · simp only [Nat.not_even_iff_odd.2 ho, ↓reduceIte]
    have : ((2 ^ a : ℕ) : ℤ) % 3 = 2 := by exact_mod_cast h2
    push_cast at this
    exact Int.dvd_iff_emod_eq_zero.2 (by omega)

theorem three_dvd_dot4_uPhi2_sub (a : ℕ) (t : Fin 2) (v : Fin 4 → ℤ) :
    (3 : ℤ) ∣ dot4 (uPhi2 a t) v - dot4 (uBar (sOf a) t) v := by
  obtain ⟨k, hk⟩ := three_dvd_two_pow_sub_sOf a
  fin_cases t
  · refine ⟨-(k * v 3), ?_⟩
    simp [uPhi2, uBar, dot4]
    linear_combination (-(v 3)) * hk
  · refine ⟨-(k * v 2), ?_⟩
    simp [uPhi2, uBar, dot4]
    linear_combination (-(v 2)) * hk

theorem dot4_single (u : Fin 4 → ℤ) (j : Fin 4) : dot4 u (Pi.single j 1) = u j := by
  fin_cases j <;> simp [dot4]

variable {L : Type} [Field L]

theorem rootChar_expTuple_left (a : ℕ) (ξ : Lˣ) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple ξ 1 (uPhi2 a)) v = ξ ^ dot4 (uPhi2 a 0) v := by
  rw [rootChar_expTuple ξ 1 (uPhi2 a) v, one_zpow, mul_one]
  show ξ ^ (∑ i : Fin 4, uPhi2 a 0 i * v i) = _
  rw [Fin.sum_univ_four]
  rfl

theorem rootChar_expTuple_right (a : ℕ) (ξ : Lˣ) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (expTuple 1 ξ (uPhi2 a)) v = ξ ^ dot4 (uPhi2 a 1) v := by
  rw [rootChar_expTuple 1 ξ (uPhi2 a) v, one_zpow, one_mul]
  show ξ ^ (∑ i : Fin 4, uPhi2 a 1 i * v i) = _
  rw [Fin.sum_univ_four]
  rfl

@[expose] def torsionPair (a : ℕ) (ζ : Lˣ) : Set (Fin ReeTag.F4.tag.rank → Lˣ) :=
  {expTuple ζ 1 (uPhi2 a), expTuple 1 ζ (uPhi2 a)}

theorem exists_mem_torsionPair (a : ℕ) (ζ : Lˣ) (t : Fin 2) :
    ∃ b ∈ torsionPair a ζ, ∀ v : Fin ReeTag.F4.tag.rank → ℤ,
      rootChar b v = ζ ^ dot4 (uPhi2 a t) v := by
  fin_cases t
  · exact ⟨_, Set.mem_insert _ _, rootChar_expTuple_left a ζ⟩
  · exact ⟨_, Set.mem_insert_of_mem _ rfl, rootChar_expTuple_right a ζ⟩

theorem famKernel_torsionPair (a : ℕ) {ζ : Lˣ} (hζ : ∀ N : ℤ, ζ ^ N = 1 → (3 : ℤ) ∣ N) :
    famKernel (torsionPair a ζ) = ∅ := by
  ext α
  simp only [famKernel, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hα hall
  have hrow : ∀ t : Fin 2, (3 : ℤ) ∣ dot4 (uBar (sOf a) t) α := by
    intro t
    obtain ⟨b, hb, hbv⟩ := exists_mem_torsionPair a ζ t
    have h1 := hζ _ ((hbv α).symm.trans (hall b hb))
    have e := three_dvd_dot4_uPhi2_sub a t α
    have h2 : dot4 (uBar (sOf a) t) α =
        dot4 (uPhi2 a t) α - (dot4 (uPhi2 a t) α - dot4 (uBar (sOf a) t) α) := by ring
    rw [h2]
    exact dvd_sub h1 e
  exact not_three_dvd_of_isRoot (sOf_mem a) hα ⟨hrow 0, hrow 1⟩

theorem three_dvd_of_mem_famStabilizer (a : ℕ) {ζ : Lˣ} (hζ : ∀ N : ℤ, ζ ^ N = 1 → (3 : ℤ) ∣ N)
    {w : WeylGroup ReeTag.F4.tag} (hw : w ∈ famStabilizer (torsionPair a ζ))
    (j : Fin ReeTag.F4.tag.rank) (t : Fin 2) :
    (3 : ℤ) ∣ dot4 (uBar (sOf a) t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) -
      uBar (sOf a) t j := by
  obtain ⟨b, hb, hbv⟩ := exists_mem_torsionPair a ζ t
  have h := hw b hb (Pi.single j 1)
  rw [hbv, hbv] at h
  have hj : dot4 (uPhi2 a t) (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) = uPhi2 a t j :=
    dot4_single (uPhi2 a t) j
  rw [hj] at h
  have hU : (3 : ℤ) ∣ dot4 (uPhi2 a t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) -
      uPhi2 a t j := by
    refine hζ _ ?_
    rw [zpow_sub, h, mul_inv_cancel]
  have e1 := three_dvd_dot4_uPhi2_sub a t (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))
  have e2 : (3 : ℤ) ∣ uPhi2 a t j - uBar (sOf a) t j := by
    have := three_dvd_dot4_uPhi2_sub a t (Pi.single j 1 : Fin 4 → ℤ)
    rwa [dot4_single (uPhi2 a t) j, dot4_single (uBar (sOf a) t) j] at this
  have h2 : dot4 (uBar (sOf a) t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) -
      uBar (sOf a) t j =
      (dot4 (uPhi2 a t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) - uPhi2 a t j) -
        (dot4 (uPhi2 a t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ)) -
          dot4 (uBar (sOf a) t) (w • (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ))) +
          (uPhi2 a t j - uBar (sOf a) t j) := by ring
  rw [h2]
  exact dvd_add (dvd_sub hU e1) e2

section Frame

variable [CharP L 2] [IsAlgClosed L] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

omit [CharP L 2] [IsAlgClosed L] in
theorem eq_one_of_mem_rootSpan_empty {u : ModGL ReeTag.F4.tag L}
    (hu : u ∈ rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ))) : u = 1 := by
  simpa [rootSpan] using hu

omit [IsAlgClosed L] in
theorem mul_wPhi2_eq_of_mem_twistedFixed (hF : IsReeFrob a F) {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ torusGroup ReeTag.F4.tag L) {w : WeylGroup ReeTag.F4.tag}
    (hg : h * canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)) :
    w * wPhi2 = wPhi2 * ReeTag.F4.weylPerm w := by
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2 with hn
  set nw := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hnw
  have hhadj : h ∈ adjointGroup ReeTag.F4.tag L := torusGroup_le_adjointGroup' hh
  have hnwadj : nw ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨hadj', hFh⟩ := hF.map_torusGroup hh
  have hFh' : Fext F h ∈ torusGroup ReeTag.F4.tag L := by
    rw [Fext_of_mem F hadj']
    exact hFh
  have hFnw : Fext F nw =
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w) := by
    rw [Fext_of_mem F hnwadj]
    have h1 : (⟨nw, hnwadj⟩ : adjointGroup ReeTag.F4.tag L) = nrep ReeTag.F4.tag L w := rfl
    rw [h1, hF.map_nrep w]
    rfl
  have hfix := hg.2
  rw [Fext_mul F hhadj hnwadj, hFnw] at hfix
  have hm1 : MapsRootLines (h * nw) w := by
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep (R := L) w)
  have hm2 : MapsRootLines (n * (Fext F h *
      canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w)) * n⁻¹)
      (wPhi2 * ReeTag.F4.weylPerm w * wPhi2⁻¹) := by
    simpa using ((mapsRootLines_canonicalRep (R := L) wPhi2).mul
      ((mapsRootLines_of_mem_torusGroup hFh').mul
        (mapsRootLines_canonicalRep (R := L) (ReeTag.F4.weylPerm w)))).mul
      (mapsRootLines_canonicalRep (R := L) wPhi2).inv
  rw [hfix] at hm2
  have he := hm1.unique hm2
  conv_lhs => rw [he]
  group

omit [IsAlgClosed L] in
theorem mem_torusGroup_of_commute (hF : IsReeFrob a F) {ζ : Lˣ}
    (hζ : ∀ N : ℤ, ζ ^ N = 1 → (3 : ℤ) ∣ N) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2))
    (hcomm : ∀ b ∈ torsionPair a ζ,
      rootDiagUnit ReeTag.F4.tag b * g * (rootDiagUnit ReeTag.F4.tag b)⁻¹ = g) :
    g ∈ torusGroup ReeTag.F4.tag L := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := fam_factor (torsionPair a ζ) hg.1 hcomm
  rw [famKernel_torsionPair a hζ, Set.empty_inter] at hu hv
  rw [eq_one_of_mem_rootSpan_empty hu, eq_one_of_mem_rootSpan_empty hv, mul_one, mul_one] at hg ⊢
  have hwB := mul_wPhi2_eq_of_mem_twistedFixed hF hh hg
  have hw1 : w = 1 :=
    eq_one_of_weylCheck (sOf_mem a) (three_dvd_of_mem_famStabilizer a hζ hw) hwB
  rw [hw1, canonicalRep_one, mul_one]
  exact hh

theorem coord_eq_of_mem_twistedFixed (hF : IsReeFrob a F) (c : Fin 4 → Lˣ)
    (hc : rootDiagUnit ReeTag.F4.tag c ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi2)) :
    c 2 = c 0 ^ 2 ^ a ∧ c 0 * c 1 * c 2 * c 3 = c 1 ^ 2 ^ a := by
  rw [rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF wPhi2 c] at hc
  have h3 := hc (Pi.single (3 : Fin 4) 1)
  have h2 := hc (Pi.single (2 : Fin 4) 1)
  rw [wPhi2_smul_single (3 : Fin 4), CTTorus.rootChar_single (reeTuple a c) (3 : Fin 4)] at h3
  rw [wPhi2_smul_single (2 : Fin 4), CTTorus.rootChar_single (reeTuple a c) (2 : Fin 4)] at h2
  have e3 : reeTuple a c (3 : Fin 4) = c 0 ^ 2 ^ a := by
    show c (ReeTag.F4.perm (3 : Fin 4)) ^ ReeTag.F4.relationExponent a (ReeTag.F4.perm (3 : Fin 4))
      = _
    rw [relExp_long a (ReeTag.F4.perm (3 : Fin 4)) (by decide)]
    rfl
  have e2 : reeTuple a c (2 : Fin 4) = c 1 ^ 2 ^ a := by
    show c (ReeTag.F4.perm (2 : Fin 4)) ^ ReeTag.F4.relationExponent a (ReeTag.F4.perm (2 : Fin 4))
      = _
    rw [relExp_long a (ReeTag.F4.perm (2 : Fin 4)) (by decide)]
    rfl
  rw [e3] at h3
  rw [e2] at h2
  have r3 : rootChar (τ := ReeTag.F4.tag) c (w0Col 3) = c 2 := by
    show ∏ i : Fin 4, c i ^ w0Col 3 i = _
    simp [Fin.prod_univ_four, w0Col]
  have r2 : rootChar (τ := ReeTag.F4.tag) c (w0Col 2) = c 0 * c 1 * c 2 * c 3 := by
    show ∏ i : Fin 4, c i ^ w0Col 2 i = _
    simp [Fin.prod_univ_four, w0Col]
  exact ⟨r3.symm.trans h3, r2.symm.trans h2⟩

end Frame

theorem card_le_nine_of_reeGamma (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (E : Subgroup (ReeTag.F4.reeGamma K a)) (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  classical
  obtain ⟨hEcomm, hE3⟩ := hE
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Φ, hΦinj, hΦ, -, hΦF⟩ := (torusParam_phi2 D.isFrob).param
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) (AlgebraicClosure K) wPhi2 with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K) :=
    canonicalRep_mem_adjointGroup _ (AlgebraicClosure K) wPhi2
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag (AlgebraicClosure K) :=
    (h : ModGL ReeTag.F4.tag (AlgebraicClosure K)) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag (AlgebraicClosure K) := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag (AlgebraicClosure K)) = h := rfl
    rw [this, hFh]
    rfl
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, hTmem, -, hTcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hTm : Nat.card T = mPhi2 a ^ 2 := by
    rw [hTcard, card_range_of_odd (odd_mPhi2' a) Φ hΦinj]
  have horder := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).1
  have hmod3 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rcases CFSG.RankThree.PartOne.BRANCH.two_pow_mod_three (2 * a + 1) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact h
  have hQ2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hindex : ¬ 3 ^ (1 + 1) ∣ T.index := by
    have h1 := T.index_mul_card
    rw [hTm] at h1
    have h2 : ¬ 9 ∣ T.index := not_nine_dvd_ree_twisted hQ2 hmod3 (by
      rw [mPhi2] at h1
      rw [horder] at h1
      rw [mul_comm] at h1
      exact h1)
    simpa using h2
  by_contra hlt
  push Not at hlt
  have hP : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE3 x.1 x.2)⟩
  have h27 : 27 ≤ Nat.card E := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at hlt ⊢
    have hk3 : 3 ≤ k := by
      by_contra hk3
      push Not at hk3
      interval_cases k <;> norm_num at hlt
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  obtain ⟨g, E₁, hE₁E, hcard, hmem⟩ :=
    exists_conj_le_of_not_dvd_index T Nat.prime_three hindex hP
  have hE₁9 : 9 ≤ Nat.card E₁ := by
    have : (3 : ℕ) ^ 1 = 3 := by norm_num
    rw [this] at hcard
    omega
  set ψ : ReeTag.F4.reeGamma K a →* ModGL ReeTag.F4.tag (AlgebraicClosure K) :=
    (MulAut.conj g₀⁻¹).toMonoidHom.comp
      ((thetaGamma (AlgebraicClosure K) a).comp (MulAut.conj g⁻¹).toMonoidHom) with hψ
  have hψapp : ∀ x, ψ x = g₀⁻¹ * thetaGamma (AlgebraicClosure K) a (g⁻¹ * x * g) * g₀ := by
    intro x
    simp [hψ]
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g₀⁻¹).injective.comp
      ((thetaGamma_injective (K := K) (AlgebraicClosure K)).comp (MulAut.conj g⁻¹).injective)
  have hψfix : ∀ x, ψ x ∈ twistedFixed D.F n := by
    intro x
    rw [hψapp]
    exact conj_mem_twistedFixed D.F hg₀adj hFg₀ (thetaGamma_mem_adjointGroup _ _)
      (D.fext_theta _)
  have hz : ∀ y : E₁, ∃ z : (rootsOfUnity (mPhi2 a) (AlgebraicClosure K)) ×
      (rootsOfUnity (mPhi2 a) (AlgebraicClosure K)), Φ z = ψ y := by
    intro y
    obtain ⟨z, hz⟩ := (hTmem _).1 (hmem y.1 y.2)
    exact ⟨z, by rw [hz, hψapp]⟩
  choose z hzΦ using hz
  have hztors : ∀ y : E₁, z y ∈ pTors (mPhi2 a) 3 := by
    intro y
    have h1 : Φ (z y ^ 3) = 1 := by
      rw [map_pow, hzΦ, ← map_pow, hE3 _ (hE₁E y.2), map_one]
    have h2 : z y ^ 3 = 1 := hΦinj (h1.trans (map_one Φ).symm)
    rw [mem_pTors]
    exact ⟨congrArg (fun w => ((w.1 : rootsOfUnity (mPhi2 a) (AlgebraicClosure K)) :
      (AlgebraicClosure K)ˣ)) h2, congrArg (fun w => ((w.2 : rootsOfUnity (mPhi2 a)
        (AlgebraicClosure K)) : (AlgebraicClosure K)ˣ)) h2⟩
  set zt : E₁ → pTors (mPhi2 a) 3 := fun y => ⟨z y, hztors y⟩ with hzt
  have hztinj : Function.Injective zt := by
    intro y y' hyy
    have h1 : z y = z y' := congrArg Subtype.val hyy
    have h2 : ψ y = ψ y' := by rw [← hzΦ, ← hzΦ, h1]
    exact Subtype.ext (hψinj h2)
  have h3m : 3 ∣ mPhi2 a := by
    rw [mPhi2]
    omega
  have hcardT : Nat.card (pTors (L := AlgebraicClosure K) (mPhi2 a) 3) = 9 :=
    card_pTors Nat.prime_three (by norm_num) h3m
  have : Finite (pTors (L := AlgebraicClosure K) (mPhi2 a) 3) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
  have hztbij : Function.Bijective zt := by
    refine (Nat.bijective_iff_injective_and_card zt).2 ⟨hztinj, ?_⟩
    have := Nat.card_le_card_of_injective zt hztinj
    omega
  obtain ⟨ζ, hζ3, hζ⟩ := exists_pTors_elt (L := AlgebraicClosure K) Nat.prime_three (by norm_num)
    h3m
  have hζ' : ∀ N : ℤ, (ζ : (AlgebraicClosure K)ˣ) ^ N = 1 → (3 : ℤ) ∣ N := by
    intro N hN
    exact_mod_cast hζ N hN
  have hmem1 : ((ζ, 1) : (rootsOfUnity (mPhi2 a) (AlgebraicClosure K)) ×
      (rootsOfUnity (mPhi2 a) (AlgebraicClosure K))) ∈ pTors (mPhi2 a) 3 := by
    rw [mem_pTors]
    exact ⟨hζ3, by simp⟩
  have hmem2 : ((1, ζ) : (rootsOfUnity (mPhi2 a) (AlgebraicClosure K)) ×
      (rootsOfUnity (mPhi2 a) (AlgebraicClosure K))) ∈ pTors (mPhi2 a) 3 := by
    rw [mem_pTors]
    exact ⟨by simp, hζ3⟩
  obtain ⟨y₁, hy₁⟩ := hztbij.2 ⟨_, hmem1⟩
  obtain ⟨y₂, hy₂⟩ := hztbij.2 ⟨_, hmem2⟩
  have hψy₁ : ψ y₁ = rootDiagUnit ReeTag.F4.tag
      (expTuple (ζ : (AlgebraicClosure K)ˣ) 1 (uPhi2 a)) := by
    rw [← hzΦ, show z y₁ = (ζ, 1) from congrArg Subtype.val hy₁, hΦ]
    rfl
  have hψy₂ : ψ y₂ = rootDiagUnit ReeTag.F4.tag
      (expTuple 1 (ζ : (AlgebraicClosure K)ˣ) (uPhi2 a)) := by
    rw [← hzΦ, show z y₂ = (1, ζ) from congrArg Subtype.val hy₂, hΦ]
    rfl
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, ψ x * ψ y = ψ y * ψ x := by
    intro x hx y hy
    have := congrArg Subtype.val (hEcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg ψ this
  have hH : ∀ x ∈ E, ψ x ∈ torusGroup ReeTag.F4.tag (AlgebraicClosure K) := by
    intro x hx
    refine mem_torusGroup_of_commute D.isFrob hζ' (hψfix x) ?_
    rintro b (rfl | rfl)
    · rw [← hψy₁, hcomm y₁ (hE₁E y₁.2) x hx]
      group
    · rw [← hψy₂, hcomm y₂ (hE₁E y₂.2) x hx]
      group
  have hc : ∀ x : E, ∃ c : Fin 4 → (AlgebraicClosure K)ˣ,
      ψ x = rootDiagUnit ReeTag.F4.tag c := fun x =>
    exists_rootDiagUnit_eq_of_mem_torusGroup (hH x.1 x.2)
  choose c hcψ using hc
  have hc3 : ∀ x : E, ∀ i, c x i ^ 3 = 1 := by
    intro x i
    have hpow : rootDiagUnit ReeTag.F4.tag (c x ^ 3) =
        (rootDiagUnit ReeTag.F4.tag (c x)) ^ 3 :=
      map_pow (rootDiagUnitHom ReeTag.F4.tag (AlgebraicClosure K)) (c x) 3
    have h1 : rootDiagUnit ReeTag.F4.tag (c x ^ 3) = rootDiagUnit ReeTag.F4.tag 1 := by
      rw [rootDiagUnit_one, hpow, ← hcψ, ← map_pow]
      have : (x : ReeTag.F4.reeGamma K a) ^ 3 = 1 := hE3 _ x.2
      rw [this, map_one]
    exact congrFun (rootDiagUnit_injective h1) i
  have hcoord : ∀ x : E, c x 2 = c x 0 ^ 2 ^ a ∧ c x 0 * c x 1 * c x 2 * c x 3 =
      c x 1 ^ 2 ^ a := fun x =>
    coord_eq_of_mem_twistedFixed D.isFrob (c x) (hcψ x ▸ hψfix x)
  set φ : E → (Fin 2 → (AlgebraicClosure K)ˣ) := fun x => ![c x 0, c x 1] with hφ
  have hφinj : Function.Injective φ := by
    intro x x' hxx
    have h0 : c x 0 = c x' 0 := congrFun hxx 0
    have h1 : c x 1 = c x' 1 := congrFun hxx 1
    have h2 : c x 2 = c x' 2 := by rw [(hcoord x).1, (hcoord x').1, h0]
    have h3 : c x 3 = c x' 3 := by
      have e := (hcoord x).2
      have e' := (hcoord x').2
      rw [h0, h1, h2] at e
      rw [← e'] at e
      exact mul_left_cancel e
    have hcc : c x = c x' := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    have : ψ x = ψ x' := by rw [hcψ, hcψ, hcc]
    exact Subtype.ext (hψinj this)
  have hb := card_le_pow_of_injective_units (k := 2) (r := 3) (by norm_num) φ hφinj
    (fun x i => by fin_cases i <;> simp [hφ, hc3])
  norm_num at hb
  omega

end Certs

theorem reeF4NativeThreeRankTwo_holds :
    ReeF4NativeThreeRankTwo := by
  intro a ha K _ _ hK F hF
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  have hH : ReeTag.F4.reeGamma K a = reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) :=
    ReeTag.reeGamma_eq_reeFixedGroup
  let ι : ↥(reeFixedGroup .F4 K reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))) ≃* ↥(ReeTag.F4.reeGamma K a) :=
    MulEquiv.subgroupCongr hH.symm
  have h9 := card_le_nine_of_reeGamma a K hK (F.map ι.toMonoidHom)
    (Sec4.isElemAbelian_map ι.toMonoidHom hF)
  rwa [Subgroup.card_map_of_injective ι.injective] at h9

theorem twistedF4EvenThreeRankTwo_holds :
    TwistedF4EvenThreeRankTwo :=
  twistedF4EvenThreeRankTwo_of_native reeF4NativeThreeRankTwo_holds

end CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof
