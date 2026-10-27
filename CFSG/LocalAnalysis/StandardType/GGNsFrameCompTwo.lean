module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompOrbit

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.OddIso Multiplicative

section Two

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)} {x : ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem mult_le_one_of_le_cyc (a : primaryFactors (Xe x)) {u : Fin n → K}
    (hu : u ∈ primaryComponent (Xe x) (a : K[X]))
    (hle : primaryComponent (Xe x) (a : K[X]) ≤ cyc (Xe x) u) :
    primaryMultiplicity (Xe x) (a : K[X]) ≤ 1 := by
  have hspan : Submodule.span (AdjoinRoot (a : K[X]))
      ({⟨u, hu⟩} : Set (primaryComponent (Xe x) (a : K[X]))) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    obtain ⟨t, ht⟩ := (mem_cyc_iff _ _ _).mp (hle v.2)
    have hv : v = AdjoinRoot.mk (a : K[X]) t • (⟨u, hu⟩ : primaryComponent (Xe x) (a : K[X])) :=
      Subtype.ext (by rw [coe_mk_smul_primaryComponent, ht])
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := finrank_span_le_card (R := AdjoinRoot (a : K[X]))
    ({⟨u, hu⟩} : Set (primaryComponent (Xe x) (a : K[X])))
  rw [hspan, finrank_top] at h1
  simpa using h1

theorem eq_zero_of_fix_primaryComponent {a : K[X]} (ha : a ∈ primaryFactors (Xe x))
    (ha1 : a ≠ X - C 1) {v : Fin n → K} (hv : v ∈ primaryComponent (Xe x) a)
    (hfix : lin x v = v) : v = 0 := by
  by_contra hv0
  have heig : Module.End.HasEigenvector (Xe x) 1 v :=
    ⟨Module.End.mem_eigenspace_iff.mpr (by rw [one_smul]; exact hfix), hv0⟩
  have h0 := mem_primaryComponent.mp hv
  rw [Module.End.aeval_apply_of_hasEigenvector heig] at h0
  have hroot : a.eval 1 = 0 := (smul_eq_zero.mp h0).resolve_right hv0
  have hdvd : X - C 1 ∣ a := dvd_iff_isRoot.mpr hroot
  have hass := (irreducible_X_sub_C (1 : K)).associated_of_dvd
    (irreducible_of_mem_primaryFactors ha) hdvd
  exact ha1 (eq_of_monic_of_associated (monic_X_sub_C 1) (monic_of_mem_primaryFactors ha) hass).symm

variable (F : PieceFrame f n K h p A)

theorem sub_mem_rng (hA : MaxElemAb p A) (j : Fin F.r) (k : ℕ) (u : Fin n → K) :
    lin (F.b j ^ k) u - u ∈ rng (F.y j) := by
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth (F.nondeg hA j) u
  have hz' : lin (F.b j ^ k) z = z := by
    induction k with
    | zero => rw [pow_zero, lin_one]; rfl
    | succ k ih => rw [pow_succ, lin_mul, Module.End.mul_apply, F.b_off j z hz]; exact ih
  rw [map_add, hz', add_sub_add_right_eq_sub]
  exact (rng (F.y j)).sub_mem (rng_inv hA (F.y_mem j) (A.pow_mem (F.b_mem j) k) m hm) hm

theorem lin_pow_on (hA : MaxElemAb p A) {s : Multiplicative (Fin F.r → ZMod p)}
    (hs : F.ι s = x) (j : Fin F.r) (N : ℕ) {u : Fin n → K} (hu : u ∈ rng (F.y j)) :
    (lin x ^ N) u = lin (F.y j ^ ((toAdd s j).val * N)) u := by
  induction N generalizing u with
  | zero => rw [pow_zero, Nat.mul_zero, pow_zero, lin_one]
  | succ N ih =>
    have hu' : lin (F.y j ^ ((toAdd s j).val * N)) u ∈ rng (F.y j) :=
      rng_inv hA (F.y_mem j) (A.pow_mem (F.y_mem j) _) u hu
    rw [pow_succ', Module.End.mul_apply, ih hu, ← hs, F.ι_on s j _ hu', ← Module.End.mul_apply,
      ← lin_mul, ← pow_add, Nat.mul_succ, add_comm]

theorem inv_of_xinv (hA : MaxElemAb p A) {s : Multiplicative (Fin F.r → ZMod p)}
    (hs : F.ι s = x) {j : Fin F.r} (hsj : toAdd s j ≠ 0) {S : Submodule K (Fin n → K)}
    (hSU : S ≤ rng (F.y j)) (hSx : ∀ v ∈ S, lin x v ∈ S) : ∀ c ∈ A, ∀ v ∈ S, lin c v ∈ S := by
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  intro c hc v hv
  obtain ⟨k, hk⟩ := F.cyc j c hc
  have hkp : ¬ p ∣ (toAdd s j).val := by
    intro hdvd
    apply hsj
    rw [← ZMod.natCast_zmod_val (toAdd s j)]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  have hcop : Nat.Coprime (toAdd s j).val p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hkp)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hyk : F.y j ^ ((toAdd s j).val * (m * k)) = F.y j ^ k := by
    rw [← mul_assoc, pow_mul, pow_eq_pow_mod _ (hA.pow _ (F.y_mem j)), hm, pow_one]
  rw [hk v (hSU hv), ← hyk, ← lin_pow_on F hA hs j _ (hSU hv)]
  exact invariant_pow hSx _ v hv

theorem exists_two_pieces_orbW (hA : MaxElemAb p A) (hxA : x ∈ A) (a : primaryFactors (Xe x))
    (ha : IsGoodBlock h (toUnitHom x) a) (ha1 : (a : K[X]) ≠ X - C 1) :
    ∃ j j' : Fin F.r, j ≠ j' ∧
      (∀ v ∈ (orbW h x a).orthogonalBilin (stdHermForm h n), lin (F.b j) v = v) ∧
      ∀ v ∈ (orbW h x a).orthogonalBilin (stdHermForm h n), lin (F.b j') v = v := by
  classical
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have : Finite K := h.finite
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  have hsq := H.squarefree
  set B := stdHermForm h n with hB
  set W := orbW h x (a : K[X]) with hW
  set OnW : Fin F.r → Prop := fun j => ∀ v ∈ W.orthogonalBilin B, lin (F.b j) v = v with hOnW
  by_contra hcon
  have huniq : ∀ j j', OnW j → OnW j' → j = j' := by
    intro j j' hj hj'
    by_contra hne
    exact hcon ⟨j, j', hne, hj, hj'⟩
  have hVa : primaryComponent (Xe x) (a : K[X]) ≠ ⊥ := primaryComponent_ne_bot hsq a.2
  have hVaW : primaryComponent (Xe x) (a : K[X]) ≤ W := le_sup_left
  have hoff : ∀ j, ¬ OnW j → ∀ v ∈ W, v ∈ (rng (F.y j)).orthogonalBilin B := by
    intro j hj v hv
    rcases piece_orbW hA F hxA a.2 j with h1 | h1
    · exact absurd h1 hj
    · have h2 : lin (F.ι (ofAdd (Pi.single j 1))) v = v := by rw [F.ι_single]; exact h1 v hv
      exact (F.ι_fix _ v).mp h2 j (by simp)
  have hxr : x ∈ F.ι.range := by rw [F.ι_range]; exact hxA
  obtain ⟨s, hs⟩ := hxr
  by_cases hex : ∃ j, OnW j
  swap
  · push Not at hex
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVa
    apply hw0
    refine eq_zero_of_fix_primaryComponent a.2 ha1 hw ?_
    rw [← hs]
    exact (F.ι_fix s w).mpr fun k _ => hoff k (hex k) w (hVaW hw)
  obtain ⟨j, hj⟩ := hex
  have hothers : ∀ k, k ≠ j → ¬ OnW k := fun k hk hk' => hk (huniq k j hk' hj)
  have hxW : ∀ v ∈ W, lin x v = lin (F.b j ^ (toAdd s j).val) v := by
    intro v hv
    have hsplit : s = ofAdd (Pi.single j (((toAdd s j).val : ℕ) : ZMod p)) *
        ofAdd (toAdd s - Pi.single j (toAdd s j)) := by
      apply toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd, ZMod.natCast_zmod_val]
      abel
    have hrest : lin (F.ι (ofAdd (toAdd s - Pi.single j (toAdd s j)))) v = v := by
      refine (F.ι_fix _ v).mpr fun k hk => ?_
      by_cases hkj : k = j
      · subst hkj
        simp at hk
      · exact hoff k (hothers k hkj) v hv
    calc lin x v = lin (F.ι s) v := by rw [hs]
      _ = lin (F.ι (ofAdd (Pi.single j (((toAdd s j).val : ℕ) : ZMod p)) *
          ofAdd (toAdd s - Pi.single j (toAdd s j)))) v := by rw [← hsplit]
      _ = lin (F.b j ^ (toAdd s j).val) v := by
        rw [map_mul, lin_mul, Module.End.mul_apply, hrest, F.ι_single_pow]
  have hinvV : ∀ v ∈ primaryComponent (Xe x) (a : K[X]),
      (lin x - 1) v ∈ primaryComponent (Xe x) (a : K[X]) := fun v hv => by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (apply_mem_primaryComponent (Commute.refl _) hv) hv
  set T := (lin x - 1).restrict hinvV with hT
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, hu⟩ hu0
    have h1 : (lin x - 1) u = 0 := congrArg Subtype.val hu0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    exact Subtype.ext (eq_zero_of_fix_primaryComponent a.2 ha1 hu h1)
  have hTsurj := LinearMap.injective_iff_surjective.mp hTinj
  have hVaU : primaryComponent (Xe x) (a : K[X]) ≤ rng (F.y j) := by
    intro v hv
    obtain ⟨⟨u, hu⟩, hTu⟩ := hTsurj ⟨v, hv⟩
    have h1 : lin x u - u = v := by
      have h2 := congrArg Subtype.val hTu
      simpa [hT] using h2
    rw [← h1, hxW u (hVaW hu)]
    exact sub_mem_rng F hA j _ u
  have hsj : toAdd s j ≠ 0 := by
    intro hsj0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVa
    apply hw0
    refine eq_zero_of_fix_primaryComponent a.2 ha1 hw ?_
    rw [hxW w (hVaW hw), hsj0, ZMod.val_zero, pow_zero, lin_one]
    rfl
  have hinvU : ∀ u ∈ rng (F.y j), lin x u ∈ rng (F.y j) := rng_inv hA (F.y_mem j) hxA
  have hndU := F.nondeg hA j
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVa
  have hwU := hVaU hw
  have hmin : ∀ S : Submodule K (Fin n → K), S ≤ rng (F.y j) → S ≠ ⊥ → NondegOn B S →
      (∀ v ∈ S, lin x v ∈ S) → S = rng (F.y j) :=
    fun S hSU hS0 hSnd hSx => F.minimal j S hSU hS0 hSnd (inv_of_xinv F hA hs hsj hSU hSx)
  have hm := ha.1
  by_cases hself : dualPoly h.bar (a : K[X]) = a
  · obtain ⟨u, huU, hu⟩ := exists_selfDualVal_ne_zero h H a.2 hself hndU hinvU
      ⟨w, hwU, hw0, mem_primaryComponent.mp hw⟩
    have hcyc : cyc (Xe x) (u : Fin n → K) = rng (F.y j) := by
      refine hmin _ (cyc_le hinvU huU) ?_ (nondegOn_cyc_of_selfDualVal h H a.2 hself u hu)
        (cyc_invariant _ _)
      intro hbot
      have h1 : (u : Fin n → K) ∈ cyc (Xe x) (u : Fin n → K) := by
        simpa using pow_mem_cyc (Xe x) (u : Fin n → K) 0
      rw [hbot, Submodule.mem_bot] at h1
      apply hu
      rw [show u = 0 from Subtype.ext h1]
      have := selfDualVal_smul_right (B := B) (0 : AdjoinRoot (a : K[X]))
        (0 : primaryComponent (Xe x) (a : K[X])) (0 : primaryComponent (Xe x) (a : K[X]))
      rwa [zero_smul, zero_mul] at this
    have := mult_le_one_of_le_cyc a u.2 (hcyc ▸ hVaU)
    omega
  · obtain ⟨w', hw'U, hww'⟩ := exists_pair_vec h H a.2 hndU hinvU hwU hw0
      (mem_primaryComponent.mp hw)
    have ha' : dualPoly h.bar (a : K[X]) ∈ primaryFactors (Xe x) :=
      dualPoly_mem_primaryFactors H a.2
    have hne : (a : K[X]) ≠ dualPoly h.bar (a : K[X]) := fun e => hself e.symm
    have hne' : dualPoly h.bar (a : K[X]) ≠ dualPoly h.bar (dualPoly h.bar (a : K[X])) := by
      rw [dualPoly_dualPoly_of_mem H a.2]; exact hself
    have hcw : cyc (Xe x) w ≤ primaryComponent (Xe x) (a : K[X]) :=
      cyc_le (fun v hv => apply_mem_primaryComponent (Commute.refl _) hv) hw
    have hcw' : cyc (Xe x) (w' : Fin n → K) ≤ primaryComponent (Xe x) (dualPoly h.bar (a : K[X])) :=
      cyc_le (fun v hv => apply_mem_primaryComponent (Commute.refl _) hv) w'.2
    have hxp : (Xe x) ^ p = 1 := by
      rw [coe_toUnitHom, ← SUTB.lin_pow, hA.pow x hxA, SUTB.lin_one]
    have hS : cyc (Xe x) w ⊔ cyc (Xe x) (w' : Fin n → K) = rng (F.y j) := by
      refine hmin _ (sup_le (cyc_le hinvU hwU) (cyc_le hinvU hw'U)) ?_ ?_ ?_
      · intro hbot
        apply hw0
        have h1 : w ∈ cyc (Xe x) w ⊔ cyc (Xe x) (w' : Fin n → K) :=
          Submodule.mem_sup_left (by simpa using pow_mem_cyc (Xe x) w 0)
        rwa [hbot, Submodule.mem_bot] at h1
      · exact nondegOn_cyc_sup H.symm H.isom hp.one_lt.le hxp
          (irreducible_of_mem_primaryFactors a.2) (irreducible_of_mem_primaryFactors ha')
          (mem_primaryComponent.mp hw) (mem_primaryComponent.mp w'.2) hww'
          (fun v hv v' hv' => isotropic_primaryComponent H a.2 hne (hcw hv) (hcw hv'))
          (fun v hv v' hv' => isotropic_primaryComponent H ha' hne' (hcw' hv) (hcw' hv'))
      · intro v hv
        obtain ⟨c, hc, c', hc', rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.add_mem_sup (cyc_invariant _ _ c hc) (cyc_invariant _ _ c' hc')
    have hle : primaryComponent (Xe x) (a : K[X]) ≤ cyc (Xe x) w := by
      intro v hv
      have hvS : v ∈ cyc (Xe x) w ⊔ cyc (Xe x) (w' : Fin n → K) := hS ▸ hVaU hv
      obtain ⟨c, hc, c', hc', hcc⟩ := Submodule.mem_sup.mp hvS
      have hc'a : c' ∈ primaryComponent (Xe x) (a : K[X]) := by
        have e : c' = v - c := by rw [← hcc]; abel
        rw [e]
        exact Submodule.sub_mem _ hv (hcw hc)
      have hc'0 : c' = 0 := by
        have e1 := primaryProjection_of_mem hsq a.2 hc'a
        have e2 := primaryProjection_of_mem_ne hsq a.2 ha' (Ne.symm hne) (hcw' hc')
        rw [e1] at e2
        exact e2
      rw [← hcc, hc'0, add_zero]
      exact hc
    have := mult_le_one_of_le_cyc a hw hle
    omega

end Two

end NsFrameComp

end CFSG.StandardType
