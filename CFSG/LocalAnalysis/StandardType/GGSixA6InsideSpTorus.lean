module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.StandardType.ChoiceTwo

namespace CFSG.StandardType.A6InsideSp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)

private theorem tor_nsmul (hζ : ζ ^ 3 = 1) (m : ℕ) (f : Fin F.s → ZMod 3) :
    F.tor (m • f) = (F.tor f : StatedSp n K) ^ m := by
  induction m with
  | zero => rw [zero_nsmul, F.tor_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, F.tor_add hζ, ih, pow_succ]

private theorem tor_smul (hζ : ζ ^ 3 = 1) (κ : ZMod 3) (f : Fin F.s → ZMod 3) :
    F.tor (κ • f) = (F.tor f : StatedSp n K) ^ κ.val := by
  rw [show κ • f = κ.val • f by
    ext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]]
  exact tor_nsmul F hζ κ.val f

private theorem fix_of_mem_spFixedFactor (hK : Nat.card K = 2) {x g : StatedSp n K}
    (hg : g ∈ spFixedFactor x) {v : Fin n ⊕ Fin n → K}
    (hv : spEnd x (spEnd x v) + spEnd x v + v = 0) : spEnd g v = v :=
  fix_of_mem_spSupported hg (phi3_irreducible hK) monic_phi3 phi3_ne_X_sub_one
    (by rw [aeval_phi3_apply]; exact hv)

private theorem fix_of_mem_spSupported_phi3 {x g : StatedSp n K}
    (hg : g ∈ spSupported x {phi3 K}) {v : Fin n ⊕ Fin n → K} (hv : spEnd x v = v) :
    spEnd g v = v :=
  fix_of_mem_spSupported hg irreducible_X_sub_one monic_X_sub_one
    (fun h => phi3_ne_X_sub_one h.symm)
    (by rw [aeval_X_sub_one_apply, sub_eq_zero]; exact hv)

theorem spSupported_le_centralizer_tor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f h : Fin F.s → ZMod 3} (κ : ZMod 3) (hh : ∀ i, f i ≠ 0 → h i = κ * f i) :
    spSupported (F.tor f) {phi3 K} ≤ Subgroup.centralizer {F.tor h} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hsum : κ • f + (h - κ • f) = h := by abel
  have htor : F.tor h = F.tor (κ • f) * F.tor (h - κ • f) := by
    rw [← F.tor_add hζ, hsum]
  have hfix : F.tor (h - κ • f) ∈ spFixedFactor (F.tor f) :=
    F.tor_mem_spFixedFactor hK hζo f (h - κ • f) fun i hi => by
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hh i hi, sub_self]
  have hcomm₁ : g * F.tor (κ • f) = F.tor (κ • f) * g := by
    rw [tor_smul F hζ κ f]
    exact (Commute.pow_right (mem_spSupported.mp hg).1 κ.val).eq
  have hcomm₂ : g * F.tor (h - κ • f) = F.tor (h - κ • f) * g :=
    (commute_of_mem_spFixedFactor hK (F.tor_pow_three hζ f) (O := {phi3 K})
      (fun hmem => phi3_ne_X_sub_one hmem.symm) hfix hg).symm
  calc g * F.tor h = g * (F.tor (κ • f) * F.tor (h - κ • f)) := by rw [htor]
    _ = (g * F.tor (κ • f)) * F.tor (h - κ • f) := by rw [mul_assoc]
    _ = (F.tor (κ • f) * g) * F.tor (h - κ • f) := by rw [hcomm₁]
    _ = F.tor (κ • f) * (g * F.tor (h - κ • f)) := by rw [mul_assoc]
    _ = F.tor (κ • f) * (F.tor (h - κ • f) * g) := by rw [hcomm₂]
    _ = (F.tor (κ • f) * F.tor (h - κ • f)) * g := by rw [← mul_assoc]
    _ = F.tor h * g := by rw [← htor]

theorem spFixedFactor_le_centralizer_tor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f h : Fin F.s → ZMod 3} (hh : ∀ i, f i = 0 → h i = 0) :
    spFixedFactor (F.tor f) ≤ Subgroup.centralizer {F.tor h} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_mem_spFixedFactor hK (F.tor_pow_three hζo.pow_eq_one f) (O := {phi3 K})
    (fun hmem => phi3_ne_X_sub_one hmem.symm) hg
    (F.tor_mem_spSupported hK hζo f h hh (O := {phi3 K}) (Set.mem_singleton _))

theorem mem_spFixedFactor_add (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f₁ f₂ : Fin F.s → ZMod 3} {g : StatedSp n K} (h₁ : g ∈ spFixedFactor (F.tor f₁))
    (h₂ : g ∈ spFixedFactor (F.tor f₂)) : g ∈ spFixedFactor (F.tor (f₁ + f₂)) := by
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  refine mem_spSupported_of hK (F.tor_pow_three hζ (f₁ + f₂)) ?_ (fun hmem => absurd rfl hmem) ?_
  · rw [F.tor_add hζ, ← mul_assoc, (mem_spSupported.mp h₁).1, mul_assoc,
      (mem_spSupported.mp h₂).1, ← mul_assoc]
  · intro _ v hv
    obtain ⟨d, rfl⟩ := F.Φ.surjective v
    have hd : ∀ i, (f₁ + f₂) i = 0 → d i = 0 := by
      rw [← F.tor_phi3_iff hζo]
      exact hv
    set d₁ : Fin F.s → L := fun i => if f₁ i = 0 then 0 else d i with hd₁
    have hd₁mem : ∀ i, f₁ i = 0 → d₁ i = 0 := by
      intro i hi
      simp [hd₁, hi]
    have hd₂mem : ∀ i, f₂ i = 0 → (d - d₁) i = 0 := by
      intro i hi
      rw [Pi.sub_apply]
      by_cases h1 : f₁ i = 0
      · have hsum : (f₁ + f₂) i = 0 := by rw [Pi.add_apply, h1, hi, add_zero]
        rw [hd i hsum]
        simp [hd₁, h1]
      · have hd₁i : d₁ i = d i := by
          rw [hd₁]
          simp [h1]
        rw [hd₁i, sub_self]
    have hfix₁ : spEnd g (F.Φ d₁) = F.Φ d₁ := by
      refine fix_of_mem_spFixedFactor hK h₁ ?_
      rw [F.tor_phi3_iff hζo]
      exact hd₁mem
    have hfix₂ : spEnd g (F.Φ (d - d₁)) = F.Φ (d - d₁) := by
      refine fix_of_mem_spFixedFactor hK h₂ ?_
      rw [F.tor_phi3_iff hζo]
      exact hd₂mem
    calc spEnd g (F.Φ d) = spEnd g (F.Φ (d₁ + (d - d₁))) := by rw [add_sub_cancel]
      _ = spEnd g (F.Φ d₁ + F.Φ (d - d₁)) := by rw [map_add]
      _ = spEnd g (F.Φ d₁) + spEnd g (F.Φ (d - d₁)) := map_add _ _ _
      _ = F.Φ d₁ + F.Φ (d - d₁) := by rw [hfix₁, hfix₂]
      _ = F.Φ (d₁ + (d - d₁)) := (map_add _ _ _).symm
      _ = F.Φ d := by rw [add_sub_cancel]

theorem mem_spFixedFactor_of_supp (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f₁ f₂ : Fin F.s → ZMod 3} {g : StatedSp n K} (hsupp : ∀ i, f₁ i ≠ 0 → f₂ i ≠ 0)
    (hg : g ∈ spFixedFactor (F.tor f₂)) (hc : g * F.tor f₁ = F.tor f₁ * g) :
    g ∈ spFixedFactor (F.tor f₁) := by
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  refine mem_spSupported_of hK (F.tor_pow_three hζ f₁) hc (fun hmem => absurd rfl hmem) ?_
  intro _ v hv
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have hd : ∀ i, f₁ i = 0 → d i = 0 := by
    rw [← F.tor_phi3_iff hζo]
    exact hv
  refine fix_of_mem_spFixedFactor hK hg ?_
  rw [F.tor_phi3_iff hζo]
  intro i hi
  exact hd i (by
    by_contra h1
    exact (hsupp i h1) hi)

theorem mem_spFixedFactor_of_disjoint (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f₁ f₂ : Fin F.s → ZMod 3} {g : StatedSp n K} (hdisj : ∀ i, f₁ i ≠ 0 → f₂ i = 0)
    (hg : g ∈ spSupported (F.tor f₂) {phi3 K}) (hc : g * F.tor f₁ = F.tor f₁ * g) :
    g ∈ spFixedFactor (F.tor f₁) := by
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  refine mem_spSupported_of hK (F.tor_pow_three hζ f₁) hc (fun hmem => absurd rfl hmem) ?_
  intro _ v hv
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have hd : ∀ i, f₁ i = 0 → d i = 0 := by
    rw [← F.tor_phi3_iff hζo]
    exact hv
  refine fix_of_mem_spSupported_phi3 hg ?_
  rw [F.tor_fix_iff hζo]
  intro i hi
  exact hd i (by
    by_contra h1
    exact hi (hdisj i h1))

theorem eq_one_of_forall_mem_spFixedFactor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {ι : Type*} (fs : ι → Fin F.s → ZMod 3) (hcover : ∀ i, ∃ j, fs j i ≠ 0) {g : StatedSp n K}
    (hg : ∀ j, g ∈ spFixedFactor (F.tor (fs j))) : g = 1 := by
  refine eq_of_spEnd_eq' fun v => ?_
  rw [spEnd_one_apply]
  obtain ⟨d, rfl⟩ := F.Φ.surjective v
  have hsingle : ∀ (i : Fin F.s) (u : L), spEnd g (F.Φ (Pi.single i u)) = F.Φ (Pi.single i u) := by
    intro i u
    obtain ⟨j, hj⟩ := hcover i
    refine fix_of_mem_spFixedFactor hK (hg j) ?_
    rw [F.tor_phi3_iff hζo]
    intro l hl
    by_cases hli : l = i
    · subst hli
      exact (hj hl).elim
    · exact Pi.single_eq_of_ne (M := fun _ => L) (i := i) (i' := l) hli u
  calc spEnd g (F.Φ d) = spEnd g (F.Φ (∑ i, Pi.single i (d i))) := by
        rw [Finset.univ_sum_single]
    _ = spEnd g (∑ i, F.Φ (Pi.single i (d i))) := by rw [map_sum]
    _ = ∑ i, spEnd g (F.Φ (Pi.single i (d i))) := map_sum _ _ _
    _ = ∑ i, F.Φ (Pi.single i (d i)) := by
        refine Finset.sum_congr rfl fun i _ => hsingle i (d i)
    _ = F.Φ (∑ i, Pi.single i (d i)) := (map_sum _ _ _).symm
    _ = F.Φ d := by rw [Finset.univ_sum_single]

theorem eq_sgnZ_of_swap_comm (hζo : IsPrimitiveRoot ζ 3) {i j : Fin F.s} (hij : i ≠ j) (b : Bool)
    {f : Fin F.s → ZMod 3} (hc : F.swap i j b * F.tor f = F.tor f * F.swap i j b) :
    f i = sgnZ b (f j) := by
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hinv : (F.swap i j b)⁻¹ = F.swap i j b :=
    inv_eq_of_mul_eq_one_right (F.swap_mul_self hij b)
  have hconj : F.swap i j b * F.tor f * (F.swap i j b)⁻¹ =
      F.tor (moveExp (Equiv.swap i j) (swapSgn i j b) f) :=
    F.move_conj hζ (Equiv.swap i j) (swapSgn i j b) f
  rw [hinv, hc, mul_assoc, F.swap_mul_self hij b, mul_one] at hconj
  have h2 : f = moveExp (Equiv.swap i j) (swapSgn i j b) f := F.tor_injective hζo hconj
  have h3 := congrFun h2 i
  rw [moveExp_apply, show swapSgn i j b i = b by simp [swapSgn],
    show Equiv.swap i j i = j from Equiv.swap_apply_left i j] at h3
  exact h3

theorem s_eq [Module.Finite K L] (hL : Module.finrank K L = 2) : F.s = n := by
  have h := LinearEquiv.finrank_eq F.Φ
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h
  simp [hL] at h
  omega

theorem nonempty_spFixedFactor_equiv [NeZero n] [Module.Finite K L] (hK : Nat.card K = 2)
    (hζo : IsPrimitiveRoot ζ 3) (hL : Module.finrank K L = 2) {f : Fin F.s → ZMod 3}
    (hf : f ≠ 0) (hz : (F.zeroSet f).Nonempty) :
    Nonempty (↥(spFixedFactor (F.tor f)) ≃* ↥(StatedSp (F.zeroSet f).card K)) := by
  have hdim : spFixedDim (F.tor f) = 2 * (F.zeroSet f).card := F.spFixedDim_tor hζo hL f
  have hpos : 0 < spFixedDim (F.tor f) := by
    rw [hdim]
    exact Nat.mul_pos (by norm_num) (Finset.card_pos.mpr hz)
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd (F.tor f)) :=
    X_sub_one_mem_primaryFactors (F.tor f) hpos
  have blocks := F.blocks_tor hK hζo hf
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm n K).restrict (primaryComponent (spEnd (F.tor f)) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin n ⊕ Fin n → K)
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB
      blocks.fixed_nondegenerate
  have hs' : s = (F.zeroSet f).card := by
    have h1 := hs
    have h2 : finrank K (primaryComponent (spEnd (F.tor f)) (X - 1)) =
        2 * (F.zeroSet f).card := hdim
    omega
  rw [hs'] at e
  exact ⟨φ.trans e⟩

end CFSG.StandardType.A6InsideSp

end
