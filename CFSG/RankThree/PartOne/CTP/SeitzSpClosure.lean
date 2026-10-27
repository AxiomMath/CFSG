module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
public import CFSG.ClassicalGroups.Alternating.Generation

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial

variable {r : ℕ} {K : Type} [Field K]

@[expose] def TransCenter (H : Subgroup (StatedSp r K)) (v : Fin r ⊕ Fin r → K) : Prop :=
  ∀ t : K, spTransvection v t ∈ H

theorem spEnd_isometry (g : StatedSp r K) (y z : Fin r ⊕ Fin r → K) :
    spForm r K (spEnd g y) (spEnd g z) = spForm r K y z :=
  mem_sesqUnitaryGroup.mp (spLin_mem g) y z

theorem spEnd_spEnd_inv (g : StatedSp r K) (y : Fin r ⊕ Fin r → K) :
    spEnd g (spEnd g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply]

theorem spTransvection_conj (g : StatedSp r K) (v : Fin r ⊕ Fin r → K) (t : K) :
    g * spTransvection v t * g⁻¹ = spTransvection (spEnd g v) t := by
  apply spLin_injective
  rw [map_mul, map_mul]
  refine Units.ext (LinearMap.ext fun y => ?_)
  simp only [Units.val_mul, Module.End.mul_apply]
  change spEnd g (spEnd (spTransvection v t) (spEnd g⁻¹ y)) =
    spEnd (spTransvection (spEnd g v) t) y
  rw [spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul, spEnd_spEnd_inv]
  congr 3
  conv_rhs => rw [← spEnd_spEnd_inv g y]
  exact (spEnd_isometry g _ v).symm

theorem spTransvection_zero (t : K) : spTransvection (0 : Fin r ⊕ Fin r → K) t = 1 := by
  apply spLin_injective
  rw [map_one]
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection 0 t) y = y
  rw [spEnd_spTransvection]
  simp

theorem spTransvection_smul (c : K) (v : Fin r ⊕ Fin r → K) (t : K) :
    spTransvection (c • v) t = spTransvection v (c * c * t) := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spTransvection (c • v) t) y = spEnd (spTransvection v (c * c * t)) y
  rw [spEnd_spTransvection, spEnd_spTransvection, map_smul, smul_smul]
  congr 2
  simp only [smul_eq_mul]
  ring

theorem commute_spTransvection {x : StatedSp r K} {u : Fin r ⊕ Fin r → K} (hu : spEnd x u = u)
    (t : K) : spTransvection u t * x = x * spTransvection u t := by
  have h := spTransvection_conj x u t
  rw [hu] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

variable {H : Subgroup (StatedSp r K)} {v a b : Fin r ⊕ Fin r → K}

theorem transCenter_zero : TransCenter H (0 : Fin r ⊕ Fin r → K) := fun t => by
  rw [spTransvection_zero]
  exact H.one_mem

theorem TransCenter.map (hv : TransCenter H v) {g : StatedSp r K} (hg : g ∈ H) :
    TransCenter H (spEnd g v) := fun t => by
  rw [← spTransvection_conj]
  exact H.mul_mem (H.mul_mem hg (hv t)) (H.inv_mem hg)

theorem TransCenter.smul (hv : TransCenter H v) (c : K) : TransCenter H (c • v) := fun t => by
  rw [spTransvection_smul]
  exact hv _

theorem TransCenter.add (ha : TransCenter H a) (hb : TransCenter H b)
    (hab : spForm r K a b ≠ 0) : TransCenter H (a + b) := by
  have hg := hb (spForm r K a b)⁻¹
  have h := ha.map hg
  rwa [spEnd_spTransvection, inv_mul_cancel₀ hab, one_smul] at h

section Transitivity

variable {U : Submodule K (Fin r ⊕ Fin r → K)}

theorem exists_mem_fixing_eq_of_form_ne_zero (hU : ∀ c ∈ U, TransCenter H c)
    {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ U) (hy' : y' ∈ U) (h : spForm r K y y' ≠ 0) :
    ∃ g ∈ H, spEnd g y = y' ∧ ∀ z, (∀ c ∈ U, spForm r K z c = 0) → spEnd g z = z := by
  refine ⟨spTransvection (y' - y) (spForm r K y y')⁻¹, hU _ (U.sub_mem hy' hy) _, ?_, ?_⟩
  · rw [spEnd_spTransvection, map_sub, spForm_isAlt.self_eq_zero, sub_zero,
      inv_mul_cancel₀ h, one_smul, add_sub_cancel]
  · intro z hz
    rw [spEnd_spTransvection, map_sub, hz y hy, hz y' hy']
    simp

theorem exists_mem_fixing_eq (hnd : ((spForm r K).restrict U).Nondegenerate)
    (hU : ∀ c ∈ U, TransCenter H c) {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ U) (hy' : y' ∈ U)
    (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    ∃ g ∈ H, spEnd g y = y' ∧ ∀ z, (∀ c ∈ U, spForm r K z c = 0) → spEnd g z = z := by
  have hex : ∀ w ∈ U, w ≠ 0 → ∃ z ∈ U, spForm r K w z ≠ 0 := fun w hw hw0 => by
    by_contra hcon
    push Not at hcon
    exact hw0 (congrArg Subtype.val (hnd.1 ⟨w, hw⟩ fun z => hcon z z.2))
  by_cases hyy : y = y'
  · exact ⟨1, H.one_mem, by rw [spEnd_one, Module.End.one_apply, hyy], fun z _ => by
      rw [spEnd_one, Module.End.one_apply]⟩
  by_cases hB : spForm r K y y' = 0
  · obtain ⟨z₁, hz₁, h₁⟩ := hex y hy hy0
    obtain ⟨z₂, hz₂, h₂⟩ := hex y' hy' hy'0
    have hz : ∃ z ∈ U, spForm r K y z ≠ 0 ∧ spForm r K y' z ≠ 0 := by
      by_cases h3 : spForm r K y' z₁ = 0
      · by_cases h4 : spForm r K y z₂ = 0
        · exact ⟨z₁ + z₂, U.add_mem hz₁ hz₂, by rwa [map_add, h4, add_zero],
            by rwa [map_add, h3, zero_add]⟩
        · exact ⟨z₂, hz₂, h4, h₂⟩
      · exact ⟨z₁, hz₁, h₁, h3⟩
    obtain ⟨z₀, hz₀, hz₀1, hz₀2⟩ := hz
    have hz₀' : spForm r K z₀ y' ≠ 0 := fun h0 => hz₀2 (by
      rw [← spForm_isAlt.neg_eq, h0, neg_zero])
    obtain ⟨g₁, hg₁, hg₁y, hg₁z⟩ := exists_mem_fixing_eq_of_form_ne_zero hU hy hz₀ hz₀1
    obtain ⟨g₂, hg₂, hg₂y, hg₂z⟩ := exists_mem_fixing_eq_of_form_ne_zero hU hz₀ hy' hz₀'
    exact ⟨g₂ * g₁, H.mul_mem hg₂ hg₁, by rw [spEnd_mul, Module.End.mul_apply, hg₁y, hg₂y],
      fun z hz => by rw [spEnd_mul, Module.End.mul_apply, hg₁z z hz, hg₂z z hz]⟩
  · exact exists_mem_fixing_eq_of_form_ne_zero hU hy hy' hB

end Transitivity

theorem closure_spTransvection_eq_top :
    Subgroup.closure {g : StatedSp r K | ∃ (v : Fin r ⊕ Fin r → K) (t : K),
      g = spTransvection v t} = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have h1 : spLin r K g ∈ bilinIsometryGroup (spForm r K) := by
    rw [KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup, ← range_spLin]
    exact ⟨g, rfl⟩
  rw [alternating_transvection_generation spForm_isAlt spForm_nondegenerate] at h1
  have h2 : spLin r K g ∈ (Subgroup.closure {g : StatedSp r K | ∃ (v : Fin r ⊕ Fin r → K) (t : K),
      g = spTransvection v t}).map (spLin r K) := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨a, c, rfl⟩
    exact ⟨spTransvection a c, ⟨a, c, rfl⟩, spLin_spTransvection a c⟩
  obtain ⟨h, hh, hhg⟩ := h2
  rwa [← spLin_injective hhg]

theorem eq_top_of_transCenter (h : ∀ v, TransCenter H v) : H = ⊤ := by
  rw [eq_top_iff, ← closure_spTransvection_eq_top (r := r) (K := K)]
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨v, t, rfl⟩
  exact h v t

section Support

variable {ι : Type*} {Vs : ι → Submodule K (Fin r ⊕ Fin r → K)}

theorem transCenter_of_pairs (hspan : ⨆ i, Vs i = ⊤)
    (horth : ∀ i j, i ≠ j → ∀ u ∈ Vs i, ∀ v ∈ Vs j, spForm r K u v = 0)
    (hnd : ∀ i, ((spForm r K).restrict (Vs i)).Nondegenerate)
    (hpure : ∀ i, ∀ c ∈ Vs i, TransCenter H c)
    (hpair : ∀ i j, i ≠ j → ∀ y ∈ Vs i, ∀ y' ∈ Vs j, y ≠ 0 → y' ≠ 0 →
      TransCenter H (y + y')) :
    ∀ v, TransCenter H v := by
  classical
  have key : ∀ n : ℕ, ∀ J : Finset ι, J.card ≤ n → ∀ v ∈ ⨆ j ∈ J, Vs j, TransCenter H v := by
    intro n
    induction n with
    | zero =>
      intro J hJ v hv
      have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      have hv0 : v = 0 := by simpa using hv
      rw [hv0]
      exact transCenter_zero
    | succ n ih =>
      intro J hJ v hv
      obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum Vs v).1 hv
      have hmem : ∀ (S : Finset ι) (k : ι), k ∈ S → ∀ w ∈ Vs k, w ∈ ⨆ j ∈ S, Vs j :=
        fun S k hk w hw => Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk hw)
      by_cases hz : ∃ j ∈ J, (μ j : Fin r ⊕ Fin r → K) = 0
      · obtain ⟨j, hj, hμj⟩ := hz
        refine ih (J.erase j) (by rw [Finset.card_erase_of_mem hj]; omega) _ ?_
        refine (Submodule.mem_iSup_finset_iff_exists_sum Vs _).2 ⟨μ, ?_⟩
        rw [← Finset.add_sum_erase J _ hj, hμj, zero_add]
      push Not at hz
      by_cases hJ2 : ∃ i ∈ J, ∃ j ∈ J, i ≠ j
      · obtain ⟨i, hi, j, hj, hij⟩ := hJ2
        have hi' : i ∈ J.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
        have hcard : (J.erase j).card ≤ n := by rw [Finset.card_erase_of_mem hj]; omega
        set v' := ∑ k ∈ J.erase j, (μ k : Fin r ⊕ Fin r → K) with hv'
        have hsum : ∑ k ∈ J, (μ k : Fin r ⊕ Fin r → K) = v' + μ j := by
          rw [hv', Finset.sum_erase_add J _ hj]
        obtain ⟨y, hy, hBy⟩ : ∃ y ∈ Vs i, spForm r K (μ i) y ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hz i hi (congrArg Subtype.val ((hnd i).1 ⟨μ i, (μ i).2⟩ fun z => hcon z z.2))
        have hy0 : y ≠ 0 := fun h0 => hBy (by rw [h0, map_zero])
        have hv'y : spForm r K v' y = spForm r K (μ i) y := by
          rw [hv', map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
          · intro k hk hki
            exact horth k i hki _ (μ k).2 y hy
          · intro hni
            exact absurd hi' hni
        have hv'μj : spForm r K v' (μ j) = 0 := by
          rw [hv', map_sum, LinearMap.sum_apply]
          refine Finset.sum_eq_zero fun k hk => ?_
          exact horth k j (Finset.ne_of_mem_erase hk) _ (μ k).2 _ (μ j).2
        have hyμj : spForm r K y (μ j) = 0 := horth i j hij y hy _ (μ j).2
        have hB : spForm r K (v' + y) (μ j - y) ≠ 0 := by
          have h0 : spForm r K (v' + y) (μ j - y) = -spForm r K (μ i) y := by
            simp only [map_add, map_sub, LinearMap.add_apply]
            rw [hv'μj, hv'y, hyμj, spForm_isAlt.self_eq_zero]
            ring
          rw [h0]
          exact neg_ne_zero.2 hBy
        have h1 : TransCenter H (v' + y) := by
          refine ih (J.erase j) hcard _ (Submodule.add_mem _ ?_ (hmem _ i hi' y hy))
          exact Submodule.sum_mem _ fun k hk => hmem _ k hk _ (μ k).2
        have h2 : TransCenter H (μ j - y) := by
          rw [← neg_add_eq_sub]
          exact hpair i j hij (-y) ((Vs i).neg_mem hy) _ (μ j).2 (neg_ne_zero.2 hy0) (hz j hj)
        have h3 := h1.add h2 hB
        rw [hsum]
        convert h3 using 1
        abel
      · push Not at hJ2
        rcases J.eq_empty_or_nonempty with hJ0 | ⟨j0, hj0⟩
        · subst hJ0
          rw [Finset.sum_empty]
          exact transCenter_zero
        · have hsum : ∑ k ∈ J, (μ k : Fin r ⊕ Fin r → K) = μ j0 :=
            Finset.sum_eq_single_of_mem j0 hj0 fun k hk hne => absurd (hJ2 k hk j0 hj0) hne
          rw [hsum]
          exact hpure j0 _ (μ j0).2
  intro v
  have hv : v ∈ ⨆ i, Vs i := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨J, hJ⟩ := Submodule.mem_iSup_iff_exists_finset.1 hv
  exact key J.card J le_rfl v hJ

end Support

end CFSG.RankThree.PartOne.CTP
