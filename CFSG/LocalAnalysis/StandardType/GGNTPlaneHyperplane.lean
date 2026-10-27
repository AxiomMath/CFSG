module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableData
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem rank_e6 : Tag.E6.rank = 6 := rfl

private def sepZ : Fin 7 → Fin 5 → (Fin Tag.E6.rank → ℤ) :=
  ![![![-1, -1, -2, -2, -1, 0], ![-1, -1, -1, -2, -1, 0], ![-1, -1, -1, -1, -1, 0],
     ![-1, -1, -1, -1, 0, 0], ![-1, 0, -1, -1, -1, 0]],
    ![![-1, -1, -2, -2, -1, 0], ![-1, -1, -1, -2, -1, 0], ![-1, -1, -1, -1, -1, 0],
     ![-1, -1, -1, -1, 0, 0], ![-1, 0, -1, -1, -1, 0]],
    ![![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -3, -2, -1], ![-1, -1, -2, -2, -2, -1],
     ![-1, -1, -1, -2, -2, -1], ![-1, -1, -1, -1, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
     ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
     ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
     ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]],
    ![![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0],
     ![-1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0]]]

private def hitChar : Fin 6 → X3 :=
  ![![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 2, 2], ![0, 0, 0, 1, 1, 1], ![0, 1, 1, 2, 0, 2],
    ![0, 1, 1, 2, 2, 1], ![0, 1, 1, 1, 1, 0]]

private def hitWord : Fin 6 → List (Fin Tag.E6.rank) :=
  ![[], [⟨4, by decide⟩], [⟨5, by decide⟩, ⟨4, by decide⟩],
    [⟨3, by decide⟩, ⟨4, by decide⟩], [⟨5, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩],
    [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]]

private theorem sepZ_mem : ∀ (k : Fin 7) (i : Fin 5), sepZ k i ∈ e6RootList := by
  decide +kernel

private theorem sepZ_pairVec : ∀ (k : Fin 7) (i : Fin 5), pairVec (reps k) (sepZ k i) = 0 := by
  decide +kernel

private theorem sepZ_spec (k : Fin 7) (hk : k = 0 ∨ k = 1 ∨ k = 2) :
    ∀ u : X3, (∀ i : Fin 5, pairVec u (sepZ k i) = 0) →
      u = 0 ∨ u = reps k ∨ u = (2 : ZMod 3) • reps k := by
  rcases hk with rfl | rfl | rfl <;> decide +kernel

private theorem hitWord_spec : ∀ i : Fin 6, applyWord (hitWord i) (reps 2) = hitChar i := by
  decide +kernel

private theorem hit_spec : ∀ l : X3, l ≠ 0 → ∃ i : Fin 6, ∑ j, l j * hitChar i j = 0 := by
  decide +kernel

private theorem repKerCard_thirty_or_forty :
    ∀ k : Fin 7, repKerCard k = 30 ∨ repKerCard k = 40 → k = 0 ∨ k = 1 ∨ k = 2 := by
  decide +kernel

private theorem pairVec_smulZMod (c : ZMod 3) (x : X3) (v : Fin Tag.E6.rank → ℤ) :
    pairVec (c • x) v = c * pairVec x v := by
  simp only [pairVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem smul_zero_X3 (g : WeylGroup Tag.E6) : g • (0 : X3) = 0 := by
  apply pairVec_eq_of_forall
  intro v
  rw [pairVec_smul]
  simp [pairVec]

private theorem smul_smul_X3 (g : WeylGroup Tag.E6) (c : ZMod 3) (x : X3) :
    g • (c • x) = c • (g • x) := by
  apply pairVec_eq_of_forall
  intro v
  rw [pairVec_smul, pairVec_smulZMod, pairVec_smulZMod, pairVec_smul]

private theorem hitChar_ncard (i : Fin 6) : (kerRoots (hitChar i)).ncard = 30 := by
  rw [← hitWord_spec i, applyWord_eq_prod_smul, ncard_kerRoots_smul, ncard_kerRoots_reps]
  norm_num [repKerCard]

private theorem exists_smul_of_forall_pairVec_eq_zero {v : X3}
    (hv : (kerRoots v).ncard = 30 ∨ (kerRoots v).ncard = 40) {w : X3}
    (h : ∀ α ∈ kerRoots v, pairVec w α = 0) : ∃ c : ZMod 3, w = c • v := by
  by_cases hv0 : v = 0
  · subst hv0
    have hw : w = 0 := by
      funext i
      have hmem : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ kerRoots (0 : X3) :=
        ⟨IsRoot.basis i, by simp [pairVec]⟩
      have h0 := h _ hmem
      rwa [pairVec_single] at h0
    exact ⟨0, by rw [hw, zero_smul]⟩
  · obtain ⟨k, g, rfl⟩ := exists_smul_reps v hv0
    have hkcard : repKerCard k = 30 ∨ repKerCard k = 40 := by
      have hc := hv
      rwa [ncard_kerRoots_smul g (reps k), ncard_kerRoots_reps k] at hc
    have hk := repKerCard_thirty_or_forty k hkcard
    have hw : w = g • (g⁻¹ • w) := (smul_inv_smul g w).symm
    have hfive : ∀ i : Fin 5, pairVec (g⁻¹ • w) (sepZ k i) = 0 := by
      intro i
      have hroot : sepZ k i ∈ kerRoots (reps k) :=
        ⟨(isRoot_iff_mem_e6RootList _).2 (sepZ_mem k i), sepZ_pairVec k i⟩
      have himg : g • sepZ k i ∈ kerRoots (g • reps k) := by
        rw [kerRoots_smul]
        exact ⟨sepZ k i, hroot, rfl⟩
      have h0 := h (g • sepZ k i) himg
      rw [pairVec_smul, inv_inv]
      exact h0
    rcases sepZ_spec k hk (g⁻¹ • w) hfive with hu | hu | hu
    · exact ⟨0, by rw [hw, hu, smul_zero_X3, zero_smul]⟩
    · exact ⟨1, by rw [hw, hu, one_smul]⟩
    · exact ⟨2, by rw [hw, hu, smul_smul_X3]⟩

private theorem ncard_eq_pow_five (H : AddSubgroup X3) (hH : 3 ^ 5 ≤ Nat.card H)
    (htop : H ≠ ⊤) : Nat.card H = 3 ^ 5 := by
  have hX3 : Nat.card X3 = 3 ^ 6 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, rank_e6]
  have hmul : Nat.card H * H.index = 3 ^ 6 := by
    rw [AddSubgroup.card_mul_index, hX3]
  have hdvd : Nat.card H ∣ 3 ^ 6 := ⟨H.index, hmul.symm⟩
  obtain ⟨k, hk6, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd
  interval_cases k
  · rw [hk] at hH; norm_num at hH
  · rw [hk] at hH; norm_num at hH
  · rw [hk] at hH; norm_num at hH
  · rw [hk] at hH; norm_num at hH
  · rw [hk] at hH; norm_num at hH
  · exact hk
  · exfalso
    exact htop (AddSubgroup.eq_top_of_card_eq H (by rw [hk, hX3]))

private theorem exists_dual_ker_eq (H : AddSubgroup X3) (htop : H ≠ ⊤)
    (hcard : Nat.card H = 3 ^ 5) :
    ∃ f : X3 →ₗ[ZMod 3] ZMod 3, f ≠ 0 ∧ ∀ x : X3, f x = 0 ↔ x ∈ H := by
  let S : Submodule (ZMod 3) X3 := AddSubgroup.toZModSubmodule (n := 3) H
  have hS_card : Nat.card S = 3 ^ 5 := by
    calc Nat.card S = (S : Set X3).ncard := Nat.card_coe_set_eq (S : Set X3)
      _ = (H : Set X3).ncard := by rw [AddSubgroup.coe_toZModSubmodule]
      _ = Nat.card H := (Nat.card_coe_set_eq (H : Set X3)).symm
      _ = 3 ^ 5 := hcard
  have hS_top : S ≠ ⊤ := by
    intro hS
    apply htop
    ext x
    constructor
    · intro _
      exact AddSubgroup.mem_top x
    · intro _
      have hx : x ∈ S := by
        rw [hS]
        exact Submodule.mem_top
      exact (AddSubgroup.mem_toZModSubmodule (n := 3) (S := H)).1 hx
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top S (lt_top_iff_ne_top.2 hS_top)
  have hX3fin : Module.finrank (ZMod 3) X3 = 6 := by
    rw [Module.finrank_fin_fun, rank_e6]
  have hker_fin : Module.finrank (ZMod 3) (LinearMap.ker f) = 5 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod 3) (V₁ := X3) hf0
    rw [hX3fin] at h
    omega
  have hS_fin : Module.finrank (ZMod 3) S = 5 := by
    have h := FiniteField.pow_finrank_eq_natCard 3 S
    rw [hS_card] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  have hSeq : S = LinearMap.ker f := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [hker_fin, hS_fin]
  refine ⟨f, hf0, fun x => ?_⟩
  rw [← LinearMap.mem_ker, ← hSeq]
  exact (AddSubgroup.mem_toZModSubmodule (n := 3) (S := H))

private theorem exists_hitChar_mem (H : AddSubgroup X3) (htop : H ≠ ⊤)
    (hcard : Nat.card H = 3 ^ 5) : ∃ v ∈ H, (kerRoots v).ncard = 30 := by
  obtain ⟨f, hf0, hfH⟩ := exists_dual_ker_eq H htop hcard
  let l : X3 := fun i => f (Pi.single i 1)
  have hfsum : ∀ x : X3, f x = ∑ j, x j * l j := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    have harg : (fun j => if i = j then (1 : ZMod 3) else 0) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [harg, smul_eq_mul]
  have hl : l ≠ 0 := by
    intro hl0
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfsum x, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hli : f (Pi.single i 1) = 0 := by
      have := congrFun hl0 i
      simpa [l] using this
    rw [show l i = f (Pi.single i 1) from rfl, hli, mul_zero]
  obtain ⟨i, hi⟩ := hit_spec l hl
  have hfi : f (hitChar i) = 0 := by
    rw [hfsum (hitChar i),
      show (∑ j, hitChar i j * l j) = ∑ j, l j * hitChar i j from
        Finset.sum_congr rfl fun j _ => mul_comm _ _]
    exact hi
  exact ⟨hitChar i, (hfH _).1 hfi, hitChar_ncard i⟩

theorem exists_mem_ncard_kerRoots_eq_thirty (H : AddSubgroup X3) (hH : 3 ^ 5 ≤ Nat.card H) :
    ∃ v ∈ H, (kerRoots v).ncard = 30 := by
  by_cases htop : H = ⊤
  · exact ⟨reps 2, by simp [htop], by rw [ncard_kerRoots_reps]; norm_num [repKerCard]⟩
  · exact exists_hitChar_mem H htop (ncard_eq_pow_five H hH htop)

theorem forall_pairVec_kerRoots_eq_zero_iff {v : X3}
    (hv : (kerRoots v).ncard = 30 ∨ (kerRoots v).ncard = 40) (w : X3) :
    (∀ α ∈ kerRoots v, pairVec w α = 0) ↔ ∃ c : ZMod 3, w = c • v := by
  constructor
  · exact fun h => exists_smul_of_forall_pairVec_eq_zero hv h
  · rintro ⟨c, rfl⟩ α hα
    rw [pairVec_smulZMod, hα.2, mul_zero]

theorem ncard_kerRoots_zero : (kerRoots (0 : X3)).ncard = 72 := by
  have hset : kerRoots (0 : X3) = ↑e6RootList.toFinset := by
    ext α
    simp [kerRoots, pairVec, isRoot_iff_mem_e6RootList]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (by decide +kernel),
    show e6RootList.length = 72 from by decide +kernel]

end CFSG.StandardType.NTPlane

end
