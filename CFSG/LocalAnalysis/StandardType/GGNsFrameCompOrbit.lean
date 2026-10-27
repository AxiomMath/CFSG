module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameComp

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.OddIso Multiplicative

section Orbit

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

variable (h) in
@[expose] noncomputable def orbW (x : ↥(unitarySU 2 f K n)) (a : K[X]) :
    Submodule K (Fin n → K) :=
  primaryComponent (Xe x) a ⊔ primaryComponent (Xe x) (dualPoly h.bar a)

variable {x : ↥(unitarySU 2 f K n)} {a : K[X]}

theorem orbW_nondeg (H : UnitaryPrimaryData h.bar (stdHermForm h n) (toUnitHom x))
    (ha : a ∈ primaryFactors (Xe x)) : NondegOn (stdHermForm h n) (orbW h x a) := by
  refine nondegOn_of_left H.symm fun w hw hB => ?_
  by_cases hself : dualPoly h.bar a = a
  · have hsep := separatingLeft_primaryComponent_selfDual H ha hself
    have hw' : w ∈ primaryComponent (Xe x) a := by
      have := hw
      rwa [orbW, hself, sup_idem] at this
    have := hsep ⟨w, hw'⟩ fun w' => hB w' (Submodule.mem_sup_left w'.2)
    exact congrArg Subtype.val this
  · have hsep := separatingLeft_primaryComponent_sup H ha (Ne.symm hself)
    have := hsep ⟨w, hw⟩ fun w' => hB w' w'.2
    exact congrArg Subtype.val this

theorem orbW_inv {c : ↥(unitarySU 2 f K n)} (hc : c ∈ Subgroup.centralizer {x}) :
    ∀ v ∈ orbW h x a, lin c v ∈ orbW h x a := by
  intro v hv
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (lin_mem_primaryComponent hc hv₁) (lin_mem_primaryComponent hc hv₂)

open Classical in
theorem exists_orbW_decomp (H : UnitaryPrimaryData h.bar (stdHermForm h n) (toUnitHom x))
    (ha : a ∈ primaryFactors (Xe x)) (v : Fin n → K) :
    ∃ w ∈ orbW h x a, v - w ∈ (orbW h x a).orthogonalBilin (stdHermForm h n) ∧
      ∀ U : Submodule K (Fin n → K), (∀ u ∈ U, lin x u ∈ U) → v ∈ U → w ∈ U := by
  have hsq := H.squarefree
  set P : K[X] → Prop := fun b => b = a ∨ b = dualPoly h.bar a with hP
  set w := ∑ b ∈ (primaryFactors (Xe x)).filter P, primaryProjection (Xe x) b v with hw
  have hsum := eq_sum_primaryProjection hsq v
  have hsplit : v - w = ∑ b ∈ (primaryFactors (Xe x)).filter (fun b => ¬ P b),
      primaryProjection (Xe x) b v := by
    rw [sub_eq_iff_eq_add', hw, Finset.sum_filter_add_sum_filter_not]
    exact hsum
  refine ⟨w, ?_, ?_, fun U hU hvU => ?_⟩
  · refine Submodule.sum_mem _ fun b hb => ?_
    obtain ⟨hbF, hbP⟩ := Finset.mem_filter.mp hb
    have hmem := primaryProjection_mem hsq hbF v
    rcases hbP with rfl | rfl
    · exact Submodule.mem_sup_left hmem
    · exact Submodule.mem_sup_right hmem
  · rw [hsplit]
    refine Submodule.sum_mem _ fun b hb => ?_
    obtain ⟨hbF, hbP⟩ := Finset.mem_filter.mp hb
    have hmem := primaryProjection_mem hsq hbF v
    refine Submodule.mem_orthogonalBilin.mpr fun m hm => ?_
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hm
    have had := dualPoly_mem_primaryFactors H ha
    have h1 : stdHermForm h n m₁ (primaryProjection (Xe x) b v) = 0 :=
      orthogonal_of_ne_dualPoly H ha hbF (fun e => hbP (Or.inr e)) hm₁ hmem
    have h2 : stdHermForm h n m₂ (primaryProjection (Xe x) b v) = 0 :=
      orthogonal_of_ne_dualPoly H had hbF
        (fun e => hbP (Or.inl (e.trans (dualPoly_dualPoly_of_mem H ha)))) hm₂ hmem
    change stdHermForm h n (m₁ + m₂) (primaryProjection (Xe x) b v) = 0
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  · refine Submodule.sum_mem _ fun b _ => ?_
    exact aeval_mem_of_inv (X := Xe x) hU _ hvU

end Orbit

section Pieces

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

theorem lin_apply_eq_of_pow {y : ↥(unitarySU 2 f K n)} (hp : p.Prime) (hyp : y ^ p = 1) {k : ℕ}
    (hk : ¬ p ∣ k) {v : Fin n → K} (hv : lin (y ^ k) v = v) : lin y v = v := by
  have hcop : Nat.Coprime k p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hiter : ∀ j : ℕ, lin (y ^ (k * j)) v = v := by
    intro j
    induction j with
    | zero => rw [Nat.mul_zero, pow_zero, lin_one]; rfl
    | succ j ih => rw [Nat.mul_succ, pow_add, lin_mul, Module.End.mul_apply, hv, ih]
  have hy1 : y ^ (k * m) = y := by rw [pow_eq_pow_mod (k * m) hyp, hm, pow_one]
  have h1 := hiter m
  rwa [hy1] at h1

namespace PieceFrame

variable (F : PieceFrame f n K h p A)

theorem nondeg (hA : MaxElemAb p A) (i : Fin F.r) : NondegOn (stdHermForm h n) (rng (F.y i)) :=
  nondegOn_rng hA (F.y_mem i)

theorem ne_bot (i : Fin F.r) : rng (F.y i) ≠ ⊥ := rng_ne_bot (F.y_ne_one i)

theorem mem_orth {i j : Fin F.r} (hij : i ≠ j) {u : Fin n → K} (hu : u ∈ rng (F.y j)) :
    u ∈ (rng (F.y i)).orthogonalBilin (stdHermForm h n) :=
  Submodule.mem_orthogonalBilin.mpr fun m hm => F.orth i j hij m hm u hu

theorem ι_single_pow (i : Fin F.r) (k : ℕ) :
    F.ι (ofAdd (Pi.single i (k : ZMod p))) = F.b i ^ k := by
  have h1 : ofAdd (Pi.single i (k : ZMod p)) =
      (ofAdd (Pi.single i 1) : Multiplicative (Fin F.r → ZMod p)) ^ k := by
    rw [← ofAdd_nsmul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  rw [h1, map_pow, F.ι_single]

theorem coord_eq_zero (hA : MaxElemAb p A) {s : Multiplicative (Fin F.r → ZMod p)} {k : Fin F.r}
    (hfix : ∀ u ∈ rng (F.y k), lin (F.ι s) u = u) : toAdd s k = 0 := by
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  by_contra hsk
  have hkp : ¬ p ∣ (toAdd s k).val := by
    intro hdvd
    apply hsk
    rw [← ZMod.natCast_zmod_val (toAdd s k)]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  apply F.ne_bot k
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  refine eq_zero_of_pow_fix h hA (F.y_mem k) hkp hu ?_
  rw [← F.ι_on s k u hu]
  exact hfix u hu

theorem eq_pow_of_triv (hA : MaxElemAb p A) {s : Multiplicative (Fin F.r → ZMod p)} {i : Fin F.r}
    (hfix : ∀ k, k ≠ i → ∀ u ∈ rng (F.y k), lin (F.ι s) u = u) :
    F.ι s = F.b i ^ (toAdd s i).val := by
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  have hs : s = ofAdd (Pi.single i (((toAdd s i).val : ℕ) : ZMod p)) := by
    apply toAdd.injective
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · rw [toAdd_ofAdd, Pi.single_eq_of_ne hk]
      exact F.coord_eq_zero hA (hfix k hk)
  rw [hs, F.ι_single_pow, toAdd_ofAdd, Pi.single_eq_same, ZMod.val_natCast,
    Nat.mod_eq_of_lt (ZMod.val_lt _)]

end PieceFrame

variable {x : ↥(unitarySU 2 f K n)} {a : K[X]}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

theorem mem_centralizer_of_mem (hA : MaxElemAb p A) (hxA : x ∈ A) {c : ↥(unitarySU 2 f K n)}
    (hc : c ∈ A) : c ∈ Subgroup.centralizer {x} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (hA.comm c hc x hxA)

theorem piece_orbW (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (hxA : x ∈ A)
    (ha : a ∈ primaryFactors (Xe x)) (i : Fin F.r) :
    (∀ v ∈ (orbW h x a).orthogonalBilin (stdHermForm h n), lin (F.b i) v = v) ∨
      ∀ v ∈ orbW h x a, lin (F.b i) v = v := by
  have hp := hA.prime
  have : NeZero p := ⟨hp.ne_zero⟩
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  obtain ⟨g, hgA, hgW, hgW'⟩ := exists_mem_restrict h hA (orbW_nondeg H ha)
    (fun c hc => orbW_inv (mem_centralizer_of_mem hA hxA hc)) (F.b_mem i)
  have hgr : g ∈ F.ι.range := by rw [F.ι_range]; exact hgA
  obtain ⟨s, rfl⟩ := hgr
  have htriv : ∀ k, k ≠ i → ∀ u ∈ rng (F.y k), lin (F.ι s) u = u := by
    intro k hk u hu
    obtain ⟨w, hwW, hw', hwU⟩ := exists_orbW_decomp H ha u
    have hwk : w ∈ rng (F.y k) := hwU _ (rng_inv hA (F.y_mem k) hxA) hu
    have hbw : lin (F.b i) w = w := F.b_off i w (F.mem_orth (Ne.symm hk) hwk)
    calc lin (F.ι s) u = lin (F.ι s) w + lin (F.ι s) (u - w) := by
          rw [← map_add, add_sub_cancel]
      _ = u := by rw [hgW w hwW, hgW' _ hw', hbw, add_sub_cancel]
  have hg := F.eq_pow_of_triv hA htriv
  by_cases hsi : toAdd s i = 0
  · right
    intro v hv
    rw [← hgW v hv, hg, hsi, ZMod.val_zero, pow_zero, lin_one]
    rfl
  · left
    intro v hv
    have hkp : ¬ p ∣ (toAdd s i).val := by
      intro hdvd
      apply hsi
      rw [← ZMod.natCast_zmod_val (toAdd s i)]
      exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    refine lin_apply_eq_of_pow hp (hA.pow _ (F.b_mem i)) hkp ?_
    rw [← hg]
    exact hgW' v hv

end Pieces

end NsFrameComp

end CFSG.StandardType
