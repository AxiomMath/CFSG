module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterCheckFastPart5

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CenterProofFast

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

open CFSG.StandardType.F4ExplicitPos.CenterCheckFast

variable {K : Type} [Field K] [CharP K 2]

noncomputable def Bf
    (K : Type) [Field K] (u w : RootModule Tag.F4 K) : K :=
  ∑ p ∈ Finset.range 52, ∑ q ∈ Finset.range 52,
    posCoord Tag.F4 K p u * (gramZ p q : K) * posCoord Tag.F4 K q w

theorem intCast_eq_of_emod_eq {z w : ℤ} (h : z % 2 = w % 2) : (z : K) = (w : K) := by
  have hd : (z - w) % 2 = 0 := (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp h
  have h0 : (z : K) - (w : K) = 0 := by
    have := (CharP.intCast_eq_zero_iff K 2 (z - w)).2 (Int.dvd_of_emod_eq_zero hd)
    push_cast at this
    exact this
  exact sub_eq_zero.mp h0

theorem Bf_add_left
    (u v w : RootModule Tag.F4 K) :
    Bf K (u + v) w = Bf K u w + Bf K v w := by
  unfold Bf
  simp only [map_add, add_mul, Finset.sum_add_distrib]

theorem Bf_smul_left
    (c : K) (u w : RootModule Tag.F4 K) :
    Bf K (c • u) w = c * Bf K u w := by
  unfold Bf
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q hq
  ring

theorem Bf_add_right
    (u v w : RootModule Tag.F4 K) :
    Bf K u (v + w) = Bf K u v + Bf K u w := by
  unfold Bf
  simp only [map_add, mul_add, Finset.sum_add_distrib]

theorem Bf_smul_right
    (c : K) (u w : RootModule Tag.F4 K) :
    Bf K u (c • w) = c * Bf K u w := by
  unfold Bf
  simp only [map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q hq
  ring

theorem Bf_sum_left
    {ι : Type*} (s : Finset ι) (f : ι → RootModule Tag.F4 K)
    (w : RootModule Tag.F4 K) : Bf K (∑ i ∈ s, f i) w = ∑ i ∈ s, Bf K (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bf_add_left, ih]

theorem Bf_sum_right
    {ι : Type*} (s : Finset ι) (f : ι → RootModule Tag.F4 K)
    (u : RootModule Tag.F4 K) : Bf K u (∑ i ∈ s, f i) = ∑ i ∈ s, Bf K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bf_add_right, ih]

theorem Bf_basis
    {p q : ℕ} (hp : p < 52) (hq : q < 52) :
    Bf K (posVec Tag.F4 K p) (posVec Tag.F4 K q) = (gramZ p q : K) := by
  unfold Bf
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · rw [posCoord_posVec (p := p) (q := p) (show p < dim Tag.F4 from hp), if_pos rfl,
        posCoord_posVec (p := q) (q := q) (show q < dim Tag.F4 from hq), if_pos rfl,
        one_mul, mul_one]
    · intro b hb hne
      rw [posCoord_posVec (p := b) (q := q) (show q < dim Tag.F4 from hq), if_neg hne, mul_zero]
    · exact fun h => absurd (Finset.mem_range.2 hq) h
  · intro p' hp' hne
    rw [posCoord_posVec (p := p') (q := p) (show p < dim Tag.F4 from hp), if_neg hne]
    simp
  · exact fun h => absurd (Finset.mem_range.2 hp) h

theorem intCast_listSum (l : List ℤ) : ((l.sum : ℤ) : K) = (l.map (Int.cast : ℤ → K)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Int.cast_add]

theorem sum_gram_dense (a : ℕ) (v : List (ℕ × ℤ)) (hv : ∀ x ∈ v, x.1 < 52) :
    ∑ b ∈ Finset.range 52, (gramZ a b : K) * (coefAt b v : K) =
      (v.map fun x => (gramZ a x.1 : K) * (x.2 : K)).sum := by
  induction v with
  | nil => simp [coefAt]
  | cons x v ih =>
    have hx : x.1 < 52 := hv x (by simp)
    have ih' := ih (fun y hy => hv y (by simp [hy]))
    have hcb : ∀ b, coefAt b (x :: v) = (if x.1 = b then x.2 else 0) + coefAt b v := by
      intro b; simp [coefAt]
    calc ∑ b ∈ Finset.range 52, (gramZ a b : K) * (coefAt b (x :: v) : K)
        = ∑ b ∈ Finset.range 52, (gramZ a b : K) *
            (((if x.1 = b then x.2 else 0 : ℤ) : K) + (coefAt b v : K)) := by
          apply Finset.sum_congr rfl; intro b hb
          rw [hcb b, Int.cast_add]
      _ = ∑ b ∈ Finset.range 52, ((gramZ a b : K) * ((if x.1 = b then x.2 else 0 : ℤ) : K)
            + (gramZ a b : K) * (coefAt b v : K)) := by
          apply Finset.sum_congr rfl; intro b hb; ring
      _ = (∑ b ∈ Finset.range 52, (gramZ a b : K) * ((if x.1 = b then x.2 else 0 : ℤ) : K))
            + ∑ b ∈ Finset.range 52, (gramZ a b : K) * (coefAt b v : K) := by
          rw [Finset.sum_add_distrib]
      _ = (gramZ a x.1 : K) * (x.2 : K)
            + (v.map fun y => (gramZ a y.1 : K) * (y.2 : K)).sum := by
          rw [ih']
          congr 1
          rw [Finset.sum_eq_single x.1]
          · rw [if_pos rfl]
          · intro b hb hne; rw [if_neg (Ne.symm hne), Int.cast_zero, mul_zero]
          · intro h; exact absurd (Finset.mem_range.2 hx) h
      _ = ((x :: v).map fun y => (gramZ a y.1 : K) * (y.2 : K)).sum := by
          rw [List.map_cons, List.sum_cons]

theorem Bf_posVec_vecOf
    {p : ℕ} (hp : p < 52) {v : List (ℕ × ℤ)}
    (hv : ValidVec Tag.F4 v) :
    Bf K (posVec Tag.F4 K p) (vecOf Tag.F4 K v) = (sparseB [(p, 1)] v : K) := by
  have hdense : Bf K (posVec Tag.F4 K p) (vecOf Tag.F4 K v) =
      ∑ b ∈ Finset.range 52, (gramZ p b : K) * (coefAt b v : K) := by
    unfold Bf
    rw [Finset.sum_eq_single p]
    · apply Finset.sum_congr rfl; intro b hb
      rw [posCoord_posVec (p := p) (q := p) (show p < dim Tag.F4 from hp), if_pos rfl,
        one_mul, posCoord_vecOf b hv]
    · intro p' hp' hne
      simp [posCoord_posVec (p := p') (q := p) (show p < dim Tag.F4 from hp), hne]
    · exact fun h => absurd (Finset.mem_range.2 hp) h
  rw [hdense, sum_gram_dense p v hv]
  unfold sparseB
  simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero, one_mul]
  rw [intCast_listSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro y hy
  rw [Function.comp_apply, Int.cast_mul]

theorem Bf_vecOf
    {u v : List (ℕ × ℤ)} (hu : ValidVec Tag.F4 u) (hv : ValidVec Tag.F4 v) :
    Bf K (vecOf Tag.F4 K u) (vecOf Tag.F4 K v) = (sparseB u v : K) := by
  induction u with
  | nil => simp [Bf, sparseB]
  | cons x u ih =>
    have hu' : ValidVec Tag.F4 u := fun y hy => hu y (by simp [hy])
    have hx : x.1 < 52 := hu x (by simp)
    calc Bf K (vecOf Tag.F4 K (x :: u)) (vecOf Tag.F4 K v)
        = Bf K ((x.2 : K) • posVec Tag.F4 K x.1) (vecOf Tag.F4 K v)
            + Bf K (vecOf Tag.F4 K u) (vecOf Tag.F4 K v) := by
          rw [vecOf_cons, Bf_add_left]
      _ = (x.2 : K) * Bf K (posVec Tag.F4 K x.1) (vecOf Tag.F4 K v)
            + (sparseB u v : K) := by
          rw [Bf_smul_left, ih hu']
      _ = (x.2 : K) * (sparseB [(x.1, 1)] v : K) + (sparseB u v : K) := by
          rw [Bf_posVec_vecOf hx hv]
      _ = ((sparseB (x :: u) v : ℤ) : K) := by
          rw [sparseB_cons x u v]; push_cast; ring

theorem Bf_eq_of_basis
    (M : Module.End K (RootModule Tag.F4 K))
    (hM : ∀ p q, p < 52 → q < 52 →
      Bf K (M (posVec Tag.F4 K p)) (M (posVec Tag.F4 K q)) =
        Bf K (posVec Tag.F4 K p) (posVec Tag.F4 K q))
    (u w : RootModule Tag.F4 K) : Bf K (M u) (M w) = Bf K u w := by
  have expand : ∀ (N : Module.End K (RootModule Tag.F4 K)) (α β : ℕ → K),
      Bf K (N (∑ p ∈ Finset.range 52, α p • posVec Tag.F4 K p))
        (N (∑ q ∈ Finset.range 52, β q • posVec Tag.F4 K q)) =
        ∑ p ∈ Finset.range 52, ∑ q ∈ Finset.range 52,
          α p * β q * Bf K (N (posVec Tag.F4 K p)) (N (posVec Tag.F4 K q)) := by
    intro N α β
    simp only [map_sum, map_smul]
    rw [Bf_sum_left]
    apply Finset.sum_congr rfl; intro p hp
    rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q hq
    rw [Bf_smul_right]; ring
  have h1 := expand M (fun p => posCoord Tag.F4 K p u) (fun q => posCoord Tag.F4 K q w)
  have h2 := expand 1 (fun p => posCoord Tag.F4 K p u) (fun q => posCoord Tag.F4 K q w)
  rw [← eq_sum_posCoord_smul_posVec u, ← eq_sum_posCoord_smul_posVec w] at h1
  rw [← eq_sum_posCoord_smul_posVec u, ← eq_sum_posCoord_smul_posVec w] at h2
  simp only [Module.End.one_apply] at h2
  rw [h1]
  refine Eq.trans (Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_) h2.symm
  rw [hM p q (Finset.mem_range.1 hp) (Finset.mem_range.1 hq)]

noncomputable def f4GenCoeff (K : Type) [Field K] (g : ℕ) (c : K) : Module.End K (RootModule Tag.F4
    K) :=
  ∑ k ∈ Finset.range 4, c ^ k • coeffOp Tag.F4 K (f4GenY g) (f4GenI g) k

theorem f4GenCoeff_even
    (i : Fin Tag.F4.rank) (c : K) :
    f4GenCoeff K (2 * (i : ℕ)) c = xOp .F4 K i c := by
  have hY : f4GenY (2 * (i : ℕ)) = false := by
    simp only [f4GenY]
    rw [show (2 * (i : ℕ)) % 2 = 0 by omega]
    rfl
  have hI : f4GenI (2 * (i : ℕ)) = i := by
    apply Fin.ext
    simp only [f4GenI]
    have hlt : (i : ℕ) < 4 := i.isLt
    omega
  unfold f4GenCoeff coeffOp
  rw [hY, hI]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (xOp_eq_sum_xCoeff i c).symm

theorem f4GenCoeff_odd
    (i : Fin Tag.F4.rank) (c : K) :
    f4GenCoeff K (2 * (i : ℕ) + 1) c = yOp .F4 K i c := by
  have hY : f4GenY (2 * (i : ℕ) + 1) = true := by
    simp only [f4GenY]
    rw [show (2 * (i : ℕ) + 1) % 2 = 1 by omega]
    rfl
  have hI : f4GenI (2 * (i : ℕ) + 1) = i := by
    apply Fin.ext
    simp only [f4GenI]
    have hlt : (i : ℕ) < 4 := i.isLt
    omega
  unfold f4GenCoeff coeffOp
  rw [hY, hI]
  simp only [↓reduceIte]
  exact (yOp_eq_sum_yCoeff i c).symm

theorem f4GenCoeff_posVec
    (g : ℕ) (hg : g < 8) (c : K) (p : ℕ) (hp : p < 52) :
    f4GenCoeff K g c (posVec Tag.F4 K p) =
      ∑ k ∈ Finset.range 4, c ^ k • vecOf Tag.F4 K (f4ColData g k p) := by
  unfold f4GenCoeff
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro k hk
  rw [LinearMap.smul_apply]
  congr 1
  by_cases h0 : k = 0
  · subst h0
    rw [coeffOp_zero_f4, Module.End.one_apply, posVec_eq_vecOf_single]
    simp [f4ColData]
  · have hk3 : k ≤ 3 := by have := Finset.mem_range.1 hk; omega
    rw [posVec_eq_vecOf_single (τ := Tag.F4) (R := K) p,
      (coeffOp_vecOf (k := k) simpleRow_F4 f4_allValid K _ _
        (by have := Finset.mem_range.1 hk; omega)
        (validVec_single (show p < dim Tag.F4 from hp))).1,
      f4ColData_eq_coeffVec g hg k hk3 p]

theorem polyCoeff_regroup (g p q : ℕ) (c : K) :
    (∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        c ^ (a + b) * (sparseB (f4ColData g a p) (f4ColData g b q) : K))
      = ∑ d ∈ Finset.range 7, c ^ d * (polyCoeff g p q d : K) := by
  have e : ∀ a b : ℕ, a < 4 → b < 4 →
      c ^ (a + b) * (sparseB (f4ColData g a p) (f4ColData g b q) : K) =
      ∑ d ∈ Finset.range 7,
        (if a + b = d then c ^ d * (sparseB (f4ColData g a p) (f4ColData g b q) : K)
          else 0) := by
    intro a b ha hb
    rw [Finset.sum_eq_single (a + b)]
    · rw [if_pos rfl]
    · intro d hd hne; rw [if_neg (fun h => hne h.symm)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  calc (∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        c ^ (a + b) * (sparseB (f4ColData g a p) (f4ColData g b q) : K))
      = ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4, ∑ d ∈ Finset.range 7,
          (if a + b = d then c ^ d * (sparseB (f4ColData g a p) (f4ColData g b q) : K)
            else 0) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        exact e a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb)
    _ = ∑ a ∈ Finset.range 4, ∑ d ∈ Finset.range 7, ∑ b ∈ Finset.range 4,
          (if a + b = d then c ^ d * (sparseB (f4ColData g a p) (f4ColData g b q) : K)
            else 0) := by
        apply Finset.sum_congr rfl; intro a ha
        rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range 7, ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
          (if a + b = d then c ^ d * (sparseB (f4ColData g a p) (f4ColData g b q) : K)
            else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range 7, c ^ d * (polyCoeff g p q d : K) := by
        apply Finset.sum_congr rfl; intro d hd
        rw [polyCoeff]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b hb
        by_cases hab : a + b = d <;> simp [hab]

theorem f4GenCoeff_Bf_basis
    (g : ℕ) (hg : g < 8) (c : K) {p q : ℕ} (hp : p < 52)
    (hq : q < 52) :
    Bf K (f4GenCoeff K g c (posVec Tag.F4 K p)) (f4GenCoeff K g c (posVec Tag.F4 K q)) =
      (gramZ p q : K) := by
  rw [f4GenCoeff_posVec g hg c p hp, f4GenCoeff_posVec g hg c q hq]
  rw [Bf_sum_left]
  calc (∑ a ∈ Finset.range 4,
        Bf K (c ^ a • vecOf Tag.F4 K (f4ColData g a p))
          (∑ b ∈ Finset.range 4, c ^ b • vecOf Tag.F4 K (f4ColData g b q)))
      = ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
          c ^ a * (c ^ b * (sparseB (f4ColData g a p) (f4ColData g b q) : K)) := by
        apply Finset.sum_congr rfl; intro a ha
        rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b hb
        rw [Bf_smul_right]
        have ha4 : a ≤ 3 := by have := Finset.mem_range.1 ha; omega
        have hb4 : b ≤ 3 := by have := Finset.mem_range.1 hb; omega
        rw [Bf_vecOf (validVec_f4ColData g hg a ha4 p hp)
          (validVec_f4ColData g hg b hb4 q hq)]
    _ = ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
          c ^ (a + b) * (sparseB (f4ColData g a p) (f4ColData g b q) : K) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro b hb
        rw [← mul_assoc, ← pow_add]
    _ = ∑ d ∈ Finset.range 7, c ^ d * (polyCoeff g p q d : K) := polyCoeff_regroup g p q c
    _ = (gramZ p q : K) := by
        rw [Finset.sum_eq_single 0]
        · rw [show (polyCoeff g p q 0 : K) = (gramZ p q : K) from
            intCast_eq_of_emod_eq (by
              have := polyCoeff_spec ⟨g, hg⟩ ⟨p, hp⟩ ⟨q, hq⟩ ⟨0, by norm_num⟩
              simpa using this)]
          simp
        · intro d hd hne
          rw [show (polyCoeff g p q d : K) = 0 from by
            have h := intCast_eq_of_emod_eq (K := K) (z := polyCoeff g p q d) (w := 0) (by
              have hs := polyCoeff_spec ⟨g, hg⟩ ⟨p, hp⟩ ⟨q, hq⟩ ⟨d, by
                have := Finset.mem_range.1 hd; omega⟩
              simpa [hne] using hs)
            simpa using h]
          rw [mul_zero]
        · intro h; exact absurd (Finset.mem_range.2 (by norm_num : 0 < 7)) h

theorem f4GenCoeff_Bf
    (g : ℕ) (hg : g < 8) (c : K) (u w : RootModule Tag.F4 K) :
    Bf K (f4GenCoeff K g c u) (f4GenCoeff K g c w) = Bf K u w :=
  Bf_eq_of_basis _ (fun p q hp hq =>
    (f4GenCoeff_Bf_basis g hg c hp hq).trans (Bf_basis hp hq).symm) u w

theorem xOp_Bf
    (i : Fin Tag.F4.rank) (c : K) (u w : RootModule Tag.F4 K) :
    Bf K (xOp .F4 K i c u) (xOp .F4 K i c w) = Bf K u w := by
  have hlt : (i : ℕ) < 4 := i.isLt
  have h := f4GenCoeff_Bf (2 * (i : ℕ)) (by omega) c u w
  rwa [f4GenCoeff_even i c] at h

theorem yOp_Bf
    (i : Fin Tag.F4.rank) (c : K) (u w : RootModule Tag.F4 K) :
    Bf K (yOp .F4 K i c u) (yOp .F4 K i c w) = Bf K u w := by
  have hlt : (i : ℕ) < 4 := i.isLt
  have h := f4GenCoeff_Bf (2 * (i : ℕ) + 1) (by omega) c u w
  rwa [f4GenCoeff_odd i c] at h

end CFSG.StandardType.F4ExplicitPos.CenterProofFast
end

end
