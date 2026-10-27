module

public import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.ChainArrays

variable {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
  {W : Array (List ℤ)} {chunks : ℕ}

theorem levT_base (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    {i : ℕ} (hi : i < Q.baseCount) {k : ℕ} (hk : k < (lev n S base i).pts.size) :
    levT n S base i k (Q.base.get ⟨i, hi⟩) = levPts Q S base i k := by
  have ht := hA.transversal_of_lt hF hi hk
  have hx : levPts Q S base i k ∈ Q.orbitPoints ⟨i, hi⟩ := by
    change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).isSome = true
    rw [ht]
    rfl
  have h := (Q.transversal_getD_spec ⟨i, hi⟩ _ hx).2.2
  change ((Q.orbitSearch ⟨i, hi⟩).transversal? _).getD 1 _ = _ at h
  rwa [ht, Option.getD_some] at h

theorem ptailOK_complete (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {xs : Array (Array ℕ)} {rels : List (ℕ × ℕ × ℕ)} {E : List (Array ℕ)} :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      (∀ h ∈ Q.levelSubgroup i, A * h * X = X * (A * h) → ∃ e ∈ E, Rep n e (A * h)) →
      ptailOK n (rawLevels n S base) base x xs rels E fuel i acc = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i _ acc A hacc hE
    rw [ptailOK]
    cases hc : commA n acc x
    · rfl
    · have hcomm : A * 1 * X = X * (A * 1) := by
        rw [mul_one]
        exact (commA_iff hacc hx).1 hc
      obtain ⟨e, he, hre⟩ := hE 1 (Subgroup.one_mem _) hcomm
      rw [mul_one] at hre
      rw [Bool.not_true, Bool.false_or, List.any_eq_true]
      exact ⟨e, he, (eqA_iff hacc hre).2 rfl⟩
  | succ fuel ih =>
    intro i hi acc A hacc hE
    have hib : i < Q.baseCount := by omega
    rw [ptailOK, allLt_iff]
    intro k hk
    have hrep : Rep n (compA n acc ((rawLevels n S base)[i]!).tr[k]!) (A * levT n S base i k) :=
      rep_compA hacc (hA.rep_levT hF hib hk)
    have hT := hA.levT_mem hF hib hk
    have hrest := ih (i + 1) (by omega) _ _ hrep (fun h hh hc => by
      have e : A * levT n S base i k * h = A * (levT n S base i k * h) := mul_assoc _ _ _
      rw [e] at hc ⊢
      exact hE _ ((Q.levelSubgroup i).mul_mem hT
        (Q.levelSubgroup_antitone i (i + 1) (Nat.le_succ i) hh)) hc)
    rw [hrest, Bool.or_true]

theorem ptailOK_of_orbits_rel (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {xs : Array (Array ℕ)}
    (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {E : List (Array ℕ)}
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ Subgroup.centralizer {X} ⊓ Q.originalSubgroup)
    (hKE : ∀ g ∈ K, ∃ e ∈ E, Rep n e g) (hEK : ∀ e ∈ E, ∃ g ∈ K, Rep n e g)
    (h0 : 0 < Q.baseCount)
    (horb : ∀ k < (lev n S base 0).pts.size,
      relOK base xs rels 0 (idA n) ((rawLevels n S base)[0]!).pts[k]! = false ∨
      ∃ r < (lev n S base 0).pts.size, ∃ c ∈ K,
      c (levPts Q S base 0 r) = levPts Q S base 0 k ∧
      ptailOK n (rawLevels n S base) base x xs rels E (Q.baseCount - 1) 1
        (compA n (idA n) ((rawLevels n S base)[0]!).tr[r]!) = true) :
    ptailOK n (rawLevels n S base) base x xs rels E Q.baseCount 0 (idA n) = true := by
  obtain ⟨m, hm⟩ : ∃ m, Q.baseCount = m + 1 := ⟨Q.baseCount - 1, by omega⟩
  have hb1 : (1 : ℕ) + m = Q.baseCount := by omega
  rw [hm, ptailOK, allLt_iff]
  intro k hk
  rcases horb k hk with hf | ⟨r, hr, c, hc, hcr, htr⟩
  · rw [hf, Bool.not_false, Bool.true_or]
  rw [hm, Nat.add_sub_cancel] at htr
  have hrestK : ptailOK n (rawLevels n S base) base x xs rels E m (0 + 1)
      (compA n (idA n) ((rawLevels n S base)[0]!).tr[k]!) = true := by
    refine ptailOK_complete hA hF hx m 1 hb1 _ (1 * levT n S base 0 k)
      (rep_compA rep_idA (hA.rep_levT hF h0 hk)) ?_
    intro h hh hcomm
    have hT0 := hA.levT_mem hF h0 hk
    have hTr := hA.levT_mem hF h0 hr
    have hgP : 1 * levT n S base 0 k * h ∈ Q.levelSubgroup 0 :=
      (Q.levelSubgroup 0).mul_mem ((Q.levelSubgroup 0).mul_mem (Q.levelSubgroup 0).one_mem hT0)
        (Q.levelSubgroup_antitone 0 1 (Nat.zero_le 1) hh)
    have hcK := hK hc
    have hcP : c ∈ Q.levelSubgroup 0 := by
      rw [Q.levelSubgroup_zero_eq_original hQ]
      exact (Subgroup.mem_inf.1 hcK).2
    have hcX : c * X = X * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcK).1
    have hcX' : c⁻¹ * X = X * c⁻¹ := by
      calc c⁻¹ * X = c⁻¹ * (X * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * X) * c⁻¹ := by rw [hcX]
        _ = X * c⁻¹ := by group
    have hfix : h (Q.base.get ⟨0, h0⟩) = Q.base.get ⟨0, h0⟩ :=
      Q.levelSubgroup_fixes_base_index 1 h hh ⟨0, h0⟩ Nat.zero_lt_one
    have hgb : (1 * levT n S base 0 k * h) (Q.base.get ⟨0, h0⟩) = c (levPts Q S base 0 r) := by
      rw [hcr, Equiv.Perm.mul_apply, hfix, one_mul, levT_base hA hF h0 hk]
    have hstab : Q.levelSubgroup 1 =
        Q.levelSubgroup 0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get ⟨0, h0⟩) :=
      Q.levelSubgroup_succ_eq_stabilizer hQ ⟨0, h0⟩
    have hh' : (levT n S base 0 r)⁻¹ * (c⁻¹ * (1 * levT n S base 0 k * h)) ∈
        Q.levelSubgroup 1 := by
      rw [hstab]
      refine Subgroup.mem_inf.2 ⟨(Q.levelSubgroup 0).mul_mem ((Q.levelSubgroup 0).inv_mem hTr)
        ((Q.levelSubgroup 0).mul_mem ((Q.levelSubgroup 0).inv_mem hcP) hgP), ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, hgb, ← levT_base hA hF h0 hr]
      simp
    have e1 : 1 * levT n S base 0 r * ((levT n S base 0 r)⁻¹ * (c⁻¹ * (1 * levT n S base 0 k * h)))
        = c⁻¹ * (1 * levT n S base 0 k * h) := by group
    have hcomm' : 1 * levT n S base 0 r *
        ((levT n S base 0 r)⁻¹ * (c⁻¹ * (1 * levT n S base 0 k * h))) * X =
        X * (1 * levT n S base 0 r *
          ((levT n S base 0 r)⁻¹ * (c⁻¹ * (1 * levT n S base 0 k * h)))) := by
      rw [e1]
      calc c⁻¹ * (1 * levT n S base 0 k * h) * X = c⁻¹ * ((1 * levT n S base 0 k * h) * X) :=
            mul_assoc _ _ _
        _ = c⁻¹ * (X * (1 * levT n S base 0 k * h)) := by rw [hcomm]
        _ = c⁻¹ * X * (1 * levT n S base 0 k * h) := (mul_assoc _ _ _).symm
        _ = X * c⁻¹ * (1 * levT n S base 0 k * h) := by rw [hcX']
        _ = X * (c⁻¹ * (1 * levT n S base 0 k * h)) := mul_assoc _ _ _
    obtain ⟨e, he, hre⟩ := ptailOK_spec hA hF hQ hx hxs hrels m 1 hb1 _
      (1 * levT n S base 0 r) (rep_compA rep_idA (hA.rep_levT hF h0 hr)) htr _ hh' hcomm'
    rw [e1] at hre
    obtain ⟨g', hg'K, hg'⟩ := hEK e he
    have hg'eq : g' = c⁻¹ * (1 * levT n S base 0 k * h) :=
      Equiv.ext fun y => Fin.ext (by rw [← hg' y, hre y])
    have hgK := K.mul_mem hc (hg'eq ▸ hg'K)
    rw [mul_inv_cancel_left] at hgK
    exact hKE _ hgK
  rw [hrestK, Bool.or_true]

theorem ptailOK_of_orbits (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {xs : Array (Array ℕ)}
    (hxs : ∀ e < xs.size, Rep n xs[e]! (X ^ e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      (xs[r.2.2]!)[base[r.1]!]! = base[r.2.1]!) {E : List (Array ℕ)}
    {K : Subgroup (Equiv.Perm (Fin n))} (hK : K ≤ Subgroup.centralizer {X} ⊓ Q.originalSubgroup)
    (hKE : ∀ g ∈ K, ∃ e ∈ E, Rep n e g) (hEK : ∀ e ∈ E, ∃ g ∈ K, Rep n e g)
    (h0 : 0 < Q.baseCount)
    (horb : ∀ k < (lev n S base 0).pts.size, ∃ r < (lev n S base 0).pts.size, ∃ c ∈ K,
      c (levPts Q S base 0 r) = levPts Q S base 0 k ∧
      ptailOK n (rawLevels n S base) base x xs rels E (Q.baseCount - 1) 1
        (compA n (idA n) ((rawLevels n S base)[0]!).tr[r]!) = true) :
    ptailOK n (rawLevels n S base) base x xs rels E Q.baseCount 0 (idA n) = true :=
  ptailOK_of_orbits_rel hA hF hQ hx hxs hrels hK hKE hEK h0 fun k hk => Or.inr (horb k hk)

end CFSG.RankThree.Native
