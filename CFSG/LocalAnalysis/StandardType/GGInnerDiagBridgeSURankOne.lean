module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTorus

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace InnerDiagSU

section TwoByTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem block_identity :
    !![1, 0; 1, 1] * !![1, 1; 0, 1] * !![1, 0; 1, 1] * !![(1 : F), 1; 0, 1] =
      !![1, 1; 0, 1] * !![1, 0; 1, 1] * !![1, 1; 0, 1] * !![(1 : F), 1; 0, 1] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination h2

theorem eq_one_of_block_eq_smul {e c : F}
    (h : !![1, 0; e, 1] * !![1, 1; 0, 1] * !![1, 0; e, 1] * !![(1 : F), 1; 0, 1] =
      c • (!![1, 1; 0, 1] * !![1, 0; e, 1] * !![1, 1; 0, 1] * !![(1 : F), 1; 0, 1])) :
    e = 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc : c = e := by linear_combination (-1 : F) * h01 + (1 - c - c * e) * h2
  subst hc
  have hsq : (1 + c) * (1 + c) = 0 := by linear_combination h00 + (c + c ^ 2) * h2
  have h1 : 1 + c = 0 := mul_self_eq_zero.mp hsq
  linear_combination h1 - h2

end TwoByTwo

section Blocks

variable {F : Type*} [Field F] {n : ℕ}

theorem toBlock_mul_scalar (p q : Fin n) (M : Matrix (Fin n) (Fin n) F) (c : F) :
    toBlock p q (M * Matrix.scalar (Fin n) c) = c • toBlock p q M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SUExtras.toBlock, Matrix.scalar_apply, mul_diagonal, mul_comm]

@[expose] def blkPair (p : Fin n) (s : Fin n) : ℕ :=
  if s = p ∨ s = Fin.rev p then 1 else 0

theorem blkPair_hblk (p c : Fin n) (hc : blkPair p c = blkPair p p) : c = p ∨ c = Fin.rev p := by
  by_contra h
  have h1 : blkPair p c = 0 := ite_eq_right_iff.mpr fun h' => absurd h' h
  have h2 : blkPair p p = 1 := ite_eq_left_iff.mpr fun h' => absurd (Or.inl rfl) h'
  omega

theorem blkPair_rev (p : Fin n) : blkPair p (Fin.rev p) = blkPair p p := by
  unfold blkPair
  simp

theorem isBlk_longRootMatrix (p : Fin n) (c : F) :
    IsBlk (blkPair p) (longRootMatrix p c) := by
  intro a b hab
  rw [longRootMatrix, Matrix.add_apply, single_apply]
  split_ifs with h
  · exfalso
    obtain ⟨rfl, rfl⟩ := h
    exact hab ⟨by simp [blkPair], by simp [blkPair]⟩
  · rw [add_zero]

theorem isBlk_longRootMatrix_rev (p : Fin n) (c : F) :
    IsBlk (blkPair p) (longRootMatrix (Fin.rev p) c) := by
  intro a b hab
  rw [longRootMatrix, Matrix.add_apply, single_apply, Fin.rev_rev]
  split_ifs with h
  · exfalso
    obtain ⟨rfl, rfl⟩ := h
    exact hab ⟨by simp [blkPair], by simp [blkPair]⟩
  · rw [add_zero]

theorem toBlock_longRootMatrix {p : Fin n} (hp : p ≠ Fin.rev p) (c : F) :
    toBlock p (Fin.rev p) (longRootMatrix p c) = !![1, c; 0, 1] := by
  have hp' : Fin.rev p ≠ p := fun h => hp h.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SUExtras.toBlock, longRootMatrix, one_apply, hp, hp']

theorem toBlock_longRootMatrix_rev {p : Fin n} (hp : p ≠ Fin.rev p) (c : F) :
    toBlock p (Fin.rev p) (longRootMatrix (Fin.rev p) c) = !![1, 0; c, 1] := by
  have hp' : Fin.rev p ≠ p := fun h => hp h.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SUExtras.toBlock, longRootMatrix, one_apply, hp, hp']

theorem eq_of_isBlk_blkPair {p : Fin n} {M N : Matrix (Fin n) (Fin n) F}
    (hM : IsBlk (blkPair p) M) (hN : IsBlk (blkPair p) N)
    (h : toBlock p (Fin.rev p) M = toBlock p (Fin.rev p) N) : M = N := by
  ext a b
  by_cases hab : blkPair p a = blkPair p b ∧ blkPair p a ≠ 0
  · have ha : a = p ∨ a = Fin.rev p := by
      unfold blkPair at hab
      split_ifs at hab with h1 <;> simp_all
    have hb : b = p ∨ b = Fin.rev p := by
      unfold blkPair at hab
      split_ifs at hab with h1 <;> simp_all
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simpa [SUExtras.toBlock] using congrFun (congrFun h 0) 0
    · simpa [SUExtras.toBlock] using congrFun (congrFun h 0) 1
    · simpa [SUExtras.toBlock] using congrFun (congrFun h 1) 0
    · simpa [SUExtras.toBlock] using congrFun (congrFun h 1) 1
  · rw [hM a b hab, hN a b hab]

end Blocks

section DiagConj

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem diagonal_mul_diagonal_inv (t : Fin n → F) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1) :
    diagonal t * diagonal (fun s => (t s)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext s
  exact mul_inv_cancel₀ (ne_zero_of_unitary ht s)

theorem conjSU_diagJ_rootHom (t : Fin n → F) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    {i j : Fin n} (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : F) :
    conjSU (diagJ t ht) (isJUnitary_diagJ t ht) (rootHom σ hσ hij hi hj (Multiplicative.ofAdd c)) =
      rootHom σ hσ hij hi hj (Multiplicative.ofAdd (t i * c * (t j)⁻¹)) := by
  apply mat_injective
  have h := signedPerm_mul_rootMatrix (σ := σ) (π := 1) (fun _ => rfl) ht i j c
  rw [SpecialLinear.signedPerm_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h
  rw [mat_apply (conjSU _ _ _), coe_conjSU, Units.val_mul, Units.val_mul, coe_diagJ, coe_diagJ_inv,
    mat_apply, coe_rootHom, coe_rootHom, toAdd_ofAdd, toAdd_ofAdd, h, Matrix.mul_assoc,
    diagonal_mul_diagonal_inv t ht, Matrix.mul_one]

omit hσ in
theorem conjSU_diagJ_longRootHom (t : Fin n → F) (ht : ∀ s, σ (t s) * t (Fin.rev s) = 1)
    {i : Fin n} (hi : i ≠ Fin.rev i) (z : traceZero σ) :
    conjSU (diagJ t ht) (isJUnitary_diagJ t ht) (longRootHom σ hi (Multiplicative.ofAdd z)) =
      longRootHom σ hi (Multiplicative.ofAdd ⟨t i * z * (t (Fin.rev i))⁻¹,
        (mem_traceZero σ).mpr (mul_mem_traceZero_of_unitary ht i ((mem_traceZero σ).mp z.2))⟩) := by
  apply mat_injective
  have h := signedPerm_mul_longRootMatrix (σ := σ) (π := 1) (fun _ => rfl) ht i (z : F)
  rw [SpecialLinear.signedPerm_one, Equiv.Perm.one_apply] at h
  rw [mat_apply (conjSU _ _ _), coe_conjSU, Units.val_mul, Units.val_mul, coe_diagJ, coe_diagJ_inv,
    mat_apply, coe_longRootHom, coe_longRootHom, toAdd_ofAdd, toAdd_ofAdd, h, Matrix.mul_assoc,
    diagonal_mul_diagonal_inv t ht, Matrix.mul_one]

end DiagConj

section RankOne

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

@[expose] noncomputable def shortX {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    SU (unitaryInvolution F 2 f) n :=
  rootHom _ (unitaryInvolution_involutive hF) (lowIdx_ne_succ hk) (lowIdx_ne_rev k k)
    (lowIdx_ne_rev _ _) (Multiplicative.ofAdd c)

@[expose] noncomputable def shortY {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    SU (unitaryInvolution F 2 f) n :=
  rootHom _ (unitaryInvolution_involutive hF) (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _)
    (lowIdx_ne_rev k k) (Multiplicative.ofAdd c)

theorem shortX_mem {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    shortX hF hk c ∈ rootGroup _ (unitaryInvolution_involutive hF) n (Pi.single k 1) :=
  rootHom_mem _ _ _ _ (short_facts hk).2.2.2 (toStd_short hk).symm _

theorem shortY_mem {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (c : F) :
    shortY hF hk c ∈ rootGroup _ (unitaryInvolution_involutive hF) n (-Pi.single k 1) :=
  rootHom_mem _ _ _ _ (lowIdx_ne_rev _ _) (toStd_short_neg hk).symm _

include hF in
theorem eq_one_of_rankOne_short (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) {G : Type*} [Group G] (β γ : SU (unitaryInvolution F 2 f) n →* G)
    (hker : γ.ker ≤ Subgroup.center _) (e : F)
    (hpos : ∀ c : F, β (shortX hF hk c) = γ (shortX hF hk c))
    (hneg : ∀ c : F, β (shortY hF hk c) = γ (shortY hF hk (e * c))) : e = 1 := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨h1, -, -, h4⟩ := short_facts (n := n) hk
  have h5 : lowIdx (n := n) k ≠ Fin.rev (lowIdx ⟨k.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hxL : ∀ c, shortX hF hk c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k :=
    fun c => Subgroup.mem_sup_left (shortX_mem hF hk c)
  have hyL : ∀ c, shortY hF hk c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k :=
    fun c => Subgroup.mem_sup_right (shortY_mem hF hk c)
  have hbx : ∀ c, SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩)
      (mat _ n (shortX hF hk c)) = !![1, c; 0, 1] := by
    intro c
    rw [toBlock_of_mem_pos hk (shortX_mem hF hk c), mat_apply, shortX, coe_rootHom, toAdd_ofAdd,
      rootMatrix_apply_pq h1 h4]
  have hby : ∀ c, SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩)
      (mat _ n (shortY hF hk c)) = !![1, 0; c, 1] := by
    intro c
    rw [toBlock_of_mem_neg hk (shortY_mem hF hk c), mat_apply, shortY, coe_rootHom, toAdd_ofAdd,
      rootMatrix_apply_pq h1.symm h5]
  have hmul : ∀ g g' : SU (unitaryInvolution F 2 f) n,
      g ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k →
        SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n (g * g')) =
          SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n g) *
            SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n g') := fun g g' hg => by
    rw [map_mul, toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk)
      (isBlk_short_of_mem hk hg).1]
  have hblk4 : ∀ a b c d : SU (unitaryInvolution F 2 f) n,
      a ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k →
      b ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k →
      c ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup _ hσ n) k →
        SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n (a * b * c * d)) =
          SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n a) *
            SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n b) *
            SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n c) *
            SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat _ n d) := by
    intro a b c d ha hb hc
    rw [hmul _ _ (mul_mem (mul_mem ha hb) hc), hmul _ _ (mul_mem ha hb), hmul _ _ ha]
  have hbase : shortY hF hk 1 * shortX hF hk 1 * shortY hF hk 1 * shortX hF hk 1 =
      shortX hF hk 1 * shortY hF hk 1 * shortX hF hk 1 * shortX hF hk 1 := by
    apply eq_of_toBlock_short hk
      (mul_mem (mul_mem (mul_mem (hyL 1) (hxL 1)) (hyL 1)) (hxL 1))
      (mul_mem (mul_mem (mul_mem (hxL 1) (hyL 1)) (hxL 1)) (hxL 1))
    rw [hblk4 _ _ _ _ (hyL 1) (hxL 1) (hyL 1), hblk4 _ _ _ _ (hxL 1) (hyL 1) (hxL 1), hbx, hby]
    exact block_identity
  have hγ : γ (shortY hF hk e * shortX hF hk 1 * shortY hF hk e * shortX hF hk 1) =
      γ (shortX hF hk 1 * shortY hF hk e * shortX hF hk 1 * shortX hF hk 1) := by
    have h := congrArg β hbase
    simp only [map_mul, hpos, hneg, mul_one] at h
    simpa only [map_mul] using h
  have hz : (shortX hF hk 1 * shortY hF hk e * shortX hF hk 1 * shortX hF hk 1)⁻¹ *
      (shortY hF hk e * shortX hF hk 1 * shortY hF hk e * shortX hF hk 1) ∈
        Subgroup.center _ :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hγ, inv_mul_cancel])
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hF hn hnq hz
  have hB : mat _ n (shortY hF hk e * shortX hF hk 1 * shortY hF hk e * shortX hF hk 1) =
      mat _ n (shortX hF hk 1 * shortY hF hk e * shortX hF hk 1 * shortX hF hk 1) *
        Matrix.scalar (Fin n) c := by
    rw [← hc, ← map_mul, mul_inv_cancel_left]
  have hblk := congrArg (SUExtras.toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩)) hB
  rw [toBlock_mul_scalar, hblk4 _ _ _ _ (hyL e) (hxL 1) (hyL e),
    hblk4 _ _ _ _ (hxL 1) (hyL e) (hxL 1), hbx, hby] at hblk
  exact eq_one_of_block_eq_smul hblk

@[expose] def oneTZ : traceZero (unitaryInvolution F 2 f) := ⟨1, one_mem_traceZero⟩

include hF in
theorem eq_one_of_rankOne_long (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : Fin n}
    (hp : p ≠ Fin.rev p) {G : Type*} [Group G] (β γ : SU (unitaryInvolution F 2 f) n →* G)
    (hker : γ.ker ≤ Subgroup.center _) (e : F)
    (hpos : ∀ z : traceZero (unitaryInvolution F 2 f),
      β (longRootHom _ hp (Multiplicative.ofAdd z)) = γ (longRootHom _ hp (Multiplicative.ofAdd z)))
    (hneg : ∀ z : traceZero (unitaryInvolution F 2 f), ∃ z' : traceZero (unitaryInvolution F 2 f),
      (z' : F) = e * z ∧ β (longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z)) =
        γ (longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z'))) : e = 1 := by
  obtain ⟨z', hz'e, hz'⟩ := hneg oneTZ
  have hz'v : (z' : F) = e := by rw [hz'e]; exact mul_one e
  set X : traceZero (unitaryInvolution F 2 f) → SU (unitaryInvolution F 2 f) n :=
    fun z => longRootHom _ hp (Multiplicative.ofAdd z) with hX
  set Y : traceZero (unitaryInvolution F 2 f) → SU (unitaryInvolution F 2 f) n :=
    fun z => longRootHom _ (rev_ne_rev_rev hp) (Multiplicative.ofAdd z) with hY
  have hmX : ∀ z, mat _ n (X z) = longRootMatrix p (z : F) := fun z => by
    rw [mat_apply, hX, coe_longRootHom, toAdd_ofAdd]
  have hmY : ∀ z, mat _ n (Y z) = longRootMatrix (Fin.rev p) (z : F) := fun z => by
    rw [mat_apply, hY, coe_longRootHom, toAdd_ofAdd]
  have hbX : ∀ z, IsBlk (blkPair p) (mat _ n (X z)) := fun z => by
    rw [hmX]; exact isBlk_longRootMatrix p _
  have hbY : ∀ z, IsBlk (blkPair p) (mat _ n (Y z)) := fun z => by
    rw [hmY]; exact isBlk_longRootMatrix_rev p _
  have htX : ∀ z, SUExtras.toBlock p (Fin.rev p) (mat _ n (X z)) = !![1, (z : F); 0, 1] :=
    fun z => by rw [hmX]; exact toBlock_longRootMatrix hp _
  have htY : ∀ z, SUExtras.toBlock p (Fin.rev p) (mat _ n (Y z)) = !![1, 0; (z : F), 1] :=
    fun z => by rw [hmY]; exact toBlock_longRootMatrix_rev hp _
  have hmul : ∀ M N : Matrix (Fin n) (Fin n) F, IsBlk (blkPair p) M →
      SUExtras.toBlock p (Fin.rev p) (M * N) =
        SUExtras.toBlock p (Fin.rev p) M * SUExtras.toBlock p (Fin.rev p) N :=
    fun M N hM => toBlock_mul hp (blkPair_hblk p) (blkPair_rev p) hM
  have hblk4 : ∀ a b c d : SU (unitaryInvolution F 2 f) n, IsBlk (blkPair p) (mat _ n a) →
      IsBlk (blkPair p) (mat _ n b) → IsBlk (blkPair p) (mat _ n c) →
        SUExtras.toBlock p (Fin.rev p) (mat _ n (a * b * c * d)) =
          SUExtras.toBlock p (Fin.rev p) (mat _ n a) * SUExtras.toBlock p (Fin.rev p) (mat _ n b) *
            SUExtras.toBlock p (Fin.rev p) (mat _ n c) *
              SUExtras.toBlock p (Fin.rev p) (mat _ n d) := by
    intro a b c d ha hb hc
    rw [map_mul, map_mul, map_mul, hmul _ _ ((ha.mul hb).mul hc), hmul _ _ (ha.mul hb),
      hmul _ _ ha]
  have hbase : Y oneTZ * X oneTZ * Y oneTZ * X oneTZ = X oneTZ * Y oneTZ * X oneTZ * X oneTZ := by
    apply mat_injective
    refine eq_of_isBlk_blkPair (p := p) ?_ ?_ ?_
    · rw [map_mul, map_mul, map_mul]
      exact (((hbY _).mul (hbX _)).mul (hbY _)).mul (hbX _)
    · rw [map_mul, map_mul, map_mul]
      exact (((hbX _).mul (hbY _)).mul (hbX _)).mul (hbX _)
    · rw [hblk4 _ _ _ _ (hbY _) (hbX _) (hbY _), hblk4 _ _ _ _ (hbX _) (hbY _) (hbX _), htX, htY]
      exact block_identity
  have hγ : γ (Y z' * X oneTZ * Y z' * X oneTZ) = γ (X oneTZ * Y z' * X oneTZ * X oneTZ) := by
    have h := congrArg β hbase
    simp only [map_mul] at h
    rw [hpos, hz'] at h
    simpa only [map_mul] using h
  have hz : (X oneTZ * Y z' * X oneTZ * X oneTZ)⁻¹ * (Y z' * X oneTZ * Y z' * X oneTZ) ∈
      Subgroup.center _ :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hγ, inv_mul_cancel])
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hF hn hnq hz
  have hB : mat _ n (Y z' * X oneTZ * Y z' * X oneTZ) =
      mat _ n (X oneTZ * Y z' * X oneTZ * X oneTZ) * Matrix.scalar (Fin n) c := by
    rw [← hc, ← map_mul, mul_inv_cancel_left]
  have hblk := congrArg (SUExtras.toBlock p (Fin.rev p)) hB
  rw [toBlock_mul_scalar, hblk4 _ _ _ _ (hbY _) (hbX _) (hbY _),
    hblk4 _ _ _ _ (hbX _) (hbY _) (hbX _), htX, htY, hz'v] at hblk
  exact eq_one_of_block_eq_smul hblk

end RankOne

end InnerDiagSU

end CFSG.StandardType
