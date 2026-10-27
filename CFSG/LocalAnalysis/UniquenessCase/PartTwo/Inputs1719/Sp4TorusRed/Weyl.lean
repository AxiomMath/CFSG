module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRootTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Weyl
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem isLinePerm_of_isPermSp {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : TorusQS.IsPermSp n π) : IsLinePerm π (spMat n) := by
  intro x y
  rw [hn]
  by_cases h : y = π x <;> simp [h]

theorem mem_torus_of_isLinePerm_one {g : StatedSp 2 K}
    (h : IsLinePerm 1 (spMat g)) : g ∈ torus 2 K := by
  have hrel : ∀ i : Fin 2, (spMat g) (Sum.inl i) (Sum.inl i) *
      (spMat g) (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have := mul_apply_swap_of_isLinePerm g.2 h (Sum.inl i)
    simpa [lineSign, Equiv.Perm.one_apply] using this
  set s : Fin 2 → Kˣ := fun i => Units.mk0 ((spMat g) (Sum.inl i) (Sum.inl i))
    (h.apply_ne_zero (Sum.inl i)) with hs
  refine ⟨s, ?_⟩
  apply statedSp_ext
  rw [coe_torusHom]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    rcases a with i | i
    · rfl
    · have hi := hrel i
      exact (eq_inv_of_mul_eq_one_right hi).symm
  · rw [Matrix.diagonal_apply_ne _ hab, h.apply_eq_zero (x := b) (y := a) hab]

theorem isLinePerm_inv {n : StatedSp 2 K} {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsLinePerm σ (spMat n)) : IsLinePerm σ⁻¹ (spMat n⁻¹) :=
  IsLinePerm.inv (g := (n : GL (Fin 2 ⊕ Fin 2) K)) hn

theorem isLinePerm_one_conj {n : StatedSp 2 K} {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsLinePerm σ (spMat n)) {t : StatedSp 2 K} (ht : t ∈ torus 2 K) :
    IsLinePerm 1 (spMat (n * t * n⁻¹)) := by
  have ht' : IsLinePerm 1 (spMat t) := isLinePerm_torusHom' ht
  have h1 : IsLinePerm (σ * 1) ((spMat n) * (spMat t)) := hn.mul ht'
  have h2 : IsLinePerm (σ * 1 * σ⁻¹) (((spMat n) * (spMat t)) * (spMat n⁻¹)) :=
    h1.mul (isLinePerm_inv hn)
  have hmat : (spMat (n * t * n⁻¹)) = ((spMat n) * (spMat t)) * (spMat n⁻¹) := by
    rw [TorusQS.spMat_mul, TorusQS.spMat_mul]
  have hperm : σ * 1 * σ⁻¹ = 1 := by ext x; simp
  rw [← hmat, hperm] at h2
  exact h2

theorem mem_normalizer_torus_of_isLinePerm {n : StatedSp 2 K} {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsLinePerm σ (spMat n)) :
    n ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact mem_torus_of_isLinePerm_one (isLinePerm_one_conj hn ht)
  · intro ht
    have h := mem_torus_of_isLinePerm_one (g := n⁻¹ * (n * t * n⁻¹) * (n⁻¹)⁻¹)
      (isLinePerm_one_conj (n := n⁻¹) (isLinePerm_inv hn) ht)
    simpa [mul_assoc] using h

theorem IsRootFree.map_conj {X : Subgroup (StatedSp 2 K)} (hX : IsRootFree X)
    {n : StatedSp 2 K} {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)} (hn : IsLinePerm σ (spMat n)) :
    IsRootFree (X.map (MulAut.conj n).toMonoidHom) := by
  intro a b hab t ht
  rw [Subgroup.mem_map] at ht
  obtain ⟨x, hxX, hx⟩ := ht
  have hx' : n⁻¹ * pairRootElt hab t * n = x := by
    rw [← hx]
    change n⁻¹ * (MulAut.conj n) x * n = x
    rw [MulAut.conj_apply]
    group
  have hconj := conj_pairRootElt (g := n⁻¹) (isLinePerm_inv hn) hab t
  rw [inv_inv] at hconj
  rw [hx'] at hconj
  have he1 : (spMat n⁻¹) (σ⁻¹ a) a ≠ 0 := (isLinePerm_inv hn).apply_ne_zero a
  have he2 : (spMat n) b (σ⁻¹ b) ≠ 0 := by
    simpa using hn.apply_ne_zero (σ⁻¹ b)
  have hzero := hX (σ⁻¹ a) (σ⁻¹ b) ((σ⁻¹).injective.ne hab)
    ((spMat n⁻¹) (σ⁻¹ a) a * (spMat n) b (σ⁻¹ b) * t) (hconj ▸ hxX)
  rcases mul_eq_zero.mp hzero with h12 | ht0
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · exact absurd h1 he1
    · exact absurd h2 he2
  · exact ht0

theorem IsLinePerm.pow {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [Field k]
    {σ : Equiv.Perm ι} {M : Matrix ι ι k} (h : IsLinePerm σ M) (n : ℕ) :
    IsLinePerm (σ ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using isLinePerm_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

theorem signedPermGroup_pow_four {σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hσ : σ ∈ signedPermGroup 2) : σ ^ 4 = 1 := by
  have hempty : (Finset.univ.filter (fun τ : Equiv.Perm (Fin 2 ⊕ Fin 2) =>
      (∀ x, τ x.swap = (τ x).swap) ∧ τ ^ 4 ≠ 1)).card = 0 := by
    decide
  by_contra h
  have hmem : σ ∈ Finset.univ.filter (fun τ : Equiv.Perm (Fin 2 ⊕ Fin 2) =>
      (∀ x, τ x.swap = (τ x).swap) ∧ τ ^ 4 ≠ 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨mem_signedPermGroup.mp hσ, h⟩
  have hpos := Finset.card_pos.mpr ⟨σ, hmem⟩
  omega

theorem isPGroup_signedPermGroup_two : IsPGroup 2 (signedPermGroup 2) := by
  intro σ
  refine ⟨2, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  simpa using signedPermGroup_pow_four σ.2

instance isNilpotent_signedPermGroup_two : Group.IsNilpotent (signedPermGroup 2) :=
  IsPGroup.isNilpotent isPGroup_signedPermGroup_two

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem torus_mulVec_line {x : StatedSp 2 K}
    (hx : x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)))
    {d : StatedSp 2 K} (hd : d ∈ torus 2 K) (j : Fin 2 ⊕ Fin 2) :
    ∃ c : K, (spMat d) *ᵥ ((spMat x) *ᵥ Pi.single j 1) =
      c • ((spMat x) *ᵥ Pi.single j 1) := by
  have hy : x⁻¹ * d * x ∈ torus 2 K := by
    have hnorm := (Subgroup.mem_normalizer_iff.mp hx) (x⁻¹ * d * x)
    refine hnorm.mpr ?_
    rwa [show x * (x⁻¹ * d * x) * x⁻¹ = d from by group]
  obtain ⟨s, hs⟩ := hy
  rw [Matrix.mulVec_mulVec, ← TorusQS.spMat_mul,
    show d * x = x * (x⁻¹ * d * x) from by group, TorusQS.spMat_mul,
    ← Matrix.mulVec_mulVec, ← hs, coe_torusHom, Matrix.diagonal_mulVec_single]
  set u : Fin 2 ⊕ Fin 2 → K :=
    Sum.elim (fun i => (s i : K)) (fun i => (((s i)⁻¹ : Kˣ) : K)) with hudef
  refine ⟨u j, ?_⟩
  have hsingle : (Pi.single j (u j) : Fin 2 ⊕ Fin 2 → K) = u j • Pi.single j 1 := by
    ext r
    by_cases hr : r = j
    · subst hr; simp
    · simp [hr]
  rw [mul_one, hsingle, Matrix.mulVec_smul]

theorem exists_single_entry_of_mem_normalizer (hK : 8 ≤ Nat.card K) {x : StatedSp 2 K}
    (hx : x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)))
    (j : Fin 2 ⊕ Fin 2) :
    ∃ k, (spMat x) k j ≠ 0 ∧ ∀ l, l ≠ k → (spMat x) l j = 0 := by
  have hcol : ∃ k, (spMat x) k j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hmul := TorusQS.spMat_inv_mul x
    have hjj := congrFun (congrFun hmul j) j
    rw [Matrix.mul_apply, Finset.sum_eq_zero (fun l _ => by rw [h l, mul_zero]),
      Matrix.one_apply_eq] at hjj
    exact one_ne_zero hjj.symm
  obtain ⟨k, hk⟩ := hcol
  set w : Fin 2 ⊕ Fin 2 → K := (spMat x) *ᵥ Pi.single j 1 with hwdef
  have hwne : w k ≠ 0 := by
    rw [hwdef, Matrix.mulVec_single_one]
    exact hk
  have hwmem : w ∈ Submodule.span K {w} := Submodule.subset_span (Set.mem_singleton w)
  have hW : ∀ d ∈ torus 2 K, ∀ v ∈ Submodule.span K {w},
      (spMat d) *ᵥ v ∈ Submodule.span K {w} := by
    intro d hd v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨c, hc⟩ := torus_mulVec_line hx hd j
    rw [Matrix.mulVec_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
  have hk_mem : Pi.single k 1 ∈ Submodule.span K {w} :=
    TorusQS.single_mem_of_torus_invariant hK hW hwmem hwne
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hk_mem
  have hak : a * w k = 1 := by
    have := congrFun ha k
    simpa using this
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hak
    exact zero_ne_one hak
  refine ⟨k, hk, fun l hl => ?_⟩
  have hal : a * w l = 0 := by
    have := congrFun ha l
    rw [Pi.smul_apply, Pi.single_eq_of_ne hl] at this
    exact this
  have hwl : w l = 0 := (mul_eq_zero.mp hal).resolve_left ha0
  rw [hwdef, Matrix.mulVec_single_one] at hwl
  exact hwl

theorem exists_isLinePerm_of_mem_normalizer (hK : 8 ≤ Nat.card K) {x : StatedSp 2 K}
    (hx : x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) :
    ∃ σ ∈ signedPermGroup 2, IsLinePerm σ (spMat x) := by
  classical
  choose σ hσ hσzero using fun j => exists_single_entry_of_mem_normalizer hK hx j
  have hcol : ∀ j : Fin 2 ⊕ Fin 2,
      (spMat x) *ᵥ Pi.single j 1 = ((spMat x) (σ j) j) • Pi.single (σ j) 1 := by
    intro j
    ext r
    rw [Matrix.mulVec_single_one]
    by_cases hr : r = σ j
    · subst hr
      simp
    · simp [hσzero j r hr, hr]
  have hinj : Function.Injective σ := by
    intro j k hjk
    by_contra hne
    have hinv : ∀ v : Fin 2 ⊕ Fin 2 → K, (spMat x⁻¹) *ᵥ ((spMat x) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, TorusQS.spMat_inv_mul, Matrix.one_mulVec]
    set cj : K := (spMat x) (σ j) j with hcj
    set ck : K := (spMat x) (σ k) k with hck
    have hcolj : (spMat x) *ᵥ Pi.single j 1 = cj • Pi.single (σ j) 1 := by
      rw [hcol j, ← hcj]
    have hcolk : (spMat x) *ᵥ Pi.single k 1 = ck • Pi.single (σ k) 1 := by
      rw [hcol k, ← hck]
    have hj : Pi.single j 1 = cj • ((spMat x⁻¹) *ᵥ Pi.single (σ j) 1) := by
      rw [← hinv (Pi.single j 1), hcolj, Matrix.mulVec_smul]
    have hk : Pi.single k 1 = ck • ((spMat x⁻¹) *ᵥ Pi.single (σ k) 1) := by
      rw [← hinv (Pi.single k 1), hcolk, Matrix.mulVec_smul]
    rw [← hjk] at hk
    have hEq : ck • Pi.single j 1 = cj • Pi.single k 1 := by
      rw [hj, hk, smul_smul, smul_smul, mul_comm]
    have hcoord := congrFun hEq j
    simp [Pi.single_eq_of_ne hne] at hcoord
    exact hσ k (hck ▸ hcoord)
  let σe : Equiv.Perm (Fin 2 ⊕ Fin 2) := Equiv.ofBijective σ hinj.bijective_of_finite
  have hline : IsLinePerm σe (spMat x) := by
    intro a b
    change (spMat x) b a ≠ 0 ↔ b = σ a
    constructor
    · intro hb
      by_contra hne
      exact hb (hσzero a b hne)
    · rintro rfl
      exact hσ a
  exact ⟨σe, IsLinePerm.mem_signedPermGroup x.2 hline, hline⟩

theorem pow_four_mem_torus_of_mem_normalizer (hK : 8 ≤ Nat.card K) {x : StatedSp 2 K}
    (hx : x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) : x ^ 4 ∈ torus 2 K := by
  obtain ⟨σ, hσmem, hσline⟩ := exists_isLinePerm_of_mem_normalizer hK hx
  have hpow := IsLinePerm.pow hσline 4
  rw [signedPermGroup_pow_four hσmem] at hpow
  have hmat : (spMat (x ^ 4)) = (spMat x) ^ 4 := by
    rw [Subgroup.coe_pow]
    rfl
  rw [← hmat] at hpow
  exact mem_torus_of_isLinePerm_one hpow

theorem mem_torus_of_mem_normalizer_of_odd (hK : 8 ≤ Nat.card K) {x : StatedSp 2 K}
    (hx : x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) (hodd : Odd (orderOf x)) :
    x ∈ torus 2 K := by
  have hx4 : x ^ 4 ∈ torus 2 K := pow_four_mem_torus_of_mem_normalizer hK hx
  rcases eq_or_ne (orderOf x) 1 with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · have hpos : 0 < orderOf x := by
      rcases Nat.eq_zero_or_pos (orderOf x) with h0 | hpos
      · obtain ⟨k, hk⟩ := hodd
        rw [h0] at hk
        omega
      · exact hpos
    have h1' : 1 < orderOf x := by omega
    have hcop : Nat.Coprime 4 (orderOf x) := by
      have h := (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 (orderOf x)).mpr
        (Nat.coprime_two_left.mpr hodd)
      simpa using h
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1'
    have hxeq : x = (x ^ 4) ^ k := by
      rw [← pow_mul, ← pow_mod_orderOf, hk, pow_one]
    rw [hxeq]
    exact (torus 2 K).pow_mem hx4 k

noncomputable def linePermNormalizer (hK : 8 ≤ Nat.card K) :
    ↥(Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) →* signedPermGroup 2 where
  toFun x := ⟨Classical.choose (exists_isLinePerm_of_mem_normalizer hK x.2),
    (Classical.choose_spec (exists_isLinePerm_of_mem_normalizer hK x.2)).1⟩
  map_one' := by
    apply Subtype.ext
    exact IsLinePerm.unique
      (Classical.choose_spec
        (exists_isLinePerm_of_mem_normalizer hK (1 : ↥(Subgroup.normalizer
          (torus 2 K : Set (StatedSp 2 K)))).2)).2 isLinePerm_one
  map_mul' x y := by
    apply Subtype.ext
    exact IsLinePerm.unique
      (Classical.choose_spec
        (exists_isLinePerm_of_mem_normalizer hK (x * y).2)).2
      ((Classical.choose_spec (exists_isLinePerm_of_mem_normalizer hK x.2)).2.mul
        (Classical.choose_spec (exists_isLinePerm_of_mem_normalizer hK y.2)).2)

theorem linePermNormalizer_spec (hK : 8 ≤ Nat.card K)
    (x : ↥(Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)))) :
    IsLinePerm ((linePermNormalizer hK x : signedPermGroup 2) : Equiv.Perm (Fin 2 ⊕ Fin 2))
      (spMat (x : StatedSp 2 K)) :=
  (Classical.choose_spec (exists_isLinePerm_of_mem_normalizer hK x.2)).2

theorem linePermNormalizer_eq_one_iff (hK : 8 ≤ Nat.card K)
    (x : ↥(Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)))) :
    linePermNormalizer hK x = 1 ↔ (x : StatedSp 2 K) ∈ torus 2 K := by
  constructor
  · intro h
    have hspec := linePermNormalizer_spec hK x
    rw [h] at hspec
    exact mem_torus_of_isLinePerm_one hspec
  · intro h
    apply Subtype.ext
    exact IsLinePerm.unique (linePermNormalizer_spec hK x) (isLinePerm_torusHom' h)

theorem eq_bot_of_le_normalizer_torus (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hH : H ≤ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) :
    H = ⊥ := by
  let q : ↥(Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K))) →* signedPermGroup 2 :=
    linePermNormalizer hK
  let ψ : H →* signedPermGroup 2 := q.comp (Subgroup.inclusion hH)
  have hsub_top : (⊤ : Subgroup ↥H).map (Subgroup.subtype H) = H := by
    refine le_antisymm (Subgroup.map_subtype_le (H := H) ⊤) ?_
    intro x hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have htop : ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := Subgroup.subtype H) (Subgroup.subtype_injective H)
    rw [Subgroup.map_commutator, hsub_top, hHH]
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have h1 : (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆).map ψ = ψ.range := by
      rw [htop, MonoidHom.range_eq_map]
    calc ⁅ψ.range, ψ.range⁆ = ⁅(⊤ : Subgroup ↥H).map ψ, (⊤ : Subgroup ↥H).map ψ⁆ := by
          rw [MonoidHom.range_eq_map]
      _ = (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆).map ψ :=
        (Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤) (f := ψ)).symm
      _ = ψ.range := h1
  have hbot : ψ.range = ⊥ := by
    have hle : ψ.range ≤ ⊥ :=
      Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := ⊥) hperf
    simpa using hle
  have hHT : H ≤ torus 2 K := by
    intro x hx
    have hmem : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot] at hmem
    have hq : q ⟨x, hH hx⟩ = 1 := by
      have hmem' := Subgroup.mem_bot.mp hmem
      change q (Subgroup.inclusion hH ⟨x, hx⟩) = 1 at hmem'
      have hincl : (Subgroup.inclusion hH) ⟨x, hx⟩ = ⟨x, hH hx⟩ := rfl
      rwa [hincl] at hmem'
    exact (linePermNormalizer_eq_one_iff hK ⟨x, hH hx⟩).mp hq
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, rfl⟩ := hHT ha
    obtain ⟨t, rfl⟩ := hHT hb
    rw [← map_mul, ← map_mul, mul_comm]
  have hcommH : IsMulCommutative ↥H :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (hcomm (a : StatedSp 2 K) a.2 (b : StatedSp 2 K) b.2)
  have hbotcomm : ⁅H, H⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hcommH
  rw [hbotcomm] at hHH
  exact hHH.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
