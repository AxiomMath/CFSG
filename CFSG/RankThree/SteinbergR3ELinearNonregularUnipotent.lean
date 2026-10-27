module

public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.RankThree.NonregularUnipotent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.RankThree.LinearPointwise CFSG.RankThree.RegularUnipotent

variable {n : ℕ} {k : Type*} [Field k]

theorem entries_of_comm_single {A : Matrix (Fin n) (Fin n) k} {i j : Fin n}
    (h : A * single i j (1 : k) = single i j 1 * A) :
    (∀ a, a ≠ i → A a i = 0) ∧ (∀ b, b ≠ j → A j b = 0) ∧ A i i = A j j := by
  refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
  · have := congrFun (congrFun h a) j
    rwa [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ ha, mul_one] at this
  · have := congrFun (congrFun h i) b
    rwa [mul_single_apply_of_ne _ _ _ _ _ hb, single_mul_apply_same, one_mul, eq_comm] at this
  · have := congrFun (congrFun h i) j
    rwa [mul_single_apply_same, single_mul_apply_same, mul_one, one_mul] at this

theorem comm_single_of_comm_transvection {A : Matrix (Fin n) (Fin n) k} {i j : Fin n}
    (hij : i ≠ j)
    (h : A * (Matrix.SpecialLinearGroup.transvection hij (1 : k) : Matrix (Fin n) (Fin n) k) =
      (Matrix.SpecialLinearGroup.transvection hij (1 : k) : Matrix (Fin n) (Fin n) k) * A) :
    A * single i j (1 : k) = single i j 1 * A := by
  rw [Matrix.SpecialLinearGroup.transvection_coe] at h
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

structure CommutantIdeal (N : Matrix (Fin n) (Fin n) k) (I : Matrix (Fin n) (Fin n) k → Prop) :
    Prop where
  zero : I 0
  comm : ∀ x, I x → x * N = N * x
  add : ∀ x y, I x → I y → I (x + y)
  mul_left : ∀ a x, a * N = N * a → I x → I (a * x)
  mul_right : ∀ a x, a * N = N * a → I x → I (x * a)
  cube : ∀ x, I x → x * x * x = 0

variable {N : Matrix (Fin n) (Fin n) k} {I : Matrix (Fin n) (Fin n) k → Prop}

theorem CommutantIdeal.comm_one_add (hI : CommutantIdeal N I) {g : Matrix (Fin n) (Fin n) k}
    (hg : I (g - 1)) : g * N = N * g := by
  have h := hI.comm _ hg
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at h
  exact sub_left_inj.mp h

@[expose] def idealSubgroup (hI : CommutantIdeal N I) :
    Subgroup (SpecialLinearGroup (Fin n) k) where
  carrier := {g | I ((g : Matrix (Fin n) (Fin n) k) - 1)}
  one_mem' := by
    change I (((1 : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1)
    rw [Matrix.SpecialLinearGroup.coe_one, sub_self]
    exact hI.zero
  mul_mem' := by
    intro g h hg hh
    change I (((g * h : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1)
    have e : ((g * h : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1 =
        ((g : Matrix (Fin n) (Fin n) k) - 1) + ((h : Matrix (Fin n) (Fin n) k) - 1) +
          ((g : Matrix (Fin n) (Fin n) k) - 1) * ((h : Matrix (Fin n) (Fin n) k) - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      noncomm_ring
    rw [e]
    exact hI.add _ _ (hI.add _ _ hg hh) (hI.mul_left _ _ (hI.comm _ hg) hh)
  inv_mem' := by
    intro g hg
    change I (((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1)
    have hgN := hI.comm_one_add hg
    have hgi : ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * g = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgi' : (g : Matrix (Fin n) (Fin n) k) * (g⁻¹ : SpecialLinearGroup (Fin n) k) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinvN : ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * N =
        N * (g⁻¹ : SpecialLinearGroup (Fin n) k) := by
      calc ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * N
          = (g⁻¹ : SpecialLinearGroup (Fin n) k) * N * ((g : Matrix (Fin n) (Fin n) k) *
              (g⁻¹ : SpecialLinearGroup (Fin n) k)) := by rw [hgi', Matrix.mul_one]
        _ = (g⁻¹ : SpecialLinearGroup (Fin n) k) * (N * g) *
              (g⁻¹ : SpecialLinearGroup (Fin n) k) := by simp only [Matrix.mul_assoc]
        _ = (g⁻¹ : SpecialLinearGroup (Fin n) k) * (g * N) *
              (g⁻¹ : SpecialLinearGroup (Fin n) k) := by rw [hgN]
        _ = N * (g⁻¹ : SpecialLinearGroup (Fin n) k) := by
              rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    have e : ((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1 =
        (-((g⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) *
          ((g : Matrix (Fin n) (Fin n) k) - 1) := by
      rw [Matrix.neg_mul, Matrix.mul_sub, hgi, Matrix.mul_one]
      abel
    rw [e]
    exact hI.mul_left _ _ (by rw [Matrix.neg_mul, Matrix.mul_neg, hinvN]) hg

theorem mem_idealSubgroup (hI : CommutantIdeal N I) {g : SpecialLinearGroup (Fin n) k} :
    g ∈ idealSubgroup hI ↔ I ((g : Matrix (Fin n) (Fin n) k) - 1) :=
  Iff.rfl

theorem idealSubgroup_comm (hI : CommutantIdeal N I) {g : SpecialLinearGroup (Fin n) k}
    (hg : g ∈ idealSubgroup hI) : (g : Matrix (Fin n) (Fin n) k) * N = N * g :=
  hI.comm_one_add hg

theorem idealSubgroup_conj_mem (hI : CommutantIdeal N I) {h g : SpecialLinearGroup (Fin n) k}
    (hh : (h : Matrix (Fin n) (Fin n) k) * N = N * h) (hg : g ∈ idealSubgroup hI) :
    h * g * h⁻¹ ∈ idealSubgroup hI := by
  have hhi : (h : Matrix (Fin n) (Fin n) k) * (h⁻¹ : SpecialLinearGroup (Fin n) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hih : ((h⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * h = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvN : ((h⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * N =
      N * (h⁻¹ : SpecialLinearGroup (Fin n) k) := by
    calc ((h⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) * N
        = (h⁻¹ : SpecialLinearGroup (Fin n) k) * N * ((h : Matrix (Fin n) (Fin n) k) *
            (h⁻¹ : SpecialLinearGroup (Fin n) k)) := by rw [hhi, Matrix.mul_one]
      _ = (h⁻¹ : SpecialLinearGroup (Fin n) k) * (N * h) *
            (h⁻¹ : SpecialLinearGroup (Fin n) k) := by simp only [Matrix.mul_assoc]
      _ = (h⁻¹ : SpecialLinearGroup (Fin n) k) * (h * N) *
            (h⁻¹ : SpecialLinearGroup (Fin n) k) := by rw [hh]
      _ = N * (h⁻¹ : SpecialLinearGroup (Fin n) k) := by
            rw [← Matrix.mul_assoc, hih, Matrix.one_mul]
  rw [mem_idealSubgroup]
  have e : ((h * g * h⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) - 1 =
      (h : Matrix (Fin n) (Fin n) k) * ((g : Matrix (Fin n) (Fin n) k) - 1) *
        (h⁻¹ : SpecialLinearGroup (Fin n) k) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hhi]
  rw [e]
  exact hI.mul_right _ _ hinvN (hI.mul_left _ _ hh hg)

theorem pow_char_eq_zero_of_cube {p : ℕ} (hp3 : 3 ≤ p) {x : Matrix (Fin n) (Fin n) k}
    (hx : x * x * x = 0) : x ^ p = 0 := by
  have h3 : x ^ 3 = 0 := by rw [pow_three, ← Matrix.mul_assoc, hx]
  exact pow_eq_zero_of_le hp3 h3

theorem idealSubgroup_pow_char {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n] (hp3 : 3 ≤ p)
    (hI : CommutantIdeal N I) {g : SpecialLinearGroup (Fin n) k} (hg : g ∈ idealSubgroup hI) :
    g ^ p = 1 := by
  apply Subtype.ext
  have hx := pow_char_eq_zero_of_cube hp3 (hI.cube _ hg)
  have hg' : (g : Matrix (Fin n) (Fin n) k) = 1 + ((g : Matrix (Fin n) (Fin n) k) - 1) := by
    abel
  rw [Matrix.SpecialLinearGroup.coe_pow, hg',
    add_pow_char_of_commute p (Commute.one_left _), one_pow, hx, add_zero,
    Matrix.SpecialLinearGroup.coe_one]

theorem exists_pow_char_eq_scalar {p : ℕ} [Fact p.Prime] [CharP k p] [NeZero n] (hp3 : 3 ≤ p)
    (A : GL (Fin n) k) {c : k} {X : Matrix (Fin n) (Fin n) k} (hX : X * X * X = 0)
    (hA : (A : Matrix (Fin n) (Fin n) k) = c • 1 + X) :
    ∃ u : kˣ, A ^ p = GeneralLinearGroup.scalar (Fin n) u := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hA
    have h3 : (A : Matrix (Fin n) (Fin n) k) * A * A = 0 := by rw [hA, hX]
    have hdet := congrArg Matrix.det h3
    have : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at hdet
    have hu : (A : Matrix (Fin n) (Fin n) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit |>.ne_zero
    exact hu (by simpa [mul_self_eq_zero] using hdet)
  refine ⟨Units.mk0 (c ^ p) (pow_ne_zero _ hc), Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hA, add_pow_char_of_commute p
    (Commute.smul_left (Commute.one_left X) c), pow_char_eq_zero_of_cube hp3 hX, add_zero,
    smul_pow, one_pow, GeneralLinearGroup.coe_scalar, Units.val_mk0]
  ext a b
  rw [Matrix.smul_apply, scalar_apply, diagonal_apply, one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem normal_prime_complements_trivial_of_commutantIdeal {p f : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hf : 1 ≤ f) (hn3 : 3 ≤ n) [Finite k] [CharP k p] (hk : Nat.card k = p ^ f)
    (hI : CommutantIdeal N I) (hNI : I N) (u₀ : SpecialLinearGroup (Fin n) k)
    (hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = 1 + N) {i j r : Fin n} (hij : i ≠ j) (hir : i ≠ r)
    (hjr : j ≠ r) (hroot : ∀ c : k, I (single i j c) ∧ I (single i r c))
    (hcent : ∀ A : Matrix (Fin n) (Fin n) k,
      (∀ g ∈ idealSubgroup hI, A * (g : Matrix (Fin n) (Fin n) k) = g * A) →
        ∃ c : k, I (A - c • 1))
    (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    (S : Subgroup (MulAut (projectiveSL n k)))
    (hSC : S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj n k u₀)})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k u₀)})).Normal)
    (hSp : ¬ p ∣ Nat.card S) : S = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := NeZero.pos n
  set U₀ := idealSubgroup hI with hU₀
  have hu₀U : u₀ ∈ U₀ := by
    rw [hU₀, mem_idealSubgroup, hu₀, add_sub_cancel_left]
    exact hNI
  have hpow : ∀ g ∈ U₀, g ^ p = 1 := fun g hg => idealSubgroup_pow_char hp3 hI hg
  have hU₀p : IsPGroup p U₀ := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hpow g g.2)⟩
  set C := Subgroup.centralizer ({proj n k u₀} : Set (projectiveSL n k)) with hC
  set L := B ⊓ Subgroup.centralizer {MulAut.conj (proj n k u₀)} with hL
  have hinj := conj_injective_projectiveSL (k := k) hn3
  have hlift : ∀ x ∈ C, ∃ h : SpecialLinearGroup (Fin n) k, proj n k h = x ∧
      (h : Matrix (Fin n) (Fin n) k) * N = N * h := by
    intro x hx
    obtain ⟨h, rfl⟩ := proj_surjective n k x
    refine ⟨h, rfl, ?_⟩
    have hx' : proj n k h * proj n k u₀ = proj n k u₀ * proj n k h :=
      Subgroup.mem_centralizer_singleton_iff.1 hx
    have hconj : proj n k ((MulAut.conj h).toMonoidHom u₀) = proj n k u₀ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, hx', map_inv,
        mul_inv_cancel_right]
    have hu1 : u₀ ^ p ^ 1 = 1 := by
      rw [pow_one]
      exact hpow u₀ hu₀U
    have h1 := eq_of_proj_eq_of_pow_eq_one hn0 _ hu1 hconj
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : h * u₀ = u₀ * h := by
      calc h * u₀ = h * u₀ * h⁻¹ * h := by group
        _ = u₀ * h := by rw [h1]
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
      h2
    simp only [Matrix.SpecialLinearGroup.coe_mul, hu₀, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at h3
    exact add_left_cancel h3
  have hW0C : U₀.map (proj n k) ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hu₀,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, idealSubgroup_comm hI hg]
  have hW0n : ((U₀.map (proj n k)).subgroupOf C).Normal := by
    constructor
    intro w hw x
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨g, hg, hgw⟩ := hw
    obtain ⟨h, hhx, hhN⟩ := hlift x x.2
    refine ⟨h * g * h⁻¹, idealSubgroup_conj_mem hI hhN hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hhx, hgw]
    rfl
  have hW0p : IsPGroup p ((U₀.map (proj n k)).subgroupOf C) :=
    (hU₀p.map (proj n k)).of_equiv (Subgroup.subgroupOfEquivOfLe hW0C).symm
  have hW0P : (U₀.map (proj n k)).subgroupOf C ≤ CFSG.pCore p C := by
    change _ ≤ sSup _
    exact le_sSup ⟨hW0n, hW0p⟩
  set P0 := (CFSG.pCore p C).map C.subtype with hP0
  have hP0p : IsPGroup p P0 := CFSG.pCore_isPGroup.map _
  have hW0P0 : U₀.map (proj n k) ≤ P0 := fun w hw =>
    ⟨⟨w, hW0C hw⟩, hW0P (Subgroup.mem_subgroupOf.2 hw), rfl⟩
  have hP0C : P0 ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hfixu : ∀ s ∈ L, s (proj n k u₀) = proj n k u₀ := by
    intro s hs
    apply hinj
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    rw [conj_apply_mulAut, h1, mul_inv_cancel_right]
  have hyC : ∀ y : MulAut (projectiveSL n k), y (proj n k u₀) = proj n k u₀ →
      ∀ z ∈ C, y z ∈ C := by
    intro y hy z hz
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    rw [← hy, ← map_mul, hz, map_mul]
  have hyP0 : ∀ y ∈ L, ∀ x ∈ P0, y x ∈ P0 := by
    intro y hy x hx
    have hyu := hfixu y hy
    have hyu' : y⁻¹ (proj n k u₀) = proj n k u₀ := by
      conv_lhs => rw [← hyu]
      exact MulAut.inv_apply_self _ y _
    let e : C ≃* C :=
      { toFun := fun z => ⟨y (z : projectiveSL n k), hyC y hyu z z.2⟩
        invFun := fun z => ⟨y⁻¹ (z : projectiveSL n k), hyC y⁻¹ hyu' z z.2⟩
        left_inv := fun z => Subtype.ext (MulAut.inv_apply_self _ y (z : projectiveSL n k))
        right_inv := fun z => Subtype.ext (MulAut.apply_inv_self _ y (z : projectiveSL n k))
        map_mul' := fun z w => Subtype.ext
          (map_mul y (z : projectiveSL n k) (w : projectiveSL n k)) }
    obtain ⟨c, hc, rfl⟩ := hx
    have hec : e c ∈ CFSG.pCore p C := by
      rw [← CFSG.pCore_map_iso p e]
      exact ⟨c, hc, rfl⟩
    exact ⟨e c, hec, rfl⟩
  set W := P0.map (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)) with hW
  have hWp : IsPGroup p W := hP0p.map _
  have hWL : W ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hB ⟨x, rfl⟩, ?_⟩
    have hxC := hP0C hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hxC
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxC]
  have hWnorm : ∀ y ∈ L, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    rintro y hy _ ⟨x, hx, rfl⟩
    exact ⟨y x, hyP0 y hy x hx, by rw [conj_apply_mulAut]⟩
  have hSnorm : ∀ y ∈ L, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hdisj : Disjoint S W := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hWp
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.Prime.coprime_iff_not_dvd hp).2 hSp).symm
  have hcomm : ∀ s ∈ S, ∀ w ∈ W, s * w = w * s := by
    intro s hs w hw
    have hsL := hSC hs
    have h1 : s * w * s⁻¹ * w⁻¹ ∈ W := W.mul_mem (hWnorm s hsL w hw) (W.inv_mem hw)
    have h2 : s * w * s⁻¹ * w⁻¹ ∈ S := by
      have := S.mul_mem hs (hSnorm w (hWL hw) s⁻¹ (S.inv_mem hs))
      rwa [← mul_assoc, ← mul_assoc] at this
    have h3 := Subgroup.disjoint_def.1 hdisj h2 h1
    calc s * w = s * w * s⁻¹ * w⁻¹ * (w * s) := by group
      _ = w * s := by rw [h3, one_mul]
  have hfix : ∀ s ∈ S, ∀ g ∈ U₀, s (proj n k g) = proj n k g := by
    intro s hs g hg
    apply hinj
    rw [conj_apply_mulAut, hcomm s hs _ ⟨_, hW0P0 ⟨g, hg, rfl⟩, rfl⟩, mul_inv_cancel_right]
  have hroot' : ∀ c : k, Matrix.SpecialLinearGroup.transvection hij c ∈ U₀ ∧
      Matrix.SpecialLinearGroup.transvection hir c ∈ U₀ := fun c => by
    refine ⟨?_, ?_⟩
    · rw [hU₀, mem_idealSubgroup, Matrix.SpecialLinearGroup.transvection_coe, add_sub_cancel_left]
      exact (hroot c).1
    · rw [hU₀, mem_idealSubgroup, Matrix.SpecialLinearGroup.transvection_coe, add_sub_cancel_left]
      exact (hroot c).2
  have hS1 : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    have hmem : s ∈ {α : MulAut (projectiveSL n k) | ∀ h ∈ U₀, α (proj n k h) = proj n k h} :=
      hfix s hs
    rw [linear_common_row_root_pointwise_automorphisms_are_linear hp hf hn3 hk U₀ hU₀p hij hir
      hjr hroot'] at hmem
    obtain ⟨A, hA, rfl⟩ := hmem
    obtain ⟨c, hc⟩ := hcent A hA
    have hAX : (A : Matrix (Fin n) (Fin n) k) =
        c • 1 + ((A : Matrix (Fin n) (Fin n) k) - c • 1) := by abel
    obtain ⟨v, hv⟩ := exists_pow_char_eq_scalar hp3 A (hI.cube _ hc) hAX
    rw [← map_pow, hv, conjAut_scalar]
  have hSp' : IsPGroup p S := fun s => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hS1 s s.2)⟩
  rcases hSp'.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.1 h
  · exact absurd h hSp

theorem transvection_mem_idealSubgroup (hI : CommutantIdeal N I) {i j : Fin n} (hij : i ≠ j)
    {c : k} (h : I (single i j c)) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ idealSubgroup hI := by
  rw [mem_idealSubgroup, Matrix.SpecialLinearGroup.transvection_coe, add_sub_cancel_left]
  exact h

theorem comm_single_of_comm_idealSubgroup (hI : CommutantIdeal N I)
    {A : Matrix (Fin n) (Fin n) k}
    (hA : ∀ g ∈ idealSubgroup hI, A * (g : Matrix (Fin n) (Fin n) k) = g * A) {i j : Fin n}
    (hij : i ≠ j) (h : I (single i j 1)) : A * single i j (1 : k) = single i j 1 * A :=
  comm_single_of_comm_transvection hij (hA _ (transvection_mem_idealSubgroup hI hij h))

theorem comm_of_comm_idealSubgroup (hI : CommutantIdeal N I) (hNI : I N)
    (u₀ : SpecialLinearGroup (Fin n) k) (hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = 1 + N)
    {A : Matrix (Fin n) (Fin n) k}
    (hA : ∀ g ∈ idealSubgroup hI, A * (g : Matrix (Fin n) (Fin n) k) = g * A) :
    A * N = N * A := by
  have h := hA u₀ (by rw [mem_idealSubgroup, hu₀, add_sub_cancel_left]; exact hNI)
  rw [hu₀, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem sub_smul_comm {A : Matrix (Fin n) (Fin n) k} (hA : A * N = N * A) (c : k) :
    (A - c • 1) * N = N * (A - c • 1) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hA]

@[expose] def idealA (k : Type*) [Field k] (x : Matrix (Fin 3) (Fin 3) k) : Prop :=
  x * single 0 2 1 = single 0 2 1 * x ∧ x 0 0 = 0 ∧ x 1 1 = 0

theorem comm_A {a : Matrix (Fin 3) (Fin 3) k} (h : a * single 0 2 1 = single 0 2 1 * a) :
    a 1 0 = 0 ∧ a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 0 0 = a 2 2 := by
  obtain ⟨h1, h2, h3⟩ := entries_of_comm_single h
  exact ⟨h1 1 (by decide), h1 2 (by decide), h2 1 (by decide), h3⟩

theorem commutantIdeal_A : CommutantIdeal (single (0 : Fin 3) 2 (1 : k)) (idealA k) where
  zero := ⟨by simp, by simp, by simp⟩
  comm := fun _ hx => hx.1
  add := fun x y hx hy => ⟨by rw [Matrix.add_mul, hx.1, hy.1, ← Matrix.mul_add],
    by rw [Matrix.add_apply, hx.2.1, hy.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2, hy.2.2, add_zero]⟩
  mul_left := fun a x ha hx => by
    obtain ⟨a10, -, -, -⟩ := comm_A ha
    obtain ⟨x10, x20, x21, -⟩ := comm_A hx.1
    refine ⟨by rw [Matrix.mul_assoc, hx.1, ← Matrix.mul_assoc, ha, Matrix.mul_assoc], ?_, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_three, hx.2.1, x10, x20]
    · simp [Matrix.mul_apply, Fin.sum_univ_three, hx.2.2, a10, x21]
  mul_right := fun a x ha hx => by
    obtain ⟨a10, a20, a21, -⟩ := comm_A ha
    obtain ⟨x10, -, -, -⟩ := comm_A hx.1
    refine ⟨by rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, hx.1, Matrix.mul_assoc], ?_, ?_⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_three, hx.2.1, a10, a20]
    · simp [Matrix.mul_apply, Fin.sum_univ_three, hx.2.2, x10, a21]
  cube := fun x hx => by
    obtain ⟨x10, x20, x21, x22⟩ := comm_A hx.1
    have x00 := hx.2.1
    have x11 := hx.2.2
    have x22' : x 2 2 = 0 := by rw [← x22, x00]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, x00, x11, x22', x10, x20, x21]

theorem idealA_single (c : k) {i j : Fin 3} (hij : (i, j) = (0, 1) ∨ (i, j) = (0, 2) ∨
    (i, j) = (1, 2)) : idealA k (single i j c) := by
  rcases hij with h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h <;>
    refine ⟨?_, by simp, by simp⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.single_apply]

theorem strictUpper_A :
    ∀ a b : Fin 3, b.val ≤ a.val → (single 0 2 1 : Matrix (Fin 3) (Fin 3) k) a b = 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢

@[expose] def idealB (k : Type*) [Field k] (x : Matrix (Fin 4) (Fin 4) k) : Prop :=
  x * single 0 3 1 = single 0 3 1 * x ∧ x 0 0 = 0 ∧ x 1 1 = 0 ∧ x 1 2 = 0 ∧ x 2 1 = 0 ∧
    x 2 2 = 0

theorem comm_B {a : Matrix (Fin 4) (Fin 4) k} (h : a * single 0 3 1 = single 0 3 1 * a) :
    a 1 0 = 0 ∧ a 2 0 = 0 ∧ a 3 0 = 0 ∧ a 3 1 = 0 ∧ a 3 2 = 0 ∧ a 0 0 = a 3 3 := by
  obtain ⟨h1, h2, h3⟩ := entries_of_comm_single h
  exact ⟨h1 1 (by decide), h1 2 (by decide), h1 3 (by decide), h2 1 (by decide),
    h2 2 (by decide), h3⟩

theorem commutantIdeal_B : CommutantIdeal (single (0 : Fin 4) 3 (1 : k)) (idealB k) where
  zero := ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  comm := fun _ hx => hx.1
  add := fun x y hx hy => ⟨by rw [Matrix.add_mul, hx.1, hy.1, ← Matrix.mul_add],
    by rw [Matrix.add_apply, hx.2.1, hy.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.1, hy.2.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.2.1, hy.2.2.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.2.2.1, hy.2.2.2.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.2.2.2, hy.2.2.2.2.2, add_zero]⟩
  mul_left := fun a x ha hx => by
    obtain ⟨a10, a20, -, -, -, -⟩ := comm_B ha
    obtain ⟨x10, x20, x30, x31, x32, -⟩ := comm_B hx.1
    obtain ⟨hxN, x00, x11, x12, x21, x22⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, hxN, ← Matrix.mul_assoc, ha, Matrix.mul_assoc],
      ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x11, x12, x21, x22, x10, x20, x30, x31, x32,
        a10, a20]
  mul_right := fun a x ha hx => by
    obtain ⟨a10, a20, a30, a31, a32, -⟩ := comm_B ha
    obtain ⟨x10, x20, -, -, -, -⟩ := comm_B hx.1
    obtain ⟨hxN, x00, x11, x12, x21, x22⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, hxN, Matrix.mul_assoc],
      ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x11, x12, x21, x22, x10, x20, a10, a20, a30,
        a31, a32]
  cube := fun x hx => by
    obtain ⟨x10, x20, x30, x31, x32, x33⟩ := comm_B hx.1
    obtain ⟨-, x00, x11, x12, x21, x22⟩ := hx
    have x33' : x 3 3 = 0 := by rw [← x33, x00]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x11, x12, x21, x22, x33', x10, x20, x30,
        x31, x32]

theorem idealB_single (c : k) {i j : Fin 4} (hij : (i, j) = (0, 1) ∨ (i, j) = (0, 2) ∨
    (i, j) = (0, 3)) : idealB k (single i j c) := by
  rcases hij with h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h <;>
    refine ⟨?_, by simp, by simp, by simp, by simp, by simp⟩ <;> ext a b <;> fin_cases a <;>
      fin_cases b <;> simp [Matrix.mul_apply, Matrix.single_apply]

theorem strictUpper_B :
    ∀ a b : Fin 4, b.val ≤ a.val → (single 0 3 1 : Matrix (Fin 4) (Fin 4) k) a b = 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢

theorem idealA_N : idealA k (single 0 2 1) := ⟨rfl, by simp, by simp⟩

theorem hcent_A : ∀ A : Matrix (Fin 3) (Fin 3) k,
    (∀ g ∈ idealSubgroup (commutantIdeal_A (k := k)), A * (g : Matrix (Fin 3) (Fin 3) k) = g * A) →
      ∃ c : k, idealA k (A - c • 1) := by
  intro A hA
  have c01 := comm_single_of_comm_idealSubgroup commutantIdeal_A hA (by decide : (0 : Fin 3) ≠ 1)
    (idealA_single 1 (Or.inl rfl))
  have c02 := comm_single_of_comm_idealSubgroup commutantIdeal_A hA (by decide : (0 : Fin 3) ≠ 2)
    (idealA_single 1 (Or.inr (Or.inl rfl)))
  have h11 := (entries_of_comm_single c01).2.2
  exact ⟨A 0 0, sub_smul_comm c02 _, by simp, by simp [h11]⟩

theorem idealB_N : idealB k (single 0 3 1) := ⟨rfl, by simp, by simp, by simp, by simp, by simp⟩

theorem hcent_B : ∀ A : Matrix (Fin 4) (Fin 4) k,
    (∀ g ∈ idealSubgroup (commutantIdeal_B (k := k)), A * (g : Matrix (Fin 4) (Fin 4) k) = g * A) →
      ∃ c : k, idealB k (A - c • 1) := by
  intro A hA
  have c01 := comm_single_of_comm_idealSubgroup commutantIdeal_B hA (by decide : (0 : Fin 4) ≠ 1)
    (idealB_single 1 (Or.inl rfl))
  have c02 := comm_single_of_comm_idealSubgroup commutantIdeal_B hA (by decide : (0 : Fin 4) ≠ 2)
    (idealB_single 1 (Or.inr (Or.inl rfl)))
  have c03 := comm_single_of_comm_idealSubgroup commutantIdeal_B hA (by decide : (0 : Fin 4) ≠ 3)
    (idealB_single 1 (Or.inr (Or.inr rfl)))
  obtain ⟨-, r1, h11⟩ := entries_of_comm_single c01
  obtain ⟨-, r2, h22⟩ := entries_of_comm_single c02
  have h12 : A 1 2 = 0 := r1 2 (by decide)
  have h21 : A 2 1 = 0 := r2 1 (by decide)
  exact ⟨A 0 0, sub_smul_comm c03 _, by simp, by simp [h11], by simp [h12], by simp [h21],
    by simp [h22]⟩

@[expose] def idealC (k : Type*) [Field k] (x : Matrix (Fin 4) (Fin 4) k) : Prop :=
  x * (single 0 2 1 + single 1 3 1) = (single 0 2 1 + single 1 3 1) * x ∧ x 0 0 = 0 ∧
    x 0 1 = 0 ∧ x 1 0 = 0 ∧ x 1 1 = 0

theorem comm_C {a : Matrix (Fin 4) (Fin 4) k}
    (h : a * (single 0 2 1 + single 1 3 1) = (single 0 2 1 + single 1 3 1) * a) :
    a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 3 0 = 0 ∧ a 3 1 = 0 := by
  have e := fun x y => congrFun (congrFun h x) y
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [Matrix.mul_apply, Matrix.single_apply] at e22 e23 e32 e33
  exact ⟨e22, e23, e32, e33⟩

theorem comm_C_diag {a : Matrix (Fin 4) (Fin 4) k}
    (h : a * (single 0 2 1 + single 1 3 1) = (single 0 2 1 + single 1 3 1) * a) :
    a 0 0 = a 2 2 ∧ a 0 1 = a 2 3 ∧ a 1 0 = a 3 2 ∧ a 1 1 = a 3 3 := by
  have e := fun x y => congrFun (congrFun h x) y
  have e02 := e 0 2
  have e03 := e 0 3
  have e12 := e 1 2
  have e13 := e 1 3
  simp [Matrix.mul_apply, Matrix.single_apply] at e02 e03 e12 e13
  exact ⟨e02, e03, e12, e13⟩

theorem commutantIdeal_C :
    CommutantIdeal (single (0 : Fin 4) 2 (1 : k) + single 1 3 1) (idealC k) where
  zero := ⟨by simp, by simp, by simp, by simp, by simp⟩
  comm := fun _ hx => hx.1
  add := fun x y hx hy => ⟨by rw [Matrix.add_mul, hx.1, hy.1, ← Matrix.mul_add],
    by rw [Matrix.add_apply, hx.2.1, hy.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.1, hy.2.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.2.1, hy.2.2.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2.2.2, hy.2.2.2.2, add_zero]⟩
  mul_left := fun a x ha hx => by
    obtain ⟨x20, x21, x30, x31⟩ := comm_C hx.1
    obtain ⟨hxN, x00, x01, x10, x11⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, hxN, ← Matrix.mul_assoc, ha, Matrix.mul_assoc],
      ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x01, x10, x11, x20, x21, x30, x31]
  mul_right := fun a x ha hx => by
    obtain ⟨a20, a21, a30, a31⟩ := comm_C ha
    obtain ⟨hxN, x00, x01, x10, x11⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, hxN, Matrix.mul_assoc],
      ?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x01, x10, x11, a20, a21, a30, a31]
  cube := fun x hx => by
    obtain ⟨x20, x21, x30, x31⟩ := comm_C hx.1
    obtain ⟨d00, d01, d10, d11⟩ := comm_C_diag hx.1
    obtain ⟨-, x00, x01, x10, x11⟩ := hx
    have x22 : x 2 2 = 0 := by rw [← d00, x00]
    have x23 : x 2 3 = 0 := by rw [← d01, x01]
    have x32 : x 3 2 = 0 := by rw [← d10, x10]
    have x33 : x 3 3 = 0 := by rw [← d11, x11]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x01, x10, x11, x20, x21, x30, x31, x22,
        x23, x32, x33]

theorem idealC_single (c : k) {i j : Fin 4} (hij : (i, j) = (0, 2) ∨ (i, j) = (0, 3) ∨
    (i, j) = (1, 2) ∨ (i, j) = (1, 3)) : idealC k (single i j c) := by
  rcases hij with h | h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h <;>
    refine ⟨?_, by simp, by simp, by simp, by simp⟩ <;> ext a b <;> fin_cases a <;>
      fin_cases b <;> simp [Matrix.mul_apply, Matrix.single_apply]

theorem idealC_N : idealC k (single 0 2 1 + single 1 3 1) :=
  ⟨rfl, by simp, by simp, by simp, by simp⟩

theorem hcent_C : ∀ A : Matrix (Fin 4) (Fin 4) k,
    (∀ g ∈ idealSubgroup (commutantIdeal_C (k := k)), A * (g : Matrix (Fin 4) (Fin 4) k) = g * A) →
      ∃ c : k, idealC k (A - c • 1) := by
  intro A hA
  have c02 := comm_single_of_comm_idealSubgroup commutantIdeal_C hA (by decide : (0 : Fin 4) ≠ 2)
    (idealC_single 1 (Or.inl rfl))
  have c12 := comm_single_of_comm_idealSubgroup commutantIdeal_C hA (by decide : (1 : Fin 4) ≠ 2)
    (idealC_single 1 (Or.inr (Or.inr (Or.inl rfl))))
  have c13 := comm_single_of_comm_idealSubgroup commutantIdeal_C hA (by decide : (1 : Fin 4) ≠ 3)
    (idealC_single 1 (Or.inr (Or.inr (Or.inr rfl))))
  have hAN : A * (single 0 2 1 + single 1 3 1) = (single 0 2 1 + single 1 3 1) * A := by
    rw [Matrix.mul_add, Matrix.add_mul, c02, c13]
  obtain ⟨col0, -, h00⟩ := entries_of_comm_single c02
  obtain ⟨col1, -, h11⟩ := entries_of_comm_single c12
  have h10 : A 1 0 = 0 := col0 1 (by decide)
  have h01 : A 0 1 = 0 := col1 0 (by decide)
  exact ⟨A 0 0, sub_smul_comm hAN _, by simp, by simp [h01], by simp [h10], by simp [h11, h00]⟩

@[expose] def idealD (k : Type*) [Field k] (x : Matrix (Fin 4) (Fin 4) k) : Prop :=
  x * (single 0 1 1 + single 1 2 1) = (single 0 1 1 + single 1 2 1) * x ∧ x 0 0 = 0 ∧
    x 3 3 = 0

theorem comm_D {a : Matrix (Fin 4) (Fin 4) k}
    (h : a * (single 0 1 1 + single 1 2 1) = (single 0 1 1 + single 1 2 1) * a) :
    a 1 0 = 0 ∧ a 2 0 = 0 ∧ a 3 0 = 0 ∧ a 2 1 = 0 ∧ a 3 1 = 0 ∧ a 1 3 = 0 ∧ a 2 3 = 0 ∧
      a 0 0 = a 1 1 ∧ a 1 1 = a 2 2 := by
  have e := fun x y => congrFun (congrFun h x) y
  have e00 := e 0 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e22 := e 2 2
  have e32 := e 3 2
  have e03 := e 0 3
  have e13 := e 1 3
  have e01 := e 0 1
  have e12 := e 1 2
  simp [Matrix.mul_apply, Matrix.single_apply] at e00 e10 e31 e22 e32
  simp [Matrix.mul_apply, Matrix.single_apply] at e03 e13 e01 e12
  exact ⟨e00.symm, e10.symm, e31, e22, e32, e03.symm, e13.symm, e01, e12⟩

theorem commutantIdeal_D :
    CommutantIdeal (single (0 : Fin 4) 1 (1 : k) + single 1 2 1) (idealD k) where
  zero := ⟨by simp, by simp, by simp⟩
  comm := fun _ hx => hx.1
  add := fun x y hx hy => ⟨by rw [Matrix.add_mul, hx.1, hy.1, ← Matrix.mul_add],
    by rw [Matrix.add_apply, hx.2.1, hy.2.1, add_zero],
    by rw [Matrix.add_apply, hx.2.2, hy.2.2, add_zero]⟩
  mul_left := fun a x ha hx => by
    obtain ⟨-, -, a30, -, a31, -, -, -, -⟩ := comm_D ha
    obtain ⟨x10, x20, x30, -, -, x13, x23, -, -⟩ := comm_D hx.1
    obtain ⟨hxN, x00, x33⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, hxN, ← Matrix.mul_assoc, ha, Matrix.mul_assoc], ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x33, x10, x20, x30, x13, x23, a30, a31]
  mul_right := fun a x ha hx => by
    obtain ⟨a10, a20, a30, -, -, a13, a23, -, -⟩ := comm_D ha
    obtain ⟨-, -, x30, -, x31, -, -, -, -⟩ := comm_D hx.1
    obtain ⟨hxN, x00, x33⟩ := hx
    refine ⟨by rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, hxN, Matrix.mul_assoc], ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x33, x30, x31, a10, a20, a30, a13, a23]
  cube := fun x hx => by
    obtain ⟨x10, x20, x30, x21, x31, x13, x23, d01, d12⟩ := comm_D hx.1
    obtain ⟨-, x00, x33⟩ := hx
    have x11 : x 1 1 = 0 := by rw [← d01, x00]
    have x22 : x 2 2 = 0 := by rw [← d12, x11]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, x00, x11, x22, x33, x10, x20, x30, x21, x31,
        x13, x23]

theorem idealD_single (c : k) {i j : Fin 4} (hij : (i, j) = (0, 2) ∨ (i, j) = (0, 3) ∨
    (i, j) = (3, 2)) : idealD k (single i j c) := by
  rcases hij with h | h | h <;> obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h <;>
    refine ⟨?_, by simp, by simp⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.single_apply]

theorem idealD_N : idealD k (single 0 1 1 + single 1 2 1) := ⟨rfl, by simp, by simp⟩

theorem strictUpper_C : ∀ a b : Fin 4, b.val ≤ a.val →
    (single 0 2 1 + single 1 3 1 : Matrix (Fin 4) (Fin 4) k) a b = 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢

theorem strictUpper_D : ∀ a b : Fin 4, b.val ≤ a.val →
    (single 0 1 1 + single 1 2 1 : Matrix (Fin 4) (Fin 4) k) a b = 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢

@[expose] def uA (k : Type*) [Field k] : SpecialLinearGroup (Fin 3) k :=
  oneAdd (single 0 2 1) strictUpper_A

@[expose] def uB (k : Type*) [Field k] : SpecialLinearGroup (Fin 4) k :=
  oneAdd (single 0 3 1) strictUpper_B

@[expose] def uC (k : Type*) [Field k] : SpecialLinearGroup (Fin 4) k :=
  oneAdd (single 0 2 1 + single 1 3 1) strictUpper_C

@[expose] def uD (k : Type*) [Field k] : SpecialLinearGroup (Fin 4) k :=
  oneAdd (single 0 1 1 + single 1 2 1) strictUpper_D

theorem hcent_D : ∀ A : Matrix (Fin 4) (Fin 4) k,
    (∀ g ∈ idealSubgroup (commutantIdeal_D (k := k)), A * (g : Matrix (Fin 4) (Fin 4) k) = g * A) →
      ∃ c : k, idealD k (A - c • 1) := by
  intro A hA
  have c03 := comm_single_of_comm_idealSubgroup commutantIdeal_D hA (by decide : (0 : Fin 4) ≠ 3)
    (idealD_single 1 (Or.inr (Or.inl rfl)))
  have hAN := comm_of_comm_idealSubgroup commutantIdeal_D idealD_N (uD k) (coe_oneAdd _ _) hA
  have h33 := (entries_of_comm_single c03).2.2
  exact ⟨A 0 0, sub_smul_comm hAN _, by simp, by simp [h33]⟩

@[expose] def NormalPrimeComplementsTrivial (p : ℕ) {n : ℕ} {k : Type*} [Field k]
    (u : SpecialLinearGroup (Fin n) k) : Prop :=
  ∀ B S : Subgroup (MulAut (projectiveSL n k)),
    (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B →
    S ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj n k u)} →
    (S.subgroupOf (B ⊓ Subgroup.centralizer {MulAut.conj (proj n k u)})).Normal →
    ¬ p ∣ Nat.card S → S = ⊥

theorem linear_three_four_nonregular_unipotent_centralizer_normal_prime_complements_trivial
    {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) [Finite k] [CharP k p]
    (hk : Nat.card k = p ^ f) :
    NormalPrimeComplementsTrivial p (uA k) ∧ NormalPrimeComplementsTrivial p (uB k) ∧
      NormalPrimeComplementsTrivial p (uC k) ∧ NormalPrimeComplementsTrivial p (uD k) := by
  refine ⟨fun B S hB hSC hSn hSp => ?_, fun B S hB hSC hSn hSp => ?_,
    fun B S hB hSC hSn hSp => ?_, fun B S hB hSC hSn hSp => ?_⟩
  · exact normal_prime_complements_trivial_of_commutantIdeal hp (by omega) hf le_rfl hk
      commutantIdeal_A idealA_N (uA k) (coe_oneAdd _ _) (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2)
      (fun c => ⟨idealA_single c (Or.inl rfl), idealA_single c (Or.inr (Or.inl rfl))⟩)
      hcent_A B hB S hSC hSn hSp
  · exact normal_prime_complements_trivial_of_commutantIdeal hp (by omega) hf (by norm_num) hk
      commutantIdeal_B idealB_N (uB k) (coe_oneAdd _ _) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 2)
      (fun c => ⟨idealB_single c (Or.inl rfl), idealB_single c (Or.inr (Or.inl rfl))⟩)
      hcent_B B hB S hSC hSn hSp
  · exact normal_prime_complements_trivial_of_commutantIdeal hp (by omega) hf (by norm_num) hk
      commutantIdeal_C idealC_N (uC k) (coe_oneAdd _ _) (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)
      (fun c => ⟨idealC_single c (Or.inl rfl), idealC_single c (Or.inr (Or.inl rfl))⟩)
      hcent_C B hB S hSC hSn hSp
  · exact normal_prime_complements_trivial_of_commutantIdeal hp (by omega) hf (by norm_num) hk
      commutantIdeal_D idealD_N (uD k) (coe_oneAdd _ _) (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (0 : Fin 4) ≠ 3) (by decide : (2 : Fin 4) ≠ 3)
      (fun c => ⟨idealD_single c (Or.inl rfl), idealD_single c (Or.inr (Or.inl rfl))⟩)
      hcent_D B hB S hSC hSn hSp

end CFSG.RankThree.NonregularUnipotent
