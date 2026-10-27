module

public import CFSG.RankThree.GF2n.Smith81.Orth28Eps
public import CFSG.RankThree.GF2n.Smith81.Orth28Kx
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace OrthEps

section Dim

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_ne_zero_zero_of_three_le_finrank {M : Type} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q' : QuadraticForm K M) (h3 : 3 ≤ Module.finrank K M) :
    ∃ z : M, z ≠ 0 ∧ Q' z = 0 := by
  classical
  have := Fintype.ofFinite K
  let m := Module.finrank K M
  let b : Module.Basis (Fin m) K M := Module.finBasis K M
  let B' := Q'.toBilin b
  let P : MvPolynomial (Fin m) K := ∑ i, ∑ j,
    MvPolynomial.C (B' (b i) (b j)) * (MvPolynomial.X i * MvPolynomial.X j)
  have hdeg : P.totalDegree < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    have h2 : P.totalDegree ≤ 2 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have heval : ∀ x : Fin m → K, MvPolynomial.eval x P = Q' (∑ i, x i • b i) := by
    intro x
    have hQ : Q' (∑ i, x i • b i) = B' (∑ i, x i • b i) (∑ i, x i • b i) := by
      conv_lhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q' b]
      rfl
    rw [hQ, LinearMap.map_sum₂]
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    ring
  have hpr : Nat.Prime 2 := Nat.prime_two
  have hdvd := char_dvd_card_solutions (K := K) (σ := Fin m) 2 hdeg
  have h0 : MvPolynomial.eval (0 : Fin m → K) P = 0 := by
    rw [heval]
    simp
  have hpos : 0 < Fintype.card { x : Fin m → K // MvPolynomial.eval x P = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : 1 < Fintype.card { x : Fin m → K // MvPolynomial.eval x P = 0 } := by
    have := Nat.le_of_dvd hpos hdvd
    have hp2 := hpr.two_le
    omega
  obtain ⟨⟨x, hx⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hone ⟨0, h0⟩
  have hx0 : x ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨∑ i, x i • b i, fun h => hx0 ?_, by rw [← heval]; exact hx⟩
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent x h)

end Dim

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]

theorem exists_plane_of_five_le (q : QuadraticForm K (ι → K)) (h5 : 5 ≤ Fintype.card ι)
    (hsing : ∃ u : ι → K, u ≠ 0 ∧ q u = 0) :
    ∃ s t : ι → K, q s = 0 ∧ q t = 0 ∧ polar q s t = 0 ∧
      ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0 := by
  obtain ⟨u, hu0, hqu⟩ := hsing
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  let ψ : (ι → K) →ₗ[K] K := (u i)⁻¹ • LinearMap.proj i
  have hψu : ψ u = 1 := by simp [ψ, inv_mul_cancel₀ hi]
  let f : (ι → K) →ₗ[K] K := q.polarBilin u
  have hn : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have h1 := finrank_le_finrank_ker_add_one f
  have h2 := finrank_le_finrank_ker_add_one ψ
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.ker ψ)
  have hsup : Module.finrank K ↥(LinearMap.ker f ⊔ LinearMap.ker ψ) ≤ Module.finrank K (ι → K) :=
    Submodule.finrank_le _
  have h3 : 3 ≤ Module.finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker ψ) := by omega
  obtain ⟨z, hz0, hqz⟩ := exists_ne_zero_zero_of_three_le_finrank
    (q.comp (LinearMap.ker f ⊓ LinearMap.ker ψ).subtype) h3
  refine ⟨z.1, u, hqz, hqu, ?_, fun a b hab => ?_⟩
  · have : f z.1 = 0 := z.2.1
    rw [QuadraticMap.polar_comm]
    exact this
  · have hz1 : ψ z.1 = 0 := z.2.2
    have hb : b = 0 := by
      have := congrArg ψ hab
      rw [map_add, map_smul, map_smul, hz1, hψu] at this
      simpa using this
    subst hb
    simp only [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right (fun h => hz0 (Subtype.ext h)), rfl⟩

end Plane

section FourMinus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {q : QuadraticForm K V} {o : V ≃ₗ[K] V}

theorem four_minus_P (hq : q.polarBilin.Nondegenerate)
    (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hoo : o * o = 1)
    (hdim : Module.finrank K V = 4)
    (heven : Even (Module.finrank K (OrthogonalInvolutions.commSpace o))) (ho1 : o ≠ 1)
    (hno : ∀ s t : V, q s = 0 → q t = 0 → polar q s t = 0 →
      ¬ ∀ a b : K, a • s + b • t = 0 → a = 0 ∧ b = 0) :
    ∃ a w : V, a ≠ 0 ∧ q a = 0 ∧ a ∈ OrthogonalInvolutions.commSpace o ∧
      w ∈ OrthogonalInvolutions.commSpace o ∧ polar q a w = 0 ∧ q w ≠ 0 ∧
      (∀ α β : K, α • a + β • w = 0 → α = 0 ∧ β = 0) ∧
      (∀ p ∈ OrthogonalInvolutions.commSpace o, ∃ α β : K, p = α • a + β • w) ∧
      (∀ s ∈ OrthogonalInvolutions.commSpace o, q s = 0 → ∃ α : K, s = α • a) ∧
      (∀ v, (∀ p ∈ OrthogonalInvolutions.commSpace o, polar q p v = 0) →
        v ∈ OrthogonalInvolutions.commSpace o) ∧
      (∀ v, o v = v → v ∈ OrthogonalInvolutions.commSpace o) := by
  have h1 := OrthogonalInvolutions.one_le_finrank_commSpace ho1
  have h2 := OrthogonalInvolutions.two_mul_finrank_commSpace_le (K := K) (V := V) hoo
  have hP : Module.finrank K (OrthogonalInvolutions.commSpace o) = 2 := by
    obtain ⟨r, hr⟩ := heven
    omega
  have hsum := OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace o
  have hPC : OrthogonalInvolutions.commSpace o = OrthogonalInvolutions.fixSpace o :=
    Submodule.eq_of_le_of_finrank_eq (OrthogonalInvolutions.commSpace_le_fixSpace hoo)
      (by omega)
  have hperp : ∀ v, (∀ p ∈ OrthogonalInvolutions.commSpace o, polar q p v = 0) →
      v ∈ OrthogonalInvolutions.commSpace o := by
    intro v hv
    rw [hPC, OrthogonalInvolutions.fixSpace_eq_orthogonal_commSpace hq ho hoo,
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro p hp
    exact hv p hp
  obtain ⟨a, haP, ha0, hqa⟩ := exists_singular_mem_commSpace ho hoo (by omega)
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := K) (M := OrthogonalInvolutions.commSpace o) (by omega)
    (x := (⟨a, haP⟩ : OrthogonalInvolutions.commSpace o))
    (fun h => ha0 (congrArg Subtype.val h))
  have hy' : LinearIndependent K ![a, (y : V)] := by
    have := hy.map' (OrthogonalInvolutions.commSpace o).subtype
      (Submodule.ker_subtype _)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hind : ∀ α β : K, α • a + β • (y : V) = 0 → α = 0 ∧ β = 0 :=
    LinearIndependent.pair_iff.mp hy'
  have hawo : polar q a (y : V) = 0 :=
    OrthogonalInvolutions.polar_commSpace_eq_zero ho hoo haP y.2
  have hqw : q (y : V) ≠ 0 := fun h => hno a y hqa h hawo hind
  have hspan : Submodule.span K {a, (y : V)} = OrthogonalInvolutions.commSpace o := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact haP
      · exact y.2
    · have h3 := finrank_span_eq_card hy'
      have hr : Set.range ![a, (y : V)] = ({a, (y : V)} : Set V) := by
        ext x
        simp [Fin.exists_fin_two, eq_comm, or_comm]
      rw [hr] at h3
      simp only [Fintype.card_fin] at h3
      rw [hP]
      simpa using h3
  have hcoord : ∀ p ∈ OrthogonalInvolutions.commSpace o, ∃ α β : K, p = α • a + β • (y : V) := by
    intro p hp
    rw [← hspan] at hp
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hp
    exact ⟨α, β, hαβ.symm⟩
  refine ⟨a, y, ha0, hqa, haP, y.2, hawo, hqw, hind, hcoord, ?_, hperp, ?_⟩
  swap
  · intro v hv
    rw [hPC]
    exact OrthogonalInvolutions.mem_fixSpace.mpr hv
  intro s hs hqs
  obtain ⟨α, β, rfl⟩ := hcoord s hs
  have : q (α • a + β • (y : V)) = β ^ 2 * q (y : V) := by
    rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hawo, hqa]
    simp [pow_two]
  rw [this] at hqs
  have hβ : β = 0 := by
    rcases mul_eq_zero.mp hqs with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · exact absurd h hqw
  exact ⟨α, by rw [hβ, zero_smul, add_zero]⟩

end FourMinus

section Dual

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {q : QuadraticForm K V}

theorem exists_dual_pair (hq : q.polarBilin.Nondegenerate) {a w : V}
    (hind : ∀ α β : K, α • a + β • w = 0 → α = 0 ∧ β = 0) :
    ∃ b c : V, polar q a b = 1 ∧ polar q w b = 0 ∧ polar q a c = 0 ∧ polar q w c = 1 := by
  have hnd : ∀ x : V, (∀ y, polar q x y = 0) → x = 0 := fun x hx =>
    hq.1 x fun y => by simpa using hx y
  have ha0 : a ≠ 0 := fun h => one_ne_zero (hind 1 0 (by simp [h])).1
  obtain ⟨v₁, hv₁⟩ : ∃ v₁, polar q a v₁ = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, polar q a y ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (hnd a h)
    exact ⟨(polar q a y)⁻¹ • y, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  obtain ⟨c₀, hc₀a, hc₀w⟩ : ∃ c₀, polar q a c₀ = 0 ∧ polar q w c₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hz : w - polar q w v₁ • a = 0 := by
      refine hnd _ fun v => ?_
      have h1 := h (v - polar q a v • v₁) (by
        rw [polar_sub_right, polar_smul_right, hv₁, smul_eq_mul, mul_one, sub_self])
      rw [polar_sub_right, polar_smul_right, smul_eq_mul] at h1
      rw [polar_sub_left, polar_smul_left, smul_eq_mul]
      linear_combination h1
    exact one_ne_zero (hind (-polar q w v₁) 1 (by
      rw [neg_smul, one_smul, neg_add_eq_sub]
      exact hz)).2
  have hinv : (polar q w c₀)⁻¹ * polar q w c₀ = 1 := inv_mul_cancel₀ hc₀w
  refine ⟨v₁ - polar q w v₁ • (polar q w c₀)⁻¹ • c₀, (polar q w c₀)⁻¹ • c₀, ?_, ?_, ?_, ?_⟩
  · simp only [polar_sub_right, polar_smul_right, smul_eq_mul, hc₀a, hv₁]
    ring
  · simp only [polar_sub_right, polar_smul_right, smul_eq_mul]
    linear_combination (-(polar q w v₁)) * hinv
  · simp only [polar_smul_right, smul_eq_mul, hc₀a]
    ring
  · simp only [polar_smul_right, smul_eq_mul]
    exact hinv

end Dual

section FixCount

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {q : QuadraticForm K V}

structure PairData (q : QuadraticForm K V) (P : Submodule K V) (a w b c : V) : Prop where
  ha : a ∈ P
  hw : w ∈ P
  hqa : q a = 0
  haw : polar q a w = 0
  hcoord : ∀ p ∈ P, ∃ α β : K, p = α • a + β • w
  hperp : ∀ v, (∀ p ∈ P, polar q p v = 0) → v ∈ P
  hPo : ∀ p ∈ P, ∀ p' ∈ P, polar q p p' = 0
  hab : polar q a b = 1
  hwb : polar q w b = 0
  hac : polar q a c = 0
  hwc : polar q w c = 1

variable {P : Submodule K V} {a w b c : V}

theorem PairData.eq_coord (hd : PairData q P a w b c) {p : V} (hp : p ∈ P) :
    p = polar q p b • a + polar q p c • w := by
  obtain ⟨α, β, rfl⟩ := hd.hcoord p hp
  have h1 : polar q (α • a + β • w) b = α := by
    rw [polar_add_left, polar_smul_left, polar_smul_left, hd.hab, hd.hwb]
    simp
  have h2 : polar q (α • a + β • w) c = β := by
    rw [polar_add_left, polar_smul_left, polar_smul_left, hd.hac, hd.hwc]
    simp
  rw [h1, h2]

theorem PairData.map_coord (hd : PairData q P a w b c) (α β : K) :
    q (α • a + β • w) = β ^ 2 * q w := by
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hd.haw, hd.hqa]
  simp [pow_two]

variable {o : V ≃ₗ[K] V}

theorem PairData.fixes_P (hd : PairData q P a w b c) (ha' : o a = a) (hw' : o w = w) {p : V}
    (hp : p ∈ P) : o p = p := by
  obtain ⟨α, β, rfl⟩ := hd.hcoord p hp
  rw [map_add, map_smul, map_smul, ha', hw']

theorem PairData.sub_mem (hd : PairData q P a w b c)
    (hiso : ∀ v, q (o v) = q v) (ha' : o a = a) (hw' : o w = w) (v : V) : o v - v ∈ P := by
  have hO := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  refine hd.hperp _ fun p hp => ?_
  have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO p v
  rw [hd.fixes_P ha' hw' hp] at h
  rw [polar_sub_right, h, sub_self]

theorem PairData.sub_eq (hd : PairData q P a w b c)
    (hiso : ∀ v, q (o v) = q v) (ha' : o a = a) (hw' : o w = w) (v : V) :
    o v - v = polar q a v • (o b - b) + polar q w v • (o c - c) := by
  set v₀ : V := v - polar q a v • b - polar q w v • c with hv₀
  have hv₀P : v₀ ∈ P := by
    refine hd.hperp _ fun p hp => ?_
    obtain ⟨α, β, rfl⟩ := hd.hcoord p hp
    have e1 : polar q a v₀ = 0 := by
      rw [hv₀]
      simp only [polar_sub_right, polar_smul_right, smul_eq_mul, hd.hab, hd.hac]
      ring
    have e2 : polar q w v₀ = 0 := by
      rw [hv₀]
      simp only [polar_sub_right, polar_smul_right, smul_eq_mul, hd.hwb, hd.hwc]
      ring
    rw [polar_add_left, polar_smul_left, polar_smul_left, e1, e2]
    simp
  have hfix := hd.fixes_P ha' hw' hv₀P
  have hv : v = v₀ + polar q a v • b + polar q w v • c := by
    rw [hv₀]
    abel
  have h2 : o v = o v₀ + polar q a v • o b + polar q w v • o c := by
    conv_lhs => rw [hv]
    rw [map_add, map_add, map_smul, map_smul]
  rw [h2, hfix]
  conv_lhs => rw [hv]
  rw [smul_sub, smul_sub]
  conv_lhs => rw [hv₀]
  abel

theorem q_sub_eq_polar (hiso : ∀ v, q (o v) = q v) (v : V) :
    q (o v - v) = polar q v (o v - v) := by
  have h : q (v + (o v - v)) = q v := by rw [add_sub_cancel]; exact hiso v
  rw [OrthogonalInvolutions.map_add_eq q v (o v - v)] at h
  have h' : q (o v - v) + polar q v (o v - v) = 0 := by
    have := h
    linear_combination this
  exact CharTwo.add_eq_zero.mp h'

theorem PairData.constraints (hd : PairData q P a w b c)
    (hiso : ∀ v, q (o v) = q v) (ha' : o a = a) (hw' : o w = w) :
    polar q (o b - b) b = q w * polar q (o b - b) c ^ 2 ∧
      polar q (o c - c) b = polar q (o b - b) c ∧
      q w * polar q (o c - c) c ^ 2 = polar q (o c - c) c := by
  have hnb := hd.sub_mem hiso ha' hw' b
  have hnc := hd.sub_mem hiso ha' hw' c
  have hqb : q (o b - b) = q w * polar q (o b - b) c ^ 2 := by
    conv_lhs => rw [hd.eq_coord hnb]
    rw [hd.map_coord]
    ring
  have hqc : q (o c - c) = q w * polar q (o c - c) c ^ 2 := by
    conv_lhs => rw [hd.eq_coord hnc]
    rw [hd.map_coord]
    ring
  have e1 := q_sub_eq_polar hiso b
  have e2 := q_sub_eq_polar hiso c
  have e3 := q_sub_eq_polar hiso (b + c)
  have hn : o (b + c) - (b + c) = (o b - b) + (o c - c) := by rw [map_add]; abel
  rw [hn, QuadraticMap.map_add q, hd.hPo _ hnb _ hnc, add_zero, polar_add_left,
    polar_add_right, polar_add_right] at e3
  rw [e1, e2] at e3
  refine ⟨?_, ?_, ?_⟩
  · rw [← hqb, e1, polar_comm]
  · have h4 : polar q b (o c - c) + polar q c (o b - b) = 0 := by linear_combination (-1 : K) * e3
    rw [polar_comm q (o c - c) b, polar_comm q (o b - b) c]
    exact CharTwo.add_eq_zero.mp h4
  · rw [← hqc, e2, polar_comm]

theorem PairData.ext_of_polar (hd : PairData q P a w b c) {o₁ o₂ : V ≃ₗ[K] V}
    (hiso₁ : ∀ v, q (o₁ v) = q v) (ha₁ : o₁ a = a) (hw₁ : o₁ w = w)
    (hiso₂ : ∀ v, q (o₂ v) = q v) (ha₂ : o₂ a = a) (hw₂ : o₂ w = w)
    (hb : polar q (o₁ b - b) c = polar q (o₂ b - b) c)
    (hc : polar q (o₁ c - c) c = polar q (o₂ c - c) c) : o₁ = o₂ := by
  obtain ⟨c11, c12, -⟩ := hd.constraints hiso₁ ha₁ hw₁
  obtain ⟨c21, c22, -⟩ := hd.constraints hiso₂ ha₂ hw₂
  have hnb : o₁ b - b = o₂ b - b := by
    rw [hd.eq_coord (hd.sub_mem hiso₁ ha₁ hw₁ b), hd.eq_coord (hd.sub_mem hiso₂ ha₂ hw₂ b), c11,
      c21, hb]
  have hnc : o₁ c - c = o₂ c - c := by
    rw [hd.eq_coord (hd.sub_mem hiso₁ ha₁ hw₁ c), hd.eq_coord (hd.sub_mem hiso₂ ha₂ hw₂ c), c12,
      c22, hb, hc]
  refine LinearEquiv.ext fun v => ?_
  have := hd.sub_eq hiso₁ ha₁ hw₁ v
  rw [hnb, hnc, ← hd.sub_eq hiso₂ ha₂ hw₂ v] at this
  exact sub_left_injective this

structure FourData (q : QuadraticForm K V) (o : V ≃ₗ[K] V) (a w b c : V) : Prop where
  pair : PairData q (OrthogonalInvolutions.commSpace o) a w b c
  ha0 : a ≠ 0
  hqw : q w ≠ 0
  hsing : ∀ s ∈ OrthogonalInvolutions.commSpace o, q s = 0 → ∃ α : K, s = α • a
  hfix : ∀ v, o v = v → v ∈ OrthogonalInvolutions.commSpace o


end FixCount

section Group

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_root_z₀ {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    ∃ z₀ ∈ Z, z₀ ≠ 1 ∧ IsConj z₀ x := by
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  refine ⟨g₀⁻¹ * x * g₀, hz₀, ?_, isConj_iff.mpr ⟨g₀, by group⟩⟩
  intro h
  apply hs.ne_one
  have : x = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by group
  rw [this, h]; group

theorem gamma_eq_of_eq {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z) (h : γ a = γ b) :
    a = b := by
  have h1 := hD.reg.one
  have hb' : γ b⁻¹ = -γ b := by
    have := hD.reg.add b hb b⁻¹ (Z.inv_mem hb)
    rw [mul_inv_cancel, h1] at this
    linear_combination -this
  have := hD.reg.inj (a * b⁻¹) (Z.mul_mem ha (Z.inv_mem hb)) (by
    rw [hD.reg.add a ha b⁻¹ (Z.inv_mem hb), hb', h]; ring)
  exact mul_inv_eq_one.mp this

theorem exists_comm_lift (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {X : Subgroup G}
    {x : G} (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU) (hoo : o * o = 1)
    {p : (C.ι → C.K) × (C.ι → C.K)} (hp1 : p.1 ∈ OrthogonalInvolutions.commSpace o)
    (hp2 : p.2 ∈ OrthogonalInvolutions.commSpace o) :
    ∃ q₀ ∈ Q, C.φ (C.M₀.π ⁅q₀, x⁆) = p ∧ x * ⁅q₀, x⁆ = ⁅q₀, x⁆ * x := by
  have H := hc.ctx.hyp
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨s₁, hs₁⟩ := OrthogonalInvolutions.mem_commSpace.mp hp1
  obtain ⟨s₂, hs₂⟩ := OrthogonalInvolutions.mem_commSpace.mp hp2
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) ((-s₁, -s₂) : _ × _)
  have hφ : C.φ (C.M₀.π ⁅q₀, x⁆) = p := by
    rw [OrthEps.phi_pi_commutator C hxQ hq₀Q hact, hq₀]
    refine Prod.ext ?_ ?_
    · simp only [orthTensor, Matrix.one_apply, Prod.fst_sub, map_neg]
      simp only [Fin.isValue, ↓reduceIte, one_smul, Fin.reduceEq, zero_smul, add_zero, map_neg]
      rw [← hs₁]; abel
    · simp only [orthTensor, Matrix.one_apply, Prod.snd_sub, map_neg]
      simp only [Fin.isValue, ↓reduceIte, one_smul, Fin.reduceEq, zero_smul, zero_add, map_neg]
      rw [← hs₂]; abel
  refine ⟨q₀, hq₀Q, hφ, ?_⟩
  have hkQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hsq : ⁅q₀, x⁆ ^ 2 ∈ Z := C.M₀.sq_mem _ hkQ
  have hγ : C.γ (⁅q₀, x⁆ ^ 2) = 0 := by
    rw [C.M₀.sq_eq _ hkQ, C.hF.qf, hφ]
    exact OrthogonalInvolutions.polar_commSpace_eq_zero hO hoo hp1 hp2
  have h1 : ⁅q₀, x⁆ ^ 2 = 1 := C.hD.reg.inj _ hsq hγ
  exact commute_comm_of_sq hs.x_sq (by rw [← pow_two]; exact h1)

theorem phi_pi_mem_of_commute (C : OrthCtx M Q Z B) {x : G}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hfix : ∀ v, o v = v → v ∈ OrthogonalInvolutions.commSpace o) {d : G} (hdQ : d ∈ Q)
    (hdx : d * x = x * d) :
    (C.φ (C.M₀.π d)).1 ∈ OrthogonalInvolutions.commSpace o ∧
      (C.φ (C.M₀.π d)).2 ∈ OrthogonalInvolutions.commSpace o := by
  have h1 : x * d * x⁻¹ = d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hdx.symm
  have h2 := hact d hdQ
  rw [h1] at h2
  have e1 : o (C.φ (C.M₀.π d)).1 = (C.φ (C.M₀.π d)).1 := by
    have := congrArg Prod.fst h2
    simp only [orthTensor, Matrix.one_apply] at this
    simpa using this.symm
  have e2 : o (C.φ (C.M₀.π d)).2 = (C.φ (C.M₀.π d)).2 := by
    have := congrArg Prod.snd h2
    simp only [orthTensor, Matrix.one_apply] at this
    simpa using this.symm
  exact ⟨hfix _ e1, hfix _ e2⟩

theorem Z_le_commutator (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) {x q₀ : G}
    (hq₀ : q₀ ∈ Q) (hne : C.M₀.π ⁅q₀, x⁆ ≠ 0) (hxM : x ∈ M) :
    Z ≤ ⁅Q, Subgroup.zpowers x⁆ := by
  have H := hc.ctx.hyp
  have hc₀Q : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hxM hq₀
  have hc₀W : ⁅q₀, x⁆ ∈ ⁅Q, Subgroup.zpowers x⁆ :=
    Subgroup.commutator_mem_commutator hq₀ (Subgroup.mem_zpowers x)
  intro z' hz'
  obtain ⟨e, he⟩ : ∃ e, C.M₀.B (C.M₀.π ⁅q₀, x⁆) e ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (C.M₀.nondeg _ h)
  obtain ⟨q₁, hq₁Q, hq₁⟩ := C.M₀.π_surj ((C.γ z' * (C.M₀.B (C.M₀.π ⁅q₀, x⁆) e)⁻¹) • e)
  have hB : C.M₀.B (C.M₀.π ⁅q₀, x⁆) (C.M₀.π q₁) = C.γ z' := by
    rw [hq₁, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ he, mul_one]
  have hcomm : ⁅⁅q₀, x⁆, q₁⁆ = z' := by
    refine gamma_eq_of_eq C.hD (C.M₀.comm_mem _ hc₀Q _ hq₁Q) hz' ?_
    rw [C.M₀.comm_eq _ hc₀Q _ hq₁Q, hB]
  rw [← hcomm]
  have hcon : q₁ * ⁅q₀, x⁆ * q₁⁻¹ = ⁅q₁ * q₀, x⁆ * ⁅q₁, x⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  have hmem : q₁ * ⁅q₀, x⁆ * q₁⁻¹ ∈ ⁅Q, Subgroup.zpowers x⁆ := by
    rw [hcon]
    exact Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (Q.mul_mem hq₁Q hq₀) (Subgroup.mem_zpowers x))
      (Subgroup.inv_mem _
        (Subgroup.commutator_mem_commutator hq₁Q (Subgroup.mem_zpowers x)))
  have e : ⁅⁅q₀, x⁆, q₁⁆ = ⁅q₀, x⁆ * (q₁ * ⁅q₀, x⁆ * q₁⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ hc₀W (Subgroup.inv_mem _ hmem)

theorem mem_commutator_of_phi_mem (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU) (hoo : o * o = 1) (ho1 : o ≠ 1)
    {d : G} (hdQ : d ∈ Q) (h1 : (C.φ (C.M₀.π d)).1 ∈ OrthogonalInvolutions.commSpace o)
    (h2 : (C.φ (C.M₀.π d)).2 ∈ OrthogonalInvolutions.commSpace o) :
    d ∈ ⁅Q, Subgroup.zpowers x⁆ := by
  have H := hc.ctx.hyp
  obtain ⟨v, hv⟩ : ∃ v, o v ≠ v := by
    by_contra h
    push Not at h
    exact ho1 (LinearEquiv.ext h)
  obtain ⟨q₁, hq₁Q, hq₁φ, -⟩ := exists_comm_lift hc C hs hact hO hoo
    (p := ((o v - v, 0) : (C.ι → C.K) × (C.ι → C.K)))
    (OrthogonalInvolutions.sub_mem_commSpace o v) (Submodule.zero_mem _)
  have hne : C.M₀.π ⁅q₁, x⁆ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hq₁φ
    exact hv (sub_eq_zero.mp (congrArg Prod.fst hq₁φ).symm)
  have hZ := Z_le_commutator hc C hq₁Q hne hs.memM
  obtain ⟨q₀, hq₀Q, hq₀φ, -⟩ := exists_comm_lift hc C hs hact hO hoo
    (p := C.φ (C.M₀.π d)) h1 h2
  have hkQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hdk : d * ⁅q₀, x⁆⁻¹ ∈ Z := by
    refine (C.M₀.π_ker _ (Q.mul_mem hdQ (Q.inv_mem hkQ))).mp ?_
    rw [C.M₀.π_mul _ hdQ _ (Q.inv_mem hkQ), Tim79.QuadModel.pi_inv C.M₀ hkQ]
    have := C.φ.injective hq₀φ
    rw [this, add_neg_cancel]
  have : d = (d * ⁅q₀, x⁆⁻¹) * ⁅q₀, x⁆ := by group
  rw [this]
  exact Subgroup.mul_mem _ (hZ hdk)
    (Subgroup.commutator_mem_commutator hq₀Q (Subgroup.mem_zpowers x))

theorem commute_of_actions (C : OrthCtx M Q Z B) {x ℓ : G} (hxℓ : x * ℓ = ℓ * x)
    (hℓQ : ∀ y ∈ Q, ℓ * y * ℓ⁻¹ ∈ Q) (hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q)
    {g : Matrix (Fin 2) (Fin 2) C.K} (hg : g.det ≠ 0)
    {o oℓ : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hactℓ : ActsAsTensor Q Z C.M₀ C.φ ℓ g ⇑oℓ) (v : C.ι → C.K) : o (oℓ v) = oℓ (o v) := by
  have h1 := ActsAsTensor.mul (o := (o : (C.ι → C.K) →ₗ[C.K] _)) (o' := (oℓ : _ →ₗ[C.K] _))
    hℓQ hact hactℓ
  have h2 := ActsAsTensor.mul (o := (oℓ : (C.ι → C.K) →ₗ[C.K] _)) (o' := (o : _ →ₗ[C.K] _))
    hxQ hactℓ hact
  rw [hxℓ] at h1
  have e := h1.orthTensor_eq h2 (v, 0)
  simp only [orthTensor, one_mul, mul_one, LinearMap.coe_comp, Function.comp_apply, map_zero,
    smul_zero, add_zero, LinearEquiv.coe_coe, Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  by_cases h00 : g 0 0 = 0
  · have h10 : g 1 0 ≠ 0 := by
      intro h10
      apply hg
      rw [Matrix.det_fin_two, h00, h10]
      ring
    exact smul_right_injective _ h10 e2
  · exact smul_right_injective _ h00 e1

theorem multiplier_eq_one (C : OrthCtx M Q Z B) {ℓ : G} (hℓQ : ∀ y ∈ Q, ℓ * y * ℓ⁻¹ ∈ Q)
    {o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hact : ActsAsTensor Q Z C.M₀ C.φ ℓ 1 ⇑o')
    {ρ : C.K} (hρ : ∀ v, C.qU (o' v) = ρ * C.qU v) {m : ℕ} (hm : ℓ ^ (2 ^ m) = 1)
    {v₀ : C.ι → C.K} (hv₀ : C.qU v₀ ≠ 0) : ρ = 1 := by
  have hiter : ∀ j : ℕ, ∀ y ∈ Q, ℓ ^ j * y * (ℓ ^ j)⁻¹ ∈ Q ∧
      C.φ (C.M₀.π (ℓ ^ j * y * (ℓ ^ j)⁻¹)) =
        ((⇑o')^[j] (C.φ (C.M₀.π y)).1, (⇑o')^[j] (C.φ (C.M₀.π y)).2) := by
    intro j
    induction j with
    | zero => intro y hy; simpa using hy
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      have e : ℓ ^ (j + 1) * y * (ℓ ^ (j + 1))⁻¹ = ℓ * (ℓ ^ j * y * (ℓ ^ j)⁻¹) * ℓ⁻¹ := by
        rw [pow_succ']; group
      rw [e]
      refine ⟨hℓQ _ h1, ?_⟩
      rw [hact _ h1, h2]
      simp [orthTensor, Matrix.one_apply, Function.iterate_succ_apply']
  have hfix : ∀ v, (⇑o')^[2 ^ m] v = v := by
    intro v
    obtain ⟨y, hy, hyφ⟩ := exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) ((v, 0) : _ × _)
    have := (hiter (2 ^ m) y hy).2
    rw [hm, hyφ] at this
    simp only [inv_one, mul_one, one_mul] at this
    rw [hyφ] at this
    exact (congrArg Prod.fst this).symm
  have hq : ∀ (k : ℕ) (v : C.ι → C.K), C.qU ((⇑o')^[k] v) = ρ ^ k * C.qU v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', hρ, ih, pow_succ]
      ring
  have h1 : ρ ^ (2 ^ m) = 1 := by
    have := hq (2 ^ m) v₀
    rw [hfix] at this
    have h3 : (ρ ^ (2 ^ m) - 1) * C.qU v₀ = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hv₀)
  have h2 : (ρ - 1) ^ (2 ^ m) = 0 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)

theorem Lx_action (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hsim : OrthSim C)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU) (hoo : o * o = 1)
    {a w b c : C.ι → C.K} (hd : FourData C.qU o a w b c)
    (hneg : ∀ d ∈ Q ⊓ QB X, ∀ α β : C.K, C.φ (C.M₀.π d) = (α • a, β • a) → α = 0 ∧ β = 0)
    {ℓ : G} (hℓ : ℓ ∈ Lx M X) :
    ∃ o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K), ActsAsTensor Q Z C.M₀ C.φ ℓ 1 ⇑o' ∧
      (∀ v, C.qU (o' v) = C.qU v) ∧ o' a = a ∧ o' w = w := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hℓM : ℓ ∈ M := (Subgroup.mem_inf.mp hℓ).2
  have hℓQB : ℓ ∈ QB X := (Subgroup.mem_inf.mp hℓ).1
  have hℓH0 : ℓ ∈ H0 M Z := Lx_le_H0 hs h12 hℓ
  have hℓQ : ∀ y ∈ Q, ℓ * y * ℓ⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hℓM).1
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hs.memM).1
  obtain ⟨g, oℓ, ρ, hg, hρ, hqρ, hactℓ⟩ := hsim ℓ hℓH0
  obtain ⟨gc, hgc⟩ := hs.conj
  have hX : IsZConjugate Z X := ⟨gc, hgc⟩
  have hxℓ : x * ℓ = ℓ * x := IsZConjugate.central_QB H hX hs.mem hℓQB
  have hcomm := commute_of_actions C hxℓ hℓQ hxQ hg hact hactℓ
  have hPℓ : ∀ p ∈ OrthogonalInvolutions.commSpace o,
      oℓ p ∈ OrthogonalInvolutions.commSpace o := by
    intro p hp
    obtain ⟨u, hu⟩ := OrthogonalInvolutions.mem_commSpace.mp hp
    refine OrthogonalInvolutions.mem_commSpace.mpr ⟨oℓ u, ?_⟩
    rw [← hu, map_sub, hcomm u]
  obtain ⟨lam, hlam⟩ := hd.hsing (oℓ a) (hPℓ a hd.pair.ha) (by
    rw [hqρ, hd.pair.hqa, mul_zero])
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hlam
    exact hd.ha0 (oℓ.map_eq_zero_iff.mp hlam)
  have hcoef : ∀ e : Fin 2 → C.K,
      e 0 = lam * (g 0 0 * e 0 + g 0 1 * e 1) ∧ e 1 = lam * (g 1 0 * e 0 + g 1 1 * e 1) := by
    intro e
    obtain ⟨q₀, hq₀Q, hq₀φ, hq₀x⟩ := exists_comm_lift hc C hs hact hO hoo
      (p := ((e 0 • a, e 1 • a) : (C.ι → C.K) × (C.ι → C.K)))
      (Submodule.smul_mem _ _ hd.pair.ha) (Submodule.smul_mem _ _ hd.pair.ha)
    have hkQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
    have hkK : ⁅q₀, x⁆ ∈ Kx Q X := centralizer_le_Kx hs
      ⟨hkQ, Subgroup.mem_centralizer_singleton_iff.mpr hq₀x.symm⟩
    have hdD : ⁅⁅q₀, x⁆, ℓ⁆ ∈ Q ⊓ QB X :=
      (smith_1_13_of_post12 hs h12).1 (Subgroup.commutator_mem_commutator hkK hℓ)
    have hφd := OrthEps.phi_pi_commutator C hℓQ hkQ hactℓ
    rw [hq₀φ] at hφd
    have hform : C.φ (C.M₀.π ⁅⁅q₀, x⁆, ℓ⁆) =
        ((e 0 - lam * (g 0 0 * e 0 + g 0 1 * e 1)) • a,
          (e 1 - lam * (g 1 0 * e 0 + g 1 1 * e 1)) • a) := by
      rw [hφd]
      refine Prod.ext ?_ ?_ <;> simp only [orthTensor, map_smul, hlam, Prod.fst_sub,
        Prod.snd_sub, smul_smul] <;> module
    obtain ⟨h1, h2⟩ := hneg _ hdD _ _ hform
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  have e1 := hcoef ![1, 0]
  have e2 := hcoef ![0, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero,
    zero_add] at e1 e2
  have hg00 : g 0 0 = lam⁻¹ := eq_inv_of_mul_eq_one_right e1.1.symm
  have hg11 : g 1 1 = lam⁻¹ := eq_inv_of_mul_eq_one_right e2.2.symm
  have hg10 : g 1 0 = 0 := (mul_eq_zero.mp e1.2.symm).resolve_left hlam0
  have hg01 : g 0 1 = 0 := (mul_eq_zero.mp e2.1.symm).resolve_left hlam0
  let o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K) :=
    oℓ.trans (LinearEquiv.smulOfNeZero C.K (C.ι → C.K) lam⁻¹ (inv_ne_zero hlam0))
  have ho'v : ∀ v, o' v = lam⁻¹ • oℓ v := fun v => rfl
  have hacto' : ActsAsTensor Q Z C.M₀ C.φ ℓ 1 ⇑o' := by
    intro y hy
    rw [hactℓ y hy]
    refine Prod.ext ?_ ?_ <;> simp [orthTensor, ho'v, hg00, hg11, hg10, hg01, Matrix.one_apply]
  have hqo' : ∀ v, C.qU (o' v) = (lam⁻¹ ^ 2 * ρ) * C.qU v := by
    intro v
    rw [ho'v, QuadraticMap.map_smul, hqρ, smul_eq_mul, pow_two]
    ring
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ℓ ^ (2 ^ m) = 1 := by
    obtain ⟨m, hm⟩ := IsZConjugate.isPGroup_QB H hX (⟨ℓ, hℓQB⟩ : QB X)
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_ctx hc.ctx C
  have hρ1 : lam⁻¹ ^ 2 * ρ = 1 := multiplier_eq_one C hℓQ hacto' hqo' hm hv₀
  have hiso : ∀ v, C.qU (o' v) = C.qU v := fun v => by rw [hqo', hρ1, one_mul]
  have ho'a : o' a = a := by
    rw [ho'v, hlam, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have ho'P : ∀ p ∈ OrthogonalInvolutions.commSpace o, o' p ∈ OrthogonalInvolutions.commSpace o :=
    fun p hp => by rw [ho'v]; exact Submodule.smul_mem _ _ (hPℓ p hp)
  obtain ⟨q₀, hq₀Q, hq₀φ, hq₀x⟩ := exists_comm_lift hc C hs hact hO hoo
    (p := ((w, 0) : (C.ι → C.K) × (C.ι → C.K))) hd.pair.hw (Submodule.zero_mem _)
  have hkQ : ⁅q₀, x⁆ ∈ Q := comm_mem_Q H hs.memM hq₀Q
  have hkK : ⁅q₀, x⁆ ∈ Kx Q X := centralizer_le_Kx hs
    ⟨hkQ, Subgroup.mem_centralizer_singleton_iff.mpr hq₀x.symm⟩
  have hdD : ⁅⁅q₀, x⁆, ℓ⁆ ∈ Q ⊓ QB X :=
    (smith_1_13_of_post12 hs h12).1 (Subgroup.commutator_mem_commutator hkK hℓ)
  have hφd := OrthEps.phi_pi_commutator C hℓQ hkQ hacto'
  rw [hq₀φ] at hφd
  have hφd' : C.φ (C.M₀.π ⁅⁅q₀, x⁆, ℓ⁆) = (w - o' w, 0) := by
    rw [hφd]
    refine Prod.ext ?_ ?_ <;> simp [orthTensor, Matrix.one_apply]
  have hwP : w - o' w ∈ OrthogonalInvolutions.commSpace o :=
    Submodule.sub_mem _ hd.pair.hw (ho'P w hd.pair.hw)
  obtain ⟨α, β, hαβ⟩ := hd.pair.hcoord _ hwP
  have ho'w : o' w = (-α) • a + (1 - β) • w := by
    have : o' w = w - (α • a + β • w) := by rw [← hαβ]; abel
    rw [this]; module
  have hβ : β = 0 := by
    have h1 : C.qU w = (1 - β) ^ 2 * C.qU w := by
      conv_lhs => rw [← hiso w, ho'w]
      rw [hd.pair.map_coord]
    have h2 : (1 - β) ^ 2 = 1 := by
      have h3 : ((1 - β) ^ 2 - 1) * C.qU w = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hd.hqw)
    have h4 : β ^ 2 = 0 := by
      have h2' : (2 : C.K) = 0 := CharTwo.two_eq_zero
      linear_combination h2 + β * h2'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h4
  have hα : α = 0 := by
    have hφ0 : C.φ (C.M₀.π ⁅⁅q₀, x⁆, ℓ⁆) = (α • a, (0 : C.K) • a) := by
      rw [hφd', hαβ, hβ]
      simp
    exact (hneg _ hdD _ _ hφ0).1
  have ho'w' : o' w = w := by
    rw [ho'w, hα, hβ]
    simp
  exact ⟨o', hacto', hiso, ho'a, ho'w'⟩

theorem card_Lx_le (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hsim : OrthSim C)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o)
    (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup C.qU) (hoo : o * o = 1)
    {a w b c : C.ι → C.K} (hd : FourData C.qU o a w b c)
    (hneg : ∀ d ∈ Q ⊓ QB X, ∀ α β : C.K, C.φ (C.M₀.π d) = (α • a, β • a) → α = 0 ∧ β = 0) :
    Nat.card ↥(Lx M X) ≤ Nat.card ↥(Q ⊓ QB X) * (2 * Nat.card C.K) := by
  classical
  have h12 := smith_1_12 hs
  haveI : Fintype C.K := Fintype.ofFinite C.K
  haveI : Fintype ↥(Lx M X) := Fintype.ofFinite _
  have hLx : ∀ ℓ : ↥(Lx M X), ∃ o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K),
      ActsAsTensor Q Z C.M₀ C.φ (ℓ : G) 1 ⇑o' ∧ (∀ v, C.qU (o' v) = C.qU v) ∧ o' a = a ∧
        o' w = w := fun ℓ => Lx_action hc C hsim hs hact hO hoo hd hneg ℓ.2
  choose f hfact hfiso hfa hfw using hLx
  let Ψ : ↥(Lx M X) → C.K × C.K := fun ℓ =>
    (QuadraticMap.polar C.qU (f ℓ b - b) c, QuadraticMap.polar C.qU (f ℓ c - c) c)
  have hfib : ∀ t t' : ↥(Lx M X), Ψ t = Ψ t' → (t : G)⁻¹ * t' ∈ Q ⊓ QB X := by
    intro t t' htt
    have hP := Prod.ext_iff.mp htt
    have heq : f t = f t' := hd.pair.ext_of_polar (hfiso t) (hfa t) (hfw t) (hfiso t') (hfa t')
      (hfw t') hP.1 hP.2
    have hact' : ActsAsTensor Q Z C.M₀ C.φ (t' : G) 1 ⇑(f t) := by rw [heq]; exact hfact t'
    have hmem : (t : G)⁻¹ * t' ∈ Q := inv_mul_mem_Q_of_same_act hc.ctx C
      (Lx_le_H0 hs h12 t'.2).1 (Lx_le_H0 hs h12 t.2).1 (g := 1) (g' := 1) (mul_one 1)
      hact' (hfact t)
    exact ⟨hmem, (QB X).mul_mem ((QB X).inv_mem (Subgroup.mem_inf.mp t.2).1)
      (Subgroup.mem_inf.mp t'.2).1⟩
  have hcard := card_le_mul_card_image_of_fibre (P := Lx M X) (Q := Q ⊓ QB X) Ψ hfib
  have himg : (Finset.univ.image Ψ) ⊆
      (Finset.univ : Finset C.K) ×ˢ ({0, (C.qU w)⁻¹} : Finset C.K) := by
    intro r hr
    obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.mp hr
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨-, -, h3⟩ := hd.pair.constraints (hfiso ℓ) (hfa ℓ) (hfw ℓ)
    show QuadraticMap.polar C.qU (f ℓ c - c) c ∈ ({0, (C.qU w)⁻¹} : Finset C.K)
    set t := QuadraticMap.polar C.qU (f ℓ c - c) c
    have h4 : t * (C.qU w * t - 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · simp [h]
    · have : t = (C.qU w)⁻¹ := eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h)
      simp [this]
  have hcard2 : (Finset.univ.image Ψ).card ≤ 2 * Nat.card C.K := by
    refine (Finset.card_le_card himg).trans ?_
    rw [Finset.card_product, Finset.card_univ, ← Nat.card_eq_fintype_card, mul_comm]
    exact Nat.mul_le_mul_right _ Finset.card_le_two
  exact hcard.trans (Nat.mul_le_mul_left _ hcard2)

theorem card_D_le (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hact : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑o) {a w b c : C.ι → C.K}
    (hd : FourData C.qU o a w b c)
    (hneg : ∀ d ∈ Q ⊓ QB X, ∀ α β : C.K, C.φ (C.M₀.π d) = (α • a, β • a) → α = 0 ∧ β = 0) :
    Nat.card ↥(Q ⊓ QB X) ≤ Nat.card C.K * Nat.card C.K := by
  classical
  have h12 := smith_1_12 hs
  have hDx := (smith_1_13_of_post12 hs h12).2.2.2.1
  have hmemP : ∀ d ∈ Q ⊓ QB X, (C.φ (C.M₀.π d)).1 ∈ OrthogonalInvolutions.commSpace o ∧
      (C.φ (C.M₀.π d)).2 ∈ OrthogonalInvolutions.commSpace o := fun d hd' =>
    phi_pi_mem_of_commute C hact hd.hfix (Subgroup.mem_inf.mp hd').1
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hDx hd')).2)
  let f : ↥(Q ⊓ QB X) → C.K × C.K := fun d =>
    (QuadraticMap.polar C.qU (C.φ (C.M₀.π d)).1 c, QuadraticMap.polar C.qU (C.φ (C.M₀.π d)).2 c)
  have hinj : Function.Injective f := by
    intro d d' hdd
    have hP := Prod.ext_iff.mp hdd
    set e : G := (d : G) * (d' : G)⁻¹ with he
    have heD : e ∈ Q ⊓ QB X := (Q ⊓ QB X).mul_mem d.2 ((Q ⊓ QB X).inv_mem d'.2)
    have heQ : e ∈ Q := (Subgroup.mem_inf.mp heD).1
    have hπ : C.φ (C.M₀.π e) = C.φ (C.M₀.π d) - C.φ (C.M₀.π d') := by
      rw [he, C.M₀.π_mul _ (Subgroup.mem_inf.mp d.2).1 _ (Q.inv_mem (Subgroup.mem_inf.mp d'.2).1),
        Tim79.QuadModel.pi_inv C.M₀ (Subgroup.mem_inf.mp d'.2).1, map_add, map_neg, sub_eq_add_neg]
    obtain ⟨he1, he2⟩ := hmemP e heD
    have hc1 : QuadraticMap.polar C.qU (C.φ (C.M₀.π e)).1 c = 0 := by
      rw [hπ, Prod.fst_sub, QuadraticMap.polar_sub_left]
      exact sub_eq_zero.mpr hP.1
    have hc2 : QuadraticMap.polar C.qU (C.φ (C.M₀.π e)).2 c = 0 := by
      rw [hπ, Prod.snd_sub, QuadraticMap.polar_sub_left]
      exact sub_eq_zero.mpr hP.2
    have hφe : C.φ (C.M₀.π e) =
        (QuadraticMap.polar C.qU (C.φ (C.M₀.π e)).1 (b) • a,
          QuadraticMap.polar C.qU (C.φ (C.M₀.π e)).2 b • a) := by
      refine Prod.ext ?_ ?_
      · conv_lhs => rw [hd.pair.eq_coord he1]
        simp [hc1]
      · conv_lhs => rw [hd.pair.eq_coord he2]
        simp [hc2]
    obtain ⟨h1, h2⟩ := hneg e heD _ _ hφe
    have hφ0 : C.φ (C.M₀.π e) = 0 := by rw [hφe, h1, h2]; simp
    have hπ0 : C.M₀.π e = 0 := by simpa using hφ0
    have heZ : e ∈ Z := (C.M₀.π_ker e heQ).mp hπ0
    have : e ∈ Z ⊓ QB X := ⟨heZ, (Subgroup.mem_inf.mp heD).2⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at this
    exact Subtype.ext (mul_inv_eq_one.mp this)
  calc Nat.card ↥(Q ⊓ QB X) ≤ Nat.card (C.K × C.K) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card C.K * Nat.card C.K := Nat.card_prod _ _

end Group

end OrthEps

theorem orthEpsFourMinus_holds : OrthEpsFourMinusStatement := by
  intro G _ _ M Q Z B hc C hNoTSP X x hs hxL o hact hiso hoo heven
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hO := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hoo' : o * o = 1 := LinearEquiv.ext fun v => hoo v
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  obtain ⟨u, hu0, hqu⟩ := exists_singular_of_ctx hc.ctx C
  have hcard : Fintype.card C.ι = 4 := by
    by_contra hne
    have h4 := four_le_card_of_cfg hc C
    obtain ⟨s, t, hs0, ht0, hst, hind⟩ :=
      OrthEps.exists_plane_of_five_le C.qU (by omega) ⟨u, hu0, hqu⟩
    exact hNoTSP s t hs0 ht0 hst hind
  have hdim : Module.finrank C.K (C.ι → C.K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  have ho1 : o ≠ 1 := by
    intro h1
    refine hs.notQ (mem_Q_of_pi_conj_eq (M₀ := C.M₀) H hs.memM fun y hy => ?_)
    apply C.φ.injective
    rw [hact y hy, h1]
    simp [orthTensor, Matrix.one_apply]
  obtain ⟨a, w, ha0, hqa, haP, hwP, haw, hqw, hind, hcoord, hsing, hperp, hfix⟩ :=
    OrthEps.four_minus_P hnd hO hoo' hdim heven ho1 hNoTSP
  obtain ⟨b, c, hab, hwb, hac, hwc⟩ := OrthEps.exists_dual_pair hnd hind
  have hd : OrthEps.FourData C.qU o a w b c :=
    ⟨⟨haP, hwP, hqa, haw, hcoord, hperp,
      fun p hp p' hp' => OrthogonalInvolutions.polar_commSpace_eq_zero hO hoo' hp hp',
      hab, hwb, hac, hwc⟩, ha0, hqw, hsing, hfix⟩
  by_cases hneg : ∀ d ∈ Q ⊓ QB X, ∀ α β : C.K, C.φ (C.M₀.π d) = (α • a, β • a) → α = 0 ∧ β = 0
  · exfalso
    have hsim := orthSim_of_dim hc C (Or.inr hNoTSP)
    have hL := OrthEps.card_Lx_le hc C hsim hs hact hO hoo' hd hneg
    have hD := OrthEps.card_D_le hc C hs hact hd hneg
    have hw4 : Width Q Z 4 := by
      have := width_of_tensor C.hD C.φ
      rwa [hcard] at this
    have hLge := Sit.card_Lx_ge hs hw4
    have hq : Nat.card C.K = Nat.card Z := C.hD.card
    have hq4 : 4 ≤ Nat.card Z := H.q4
    rw [← hq] at hLge hq4
    set q := Nat.card C.K
    have h1 : q ^ 4 ≤ q * q * (2 * q) := hLge.trans (hL.trans (Nat.mul_le_mul_right _ hD))
    have h2 : 0 < q ^ 3 := by positivity
    nlinarith
  · push Not at hneg
    obtain ⟨d, hdD, α, β, hφ, hαβ'⟩ := hneg
    have hαβ : α ≠ 0 ∨ β ≠ 0 := by
      by_cases h : α = 0
      · exact Or.inr (hαβ' h)
      · exact Or.inl h
    have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hdD).1
    have hDx := (smith_1_13_of_post12 hs h12).2.2.2.1
    obtain ⟨hP1, hP2⟩ := OrthEps.phi_pi_mem_of_commute C hact hfix hdQ
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hDx hdD)).2)
    have hJ : d ∈ ⁅Q, Subgroup.zpowers x⁆ :=
      OrthEps.mem_commutator_of_phi_mem hc C hs hact hO hoo' ho1 hdQ hP1 hP2
    have hφne : C.φ (C.M₀.π d) ≠ 0 := by
      rw [hφ]
      intro h0
      rw [Prod.mk_eq_zero] at h0
      rcases hαβ with h | h
      · exact h ((smul_eq_zero.mp h0.1).resolve_right ha0)
      · exact h ((smul_eq_zero.mp h0.2).resolve_right ha0)
    have hdZ : d ∉ Z := fun h => hφne (by rw [(C.M₀.π_ker d hdQ).mpr h, map_zero])
    obtain ⟨z₀, hz₀, hz₀1, hz₀x⟩ := OrthEps.exists_root_z₀ hs
    have hconj : IsConj z₀ d := (C.hF.root z₀ hz₀ hz₀1 d hdQ hdZ).mpr
      ⟨α, β, a, hαβ, ha0, hqa, hφ⟩
    refine ⟨d, ⟨hJ, (Subgroup.mem_inf.mp hdD).2⟩, ?_, hz₀x.symm.trans hconj⟩
    intro h1
    apply hφne
    rw [h1, C.M₀.pi_one, map_zero]

theorem orthEps_holds (h24 : Smith24ActStatement)
    (h52 : Smith52ActStatement) (hT : OrthTacitStatement) : OrthEpsStatement :=
  orthEps_of h24 h52 hT orthEpsFourMinus_holds

theorem orthEps_of_25 (h24 : Smith24ActStatement)
    (h25 : Smith25OrthStatement) (hT : OrthTacitStatement) : OrthEpsStatement :=
  orthEps_holds h24 (smith52Act_of h25 hT) hT

end CFSG.RankThree.GF2n.Smith81
