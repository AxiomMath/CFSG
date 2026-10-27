module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

section Group

variable {M : Type*} [Group M] {x y z : M}

theorem mul_pow_eq_of_mul_eq (hzy : Commute z y) (h : x * y = z * (y * x)) (n : ℕ) :
    x * y ^ n = z ^ n * (y ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * y ^ (n + 1) = (x * y ^ n) * y := by rw [pow_succ, mul_assoc]
      _ = z ^ n * y ^ n * (x * y) := by rw [ih]; group
      _ = z ^ n * y ^ n * (z * (y * x)) := by rw [h]
      _ = z ^ n * (y ^ n * z) * y * x := by group
      _ = z ^ n * (z * y ^ n) * y * x := by rw [(hzy.pow_right n).eq.symm]
      _ = z ^ (n + 1) * (y ^ (n + 1) * x) := by rw [pow_succ, pow_succ]; group

theorem pow_mul_pow_of_mul_eq (hzx : Commute z x) (hzy : Commute z y) (h : x * y = z * (y * x))
    (n : ℕ) : x ^ n * y ^ n = z ^ (n.choose 2) * (x * y) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := mul_pow_eq_of_mul_eq hzy h n
    calc x ^ (n + 1) * y ^ (n + 1) = x ^ n * (x * y ^ n) * y := by
          rw [pow_succ', pow_succ]; group
      _ = x ^ n * (z ^ n * (y ^ n * x)) * y := by rw [h1]
      _ = z ^ n * (x ^ n * y ^ n) * (x * y) := by
          rw [← mul_assoc (x ^ n), ((hzx.pow_pow n n).eq.symm : x ^ n * z ^ n = z ^ n * x ^ n)]
          group
      _ = z ^ n * (z ^ (n.choose 2) * (x * y) ^ n) * (x * y) := by rw [ih]
      _ = z ^ (n + 1).choose 2 * (x * y) ^ (n + 1) := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add, pow_succ]
          simp only [mul_assoc]

theorem mul_pow_eq_of_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzx : Commute z x)
    (hzy : Commute z y) (h : x * y = z * (y * x)) (hz : z ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hdvd : p ∣ p.choose 2 := by
    rw [Nat.choose_two_right]
    obtain ⟨k, hk⟩ : 2 ∣ p - 1 := by
      rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩
      · exact absurd h2 hp2
      · exact ⟨k, by omega⟩
    rw [hk, show p * (2 * k) = 2 * (p * k) by ring, Nat.mul_div_cancel_left _ two_pos]
    exact dvd_mul_right p k
  obtain ⟨k, hk⟩ := hdvd
  rw [pow_mul_pow_of_mul_eq hzx hzy h, hk, pow_mul, hz, one_pow, one_mul]

end Group

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

structure IsProjElem (p : ℕ) (G : Subgroup (GL ι K)) : Prop where
  scalar_mem : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G
  pow_scalar : ∀ g ∈ G, ∃ u : Kˣ, g ^ p = GeneralLinearGroup.scalar ι u
  comm_scalar : ∀ g ∈ G, ∀ h ∈ G, ∃ u : Kˣ, g * h = GeneralLinearGroup.scalar ι u * (h * g)

theorem isProjElem_comap_map_subtype
    {H : Type*} [Group H] {N : Subgroup (GL ι K)}
    (hNscal : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ N)
    {ρ : N →* H}
    (hρscal : ∀ u : Kˣ, ρ ⟨GeneralLinearGroup.scalar ι u, hNscal u⟩ = 1)
    (hker : ∀ x : N, ρ x = 1 → ∃ u : Kˣ,
      (x : GL ι K) = GeneralLinearGroup.scalar ι u)
    {X : Subgroup H} (hX : CFSG.Open.IsElemAbelian p X) :
    IsProjElem p ((X.comap ρ).map N.subtype) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    let x : X.comap ρ := ⟨⟨GeneralLinearGroup.scalar ι u, hNscal u⟩, by
      rw [Subgroup.mem_comap, hρscal u]
      exact X.one_mem⟩
    exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    have hxX : ρ x ∈ X := Subgroup.mem_comap.mp hx
    have hxp : ρ (x ^ p) = 1 := by
      rw [map_pow]
      exact hX.2 (ρ x) hxX
    obtain ⟨u, hu⟩ := hker (x ^ p) hxp
    refine ⟨u, ?_⟩
    simpa using hu
  · intro g hg h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    have hxX : ρ x ∈ X := Subgroup.mem_comap.mp hx
    have hyX : ρ y ∈ X := Subgroup.mem_comap.mp hy
    have h1 : ρ (x * y * (y * x)⁻¹) = 1 := by
      have hcomm := hX.1.is_comm.comm ⟨ρ x, hxX⟩ ⟨ρ y, hyX⟩
      have hcomm' : ρ x * ρ y = ρ y * ρ x := congrArg Subtype.val hcomm
      rw [map_mul, map_inv, map_mul, map_mul, hcomm', mul_inv_cancel]
    obtain ⟨u, hu⟩ := hker (x * y * (y * x)⁻¹) h1
    refine ⟨u, ?_⟩
    have hu' : N.subtype x * N.subtype y * (N.subtype y * N.subtype x)⁻¹ =
        GeneralLinearGroup.scalar ι u := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hu
    rw [← hu']
    group

@[expose] def IsToral (G : Subgroup (GL ι K)) : Prop :=
  ∃ A : GL ι K, ∀ g ∈ G, ∀ i j, i ≠ j →
    ((A : Matrix ι ι K) * (g : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) i j = 0

theorem scalar_mul_comm (u : Kˣ) (A : GL ι K) :
    GeneralLinearGroup.scalar ι u * A = A * GeneralLinearGroup.scalar ι u := by
  ext : 1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem commute_scalar (u : Kˣ) (A : GL ι K) : Commute (GeneralLinearGroup.scalar ι u) A :=
  scalar_mul_comm u A

theorem scalar_injective [Nonempty ι] :
    Function.Injective (GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro u v huv
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) huv
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h1
  exact Units.ext h1

theorem eq_of_scalar_mul_eq [Nonempty ι] {u v : Kˣ} {x : GL ι K}
    (h : GeneralLinearGroup.scalar ι u * x = GeneralLinearGroup.scalar ι v * x) : u = v :=
  scalar_injective (mul_right_cancel h)

theorem IsProjElem.map_conj {G : Subgroup (GL ι K)} (hG : IsProjElem p G) (A : GL ι K) :
    IsProjElem p (G.map (MulAut.conj A).toMonoidHom) := by
  have hc : ∀ u : Kˣ, (MulAut.conj A) (GeneralLinearGroup.scalar ι u) =
      GeneralLinearGroup.scalar ι u := fun u => by
    rw [MulAut.conj_apply, ← scalar_mul_comm u A, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨fun u => ⟨_, hG.scalar_mem u, hc u⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := hG.pow_scalar x hx
    refine ⟨u, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hu, hc]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu⟩ := hG.comm_scalar x hx y hy
    refine ⟨u, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hu, map_mul, hc, map_mul]

theorem card_map_conj (G : Subgroup (GL ι K)) (A : GL ι K) :
    Nat.card (G.map (MulAut.conj A).toMonoidHom) = Nat.card G :=
  Subgroup.card_map_of_injective (MulEquiv.injective _)

end Setting

section Chars

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}
  {G : Subgroup (GL ι K)}

noncomputable def commCharFun (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) (x : G) : Kˣ :=
  Classical.choose (hG.comm_scalar a ha x x.2)

theorem commCharFun_spec (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) (x : G) :
    a * x = GeneralLinearGroup.scalar ι (commCharFun hG ha x) * (x * a) :=
  Classical.choose_spec (hG.comm_scalar a ha x x.2)

variable [Nonempty ι]

theorem commCharFun_eq (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) {x : G} {u : Kˣ}
    (h : a * x = GeneralLinearGroup.scalar ι u * (x * a)) : commCharFun hG ha x = u :=
  eq_of_scalar_mul_eq ((commCharFun_spec hG ha x).symm.trans h)

noncomputable def commChar (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) : G →* Kˣ where
  toFun := commCharFun hG ha
  map_one' := commCharFun_eq hG ha (by simp)
  map_mul' x y := by
    apply commCharFun_eq hG ha
    have hx := commCharFun_spec hG ha x
    have hy := commCharFun_spec hG ha y
    have hxc := scalar_mul_comm (commCharFun hG ha y) (x : GL ι K)
    calc a * ((x * y : G) : GL ι K) = (a * x) * y := by rw [Subgroup.coe_mul, mul_assoc]
      _ = GeneralLinearGroup.scalar ι (commCharFun hG ha x) * (x * (a * y)) := by
          rw [hx]; simp only [mul_assoc]
      _ = GeneralLinearGroup.scalar ι (commCharFun hG ha x) *
          ((x * GeneralLinearGroup.scalar ι (commCharFun hG ha y)) * (y * a)) := by
          rw [hy]; simp only [mul_assoc]
      _ = _ := by rw [← hxc, map_mul, Subgroup.coe_mul]; simp only [mul_assoc]

theorem commChar_spec (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) (x : G) :
    a * x = GeneralLinearGroup.scalar ι (commChar hG ha x) * (x * a) :=
  commCharFun_spec hG ha x

theorem commChar_eq (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) {x : G} {u : Kˣ}
    (h : a * x = GeneralLinearGroup.scalar ι u * (x * a)) : commChar hG ha x = u :=
  commCharFun_eq hG ha h

theorem commChar_eq_one_iff (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) (x : G) :
    commChar hG ha x = 1 ↔ a * x = x * a := by
  constructor
  · intro h
    have := commChar_spec hG ha x
    rwa [h, map_one, one_mul] at this
  · intro h
    exact commChar_eq hG ha (by rw [h, map_one, one_mul])

theorem commChar_pow_eq_one (hG : IsProjElem p G) {a : GL ι K} (ha : a ∈ G) (x : G) :
    commChar hG ha x ^ p = 1 := by
  rw [← map_pow, commChar_eq_one_iff]
  obtain ⟨v, hv⟩ := hG.pow_scalar x x.2
  rw [Subgroup.coe_pow, hv, scalar_mul_comm]

omit [Nonempty ι] in
noncomputable def lamFun (hG : IsProjElem p G) (x : G) : Kˣ :=
  Classical.choose (hG.pow_scalar x x.2)

omit [Nonempty ι] in
theorem lamFun_spec (hG : IsProjElem p G) (x : G) :
    (x : GL ι K) ^ p = GeneralLinearGroup.scalar ι (lamFun hG x) :=
  Classical.choose_spec (hG.pow_scalar x x.2)

noncomputable def lam (hp : p.Prime) (hp2 : p ≠ 2) (hG : IsProjElem p G) : G →* Kˣ where
  toFun := lamFun hG
  map_one' := scalar_injective (ι := ι) (by rw [← lamFun_spec, map_one, Subgroup.coe_one, one_pow])
  map_mul' x y := by
    apply scalar_injective (ι := ι)
    rw [← lamFun_spec, map_mul, ← lamFun_spec, ← lamFun_spec, Subgroup.coe_mul]
    have hz := commChar_pow_eq_one hG x.2 y
    refine mul_pow_eq_of_odd hp hp2 (commute_scalar _ _) (commute_scalar _ _)
      (commChar_spec hG x.2 y) ?_
    rw [← map_pow, hz, map_one]

theorem lam_spec (hp : p.Prime) (hp2 : p ≠ 2) (hG : IsProjElem p G) (x : G) :
    (x : GL ι K) ^ p = GeneralLinearGroup.scalar ι (lam hp hp2 hG x) :=
  lamFun_spec hG x

end Chars

section PowQuot

variable (K : Type*) [Field K] (p : ℕ)

abbrev PowQuot : Type _ := Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range

variable {K p}

theorem powQuot_mk_eq_one_iff {u : Kˣ} :
    (QuotientGroup.mk u : PowQuot K p) = 1 ↔ ∃ c : Kˣ, c ^ p = u := by
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  rfl

theorem card_powQuot_le [Finite K] [NeZero p] : Nat.card (PowQuot K p) ≤ p := by
  set f : Kˣ →* Kˣ := powMonoidHom p with hf
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_ker_mul_card_range f
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have h3 : f.range.index = Nat.card f.ker := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1, mul_comm, h2]
  have h4 : f.ker ≤ rootsOfUnity p K := fun x hx => by
    rw [MonoidHom.mem_ker, hf, powMonoidHom_apply] at hx
    exact hx
  calc Nat.card (PowQuot K p) = f.range.index := rfl
    _ = Nat.card f.ker := h3
    _ ≤ Nat.card (rootsOfUnity p K) := Subgroup.card_le_of_le h4
    _ ≤ p := card_rootsOfUnity K p

end PowQuot

end CFSG.StandardType.TypeA.PGLTor
