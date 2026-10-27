module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

section Act

variable {G : Type} [Group G] (T N : Subgroup G)

theorem actQ_aux (hN : (N.subgroupOf T).Normal) {x : G} (hx : x ∈ Subgroup.normalizer (T : Set G))
    (hc : ∀ n ∈ N, x * n = n * x) :
    (N.subgroupOf T).map ((T.normalizerMonoidHom ⟨x, hx⟩ : MulAut T) : T →* T) =
      N.subgroupOf T := by
  have key : ∀ y : T, y ∈ N.subgroupOf T →
      (T.normalizerMonoidHom ⟨x, hx⟩ : MulAut T) y = y := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    apply Subtype.ext
    show x * (y : G) * x⁻¹ = y
    rw [hc _ hy, mul_inv_cancel_right]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    show (T.normalizerMonoidHom ⟨x, hx⟩ : MulAut T) z ∈ N.subgroupOf T
    rw [key z hz]
    exact hz
  · intro hy
    exact ⟨y, hy, key y hy⟩

noncomputable def actQ (hN : (N.subgroupOf T).Normal) {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) (hc : ∀ n ∈ N, x * n = n * x) :
    MulAut (T ⧸ N.subgroupOf T) :=
  haveI := hN
  QuotientGroup.congr (N.subgroupOf T) (N.subgroupOf T) (T.normalizerMonoidHom ⟨x, hx⟩)
    (actQ_aux T N hN hx hc)

theorem actQ_mk (hN : (N.subgroupOf T).Normal) {x : G}
    (hx : x ∈ Subgroup.normalizer (T : Set G)) (hc : ∀ n ∈ N, x * n = n * x) (u : T) :
    actQ T N hN hx hc (QuotientGroup.mk u) =
      QuotientGroup.mk ((T.normalizerMonoidHom ⟨x, hx⟩ : MulAut T) u) := by
  haveI := hN
  unfold actQ
  exact QuotientGroup.congr_mk _ _ _ _ _

noncomputable def actHom (hN : (N.subgroupOf T).Normal) (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (T : Set G)) (hc : ∀ x ∈ X, ∀ n ∈ N, x * n = n * x) :
    ↥X →* MulAut (T ⧸ N.subgroupOf T) where
  toFun x := actQ T N hN (hX x.2) (hc x x.2)
  map_one' := by
    haveI := hN
    apply MulEquiv.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | H u =>
      rw [actQ_mk]
      apply congrArg
      apply Subtype.ext
      simp
  map_mul' := by
    haveI := hN
    intro x y
    apply MulEquiv.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | H u =>
      show actQ T N hN (hX (x * y).2) (hc _ (x * y).2) _ = (actQ T N hN (hX x.2) (hc _ x.2) *
        actQ T N hN (hX y.2) (hc _ y.2)) _
      rw [MulAut.mul_apply, actQ_mk, actQ_mk, actQ_mk]
      apply congrArg
      apply Subtype.ext
      simp [mul_assoc]

theorem actHom_mk (hN : (N.subgroupOf T).Normal) (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (T : Set G)) (hc : ∀ x ∈ X, ∀ n ∈ N, x * n = n * x)
    (x : X) (u : T) :
    actHom T N hN X hX hc x (QuotientGroup.mk u) =
      QuotientGroup.mk (⟨(x : G) * u * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hX x.2) _).1 u.2⟩ : T) := by
  show actQ T N hN (hX x.2) (hc x x.2) _ = _
  rw [actQ_mk]
  rfl

theorem actHom_eq_one_iff (hN : (N.subgroupOf T).Normal) (X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (T : Set G)) (hc : ∀ x ∈ X, ∀ n ∈ N, x * n = n * x)
    (x : X) :
    actHom T N hN X hX hc x = 1 ↔ ∀ u ∈ T, ∃ n ∈ N, (x : G) * u * (x : G)⁻¹ = u * n := by
  haveI := hN
  constructor
  · intro h u hu
    have h1 := actHom_mk T N hN X hX hc x ⟨u, hu⟩
    rw [h] at h1
    have h2 : (QuotientGroup.mk (⟨u, hu⟩ : T) : T ⧸ N.subgroupOf T) =
        QuotientGroup.mk ⟨(x : G) * u * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hX x.2) _).1 hu⟩ :=
      h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    refine ⟨u⁻¹ * ((x : G) * u * (x : G)⁻¹), h2, ?_⟩
    group
  · intro h
    apply MulEquiv.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | H u =>
      rw [actHom_mk]
      show _ = QuotientGroup.mk u
      symm
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      obtain ⟨n, hn, hxn⟩ := h u.1 u.2
      show (u : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ N
      rw [hxn, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hn

end Act

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
