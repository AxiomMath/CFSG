module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem orderOf_card_dvd_finrank_range {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {g : V ≃ₗ[K] V} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hg : orderOf g = p) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ∣
      Module.finrank K (LinearMap.range ((g : V →ₗ[K] V) - 1)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite V := Module.finite_of_finite K
  have hq0 : ((Nat.card K : ℕ) : ZMod p) ≠ 0 := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    push_cast
    refine pow_ne_zero _ fun h2 => hp2 ?_
    have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3
  have hH : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hg])
  have hmod := hH.card_modEq_card_fixedPoints V
  have hfix : MulAction.fixedPoints (Subgroup.zpowers g) V =
      (LinearMap.ker ((g : V →ₗ[K] V) - 1) : Set V) := by
    ext v
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h m
      have hs : g ∈ MulAction.stabilizer (V ≃ₗ[K] V) v := h
      exact (Subgroup.zpowers_le.mpr hs) m.2
  have hcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) V) =
      Nat.card K ^ Module.finrank K (LinearMap.ker ((g : V →ₗ[K] V) - 1)) := by
    rw [hfix]
    exact Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker ((g : V →ₗ[K] V) - 1))
  rw [hcard, Module.natCard_eq_pow_finrank (K := K) (V := V)] at hmod
  have hrn := LinearMap.finrank_range_add_finrank_ker ((g : V →ₗ[K] V) - 1)
  rw [← hrn] at hmod
  have hz := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod.symm
  push_cast at hz
  rw [pow_add, mul_comm] at hz
  have h1 : ((Nat.card K : ℕ) : ZMod p) ^ Module.finrank K (LinearMap.range ((g : V →ₗ[K] V) - 1))
      = 1 := by
    have hne : ((Nat.card K : ℕ) : ZMod p) ^
        Module.finrank K (LinearMap.ker ((g : V →ₗ[K] V) - 1)) ≠ 0 := pow_ne_zero _ hq0
    exact (mul_eq_left₀ hne).mp hz.symm
  exact orderOf_dvd_of_pow_eq_one h1

theorem finrank_range_sub_one_pos {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : V ≃ₗ[K] V} (hne : g ≠ 1) :
    0 < Module.finrank K (LinearMap.range ((g : V →ₗ[K] V) - 1)) := by
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot, sub_eq_zero]
  intro h
  refine hne (LinearEquiv.ext fun v => ?_)
  simpa using LinearMap.congr_fun h v

theorem orderOf_card_le_finrank {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {g : V ≃ₗ[K] V} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hg : orderOf g = p) :
    orderOf ((Nat.card K : ℕ) : ZMod p) ≤ Module.finrank K V := by
  have hne : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hp.one_lt.ne hg
  exact (Nat.le_of_dvd (finrank_range_sub_one_pos hne)
    (orderOf_card_dvd_finrank_range hp hp2 hg)).trans (Submodule.finrank_le _)

theorem even_finrank_of_alt_nondegenerate {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank K V) := by
  classical
  let P : ℕ → Prop := fun n => ∃ U : Submodule K V, U ≤ B.orthogonal U ∧ Module.finrank K U = n
  have hP0 : P 0 := ⟨⊥, bot_le, finrank_bot K V⟩
  obtain ⟨U, hUiso, hUm⟩ : P (Nat.findGreatest P (Module.finrank K V)) :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hmax : B.orthogonal U ≤ U := by
    intro x hx
    by_contra hxU
    have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
    have hiso : U ⊔ Submodule.span K {x} ≤ B.orthogonal (U ⊔ Submodule.span K {x}) := by
      intro a ha
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro b hb
      obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨u', hu', s', hs', rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hs'
      have h1 : B u' u = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp (hUiso hu)) u' hu'
      have h2 : B u' x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u' hu'
      have h3 : B x u = 0 := (hB.eq_iff).mp
        ((LinearMap.BilinForm.mem_orthogonal_iff.mp hx) u hu)
      have h4 : B x x = 0 := hB x
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h1, h2, h3, h4,
        smul_zero, add_zero]
    have hdim : Module.finrank K ↥(U ⊔ Submodule.span K {x}) =
        Nat.findGreatest P (Module.finrank K V) + 1 := by
      have hinf : U ⊓ Submodule.span K {x} = ⊥ :=
        disjoint_iff.mp ((Submodule.disjoint_span_singleton' hx0).mpr hxU)
      have := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span K {x})
      rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0, hUm] at this
      exact this
    have hle := Nat.le_findGreatest (P := P)
      (hdim ▸ Submodule.finrank_le (U ⊔ Submodule.span K {x})) ⟨_, hiso, hdim⟩
    omega
  have heq : B.orthogonal U = U := le_antisymm hmax hUiso
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [heq] at hdim
  have hle := Submodule.finrank_le U
  exact ⟨Module.finrank K U, by omega⟩

theorem two_mul_orderOf_le_finrank_of_isometry {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {g : V ≃ₗ[K] V} (hiso : ∀ x y, B (g x) (g y) = B x y)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : orderOf g = p) (hne : g ≠ 1)
    (hodd : Odd (orderOf ((Nat.card K : ℕ) : ZMod p))) :
    2 * orderOf ((Nat.card K : ℕ) : ZMod p) ≤ Module.finrank K V := by
  have hTp : (g : V →ₗ[K] V) ^ p = 1 := by
    have h1 : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
    refine LinearMap.ext fun v => ?_
    have h2 := LinearEquiv.pow_apply g p v
    rw [h1] at h2
    exact (Module.End.pow_apply _ p v).trans h2.symm
  have hsup := ker_sup_range_eq_top_of_pow_eq_one (hp.odd_of_ne_two hp2) hTp
  have hCW : ∀ c ∈ LinearMap.ker ((g : V →ₗ[K] V) - 1),
      ∀ w ∈ LinearMap.range ((g : V →ₗ[K] V) - 1), B c w = 0 := by
    intro c hc w hw
    obtain ⟨x, rfl⟩ := hw
    have hgc : g c = c := by
      simpa [sub_eq_zero] using LinearMap.mem_ker.mp hc
    have h1 := hiso c x
    rw [hgc] at h1
    simp [h1]
  have hleft : (B.restrict (LinearMap.range ((g : V →ₗ[K] V) - 1))).SeparatingLeft := by
    intro w hw
    have hall : ∀ y : V, B w y = 0 := by
      intro y
      have hy : y ∈ LinearMap.ker ((g : V →ₗ[K] V) - 1) ⊔
          LinearMap.range ((g : V →ₗ[K] V) - 1) := hsup ▸ Submodule.mem_top
      obtain ⟨c, hc, w', hw', rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, hB.eq_iff.mp (hCW c hc w w.2), zero_add]
      simpa using hw ⟨w', hw'⟩
    exact Subtype.ext (hnd.1 w hall)
  have hndW : (B.restrict (LinearMap.range ((g : V →ₗ[K] V) - 1))).Nondegenerate := by
    refine ⟨hleft, fun w hw => hleft w fun y => ?_⟩
    simpa using hB.eq_iff.mp (hw y)
  have hev : 2 ∣ Module.finrank K (LinearMap.range ((g : V →ₗ[K] V) - 1)) :=
    even_iff_two_dvd.mp (even_finrank_of_alt_nondegenerate _ (fun x => hB x) hndW)
  have hdvd := orderOf_card_dvd_finrank_range hp hp2 hg
  have hmul : 2 * orderOf ((Nat.card K : ℕ) : ZMod p) ∣
      Module.finrank K (LinearMap.range ((g : V →ₗ[K] V) - 1)) :=
    (Nat.coprime_two_left.mpr hodd).mul_dvd_of_dvd_of_dvd hev hdvd
  exact (Nat.le_of_dvd (finrank_range_sub_one_pos hne) hmul).trans (Submodule.finrank_le _)

theorem orderOf_two_zmod_eq_of_primitive {e p : ℕ} (hp : p.Prime) (he : 0 < e)
    (hdvd : p ∣ 2 ^ e - 1) (hprim : ∀ k : ℕ, 0 < k → k < e → ¬ p ∣ 2 ^ k - 1) :
    orderOf (2 : ZMod p) = e := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ k : ℕ, p ∣ 2 ^ k - 1 ↔ (2 : ZMod p) ^ k = 1 := fun k => by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    exact sub_eq_zero
  have h1 : (2 : ZMod p) ^ e = 1 := (hpow e).mp hdvd
  have hpos : 0 < orderOf (2 : ZMod p) :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨e, he, h1⟩)
  have hle : orderOf (2 : ZMod p) ≤ e := Nat.le_of_dvd he (orderOf_dvd_of_pow_eq_one h1)
  by_contra hne
  exact hprim _ hpos (lt_of_le_of_ne hle hne) ((hpow _).mpr (pow_orderOf_eq_one _))

theorem exists_prime_orderOf_two_eq {e : ℕ} (he : 2 ≤ e) (he6 : e ≠ 6) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf (2 : ZMod p) = e := by
  obtain ⟨p, hp, hdvd, hprim⟩ := CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one e he he6
  have h := orderOf_two_zmod_eq_of_primitive hp (by omega) hdvd hprim
  refine ⟨p, hp, ?_, h⟩
  rintro rfl
  have h0 : (2 : ZMod 2) = 0 := rfl
  rw [h0, orderOf_zero] at h
  omega

theorem orderOf_ne_prime_of_finrank_lt {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : Module.finrank (ZMod 2) V < orderOf (2 : ZMod p)) (g : V ≃ₗ[ZMod 2] V) :
    orderOf g ≠ p := by
  intro hg
  have h := orderOf_card_le_finrank (K := ZMod 2) (V := V) hp hp2 hg
  rw [Nat.card_zmod] at h
  exact absurd hlt (not_lt.mpr h)

end CFSG.RankThree.GF2n.Stroth80
