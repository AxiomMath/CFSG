module

public import CFSG.RankThree.GF2n.Smith81.S81HOrthRank
public import CFSG.RankThree.GF2n.Smith81.S81HO12Defs
public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthGraph

open Module
open QuadraticMap (polar polar_comm polar_smul_left polar_smul_right polar_sub_left
  polar_sub_right polar_add_left polar_add_right polar_self)
open CFSG.RankThree.PartOne.StrongP

variable {k : Type} [Field k] [Finite k] [CharP k 2]

section Helpers

variable {V : Type} [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}

private theorem polar_self_zero (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_smul, CharTwo.add_self_eq_zero]

private theorem exists_polar_one (hQ : Q.polarBilin.Nondegenerate) {x : V} (hx : x ≠ 0) :
    ∃ y, polar Q x y = 1 := by
  by_contra h
  push Not at h
  refine hx (hQ.1 x fun y => ?_)
  show polar Q x y = 0
  by_contra hy
  refine h ((polar Q x y)⁻¹ • y) ?_
  rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]

private theorem exists_singular_polar_one (hQ : Q.polarBilin.Nondegenerate) {x : V} (hx : x ≠ 0)
    (hQx : Q x = 0) : ∃ y, Q y = 0 ∧ polar Q x y = 1 := by
  obtain ⟨y, hy⟩ := exists_polar_one hQ hx
  refine ⟨y - Q y • x, ?_, ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add (Q : V → k), QuadraticMap.map_smul, hQx,
      smul_zero, add_zero, polar_smul_right, polar_comm, hy, smul_eq_mul, mul_one, add_neg_cancel]
  · rw [polar_sub_right, polar_smul_right, polar_self_zero, smul_zero, sub_zero, hy]

private theorem polar_sum_left {ι : Type*} [Fintype ι] (a : ι → k) (x : ι → V) (y : V) :
    polar Q (∑ j, a j • x j) y = ∑ j, a j * polar Q (x j) y := by
  have h := map_sum (Q.polarBilin.flip y) (fun j => a j • x j) Finset.univ
  simp only [LinearMap.flip_apply, QuadraticMap.polarBilin_apply_apply, polar_smul_left,
    smul_eq_mul] at h
  exact h

private theorem polar_sum_right {ι : Type*} [Fintype ι] (a : ι → k) (x : ι → V) (y : V) :
    polar Q y (∑ j, a j • x j) = ∑ j, a j * polar Q y (x j) := by
  have h := map_sum (Q.polarBilin y) (fun j => a j • x j) Finset.univ
  simp only [QuadraticMap.polarBilin_apply_apply, polar_smul_right, smul_eq_mul] at h
  exact h

private theorem exists_fixed_ne_zero [FiniteDimensional k V] (hV : 0 < finrank k V)
    {G : Type*} [Group G] (hG : IsPGroup 2 G) (ρ : Representation k G V) :
    ∃ u : V, u ≠ 0 ∧ ∀ g, ρ g u = u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite k
  have : Fintype k := Fintype.ofFinite k
  letI : MulAction G V :=
    { smul := fun g u => ρ g u
      one_smul := fun u => by show ρ 1 u = u; simp
      mul_smul := fun g h u => by show ρ (g * h) u = ρ g (ρ h u); simp }
  have h0 : (0 : V) ∈ MulAction.fixedPoints G V := fun g => map_zero (ρ g)
  have hk : 2 ∣ Nat.card k := by
    rw [Nat.card_eq_fintype_card]
    exact (CharP.cast_eq_zero_iff k 2 _).mp (FiniteField.cast_card_eq_zero k)
  have hdvd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := k)]
    exact hk.trans (dvd_pow_self _ hV.ne')
  obtain ⟨u, hu, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd h0
  exact ⟨u, fun h => hne h.symm, fun g => hu g⟩

end Helpers

structure FlagData {V : Type} [AddCommGroup V] [Module k V] {G : Type*} [Group G]
    (Q : QuadraticForm k V) (ρ : Representation k G V) (n : ℕ) (v w : Fin n → V)
    (u u' : V) : Prop where
  Qv : ∀ i, Q (v i) = 0
  Qw : ∀ i, Q (w i) = 0
  vv : ∀ i j, polar Q (v i) (v j) = 0
  ww : ∀ i j, polar Q (w i) (w j) = 0
  vw : ∀ i j, polar Q (v i) (w j) = if i = j then 1 else 0
  vu : ∀ i, polar Q (v i) u = 0
  vu' : ∀ i, polar Q (v i) u' = 0
  wu : ∀ i, polar Q (w i) u = 0
  wu' : ∀ i, polar Q (w i) u' = 0
  uu' : polar Q u u' = 1
  fixv : ∀ g i, ∃ a : Fin n → k, (∀ j, i ≤ j → a j = 0) ∧ ρ g (v i) = v i + ∑ j, a j • v j
  fixu : ∀ g, ∃ a : Fin n → k, ρ g u = u + ∑ j, a j • v j
  fixu' : ∀ g, ∃ (c : k) (a : Fin n → k), ρ g u' = u' + c • u + ∑ j, a j • v j

theorem exists_flagData {G : Type*} [Group G] (hG : IsPGroup 2 G) (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      {Q : QuadraticForm k V}, Q.polarBilin.Nondegenerate → finrank k V = 2 * n + 2 →
      ∀ ρ : Representation k G V, (∀ g x, Q (ρ g x) = Q x) →
      ∃ (v w : Fin n → V) (u u' : V), FlagData Q ρ n v w u u' := by
  induction n with
  | zero =>
    intro V _ _ _ Q hQ hV ρ hiso
    have hsymm : ∀ x y, polar Q x y = polar Q y x := fun x y => polar_comm _ x y
    have hpiso : ∀ g x y, polar Q (ρ g x) (ρ g y) = polar Q x y := fun g x y => by
      simp only [polar, ← map_add, hiso]
    obtain ⟨u, hu0, hρu⟩ := exists_fixed_ne_zero (by omega) hG ρ
    obtain ⟨u', hu'⟩ := exists_polar_one hQ hu0
    have hinj : ∀ d, polar Q d u = 0 → polar Q d u' = 0 → d = 0 := by
      intro d h1 h2
      let Φ : V →ₗ[k] k × k := (Q.polarBilin.flip u).prod (Q.polarBilin.flip u')
      have hsurj : Function.Surjective Φ := fun p => ⟨p.1 • u' + p.2 • u, by
        ext <;> simp [Φ, polar_add_left, polar_smul_left, polar_self_zero, hu', hsymm u' u,
          CharTwo.two_eq_zero]⟩
      have hrk := LinearMap.finrank_range_add_finrank_ker Φ
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrk
      simp only [Module.finrank_prod, Module.finrank_self] at hrk
      have hker : LinearMap.ker Φ = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have hd : d ∈ LinearMap.ker Φ := by
        simp [Φ, Prod.ext_iff, h1, h2]
      rw [hker, Submodule.mem_bot] at hd
      exact hd
    refine ⟨Fin.elim0, Fin.elim0, u, u', ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, hu', fun _ i => i.elim0, fun g => ⟨Fin.elim0, by simp [hρu]⟩,
      fun g => ⟨polar Q (ρ g u') u', Fin.elim0, ?_⟩⟩⟩
    have hd := hinj (ρ g u' - u' - polar Q (ρ g u') u' • u)
      (by
        have h := hpiso g u' u
        rw [hρu] at h
        rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_self_zero, smul_zero,
          sub_zero, h, sub_self])
      (by rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_self_zero, hu',
          smul_eq_mul, mul_one, sub_zero, sub_self])
    simp only [Fin.sum_univ_zero, add_zero]
    rw [sub_sub, sub_eq_zero] at hd
    exact hd
  | succ n ih =>
    intro V _ _ _ Q hQ hV ρ hiso
    have hsymm : ∀ x y, polar Q x y = polar Q y x := fun x y => polar_comm _ x y
    have hpiso : ∀ g x y, polar Q (ρ g x) (ρ g y) = polar Q x y := fun g x y => by
      simp only [polar, ← map_add, hiso]
    obtain ⟨v₀, hv0, hQv, hρv⟩ := OrthRank.exists_fixed_singular (by omega) Q hG ρ hiso
    obtain ⟨c, hQc, hvc⟩ := exists_singular_polar_one hQ hv0 hQv
    have hcv : polar Q c v₀ = 1 := by rw [hsymm]; exact hvc
    have hpv : ∀ g x, polar Q (ρ g x) v₀ = polar Q x v₀ := fun g x => by
      calc polar Q (ρ g x) v₀ = polar Q (ρ g x) (ρ g v₀) := by rw [hρv]
        _ = polar Q x v₀ := hpiso g x v₀
    let Φ : V →ₗ[k] k × k := (Q.polarBilin.flip v₀).prod (Q.polarBilin c)
    let U := LinearMap.ker Φ
    have hmemU : ∀ x, x ∈ U ↔ polar Q x v₀ = 0 ∧ polar Q c x = 0 := fun x => by
      simp [U, Φ, Prod.ext_iff]
    have hUdim : finrank k U = 2 * n + 2 := by
      have hsurj : Function.Surjective Φ := fun p => ⟨p.1 • c + p.2 • v₀, by
        ext <;> simp [Φ, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
          polar_self_zero, hcv, hvc, CharTwo.two_eq_zero]⟩
      have h1 := LinearMap.finrank_range_add_finrank_ker Φ
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
      simp only [Module.finrank_prod, Module.finrank_self] at h1
      show finrank k (LinearMap.ker Φ) = 2 * n + 2
      omega
    let T : G → (V →ₗ[k] V) := fun g => ρ g - (Q.polarBilin c ∘ₗ ρ g).smulRight v₀
    have hTapp : ∀ g x, T g x = ρ g x - polar Q c (ρ g x) • v₀ := fun g x => by
      simp [T]
    have hT : ∀ g, ∀ x ∈ U, T g x ∈ U := by
      intro g x hx
      rw [hmemU] at hx ⊢
      rw [hTapp]
      refine ⟨?_, ?_⟩
      · rw [polar_sub_left, polar_smul_left, polar_self_zero, smul_zero, sub_zero, hpv]
        exact hx.1
      · rw [polar_sub_right, polar_smul_right, hcv, smul_eq_mul, mul_one, sub_self]
    let ρU : Representation k G U :=
      { toFun := fun g => (T g).restrict (hT g)
        map_one' := by
          refine LinearMap.ext fun x => Subtype.ext ?_
          rw [LinearMap.coe_restrict_apply, hTapp, map_one, Module.End.one_apply,
            ((hmemU x).1 x.2).2, zero_smul, sub_zero]
          rfl
        map_mul' := fun g h => by
          refine LinearMap.ext fun x => Subtype.ext ?_
          rw [Module.End.mul_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply,
            LinearMap.coe_restrict_apply, hTapp, hTapp, hTapp, map_sub, map_smul, hρv, map_mul,
            Module.End.mul_apply, polar_sub_right, polar_smul_right, hcv, smul_eq_mul, mul_one,
            sub_smul]
          abel }
    have hρU' : ∀ g (x : U), ρ g (x : V) = (ρU g x : V) + polar Q c (ρ g x) • v₀ :=
      fun g x => by
        have h : (ρU g x : V) = ρ g x - polar Q c (ρ g x) • v₀ := hTapp g x
        rw [h, sub_add_cancel]
    let QU : QuadraticForm k U := Q.comp U.subtype
    have hisoU : ∀ g x, QU (ρU g x) = QU x := fun g x => by
      show Q (T g x) = Q x
      rw [hTapp, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add (Q : V → k),
        QuadraticMap.map_smul, hQv, smul_zero, add_zero, polar_smul_right, hpv,
        ((hmemU x).1 x.2).1, smul_zero, add_zero, hiso]
    have hdec : ∀ z : V, z - polar Q z c • v₀ - polar Q z v₀ • c ∈ U := fun z => by
      rw [hmemU]
      constructor
      · rw [polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, polar_self_zero,
          hcv, smul_zero, smul_eq_mul, mul_one, sub_zero, sub_self]
      · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hcv,
          polar_self_zero, smul_zero, smul_eq_mul, mul_one, sub_zero, hsymm c z, sub_self]
    have hm : ∀ x : U, polar Q (x : V) v₀ = 0 ∧ polar Q c (x : V) = 0 := fun x => (hmemU x).1 x.2
    have hrad : ∀ x : U, (∀ y : U, polar Q (x : V) (y : V) = 0) → x = 0 := by
      intro x hx
      refine Subtype.ext (hQ.1 x fun z => ?_)
      show polar Q (x : V) z = 0
      have h := hx ⟨_, hdec z⟩
      change polar Q (x : V) (z - polar Q z c • v₀ - polar Q z v₀ • c) = 0 at h
      rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, (hm x).1,
        hsymm (x : V) c, (hm x).2, smul_zero, smul_zero, sub_zero, sub_zero] at h
      exact h
    have hQU : QU.polarBilin.Nondegenerate :=
      ⟨fun x hx => hrad x fun y => hx y, fun y hy => hrad y fun x => by rw [hsymm]; exact hy x⟩
    obtain ⟨v', w', u₀, u₀', hF⟩ := ih hQU hUdim ρU hisoU
    have hcoe : ∀ (a : Fin n → k) (y : Fin n → U),
        ((∑ j, a j • y j : U) : V) = ∑ j, a j • (y j : V) := fun a y => by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    refine ⟨Fin.cons v₀ fun i => (v' i : V), Fin.cons c fun i => (w' i : V), u₀, u₀',
      { Qv := fun i => ?_
        Qw := fun i => ?_
        vv := fun i j => ?_
        ww := fun i j => ?_
        vw := fun i j => ?_
        vu := fun i => ?_
        vu' := fun i => ?_
        wu := fun i => ?_
        wu' := fun i => ?_
        uu' := hF.uu'
        fixv := fun g i => ?_
        fixu := fun g => ?_
        fixu' := fun g => ?_ }⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; exact hQv
      · simp only [Fin.cons_succ]; exact hF.Qv i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; exact hQc
      · simp only [Fin.cons_succ]; exact hF.Qw i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
        simp only [Fin.cons_zero, Fin.cons_succ]
      · exact polar_self_zero v₀
      · rw [hsymm]; exact (hm _).1
      · exact (hm _).1
      · exact hF.vv i j
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
        simp only [Fin.cons_zero, Fin.cons_succ]
      · exact polar_self_zero c
      · exact (hm _).2
      · rw [hsymm]; exact (hm _).2
      · exact hF.ww i j
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · rw [if_pos rfl]
        exact hvc
      · rw [if_neg (Fin.succ_ne_zero j).symm]
        show polar Q v₀ (w' j : V) = 0
        rw [hsymm]; exact (hm _).1
      · rw [if_neg (Fin.succ_ne_zero i)]
        show polar Q (v' i : V) c = 0
        rw [hsymm]; exact (hm _).2
      · have h := hF.vw i j
        show polar Q (v' i : V) (w' j : V) = if i.succ = j.succ then 1 else 0
        simp only [Fin.succ_inj]
        exact h
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; rw [hsymm]; exact (hm _).1
      · simp only [Fin.cons_succ]; exact hF.vu i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; rw [hsymm]; exact (hm _).1
      · simp only [Fin.cons_succ]; exact hF.vu' i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; exact (hm _).2
      · simp only [Fin.cons_succ]; exact hF.wu i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · simp only [Fin.cons_zero]; exact (hm _).2
      · simp only [Fin.cons_succ]; exact hF.wu' i
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · refine ⟨0, fun _ _ => rfl, ?_⟩
        simp only [Fin.cons_zero, hρv, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      · obtain ⟨a, ha0, ha⟩ := hF.fixv g i
        refine ⟨Fin.cons (polar Q c (ρ g (v' i))) a, fun j hj => ?_, ?_⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact absurd hj (not_le.mpr (Fin.succ_pos i))
          · rw [Fin.cons_succ]
            exact ha0 j (Fin.succ_le_succ_iff.mp hj)
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          have h := hρU' g (v' i)
          rw [ha, Submodule.coe_add, hcoe] at h
          exact h.trans (by abel)
    · obtain ⟨a, ha⟩ := hF.fixu g
      refine ⟨Fin.cons (polar Q c (ρ g u₀)) a, ?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h := hρU' g u₀
      rw [ha, Submodule.coe_add, hcoe] at h
      exact h.trans (by abel)
    · obtain ⟨c', a, ha⟩ := hF.fixu' g
      refine ⟨c', Fin.cons (polar Q c (ρ g u₀')) a, ?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have h := hρU' g u₀'
      rw [ha, Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, hcoe] at h
      exact h.trans (by abel)

private theorem pdual_inj' {n : ℕ} {p q : PIdx n} : pdual p = pdual q ↔ p = q :=
  ⟨fun h => by simpa using congrArg pdual h, fun h => h ▸ rfl⟩

theorem exists_pairBasis_unitri {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {Q : QuadraticForm k V} {n : ℕ} (hQ : Q.polarBilin.Nondegenerate)
    (hV : finrank k V = 2 * n + 2) (E : Subgroup (V ≃ₗ[k] V)) (hE : IsPGroup 2 E)
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ b : Basis (PIdx n) k V, IsPairBasis Q b ∧ ∀ g ∈ E, IsUnitri prank (basisMat b g) := by
  classical
  let ρ : Representation k E V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp E.subtype
  have hiso : ∀ (g : E) x, Q (ρ g x) = Q x := fun g x =>
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hEO g.2)) x
  have hsymm : ∀ x y, polar Q x y = polar Q y x := fun x y => polar_comm _ x y
  have hpiso : ∀ (g : E) x y, polar Q (ρ g x) (ρ g y) = polar Q x y := fun g x y => by
    simp only [polar, ← map_add, hiso]
  obtain ⟨v, w, u, u', hF⟩ := exists_flagData hE n hQ hV ρ hiso
  have hfin2 : ∀ t : Fin 2, t = 0 ∨ t = 1 := by decide
  have hpd0 : (pdual (Sum.inr (Sum.inl 0)) : PIdx n) = Sum.inr (Sum.inl 1) := rfl
  have hpd1 : (pdual (Sum.inr (Sum.inl 1)) : PIdx n) = Sum.inr (Sum.inl 0) := rfl
  have h01 : (Sum.inr (Sum.inl 0) : PIdx n) ≠ Sum.inr (Sum.inl 1) :=
    Sum.inr_injective.ne (Sum.inl_injective.ne (by decide))
  let f : PIdx n → V := Sum.elim v (Sum.elim ![u, u'] w)
  have hpol : ∀ p q, polar Q (f p) (f q) = if q = pdual p then 1 else 0 := by
    intro p q
    rcases p with i | t | i <;> rcases q with i' | t' | i'
    · rw [if_neg (by simp)]
      exact hF.vv i i'
    · rw [if_neg (by simp)]
      rcases hfin2 t' with rfl | rfl
      · exact hF.vu i
      · exact hF.vu' i
    · have h := hF.vw i i'
      show polar Q (v i) (w i') = if Sum.inr (Sum.inr i') = pdual (Sum.inl i) then 1 else 0
      simp only [pdual_inl, Sum.inr.injEq]
      by_cases hii : i = i'
      · subst hii
        rw [if_pos rfl] at h ⊢
        exact h
      · rw [if_neg hii] at h
        rw [if_neg (Ne.symm hii)]
        exact h
    · rw [if_neg (by simp)]
      rcases hfin2 t with rfl | rfl
      · show polar Q u (v i') = 0
        rw [hsymm]; exact hF.vu i'
      · show polar Q u' (v i') = 0
        rw [hsymm]; exact hF.vu' i'
    · rcases hfin2 t with rfl | rfl <;> rcases hfin2 t' with rfl | rfl
      · rw [hpd0, if_neg h01]; exact polar_self_zero u
      · rw [hpd0, if_pos rfl]; exact hF.uu'
      · rw [hpd1, if_pos rfl]
        show polar Q u' u = 1
        rw [hsymm]; exact hF.uu'
      · rw [hpd1, if_neg h01.symm]; exact polar_self_zero u'
    · rw [if_neg (by simp)]
      rcases hfin2 t with rfl | rfl
      · show polar Q u (w i') = 0
        rw [hsymm]; exact hF.wu i'
      · show polar Q u' (w i') = 0
        rw [hsymm]; exact hF.wu' i'
    · show polar Q (w i) (v i') = if Sum.inl i' = pdual (Sum.inr (Sum.inr i)) then 1 else 0
      simp only [pdual_inr_inr, Sum.inl.injEq]
      rw [hsymm]
      exact hF.vw i' i
    · rw [if_neg (by simp)]
      rcases hfin2 t' with rfl | rfl
      · exact hF.wu i
      · exact hF.wu' i
    · rw [if_neg (by simp)]
      exact hF.ww i i'
  have hli : LinearIndependent k f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha q
    have h := congrArg (fun x => polar Q x (f (pdual q))) ha
    simp only [polar_sum_left, QuadraticMap.polar_zero_left, hpol, pdual_inj', mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  have hcard : Fintype.card (PIdx n) = finrank k V := by
    rw [hV]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ p, b p = f p := fun p =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) p
  have hbP : IsPairBasis Q b :=
    ⟨fun p q => by rw [hb, hb]; exact hpol p q, fun i => by rw [hb]; exact hF.Qv i,
      fun i => by rw [hb]; exact hF.Qw i⟩
  have hcol : ∀ (g : E) p q, prank q ≤ prank p → polar Q (ρ g (f q) - f q) (f (pdual p)) = 0 := by
    intro g p q hpq
    rcases q with i | t | i
    · obtain ⟨a, ha0, ha⟩ := hF.fixv g i
      have hd : ρ g (f (.inl i)) - f (.inl i) = ∑ j, a j • v j := by
        show ρ g (v i) - v i = _
        rw [ha, add_sub_cancel_left]
      rw [hd, polar_sum_left]
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases p with i' | t' | i'
      · simp only [prank_inl] at hpq
        show a l * polar Q (v l) (w i') = 0
        rw [hF.vw]
        by_cases hl : l = i'
        · rw [hl, ha0 i' (Fin.le_def.mpr hpq), zero_mul]
        · rw [if_neg hl, mul_zero]
      · rcases hfin2 t' with rfl | rfl
        · show a l * polar Q (v l) u' = 0
          rw [hF.vu', mul_zero]
        · show a l * polar Q (v l) u = 0
          rw [hF.vu, mul_zero]
      · show a l * polar Q (v l) (v i') = 0
        rw [hF.vv, mul_zero]
    · rcases hfin2 t with rfl | rfl
      · obtain ⟨a, ha⟩ := hF.fixu g
        have hd : ρ g (f (.inr (.inl 0))) - f (.inr (.inl 0)) = ∑ j, a j • v j := by
          show ρ g u - u = _
          rw [ha, add_sub_cancel_left]
        rw [hd, polar_sum_left]
        refine Finset.sum_eq_zero fun l _ => ?_
        rcases p with i' | t' | i'
        · simp only [prank_inl, prank_inr_inl, Fin.val_zero] at hpq
          have := i'.isLt
          omega
        · rcases hfin2 t' with rfl | rfl
          · show a l * polar Q (v l) u' = 0
            rw [hF.vu', mul_zero]
          · show a l * polar Q (v l) u = 0
            rw [hF.vu, mul_zero]
        · show a l * polar Q (v l) (v i') = 0
          rw [hF.vv, mul_zero]
      · obtain ⟨c, a, ha⟩ := hF.fixu' g
        have hd : ρ g (f (.inr (.inl 1))) - f (.inr (.inl 1)) = c • u + ∑ j, a j • v j := by
          show ρ g u' - u' = _
          rw [ha, add_assoc, add_sub_cancel_left]
        rw [hd, polar_add_left, polar_smul_left, polar_sum_left]
        rcases p with i' | t' | i'
        · simp only [prank_inl, prank_inr_inl, Fin.val_one] at hpq
          have := i'.isLt
          omega
        · rcases hfin2 t' with rfl | rfl
          · simp only [prank_inr_inl, Fin.val_zero, Fin.val_one] at hpq
            omega
          · show c • polar Q u u + ∑ l, a l * polar Q (v l) u = 0
            rw [polar_self_zero, smul_zero, zero_add]
            exact Finset.sum_eq_zero fun l _ => by rw [hF.vu, mul_zero]
        · show c • polar Q u (v i') + ∑ l, a l * polar Q (v l) (v i') = 0
          rw [hsymm, hF.vu, smul_zero, zero_add]
          exact Finset.sum_eq_zero fun l _ => by rw [hF.vv, mul_zero]
    · rcases p with i' | t' | i'
      · simp only [prank_inl, prank_inr_inr] at hpq
        have := i.isLt
        have := i'.isLt
        omega
      · simp only [prank_inr_inl, prank_inr_inr] at hpq
        have := i.isLt
        have := t'.isLt
        omega
      · simp only [prank_inr_inr] at hpq
        have hii : i' ≤ i := by
          rw [Fin.le_def]
          have := i.isLt
          have := i'.isLt
          omega
        obtain ⟨a, ha0, ha⟩ := hF.fixv g⁻¹ i'
        show polar Q (ρ g (w i) - w i) (v i') = 0
        have hgg : ρ g (ρ g⁻¹ (v i')) = v i' := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        have h1 : polar Q (ρ g (w i)) (v i') = polar Q (w i) (ρ g⁻¹ (v i')) := by
          rw [← hpiso g (w i) (ρ g⁻¹ (v i')), hgg]
        rw [polar_sub_left, h1, ha, polar_add_right, polar_sum_right, add_sub_cancel_left]
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [hsymm, hF.vw]
        by_cases hl : l = i
        · rw [hl, ha0 i hii, zero_mul]
        · rw [if_neg hl, mul_zero]
  refine ⟨b, hbP, fun g hg => ?_⟩
  intro p q hpq
  by_contra hlt
  push Not at hlt
  apply hpq
  have h1 : polar Q (g (f q)) (f (pdual p)) = polar Q (f q) (f (pdual p)) := by
    have := hcol ⟨g, hg⟩ p q hlt
    rwa [polar_sub_left, sub_eq_zero] at this
  rw [Matrix.sub_apply, basisMat_apply, hbP.repr_apply, hb, hb, h1, hpol, Matrix.one_apply]
  simp only [pdual_inj', sub_self]

end CFSG.RankThree.GF2n.Smith81.OrthGraph
