module

public import CFSG.LieType.ChevTwo.OppCl.Toolkit
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMRed
import CFSG.GH74.GLS.IVK.L2.Lemma12
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals
import CFSG.GH74.BNPair.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylowParameter

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open
  CFSG.EvenSmallLie.CatalogOrders
  CFSG.LieType.ChevTwo.OppCl

private lemma lre6bla_map_zero {V : Type} [AddCommGroup V] {g : Equiv.Perm V}
    (hadd : ∀ u v, g (u + v) = g u + g v) : g 0 = 0 := by
  have h : g 0 = g 0 + g 0 := by simpa using hadd 0 0
  have h2 : g 0 + 0 = g 0 + g 0 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

private lemma lre6bla_sigma_unique {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] (g : semilinGroup F V) {σ τ : F ≃+* F}
    (hσ : ∀ (c : F) (v : V), (g : Equiv.Perm V) (c • v) = σ c • (g : Equiv.Perm V) v)
    (hτ : ∀ (c : F) (v : V), (g : Equiv.Perm V) (c • v) = τ c • (g : Equiv.Perm V) v) :
    σ = τ := by
  ext c
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hg0 : (g : Equiv.Perm V) 0 = 0 := lre6bla_map_zero g.2.1
  have hgv : (g : Equiv.Perm V) v ≠ 0 := by
    intro h0
    exact hv ((g : Equiv.Perm V).injective (by rw [h0, hg0]))
  exact smul_left_injective F hgv
    (show σ c • (g : Equiv.Perm V) v = τ c • (g : Equiv.Perm V) v by
      rw [← hσ c v, ← hτ c v])

private noncomputable def lre6bla_sig {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : semilinGroup F V) : F ≃+* F :=
  Classical.choose g.2.2

private lemma lre6bla_sig_spec {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : semilinGroup F V) (c : F) (v : V) :
    (g : Equiv.Perm V) (c • v) = lre6bla_sig g c • (g : Equiv.Perm V) v :=
  Classical.choose_spec g.2.2 c v

private noncomputable def lre6bla_sigHom {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] : semilinGroup F V →* (F ≃+* F) where
  toFun := lre6bla_sig
  map_one' := by
    apply lre6bla_sigma_unique (1 : semilinGroup F V)
    · exact lre6bla_sig_spec 1
    · intro c v
      change (1 : Equiv.Perm V) (c • v) = (1 : F ≃+* F) c • (1 : Equiv.Perm V) v
      simp
  map_mul' := by
    intro a b
    apply lre6bla_sigma_unique (a * b)
    · exact lre6bla_sig_spec (a * b)
    · intro c v
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, lre6bla_sig_spec, RingAut.mul_apply]

private noncomputable def lre6bla_linOf {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] (g : (lre6bla_sigHom (F := F) (V := V)).ker) : V ≃ₗ[F] V where
  toFun := (g : semilinGroup F V)
  map_add' := (g : semilinGroup F V).2.1
  map_smul' := by
    intro c v
    have h : lre6bla_sig (g : semilinGroup F V) = 1 := MonoidHom.mem_ker.mp g.2
    rw [lre6bla_sig_spec (g : semilinGroup F V) c v, h]
    simp
  invFun := ((g : semilinGroup F V) : Equiv.Perm V).symm
  left_inv := ((g : semilinGroup F V) : Equiv.Perm V).left_inv
  right_inv := ((g : semilinGroup F V) : Equiv.Perm V).right_inv

private lemma lre6bla_linOf_injective {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] : Function.Injective (lre6bla_linOf (F := F) (V := V)) := by
  intro g h e
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro v
  exact congrFun (congrArg (fun f : V ≃ₗ[F] V => (f : V → V)) e) v

private noncomputable def lre6bla_linHom {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] : (lre6bla_sigHom (F := F) (V := V)).ker →* (V ≃ₗ[F] V) where
  toFun := lre6bla_linOf
  map_one' := by
    ext v
    rfl
  map_mul' := by
    intro a b
    ext v
    rfl

private lemma lre6bla_linHom_injective {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V] : Function.Injective (lre6bla_linHom (F := F) (V := V)) :=
  lre6bla_linOf_injective

theorem lre6b_card_semilin_dvd {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [Finite V] [Nontrivial V] :
    Nat.card (semilinGroup F V) ∣ Nat.card (V ≃ₗ[F] V) * Nat.card (F ≃+* F) := by
  have hker : Nat.card (lre6bla_sigHom (F := F) (V := V)).ker ∣ Nat.card (V ≃ₗ[F] V) :=
    Subgroup.card_dvd_of_injective (lre6bla_linHom (F := F) (V := V))
      (lre6bla_linHom_injective (F := F) (V := V))
  have hrange : Nat.card (lre6bla_sigHom (F := F) (V := V)).range ∣ Nat.card (F ≃+* F) :=
    Subgroup.card_subgroup_dvd_card (lre6bla_sigHom (F := F) (V := V)).range
  have hcard := Subgroup.card_ker_mul_card_range (lre6bla_sigHom (F := F) (V := V))
  rw [← hcard]
  exact Nat.mul_dvd_mul hker hrange

private theorem lre6blb_foldl_range (q N : ℕ) :
    (List.range N).foldl (fun a i => a * (q ^ (i + 1) - 1)) 1 =
      ∏ i ∈ Finset.range N, (q ^ (i + 1) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Finset.prod_range_succ]

private theorem lre6blb_card_GL (q N : ℕ) :
    (∏ i : Fin N, (q ^ N - q ^ (i : ℕ))) = bmGlOrd N q := by
  have hfold := lre6blb_foldl_range q N
  have hfin : (∏ i : Fin N, (q ^ N - q ^ (i : ℕ))) =
      ∏ i ∈ Finset.range N, (q ^ N - q ^ i) :=
    Fin.prod_univ_eq_prod_range (fun i => q ^ N - q ^ i) N
  unfold bmGlOrd
  rw [hfold, hfin]
  calc
    (∏ i ∈ Finset.range N, (q ^ N - q ^ i))
        = ∏ i ∈ Finset.range N, q ^ i * (q ^ (N - i) - 1) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hi' : i ≤ N := Nat.le_of_lt (Finset.mem_range.mp hi)
          rw [Nat.mul_sub, ← pow_add, Nat.add_sub_of_le hi', mul_one]
    _ = (∏ i ∈ Finset.range N, q ^ i) * (∏ i ∈ Finset.range N, (q ^ (N - i) - 1)) := by
          rw [Finset.prod_mul_distrib]
    _ = q ^ (∑ i ∈ Finset.range N, i) * (∏ i ∈ Finset.range N, (q ^ (N - i) - 1)) := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ = q ^ (N * (N - 1) / 2) * (∏ i ∈ Finset.range N, (q ^ (N - i) - 1)) := by
          rw [Finset.sum_range_id]
    _ = q ^ (N * (N - 1) / 2) * (∏ i ∈ Finset.range N, (q ^ (i + 1) - 1)) := by
          congr 1
          rw [← Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) N]
          apply Finset.prod_congr rfl
          intro i hi
          exact congrArg (fun e => q ^ e - 1)
            (by have hi' : i < N := Finset.mem_range.mp hi; omega)

theorem lre6b_card_linearEquiv {F ι : Type} [Field F] [Finite F] [Fintype ι] [DecidableEq ι]
    {N : ℕ} (hN : Fintype.card ι = N) :
    Nat.card ((ι → F) ≃ₗ[F] (ι → F)) = bmGlOrd N (Nat.card F) := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let b : Module.Basis (Fin N) F (ι → F) :=
    (Pi.basisFun F ι).reindex (Fintype.equivFinOfCardEq hN)
  have hcard : Nat.card ((ι → F) ≃ₗ[F] (ι → F)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin N) F) :=
    (Nat.card_congr
      ((Matrix.GeneralLinearGroup.toLin' b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))).toEquiv).symm
  rw [hcard, Matrix.card_GL_field]
  simpa only [Nat.card_eq_fintype_card] using lre6blb_card_GL (Fintype.card F) N

private lemma lre6blc_induces_functional {F V H K : Type} [Field F] [AddCommGroup V] [Module F V]
    [Group H] [Group K] (π : H →* K) (ρ : H →* Module.End F V)
    (hπ : Function.Surjective π) (hρ : Function.Injective ρ)
    {r : Equiv.Perm V} {α β : MulAut K} (hα : Induces π ρ r α) (hβ : Induces π ρ r β) :
    α = β := by
  apply MulEquiv.ext
  intro k
  obtain ⟨h, rfl⟩ := hπ k
  obtain ⟨h', hh', hα'⟩ := hα.1 h
  obtain ⟨h'', hh'', hβ'⟩ := hβ.1 h
  have hρeq : ρ h' = ρ h'' := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := r.surjective v
    rw [← hh' w, ← hh'' w]
  have hh : h' = h'' := hρ hρeq
  rw [hα', hβ', hh]

theorem lre6b_factorization_le_of_lift {F V H K : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [Finite V] [Group H] [Group K] [Finite K] (π : H →* K)
    (hπ : Function.Surjective π) (ρ : H →* Module.End F V) (hρ : Function.Injective ρ)
    (P : Equiv.Perm V → Prop) (hP1 : P 1) (hPm : ∀ r s, P r → P s → P (r * s))
    (hPi : ∀ r, P r → P r⁻¹) (ℓ : ℕ) [Fact ℓ.Prime]
    (hind : ∀ R : Subgroup (MulAut K), IsPGroup ℓ R → ∀ α ∈ R, ∃ r : Equiv.Perm V,
      r ∈ semilinGroup F V ∧ P r ∧ Induces π ρ r α) :
    (Nat.card (MulAut K)).factorization ℓ ≤ (Nat.card (semilinGroup F V)).factorization ℓ := by
  classical
  haveI : Finite (MulAut K) := inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow ℓ (MulAut K)) := Sylow.nonempty
  let R : Subgroup (MulAut K) := S
  have hR : IsPGroup ℓ R := by simpa only [R] using S.isPGroup'
  have hS : Nat.card R = ℓ ^ (Nat.card (MulAut K)).factorization ℓ := by
    simpa only [R] using Sylow.card_eq_multiplicity S
  obtain ⟨Rh, hRh_le, _hRh_P, hRh_p, _hRh_norm, hInd, _hInd'⟩ :=
    autLift_of_induced (P := P) hP1 hPm hPi ℓ R hR (hind R hR)
  haveI : Finite Rh := inferInstance
  have hchoose : ∀ α : R, ∃ r ∈ Rh, Induces π ρ r (α : MulAut K) :=
    fun α => hInd α α.2
  let rOf : R → Rh := fun α =>
    ⟨Classical.choose (hchoose α), (Classical.choose_spec (hchoose α)).1⟩
  have hrOf_spec : ∀ α : R, Induces π ρ (rOf α) (α : MulAut K) :=
    fun α => (Classical.choose_spec (hchoose α)).2
  have hle_card : Nat.card R ≤ Nat.card Rh := by
    refine Nat.card_le_card_of_injective rOf ?_
    intro α β hαβ
    apply Subtype.ext
    have h1 : Induces π ρ (rOf α) (α : MulAut K) := hrOf_spec α
    have h2 : Induces π ρ (rOf β) (β : MulAut K) := hrOf_spec β
    have hEq : (rOf α : Equiv.Perm V) = (rOf β : Equiv.Perm V) := congrArg Subtype.val hαβ
    rw [← hEq] at h2
    exact lre6blc_induces_functional π ρ hπ hρ h1 h2
  have hdvd : Nat.card Rh ∣ Nat.card (semilinGroup F V) := Subgroup.card_dvd_of_le hRh_le
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hRh_p
  have hpow_dvd : ℓ ^ m ∣ Nat.card (semilinGroup F V) := by
    rw [← hm]
    exact hdvd
  have hne : Nat.card (semilinGroup F V) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hm_le : m ≤ (Nat.card (semilinGroup F V)).factorization ℓ :=
    (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : ℓ.Prime) hne).mp hpow_dvd
  have hle : ℓ ^ (Nat.card (MulAut K)).factorization ℓ ≤ ℓ ^ m := by
    rw [← hS, ← hm]
    exact hle_card
  exact le_trans ((pow_le_pow_iff_right₀ (Fact.out : ℓ.Prime).one_lt).mp hle) hm_le

end CFSG.StandardType.SporadicShape
