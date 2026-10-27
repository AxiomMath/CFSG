module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588
open scoped commutatorElement

theorem commutator_eq_self_of_simple {G : Type*} [Group G] {S : Subgroup G}
    (hS : IsSimpleGroup S) {x y : G} (hx : x ∈ S) (hy : y ∈ S) (hxy : x * y ≠ y * x) :
    ⁅S, S⁆ = S := by
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) with
      h | h
    · exfalso
      have hmem : ⁅(⟨x, hx⟩ : S), (⟨y, hy⟩ : S)⁆ ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
        Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hxy (congrArg Subtype.val hmem)
    · exact h
  have e := congrArg (Subgroup.map S.subtype) htop
  rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at e

theorem isQuasisimple_of_simple_uc6b {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q) {x y : Q}
    (hxy : x * y ≠ y * x) : CFSG.IsQuasisimple Q := by
  have hZ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with h | h
    · exact h
    · exact absurd ((mem_center_iff.1 (h ▸ mem_top y)) x) hxy
  have hperf : Group.IsPerfect Q := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      have h1 : ⁅x, y⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact hxy h1
    · exact h
  let e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, e.symm x, e.symm y, fun h => hxy ?_⟩
  have := congrArg e h
  simpa using this

theorem pow_five_of_mem_S₀ {x : A10} (hx : x ∈ S₀) : x ^ 5 = 1 := by
  obtain ⟨i, j, rfl⟩ := mem_S₀.1 hx
  rw [(Commute.pow_pow a₁₂_commute i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
    pow_mul, pow_mul, a₁_pow, a₂_pow, one_pow, one_pow, one_mul]

open scoped Pointwise in
theorem pow_five_of_pow_twentyfive {x : A10} (hx : x ^ 25 = 1) : x ^ 5 = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Q : Sylow 5 A10 := Sylow.ofCard S₀ (by rw [card_S₀, factorization_A10]; norm_num)
  have hp : IsPGroup 5 (zpowers x) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).1
      (orderOf_dvd_of_pow_eq_one (show x ^ (5 ^ 2) = 1 by norm_num [hx]))
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A10 Q P
  have hxP : x ∈ (P : Subgroup A10) := hP (mem_zpowers x)
  have h2 : (P : Subgroup A10) = MulAut.conj g • (Q : Subgroup A10) := by rw [← hg]; rfl
  rw [h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
  have hy : ((MulAut.conj g)⁻¹ • x) ^ 5 = 1 := pow_five_of_mem_S₀ hxP
  rw [MulAut.smul_def, ← map_pow] at hy
  exact (MulAut.conj g)⁻¹.injective (hy.trans (map_one _).symm)

noncomputable def conjEquiv10 : Equiv.Perm (Fin 10) ≃* MulAut A10 :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
      (by norm_num))

theorem conjEquiv10_coe (a : A10) : conjEquiv10 (a : Equiv.Perm (Fin 10)) = MulAut.conj a := by
  rw [conjEquiv10, MulEquiv.ofBijective_apply]
  exact MulAut.conjNormal_val

namespace Mz614

namespace A10Setup

variable {G : Type} [Group G] [Finite G] {m : Mz614 G} (D : A10Setup m)

include D in
theorem center_eq_bot : center ↥m.L = ⊥ := centreless_of_isAlt_ten ⟨D.ψ⟩

include D in
theorem eq_one_of_mem_centralizer {x : G} (hxL : x ∈ m.L) (hx : x ∈ centralizer (m.L : Set G)) :
    x = 1 := by
  have h : (⟨x, hxL⟩ : ↥m.L) ∈ center ↥m.L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hx g g.2)
  rw [D.center_eq_bot, mem_bot] at h
  exact congrArg Subtype.val h

include D in
theorem pow_five_of_mem_L {ℓ : G} (hℓ : ℓ ∈ m.L) (h : ℓ ^ 25 = 1) : ℓ ^ 5 = 1 := by
  obtain ⟨σ, rfl⟩ := D.exists_ι hℓ
  have hσ : σ ^ 25 = 1 := D.ι_injective (by rw [map_pow, h, map_one])
  rw [← map_pow, pow_five_of_pow_twentyfive hσ, map_one]

noncomputable def autA : MulAut ↥m.L →* MulAut A10 where
  toFun f := (D.ψ.symm.trans f).trans D.ψ
  map_one' := by
    ext x
    simp
  map_mul' f g := by
    ext x
    simp

noncomputable def permOf : ↥(normalizer (m.L : Set G)) →* Equiv.Perm (Fin 10) :=
  conjEquiv10.symm.toMonoidHom.comp (D.autA.comp m.L.normalizerMonoidHom)

@[expose] noncomputable def chi : ↥(normalizer (m.L : Set G)) →* ℤˣ := Equiv.Perm.sign.comp D.permOf

theorem permOf_mem_of_chi {n : ↥(normalizer (m.L : Set G))} (h : D.chi n = 1) :
    D.permOf n ∈ alternatingGroup (Fin 10) :=
  Equiv.Perm.mem_alternatingGroup.2 h

theorem conjEquiv10_permOf (n : ↥(normalizer (m.L : Set G))) :
    conjEquiv10 (D.permOf n) = D.autA (m.L.normalizerMonoidHom n) := by
  simp [permOf]

theorem conj_eq_of_permOf {n : ↥(normalizer (m.L : Set G))} {a : A10}
    (h : D.permOf n = (a : Equiv.Perm (Fin 10))) {y : G} (hy : y ∈ m.L) :
    (n : G) * y * (n : G)⁻¹ = D.ι a * y * (D.ι a)⁻¹ := by
  have h1 : D.autA (m.L.normalizerMonoidHom n) = MulAut.conj a := by
    rw [← conjEquiv10_coe, ← h, D.conjEquiv10_permOf]
  have h2 := congrArg (fun f : MulAut A10 => D.ι (f (D.ψ ⟨y, hy⟩))) h1
  simp only [autA, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulAut.conj_apply, map_mul, map_inv, ι_ψ] at h2
  rw [← h2]
  simp

theorem permOf_eq_of_conj {n : ↥(normalizer (m.L : Set G))} {a : A10}
    (h : ∀ y ∈ m.L, (n : G) * y * (n : G)⁻¹ = D.ι a * y * (D.ι a)⁻¹) :
    D.permOf n = (a : Equiv.Perm (Fin 10)) := by
  apply conjEquiv10.injective
  rw [conjEquiv10_coe, D.conjEquiv10_permOf]
  refine MulEquiv.ext fun x => ?_
  apply D.ι_injective
  have hx := h _ (D.ι_mem_L x)
  simp only [autA, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply, MulAut.conj_apply,
    map_mul, map_inv, ι_ψ]
  rw [← hx, ι_apply]
  simp

theorem mem_centralizer_of_permOf_eq_one {n : ↥(normalizer (m.L : Set G))}
    (h : D.permOf n = 1) : (n : G) ∈ centralizer (m.L : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have h1 := D.conj_eq_of_permOf (a := 1) (by rw [h]; rfl) hy
  rw [map_one, one_mul, inv_one, mul_one] at h1
  calc y * n = ((n : G) * y * (n : G)⁻¹) * n := by rw [h1]
    _ = n * y := by group

theorem exists_mem_centralizer_of_chi_eq_one {n : ↥(normalizer (m.L : Set G))}
    (h : D.chi n = 1) : ∃ ℓ ∈ m.L, ℓ⁻¹ * (n : G) ∈ centralizer (m.L : Set G) := by
  have hmem : D.permOf n ∈ alternatingGroup (Fin 10) := D.permOf_mem_of_chi h
  refine ⟨D.ι ⟨D.permOf n, hmem⟩, D.ι_mem_L _, mem_centralizer_iff.2 fun y hy => ?_⟩
  have h1 := D.conj_eq_of_permOf (a := ⟨D.permOf n, hmem⟩) rfl hy
  set ℓ := D.ι ⟨D.permOf n, hmem⟩
  calc y * (ℓ⁻¹ * n) = ℓ⁻¹ * (ℓ * y * ℓ⁻¹) * n := by group
    _ = ℓ⁻¹ * ((n : G) * y * (n : G)⁻¹) * n := by rw [h1]
    _ = ℓ⁻¹ * n * y := by group

theorem chi_eq_one_of_pow {n : ↥(normalizer (m.L : Set G))} {k : ℕ} (hk : Odd k)
    (h : (n : G) ^ k = 1) : D.chi n = 1 := by
  have h1 : n ^ k = 1 := Subtype.ext (by simpa using h)
  have h2 : D.chi n ^ k = 1 := by rw [← map_pow, h1, map_one]
  obtain ⟨j, rfl⟩ := hk
  rwa [pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h2

theorem chi_of_mem_L {ℓ : G} (hℓ : ℓ ∈ m.L) (hn : ℓ ∈ normalizer (m.L : Set G)) :
    D.chi ⟨ℓ, hn⟩ = 1 := by
  obtain ⟨σ, rfl⟩ := D.exists_ι hℓ
  have h : D.permOf ⟨D.ι σ, hn⟩ = (σ : Equiv.Perm (Fin 10)) :=
    D.permOf_eq_of_conj fun _ _ => rfl
  show Equiv.Perm.sign (D.permOf ⟨D.ι σ, hn⟩) = 1
  rw [h]
  exact Equiv.Perm.mem_alternatingGroup.1 σ.2

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
