module

public import CFSG.Quasithin.H13.L32ACSkPfSp4
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.Open.PGLModelStated
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (projUnipotent proj)
open CFSG.Quasithin.H13.L32A.C.SkPf (mem_centMod le_centMod map_congr_symm_eq pow_two_pow_congr exists_map_conj_eq
  isSylowTwoOf_map_symm map_map_symm mem_normalizer_of_map_conj_eq map_mul_eq map_inv_eq isSylowTwoOf_sylow sp4T
  spTau tauAut_sp4T fieldAut_sp4T sp4T_mem_iff sp4T_range_le sp4_comm_mem map_std_sp4 exists_conj_mul_std_sp4
  isSylowTwoOf_projUnipotent_two)
open CFSG.QuasithinUnique.Lin2.Five (tauAut)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_mk rhoL_mk_coe)

theorem uc22p218c_pow_two_pow_mul_eq {M : Type*} [Monoid M] {t : M} {a : ℕ} (ha : t ^ 2 ^ a = t) (j : ℕ) :
    t ^ 2 ^ (a * j) = t := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, ha]

theorem uc22p218c_pow_two_pow_eq_of_two_mul {M : Type*} [Monoid M] {t : M} {s B : ℕ} (hs : Odd s)
    (h1 : t ^ 2 ^ s = t) (h2 : t ^ 2 ^ (2 * B) = t) : t ^ 2 ^ B = t := by
  obtain ⟨m, rfl⟩ := hs
  have h3 := uc22p218c_pow_two_pow_mul_eq h2 (m + 1)
  rwa [show 2 * B * (m + 1) = (2 * m + 1) * B + B by ring, pow_add, pow_mul,
    uc22p218c_pow_two_pow_mul_eq h1 B] at h3

theorem uc22p218c_pow_two_pow_eq_of_mul_two_pow {M : Type*} [Monoid M] {t : M} {s : ℕ} (hs : Odd s)
    (h1 : t ^ 2 ^ s = t) {A : ℕ} (e : ℕ) (h2 : t ^ 2 ^ (A * 2 ^ e) = t) : t ^ 2 ^ A = t := by
  induction e with
  | zero => simpa using h2
  | succ e ih =>
    refine ih (uc22p218c_pow_two_pow_eq_of_two_mul hs h1 ?_)
    rwa [pow_succ, ← mul_assoc, mul_comm _ 2] at h2

theorem uc22p218c_iterate_pow_two_pow {M : Type*} [Monoid M] (B j : ℕ) (x : M) :
    (fun y : M => y ^ 2 ^ B)^[j] x = x ^ 2 ^ (B * j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, ← pow_mul, ← pow_add, mul_add_one]

theorem uc22p218c_iterate_mul_inv_mem {M A : Type*} [Group M] {U : Subgroup M} {α : MulAut M}
    (hαU : U.map α.toMonoidHom = U) (h : A → M) (ρ : A → A) (hρ : ∀ a, α (h a) * (h (ρ a))⁻¹ ∈ U)
    (j : ℕ) (a : A) : (α ^ j) (h a) * (h (ρ^[j] a))⁻¹ ∈ U := by
  have hα : ∀ u ∈ U, α u ∈ U := fun u hu => by
    have h1 := mem_map_of_mem α.toMonoidHom hu
    rwa [hαU] at h1
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, Function.iterate_succ_apply']
    have e : α ((α ^ j) (h a)) * (h (ρ (ρ^[j] a)))⁻¹ =
        α ((α ^ j) (h a) * (h (ρ^[j] a))⁻¹) * (α (h (ρ^[j] a)) * (h (ρ (ρ^[j] a)))⁻¹) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact mul_mem (hα _ ih) (hρ _)

theorem uc22p218c_ne_two_of_dvd {n r : ℕ} (hn : 1 ≤ n) (hrn : r ∣ 2 ^ n - 1) : r ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uc22p218c_exists_torus_action (α : MulAut (StatedProj (StatedSp 2 K)))
    (hαU : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) :
    ∃ i ε : ℕ, ε ≤ 1 ∧ ∀ t : Fin 2 → Kˣ,
      α (sp4T K t) * (sp4T K ((spTau^[ε] t) ^ 2 ^ i))⁻¹ ∈ projUnipotent 2 K := by
  obtain ⟨y, σ, ε, hε, rfl⟩ := exists_conj_mul_std_sp4 α
  obtain ⟨i, hi⟩ := uc22pwlie_ringEquiv_pow σ
  have hy : y ∈ normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) := by
    apply mem_normalizer_of_map_conj_eq
    have h1 := map_mul_eq hαU (map_inv_eq (map_std_sp4 σ ε))
    rwa [mul_inv_cancel_right] at h1
  have htau : ∀ (m : ℕ) (u : Fin 2 → Kˣ), (tauAut ^ m) (sp4T K u) = sp4T K (spTau^[m] u) := by
    intro m
    induction m with
    | zero => intro u; rw [pow_zero, MulAut.one_apply, Function.iterate_zero, id]
    | succ m ih =>
      intro u
      rw [pow_succ', MulAut.mul_apply, ih, tauAut_sp4T, Function.iterate_succ_apply']
  have hfield : ∀ u : Fin 2 → Kˣ,
      (fun j => Units.map σ.toRingHom.toMonoidHom (u j)) = u ^ 2 ^ i := by
    intro u
    funext j
    apply Units.ext
    simp [hi]
  refine ⟨i, ε, hε, fun t => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, htau, fieldAut_sp4T, hfield, MulAut.conj_apply]
  exact sp4_comm_mem y hy _ (sp4T_range_le ⟨_, rfl⟩)

theorem uc22p218c_normalizer_le_sup :
    normalizer ((projUnipotent 2 K : Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) ≤
      (sp4T K).range ⊔ projUnipotent 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_projUnipotent 2 (by norm_num)]
  rintro _ ⟨b, hb, rfl⟩
  have hY : CFSG.Quasithin.H13.KG22.spY.range ⊔ CFSG.Quasithin.H13.KG22.spY'.range ≤
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := 2) (k := K)).range := by
    refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨_, (CFSG.Quasithin.H13.KG22.spY_apply a).symm⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨_, (CFSG.Quasithin.H13.KG22.spY'_apply a).symm⟩
  have h1 := mem_map_of_mem (proj 2 K) (sup_le_sup_right hY _ (CFSG.Quasithin.H13.KG22.borel_le hb))
  rwa [Subgroup.map_sup, MonoidHom.map_range] at h1

omit [Finite K] [CharP K 2] in
theorem uc22p218c_spTau_mul (x y : Fin 2 → Kˣ) : spTau (x * y) = spTau x * spTau y := by
  funext j
  fin_cases j
  · exact mul_mul_mul_comm (x 0) (y 0) (x 1) (y 1)
  · show x 0 * y 0 * (x 1 * y 1)⁻¹ = x 0 * (x 1)⁻¹ * (y 0 * (y 1)⁻¹)
    rw [mul_inv]
    exact mul_mul_mul_comm (x 0) (y 0) (x 1)⁻¹ (y 1)⁻¹

omit [Finite K] [CharP K 2] in
theorem uc22p218c_spTau_pow (x : Fin 2 → Kˣ) (m : ℕ) : spTau (x ^ m) = spTau x ^ m :=
  map_pow (MonoidHom.mk' spTau uc22p218c_spTau_mul) x m

omit [Finite K] [CharP K 2] in
theorem uc22p218c_spTau_spTau (x : Fin 2 → Kˣ) : spTau (spTau x) = x ^ 2 := by
  funext j
  fin_cases j
  · show x 0 * x 1 * (x 0 * (x 1)⁻¹) = x 0 ^ 2
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, sq]
  · show x 0 * x 1 * (x 0 * (x 1)⁻¹)⁻¹ = x 1 ^ 2
    rw [mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul, sq]

omit [CharP K 2] in
theorem uc22p218c_exists_orderOf_units {n s : ℕ} (hK : Nat.card K = 2 ^ n) (hsn : s ∣ n) :
    ∃ t : Kˣ, orderOf t = 2 ^ s - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hg' : orderOf g = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨m, hm⟩ := Nat.pow_sub_one_dvd_pow_sub_one 2 hsn
  have hn2 : 2 ≤ 2 ^ n := by
    rw [← hK]
    exact Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  refine ⟨g ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hg', hm]; exact Dvd.intro_left _ rfl), hg', hm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

omit [Finite K] [CharP K 2] in
theorem uc22p218c_spTau_suzuki {k : ℕ} {t : Kˣ} (ht : t ^ 2 ^ (2 * k + 1) = t) :
    spTau ![t ^ (2 ^ k + 1), t ^ 2 ^ k] =
      ![(t ^ 2 ^ (k + 1)) ^ (2 ^ k + 1), (t ^ 2 ^ (k + 1)) ^ 2 ^ k] := by
  have hc : (t ^ 2 ^ (k + 1)) ^ 2 ^ k = t := by
    rw [← pow_mul, ← pow_add, show k + 1 + k = 2 * k + 1 by ring, ht]
  have h1 : t ^ (2 ^ k + 1) * t ^ 2 ^ k = (t ^ 2 ^ (k + 1)) ^ (2 ^ k + 1) := by
    rw [pow_succ (t ^ 2 ^ (k + 1)), hc, ← pow_add, ← pow_succ']
    congr 1
    ring
  have h2 : t ^ (2 ^ k + 1) * (t ^ 2 ^ k)⁻¹ = (t ^ 2 ^ (k + 1)) ^ 2 ^ k := by
    rw [hc, pow_succ, mul_comm, inv_mul_cancel_left]
  funext j
  fin_cases j
  · exact h1
  · exact h2

omit [Finite K] [CharP K 2] in
theorem uc22p218c_pow_mem_suzuki {k : ℕ} {t : Kˣ} (ht : t ^ 2 ^ (2 * k + 1) = t) (a : ℕ) :
    (t ^ a) ^ 2 ^ (2 * k + 1) = t ^ a := by
  rw [← pow_mul, mul_comm, pow_mul, ht]

omit [Finite K] [CharP K 2] in
theorem uc22p218c_iterate_spTau_suzuki {k : ℕ} {t : Kˣ} (ht : t ^ 2 ^ (2 * k + 1) = t) (ε : ℕ) :
    spTau^[ε] ![t ^ (2 ^ k + 1), t ^ 2 ^ k] =
      ![(t ^ 2 ^ ((k + 1) * ε)) ^ (2 ^ k + 1), (t ^ 2 ^ ((k + 1) * ε)) ^ 2 ^ k] := by
  induction ε with
  | zero => simp
  | succ ε ih =>
    have h2 : (t ^ 2 ^ ((k + 1) * ε)) ^ 2 ^ (k + 1) = t ^ 2 ^ ((k + 1) * (ε + 1)) := by
      rw [← pow_mul, ← pow_add, mul_add_one]
    rw [Function.iterate_succ_apply', ih, uc22p218c_spTau_suzuki (uc22p218c_pow_mem_suzuki ht _), h2]

omit [Finite K] [CharP K 2] in
theorem uc22p218c_suzuki_pow (k : ℕ) (u : Kˣ) (m : ℕ) :
    (![u ^ (2 ^ k + 1), u ^ 2 ^ k] : Fin 2 → Kˣ) ^ m = ![(u ^ m) ^ (2 ^ k + 1), (u ^ m) ^ 2 ^ k] := by
  funext j
  fin_cases j
  · show (u ^ (2 ^ k + 1)) ^ m = (u ^ m) ^ (2 ^ k + 1)
    rw [← pow_mul, ← pow_mul, mul_comm]
  · show (u ^ 2 ^ k) ^ m = (u ^ m) ^ 2 ^ k
    rw [← pow_mul, ← pow_mul, mul_comm]

omit [Finite K] in
theorem uc22p218c_sp4T_injective : Function.Injective (sp4T K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  exact (sp4T_mem_iff t).1 (by rw [ht]; exact one_mem _)

omit [Finite K] in
theorem uc22p218c_orderOf_sp4T_suzuki (k : ℕ) (t : Kˣ) :
    orderOf (sp4T K ![t ^ (2 ^ k + 1), t ^ 2 ^ k]) = orderOf t := by
  let δ : Kˣ →* (Fin 2 → Kˣ) := MonoidHom.pi fun j => powMonoidHom (![2 ^ k + 1, 2 ^ k] j)
  have hδ : δ t = ![t ^ (2 ^ k + 1), t ^ 2 ^ k] := by
    funext j
    fin_cases j <;> rfl
  have hinj : Function.Injective ((sp4T K).comp δ) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : δ u = 1 := uc22p218c_sp4T_injective (by rw [map_one]; exact hu)
    have h0 : u ^ (2 ^ k + 1) = 1 := congrFun h1 0
    have h1' : u ^ 2 ^ k = 1 := congrFun h1 1
    rwa [pow_succ, h1', one_mul] at h0
  rw [← hδ, ← MonoidHom.comp_apply, orderOf_injective _ hinj]

theorem uc22p218c_sp4T_suzuki_mem_centMod {k : ℕ} {t : Kˣ} (ht : t ^ 2 ^ (2 * k + 1) = t)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα : ∃ e : ℕ, α ^ 2 ^ e = 1)
    (hαU : (projUnipotent 2 K).map α.toMonoidHom = projUnipotent 2 K) :
    sp4T K ![t ^ (2 ^ k + 1), t ^ 2 ^ k] ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod (projUnipotent 2 K) α := by
  obtain ⟨e, he⟩ := hα
  obtain ⟨i, ε, -, hact⟩ := uc22p218c_exists_torus_action α hαU
  have hρ : ∀ u : Kˣ, u ^ 2 ^ (2 * k + 1) = u →
      (spTau^[ε] ![u ^ (2 ^ k + 1), u ^ 2 ^ k]) ^ 2 ^ i =
        ![(u ^ 2 ^ ((k + 1) * ε + i)) ^ (2 ^ k + 1), (u ^ 2 ^ ((k + 1) * ε + i)) ^ 2 ^ k] := by
    intro u hu
    have h2 : (u ^ 2 ^ ((k + 1) * ε)) ^ 2 ^ i = u ^ 2 ^ ((k + 1) * ε + i) := by
      rw [← pow_mul, ← pow_add]
    rw [uc22p218c_iterate_spTau_suzuki hu, uc22p218c_suzuki_pow, h2]
  have hiter : ∀ j, (fun x => (spTau^[ε] x) ^ 2 ^ i)^[j] ![t ^ (2 ^ k + 1), t ^ 2 ^ k] =
      ![(t ^ 2 ^ (((k + 1) * ε + i) * j)) ^ (2 ^ k + 1), (t ^ 2 ^ (((k + 1) * ε + i) * j)) ^ 2 ^ k] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h2 : (t ^ 2 ^ (((k + 1) * ε + i) * j)) ^ 2 ^ ((k + 1) * ε + i) =
          t ^ 2 ^ (((k + 1) * ε + i) * (j + 1)) := by
        rw [← pow_mul, ← pow_add, mul_add_one]
      rw [Function.iterate_succ_apply', ih, hρ _ (uc22p218c_pow_mem_suzuki ht _), h2]
  have h1 := uc22p218c_iterate_mul_inv_mem hαU (sp4T K) (fun x => (spTau^[ε] x) ^ 2 ^ i) hact (2 ^ e)
    ![t ^ (2 ^ k + 1), t ^ 2 ^ k]
  rw [he, MulAut.one_apply, hiter, ← map_inv, ← map_mul, sp4T_mem_iff] at h1
  have e0 := congrFun h1 0
  have e1 := congrFun h1 1
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_inv_eq_one] at e0 e1
  rw [pow_succ, pow_succ, e1] at e0
  have h3 := uc22p218c_pow_two_pow_eq_of_mul_two_pow ⟨k, rfl⟩ ht e (mul_left_cancel e0).symm
  refine mem_centMod.2 ⟨sp4T_range_le ⟨_, rfl⟩, ?_⟩
  have h4 := hact ![t ^ (2 ^ k + 1), t ^ 2 ^ k]
  rwa [hρ t ht, h3] at h4

theorem uc22p218c_exists_elemAbelian_torus {r : ℕ} (hr : r.Prime) (hrK : r ∣ Nat.card K - 1) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≤ normalizer ((projUnipotent 2 K :
      Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rw [Nat.card_units]; exact hrK)
  let f : (Fin 2 → ↥(zpowers ζ)) →* StatedProj (StatedSp 2 K) :=
    (sp4T K).comp ((zpowers ζ).subtype.compLeft (Fin 2))
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := uc22p218c_sp4T_injective hab
    funext j
    exact Subtype.ext (congrFun h1 j)
  have hpow : ∀ x : ↥(zpowers ζ), x ^ r = 1 := fun x => by
    rw [← hζ, ← Nat.card_zpowers]
    exact pow_card_eq_one'
  refine ⟨(⊤ : Subgroup (Fin 2 → ↥(zpowers ζ))).map f, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact sp4T_range_le ⟨_, rfl⟩
  · refine CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun x _ => ?_⟩ f
    funext j
    exact hpow (x j)
  · rw [Subgroup.card_map_of_injective hf, Subgroup.card_top, Nat.card_pi, Fin.prod_univ_two,
      Nat.card_zpowers, hζ, sq]

theorem uc22p218c_pRank_model {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : r ∣ Nat.card K - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSp 2 K))) = 2 := by
  apply le_antisymm
  · rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (CFSG.PGLModel.projSpEquivStatedProj 2 K)]
    exact CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le hr hr2
      (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hr hr2)
  · obtain ⟨E, -, hE, hcard⟩ := uc22p218c_exists_elemAbelian_torus hr hrK
    exact CFSG.SectionRank.le_pRank hr.one_lt le_top hE hcard

theorem uc22p218c_exists_mulEquiv_map {X : Type} [Group X] (e : X ≃* StatedProj (StatedSp 2 K))
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ φ : StatedProj (StatedSp 2 K) ≃* X, (projUnipotent 2 K).map φ.toMonoidHom = U := by
  have hU₁ : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := isSylowTwoOf_map_symm e.symm hU
  obtain ⟨g, hg⟩ := exists_map_conj_eq isSylowTwoOf_projUnipotent_two hU₁
  refine ⟨(MulAut.conj g).trans e.symm, ?_⟩
  show (projUnipotent 2 K).map (e.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = U
  rw [← Subgroup.map_map, hg]
  exact map_map_symm e.symm U

end Model

section Abstract

variable {X : Type} [Group X]

theorem uc22p218c_exists_mem_centMod_sp4 {n s : ℕ} (hX : IsSp4 X n) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hs : Odd s) (hsn : s ∣ n) :
    ∃ d : X, orderOf d = 2 ^ s - 1 ∧ ∀ α : MulAut X, (∃ e : ℕ, α ^ 2 ^ e = 1) →
      U.map α.toMonoidHom = U → d ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod U α := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  obtain ⟨φ, hφ⟩ := uc22p218c_exists_mulEquiv_map e hU
  obtain ⟨t, ht⟩ := uc22p218c_exists_orderOf_units hK hsn
  obtain ⟨k, rfl⟩ := hs
  have ht' : t ^ 2 ^ (2 * k + 1) = t := by
    have h1 : t ^ (2 ^ (2 * k + 1) - 1) = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := 2 * k + 1)), pow_succ, h1, one_mul]
  refine ⟨φ (sp4T K ![t ^ (2 ^ k + 1), t ^ 2 ^ k]), ?_, fun α hα hαU => ?_⟩
  · rw [MulEquiv.orderOf_eq, uc22p218c_orderOf_sp4T_suzuki, ht]
  · rw [← hφ, CFSG.Quasithin.H13.L32A.C.SkPf.centMod_map]
    refine mem_map_of_mem _ (uc22p218c_sp4T_suzuki_mem_centMod ht' (pow_two_pow_congr φ hα)
      (map_congr_symm_eq φ ?_))
    rw [hφ]
    exact hαU

theorem uc22p218c_pRank_eq_two_sp4 [Finite X] {n r : ℕ} (hX : IsSp4 X n) (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup X) = 2 := by
  obtain ⟨⟨-, hn1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact uc22p218c_pRank_model hr (uc22p218c_ne_two_of_dvd hn1 hrn) (by rw [hK]; exact hrn)

end Abstract

section Group

variable {G : Type} [Group G] [Finite G]

theorem uc22p218c_pRank_eq_two_of_bar2 {L : Subgroup G} {n r : ℕ} (hX : IsSp4 (Bar2 L) n) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : CFSG.Open.pRank r L = 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨-, hn1, -, -⟩, -⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hN : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro h
    exact uc22p218c_ne_two_of_dvd hn1 hrn ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN]
  exact uc22p218c_pRank_eq_two_sp4 hX hr hrn

theorem uc22p218c_conj_mul_inv_mem_of_mem_centMod {L : Subgroup G} (Q : Sylow 2 ↥L) {t : G}
    (htL : t ∈ normalizer (L : Set G)) {x : ↥L}
    (hx : (QuotientGroup.mk x : Bar2 L) ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod
      ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) (rhoL L ⟨t, htL⟩)) :
    t * (x : G) * t⁻¹ * (x : G)⁻¹ ∈ (Q : Subgroup ↥L).map L.subtype := by
  obtain ⟨-, hx2⟩ := mem_centMod.1 hx
  rw [rhoL_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hx2
  obtain ⟨q, hq, hqe⟩ := mem_map.1 hx2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hqe
  have h1 := mul_mem hq (CFSG.fitting_pCore_le_sylow Q hqe)
  rw [mul_inv_cancel_left] at h1
  refine mem_map.2 ⟨_, h1, ?_⟩
  simp [rhoL_mk_coe]

theorem uc22p218c_rhoL_pow_and_map {L : Subgroup G} (Q : Sylow 2 ↥L) {t : G} (htL : t ∈ normalizer (L : Set G))
    (htS : t ∈ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup G) : Set G)) (ht : ∃ a : ℕ, t ^ 2 ^ a = 1) :
    (∃ e : ℕ, rhoL L ⟨t, htL⟩ ^ 2 ^ e = 1) ∧
      ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map (rhoL L ⟨t, htL⟩).toMonoidHom =
        (Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
  obtain ⟨a, ha⟩ := ht
  refine ⟨⟨a, ?_⟩, CFSG.Quasithin.H13.L32A.C.SkPf.map_eq_of_forall_mem fun u hu => ?_⟩
  · have h1 : (⟨t, htL⟩ : ↥(normalizer (L : Set G))) ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha)
    rw [← map_pow, h1, map_one]
  · obtain ⟨q, hq, rfl⟩ := mem_map.1 hu
    have h1 : ((Subgroup.normalizerMonoidHom L ⟨t, htL⟩ q : ↥L) : G) ∈ (Q : Subgroup ↥L).map L.subtype := by
      rw [rhoL_mk_coe]
      exact (mem_normalizer_iff.1 htS q).1 (mem_map_of_mem L.subtype hq)
    exact mem_map.2 ⟨_, (mem_map_iff_mem L.subtype_injective).1 h1, (rhoL_mk L ⟨t, htL⟩ q).symm⟩

theorem uc22p218c_exists_conj_mul_inv_mem_sp4 {L S : Subgroup G} {n s : ℕ} (hS : IsSylowOf 2 S L)
    (hX : IsSp4 (Bar2 L) n) (hs : Odd s) (hsn : s ∣ n) :
    ∃ d ∈ L, orderOf d = 2 ^ s - 1 ∧ ∀ x ∈ zpowers d, ∀ t ∈ normalizer (L : Set G),
      t ∈ normalizer (S : Set G) → (∃ a : ℕ, t ^ 2 ^ a = 1) → t * x * t⁻¹ * x⁻¹ ∈ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hSb : IsSylowTwoOf ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) ⊤ :=
    isSylowTwoOf_sylow (Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)))
  obtain ⟨db, hdb, hcent⟩ := uc22p218c_exists_mem_centMod_sp4 hX hSb hs hsn
  obtain ⟨d₀, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) db
  have hd₀ : d₀ ^ (2 ^ s - 1) ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_pow, ← hdb]
    exact pow_orderOf_eq_one _
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hd₀⟩
  have hc' : (d₀ ^ (2 ^ s - 1)) ^ 2 ^ c = 1 := congrArg Subtype.val hc
  have hodd : Odd (2 ^ s - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hs.pos.ne'⟩) odd_one
  have hcop : (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) d₀)).Coprime (2 ^ c) := by
    rw [hdb]
    exact (Nat.coprime_two_right.2 hodd).pow_right c
  have hmk : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (d₀ ^ 2 ^ c)) = 2 ^ s - 1 := by
    rw [map_pow, hcop.orderOf_pow, hdb]
  have hord : orderOf (d₀ ^ 2 ^ c) = 2 ^ s - 1 := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
    · rw [← pow_mul, mul_comm (2 ^ c), pow_mul, hc']
    · rw [← hmk]
      exact orderOf_map_dvd _ _
  refine ⟨((d₀ ^ 2 ^ c : ↥L) : G), (d₀ ^ 2 ^ c).2, by rw [Subgroup.orderOf_coe, hord], ?_⟩
  intro x hx t htL htS ht
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  obtain ⟨hα, hαU⟩ := uc22p218c_rhoL_pow_and_map Q htL htS ht
  have h1 : (QuotientGroup.mk ((d₀ ^ 2 ^ c) ^ m) : Bar2 L) ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod
      ((Q : Subgroup ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) (rhoL L ⟨t, htL⟩) := by
    rw [QuotientGroup.mk_zpow, QuotientGroup.mk_pow]
    exact zpow_mem (pow_mem (hcent _ hα hαU) _) m
  have h2 := uc22p218c_conj_mul_inv_mem_of_mem_centMod Q htL h1
  rwa [Subgroup.coe_zpow] at h2

theorem uc22p218c_exists_mem_normalizer_sp4 {L T : Subgroup G} {n s : ℕ} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L) (hX : IsSp4 (Bar2 L) n) (hs : Odd s)
    (hsn : s ∣ n) : ∃ d ∈ L, orderOf d = 2 ^ s - 1 ∧ zpowers d ≤ normalizer (T : Set G) := by
  obtain ⟨d, hdL, hd, hcomm⟩ := uc22p218c_exists_conj_mul_inv_mem_sp4 hS hX hs hsn
  have key : ∀ x ∈ zpowers d, ∀ h ∈ T, x * h * x⁻¹ ∈ T := by
    intro x hx h hh
    have hhL : h⁻¹ ∈ normalizer (L : Set G) := hTL (inv_mem hh)
    have hhS : h⁻¹ ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.1 (le_normalizer (inv_mem hh)) y, ← mem_normalizer_iff.1 hhL y]
    obtain ⟨a, ha⟩ := hT ⟨h⁻¹, inv_mem hh⟩
    have h1 := hcomm x hx h⁻¹ hhL hhS ⟨a, congrArg Subtype.val ha⟩
    have e : x * h * x⁻¹ = h * (h⁻¹ * x * h⁻¹⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hh (mem_inf.1 h1).1
  refine ⟨d, hdL, hd, fun x hx => mem_normalizer_iff.2 fun h => ⟨key x hx h, fun hh => ?_⟩⟩
  have h1 := key x⁻¹ (inv_mem hx) _ hh
  rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h1

theorem uc22p218c_exists_orderOf_eq_mem_normalizer_sp4 {L T : Subgroup G} {n s r : ℕ} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L) (hX : IsSp4 (Bar2 L) n) (hs : Odd s)
    (hsn : s ∣ n) (hr : r ∣ 2 ^ s - 1) : ∃ y ∈ L, orderOf y = r ∧ zpowers y ≤ normalizer (T : Set G) := by
  obtain ⟨d, hdL, hd, hdN⟩ := uc22p218c_exists_mem_normalizer_sp4 hT hTL hS hX hs hsn
  refine ⟨d ^ ((2 ^ s - 1) / r), pow_mem hdL _, ?_, (zpowers_le.2 (pow_mem (mem_zpowers d) _)).trans hdN⟩
  have h0 : orderOf d ≠ 0 := by
    rw [hd]
    have := Nat.one_lt_two_pow hs.pos.ne'
    omega
  rw [← hd]
  exact orderOf_pow_orderOf_div h0 (by rw [hd]; exact hr)

end Group

end CFSG.LocalAnalysis.UniquenessCase.UC22
