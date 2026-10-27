module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26b
public import Certificates.Certificate7251
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Hat7
import all Mathlib.GroupTheory.Perm.Cycle.Factors
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Equiv
open scoped commutatorElement

namespace HatA7L

@[expose] def c1 : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def c2 : Perm (Fin 7) := swap 3 4 * swap 4 5

@[expose] def w : Perm (Fin 7) := swap 0 3 * swap 1 4 * swap 2 5

@[expose] def jc : Perm (Fin 7) := swap 0 1 * swap 4 5

@[expose] def jd : Perm (Fin 7) := swap 0 1 * swap 3 4

theorem sign_t0 : Perm.sign HatA7Loc.t0 = 1 := by decide
theorem sign_c : Perm.sign HatA7Loc.c = 1 := by decide
theorem sign_d : Perm.sign HatA7Loc.d = 1 := by decide
theorem sign_c1 : Perm.sign c1 = 1 := by decide
theorem sign_c2 : Perm.sign c2 = 1 := by decide
theorem sign_jc : Perm.sign jc = 1 := by decide
theorem sign_jd : Perm.sign jd = 1 := by decide
theorem sign_w : Perm.sign w = -1 := by decide
theorem cycleType_t0 : HatA7Loc.t0.cycleType = Multiset.replicate 2 2 := by decide
theorem cycleType_c : HatA7Loc.c.cycleType = Multiset.replicate 1 3 := by decide
theorem cycleType_d : HatA7Loc.d.cycleType = Multiset.replicate 2 3 := by decide
theorem card_support_t0 : HatA7Loc.t0.support.card = 4 := by decide
theorem w_comm : w * HatA7Loc.d = HatA7Loc.d * w := by decide
theorem jc_inv : jc * HatA7Loc.c * jc⁻¹ = HatA7Loc.c⁻¹ := by decide
theorem jd_inv : jd * HatA7Loc.d * jd⁻¹ = HatA7Loc.d⁻¹ := by decide
theorem c1_c2 : c1 * c2 = c2 * c1 := by decide
theorem swap_c1 : swap (0 : Fin 7) 1 * c1 * swap 0 1 = c1⁻¹ := by decide
theorem swap_c2 : swap (0 : Fin 7) 1 * c2 * swap 0 1 = c2 := by decide
theorem c1_pow : c1 ^ 3 = 1 := by decide
theorem c2_pow : c2 ^ 3 = 1 := by decide
theorem c1_ne : c1 ≠ 1 ∧ c1 ≠ c2 ∧ c1 ≠ c2 ^ 2 := by decide
theorem sign_v2 : Perm.sign HatA7Loc.v2 = 1 := by decide
theorem t0_c : HatA7Loc.t0 * HatA7Loc.c = HatA7Loc.c * HatA7Loc.t0 := by decide
theorem v2_c : HatA7Loc.v2 * HatA7Loc.c = HatA7Loc.c * HatA7Loc.v2 := by decide
theorem t0_v2 : HatA7Loc.t0 * HatA7Loc.v2 = HatA7Loc.v2 * HatA7Loc.t0 := by decide
theorem v3_eq : HatA7Loc.v3 = HatA7Loc.t0 * HatA7Loc.v2 := by decide
theorem t0_sq : HatA7Loc.t0 ^ 2 = 1 := by decide
theorem v2_sq : HatA7Loc.v2 ^ 2 = 1 := by decide
theorem c_pow : HatA7Loc.c ^ 3 = 1 := by decide
theorem c_ne : HatA7Loc.c ≠ 1 := by decide
theorem d_pow : HatA7Loc.d ^ 3 = 1 := by decide
theorem d_ne : HatA7Loc.d ≠ 1 := by decide
theorem c1_c : c1 * HatA7Loc.c = HatA7Loc.c * c1 := by decide
theorem c1_ne_c : c1 ≠ 1 ∧ c1 ≠ HatA7Loc.c ∧ c1 ≠ HatA7Loc.c ^ 2 := by decide

abbrev A7 : Type := ↥(alternatingGroup (Fin 7))

@[expose] def t0' : A7 := ⟨HatA7Loc.t0, sign_t0⟩

@[expose] def c' : A7 := ⟨HatA7Loc.c, sign_c⟩

@[expose] def d' : A7 := ⟨HatA7Loc.d, sign_d⟩

theorem cycleType_of_pow {p : ℕ} [Fact p.Prime] (σ : A7) (hp : σ ^ p = 1) (h1 : σ ≠ 1) :
    ∃ m : ℕ, (σ : Perm (Fin 7)).cycleType = Multiset.replicate m p ∧ m ≠ 0 ∧ m * p ≤ 7 := by
  have hs : (σ : Perm (Fin 7)) ^ p = 1 := by simpa using congrArg Subtype.val hp
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hs
  refine ⟨_, hct, fun h => h1 (Subtype.ext ?_), ?_⟩
  · rw [Multiset.card_eq_zero, Equiv.Perm.cycleType_eq_zero] at h
    exact h
  · have h7 := (Finset.card_le_univ (σ : Perm (Fin 7)).support).trans_eq (Fintype.card_fin 7)
    rw [← Equiv.Perm.sum_cycleType, hct, Multiset.sum_replicate, smul_eq_mul] at h7
    exact h7

theorem exists_conj_t0 (σ : A7) (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    ∃ g : A7, g * σ * g⁻¹ = t0' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hct, hm0, hm7⟩ := cycleType_of_pow σ h2 h1
  have hsign : Perm.sign (σ : Perm (Fin 7)) = 1 := σ.2
  rw [Equiv.Perm.sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hm2 : m = 2 := by
    have hm3 : m ≤ 3 := by omega
    interval_cases m
    · omega
    · exact absurd hsign (by decide)
    · rfl
    · exact absurd hsign (by decide)
  have hc : IsConj (t0' : Perm (Fin 7)) (σ : Perm (Fin 7)) := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hct, hm2]
    exact cycleType_t0
  have hsupp : (t0' : Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [show (t0' : Perm (Fin 7)) = HatA7Loc.t0 from rfl, card_support_t0, Fintype.card_fin]
    norm_num
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.isConj_of hc hsupp)
  exact ⟨g⁻¹, by rw [← hg]; group⟩

theorem exists_conj_three (σ : A7) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    (∃ g : A7, g * σ * g⁻¹ = c') ∨ ∃ g : A7, g * σ * g⁻¹ = d' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hct, hm0, hm7⟩ := cycleType_of_pow σ h3 h1
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl
  · left
    have hσ3 : (σ : Perm (Fin 7)).IsThreeCycle := by
      rw [Equiv.Perm.IsThreeCycle, hct]
      rfl
    have hc3 : (c' : Perm (Fin 7)).IsThreeCycle := by
      rw [Equiv.Perm.IsThreeCycle, show (c' : Perm (Fin 7)) = HatA7Loc.c from rfl, cycleType_c]
      rfl
    have h5 : 5 ≤ Nat.card (Fin 7) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
    obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.isThreeCycle_isConj h5 hσ3 hc3)
    exact ⟨g, hg⟩
  · right
    have hc : IsConj HatA7Loc.d (σ : Perm (Fin 7)) := by
      rw [Equiv.Perm.isConj_iff_cycleType_eq, hct]
      exact cycleType_d
    obtain ⟨π₀, hπ₀⟩ := isConj_iff.mp hc
    by_cases he : Perm.sign π₀ = 1
    · refine ⟨(⟨π₀, he⟩ : A7)⁻¹, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hπ₀]
      group
      rfl
    · have he' : Perm.sign (π₀ * w) = 1 := by
        rw [Perm.sign_mul, sign_w]
        rcases Int.units_eq_one_or (Perm.sign π₀) with h | h
        · exact absurd h he
        · rw [h]
          rfl
      refine ⟨(⟨π₀ * w, he'⟩ : A7)⁻¹, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hπ₀]
      calc (π₀ * w)⁻¹ * (π₀ * HatA7Loc.d * π₀⁻¹) * (π₀ * w)⁻¹⁻¹ =
          w⁻¹ * (HatA7Loc.d * w) := by group
        _ = w⁻¹ * (w * HatA7Loc.d) := by rw [← w_comm]
        _ = HatA7Loc.d := by group

theorem exists_inv (σ : A7) (h3 : σ ^ 3 = 1) : ∃ τ : A7, τ * σ * τ⁻¹ = σ⁻¹ := by
  by_cases h1 : σ = 1
  · exact ⟨1, by rw [h1]; group⟩
  rcases exists_conj_three σ h3 h1 with ⟨g, hg⟩ | ⟨g, hg⟩
  · refine ⟨g⁻¹ * ⟨jc, sign_jc⟩ * g, ?_⟩
    have hj : (⟨jc, sign_jc⟩ : A7) * c' * (⟨jc, sign_jc⟩ : A7)⁻¹ = c'⁻¹ := Subtype.ext jc_inv
    have hσ : σ = g⁻¹ * c' * g := by rw [← hg]; group
    rw [hσ]
    calc g⁻¹ * ⟨jc, sign_jc⟩ * g * (g⁻¹ * c' * g) * (g⁻¹ * ⟨jc, sign_jc⟩ * g)⁻¹ =
        g⁻¹ * ((⟨jc, sign_jc⟩ : A7) * c' * (⟨jc, sign_jc⟩ : A7)⁻¹) * g := by group
      _ = (g⁻¹ * c' * g)⁻¹ := by rw [hj]; group
  · refine ⟨g⁻¹ * ⟨jd, sign_jd⟩ * g, ?_⟩
    have hj : (⟨jd, sign_jd⟩ : A7) * d' * (⟨jd, sign_jd⟩ : A7)⁻¹ = d'⁻¹ := Subtype.ext jd_inv
    have hσ : σ = g⁻¹ * d' * g := by rw [← hg]; group
    rw [hσ]
    calc g⁻¹ * ⟨jd, sign_jd⟩ * g * (g⁻¹ * d' * g) * (g⁻¹ * ⟨jd, sign_jd⟩ * g)⁻¹ =
        g⁻¹ * ((⟨jd, sign_jd⟩ : A7) * d' * (⟨jd, sign_jd⟩ : A7)⁻¹) * g := by group
      _ = (g⁻¹ * d' * g)⁻¹ := by rw [hj]; group

variable {X : Type} [Group X]

noncomputable def proj (hX : IsHat X (alternatingGroup (Fin 7))) : X →* A7 :=
  (Classical.choice hX.2.2).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))

theorem proj_surjective (hX : IsHat X (alternatingGroup (Fin 7))) :
    Function.Surjective (proj hX) :=
  (Classical.choice hX.2.2).surjective.comp (QuotientGroup.mk'_surjective _)

theorem proj_eq_one_iff (hX : IsHat X (alternatingGroup (Fin 7))) (x : X) :
    proj hX x = 1 ↔ x ∈ Subgroup.center X := by
  rw [proj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem proj_eq_iff (hX : IsHat X (alternatingGroup (Fin 7))) (x y : X) :
    proj hX x = proj hX y ↔ x⁻¹ * y ∈ Subgroup.center X := by
  rw [← proj_eq_one_iff hX, map_mul, map_inv, inv_mul_eq_one]

theorem pow_three_center (hX : IsHat X (alternatingGroup (Fin 7))) {z : X}
    (hz : z ∈ Subgroup.center X) : z ^ 3 = 1 := by
  have : Finite ↥(Subgroup.center X) := Nat.finite_of_card_ne_zero (by rw [hX.2.1]; norm_num)
  have h := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := ⟨z, hz⟩)
  rw [hX.2.1] at h
  exact congrArg Subtype.val h

theorem cube_eq_one (hX : IsHat X (alternatingGroup (Fin 7))) {s : X}
    (hs : s ^ 3 ∈ Subgroup.center X) : s ^ 3 = 1 := by
  have h3 : (proj hX s) ^ 3 = 1 := by rw [← map_pow]; exact (proj_eq_one_iff hX _).mpr hs
  obtain ⟨τ, hτ⟩ := exists_inv (proj hX s) h3
  obtain ⟨t, rfl⟩ := proj_surjective hX τ
  have hζ : s * (t * s * t⁻¹) ∈ Subgroup.center X := by
    have := (proj_eq_iff hX s⁻¹ (t * s * t⁻¹)).mp (by rw [map_mul, map_mul, map_inv, map_inv, hτ])
    simpa using this
  have e1 : t * s * t⁻¹ = s⁻¹ * (s * (t * s * t⁻¹)) := by group
  have e2 : (t * s * t⁻¹) ^ 3 = s ^ 3 := by
    rw [conj_pow, (Subgroup.mem_center_iff.mp hs t)]
    group
  have hc : Commute s⁻¹ (s * (t * s * t⁻¹)) := (Subgroup.mem_center_iff.mp hζ s⁻¹)
  have e3 : (s⁻¹ * (s * (t * s * t⁻¹))) ^ 3 = (s ^ 3)⁻¹ := by
    rw [hc.mul_pow, pow_three_center hX hζ, mul_one, inv_pow]
  have h4 : s ^ 3 = (s ^ 3)⁻¹ := by rw [← e3, ← e1, e2]
  have h5 : (s ^ 3) ^ 3 = 1 := pow_three_center hX hs
  have h6 : (s ^ 3) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [h4]
    exact mul_inv_cancel _
  calc s ^ 3 = (s ^ 3) ^ 3 * ((s ^ 3) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h5, h6, inv_one, mul_one]

theorem card_eq_inf_ker_mul_map {Y : Type} [Group Y] (f : X →* Y) (K : Subgroup X) :
    Nat.card K = Nat.card ↥(K ⊓ f.ker) * Nat.card ↥(K.map f) := by
  let g : ↥K →* Y := f.comp K.subtype
  have hrange : g.range = K.map f := by
    ext y
    simp [g, MonoidHom.mem_range, Subgroup.mem_map]
  have hker : Nat.card g.ker = Nat.card ↥(K ⊓ f.ker) := by
    have e : g.ker = f.ker.subgroupOf K := by
      ext x
      simp [g, Subgroup.mem_subgroupOf]
    rw [e, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker, mul_comm]

theorem ker_proj (hX : IsHat X (alternatingGroup (Fin 7))) :
    (proj hX).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, proj_eq_one_iff]

theorem card_comap_proj (hX : IsHat X (alternatingGroup (Fin 7))) (H : Subgroup A7) :
    Nat.card ↥(H.comap (proj hX)) = Nat.card H * 3 := by
  rw [card_eq_inf_ker_mul_map (proj hX), Subgroup.map_comap_eq_self_of_surjective
    (proj_surjective hX), ker_proj, inf_eq_right.mpr, hX.2.1, mul_comm]
  intro z hz
  show proj hX z ∈ H
  rw [(proj_eq_one_iff hX z).mpr hz]
  exact H.one_mem

theorem card_closure_pair {a b : A7} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hab : a * b = b * a) (hn : a ≠ 1 ∧ a ≠ b ∧ a ≠ b ^ 2) :
    Nat.card ↥(Subgroup.closure ({a, b} : Set A7)) = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k : Set A7 := {a, b} with hk
  have hpw : k.Pairwise Commute := by
    rintro x (rfl | rfl) y (rfl | rfl) _
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcl := (Subgroup.isMulCommutative_closure hpw).is_comm
  have hpow3 : ∀ x ∈ Subgroup.closure k, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := congrArg Subtype.val
        (hcl.comm (⟨x, hx⟩ : ↥(Subgroup.closure k)) ⟨y, hy⟩)
      rw [(Commute.mul_pow hxy 3), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hP : IsPGroup 3 ↥(Subgroup.closure k) := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hpow3 x x.2)⟩
  obtain ⟨n, hn'⟩ := hP.exists_card_eq
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hlt : Subgroup.zpowers b < Subgroup.closure k := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp [hk])))
      fun h => ?_
    have ha' : a ∈ Subgroup.zpowers b := h ▸ Subgroup.subset_closure (by simp [hk])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have hm3 : b ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hb
    rw [zpow_eq_zpow_emod m hm3] at hm
    have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    obtain ⟨hne1, hne2, hne3⟩ := hn
    rcases hcases with h0 | h0 | h0 <;> rw [h0] at hm
    · exact hne1 hm.symm
    · exact hne2 (by simpa using hm.symm)
    · exact hne3 (by simpa [zpow_ofNat] using hm.symm)
  have hgt : 3 < Nat.card ↥(Subgroup.closure k) := by
    have h1 := Subgroup.card_dvd_of_le hlt.le
    rw [Nat.card_zpowers, hbo] at h1
    have h2 : Nat.card ↥(Subgroup.zpowers b) ≠ Nat.card ↥(Subgroup.closure k) := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.ge)
    rw [Nat.card_zpowers, hbo] at h2
    exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h1) h2
  have hdvd : Nat.card ↥(Subgroup.closure k) ∣ 2520 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.closure k)
    rwa [Nat.card_eq_fintype_card (α := A7), card_alternatingGroup, Fintype.card_fin] at this
  rw [hn'] at hgt hdvd ⊢
  rcases n with _ | _ | _ | n
  · norm_num at hgt
  · norm_num at hgt
  · norm_num
  · exfalso
    have : 27 ∣ 2520 := (pow_dvd_pow 3 (show 3 ≤ n + 3 by omega)).trans hdvd
    norm_num at this

theorem c2_ne : c2 ≠ 1 := by decide

theorem card_closure_c1c2 :
    Nat.card ↥(Subgroup.closure ({⟨c1, sign_c1⟩, ⟨c2, sign_c2⟩} : Set A7)) = 9 := by
  obtain ⟨h1, h2, h3⟩ := c1_ne
  refine card_closure_pair (Subtype.ext c1_pow) (Subtype.ext c2_pow)
    (fun h => c2_ne (congrArg Subtype.val h)) (Subtype.ext c1_c2) ⟨fun h => h1 (congrArg
      Subtype.val h), fun h => h2 (congrArg Subtype.val h), fun h => h3 (by
        simpa using congrArg Subtype.val h)⟩

noncomputable def ind (hX : IsHat X (alternatingGroup (Fin 7))) (α : MulAut X) : MulAut A7 :=
  ((Classical.choice hX.2.2).symm.trans (QuotientGroup.congr (Subgroup.center X)
    (Subgroup.center X) α (Subgroup.map_center_eq α))).trans (Classical.choice hX.2.2)

theorem ind_proj (hX : IsHat X (alternatingGroup (Fin 7))) (α : MulAut X) (x : X) :
    ind hX α (proj hX x) = proj hX (α x) := by
  simp only [ind, proj, MulEquiv.trans_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, MulEquiv.symm_apply_apply]
  rfl

theorem ind_mul (hX : IsHat X (alternatingGroup (Fin 7))) (α β : MulAut X) :
    ind hX (α * β) = ind hX α * ind hX β := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := proj_surjective hX y
  rw [MulAut.mul_apply, ind_proj, ind_proj, ind_proj, MulAut.mul_apply]

theorem ind_one (hX : IsHat X (alternatingGroup (Fin 7))) : ind hX 1 = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := proj_surjective hX y
  rw [ind_proj]
  rfl

theorem ind_pow (hX : IsHat X (alternatingGroup (Fin 7))) (α : MulAut X) (n : ℕ) :
    ind hX (α ^ n) = ind hX α ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ind_one]
  | succ n ih => rw [pow_succ, pow_succ, ind_mul, ih]

theorem exists_perm (hX : IsHat X (alternatingGroup (Fin 7))) (α : MulAut X) :
    ∃ σ : Perm (Fin 7), MulAut.conjNormal σ = ind hX α :=
  (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)).2 _

theorem proj_apply_of (hX : IsHat X (alternatingGroup (Fin 7))) {α : MulAut X}
    {σ : Perm (Fin 7)} (hσ : MulAut.conjNormal σ = ind hX α) (x : X) :
    ((proj hX (α x) : A7) : Perm (Fin 7)) = σ * (proj hX x : Perm (Fin 7)) * σ⁻¹ := by
  rw [← ind_proj, ← hσ, MulAut.conjNormal_apply]

theorem eq_of_inv_mul_mem_center [Group.IsPerfect X] {α β : MulAut X}
    (h : ∀ s, (β s)⁻¹ * α s ∈ Subgroup.center X) : α = β := by
  let z : X →* Subgroup.center X :=
    { toFun := fun s => ⟨(β s)⁻¹ * α s, h s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h s) ((β t)⁻¹)
        simp only [map_mul, _root_.mul_inv_rev, Subgroup.coe_mul]
        calc (β t)⁻¹ * (β s)⁻¹ * (α s * α t) = (β t)⁻¹ * ((β s)⁻¹ * α s) * α t := by group
          _ = (β s)⁻¹ * α s * (β t)⁻¹ * α t := by rw [hc]
          _ = (β s)⁻¹ * α s * ((β t)⁻¹ * α t) := by group }
  have hker : z.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := X)]
    exact Abelianization.commutator_subset_ker z
  refine MulEquiv.ext fun s => ?_
  have hs : s ∈ z.ker := hker ▸ Subgroup.mem_top s
  have h1 : (β s)⁻¹ * α s = 1 := congrArg Subtype.val hs
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem inner_of_even (hX : IsHat X (alternatingGroup (Fin 7))) {α : MulAut X}
    {σ : Perm (Fin 7)} (hσ : MulAut.conjNormal σ = ind hX α) (he : Perm.sign σ = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Group.IsPerfect X := hX.1.1
  obtain ⟨x₀, hx₀⟩ := proj_surjective hX ⟨σ, he⟩
  refine ⟨x₀, eq_of_inv_mul_mem_center fun s => ?_⟩
  rw [← proj_eq_one_iff hX]
  apply Subtype.ext
  have h1 := proj_apply_of hX hσ s
  simp only [map_mul, map_inv, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, h1, hx₀,
    OneMemClass.coe_one]
  group

theorem sign_of_odd (hX : IsHat X (alternatingGroup (Fin 7))) {α : MulAut X}
    {σ : Perm (Fin 7)} (hσ : MulAut.conjNormal σ = ind hX α) (hα : Odd (orderOf α)) :
    Perm.sign σ = 1 := by
  have hinj := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).1
  have h1 : MulAut.conjNormal (H := alternatingGroup (Fin 7)) (σ ^ orderOf α) = 1 := by
    rw [map_pow, hσ, ← ind_pow, pow_orderOf_eq_one, ind_one]
  have h2 : σ ^ orderOf α = 1 := hinj (h1.trans (map_one _).symm)
  have hσo : Odd (orderOf σ) := Odd.of_dvd_nat hα (orderOf_dvd_of_pow_eq_one h2)
  have h3 : Perm.sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := hσo
    rw [h, hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h3
    exact absurd h3 (by decide)

theorem comm_mul_center {g h ζ ξ : X} (hgh : g * h = h * g) (hζ : ζ ∈ Subgroup.center X)
    (hξ : ξ ∈ Subgroup.center X) : g * ζ * (h * ξ) = h * ξ * (g * ζ) := by
  have hζh : ζ * h = h * ζ := (Subgroup.mem_center_iff.mp hζ h).symm
  have hξg : g * ξ = ξ * g := Subgroup.mem_center_iff.mp hξ g
  have hζξ : ζ * ξ = ξ * ζ := (Subgroup.mem_center_iff.mp hζ ξ).symm
  calc g * ζ * (h * ξ) = g * (ζ * h) * ξ := by group
    _ = g * (h * ζ) * ξ := by rw [hζh]
    _ = (g * h) * (ζ * ξ) := by group
    _ = (h * g) * (ξ * ζ) := by rw [hgh, hζξ]
    _ = h * (g * ξ) * ζ := by group
    _ = h * (ξ * g) * ζ := by rw [hξg]
    _ = h * ξ * (g * ζ) := by group

theorem center_le_of_card_nine [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) {P : Subgroup X}
    (hP : Nat.card P = 9) : Subgroup.center X ≤ P := by
  classical
  by_contra hZP
  have hZ3 : Nat.card ↥(Subgroup.center X) = 3 := hX.2.1
  have hinf : Subgroup.center X ⊓ P = ⊥ := by
    have hd : Nat.card ↥(Subgroup.center X ⊓ P) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      apply hZP
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : Subgroup.center X ⊓ P ≤ _)
        (by rw [h, hZ3])
      rw [← this]
      exact inf_le_right
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPc : ∀ a b : ↥P, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP]; norm_num)).is_comm.comm
  have hcomm : ∀ (a : ↥P) (z : ↥(Subgroup.center X)),
      Commute (P.subtype a) ((Subgroup.center X).subtype z) := fun a z => by
    show (a : X) * z = z * a
    exact Subgroup.mem_center_iff.mp z.2 a
  let Φ := P.subtype.noncommCoprod (Subgroup.center X).subtype hcomm
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h1
    have h1' : (a : X) * z = 1 := h1
    have ha : (a : X) ∈ Subgroup.center X ⊓ P := by
      refine ⟨?_, a.2⟩
      rw [eq_inv_of_mul_eq_one_left h1']
      exact Subgroup.inv_mem _ z.2
    rw [hinf, Subgroup.mem_bot] at ha
    have hz : (z : X) = 1 := by rw [ha, one_mul] at h1'; exact h1'
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hz)
  have h27 : Nat.card Φ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hP, hZ3]
  obtain ⟨a, ha, b, hb, hab⟩ := CFSG.Quasithin.H13.factHatA7SylowThree_holds X hX Φ.range h27
  obtain ⟨⟨p, z⟩, rfl⟩ := ha
  obtain ⟨⟨p', z'⟩, rfl⟩ := hb
  apply hab
  simp only [Φ, MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype]
  exact comm_mul_center (congrArg Subtype.val (hPc p p')) z.2 z'.2

theorem comm_ne_one [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) {a b : X}
    (ha : proj hX a = ⟨c1, sign_c1⟩) (hb : proj hX b = ⟨c2, sign_c2⟩) : a * b ≠ b * a := by
  classical
  intro hab
  set k : Set A7 := {⟨c1, sign_c1⟩, ⟨c2, sign_c2⟩} with hk
  set S := (Subgroup.closure k).comap (proj hX) with hS
  have h27 : Nat.card S = 27 := by rw [hS, card_comap_proj, card_closure_c1c2]
  obtain ⟨x, hx, y, hy, hxy⟩ := CFSG.Quasithin.H13.factHatA7SylowThree_holds X hX S h27
  apply hxy
  have hmap : (Subgroup.closure ({a, b} : Set X)).map (proj hX) = Subgroup.closure k := by
    rw [MonoidHom.map_closure, Set.image_pair, ha, hb]
  have hpw : ({a, b} : Set X).Pairwise Commute := by
    rintro u (rfl | rfl) v (rfl | rfl) _
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcl := (Subgroup.isMulCommutative_closure hpw).is_comm
  have hdec : ∀ s ∈ S, ∃ t ∈ Subgroup.closure ({a, b} : Set X), t⁻¹ * s ∈ Subgroup.center X := by
    intro s hs
    have hs' : proj hX s ∈ (Subgroup.closure ({a, b} : Set X)).map (proj hX) := by
      rw [hmap]
      exact hs
    obtain ⟨t, ht, hts⟩ := hs'
    exact ⟨t, ht, (proj_eq_iff hX t s).mp hts⟩
  obtain ⟨t, ht, htx⟩ := hdec x hx
  obtain ⟨u, hu, huy⟩ := hdec y hy
  have hx' : x = t * (t⁻¹ * x) := by group
  have hy' : y = u * (u⁻¹ * y) := by group
  have htu : t * u = u * t := congrArg Subtype.val
    (hcl.comm (⟨t, ht⟩ : ↥(Subgroup.closure ({a, b} : Set X))) ⟨u, hu⟩)
  rw [hx', hy']
  exact comm_mul_center htu htx huy

theorem comm_mul_left {a z : X} (hz : z ∈ Subgroup.center X) (b : X) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_right (a : X) {b z : X} (hz : z ∈ Subgroup.center X) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a = a * z := (Subgroup.mem_center_iff.mp hz a).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by
        rw [show z * a⁻¹ = a⁻¹ * z from (Subgroup.mem_center_iff.mp hz a⁻¹).symm]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem sign_eq_one_of_fix [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) {α : MulAut X}
    {σ : Perm (Fin 7)} (hσ : MulAut.conjNormal σ = ind hX α)
    (hZ : ∀ z ∈ Subgroup.center X, α z = z) : Perm.sign σ = 1 := by
  by_contra he
  have he' : Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left he
  have hρ : Perm.sign (σ * swap 0 1) = 1 := by
    rw [Perm.sign_mul, he', Perm.sign_swap (by decide)]
    rfl
  obtain ⟨r, hr⟩ := proj_surjective hX ⟨σ * swap 0 1, hρ⟩
  have hkey : ∀ x : X, ((proj hX (r⁻¹ * α x * r) : A7) : Perm (Fin 7)) =
      swap 0 1 * (proj hX x : Perm (Fin 7)) * swap 0 1 := by
    intro x
    rw [map_mul, map_mul, map_inv, hr]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, proj_apply_of hX hσ x]
    rw [mul_inv_rev, swap_inv]
    group
  obtain ⟨a, ha⟩ := proj_surjective hX ⟨c1, sign_c1⟩
  obtain ⟨b, hb⟩ := proj_surjective hX ⟨c2, sign_c2⟩
  have hzZ : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X := by
    rw [← proj_eq_one_iff hX]
    apply Subtype.ext
    simp only [map_mul, map_inv, ha, hb, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [c1_c2]
    group
  have hz1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := fun h => comm_ne_one hX ha hb (by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul])
  have hza : a * (r⁻¹ * α a * r) ∈ Subgroup.center X := by
    have := (proj_eq_iff hX a⁻¹ (r⁻¹ * α a * r)).mp (Subtype.ext (by
      rw [hkey, map_inv, ha]
      simp only [Subgroup.coe_inv]
      exact swap_c1.symm))
    simpa using this
  have hzb : b⁻¹ * (r⁻¹ * α b * r) ∈ Subgroup.center X :=
    (proj_eq_iff hX b (r⁻¹ * α b * r)).mp (Subtype.ext (by
      rw [hkey, hb]
      exact swap_c2.symm))
  set ζ₁ := a * (r⁻¹ * α a * r) with hζ₁
  set ζ₂ := b⁻¹ * (r⁻¹ * α b * r) with hζ₂
  have ha' : r⁻¹ * α a * r = a⁻¹ * ζ₁ := by rw [hζ₁]; group
  have hb' : r⁻¹ * α b * r = b * ζ₂ := by rw [hζ₂]; group
  set z := a * b * a⁻¹ * b⁻¹ with hz
  have hzc := Subgroup.mem_center_iff.mp hzZ
  have h1 : r⁻¹ * α z * r = z := by
    rw [hZ z hzZ]
    calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
      _ = r⁻¹ * (r * z) := by rw [hzc r]
      _ = z := by group
  have h2 : r⁻¹ * α z * r = (r⁻¹ * α a * r) * (r⁻¹ * α b * r) * (r⁻¹ * α a * r)⁻¹ *
      (r⁻¹ * α b * r)⁻¹ := by
    rw [hz]
    simp only [map_mul, map_inv]
    group
  have h3 : (a⁻¹ * ζ₁) * (b * ζ₂) * (a⁻¹ * ζ₁)⁻¹ * (b * ζ₂)⁻¹ = a⁻¹ * b * a * b⁻¹ := by
    have e1 : ⁅a⁻¹ * ζ₁, b * ζ₂⁆ = ⁅a⁻¹, b⁆ := by rw [comm_mul_right _ hzb, comm_mul_left hza]
    rw [commutatorElement_def, commutatorElement_def, inv_inv] at e1
    exact e1
  have h4 : a⁻¹ * b * a * b⁻¹ = z⁻¹ := by
    have hzi := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hzZ)
    calc a⁻¹ * b * a * b⁻¹ = a⁻¹ * (z⁻¹ * a) := by rw [hz]; group
      _ = a⁻¹ * (a * z⁻¹) := by rw [← hzi a]
      _ = z⁻¹ := by group
  have h5 : z = z⁻¹ := by
    calc z = r⁻¹ * α z * r := h1.symm
      _ = (r⁻¹ * α a * r) * (r⁻¹ * α b * r) * (r⁻¹ * α a * r)⁻¹ * (r⁻¹ * α b * r)⁻¹ := h2
      _ = (a⁻¹ * ζ₁) * (b * ζ₂) * (a⁻¹ * ζ₁)⁻¹ * (b * ζ₂)⁻¹ := by rw [ha', hb']
      _ = a⁻¹ * b * a * b⁻¹ := h3
      _ = z⁻¹ := h4
  have h6 : z ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [h5]; exact mul_inv_cancel z
  have h7 : z ^ 3 = 1 := pow_three_center hX hzZ
  apply hz1
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h6, h7, inv_one, mul_one]

theorem inner_of [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) (α : MulAut X)
    (h : Odd (orderOf α) ∨ ∃ P : Subgroup X, Nat.card P = 9 ∧ ∀ x ∈ P, α x = x) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨σ, hσ⟩ := exists_perm hX α
  refine inner_of_even hX hσ ?_
  rcases h with hodd | ⟨P, hP9, hfix⟩
  · exact sign_of_odd hX hσ hodd
  · exact sign_eq_one_of_fix hX hσ fun z hz => hfix z (center_le_of_card_nine hX hP9 hz)

theorem pow_sixteen (σ : Perm (Fin 7)) {n : ℕ} (hn : σ ^ 2 ^ n = 1) : σ ^ 16 = 1 := by
  have h1 : orderOf σ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf σ ∣ 16 * 315 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
  have hc : Nat.Coprime (orderOf σ) 315 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left n (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right h2)

theorem pow_315 (σ : Perm (Fin 7)) (hodd : Odd (orderOf σ)) : σ ^ 315 = 1 := by
  have h2 : orderOf σ ∣ 315 * 16 := by
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
  have hc : Nat.Coprime (orderOf σ) 16 :=
    Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr hodd) |>.coprime_dvd_right (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right h2)

theorem orderOf_proj_dvd (hX : IsHat X (alternatingGroup (Fin 7))) (x : X) :
    orderOf ((proj hX x : A7) : Perm (Fin 7)) ∣ orderOf x :=
  orderOf_map_dvd ((alternatingGroup (Fin 7)).subtype.comp (proj hX)) x

theorem exists_lift_sq (hX : IsHat X (alternatingGroup (Fin 7))) {σ : A7} (hσ : σ ^ 2 = 1) :
    ∃ y : X, proj hX y = σ ∧ y ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := proj_surjective hX σ
  have hz : y ^ 2 ∈ Subgroup.center X := (proj_eq_one_iff hX _).mp (by rw [map_pow, hσ])
  refine ⟨y ^ 3, ?_, ?_⟩
  · rw [map_pow, pow_succ, hσ, one_mul]
  · rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul]
    exact pow_three_center hX hz

theorem comm_of_sq (hX : IsHat X (alternatingGroup (Fin 7))) {x e : X} (hx : x ^ 2 = 1)
    (hc : proj hX x * proj hX e = proj hX e * proj hX x) : x * e = e * x := by
  have hζ : e⁻¹ * (x * e * x⁻¹) ∈ Subgroup.center X := (proj_eq_iff hX _ _).mp (by
    rw [map_mul, map_mul, map_inv, hc]
    group)
  set ζ := e⁻¹ * (x * e * x⁻¹) with hζdef
  have hxe : x * e * x⁻¹ = e * ζ := by rw [hζdef]; group
  have hxi : x⁻¹ = x := by rw [inv_eq_iff_mul_eq_one, ← sq, hx]
  have h1 : e = e * ζ * ζ := by
    calc e = x * (x * e * x⁻¹) * x⁻¹ := by
          have hx2 : x * x = 1 := by rw [← sq, hx]
          have : x * (x * e * x⁻¹) * x⁻¹ = (x * x) * e * (x * x)⁻¹ := by group
          rw [this, hx2]
          group
      _ = x * (e * ζ) * x⁻¹ := by rw [hxe]
      _ = (x * e * x⁻¹) * ζ := by
          rw [show x * (e * ζ) * x⁻¹ = x * e * (ζ * x⁻¹) by group,
            ← (Subgroup.mem_center_iff.mp hζ x⁻¹)]
          group
      _ = e * ζ * ζ := by rw [hxe]
  have h2 : ζ ^ 2 = 1 := by
    have : ζ * ζ = 1 := by
      have := h1
      rw [mul_assoc] at this
      exact (mul_eq_left.mp this.symm)
    rw [sq, this]
  have h3 : ζ = 1 := by
    have h3' := pow_three_center hX hζ
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2, inv_one, mul_one]
  rw [h3, mul_one] at hxe
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [hxe]

theorem isElemAbelian_comap (hX : IsHat X (alternatingGroup (Fin 7))) {e : A7}
    (he : e ^ 3 = 1) : IsElemAbelian 3 ((Subgroup.zpowers e).comap (proj hX)) := by
  obtain ⟨y₀, hy₀⟩ := proj_surjective hX e
  have hdec : ∀ x ∈ (Subgroup.zpowers e).comap (proj hX), ∃ m : ℤ,
      (y₀ ^ m)⁻¹ * x ∈ Subgroup.center X := by
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ⟨m, (proj_eq_iff hX _ _).mp (by rw [map_zpow, hy₀, hm])⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := hdec a a.2
    obtain ⟨n, hn⟩ := hdec b b.2
    have ha : (a : X) = y₀ ^ m * ((y₀ ^ m)⁻¹ * a) := by group
    have hb : (b : X) = y₀ ^ n * ((y₀ ^ n)⁻¹ * b) := by group
    show (a : X) * b = b * a
    rw [ha, hb]
    exact comm_mul_center (Commute.zpow_zpow_self y₀ m n).eq hm hn
  · apply cube_eq_one hX
    rw [← proj_eq_one_iff hX]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (show proj hX x ∈ Subgroup.zpowers e from hx)
    rw [map_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he,
      one_zpow]

theorem card_comap_zpowers (hX : IsHat X (alternatingGroup (Fin 7))) {e : A7}
    (he : e ^ 3 = 1) (he1 : e ≠ 1) : Nat.card ((Subgroup.zpowers e).comap (proj hX)) = 9 := by
  rw [card_comap_proj, Nat.card_zpowers, orderOf_eq_prime he he1]

theorem clause3 (hX : IsHat X (alternatingGroup (Fin 7))) (hc : HatA7Loc.stmt) (k : X)
    (hk2 : k ^ 2 = 1) (hk1 : k ≠ 1) : ∃ E : Subgroup X, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x : X, x * k = k * x → Odd (orderOf x) → x ∈ E := by
  have hpk : proj hX k ≠ 1 := by
    intro h
    have h3 := pow_three_center hX ((proj_eq_one_iff hX k).mp h)
    apply hk1
    calc k = k ^ 3 * (k ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hk2, inv_one, mul_one]
  obtain ⟨g₀, hg₀⟩ := exists_conj_t0 (proj hX k) (by rw [← map_pow, hk2, map_one]) hpk
  obtain ⟨g, rfl⟩ := proj_surjective hX g₀
  have hc3 : c' ^ 3 = 1 := Subtype.ext c_pow
  have hc1 : c' ≠ 1 := fun h => c_ne (congrArg Subtype.val h)
  set E₀ := (Subgroup.zpowers c').comap (proj hX) with hE₀
  refine ⟨E₀.map (MulAut.conj g⁻¹).toMonoidHom, CFSG.SectionRank.isElemAbelian_map
    (isElemAbelian_comap hX hc3) _, ?_, fun x hxk hodd => ?_⟩
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_comap_zpowers hX hc3 hc1]
  have hgk : proj hX (g * k * g⁻¹) = t0' := by rw [map_mul, map_mul, map_inv, hg₀]
  have hx' : g * x * g⁻¹ ∈ E₀ := by
    show proj hX (g * x * g⁻¹) ∈ Subgroup.zpowers c'
    have h2 : (g * x * g⁻¹) * (g * k * g⁻¹) = (g * k * g⁻¹) * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * (g * k * g⁻¹) = g * (x * k) * g⁻¹ := by group
        _ = g * (k * x) * g⁻¹ := by rw [hxk]
        _ = (g * k * g⁻¹) * (g * x * g⁻¹) := by group
    have h3 : proj hX (g * x * g⁻¹) * proj hX (g * k * g⁻¹) =
        proj hX (g * k * g⁻¹) * proj hX (g * x * g⁻¹) := by rw [← map_mul, ← map_mul, h2]
    rw [hgk] at h3
    have hcomm : (proj hX (g * x * g⁻¹) : Perm (Fin 7)) * HatA7Loc.t0 =
        HatA7Loc.t0 * proj hX (g * x * g⁻¹) := congrArg Subtype.val h3
    have hord : orderOf (g * x * g⁻¹) = orderOf x := by
      rw [← MulAut.conj_apply]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) x
    have hpow : (proj hX (g * x * g⁻¹) : Perm (Fin 7)) ^ 315 = 1 := by
      refine pow_315 _ (Odd.of_dvd_nat ?_ (orderOf_proj_dvd hX _))
      rw [hord]
      exact hodd
    rcases hc.1 _ hcomm hpow with h | h | h
    · rw [show proj hX (g * x * g⁻¹) = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show proj hX (g * x * g⁻¹) = c' from Subtype.ext h]
      exact Subgroup.mem_zpowers _
    · rw [show proj hX (g * x * g⁻¹) = c' ^ 2 from Subtype.ext h]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact ⟨_, hx', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

@[expose] def Prop4 (E : Subgroup X) : Prop :=
  ∃ A S : Subgroup X, IsPGroup 2 A ∧ A ≤ Subgroup.centralizer (E : Set X) ∧
    (∀ x ∈ Subgroup.centralizer (E : Set X), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ A) ∧
    IsPGroup 3 S ∧ Nat.card S = 27 ∧ S ≤ Subgroup.normalizer (A : Set X)

theorem mem_normalizer_of_forall {A : Subgroup X} {g : X} (h1 : ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (h2 : ∀ x ∈ A, g⁻¹ * x * g ∈ A) : g ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem prop4_map (φ : MulAut X) {E : Subgroup X} (h : Prop4 E) :
    Prop4 (E.map φ.toMonoidHom) := by
  obtain ⟨A, S, hA2, hAC, hAmax, hS3, hS27, hSA⟩ := h
  refine ⟨A.map φ.toMonoidHom, S.map φ.toMonoidHom, hA2.map _, ?_, ?_, hS3.map _,
    by rw [Subgroup.card_map_of_injective φ.injective, hS27], ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hAC ha) e he
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · intro x hx ⟨n, hn⟩
    have hx' : φ.symm x ∈ Subgroup.centralizer (E : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have := Subgroup.mem_centralizer_iff.mp hx (φ e) ⟨e, he, rfl⟩
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact this
    have := hAmax _ hx' ⟨n, by rw [← map_pow, hn, map_one]⟩
    exact ⟨_, this, by simp⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine mem_normalizer_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨s * a * s⁻¹, (Subgroup.mem_normalizer_iff.mp (hSA hs) a).mp ha, by simp⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨s⁻¹ * a * s, ?_, by simp⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSA hs)) a).mp ha
      simpa using this

theorem eq_one_of_two_three {x : X} {n : ℕ} (h2 : x ^ 2 ^ n = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hc : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hc) h1')

theorem prop4_c [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) (hc : HatA7Loc.stmt) :
    Prop4 ((Subgroup.zpowers c').comap (proj hX)) := by
  classical
  set E₀ := (Subgroup.zpowers c').comap (proj hX) with hE₀
  obtain ⟨y₀, hy₀⟩ := proj_surjective hX c'
  have hy₀E : y₀ ∈ E₀ := show proj hX y₀ ∈ Subgroup.zpowers c' by
    rw [hy₀]; exact Subgroup.mem_zpowers _
  obtain ⟨a₁, ha₁, ha₁2⟩ := exists_lift_sq hX (σ := t0') (Subtype.ext t0_sq)
  obtain ⟨a₂, ha₂, ha₂2⟩ := exists_lift_sq hX (σ := ⟨HatA7Loc.v2, sign_v2⟩) (Subtype.ext v2_sq)
  have h12 : a₁ * a₂ = a₂ * a₁ := comm_of_sq hX ha₁2 (by rw [ha₁, ha₂]; exact Subtype.ext t0_v2)
  have hcomm_c : ∀ σ : A7, σ * c' = c' * σ → ∀ e ∈ E₀, σ * proj hX e = proj hX e * σ := by
    intro σ hσ e he
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (show proj hX e ∈ Subgroup.zpowers c' from he)
    rw [← hm]
    exact (Commute.zpow_right hσ m).eq
  have ha₁C : a₁ ∈ Subgroup.centralizer (E₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (comm_of_sq hX ha₁2 (by rw [ha₁]; exact hcomm_c _ (Subtype.ext t0_c) e he)).symm
  have ha₂C : a₂ ∈ Subgroup.centralizer (E₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (comm_of_sq hX ha₂2 (by rw [ha₂]; exact hcomm_c _ (Subtype.ext v2_c) e he)).symm
  set A₀ := Subgroup.closure ({a₁, a₂} : Set X) with hA₀
  have hpw : ({a₁, a₂} : Set X).Pairwise Commute := by
    rintro u (rfl | rfl) v (rfl | rfl) _
    · exact Commute.refl _
    · exact h12
    · exact h12.symm
    · exact Commute.refl _
  have hcl := (Subgroup.isMulCommutative_closure hpw).is_comm
  have hsqA : ∀ x ∈ A₀, x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha₁2
      · exact ha₂2
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := congrArg Subtype.val (hcl.comm (⟨x, hx⟩ : ↥A₀) ⟨y, hy⟩)
      rw [(Commute.mul_pow hxy 2), ihx, ihy, one_mul]
    | inv x hx ihx => rw [inv_pow, ihx, inv_one]
  have hA2 : IsPGroup 2 ↥A₀ := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hsqA x x.2)⟩
  have hAC : A₀ ≤ Subgroup.centralizer (E₀ : Set X) := by
    rw [hA₀, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha₁C
    · exact ha₂C
  have hmax : ∀ x ∈ Subgroup.centralizer (E₀ : Set X), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ A₀ := by
    rintro x hx ⟨n, hn⟩
    have hxc : (proj hX x : Perm (Fin 7)) * HatA7Loc.c = HatA7Loc.c * proj hX x := by
      have h1 := Subgroup.mem_centralizer_iff.mp hx y₀ hy₀E
      have h2 := congrArg (fun z => ((proj hX z : A7) : Perm (Fin 7))) h1
      simp only [map_mul, Subgroup.coe_mul, hy₀] at h2
      exact h2.symm
    have hsign : Perm.sign (proj hX x : Perm (Fin 7)) = 1 := (proj hX x).2
    have h16 : (proj hX x : Perm (Fin 7)) ^ 16 = 1 := pow_sixteen _ (n := n) (by
      rw [← Subgroup.coe_pow, ← map_pow, hn, map_one]
      rfl)
    obtain ⟨w, hwA, hw⟩ : ∃ w ∈ A₀, proj hX w = proj hX x := by
      rcases hc.2.1 _ hsign hxc h16 with h | h | h | h
      · exact ⟨1, A₀.one_mem, by rw [map_one]; exact (Subtype.ext h).symm⟩
      · exact ⟨a₁, Subgroup.subset_closure (by simp), by rw [ha₁]; exact (Subtype.ext h).symm⟩
      · exact ⟨a₂, Subgroup.subset_closure (by simp), by rw [ha₂]; exact (Subtype.ext h).symm⟩
      · refine ⟨a₁ * a₂, A₀.mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)), ?_⟩
        rw [map_mul, ha₁, ha₂]
        apply Subtype.ext
        rw [Subgroup.coe_mul, h, v3_eq]
        rfl
    have hζ : w⁻¹ * x ∈ Subgroup.center X := (proj_eq_iff hX w x).mp hw
    have hx' : x = w * (w⁻¹ * x) := by group
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [pow_zero, pow_one] at hn
      rw [hn]
      exact A₀.one_mem
    · have hw2 : w ^ 2 ^ n = 1 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [pow_succ', pow_mul, hsqA w hwA, one_pow]
      have hcw : Commute w (w⁻¹ * x) := Subgroup.mem_center_iff.mp hζ w
      have h1 : (w⁻¹ * x) ^ 2 ^ n = 1 := by
        have := hn
        rw [hx', hcw.mul_pow, hw2, one_mul] at this
        exact this
      have h4 : w⁻¹ * x = 1 := eq_one_of_two_three h1 (pow_three_center hX hζ)
      rw [hx', h4, mul_one]
      exact hwA
  have hc1c : (⟨c1, sign_c1⟩ : A7) * c' = c' * ⟨c1, sign_c1⟩ := Subtype.ext c1_c
  set S₀ := (Subgroup.closure ({⟨c1, sign_c1⟩, c'} : Set A7)).comap (proj hX) with hS₀
  have hS27 : Nat.card S₀ = 27 := by
    obtain ⟨h1, h2, h3⟩ := c1_ne_c
    rw [hS₀, card_comap_proj, card_closure_pair (Subtype.ext c1_pow) (Subtype.ext c_pow)
      (fun h => c_ne (congrArg Subtype.val h)) hc1c ⟨fun h => h1 (congrArg Subtype.val h),
        fun h => h2 (congrArg Subtype.val h), fun h => h3 (by
          have := congrArg Subtype.val h
          rw [Subgroup.coe_pow] at this
          exact this)⟩]
  have hS3 : IsPGroup 3 ↥S₀ := IsPGroup.of_card (n := 3) (by rw [hS27]; norm_num)
  have hclc : ∀ σ ∈ Subgroup.closure ({⟨c1, sign_c1⟩, c'} : Set A7), σ * c' = c' * σ := by
    intro σ hσ
    have hle : Subgroup.closure ({⟨c1, sign_c1⟩, c'} : Set A7) ≤
        Subgroup.centralizer ({c'} : Set A7) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hc1c
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hσ)
  have hsE : ∀ s ∈ S₀, ∀ e ∈ E₀, s * e * s⁻¹ ∈ E₀ := by
    intro s hs e he
    show proj hX (s * e * s⁻¹) ∈ Subgroup.zpowers c'
    rw [map_mul, map_mul, map_inv, hcomm_c (proj hX s) (hclc _ hs) e he, mul_inv_cancel_right]
    exact he
  have hconjA : ∀ s ∈ S₀, ∀ a ∈ A₀, s * a * s⁻¹ ∈ A₀ := by
    intro s hs a ha
    apply hmax
    · rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : s⁻¹ * e * s⁻¹⁻¹ ∈ E₀ := hsE s⁻¹ (S₀.inv_mem hs) e he
      have h1 := Subgroup.mem_centralizer_iff.mp (hAC ha) _ he'
      calc e * (s * a * s⁻¹) = s * ((s⁻¹ * e * s⁻¹⁻¹) * a) * s⁻¹ := by group
        _ = s * (a * (s⁻¹ * e * s⁻¹⁻¹)) * s⁻¹ := by rw [h1]
        _ = s * a * s⁻¹ * e := by group
    · refine ⟨1, ?_⟩
      rw [pow_one, conj_pow, hsqA a ha]
      group
  refine ⟨A₀, S₀, hA2, hAC, hmax, hS3, hS27, fun s hs => mem_normalizer_of_forall
    (hconjA s hs) fun a ha => ?_⟩
  have := hconjA s⁻¹ (S₀.inv_mem hs) a ha
  simpa using this

theorem card_hatA7 (hX : IsHat X (alternatingGroup (Fin 7))) : Nat.card X = 7560 := by
  obtain ⟨e⟩ := hX.2.2
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
    Nat.card_congr e.toEquiv, hA7, hX.2.1]

theorem prop4_d [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) (hc : HatA7Loc.stmt) :
    Prop4 ((Subgroup.zpowers d').comap (proj hX)) := by
  obtain ⟨y₀, hy₀⟩ := proj_surjective hX d'
  have hy₀E : y₀ ∈ (Subgroup.zpowers d').comap (proj hX) :=
    show proj hX y₀ ∈ Subgroup.zpowers d' by rw [hy₀]; exact Subgroup.mem_zpowers _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 3 ∣ Nat.card X := by rw [card_hatA7 hX]; norm_num
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  refine ⟨⊥, S, IsPGroup.of_bot, bot_le, fun x hx ⟨n, hn⟩ => ?_, IsPGroup.of_card hS,
    by rw [hS]; norm_num, fun s _ => mem_normalizer_of_forall (fun y hy => ?_) (fun y hy => ?_)⟩
  · have hxd : (proj hX x : Perm (Fin 7)) * HatA7Loc.d = HatA7Loc.d * proj hX x := by
      have h1 := Subgroup.mem_centralizer_iff.mp hx y₀ hy₀E
      have h2 := congrArg (fun z => ((proj hX z : A7) : Perm (Fin 7))) h1
      simp only [map_mul, Subgroup.coe_mul, hy₀] at h2
      exact h2.symm
    have h16 : (proj hX x : Perm (Fin 7)) ^ 16 = 1 := pow_sixteen _ (n := n) (by
      rw [← Subgroup.coe_pow, ← map_pow, hn, map_one]
      rfl)
    have h1 : proj hX x = 1 := Subtype.ext (hc.2.2 _ (proj hX x).2 hxd h16)
    rw [Subgroup.mem_bot]
    exact eq_one_of_two_three hn (pow_three_center hX ((proj_eq_one_iff hX x).mp h1))
  · rw [Subgroup.mem_bot] at hy ⊢
    rw [hy]
    group
  · rw [Subgroup.mem_bot] at hy ⊢
    rw [hy]
    group

theorem prop4 [Finite X] (hX : IsHat X (alternatingGroup (Fin 7))) (hc : HatA7Loc.stmt)
    {E : Subgroup X} (hE9 : Nat.card E = 9) (hZE : Subgroup.center X ≤ E) : Prop4 E := by
  classical
  have hcardE : Nat.card (E.map (proj hX)) = 3 := by
    have h := card_eq_inf_ker_mul_map (proj hX) E
    rw [ker_proj, inf_eq_right.mpr hZE, hX.2.1, hE9] at h
    omega
  obtain ⟨ê, hêE, hê1⟩ : ∃ ê ∈ E.map (proj hX), ê ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E.map (proj hX) = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [hbot, Subgroup.card_bot] at hcardE
    omega
  have hê3 : ê ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(E.map (proj hX))) (x := ⟨ê, hêE⟩)
    rw [hcardE] at this
    exact congrArg Subtype.val this
  have hE : E.map (proj hX) = Subgroup.zpowers ê :=
    (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hêE)
      (by rw [hcardE, Nat.card_zpowers, orderOf_eq_prime hê3 hê1])).symm
  have hconj : ∀ (f : A7) (g : X), proj hX g * ê * (proj hX g)⁻¹ = f → f ^ 3 = 1 → f ≠ 1 →
      E.map (MulAut.conj g).toMonoidHom = (Subgroup.zpowers f).comap (proj hX) := by
    intro f g hg hf3 hf1
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨e, he, rfl⟩
      show proj hX (g * e * g⁻¹) ∈ Subgroup.zpowers f
      have hm : proj hX e ∈ Subgroup.zpowers ê := hE ▸ ⟨e, he, rfl⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hm
      rw [map_mul, map_mul, map_inv, ← hm, ← conj_zpow, hg]
      exact Subgroup.zpow_mem_zpowers f m
    · rw [card_comap_zpowers hX hf3 hf1, Subgroup.card_map_of_injective (MulEquiv.injective _),
        hE9]
  have hback : ∀ g : X, Prop4 (E.map (MulAut.conj g).toMonoidHom) → Prop4 E := by
    intro g h
    have hEq : (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = E := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id E
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have := prop4_map (MulAut.conj g⁻¹) h
    rwa [hEq] at this
  rcases exists_conj_three ê hê3 hê1 with ⟨g₀, hg₀⟩ | ⟨g₀, hg₀⟩
  · obtain ⟨g, rfl⟩ := proj_surjective hX g₀
    refine hback g ?_
    rw [hconj c' g hg₀ (Subtype.ext c_pow) (fun h => c_ne (congrArg Subtype.val h))]
    exact prop4_c hX hc
  · obtain ⟨g, rfl⟩ := proj_surjective hX g₀
    refine hback g ?_
    rw [hconj d' g hg₀ (Subtype.ext d_pow) (fun h => d_ne (congrArg Subtype.val h))]
    exact prop4_d hX hc

end HatA7L

theorem factHatA7Loc12626_of (hc : HatA7Loc.stmt) : FactHatA7Loc12626 := by
  intro X _ _ hX
  exact ⟨fun s hs => HatA7L.cube_eq_one hX hs, fun α h => HatA7L.inner_of hX α h,
    fun k hk2 hk1 => HatA7L.clause3 hX hc k hk2 hk1, fun E _ hE9 hZE => HatA7L.prop4 hX hc hE9 hZE⟩

theorem factHatA7Loc12626_holds : FactHatA7Loc12626 :=
  factHatA7Loc12626_of (of_decide_eq_true Certificates.certificate7251)

end CFSG.Quasithin.H13
