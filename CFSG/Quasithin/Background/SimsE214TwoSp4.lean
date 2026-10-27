module

public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SimsE213MSp4
public import CFSG.Quasithin.Vol2.E2FourteenA

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace E214T

open scoped commutatorElement

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem map_closure_twoElts (φ : X ≃* Y) (P : Subgroup X) :
    (Subgroup.closure {x : X | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).map φ.toMonoidHom =
      Subgroup.closure {y : Y | y ∈ P.map φ.toMonoidHom ∧ ∃ k : ℕ, y ^ 2 ^ k = 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, k, hk⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, k, by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hxP, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hxP, k, φ.injective ?_⟩, rfl⟩
    rw [map_pow, map_one]
    exact hk

theorem map_le_rootGroupOfParabolic (φ : X ≃* Y) {P R : Subgroup X}
    (hR : R ≤ rootGroupOfParabolic P) :
    R.map φ.toMonoidHom ≤ rootGroupOfParabolic (P.map φ.toMonoidHom) := by
  rintro _ ⟨r, hr, rfl⟩
  have hr' := hR hr
  rw [rootGroupOfParabolic, Subgroup.mem_inf] at hr' ⊢
  obtain ⟨hr1, hr2⟩ := hr'
  refine ⟨?_, ?_⟩
  · rw [← map_closure_twoElts]
    exact ⟨r, hr1, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, ← map_closure_twoElts] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := Subgroup.mem_centralizer_iff.mp hr2 x hx
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h1]

theorem isParabolic2_map (φ : X ≃* Y) {P : Subgroup X} (h : IsParabolic2 ⊤ P) :
    IsParabolic2 ⊤ (P.map φ.toMonoidHom) := by
  obtain ⟨-, S, hS, hSP⟩ := h
  refine ⟨le_top, S.map φ.toMonoidHom, E2.isSylowTwoOf_map_mulEquiv φ hS, ?_⟩
  rw [top_inf_eq, ← Subgroup.map_equiv_normalizer_eq]
  rw [top_inf_eq] at hSP
  exact Subgroup.map_mono hSP

theorem isMaxParabolic2_map (φ : X ≃* Y) {P : Subgroup X} (h : IsMaxParabolic2 ⊤ P) :
    IsMaxParabolic2 ⊤ (P.map φ.toMonoidHom) := by
  obtain ⟨hP, hPt, hmax⟩ := h
  have hback : ∀ Q : Subgroup Y, (Q.map φ.symm.toMonoidHom).map φ.toMonoidHom = Q := by
    intro Q
    rw [Subgroup.map_map]
    convert Subgroup.map_id Q
    ext y
    simp
  refine ⟨isParabolic2_map φ hP, fun h1 => hPt ?_, fun Q hQ hQt hPQ => ?_⟩
  · have h2 := congrArg (Subgroup.map φ.symm.toMonoidHom) h1
    rw [Subgroup.map_map] at h2
    convert h2 using 1
    · convert (Subgroup.map_id P).symm
      ext x
      simp
    · rw [Subgroup.map_top_of_surjective _ φ.symm.surjective]
  · have hQ' := isParabolic2_map φ.symm hQ
    have hQt' : Q.map φ.symm.toMonoidHom ≠ ⊤ := by
      intro h1
      apply hQt
      rw [← hback Q, h1, Subgroup.map_top_of_surjective _ φ.surjective]
    have hPQ' : P ≤ Q.map φ.symm.toMonoidHom := by
      intro x hx
      refine ⟨φ x, hPQ ⟨x, hx, rfl⟩, ?_⟩
      simp
    have h1 := hmax _ hQ' hQt' hPQ'
    rw [← hback Q, h1]

end Transport

section AntiSp

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)

variable {K : Type} [Field K] [CharP K 2]

theorem col_zero_of_mem_normalizer_radA2 {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (radA2 K : Set (antiSp K))) :
    glMat (g : GL (Fin 4) K) 1 0 = 0 ∧ glMat (g : GL (Fin 4) K) 2 0 = 0 ∧
      glMat (g : GL (Fin 4) K) 3 0 = 0 := by
  have key : ∀ a b c : K, a * glMat (g : GL (Fin 4) K) 1 0 + b * glMat (g : GL (Fin 4) K) 2 0 +
      c * glMat (g : GL (Fin 4) K) 3 0 = 0 := by
    intro a b c
    have hu : g⁻¹ * uElt a b c 0 * g ∈ radA2 K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg)
        (uElt a b c 0)).mp ⟨a, b, c, rfl⟩
      simpa using this
    obtain ⟨a', b', c', h'⟩ := hu
    have hE := SteinbergBS.glMat_mul_eq_of_conj h'
    rw [glMat_uElt] at hE
    have e := congrFun (congrFun hE 0) 0
    rw [SteinbergBS.uMat_mul_apply_zero, SteinbergBS.mul_uMat_apply_zero] at e
    linear_combination e
  refine ⟨?_, ?_, ?_⟩
  · simpa using key 1 0 0
  · simpa using key 0 1 0
  · simpa using key 0 0 1

theorem row_three_of_col_zero {g : antiSp K} (h1 : glMat (g : GL (Fin 4) K) 1 0 = 0)
    (h2 : glMat (g : GL (Fin 4) K) 2 0 = 0) (h3 : glMat (g : GL (Fin 4) K) 3 0 = 0) :
    glMat (g : GL (Fin 4) K) 3 1 = 0 ∧ glMat (g : GL (Fin 4) K) 3 2 = 0 ∧
      glMat (g : GL (Fin 4) K) 0 0 * glMat (g : GL (Fin 4) K) 3 3 = 1 := by
  have hJ := mem_antiSp.mp g.2
  have e1 := congrFun (congrFun hJ 0) 1
  have e2 := congrFun (congrFun hJ 0) 2
  have e3 := congrFun (congrFun hJ 0) 3
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply, h1, h2, h3] at e1 e2 e3
  simp only [zero_mul, add_zero, Fin.val_zero, Fin.val_one, Fin.val_two] at e1 e2 e3
  norm_num at e3
  have h00 : glMat (g : GL (Fin 4) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one e3
  have e1' : glMat (g : GL (Fin 4) K) 0 0 * glMat (g : GL (Fin 4) K) 3 1 = 0 := by
    rw [e1]; rfl
  have e2' : glMat (g : GL (Fin 4) K) 0 0 * glMat (g : GL (Fin 4) K) 3 2 = 0 := by
    rw [e2]; rfl
  exact ⟨(mul_eq_zero.mp e1').resolve_left h00, (mul_eq_zero.mp e2').resolve_left h00, e3⟩

theorem glMat_pow_zero_zero {g : antiSp K} (h1 : glMat (g : GL (Fin 4) K) 1 0 = 0)
    (h2 : glMat (g : GL (Fin 4) K) 2 0 = 0) (h3 : glMat (g : GL (Fin 4) K) 3 0 = 0) :
    ∀ m : ℕ, glMat ((g ^ m : antiSp K) : GL (Fin 4) K) 0 0 = glMat (g : GL (Fin 4) K) 0 0 ^ m := by
  intro m
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have e : glMat ((g ^ (m + 1) : antiSp K) : GL (Fin 4) K) =
        glMat ((g ^ m : antiSp K) : GL (Fin 4) K) * glMat (g : GL (Fin 4) K) := by
      rw [pow_succ]
      rfl
    rw [e, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3, ih, pow_succ]
    ring

theorem comm_rootLong_of_mem_normalizer_radA2 {g : antiSp K}
    (hg : g ∈ Subgroup.normalizer (radA2 K : Set (antiSp K))) {j : ℕ} (hj : g ^ 2 ^ j = 1)
    {z : antiSp K} (hz : z ∈ rootLong K) : g * z = z * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, h3⟩ := col_zero_of_mem_normalizer_radA2 hg
  obtain ⟨h31, h32, h0033⟩ := row_three_of_col_zero h1 h2 h3
  have hpow := glMat_pow_zero_zero h1 h2 h3 (2 ^ j)
  rw [hj] at hpow
  have h00 : glMat (g : GL (Fin 4) K) 0 0 = 1 := by
    have e1 : (1 : K) = glMat (g : GL (Fin 4) K) 0 0 ^ 2 ^ j := by
      rw [← hpow]
      rfl
    have e2 : (glMat (g : GL (Fin 4) K) 0 0 - 1) ^ 2 ^ j = 0 := by
      rw [sub_pow_char_pow, one_pow, ← e1, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero j two_ne_zero) |>.mp e2)
  have h33 : glMat (g : GL (Fin 4) K) 3 3 = 1 := by
    rw [h00, one_mul] at h0033
    exact h0033
  obtain ⟨t, rfl⟩ := hz
  apply antiSp_ext
  change glMat (g : GL (Fin 4) K) * glMat (uElt 0 0 t 0 : GL (Fin 4) K) =
    glMat (uElt 0 0 t 0 : GL (Fin 4) K) * glMat (g : GL (Fin 4) K)
  rw [glMat_uElt]
  set A := glMat (g : GL (Fin 4) K)
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, uMat, h1, h2, h3, h31, h32, h00, h33] <;> ring

theorem rootLong_le_rootGroupOfParabolic :
    rootLong K ≤ rootGroupOfParabolic (Subgroup.normalizer (radA2 K : Set (antiSp K))) := by
  have hLA : rootLong K ≤ radA2 K := by
    rintro _ ⟨t, rfl⟩
    exact ⟨0, 0, t, rfl⟩
  have hsub : (rootLong K : Set (antiSp K)) ⊆ {x | x ∈ Subgroup.normalizer
      (radA2 K : Set (antiSp K)) ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := fun x hx =>
    ⟨Subgroup.le_normalizer (hLA hx), 1, by
      rw [pow_one, pow_two]
      exact mul_self_of_mem_radA2 (hLA hx)⟩
  intro z hz
  rw [rootGroupOfParabolic, Subgroup.mem_inf]
  refine ⟨Subgroup.subset_closure (hsub hz), ?_⟩
  have hle : Subgroup.closure {x | x ∈ Subgroup.normalizer (radA2 K : Set (antiSp K)) ∧
      ∃ k : ℕ, x ^ 2 ^ k = 1} ≤ Subgroup.centralizer ({z} : Set (antiSp K)) := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxN, j, hj⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (comm_rootLong_of_mem_normalizer_radA2 hxN hj hz).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := Subgroup.mem_centralizer_iff.mp (hle hy) z rfl
  exact this.symm

variable [Finite K]

theorem isMaxParabolic2_normalizer_radA2 {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsMaxParabolic2 ⊤ (Subgroup.normalizer (radA2 K : Set (antiSp K))) := by
  have hB := Borel252.Sp4.borelData_Sp hn hK
  refine ⟨⟨le_top, antiUnipotent K, hB.sylow, by rw [top_inf_eq]; exact hB.lt₂.le⟩,
    hB.lt_top₂.ne, fun Q _ hQt hPQ => ?_⟩
  rcases hB.only Q (lt_of_lt_of_le hB.lt₂ hPQ) (lt_top_iff_ne_top.mpr hQt) with h | h
  · exfalso
    rw [h] at hPQ
    have hfw : ∀ q ∈ Subgroup.normalizer (radA2 K : Set (antiSp K)), ∀ x ∈ antiUnipotent K,
        q * x * q⁻¹ ∈ antiUnipotent K := by
      intro q hq x hx
      rw [antiUnipotent_eq_radA1_sup_radA2] at hx ⊢
      exact Fin257.conj_mem_sup (fun y hy => (Subgroup.mem_normalizer_iff.mp (hPQ hq) y).mp hy)
        (fun y hy => (Subgroup.mem_normalizer_iff.mp hq y).mp hy) x hx
    have hle : Subgroup.normalizer (radA2 K : Set (antiSp K)) ≤
        Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hfw q hq x, fun hx => ?_⟩
      have := hfw q⁻¹ (inv_mem hq) _ hx
      simpa [mul_assoc] using this
    exact absurd hB.lt₂ (not_lt_of_ge hle)
  · exact h

theorem map_minorAut_antiUnipotent :
    (antiUnipotent K).map (minorAut K).toMonoidHom = antiUnipotent K := by
  have hle : (antiUnipotent K).map (minorAut K).toMonoidHom ≤ antiUnipotent K := by
    rintro _ ⟨_, ⟨a, b, c, d, rfl⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, SteinbergBS.minorAut_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (Nat.card_congr ((minorAut K).subgroupMap (antiUnipotent K)).toEquiv).le

theorem map_minorAut_rootLong :
    (rootLong K).map (minorAut K).toMonoidHom = rootShort K := by
  have e : ∀ t : K, minorAut K (uElt 0 0 t 0) = uElt 0 t 0 0 := by
    intro t
    rw [SteinbergBS.minorAut_uElt]
    congr 1 <;> ring
  apply le_antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, e t⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨uElt 0 0 t 0, ⟨t, rfl⟩, e t⟩

theorem map_minorAut_normalizer :
    (Subgroup.normalizer (antiUnipotent K : Set (antiSp K))).map (minorAut K).toMonoidHom =
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  rw [Subgroup.map_equiv_normalizer_eq, map_minorAut_antiUnipotent]

theorem minorAut_parabolic {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsMaxParabolic2 ⊤
        ((Subgroup.normalizer (radA2 K : Set (antiSp K))).map (minorAut K).toMonoidHom) ∧
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) ≤
        (Subgroup.normalizer (radA2 K : Set (antiSp K))).map (minorAut K).toMonoidHom ∧
      rootShort K ≤ rootGroupOfParabolic
        ((Subgroup.normalizer (radA2 K : Set (antiSp K))).map (minorAut K).toMonoidHom) := by
  refine ⟨isMaxParabolic2_map (minorAut K) (isMaxParabolic2_normalizer_radA2 hn hK), ?_, ?_⟩
  · rw [← map_minorAut_normalizer]
    exact Subgroup.map_mono Fin257.Sp4.normalizer_U_le_normalizer_radA2
  · rw [← map_minorAut_rootLong]
    exact map_le_rootGroupOfParabolic (minorAut K) rootLong_le_rootGroupOfParabolic

omit [CharP K 2] in
theorem exists_ne_zero_ne_one (hk : 4 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  haveI := Fintype.ofFinite K
  have hcard : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    have h1 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  exact ⟨t, ht.1, ht.2⟩

theorem exists_torus_conj {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (β₀ γ₀ : K) :
    ∃ w ∈ antiUnipotentCenter K, ∃ n ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
      n⁻¹ * w * n = w * uElt 0 β₀ γ₀ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hx2 : x ^ 2 - 1 ≠ 0 := by
    have e : x ^ 2 - 1 = (x - 1) ^ 2 := by linear_combination (x - 1) * h2
    rw [e]
    exact pow_ne_zero 2 hx1'
  set u := Units.mk0 x hx0
  refine ⟨uElt 0 (β₀ / (x - 1)) (γ₀ / (x ^ 2 - 1)) 0, ⟨_, _, rfl⟩,
    (E2.TI2b.Sp4.dd u 1)⁻¹, inv_mem (E2.TI2b.Sp4.dd_mem_normalizer u 1), ?_⟩
  rw [inv_inv, E2.TI2b.Sp4.dd_conj_uElt, uElt_mul]
  have hu : ((u : Kˣ) : K) = x := rfl
  simp only [hu, Units.val_one, inv_one, mul_zero, one_pow, mul_one, zero_mul, add_zero]
  congr 1
  · field_simp
    ring
  · field_simp
    ring

end AntiSp

variable {G : Type} [Group G] [Finite G]

theorem comm_of_star {T M V I : Subgroup G} {g : G} (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g)
    (h : ∀ z ∈ E2.star (M ⊓ I) I V, z ≠ 1 → ∃ w ∈ E2.star (M ⊓ I) I V,
      ∃ n ∈ E2.star (M ⊓ I) I (M ⊓ I), n⁻¹ * w * n = w * z) :
    ∀ v ∈ V, v ∉ kerIn (M ⊓ I) I → ∃ u ∈ V, ∃ n ∈ M ⊓ I,
      (u * v)⁻¹ * (n⁻¹ * u * n) ∈ kerIn (M ⊓ I) I := by
  intro v hv hvJ
  have hvI : v ∈ I := hp.V_le hv
  set sq := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hsq
  have hvs : sq ⟨v, hvI⟩ ∈ E2.star (M ⊓ I) I V := ⟨⟨v, hvI⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
  have hv1 : sq ⟨v, hvI⟩ ≠ 1 := by
    rw [hsq, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hvJ
  obtain ⟨w, hw, n, hn, hnw⟩ := h _ hvs hv1
  obtain ⟨⟨u, huI⟩, hu, rfl⟩ := hw
  replace hu : u ∈ V := hu
  obtain ⟨⟨n₀, hn₀I⟩, hn₀, rfl⟩ := hn
  replace hn₀ : n₀ ∈ M ⊓ I := hn₀
  refine ⟨u, hu, n₀, hn₀, ?_⟩
  have hnz' : sq ((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩) = sq (⟨u, huI⟩ * ⟨v, hvI⟩) := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact hnw
  rw [hsq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hnz'
  have e : ((((⟨n₀, hn₀I⟩ : I)⁻¹ * ⟨u, huI⟩ * ⟨n₀, hn₀I⟩)⁻¹ * (⟨u, huI⟩ * ⟨v, hvI⟩) : I) : G) =
      ((u * v)⁻¹ * (n₀⁻¹ * u * n₀))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at hnz'
  have h3 := (kerIn (M ⊓ I) I).inv_mem hnz'
  rw [inv_inv] at h3
  exact h3

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b in
open CFSG.Quasithin.SteinbergBS (rootLong rootShort) in
theorem star_eq_center_of_sp4 {T M V I : Subgroup G} {g : G}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hsyl : IsSylowTwoOf (T ⊓ I) I) (hTMI : T ⊓ I ≤ M ⊓ I)
    (hg : g ∈ I) (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G))
    (hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)))
    (hroot : ∀ P : Subgroup (E2.StarQuot (M ⊓ I) I), IsMaxParabolic2 ⊤ P →
      E2.star (M ⊓ I) I (M ⊓ I) ≤ P → ¬ E2.star (M ⊓ I) I V ≤ rootGroupOfParabolic P)
    {k : ℕ} (hY : IsPSp4 2 k (E2.StarQuot (M ⊓ I) I)) :
    E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) ∧
      ∀ v ∈ V, v ∉ kerIn (M ⊓ I) I → ∃ u ∈ V, ∃ n ∈ M ⊓ I,
        (u * v)⁻¹ * (n⁻¹ * u * n) ∈ kerIn (M ⊓ I) I := by
  have := E2P.finite_starQuot (M ⊓ I) I
  have hk := E2.two_le_of_isPSp4 hY
  have hs : IsSimpleGroup (E2.StarQuot (M ⊓ I) I) := E2.isSimpleGroup_of_isPSp4 hY
  obtain ⟨K, _, _, _, hK, ⟨θ₀⟩⟩ := E213M.exists_antiSp_of_isSp4Full (Or.inl hY)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : Finite (antiSp K) := Finite.of_equiv _ θ₀.toEquiv
  set Ts := E2.star (M ⊓ I) I (T ⊓ I) with hTs
  set Ms := E2.star (M ⊓ I) I (M ⊓ I) with hMs
  set Vs := E2.star (M ⊓ I) I V with hVs
  have hS := E2.isSylowTwoOf_star_inf (M := M) hsyl
  have hS' := E2.isSylowTwoOf_map_equiv θ₀ hS
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2 hS'
  set θ := θ₀.trans (MulAut.conj c⁻¹) with hθ
  have hθapp : ∀ t, θ t = c⁻¹ * θ₀ t * c⁻¹⁻¹ := fun t => rfl
  have hθT : ∀ t, t ∈ Ts ↔ θ t ∈ antiUnipotent K := by
    intro t
    rw [hθapp, inv_inv, ← B6.mem_conjSub, ← hc]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t', ht', he⟩
      rwa [θ₀.injective he] at ht'
  have hBor := E2.star_eq_normalizer_of_isBorelIn hTMI hsyl hBorel
  have hθM : ∀ m, m ∈ Ms ↔ θ m ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
    intro m
    rw [hMs, hBor, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h r
      obtain ⟨t, rfl⟩ := θ.surjective r
      rw [← hθT, ← map_inv, ← map_mul, ← map_mul, ← hθT]
      exact h t
    · intro h t
      rw [hθT, hθT, map_mul, map_mul, map_inv]
      exact h (θ t)
  have hθZ : ∀ z, z ∈ centerOf Ts ↔ θ z ∈ antiUnipotentCenter K := by
    intro z
    rw [centerOf, Subgroup.mem_inf, mem_antiUnipotentCenter_iff_central, ← hθT]
    refine ⟨fun ⟨hzT, hzc⟩ => ⟨hzT, fun u hu => ?_⟩, fun ⟨hzT, hzc⟩ => ⟨hzT, ?_⟩⟩
    · obtain ⟨t, rfl⟩ := θ.surjective u
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hzc t ((hθT t).mpr hu)]
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact θ.injective (by rw [map_mul, map_mul, hzc (θ t) ((hθT t).mp ht)])
  have hVT : Vs ≤ Ts := Subgroup.map_mono (Subgroup.subgroupOf_mono I hp.le_T)
  have hVZ' : Vs ≤ centerOf Ts := le_inf hVT hVZ
  have hN : Ms ≤ Subgroup.normalizer (Vs : Set (E2.StarQuot (M ⊓ I) I)) :=
    E2.star_le_normalizer_star (inf_le_left.trans hMN)
  set W := Vs.map θ.toMonoidHom with hW
  have hWZ : W ≤ antiUnipotentCenter K := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hθZ v).mp (hVZ' hv)
  have hWinv : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ w ∈ W,
      b * w * b⁻¹ ∈ W := by
    rintro b hb _ ⟨v, hv, rfl⟩
    obtain ⟨m, rfl⟩ := θ.surjective b
    have hm : m ∈ Ms := (hθM m).mpr hb
    refine ⟨m * v * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hN hm) v).mp hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hmemW : ∀ y, y ∈ Vs ↔ θ y ∈ W := by
    intro y
    refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨y', hy', he⟩
    rwa [θ.injective he] at hy'
  have hVeq : Vs = centerOf Ts := by
    have hV1 : Vs ≠ ⊥ := E2.star_ne_bot_of_gen hg hgen
    rcases E2.TI2b.Sp4.borelInvariant_center hK4 hWZ hWinv with h | h | h | h
    ·
      exfalso
      apply hV1
      rw [eq_bot_iff]
      intro y hy
      have := (hmemW y).mp hy
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact θ.injective (by rw [this, map_one])
    ·
      exfalso
      refine hroot ((Subgroup.normalizer (radA2 K : Set (antiSp K))).map θ.symm.toMonoidHom)
        (isMaxParabolic2_map θ.symm (isMaxParabolic2_normalizer_radA2 hk hK)) ?_ ?_
      · intro m hm
        refine ⟨θ m, Fin257.Sp4.normalizer_U_le_normalizer_radA2 ((hθM m).mp hm), ?_⟩
        simp
      · have h1 := map_le_rootGroupOfParabolic θ.symm (rootLong_le_rootGroupOfParabolic (K := K))
        refine le_trans ?_ h1
        intro y hy
        refine ⟨θ y, h ▸ (hmemW y).mp hy, ?_⟩
        simp
    ·
      exfalso
      obtain ⟨hmax, hBP, hroot'⟩ := minorAut_parabolic (K := K) hk hK
      refine hroot (((Subgroup.normalizer (radA2 K : Set (antiSp K))).map
        (minorAut K).toMonoidHom).map θ.symm.toMonoidHom) (isMaxParabolic2_map θ.symm hmax) ?_ ?_
      · intro m hm
        refine ⟨θ m, hBP ((hθM m).mp hm), ?_⟩
        simp
      · refine le_trans ?_ (map_le_rootGroupOfParabolic θ.symm hroot')
        intro y hy
        refine ⟨θ y, h ▸ (hmemW y).mp hy, ?_⟩
        simp
    ·
      ext y
      rw [hmemW, h, hθZ]
  refine ⟨hVeq, comm_of_star hp fun z hz hz1 => ?_⟩
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_ne_one hK4
  have hzW : θ z ∈ antiUnipotentCenter K := by
    rw [← hVs, hVeq] at hz
    exact (hθZ z).mp hz
  obtain ⟨β₀, γ₀, hβγ⟩ := hzW
  obtain ⟨w', hw', n', hn', hnw⟩ := exists_torus_conj hx0 hx1 β₀ γ₀
  refine ⟨θ.symm w', ?_, θ.symm n', (hθM _).mpr (by simpa using hn'), ?_⟩
  · rw [← hVs, hVeq, hθZ]
    simpa using hw'
  · apply θ.injective
    rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      hnw, hβγ]

theorem two_of_sp4
    {T M V I : Subgroup G} {g : G}
    (hp : E2.Pair I (T ⊓ I) (M ⊓ I) V g) (hsyl : IsSylowTwoOf (T ⊓ I) I) (hTMI : T ⊓ I ≤ M ⊓ I)
    (hg : g ∈ I) (hgen : I = V ⊔ B6.conjSub g V)
    (hVZ : E2.star (M ⊓ I) I V ≤
      Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)))
    (hMN : M ⊓ I ≤ Subgroup.normalizer (V : Set G))
    (hBorel : E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)))
    (hroot : ∀ P : Subgroup (E2.StarQuot (M ⊓ I) I), IsMaxParabolic2 ⊤ P →
      E2.star (M ⊓ I) I (M ⊓ I) ≤ P → ¬ E2.star (M ⊓ I) I V ≤ rootGroupOfParabolic P)
    {k : ℕ} (hY : IsPSp4 2 k (E2.StarQuot (M ⊓ I) I)) :
    E2.Pair.PP (M ⊓ I) V I g = kerIn (M ⊓ I) I ∧
      E2.star (M ⊓ I) I V = centerOf (E2.star (M ⊓ I) I (T ⊓ I)) := by
  have := E2P.finite_starQuot (M ⊓ I) I
  obtain ⟨hVeq, hcomm⟩ := star_eq_center_of_sp4 hp hsyl hTMI hg hgen hVZ hMN hBorel hroot hY
  refine ⟨?_, hVeq⟩
  have := hp.normal_P
  have := hp.normal_Jbar
  have hVbar : E2.Pair.Vbar (M ⊓ I) V I g ≤ commutator (E2.Pair.Xbar (M ⊓ I) V I g) :=
    hp.Vbar_le_commutator fun v hv hvJ => by
      obtain ⟨u, hu, n, hn, h⟩ := hcomm v hv hvJ
      exact ⟨u, hu, n, ⟨hn.2, hMN hn⟩, h⟩
  have htop : (⊤ : Subgroup (E2.Pair.Xbar (M ⊓ I) V I g)) =
      commutator (E2.Pair.Xbar (M ⊓ I) V I g) :=
    le_antisymm (hp.top_eq_commutator_sup_Vbar.le.trans (sup_le le_rfl hVbar)) le_top
  have hXs := E2.isSimpleGroup_of_isPSp4 hY
  have hXp := E2.commutator_eq_top_of_isPSp4 hY
  have := hXs.toNontrivial
  have hXna := E2.nonabelian_of_commutator_eq_top hXp
  set e := hp.quotJbarEquiv
  have hS : commutator (E2.Pair.Xbar (M ⊓ I) V I g ⧸ E2.Pair.Jbar (M ⊓ I) V I g) = ⊤ :=
    E2.Pair.commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (E2.Pair.Xbar (M ⊓ I) V I g ⧸ E2.Pair.Jbar (M ⊓ I) V I g) :=
    MulEquiv.isSimpleGroup e
  have hna : ∃ a b : E2.Pair.Xbar (M ⊓ I) V I g ⧸ E2.Pair.Jbar (M ⊓ I) V I g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  have hJc := hp.Jbar_le_center
  obtain ⟨hLq, ⟨eL⟩⟩ := E2.quasisimple_commutator _ hJc hS hsimp hna
  have : Group.IsPerfect ↥(commutator (E2.Pair.Xbar (M ⊓ I) V I g)) := hLq.1
  have hb : Subgroup.center ↥(commutator (E2.Pair.Xbar (M ⊓ I) V I g)) = ⊥ :=
    E2.center_eq_bot_of_isPSp4 hY (eL.trans e)
  have hZc := E2.map_center_commutator_eq _ hJc hS hsimp hna
  rw [hb, Subgroup.map_bot, ← htop, top_inf_eq] at hZc
  refine le_antisymm hp.P_le_J fun j hj => ?_
  have hjI : j ∈ I := kerIn_le.trans hp.le_X hj
  have h1 : QuotientGroup.mk' ((E2.Pair.PP (M ⊓ I) V I g).subgroupOf I) (⟨j, hjI⟩ : I) ∈
      E2.Pair.Jbar (M ⊓ I) V I g := ⟨⟨j, hjI⟩, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  rw [← hZc, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

end E214T

end CFSG.Quasithin.SimsE2
