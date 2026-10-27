module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNAut
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.E6QTwo

open CFSG CFSG.Assembly E6QTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

theorem ggQ2s08rN_mul_self_mod_three {n : ℕ} (h3n : ¬ 3 ∣ n) : ∃ k, n * n = 3 * k + 1 := by
  have h : n * n % 3 = 1 := by
    rw [Nat.mul_mod]
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [h]
  refine ⟨n * n / 3, ?_⟩
  have h2 := Nat.div_add_mod (n * n) 3
  generalize n * n = m at h h2 ⊢
  omega

theorem ggQ2s08rN_pow_mul_self {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {n : ℕ}
    (h3n : ¬ 3 ∣ n) (u : Kˣ) : u ^ (n * n) = u := by
  obtain ⟨k, hk⟩ := ggQ2s08rN_mul_self_mod_three h3n
  rw [hk, pow_add, pow_mul, USixTwo.cube_unit_eq_one hK, one_pow, one_mul, pow_one]

@[expose] noncomputable def ggQ2s08rNNormAt {K : Type} [Field K] {n : ℕ} (w : Fin (n + 1))
    (σ : Fin (n + 1) → Kˣ) : Fin (n + 1) → Kˣ :=
  fun k => if k = w then 1 else (σ w * (∏ i, σ i)⁻¹) ^ n * σ k

theorem ggQ2s08rNNormAt_self {K : Type} [Field K] {n : ℕ} (w : Fin (n + 1))
    (σ : Fin (n + 1) → Kˣ) : ggQ2s08rNNormAt w σ w = 1 :=
  if_pos rfl

theorem ggQ2s08rNNormAt_of_ne {K : Type} [Field K] {n : ℕ} {w k : Fin (n + 1)}
    (σ : Fin (n + 1) → Kˣ) (hk : k ≠ w) :
    ggQ2s08rNNormAt w σ k = (σ w * (∏ i, σ i)⁻¹) ^ n * σ k :=
  if_neg hk

theorem ggQ2s08rNNormAt_prod {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {n : ℕ}
    (h3n : ¬ 3 ∣ n) (w : Fin (n + 1)) (σ : Fin (n + 1) → Kˣ) :
    ∏ k, ggQ2s08rNNormAt w σ k = 1 := by
  classical
  set lam : Kˣ := (σ w * (∏ i, σ i)⁻¹) ^ n with hlam
  have h1 := Finset.mul_prod_erase Finset.univ (ggQ2s08rNNormAt w σ) (Finset.mem_univ w)
  have h2 := Finset.mul_prod_erase Finset.univ σ (Finset.mem_univ w)
  have h3 : ∏ k ∈ Finset.univ.erase w, ggQ2s08rNNormAt w σ k =
      ∏ k ∈ Finset.univ.erase w, (lam * σ k) :=
    Finset.prod_congr rfl fun k hk => ggQ2s08rNNormAt_of_ne σ (Finset.ne_of_mem_erase hk)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ w),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at h3
  have h4 : ∏ k ∈ Finset.univ.erase w, σ k = (σ w)⁻¹ * ∏ i, σ i := by
    rw [← h2, inv_mul_cancel_left]
  have h5 : lam ^ n = σ w * (∏ i, σ i)⁻¹ := by
    rw [hlam, ← pow_mul, ggQ2s08rN_pow_mul_self hK h3n]
  rw [← h1, ggQ2s08rNNormAt_self, one_mul, h3, h4, h5, mul_comm (σ w) _, mul_assoc,
    ← mul_assoc (σ w), mul_inv_cancel, one_mul, inv_mul_cancel]

theorem ggQ2s08rNNormAt_const {K : Type} [Field K] {n : ℕ} (w : Fin (n + 1))
    (σ : Fin (n + 1) → Kˣ) :
    ∀ i j, i ≠ w → j ≠ w →
      (ggQ2s08rNNormAt w σ i)⁻¹ * σ i = (ggQ2s08rNNormAt w σ j)⁻¹ * σ j := by
  have key : ∀ k, k ≠ w → (ggQ2s08rNNormAt w σ k)⁻¹ * σ k = ((σ w * (∏ i, σ i)⁻¹) ^ n)⁻¹ := by
    intro k hk
    rw [ggQ2s08rNNormAt_of_ne σ hk, mul_inv_rev, mul_comm (σ k)⁻¹, mul_assoc, inv_mul_cancel,
      mul_one]
  intro i j hi hj
  rw [key i hi, key j hj]

theorem ggQ2s08rN_permGLSU_conj_diag {K : Type} [Field K] {n : ℕ} (hK : Nat.card K = 4)
    (τ : Equiv.Perm (Fin (n + 1))) (σ : Fin (n + 1) → Kˣ) :
    (e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K) * diagHom (n + 1) σ *
        ((e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K))⁻¹ = diagHom (n + 1) (σ ∘ ⇑τ.symm) := by
  have hcoe : (e6QTwoNPermGLSU hK τ : GL (Fin (n + 1)) K) =
      TauCeti.permutationGL (k := K) τ := e6QTwoNCoePermGLSU hK τ
  have hdiag : (diagHom (n + 1) σ : GL (Fin (n + 1)) K) = TauCeti.diagGL σ := Units.ext (by
    rw [coe_diagHom, TauCeti.diagGL_coe])
  have hdiag' : (diagHom (n + 1) (σ ∘ ⇑τ.symm) : GL (Fin (n + 1)) K) =
      TauCeti.diagGL (σ ∘ ⇑τ.symm) := Units.ext (by rw [coe_diagHom, TauCeti.diagGL_coe])
  rw [hcoe, hdiag, hdiag']
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (TauCeti.permutationGL (k := K) τ) τ.symm
    (TauCeti.permutationGL_coe τ) σ]
  group

namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}

omit [Finite G]
  in
theorem su_scalars_eq_bot_of_not_dvd (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    {m : ℕ} (hm : 1 ≤ m) (h3 : ¬ 3 ∣ m) :
    (CFSG.Open.StatedScalars (Fin m) K).subgroupOf (CFSG.Open.StatedSU m (2 ^ 1) K) = ⊥ := by
  have hKc : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨c, hc⟩ := hg
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈ CFSG.Open.StatedSU m (2 ^ 1) K := by
      rw [hc]
      exact g.2
    have h := (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 1) Nat.prime_two hKc
      hm c).mp hmem
    have hc3 : c ^ 3 = 1 := by simpa using h.2
    have hcop : Nat.gcd 3 m = 1 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hdvd : orderOf c ∣ Nat.gcd 3 m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one h.1)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hc, hdvd, map_one]
  · intro hg
    rw [Subgroup.mem_bot] at hg
    rw [hg]
    exact Subgroup.one_mem _

theorem eq_one_of_piL_eq_one_of_not_dvd (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n)
    (w : Fin (n + 1)) {q : ↥L} (hq : q ∈ c.compL w) (h1 : c.piL q = 1) : q = 1 := by
  have hKc : Nat.card c.K = (2 ^ 1) ^ 2 := by rw [c.hK]; norm_num
  have hU := USixTwo.fieldDataFour c.hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP c.K 2 := hU.charP
  have hperf : Group.IsPerfect ↥(c.compL w) := Group.isPerfect_def.mpr (c.compL_quasisimple w).1
  let ρ₀ : ↥(c.compL w) →* ↥(c.stabImg w) :=
    (c.piL.comp (c.compL w).subtype).codRestrict (c.stabImg w)
      (fun q' => c.compL_le_stabPre w q'.2)
  let e : ↥(c.stabImg w) ≃* ↥(CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    (c.stabEquiv w).symm.trans (ggQ2s08rN_stabSUEquiv c.hK w)
  let Zs : Subgroup ↥(CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    (CFSG.Open.StatedScalars (Fin n) c.K).subgroupOf (CFSG.Open.StatedSU n (2 ^ 1) c.K)
  let mk := QuotientGroup.mk' Zs
  have hmk : Function.Injective mk := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact su_scalars_eq_bot_of_not_dvd c.K c.hK (by have := c.hn; omega) h3n
  let ρ : ↥(c.compL w) →* CFSG.Open.StatedProj (CFSG.Open.StatedSU n (2 ^ 1) c.K) :=
    mk.comp (e.toMonoidHom.comp ρ₀)
  have hρ₀ : Function.Surjective ρ₀ := by
    rintro ⟨r, hr⟩
    have hmap := ggQ2s08r6_map_comm_comap c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
    rw [← hmap] at hr
    obtain ⟨q', hq', hq'r⟩ := hr
    exact ⟨⟨q', hq'⟩, Subtype.ext hq'r⟩
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp hρ₀)
  have hρker : ∀ q' : ↥(c.compL w), ρ q' = 1 ↔ c.piL q' = 1 := by
    intro q'
    constructor
    · intro h
      have h2 : e (ρ₀ q') = 1 := hmk (by rw [map_one]; exact h)
      have h3 : ρ₀ q' = 1 := e.injective (by rw [h2, map_one])
      exact congrArg Subtype.val h3
    · intro h
      have h3 : ρ₀ q' = 1 := Subtype.ext h
      change mk (e (ρ₀ q')) = 1
      rw [h3, map_one, map_one]
  have hker : ρ.ker ≤ Subgroup.center ↥(c.compL w) := by
    intro q' hq'
    rw [MonoidHom.mem_ker, hρker] at hq'
    have hz : (q' : ↥L) ∈ Subgroup.center ↥L := by rw [← c.piL_ker]; exact hq'
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro r
    exact Subtype.ext (hz r)
  obtain ⟨φ, hφ, hφρ⟩ := CFSG.LieType.SeitzGeneration.exists_su_cover_hom hKc le_rfl
    (by have := c.hn; omega : 4 ≤ n) ρ hρ hker
    (fun he => by
      rcases hpar with hodd | hZodd
      · exact absurd he (Nat.not_even_iff_odd.mpr hodd)
      · let ι : ρ.ker →* Subgroup.center ↥L :=
          { toFun := fun q' => ⟨((q' : ↥(c.compL w)) : ↥L), by
              rw [← c.piL_ker]
              exact (hρker (q' : ↥(c.compL w))).mp q'.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have hι : Function.Injective ι := by
          intro a a' h
          have h' : ((a : ↥(c.compL w)) : ↥L) = ((a' : ↥(c.compL w)) : ↥L) :=
            congrArg (fun z : ↥(Subgroup.center ↥L) => (z : ↥L)) h
          exact Subtype.ext (Subtype.ext h')
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι)
          (Nat.coprime_two_left.mpr hZodd))
  obtain ⟨g, hg⟩ := hφ ⟨q, hq⟩
  have hρq : ρ ⟨q, hq⟩ = 1 := (hρker _).mpr h1
  rw [← hg, hφρ] at hρq
  have hg1 : g = 1 := hmk (by rw [map_one]; exact hρq)
  rw [hg1, map_one] at hg
  exact congrArg Subtype.val hg.symm

theorem piL_injOn_compL (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n)
    (w : Fin (n + 1)) {q q' : ↥L} (hq : q ∈ c.compL w) (hq' : q' ∈ c.compL w)
    (h : c.piL q = c.piL q') : q = q' := by
  have h1 : c.piL (q⁻¹ * q') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  exact inv_mul_eq_one.mp (c.eq_one_of_piL_eq_one_of_not_dvd hpar h3n w
    ((c.compL w).mul_mem ((c.compL w).inv_mem hq) hq') h1)

theorem exists_mem_compL_piL_eq (c : GGQ2S08RoN n Bs L x) (w : Fin (n + 1))
    {r : LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) c.K (2 ^ 1))} (hr : r ∈ c.stabImg w) :
    ∃ q ∈ c.compL w, c.piL q = r := by
  have hmap := ggQ2s08r6_map_comm_comap c.piL_surjective (c.stabImg w) (c.stabImg_perfect w)
  rw [← hmap] at hr
  obtain ⟨q, hq, hqr⟩ := hr
  exact ⟨q, hq, hqr⟩

@[expose] noncomputable def diagSU (c : GGQ2S08RoN n Bs L x) (s : Fin (n + 1) → c.Kˣ)
    (hs : ∏ k, s k = 1) : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2) :=
  ⟨diagHom (n + 1) s, (ggQ2s08rN_diagHom_mem_iff c.hK s).mpr hs⟩

theorem coe_diagSU (c : GGQ2S08RoN n Bs L x) (s : Fin (n + 1) → c.Kˣ) (hs : ∏ k, s k = 1) :
    ((c.diagSU s hs : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2)) : GL (Fin (n + 1)) c.K) =
      diagHom (n + 1) s := rfl

theorem diagSU_mem_stab (c : GGQ2S08RoN n Bs L x) {w : Fin (n + 1)} {s : Fin (n + 1) → c.Kˣ}
    (hs : ∏ k, s k = 1) (hw : s w = 1) : c.diagSU s hs ∈ ggQ2s08rNStab c.K w := by
  intro i
  rw [coe_diagSU, coe_diagHom, Matrix.diagonal_apply]
  by_cases hi : i = w
  · rw [if_pos hi, if_pos hi, hi, hw, Units.val_one]
  · rw [if_neg hi, if_neg hi]

theorem diagSU_commute (c : GGQ2S08RoN n Bs L x) (s s' : Fin (n + 1) → c.Kˣ) (hs : ∏ k, s k = 1)
    (hs' : ∏ k, s' k = 1) : c.diagSU s hs * c.diagSU s' hs' = c.diagSU s' hs' * c.diagSU s hs := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_diagSU, coe_diagSU, ← map_mul, ← map_mul, mul_comm]

theorem diagConj_eq_normAt (c : GGQ2S08RoN n Bs L x) (h3n : ¬ 3 ∣ n) {w : Fin (n + 1)}
    (σ : Fin (n + 1) → c.Kˣ) {u : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2)}
    (hu : u ∈ ggQ2s08rNStab c.K w) :
    c.diagConj σ u = c.diagSU (ggQ2s08rNNormAt w σ) (ggQ2s08rNNormAt_prod c.hK h3n w σ) * u *
      (c.diagSU (ggQ2s08rNNormAt w σ) (ggQ2s08rNNormAt_prod c.hK h3n w σ))⁻¹ := by
  apply Subtype.ext
  set s := ggQ2s08rNNormAt w σ with hsdef
  set ε : Fin (n + 1) → c.Kˣ := fun k => (s k)⁻¹ * σ k with hεdef
  have hσ : σ = s * ε := funext fun k => by
    rw [Pi.mul_apply, hεdef, mul_inv_cancel_left]
  have hcomm : (u : GL (Fin (n + 1)) c.K) * diagHom (n + 1) ε = diagHom (n + 1) ε * u :=
    ggQ2s08rN_stab_commute c.hK hu (fun i j hi hj => ggQ2s08rNNormAt_const w σ i j hi hj)
  rw [coe_diagConj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_diagSU]
  calc diagHom (n + 1) σ * (u : GL (Fin (n + 1)) c.K) * (diagHom (n + 1) σ)⁻¹
      = diagHom (n + 1) s * (diagHom (n + 1) ε * u) * (diagHom (n + 1) ε)⁻¹ *
          (diagHom (n + 1) s)⁻¹ := by
        conv_lhs => rw [hσ, map_mul]
        group
    _ = diagHom (n + 1) s * (u * diagHom (n + 1) ε) * (diagHom (n + 1) ε)⁻¹ *
          (diagHom (n + 1) s)⁻¹ := by rw [hcomm]
    _ = diagHom (n + 1) s * u * (diagHom (n + 1) s)⁻¹ := by group

theorem exists_inner (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n) (w : Fin (n + 1))
    (b : Bs) :
    ∃ t ∈ c.compL w, c.piL t = c.fr (c.diagSU (ggQ2s08rNNormAt w (c.diag b))
        (ggQ2s08rNNormAt_prod c.hK h3n w (c.diag b))) ∧
      ∀ y ∈ c.compL w, c.conjB b y = t * y * t⁻¹ := by
  set D := c.diagSU (ggQ2s08rNNormAt w (c.diag b)) (ggQ2s08rNNormAt_prod c.hK h3n w (c.diag b))
    with hD
  have hDs : D ∈ ggQ2s08rNStab c.K w := c.diagSU_mem_stab _ (ggQ2s08rNNormAt_self w _)
  obtain ⟨t, ht, htD⟩ := c.exists_mem_compL_piL_eq w ⟨D, hDs, rfl⟩
  refine ⟨t, ht, htD, fun y hy => ?_⟩
  refine c.piL_injOn_compL hpar h3n w (c.conjB_mem_compL w b hy)
    ((c.compL w).mul_mem ((c.compL w).mul_mem ht hy) ((c.compL w).inv_mem ht)) ?_
  obtain ⟨u, hu, hul⟩ := (show c.piL y ∈ c.stabImg w from c.compL_le_stabPre w hy)
  rw [piL_conjB, ← hul, act_fr, c.diagConj_eq_normAt h3n _ hu]
  simp only [map_mul, map_inv]
  rw [htD, hul]

theorem four_dvd_card_automizer_of_inner (c : GGQ2S08RoN n Bs L x)
    (hpar : Odd n ∨ Odd (Nat.card (Subgroup.center ↥L))) (h3n : ¬ 3 ∣ n) (w : Fin (n + 1)) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  classical
  choose t htmem htpi htconj using fun b : Bs => c.exists_inner hpar h3n w b
  have hinj : ∀ {q q' : ↥L}, q ∈ c.compL w → q' ∈ c.compL w → c.piL q = c.piL q' → q = q' :=
    fun hq hq' h => c.piL_injOn_compL hpar h3n w hq hq' h
  set s : Bs → Fin (n + 1) → c.Kˣ := fun b => ggQ2s08rNNormAt w (c.diag b) with hsdef
  have hs : ∀ b, ∏ k, s b k = 1 := fun b => ggQ2s08rNNormAt_prod c.hK h3n w (c.diag b)
  have hfrcomm : ∀ (d d' : Fin (n + 1) → c.Kˣ) (hd : ∏ k, d k = 1) (hd' : ∏ k, d' k = 1),
      c.fr (c.diagSU d hd) * c.fr (c.diagSU d' hd') =
        c.fr (c.diagSU d' hd') * c.fr (c.diagSU d hd) := by
    intro d d' hd hd'
    rw [← map_mul, ← map_mul, c.diagSU_commute]
  have htcomm : ∀ b b', t b * t b' = t b' * t b := by
    intro b b'
    refine hinj ((c.compL w).mul_mem (htmem b) (htmem b'))
      ((c.compL w).mul_mem (htmem b') (htmem b)) ?_
    rw [map_mul, map_mul, htpi, htpi]
    exact hfrcomm _ _ _ _
  have htcube : ∀ b, t b ^ 3 = 1 := by
    intro b
    refine hinj ((c.compL w).pow_mem (htmem b) 3) (c.compL w).one_mem ?_
    have hD3 : c.diagSU (s b) (hs b) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, coe_diagSU, Subgroup.coe_one, ← map_pow]
      have h3 : s b ^ 3 = 1 := funext fun k => by rw [Pi.pow_apply, c.cube, Pi.one_apply]
      rw [h3, map_one]
    rw [map_pow, htpi, ← map_pow, map_one]
    exact congrArg c.fr hD3 |>.trans (map_one c.fr)
  have hact : ∀ (b : Bs) (y : ↥L), y ∈ c.compL w →
      (b : G) * (y : G) * (b : G)⁻¹ = (t b : G) * (y : G) * (t b : G)⁻¹ := by
    intro b y hy
    rw [← e6QTwoBstarConjAction_apply c.hNL b y]
    have h := congrArg Subtype.val (htconj b y hy)
    simpa using h
  have hmemB : ∀ y : ↥L, y ∈ c.compL w → (∀ b, t b * y = y * t b) → y ^ 3 = 1 → (y : G) ∈ Bs := by
    intro y hy hcomm hy3
    refine c.hstar _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h := hact ⟨b', hb'⟩ y hy
      have h2 : (t ⟨b', hb'⟩ : G) * (y : G) * (t ⟨b', hb'⟩ : G)⁻¹ = (y : G) := by
        have := congrArg Subtype.val (hcomm ⟨b', hb'⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
        rw [this, mul_inv_cancel_right]
      calc b' * (y : G) = (b' * (y : G) * b'⁻¹) * b' := by group
        _ = (y : G) * b' := by rw [show b' * (y : G) * b'⁻¹ = (y : G) from h.trans h2]
    · have := congrArg Subtype.val hy3
      simpa using this
  have htB : ∀ b, (t b : G) ∈ Bs := fun b =>
    hmemB (t b) (htmem b) (fun b' => htcomm b' b) (htcube b)
  obtain ⟨τ, hτw, hτ2, hτ4⟩ := ggQ2s08rN_exists_perm_four (by have := c.hn; omega) w
  have hτord : orderOf τ = 2 ^ (1 + 1) := orderOf_eq_prime_pow hτ2 hτ4
  set P : ↥(LargeEvenSUGroup (Fin (n + 1)) c.K 2) :=
    (suCongrN c.K).symm (e6QTwoNPermGLSU c.hK τ) with hPdef
  have hP : P ∈ ggQ2s08rNStab c.K w := by
    refine ggQ2s08rN_permGL_mem_stab hτw P ?_
    change (e6QTwoNPermGLSU c.hK τ : GL (Fin (n + 1)) c.K) = _
    rw [e6QTwoNCoePermGLSU]
    ext i j
    simp [TauCeti.permutationGL_coe, Matrix.permMatrixHom_apply]
  obtain ⟨q, hq, hqP⟩ := c.exists_mem_compL_piL_eq w ⟨P, hP, rfl⟩
  have hPD : ∀ (d : Fin (n + 1) → c.Kˣ) (hd : ∏ k, d k = 1),
      P * c.diagSU d hd * P⁻¹ = c.diagSU (d ∘ ⇑τ.symm)
        (by rw [← hd]; exact Equiv.prod_comp τ.symm d) := by
    intro d hd
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_diagSU, coe_diagSU]
    exact ggQ2s08rN_permGLSU_conj_diag c.hK τ d
  have hqtB : ∀ b, (q : G) * (t b : G) * (q : G)⁻¹ ∈ Bs := by
    intro b
    have hmem : q * t b * q⁻¹ ∈ c.compL w :=
      (c.compL w).mul_mem ((c.compL w).mul_mem hq (htmem b)) ((c.compL w).inv_mem hq)
    have hpi : c.piL (q * t b * q⁻¹) = c.fr (c.diagSU (s b ∘ ⇑τ.symm)
        (by rw [← hs b]; exact Equiv.prod_comp τ.symm (s b))) := by
      rw [map_mul, map_mul, map_inv, hqP, htpi, ← map_inv, ← map_mul, ← map_mul, hPD]
    have hy := hmemB (q * t b * q⁻¹) hmem (fun b' => by
      refine hinj ((c.compL w).mul_mem (htmem b') hmem) ((c.compL w).mul_mem hmem (htmem b')) ?_
      rw [map_mul c.piL (t b') (q * t b * q⁻¹), map_mul c.piL (q * t b * q⁻¹) (t b'), hpi, htpi]
      exact hfrcomm _ _ _ _) (by rw [conj_pow, htcube, mul_one, mul_inv_cancel])
    simpa using hy
  have hqconj : ∀ b : Bs, (q : G) * b * (q : G)⁻¹ ∈ Bs := by
    intro b
    have h := hact b q hq
    have h' : (t b : G)⁻¹ * b * q = q * ((t b : G)⁻¹ * b) := by
      calc (t b : G)⁻¹ * b * q = (t b : G)⁻¹ * ((b : G) * q * (b : G)⁻¹) * b := by group
        _ = (t b : G)⁻¹ * ((t b : G) * q * (t b : G)⁻¹) * b := by rw [h]
        _ = q * ((t b : G)⁻¹ * b) := by group
    have h'' : (q : G)⁻¹ * ((t b : G)⁻¹ * b) = ((t b : G)⁻¹ * b) * (q : G)⁻¹ := by
      calc (q : G)⁻¹ * ((t b : G)⁻¹ * b)
          = (q : G)⁻¹ * ((t b : G)⁻¹ * b * q) * (q : G)⁻¹ := by group
        _ = (q : G)⁻¹ * (q * ((t b : G)⁻¹ * b)) * (q : G)⁻¹ := by rw [h']
        _ = ((t b : G)⁻¹ * b) * (q : G)⁻¹ := by group
    have heq : (q : G) * b * (q : G)⁻¹ =
        ((q : G) * (t b : G) * (q : G)⁻¹) * ((t b : G)⁻¹ * b) := by
      calc (q : G) * b * (q : G)⁻¹ = (q : G) * (t b : G) * (((t b : G)⁻¹ * b) * (q : G)⁻¹) := by
            group
        _ = (q : G) * (t b : G) * ((q : G)⁻¹ * ((t b : G)⁻¹ * b)) := by rw [h'']
        _ = ((q : G) * (t b : G) * (q : G)⁻¹) * ((t b : G)⁻¹ * b) := by group
    rw [heq]
    exact Bs.mul_mem (hqtB b) (Bs.mul_mem (Bs.inv_mem (htB b)) b.2)
  have hconjq : e6QTwoNConjOnQuot c.θ q = e6QTwoNFramePerm c.hK c.hQ τ := by
    have h1 : c.θ (QuotientGroup.mk' (Subgroup.center ↥L) q) =
        InndiagSU.frameMk (USixTwo.fieldDataFour c.hK) c.Q c.hQ (e6QTwoNPermGLSU c.hK τ) := by
      have h := hqP
      rw [fr_apply, hPdef, MulEquiv.apply_symm_apply] at h
      exact h
    simp only [e6QTwoNConjOnQuot]
    rw [e6QTwoQuotCenterAutHom_conj,
      ← e6QTwoMulAutConjCongr c.θ (QuotientGroup.mk' (Subgroup.center L) q), h1]
    rfl
  have hrelq : ∀ b : Bs, ∃ μ : c.Kˣ, ∀ k,
      c.diag ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ k = μ * c.diag b (τ.symm k) := by
    intro b
    have h : c.FrameDiag ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩ (c.diag b ∘ ⇑τ.symm) := by
      change TableBUD.FrameAct (USixTwo.fieldDataFour c.hK) c.Q c.hQ
        (e6QTwoNFrameAction c.hNL c.θ ⟨(q : G) * b * (q : G)⁻¹, hqconj b⟩) _
      rw [e6QTwoNFrameAction_conj c.θ c.hNL q.2 (hqconj b)]
      rw [show (⟨(q : G), q.2⟩ : ↥L) = q from rfl, hconjq]
      exact e6QTwoNFrameAct_perm c.hK (c.frameDiag_diag b) τ
    obtain ⟨μ, hμ⟩ := c.exists_eq_smul_diag h
    refine ⟨μ⁻¹, fun k => ?_⟩
    have := hμ k
    simp only [Function.comp_apply] at this
    rw [this, inv_mul_cancel_left]
  exact c.four_dvd_card_automizer_of_mem hτord hq hqconj hrelq

theorem four_dvd_card_automizer (c : GGQ2S08RoN n Bs L x) (w : Fin (n + 1)) :
    4 ∣ Nat.card ↥(ggAutomizer (c.comp w) Bs) := by
  rcases c.hZcop with hZ | ⟨hpar, h3n⟩
  · exact c.four_dvd_card_automizer_of_coprime hZ w
  · exact c.four_dvd_card_automizer_of_inner hpar h3n w

end GGQ2S08RoN

end CFSG.StandardType.E6QTwo

end
