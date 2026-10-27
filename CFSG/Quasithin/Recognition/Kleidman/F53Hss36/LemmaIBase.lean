module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Basic
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.ModFacts
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Kd (ν : Geo H M) : Subgroup G where
  carrier := {g | g ∈ stab ν ∧ g ∈ Subgroup.normalizer (Zv ν : Set G) ∧
    ∀ x ∈ Iv ν, ⁅x, g⁆ ∈ Zv ν}
  mul_mem' := by
    rintro a b ⟨ha, haN, ha'⟩ ⟨hb, hbN, hb'⟩
    refine ⟨mul_mem ha hb, mul_mem haN hbN, fun x hx => ?_⟩
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (ha' x hx) ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb' x hx))
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by
    have : ⁅x, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [this]; exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, haN, ha'⟩
    refine ⟨inv_mem ha, inv_mem haN, fun x hx => ?_⟩
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅x, a⁆⁻¹ ∈ Zv ν := inv_mem (ha' x hx)
    have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) _).mp h1
    simpa [mul_assoc] using h2

omit [Finite G] in
theorem pow_two_pow_two_pow_eq {X : Type*} [Group X] {x : X} (hx : x ^ 3 = 1) (m : ℕ) :
    (x ^ 2 ^ m) ^ 2 ^ m = x := by
  have h5 : 2 ^ m * 2 ^ m % 3 = 1 := by
    have : 2 ^ m * 2 ^ m = 4 ^ m := by rw [← mul_pow]; norm_num
    rw [this, Nat.pow_mod]; norm_num
  rw [← pow_mul]
  calc x ^ (2 ^ m * 2 ^ m) = x ^ (2 ^ m * 2 ^ m % 3 + 3 * (2 ^ m * 2 ^ m / 3)) := by
        rw [Nat.mod_add_div]
    _ = x := by rw [pow_add, pow_mul, hx, one_pow, mul_one, h5, pow_one]

theorem Kd_le_stab (ν : Geo H M) : Kd ν ≤ stab ν := fun _ hg => hg.1

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Zv_le_Iv {ν : Geo H M} : Zv ν ≤ Iv ν :=
  le_iInf₂ fun _ hε => Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm hε)

theorem isElemAbelian_Iv {ν δ : Geo H M} (hδ : δ ∈ nbrs ν) : IsElemAbelian 2 (Iv ν) := by
  have hV := isElemAbelian_Vn C.hA C.hb3 δ
  refine ⟨isMulCommutative_subgroup_iff.mpr fun a ha b hb =>
    (isMulCommutative_subgroup_iff.mp hV.1) a (Iv_le_Vn hδ ha) b (Iv_le_Vn hδ hb),
    fun x hx => hV.2 x (Iv_le_Vn hδ hx)⟩

theorem comm_Iv_Qv_mem {ν μ : Geo H M} (hν : vtype ν = true) (hμ : μ ∈ nbrs ν) {x q : G}
    (hx : x ∈ Iv ν) (hq : q ∈ Qv μ) : ⁅x, q⁆ ∈ Zv ν := by
  have hvμ := vtype_false_of_mem_nbrs_true hμ hν
  have h1 : ⁅x, q⁆ ∈ ⁅Vn μ, Qv μ⁆ := Subgroup.commutator_mem_commutator (Iv_le_Vn hμ hx) hq
  rw [C.comm_Vn_Qv_eq hvμ] at h1
  exact C.Zv_le_Zv_of_mem_nbrs hν hμ h1

theorem Qv_le_Kd {ν μ : Geo H M} (hν : vtype ν = true) (hμ : μ ∈ nbrs ν) : Qv μ ≤ Kd ν := by
  intro q hq
  have hqs : q ∈ stab ν :=
    (Qv_le_inf C.hA (mem_nbrs_comm hμ) hq).2
  exact ⟨hqs, stab_le_normalizer_Zv C.hA ν hqs, fun x hx => C.comm_Iv_Qv_mem hν hμ hx hq⟩

theorem stab_le_normalizer_Kd (ν : Geo H M) :
    stab ν ≤ Subgroup.normalizer (Kd ν : Set G) := by
  intro h hh
  have key : ∀ h ∈ stab ν, ∀ g ∈ Kd ν, h * g * h⁻¹ ∈ Kd ν := by
    intro h hh g hg
    refine ⟨mul_mem (mul_mem hh hg.1) (inv_mem hh),
      mul_mem (mul_mem (stab_le_normalizer_Zv C.hA ν hh) hg.2.1)
        (inv_mem (stab_le_normalizer_Zv C.hA ν hh)), fun x hx => ?_⟩
    have hx' : h⁻¹ * x * h ∈ Iv ν := by
      have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Iv ν (inv_mem hh)) x).mp hx
      simpa using this
    have h1 := hg.2.2 _ hx'
    have e : ⁅x, h * g * h⁻¹⁆ = h * ⁅h⁻¹ * x * h, g⁆ * h⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv C.hA ν hh) _).mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key h hh g, fun hg => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hg
  simpa [mul_assoc] using this

theorem stab_le_Kd_sup {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν) :
    stab ν ≤ Kd ν ⊔ Qv ν := by
  obtain ⟨δ', hδ', hne⟩ := exists_mem_nbrs_ne C.hA ν hδ
  have h1 := sup_edges_eq_stab C.hA hν hδ hδ' (Ne.symm hne)
  have e1 : Qv ν ⊔ Qv δ = stab ν ⊓ stab δ := C.h28 C.hb1 ν δ hδ (C.bAt_eq_of_true hν)
  have e2 : Qv ν ⊔ Qv δ' = stab ν ⊓ stab δ' := C.h28 C.hb1 ν δ' hδ' (C.bAt_eq_of_true hν)
  rw [← h1, ← e1, ← e2]
  exact sup_le (sup_le le_sup_right ((C.Qv_le_Kd hν hδ).trans le_sup_left))
    (sup_le le_sup_right ((C.Qv_le_Kd hν hδ').trans le_sup_left))

theorem cube_mem_Kd {ν δ : Geo H M} (hν : vtype ν = true) (hδ : δ ∈ nbrs ν) {g : G}
    (hg : g ∈ stab ν) (hg3 : g ^ 3 = 1) : g ∈ Kd ν := by
  have hn : ((Kd ν).subgroupOf (stab ν)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Kd_le_stab ν)).mpr
      (C.stab_le_normalizer_Kd ν)
  obtain ⟨k, hk, q, hq, hgkq⟩ := mem_sup_of_le_normalizer
    ((pCoreOf_le 2 (stab ν)).trans (C.stab_le_normalizer_Kd ν)) (C.stab_le_Kd_sup hν hδ hg)
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup (r := 2) (stab ν)) ⟨q, hq⟩
  have hq2 : q ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  set φ := QuotientGroup.mk' ((Kd ν).subgroupOf (stab ν)) with hφ
  have hkst : k ∈ stab ν := hk.1
  have hqst : q ∈ stab ν := pCoreOf_le 2 (stab ν) hq
  have h1 : φ ⟨g, hg⟩ = φ ⟨q, hqst⟩ := by
    have : (⟨g, hg⟩ : ↥(stab ν)) = ⟨k, hkst⟩ * ⟨q, hqst⟩ := Subtype.ext hgkq
    rw [this, map_mul]
    have hk' : φ ⟨k, hkst⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
    rw [hk', one_mul]
  have h2 : (⟨g, hg⟩ : ↥(stab ν)) ^ 2 ^ m ∈ (Kd ν).subgroupOf (stab ν) := by
    have e : φ ((⟨g, hg⟩ : ↥(stab ν)) ^ 2 ^ m) = 1 := by
      rw [map_pow, h1, ← map_pow]
      have : (⟨q, hqst⟩ : ↥(stab ν)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hq2)
      rw [this, map_one]
    exact (QuotientGroup.eq_one_iff _).mp e
  have h3 : g ^ 2 ^ m ∈ Kd ν := by simpa using Subgroup.mem_subgroupOf.mp h2
  have h4 : g = (g ^ 2 ^ m) ^ 2 ^ m := (pow_two_pow_two_pow_eq hg3 m).symm
  rw [h4]; exact pow_mem h3 _

theorem exists_cube {ν : Geo H M} (hν : vtype ν = true) :
    ∃ d ∈ stab ν, d ^ 3 = 1 ∧ d ∉ Qv ν := by
  obtain ⟨ψ, hs, hker⟩ := exists_quotHom_true C.hA hν
  set c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc3
  have hc3_3 : c3 ^ 3 = 1 := by decide +kernel
  have hc3_1 : c3 ≠ 1 := by decide +kernel
  obtain ⟨x, hx⟩ := hs c3
  have hx3 : (x : G) ^ 3 ∈ Qv ν := by
    have : ψ (x ^ 3) = 1 := by rw [map_pow, hx, hc3_3]
    simpa using (hker _).mp this
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup (r := 2) (stab ν)) ⟨(x : G) ^ 3, hx3⟩
  have hm' : ((x : G) ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  refine ⟨(x : G) ^ 2 ^ m, pow_mem x.2 _, ?_, fun hd => ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; exact hm'
  · have hψ : ψ (x ^ 2 ^ m) = 1 := (hker _).mpr (by simpa using hd)
    rw [map_pow, hx] at hψ
    apply hc3_1
    have := pow_two_pow_two_pow_eq hc3_3 m
    rw [hψ, one_pow] at this
    exact this.symm

omit C in
theorem smul_mem_nbrs_stab {ν ε : Geo H M} {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab ν)
    (hε : ε ∈ nbrs ν) : g • ε ∈ nbrs ν := by
  have := (smul_mem_nbrs_iff g (l := ν) (δ := ε)).mpr hε
  rwa [smul_eq_of_mem_stab hg] at this

theorem cube_smul_ne {ν ε : Geo H M} (hν : vtype ν = true) (hε : ε ∈ nbrs ν) {d : ↥(H ⊔ M)}
    (hdst : (d : G) ∈ stab ν) (hd3 : (d : G) ^ 3 = 1) (hdQ : (d : G) ∉ Qv ν) : d • ε ≠ ε := by
  intro hfix
  obtain ⟨ε', hε', hne'⟩ := exists_mem_nbrs_ne C.hA ν hε
  obtain ⟨ε'', hε'', h2, h3⟩ := exists_third_mem_nbrs C.hA hν (Ne.symm hne')
  have hnb := eq_of_three_mem_nbrs C.hA hν (Ne.symm hne') h2.symm h3.symm hε hε' hε''
  have hd1 : d • ε' ∈ nbrs ν := smul_mem_nbrs_stab hdst hε'
  have hd2 : d • ε'' ∈ nbrs ν := smul_mem_nbrs_stab hdst hε''
  have hcube : d ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hcube' : ∀ x : Geo H M, d • d • d • x = x := fun x => by
    have : (d ^ 3) • x = x := by rw [hcube, one_smul]
    simpa [pow_succ, mul_smul] using this
  rw [hnb] at hd1 hd2
  have inj : ∀ a b : Geo H M, d • a = d • b → a = b := fun a b h => smul_left_cancel d h
  rcases hd1 with h | h | h
  · exact hne' (inj _ _ (h.trans hfix.symm))
  ·
    exact hdQ (mem_Qv_of_fixes_two_nbrs C.hA hν hε hε' (Ne.symm hne') hdst
      (mem_stab_of_smul_eq (g := d) hfix) (mem_stab_of_smul_eq (g := d) h))
  · rcases hd2 with h' | h' | h'
    · exact h2 (inj _ _ (h'.trans hfix.symm))
    ·
      have : d • d • d • ε' = ε' := hcube' ε'
      rw [h, h', h] at this
      exact h3 this
    · exact h3 (inj _ _ (h'.trans h.symm))

theorem cube_exists_pow_smul {ν ε ε' : Geo H M} (hν : vtype ν = true) (hε : ε ∈ nbrs ν)
    (hε' : ε' ∈ nbrs ν) {d : ↥(H ⊔ M)} (hdst : (d : G) ∈ stab ν) (hd3 : (d : G) ^ 3 = 1)
    (hdQ : (d : G) ∉ Qv ν) : ∃ i : ℕ, d ^ i • ε = ε' := by
  have hcube : d ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hne1 : d • ε ≠ ε := C.cube_smul_ne hν hε hdst hd3 hdQ
  have hdε : d • ε ∈ nbrs ν := smul_mem_nbrs_stab hdst hε
  have hdd : d • d • ε ∈ nbrs ν := smul_mem_nbrs_stab hdst hdε
  have hne2 : d • d • ε ≠ d • ε := C.cube_smul_ne hν hdε hdst hd3 hdQ
  have hne3 : d • d • ε ≠ ε := by
    intro h
    have : d • d • d • ε = d • ε := by rw [h]
    have h3 : d • d • d • ε = ε := by
      have : (d ^ 3) • ε = ε := by rw [hcube, one_smul]
      simpa [pow_succ, mul_smul] using this
    exact hne1 (by rw [← this, h3])
  have hnb := eq_of_three_mem_nbrs C.hA hν hne1.symm hne3.symm hne2.symm hε hdε hdd
  have hmem : ε' ∈ ({ε, d • ε, d • d • ε} : Set (Geo H M)) := hnb ▸ hε'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact ⟨0, by simpa using h.symm⟩
  · exact ⟨1, by simpa using h.symm⟩
  · exact ⟨2, by simp [pow_succ, mul_smul, h.symm]⟩

theorem cube_fixed_Zv {ν : Geo H M} (hν : vtype ν = true) {d : G} (hdst : d ∈ stab ν)
    (hd3 : d ^ 3 = 1) (hdQ : d ∉ Qv ν) : ∀ z ∈ Zv ν, d * z * d⁻¹ = z → z = 1 := by
  have hN : d ∈ Subgroup.normalizer (Zv ν : Set G) := stab_le_normalizer_Zv C.hA ν hdst
  have hconj : ∀ x ∈ Zv ν, d * x * d⁻¹ ∈ Zv ν := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have hconji : ∀ x ∈ Zv ν, d⁻¹ * x * d⁻¹⁻¹ ∈ Zv ν := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (inv_mem hN) x).mp hx
  have hZ4 := C.card_Zv_true hν
  have hfin : Finite (Zv ν) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup (Zv ν),
      F = (Subgroup.centralizer ({d} : Set G)).subgroupOf (Zv ν) := ⟨_, rfl⟩
  have hFix : ∀ x : Zv ν, conjPermOf hconj hconji x = x ↔ d * (x : G) = (x : G) * d := by
    intro x
    rw [Subtype.ext_iff, conjPermOf_apply_val, mul_inv_eq_iff_eq_mul]
  have hmem : ∀ x : Zv ν, x ∈ F ↔ d * (x : G) = (x : G) * d := by
    intro x
    simp [hFdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  have hcardF : Nat.card {x : Zv ν // conjPermOf hconj hconji x = x} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [hFix, hmem])
  have hmod : Nat.card (Zv ν) ≡ Nat.card {x : Zv ν // conjPermOf hconj hconji x = x} [MOD 3] :=
    CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.natCard_fixed_modEq_three _
      (conjPermOf_pow_three hconj hconji hd3)
  rw [hZ4, hcardF] at hmod
  have hdvd : Nat.card F ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card F
    rwa [hZ4] at this
  have hF1 : Nat.card F = 1 := by
    have hcle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card F := Nat.card_pos
    by_contra hne1
    have h4 : Nat.card F = 4 := by
      unfold Nat.ModEq at hmod
      generalize hc : Nat.card F = c at hmod hdvd hcle hpos hne1
      interval_cases c <;> omega
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [h4, hZ4])
    have hcent : d ∈ Subgroup.centralizer (Zv ν : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzF : (⟨z, hz⟩ : Zv ν) ∈ F := by rw [htop]; exact Subgroup.mem_top _
      exact ((hmem _).mp hzF).symm
    have h12 := centralizer_Zv_eq_Qv_of_bAt C.hA (C.bAt_eq_of_true hν)
    exact hdQ (by rw [← h12]; exact ⟨hdst, hcent⟩)
  intro z hz hzd
  have hzF : (⟨z, hz⟩ : Zv ν) ∈ F := by
    rw [hmem]
    rw [mul_inv_eq_iff_eq_mul] at hzd
    exact hzd
  have hbot : F = ⊥ := (Subgroup.card_eq_one).mp hF1
  rw [hbot, Subgroup.mem_bot] at hzF
  exact congrArg Subtype.val hzF

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
