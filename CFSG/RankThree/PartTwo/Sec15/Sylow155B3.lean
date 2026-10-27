module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155B2
public import CFSG.RankThree.PartTwo.Sec15.Sylow155B3Q
import CFSG.RankThree.PartTwo.Sec15.Sylow155KerZ
import CFSG.RankThree.PartTwo.Sec15.Sylow155Gen
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
open scoped commutatorElement

namespace Sylow155B3

open Sylow155R

section Center

variable {Q : Type} [Group Q]

theorem mulAut_mem_center (σ : MulAut Q) {z : Q} (hz : z ∈ Subgroup.center Q) :
    σ z ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨h, rfl⟩ := σ.surjective g
  rw [← map_mul, ← map_mul, hz h]

theorem center_eq_zpowers [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3) {ζ : Q}
    (hζ : ζ ∈ Subgroup.center Q) (hζ1 : ζ ≠ 1) : Subgroup.center Q = Subgroup.zpowers ζ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers ζ ≤ Subgroup.center Q := Subgroup.zpowers_le.mpr hζ
  have h3 : Nat.card (Subgroup.zpowers ζ) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (pow_three_of_mem_center hZ hζ) hζ1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, h3])).symm

theorem fixes_center_of_fixes [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3) {ζ : Q}
    (hζ : ζ ∈ Subgroup.center Q) (hζ1 : ζ ≠ 1) {σ : MulAut Q} (hσ : σ ζ = ζ) :
    ∀ z ∈ Subgroup.center Q, σ z = z := by
  intro z hz
  rw [center_eq_zpowers hZ hζ hζ1] at hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [map_zpow, hσ]

theorem fixes_center_of_pow_three [Finite Q] (hZ : Nat.card (Subgroup.center Q) = 3)
    {σ : MulAut Q} (hσ : σ ^ 3 = 1) : ∀ z ∈ Subgroup.center Q, σ z = z := by
  obtain ⟨ζ, hζ, hζ1⟩ := LocalAnalysis.GLTheoremB.Prop95I1921.exists_mem_center_ne_one hZ
  refine fixes_center_of_fixes hZ hζ hζ1 ?_
  have hζ3 : ζ ^ (3 : ℤ) = 1 := by exact_mod_cast pow_three_of_mem_center hZ hζ
  have hσζ : σ ζ ∈ Subgroup.zpowers ζ := by
    rw [← center_eq_zpowers hZ hζ hζ1]
    exact mulAut_mem_center σ hζ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσζ
  rw [zpow_eq_zpow_emod k hζ3] at hk
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h, zpow_zero] at hk
    exact absurd (σ.map_eq_one_iff.mp hk.symm) hζ1
  · rw [h, zpow_one] at hk
    exact hk.symm
  · rw [h] at hk
    have h2 : σ ζ = ζ⁻¹ := by
      rw [← hk, eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
      exact hζ3
    have hσσ : (σ * σ) ζ = ζ := by rw [MulAut.mul_apply, h2, map_inv, h2, inv_inv]
    calc σ ζ = σ ((σ * σ) ζ) := by rw [hσσ]
      _ = (σ ^ 3) ζ := by simp only [pow_three, MulAut.mul_apply]
      _ = ζ := by rw [hσ, MulAut.one_apply]

end Center

section Rho6

variable {G : Type} [Group G] {W K : Subgroup G} [(K.subgroupOf W).Normal]

theorem mk_eq_mk_iff {x y : G} (hx : x ∈ W) (hy : y ∈ W) :
    (QuotientGroup.mk ⟨x, hx⟩ : ↥W ⧸ K.subgroupOf W) = QuotientGroup.mk ⟨y, hy⟩ ↔
      x⁻¹ * y ∈ K := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem mk_eq_mk_of_mul_inv_mem (hWK : W ≤ Subgroup.normalizer (K : Set G)) {x y : G}
    (hx : x ∈ W) (hy : y ∈ W) (h : x * y⁻¹ ∈ K) :
    (QuotientGroup.mk ⟨x, hx⟩ : ↥W ⧸ K.subgroupOf W) = QuotientGroup.mk ⟨y, hy⟩ := by
  rw [mk_eq_mk_iff]
  have h1 := (Subgroup.mem_normalizer_iff.mp (hWK (W.inv_mem hx)) _).mp (K.inv_mem h)
  have e : x⁻¹ * (x * y⁻¹)⁻¹ * x⁻¹⁻¹ = x⁻¹ * y := by group
  rwa [e] at h1

theorem qAct_mk_eq_iff (hWK : W ≤ Subgroup.normalizer (K : Set G)) (g : ↥(nWK W K)) {y : G}
    (hy : y ∈ W) :
    qAct W K g (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ ↔
      (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ K := by
  rw [qAct_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    conjW_apply]
  have hyK := hWK hy
  constructor
  · intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp hyK _).mp (K.inv_mem h)
    have e : y * (((g : G) * y * (g : G)⁻¹)⁻¹ * y)⁻¹ * y⁻¹ = (g : G) * y * (g : G)⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1
  · intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyK) _).mp h
    have h2 := K.inv_mem h1
    have e : (y⁻¹ * ((g : G) * y * (g : G)⁻¹ * y⁻¹) * y⁻¹⁻¹)⁻¹ =
        ((g : G) * y * (g : G)⁻¹)⁻¹ * y := by group
    rwa [e] at h2

theorem mk_mem_center_of_qAct_eq_one (hWK : W ≤ Subgroup.normalizer (K : Set G)) {w : G}
    (hw : w ∈ W) (h : qAct W K ⟨w, mem_nWK hWK hw⟩ = 1) :
    (QuotientGroup.mk ⟨w, hw⟩ : ↥W ⧸ K.subgroupOf W) ∈
      Subgroup.center (↥W ⧸ K.subgroupOf W) := by
  rw [qAct_mem W K hWK w hw] at h
  rw [Subgroup.mem_center_iff]
  intro q
  have h1 := congrArg (fun σ : MulAut (↥W ⧸ K.subgroupOf W) => σ q) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

variable (ψ6 : (↥W ⧸ K.subgroupOf W) ⧸ Subgroup.center (↥W ⧸ K.subgroupOf W) ≃*
  ↥A6Models.psl29)

@[expose] noncomputable def rho6 : ↥(nWK W K) →* P10 :=
  A6Models.autA6.subtype.comp ((Sylow155B3Q.rhoQ ψ6).comp (qAct W K))

theorem rho6_apply (g : ↥(nWK W K)) :
    rho6 ψ6 g = ((Sylow155B3Q.rhoQ ψ6 (qAct W K g) : ↥A6Models.autA6) : P10) :=
  rfl

theorem rho6_mem_autA6 (g : ↥(nWK W K)) : rho6 ψ6 g ∈ A6Models.autA6 :=
  (Sylow155B3Q.rhoQ ψ6 (qAct W K g)).2

theorem rho6_spec (g : ↥(nWK W K)) (q : ↥W ⧸ K.subgroupOf W) :
    ((ψ6 (QuotientGroup.mk (qAct W K g q)) : ↥A6Models.psl29) : P10) =
      rho6 ψ6 g * (ψ6 (QuotientGroup.mk q) : P10) * (rho6 ψ6 g)⁻¹ :=
  Sylow155B3Q.rhoQ_spec ψ6 (qAct W K g) q

theorem rho6_mem (hWK : W ≤ Subgroup.normalizer (K : Set G)) (w : G) (hw : w ∈ W) :
    rho6 ψ6 ⟨w, mem_nWK hWK hw⟩ =
      ((ψ6 (QuotientGroup.mk (QuotientGroup.mk ⟨w, hw⟩ : ↥W ⧸ K.subgroupOf W)) :
        ↥A6Models.psl29) : P10) := by
  rw [rho6_apply, qAct_mem W K hWK w hw]
  exact Sylow155B3Q.rhoQ_conj ψ6 _

theorem rho6_eq_one_iff (hperf : commutator (↥W ⧸ K.subgroupOf W) = ⊤) (g : ↥(nWK W K)) :
    rho6 ψ6 g = 1 ↔ qAct W K g = 1 := by
  rw [rho6_apply, OneMemClass.coe_eq_one, Sylow155B3Q.rhoQ_eq_one_iff hperf]

theorem rho6_eq_one_of_mem (hWK : W ≤ Subgroup.normalizer (K : Set G)) (k : G) (hkW : k ∈ W)
    (hkK : k ∈ K) : rho6 ψ6 ⟨k, mem_nWK hWK hkW⟩ = 1 := by
  rw [rho6_mem ψ6 hWK k hkW]
  have h1 : (QuotientGroup.mk ⟨k, hkW⟩ : ↥W ⧸ K.subgroupOf W) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkK)
  rw [h1, QuotientGroup.mk_one, map_one, OneMemClass.coe_one]

theorem exists_rho6_eq (hWK : W ≤ Subgroup.normalizer (K : Set G)) {x : P10}
    (hx : x ∈ A6Models.psl29) : ∃ (w : G) (hw : w ∈ W), rho6 ψ6 ⟨w, mem_nWK hWK hw⟩ = x := by
  obtain ⟨q, hq⟩ := ψ6.surjective ⟨x, hx⟩
  obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q'
  refine ⟨w, w.2, ?_⟩
  rw [rho6_mem ψ6 hWK _ w.2]
  exact congrArg Subtype.val hq

end Rho6

section Kernel

variable {G : Type} [Group G] [Finite G] {W K : Subgroup G} [(K.subgroupOf W).Normal]

theorem exists_mem_inf_center {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3) :
    ∃ (z : G) (hz : z ∈ A ⊓ W),
      (QuotientGroup.mk ⟨z, hz.2⟩ : ↥W ⧸ K.subgroupOf W) ∈
          Subgroup.center (↥W ⧸ K.subgroupOf W) ∧
        (QuotientGroup.mk ⟨z, hz.2⟩ : ↥W ⧸ K.subgroupOf W) ≠ 1 := by
  obtain ⟨ζ, hζ, hζ1⟩ := LocalAnalysis.GLTheoremB.Prop95I1921.exists_mem_center_ne_one hZ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ζ
  have hfix : ∀ a ∈ A, a * (y : G) * a⁻¹ * (y : G)⁻¹ ∈ K := by
    intro a ha
    have h3 : qAct W K ⟨a, hAW ha, hAK ha⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have e : (⟨a, hAW ha, hAK ha⟩ : ↥(nWK W K)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hAF.1.2 a ha)
      rw [e, map_one]
    exact (qAct_mk_eq_iff hWK _ y.2).mp (fixes_center_of_pow_three hZ h3 _ hζ)
  have hy3 : (y : G) ^ 3 ∈ K := by
    have h := pow_three_of_mem_center hZ hζ
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨a₀, ha₀, ha₀K⟩ := exists_mem_inf_of_fixed hAF hAW hAK hWK hK y.2 hfix hy3
  refine ⟨a₀, ha₀, ?_⟩
  rw [mk_eq_mk_of_mul_inv_mem hWK ha₀.2 y.2 ha₀K]
  exact ⟨hζ, hζ1⟩

theorem exists_eq_mul_zpow (hWK : W ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3) {z₀ : G} (hz₀ : z₀ ∈ W)
    (hz₀Z : (QuotientGroup.mk ⟨z₀, hz₀⟩ : ↥W ⧸ K.subgroupOf W) ∈
      Subgroup.center (↥W ⧸ K.subgroupOf W))
    (hz₀1 : (QuotientGroup.mk ⟨z₀, hz₀⟩ : ↥W ⧸ K.subgroupOf W) ≠ 1) {w : G} (hw : w ∈ W)
    (h : qAct W K ⟨w, mem_nWK hWK hw⟩ = 1) :
    ∃ k ∈ K ⊓ W, ∃ n : ℤ, w = k * z₀ ^ n := by
  have hc := mk_mem_center_of_qAct_eq_one hWK hw h
  rw [center_eq_zpowers hZ hz₀Z hz₀1] at hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hzn : z₀ ^ n ∈ W := W.zpow_mem hz₀ n
  have hn' : (QuotientGroup.mk ⟨z₀ ^ n, hzn⟩ : ↥W ⧸ K.subgroupOf W) =
      QuotientGroup.mk ⟨w, hw⟩ := by
    rw [← hn, ← QuotientGroup.mk_zpow]
    rfl
  rw [mk_eq_mk_iff] at hn'
  refine ⟨w * (z₀ ^ n)⁻¹, ⟨?_, W.mul_mem hw (W.inv_mem hzn)⟩, n, by group⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp (hWK hzn) _).mp hn'
  have e : z₀ ^ n * ((z₀ ^ n)⁻¹ * w) * (z₀ ^ n)⁻¹ = w * (z₀ ^ n)⁻¹ := by group
  rwa [e] at h1

omit [Finite G] in
variable (W K) in
noncomputable abbrev fixZ : Subgroup G :=
  ((fixingSubgroup (MulAut (↥W ⧸ K.subgroupOf W))
    ((Subgroup.center (↥W ⧸ K.subgroupOf W) : Subgroup (↥W ⧸ K.subgroupOf W)) :
      Set (↥W ⧸ K.subgroupOf W))).comap (qAct W K)).map (nWK W K).subtype

omit [Finite G] in
theorem mem_fixZ_iff {x : G} : x ∈ fixZ W K ↔ ∃ hx : x ∈ nWK W K,
    ∀ z ∈ Subgroup.center (↥W ⧸ K.subgroupOf W), qAct W K ⟨x, hx⟩ z = z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun z hz => (mem_fixingSubgroup_iff _).mp hy z hz⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, (mem_fixingSubgroup_iff _).mpr fun z hz => h z hz, rfl⟩

omit [Finite G] in
theorem conj_mem_fixZ {g : G} (hg : g ∈ nWK W K) {x : G} (hx : x ∈ fixZ W K) :
    g * x * g⁻¹ ∈ fixZ W K := by
  obtain ⟨hxn, hfx⟩ := mem_fixZ_iff.mp hx
  have hgx : g * x * g⁻¹ ∈ nWK W K :=
    (nWK W K).mul_mem ((nWK W K).mul_mem hg hxn) ((nWK W K).inv_mem hg)
  refine mem_fixZ_iff.mpr ⟨hgx, fun z hz => ?_⟩
  have e : (⟨g * x * g⁻¹, hgx⟩ : ↥(nWK W K)) = ⟨g, hg⟩ * ⟨x, hxn⟩ * (⟨g, hg⟩)⁻¹ :=
    Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
    hfx _ (mulAut_mem_center (qAct W K ⟨g, hg⟩)⁻¹ hz), MulAut.apply_inv_self]

theorem le_fixZ {A V : Subgroup G} (hAF : A ∈ partTwoF G) (hAn : A ≤ nWK W K)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hZ : Nat.card (Subgroup.center (↥W ⧸ K.subgroupOf W)) = 3) (hVn : V ≤ nWK W K)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hV3 : ¬ 3 ∣ Nat.card V) : V ≤ fixZ W K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha => (hAn ha).1
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha => (hAn ha).2
  obtain ⟨z₀, hz₀, hz₀Z, hz₀1⟩ := exists_mem_inf_center hAF hAW hAK hWK hK hZ
  have hAfix : ∀ (a : G) (ha : a ∈ A), ∀ z ∈ Subgroup.center (↥W ⧸ K.subgroupOf W),
      qAct W K ⟨a, hAn ha⟩ z = z := by
    intro a ha
    refine fixes_center_of_pow_three hZ ?_
    rw [← map_pow]
    have e : (⟨a, hAn ha⟩ : ↥(nWK W K)) ^ 3 = 1 := Subtype.ext (by simpa using hAF.1.2 a ha)
    rw [e, map_one]
  have hAL : A ≤ Subgroup.normalizer (fixZ W K : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => conj_mem_fixZ (hAn ha) hx, fun hx => ?_⟩
    have h1 := conj_mem_fixZ ((nWK W K).inv_mem (hAn ha)) hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rwa [e] at h1
  have hcop : ¬ 3 ∣ Nat.card ↥(V ⊓ fixZ W K) := fun h3 =>
    hV3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  intro v hv
  have hvn := hVn hv
  have hfix : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ fixZ W K := by
    intro a ha
    have hmem : a * v * a⁻¹ * v⁻¹ ∈ nWK W K :=
      (nWK W K).mul_mem ((nWK W K).mul_mem ((nWK W K).mul_mem (hAn ha) hvn)
        ((nWK W K).inv_mem (hAn ha))) ((nWK W K).inv_mem hvn)
    refine mem_fixZ_iff.mpr ⟨hmem, fun z hz => ?_⟩
    have e : (⟨a * v * a⁻¹ * v⁻¹, hmem⟩ : ↥(nWK W K)) =
        ⟨a, hAn ha⟩ * ⟨v, hvn⟩ * (⟨a, hAn ha⟩)⁻¹ * (⟨v, hvn⟩)⁻¹ := Subtype.ext rfl
    have hz' : (qAct W K ⟨v, hvn⟩)⁻¹ z ∈ Subgroup.center (↥W ⧸ K.subgroupOf W) :=
      mulAut_mem_center _ hz
    have hainv : (qAct W K ⟨a, hAn ha⟩)⁻¹ ((qAct W K ⟨v, hvn⟩)⁻¹ z) =
        (qAct W K ⟨v, hvn⟩)⁻¹ z :=
      (MulEquiv.symm_apply_eq _).mpr (hAfix a ha _ hz').symm
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      MulAut.mul_apply, hainv, MulAut.apply_inv_self, hAfix a ha z hz]
  obtain ⟨c, hcV, hcA, hcv⟩ := Sylow155G.exists_fixed_mul_inv_mem hA3 hAV hAL hcop hv hfix
  have hcn := hVn hcV
  have hcL : c ∈ fixZ W K := by
    refine mem_fixZ_iff.mpr ⟨hcn, fixes_center_of_fixes hZ hz₀Z hz₀1 ?_⟩
    rw [qAct_mk_eq_iff hWK ⟨c, hcn⟩ hz₀.2]
    show c * z₀ * c⁻¹ * z₀⁻¹ ∈ K
    have h1 := hcA z₀ hz₀.1
    have e : c * z₀ * c⁻¹ * z₀⁻¹ = 1 := by
      calc c * z₀ * c⁻¹ * z₀⁻¹ = (z₀ * c * z₀⁻¹) * z₀ * c⁻¹ * z₀⁻¹ := by rw [h1]
        _ = 1 := by group
    rw [e]
    exact K.one_mem
  have e : v = (c * v⁻¹)⁻¹ * c := by group
  rw [e]
  exact (fixZ W K).mul_mem ((fixZ W K).inv_mem hcv) hcL

end Kernel

section Sec155

variable {G : Type} [Group G] [Finite G]
variable {A X K Y M T P : Subgroup G} [((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal]
  (ψ6 : (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) ⧸
    Subgroup.center (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) ≃*
      ↥A6Models.psl29)

theorem delta_le_fixZ {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hC : Ctx155 A X K Y M T)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card (Subgroup.center
      (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X))) = 3) :
    delta A (lB A) M ≤ fixZ (w155 A M X) (pPrimeCoreOf 3 M) :=
  sSup_le fun V hV => le_fixZ h.mem_partTwoF (Sylow155B2.a_le_nWK hC)
    (Sylow155B2.w155_le_normalizer A M X)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)) hZ
    ((le_delta hV.1 hV.2).trans (Sylow155B2.delta_le_nWK hIX)) hV.1.1.2.2
    ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp hV.1.1.2.1)

theorem commutator_mem_of_rho6_eq_one
    (hperf : commutator (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) = ⊤)
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hC : Ctx155 A X K Y M T)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card (Subgroup.center
      (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X))) = 3)
    {w : G} (hw : w ∈ w155 A M X)
    (hρ : rho6 ψ6 ⟨w, mem_nWK (Sylow155B2.w155_le_normalizer A M X) hw⟩ = 1) {u : G}
    (hu : u ∈ u155 A M X) : w * u * w⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWK := Sylow155B2.w155_le_normalizer A M X
  have hc := mk_mem_center_of_qAct_eq_one hWK hw ((rho6_eq_one_iff ψ6 hperf _).mp hρ)
  obtain ⟨hun, hfix⟩ := mem_fixZ_iff.mp (delta_le_fixZ h hC hIX hZ hu.1)
  have h1 : u * w * u⁻¹ * w⁻¹ ∈ pPrimeCoreOf 3 M :=
    (qAct_mk_eq_iff hWK ⟨u, hun⟩ hw).mp (hfix _ hc)
  have hmemW : u * w * u⁻¹ * w⁻¹ ∈ w155 A M X :=
    (w155 A M X).mul_mem ((Subgroup.mem_normalizer_iff.mp hun.1 w).mp hw)
      ((w155 A M X).inv_mem hw)
  have hle : w155 A M X ⊓ pPrimeCoreOf 3 M ≤ pPrimeCoreOf 3 (u155 A M X) :=
    le_pPrimeCoreOf (inf_le_left.trans (Proof155Wx.w155_le_u155 A M X))
      ((Sylow155B2.u155_le_nWK A M X).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (coprime_card_pPrimeCoreOf 3 M))
  have e : w * u * w⁻¹ * u⁻¹ = (u * w * u⁻¹ * w⁻¹)⁻¹ := by group
  rw [e]
  exact (pPrimeCoreOf 3 (u155 A M X)).inv_mem (hle ⟨hmemW, h1⟩)

theorem rho6_eq_one_of_mem_x (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) {x : G} (hx : x ∈ X)
    (hxn : x ∈ nWK (w155 A M X) (pPrimeCoreOf 3 M)) : rho6 ψ6 ⟨x, hxn⟩ = 1 := by
  have hq : qAct (w155 A M X) (pPrimeCoreOf 3 M) ⟨x, hxn⟩ = 1 := by
    refine Sylow155B2.qAct_eq_one _ fun w hw => ?_
    have h1 : ⁅w, x⁆ ∈ CFSG.Open.pCoreOf 2 M :=
      Proof155P.commutator_w155_le hf hX (Subgroup.commutator_mem_commutator hw hx)
    have h2 := Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf M ((CFSG.Open.pCoreOf 2 M).inv_mem h1)
    rw [commutatorElement_inv, commutatorElement_def] at h2
    exact h2
  rw [rho6_apply, hq, map_one, OneMemClass.coe_one]

theorem ker_central6
    (hperf : commutator (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X)) = ⊤)
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hC : Ctx155 A X K Y M T)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card (Subgroup.center
      (↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X))) = 3)
    (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X) {k : G} (hk : k ∈ u155 A M X)
    (hρ : rho6 ψ6 ⟨k, Sylow155B2.u155_le_nWK A M X hk⟩ = 1) :
    (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
      ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X) :=
  Sylow155KZ.ker_central_u155_of_central hBXW
    ((rho6 ψ6).comp (Subgroup.inclusion (Sylow155B2.u155_le_nWK A M X)))
    (fun _ hx _ => rho6_eq_one_of_mem_x ψ6 hf hX hx _)
    (fun _ hw hρw _ hu => commutator_mem_of_rho6_eq_one ψ6 hperf h hC hIX hZ hw hρw hu) hk hρ

end Sec155

section Criterion

variable {G : Type} [Group G] [Finite G]
variable {A X K Y M T P : Subgroup G} {H : Type*} [Group H]
  (f : ↥(Sylow155R.nWK (w155 A M X) (pPrimeCoreOf 3 M)) →* H)

noncomputable abbrev imR (Y : Subgroup G) : Subgroup H :=
  ((CFSG.Open.pCoreOf 2 Y).subgroupOf (nWK (w155 A M X) (pPrimeCoreOf 3 M))).map f

theorem conj_mem_sup_of_ker
    (hker : ∀ {k : G} (hk : k ∈ u155 A M X), f ⟨k, Sylow155B2.u155_le_nWK A M X hk⟩ = 1 →
      (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
        ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X))
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {g : G}
    (hgI : g ∈ delta A (lB A) M)
    (hgR : f ⟨g, Sylow155B2.delta_le_nWK hIX hgI⟩ ∈ Subgroup.normalizer (imR f Y : Set H))
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) :
    g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := u155 A M X with hUdef
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hRU : R ≤ U := Sylow155F.r_le_u155 hE hRP
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hgU : g ∈ Subgroup.normalizer (U : Set G) :=
    Sylow155B1.le_normalizer_u155 Subgroup.le_normalizer hIX hgI
  have hgU0 : g ∈ Subgroup.normalizer (pPrimeCoreOf 3 U : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 U hgU
  have h2pow : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m = 1 := by
    intro r hr
    obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
    have h := congrArg Subtype.val hm
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact ⟨m, h⟩
  suffices hle : R ⊔ pPrimeCoreOf 3 U ≤
      (R ⊔ pPrimeCoreOf 3 U).comap (MulAut.conj g).toMonoidHom from hle hx
  refine sup_le (fun r hr => ?_) (fun y hy => ?_)
  ·
    change g * r * g⁻¹ ∈ R ⊔ pPrimeCoreOf 3 U
    have hrU := hRU hr
    have hgr : g * r * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgU r).mp hrU
    have hρr : f ⟨r, Sylow155B2.u155_le_nWK A M X hrU⟩ ∈ imR f Y :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
    have hρ := (Subgroup.mem_normalizer_iff.mp hgR _).mp hρr
    obtain ⟨r'', hr'', hρr''⟩ := Subgroup.mem_map.mp hρ
    rw [Subgroup.mem_subgroupOf] at hr''
    set r' : G := (r'' : G) with hr'def
    have hr'U : r' ∈ U := hRU hr''
    have hkU : r'⁻¹ * (g * r * g⁻¹) ∈ U := U.mul_mem (U.inv_mem hr'U) hgr
    have hρk : f ⟨r'⁻¹ * (g * r * g⁻¹), Sylow155B2.u155_le_nWK A M X hkU⟩ = 1 := by
      have e : (⟨r'⁻¹ * (g * r * g⁻¹), Sylow155B2.u155_le_nWK A M X hkU⟩ :
          ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) =
          r''⁻¹ * ((⟨g, Sylow155B2.delta_le_nWK hIX hgI⟩ :
            ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) *
            ⟨r, Sylow155B2.u155_le_nWK A M X hrU⟩ * (⟨g, Sylow155B2.delta_le_nWK hIX hgI⟩)⁻¹) :=
        Subtype.ext rfl
      rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hρr'', inv_mul_cancel]
    obtain ⟨hcen, m, hm⟩ := hker hkU hρk
    have hrc : r' * (r'⁻¹ * (g * r * g⁻¹)) * r'⁻¹ * (r'⁻¹ * (g * r * g⁻¹))⁻¹ ∈
        pPrimeCoreOf 3 U := by
      have h := (pPrimeCoreOf 3 U).inv_mem (hcen r' hr'U)
      have e : r' * (r'⁻¹ * (g * r * g⁻¹)) * r'⁻¹ * (r'⁻¹ * (g * r * g⁻¹))⁻¹ =
          ((r'⁻¹ * (g * r * g⁻¹)) * r' * (r'⁻¹ * (g * r * g⁻¹))⁻¹ * r'⁻¹)⁻¹ := by group
      rw [e]
      exact h
    have hrc2 : ∃ m : ℕ, (r' * (r'⁻¹ * (g * r * g⁻¹))) ^ 2 ^ m = 1 := by
      obtain ⟨m', hm'⟩ := h2pow r hr
      refine ⟨m', ?_⟩
      rw [mul_inv_cancel_left, conj_pow, hm', mul_one, mul_inv_cancel]
    have hk0 := Sylow155G.mem_of_mul_pow_two (le_normalizer_pPrimeCoreOf 3 U) hr'U hkU hrc
      (h2pow r' hr'') ⟨m, hm⟩ hrc2
    have e : g * r * g⁻¹ = r' * (r'⁻¹ * (g * r * g⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hr'' hk0
  · change g * y * g⁻¹ ∈ R ⊔ pPrimeCoreOf 3 U
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgU0 y).mp hy)

theorem mem_normalizer_sup_of_ker
    (hker : ∀ {k : G} (hk : k ∈ u155 A M X), f ⟨k, Sylow155B2.u155_le_nWK A M X hk⟩ = 1 →
      (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
        ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X))
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) {g : G}
    (hgI : g ∈ delta A (lB A) M)
    (hgR : f ⟨g, Sylow155B2.delta_le_nWK hIX hgI⟩ ∈ Subgroup.normalizer (imR f Y : Set H)) :
    g ∈ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) : Subgroup G) : Set G) := by
  have hgI' : g⁻¹ ∈ delta A (lB A) M := (delta A (lB A) M).inv_mem hgI
  have hgR' : f ⟨g⁻¹, Sylow155B2.delta_le_nWK hIX hgI'⟩ ∈
      Subgroup.normalizer (imR f Y : Set H) := by
    have e : (⟨g⁻¹, Sylow155B2.delta_le_nWK hIX hgI'⟩ :
        ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) = (⟨g, Sylow155B2.delta_le_nWK hIX hgI⟩)⁻¹ :=
      Subtype.ext rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ hgR
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact conj_mem_sup_of_ker f hker hE hRP hIX hgI hgR hx
  · have h := conj_mem_sup_of_ker f hker hE hRP hIX hgI' hgR' hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

end Criterion

end Sylow155B3

end CFSG.RankThree.PartTwo.Sec15
