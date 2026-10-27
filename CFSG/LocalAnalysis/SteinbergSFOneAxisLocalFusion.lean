module

public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourOuterSquare

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace OneAxisFusion

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Act

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

theorem normAct_of_eq (φ : L ≃* X) {x : normalizer (L : Set G)} {l : L} (hxl : (x : G) = l) :
    normAct φ x = MulAut.conj (φ l) := by
  have : x = ⟨l, le_normalizer l.2⟩ := Subtype.ext hxl
  rw [this, normAct_of_mem]

theorem coe_symm_pow (φ : L ≃* X) (a : X) (k : ℕ) :
    ((φ.symm (a ^ k) : L) : G) = ((φ.symm a : L) : G) ^ k := by
  rw [map_pow, SubgroupClass.coe_pow]

theorem coe_symm_eq_one_iff (φ : L ≃* X) {a : X} : ((φ.symm a : L) : G) = 1 ↔ a = 1 := by
  constructor
  · intro h
    exact φ.symm.map_eq_one_iff.mp (Subtype.ext h)
  · rintro rfl
    simp

end Act

theorem exists_conj_of_outer {G : Type} [Group G]
    {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (φ : L ≃* antiSp K) {v : G} (hv : v ∈ normalizer (L : Set G))
    (hvv : v * v = 1) (hout : normAct φ ⟨v, hv⟩ ∉ inner (antiSp K)) {y : G} (hyL : y ∈ L)
    (hyv : v * y = y * v) (hyy : y * y = 1) : ∃ l ∈ L, v * y = l * v * l⁻¹ := by
  obtain ⟨-, -, -, hall⟩ := even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  set x : normalizer (L : Set G) := ⟨v, hv⟩
  set yN : normalizer (L : Set G) := ⟨y, le_normalizer hyL⟩
  have hθθ : normAct φ x * normAct φ x = 1 := by
    rw [← map_mul, show x * x = 1 from Subtype.ext hvv, map_one]
  obtain ⟨hconj, -, -⟩ := hall (normAct φ x) hθθ hout
  have hxy : x * yN * (x * yN) = 1 := Subtype.ext (by
    change v * y * (v * y) = 1
    calc v * y * (v * y) = v * (y * v) * y := by group
      _ = v * v * (y * y) := by rw [← hyv]; group
      _ = 1 := by rw [hvv, hyy, one_mul])
  have hθk : normAct φ (x * yN) * normAct φ (x * yN) = 1 := by
    rw [← map_mul, hxy, map_one]
  have hθk' : normAct φ (x * yN) * (normAct φ x)⁻¹ ∈ inner (antiSp K) := by
    have hxyx : ((x * yN * x⁻¹ : normalizer (L : Set G)) : G) = ((⟨y, hyL⟩ : L) : G) := by
      change v * y * v⁻¹ = y
      rw [hyv, mul_inv_cancel_right]
    rw [← map_inv, ← map_mul, normAct_of_eq φ hxyx]
    exact ⟨_, rfl⟩
  obtain ⟨cX, hcX⟩ := hconj (normAct φ (x * yN)) hθk hθk'
  set l : G := ((φ.symm cX : L) : G)
  have hlL : l ∈ L := (φ.symm cX).2
  set lN : normalizer (L : Set G) := ⟨l, le_normalizer hlL⟩
  have hρl : normAct φ lN = MulAut.conj cX := by
    rw [normAct_of_eq φ (l := φ.symm cX) rfl, MulEquiv.apply_symm_apply]
  have hone : normAct φ ((lN * x * lN⁻¹)⁻¹ * (x * yN)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hρl, hcX]
    group
  have h0 := (normAct_eq_one_iff φ _).mp hone
  have hmemL : (((lN * x * lN⁻¹)⁻¹ * (x * yN) : normalizer (L : Set G)) : G) ∈ L := by
    change (l * v * l⁻¹)⁻¹ * (v * y) ∈ L
    have hu' : v⁻¹ * l⁻¹ * v ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hv) l⁻¹).mp (inv_mem hlL)
      simpa using this
    have e : (l * v * l⁻¹)⁻¹ * (v * y) = l * (v⁻¹ * l⁻¹ * v) * y := by group
    rw [e]
    exact mul_mem (mul_mem hlL hu') hyL
  have h1 := eq_one_of_mem_centralizer φ hmemL h0
  refine ⟨l, hlL, ?_⟩
  change (l * v * l⁻¹)⁻¹ * (v * y) = 1 at h1
  calc v * y = (l * v * l⁻¹) * ((l * v * l⁻¹)⁻¹ * (v * y)) := by group
    _ = l * v * l⁻¹ := by rw [h1, mul_one]

section Setup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {φ : L ≃* antiSp K}
  {TG : Subgroup G} {t : G}

theorem reequiv (hS : Setup L K n φ TG t) (φ' : L ≃* antiSp K) : Setup L K n φ' TG t :=
  ⟨hS.two_le, hS.card_K, hS.T_le, hS.t_mem, hS.order_t, hS.T_cyclic, hS.T_two, hS.cent_inf,
    hS.L_le, hS.cent_le⟩

theorem mul_self_mem_L [Finite G] (hS : Setup L K n φ TG t) (hT : TG = zpowers t) {y : G}
    (hy : y ∈ L ⊔ TG) : y * y ∈ L := by
  obtain ⟨l, hl, c, hc, rfl⟩ := (mem_sup_of_commute fun a ha b hb => hS.comm_L_T ha hb).mp hy
  have hlc : l * c = c * l := hS.comm_L_T hl hc
  have hcc : c * c = 1 := by
    rw [hT] at hc
    obtain ⟨j, rfl⟩ := hc
    rw [← zpow_add, ← two_mul, zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two, hS.t_mul_t],
      one_zpow]
  have e : l * c * (l * c) = l * l := by
    calc l * c * (l * c) = l * (c * l) * c := by group
      _ = l * (l * c) * c := by rw [hlc]
      _ = l * l * (c * c) := by group
      _ = l * l := by rw [hcc, mul_one]
  rw [e]
  exact mul_mem hl hl

theorem exists_of_inner [Finite G] (hS : Setup L K n φ TG t) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G))
    (hinn : normAct φ ⟨x, hS.cent_le hxC⟩ ∈ inner (antiSp K)) :
    ∃ l ∈ L, (∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) ∧ ∃ c ∈ TG, x = l * c := by
  obtain ⟨a, ha⟩ := hinn
  have ha' : normAct φ ⟨x, hS.cent_le hxC⟩ = MulAut.conj (φ (φ.symm a)) := by
    rw [MulEquiv.apply_symm_apply]
    exact ha.symm
  set l : G := ((φ.symm a : L) : G)
  have hlL : l ∈ L := (φ.symm a).2
  have h0 : l⁻¹ * x ∈ centralizer (L : Set G) := inv_mul_mem_centralizer φ _ _ ha'
  have hcT : l⁻¹ * x ∈ TG := hS.mem_T h0 (mul_mem (inv_mem (hS.L_le hlL)) hxC)
  refine ⟨l, hlL, fun y hy => ?_, l⁻¹ * x, hcT, by group⟩
  have hc := mem_centralizer_iff.mp h0 y hy
  calc x * y * x⁻¹ = l * ((l⁻¹ * x) * y) * x⁻¹ := by group
    _ = l * (y * (l⁻¹ * x)) * x⁻¹ := by rw [hc]
    _ = l * y * l⁻¹ := by group

theorem eq_mul_t_of_inner [Finite G] [CharP K 2] (hS : Setup L K n φ TG t) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxx : x * x = 1)
    (hinn : normAct φ ⟨x, hS.cent_le hxC⟩ ∈ inner (antiSp K)) (hxL : x ∉ L) :
    ∃ l ∈ L, l * l = 1 ∧ x = l * t := by
  obtain ⟨l, hlL, -, c, hcT, hxlc⟩ := exists_of_inner hS hxC hinn
  have hlc : l * c = c * l := hS.comm_L_T hlL hcT
  have hsq : l * l * (c * c) = 1 := by
    rw [← hxx, hxlc]
    calc l * l * (c * c) = l * (l * c) * c := by group
      _ = l * (c * l) * c := by rw [hlc]
      _ = l * c * (l * c) := by group
  have hll : l * l = 1 := by
    have hmem : l * l ∈ L ⊓ TG := ⟨mul_mem hlL hlL, by
      rw [eq_inv_of_mul_eq_one_left hsq]; exact TG.inv_mem (TG.mul_mem hcT hcT)⟩
    rw [hS.L_inf_T, mem_bot] at hmem
    exact hmem
  have hcc : c * c = 1 := by rw [hll, one_mul] at hsq; exact hsq
  have hc1 : c ≠ 1 := fun h => hxL (by rw [hxlc, h, mul_one]; exact hlL)
  have hct : c = t := hS.eq_t_of_mem_T hcT (orderOf_eq_prime (by rw [sq]; exact hcc) hc1)
  exact ⟨l, hlL, hll, by rw [hxlc, hct]⟩

theorem not_conj_of_not_axis [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t)
    (hax : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisOne K), x = t * u} ∨
      {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisTwo K), x = t * u})
    {z : G} (hz : z ∈ pull φ (antiUnipotentCenter K)) (h1 : z ∉ pull φ (axisOne K))
    (h2 : z ∉ pull φ (axisTwo K)) (h : G) : t * z ≠ h⁻¹ * t * h := by
  intro hconj
  have hZ : h⁻¹ * t * h ∈ (center ↥(pull φ (antiUnipotent K) ⊔ TG)).map
      (pull φ (antiUnipotent K) ⊔ TG).subtype := by
    have := hS.mul_mem_ZQ hz hS.t_mem
    rwa [hS.comm_L_T (pull_le φ _ hz) hS.t_mem, hconj] at this
  obtain ⟨m, hm, hhm⟩ := hS.mem_conj_normalizer hZ
  have hmem : t * z ∈ {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG :
      Subgroup G) : Set G), x = m⁻¹ * t * m} := ⟨m, hm, hconj.trans hhm⟩
  rcases hax with hax | hax <;> rw [hax] at hmem <;> obtain ⟨u, hu, hzu⟩ := hmem
  · exact h1 (by rwa [mul_left_cancel hzu])
  · exact h2 (by rwa [mul_left_cancel hzu])

theorem not_conj_sq [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t)
    (hax : {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisOne K), x = t * u} ∨
      {x : G | ∃ m ∈ normalizer ((pull φ (antiUnipotent K) ⊔ TG : Subgroup G) : Set G),
        x = m⁻¹ * t * m} = {x | ∃ u ∈ pull φ (axisTwo K), x = t * u})
    {w : G} (hwL : w ∈ L) (hw4 : w ^ 4 = 1) (hw2 : w ^ 2 ≠ 1) (h : G) :
    t * w ^ 2 ≠ h⁻¹ * t * h := by
  intro hconj
  set x : antiSp K := φ ⟨w, hwL⟩ with hx
  have hx4 : x ^ 2 ^ 2 = 1 := by
    rw [hx, ← map_pow, φ.map_eq_one_iff]
    exact Subtype.ext (by simpa using hw4)
  obtain ⟨m, -, hm⟩ := CFSG.QuasithinUnique.BenderStart.exists_mem_conj_mem_of_isSylowTwoOf
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2 le_top le_top
    (CFSG.QuasithinUnique.BenderStart.isPGroup_zpowers_of_pow_eq_one hx4)
  have hv := hm x (mem_zpowers x)
  have hvZ := sq_mem_antiUnipotentCenter hv
  have hvv : m⁻¹ * x * m * (m⁻¹ * x * m) = m⁻¹ * (x * x) * m := by group
  have hv1 : m⁻¹ * x * m * (m⁻¹ * x * m) ≠ 1 := by
    rw [hvv]
    intro h0
    apply hw2
    have hxx : x * x = 1 := by
      calc x * x = m * (m⁻¹ * (x * x) * m) * m⁻¹ := by group
        _ = 1 := by rw [h0]; group
    rw [hx, ← map_mul, φ.map_eq_one_iff] at hxx
    rw [sq]
    simpa using congrArg Subtype.val hxx
  have hnax : ¬ (m⁻¹ * x * m * (m⁻¹ * x * m) ∈ axisOne K ∨
      m⁻¹ * x * m * (m⁻¹ * x * m) ∈ axisTwo K) := by
    rw [mem_axis_iff hvZ]
    push Not
    exact ⟨hv1, _, hv, rfl⟩
  set l : G := ((φ.symm m : L) : G) with hl
  have hlL : l ∈ L := (φ.symm m).2
  have hz : ((φ.symm (m⁻¹ * x * m * (m⁻¹ * x * m)) : L) : G) = l⁻¹ * w ^ 2 * l := by
    rw [hvv, sq]
    simp [hl, hx, map_mul, map_inv]
  have hzZ : l⁻¹ * w ^ 2 * l ∈ pull φ (antiUnipotentCenter K) := hz ▸ symm_mem_pull.mpr hvZ
  refine not_conj_of_not_axis hS hax hzZ (fun h1 => hnax (Or.inl ?_))
    (fun h2 => hnax (Or.inr ?_)) (h * l) ?_
  · rw [← hz] at h1
    exact symm_mem_pull.mp h1
  · rw [← hz] at h2
    exact symm_mem_pull.mp h2
  · have hlt : l * t = t * l := hS.comm_L_T hlL hS.t_mem
    calc t * (l⁻¹ * w ^ 2 * l) = l⁻¹ * (l * t) * l⁻¹ * w ^ 2 * l := by group
      _ = l⁻¹ * (t * w ^ 2) * l := by rw [hlt]; group
      _ = (h * l)⁻¹ * t * (h * l) := by rw [hconj]; group

theorem act_inner [Finite G] [Finite K] [CharP K 2]
    (hS : Setup L K n φ TG t) (hO : CFSG.oddCore G = ⊥) (hLn : ¬ L.Normal)
    (hax : ∀ w ∈ L, w ^ 4 = 1 → w ^ 2 ≠ 1 → ∀ h : G, t * w ^ 2 ≠ h⁻¹ * t * h)
    {g : G} (hgC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) :
    normAct φ ⟨g⁻¹ * t * g, hS.cent_le hgC⟩ ∈ inner (antiSp K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hout
  set C := centralizer ({t} : Set G) with hC
  have hT := hS.T_eq_zpowers hO hLn
  have huu : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hS.t_mul_t]; group
  set θ := normAct φ ⟨g⁻¹ * t * g, hS.cent_le hgC⟩ with hθ
  have hθθ : θ * θ = 1 := by
    rw [hθ, ← map_mul, show (⟨g⁻¹ * t * g, hS.cent_le hgC⟩ : normalizer (L : Set G)) *
      ⟨g⁻¹ * t * g, hS.cent_le hgC⟩ = 1 from Subtype.ext huu, map_one]
  obtain ⟨-, -, -, w, -, -, hword, -, hres, hw1, -⟩ :=
    even_symplectic_four_outer_involution_fixed_central_square hS.two_le hS.card_K θ hθθ hout
  set wL : G := ((φ.symm w : L) : G) with hwL
  have hwLL : wL ∈ L := (φ.symm w).2
  have hw4 : wL ^ 4 = 1 := by
    rw [hwL, ← coe_symm_pow, coe_symm_eq_one_iff]
    have h := pow_orderOf_eq_one w
    rwa [hword] at h
  have hw2 : wL ^ 2 ≠ 1 := by
    rw [hwL, ← coe_symm_pow, Ne, coe_symm_eq_one_iff]
    exact hw1
  have hfixc : ∀ y : antiSp K, θ y = y →
      g⁻¹ * t * g * ((φ.symm y : L) : G) * (g⁻¹ * t * g)⁻¹ = ((φ.symm y : L) : G) := by
    intro y hy
    have h := normAct_symm_apply φ ⟨g⁻¹ * t * g, hS.cent_le hgC⟩ y
    rw [← hθ, hy] at h
    exact h.symm
  have hψmem : ∀ y : fixedSubgroup θ,
      ((MulAut.conj g).toMonoidHom.comp (L.subtype.comp
        (φ.symm.toMonoidHom.comp (fixedSubgroup θ).subtype))) y ∈ C := by
    intro y
    have h1 := hfixc y y.2
    change g * ((φ.symm y : L) : G) * g⁻¹ ∈ C
    rw [hC, mem_centralizer_singleton_iff]
    calc g * ((φ.symm y : L) : G) * g⁻¹ * t
        = g * (g⁻¹ * t * g * ((φ.symm y : L) : G) * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) * g⁻¹ := by
          rw [h1]; group
      _ = t * (g * ((φ.symm y : L) : G) * g⁻¹) := by group
  set ψ := ((MulAut.conj g).toMonoidHom.comp (L.subtype.comp
    (φ.symm.toMonoidHom.comp (fixedSubgroup θ).subtype))).codRestrict C hψmem
  obtain ⟨y₀, hy₀, hy₀w⟩ := hres
  have hψy : ψ y₀ ∈ derivedSeries C 2 :=
    map_derivedSeries_le_derivedSeries ψ 2 ⟨y₀, (mem_iInf.mp hy₀) 2, rfl⟩
  have hgz : g * wL ^ 2 * g⁻¹ ∈ L := by
    have h := hS.derivedSeries_two_le hψy
    change g * ((φ.symm (y₀ : antiSp K) : L) : G) * g⁻¹ ∈ L at h
    have hy : (y₀ : antiSp K) = w ^ 2 := hy₀w
    rwa [hy, coe_symm_pow] at h
  have hB := hax wL hwLL hw4 hw2
  have ht'C : g * t * g⁻¹ ∈ C := by
    have h := mem_centralizer_singleton_iff.mp hgC
    rw [hC, mem_centralizer_singleton_iff]
    calc g * t * g⁻¹ * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g * t) * g⁻¹ := by rw [h]
      _ = t * (g * t * g⁻¹) := by group
  have ht't' : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hS.t_mul_t]; group
  have hw2t : wL ^ 2 * t = t * wL ^ 2 := hS.comm_L_T (pow_mem hwLL 2) hS.t_mem
  have hww : wL ^ 2 * wL ^ 2 = 1 := by rw [← pow_add, hw4]
  have hinn' : normAct φ ⟨g * t * g⁻¹, hS.cent_le ht'C⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
    by_contra hout'
    obtain ⟨l, hlL, hl⟩ := exists_conj_of_outer hS.two_le hS.card_K φ (hS.cent_le ht'C) ht't'
      hout' hgz (by
        calc g * t * g⁻¹ * (g * wL ^ 2 * g⁻¹) = g * (t * wL ^ 2) * g⁻¹ := by group
          _ = g * (wL ^ 2 * t) * g⁻¹ := by rw [hw2t]
          _ = g * wL ^ 2 * g⁻¹ * (g * t * g⁻¹) := by group) (by
        calc g * wL ^ 2 * g⁻¹ * (g * wL ^ 2 * g⁻¹) = g * (wL ^ 2 * wL ^ 2) * g⁻¹ := by group
          _ = 1 := by rw [hww]; group)
    apply hB (g⁻¹ * l⁻¹ * g)
    calc t * wL ^ 2 = g⁻¹ * (g * t * g⁻¹ * (g * wL ^ 2 * g⁻¹)) * g := by group
      _ = g⁻¹ * (l * (g * t * g⁻¹) * l⁻¹) * g := by rw [hl]
      _ = (g⁻¹ * l⁻¹ * g)⁻¹ * t * (g⁻¹ * l⁻¹ * g) := by group
  have ht'L : g * t * g⁻¹ ∉ L := by
    have := hS.conj_not_mem_L hO hLn g⁻¹
    rwa [inv_inv] at this
  obtain ⟨ℓ, hℓL, hℓℓ, ht'ℓ⟩ := eq_mul_t_of_inner hS ht'C ht't' hinn' ht'L
  have hφℓ : φ ⟨ℓ, hℓL⟩ * φ ⟨ℓ, hℓL⟩ = 1 := by
    rw [← map_mul, φ.map_eq_one_iff]
    exact Subtype.ext hℓℓ
  obtain ⟨h₁, hh₁⟩ := SymplecticFourFusion.exists_conj_mem_center hφℓ
  set φ₁ : L ≃* antiSp K := φ.trans (MulAut.conj h₁)
  have hS₁ := reequiv hS φ₁
  have hℓZ : ℓ ∈ pull φ₁ (antiUnipotentCenter K) := mem_pull.mpr ⟨hℓL, hh₁⟩
  have ht'Z := hS₁.mul_mem_ZQ hℓZ hS.t_mem
  rw [← ht'ℓ] at ht'Z
  set Q₁ := pull φ₁ (antiUnipotent K) ⊔ TG
  set X₁ := Q₁.map (MulAut.conj g⁻¹).toMonoidHom
  have hX₁C : X₁ ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    have hqt := (mem_center_map_iff.mp ht'Z).2 q hq
    rw [hC, mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * q * g * t = g⁻¹ * (q * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * q) * g := by rw [hqt]
      _ = t * (g⁻¹ * q * g) := by group
  have hX₁2 : IsPGroup 2 X₁ := hS₁.Q_two.map _
  obtain ⟨R, hXR⟩ := (hX₁2.of_equiv (subgroupOfEquivOfLe hX₁C).symm).exists_le_sylow
  set RG := (R : Subgroup C).map C.subtype
  have hRGC : RG ≤ C := map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map _
  have hX₁R : X₁ ≤ RG := fun x hx => ⟨⟨x, hX₁C hx⟩, hXR (mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨Pt, hPt⟩ := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
    (p := 2) (P := RG) ⟨R, rfl⟩ hS.L_le hS.cent_le
  obtain ⟨φ₂, hφ₂⟩ := exists_equiv_pull_eq φ Pt
  have hS₂ := reequiv hS φ₂
  have htR : t ∈ RG := hX₁R ⟨g * t * g⁻¹, (mem_center_map_iff.mp ht'Z).1, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩
  have hQtR : pull φ₂ (antiUnipotent K) ⊔ TG ≤ RG := by
    refine sup_le ?_ (by rw [hT]; exact zpowers_le.mpr htR)
    rw [← hφ₂, hPt]
    exact inf_le_left
  have key : ∀ A : Subgroup (antiSp K), A ≤ antiUnipotent K →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) → Nat.card A = 2 ^ (3 * n) →
      pull φ₁ A ≤ (L ⊔ TG).comap (MulAut.conj g⁻¹).toMonoidHom := by
    intro A hAU hAc hA2 hAcard
    obtain ⟨hBc, hBQ, hBr⟩ := hS₁.rank_radical_mul hAU hAc hA2 hAcard
    set B := pull φ₁ A ⊔ TG
    set B' := B.map (MulAut.conj g⁻¹).toMonoidHom
    have hB'R : B' ≤ RG := (map_mono hBQ).trans hX₁R
    have : IsMulCommutative B' := isMulCommutative_iff_of_setLike.mpr fun x hx y hy => by
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      rw [← map_mul, ← map_mul, setLike_mul_comm ha hb]
    have hB'r : Group.rank B' = 3 * n + 1 := by
      rw [← hBr]
      exact (Group.rank_congr (B.equivMapOfInjective _ (MulAut.conj g⁻¹).injective)).symm
    have h1 := (hS₂.rank_bound hRGC hRG2 hQtR hB'R).2 hB'r
    intro p hp
    exact sup_le_sup_right (pull_le φ₂ _) TG (h1 ⟨p, mem_sup_left hp, rfl⟩)
  obtain ⟨-, ⟨-, -, hA1card⟩, ⟨-, -, hA2card⟩, -⟩ :=
    even_symplectic_four_Sylow_involution_radicals hS.card_K
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hS.card_K, ← pow_mul, mul_comm]
  have hU : pull φ₁ (antiUnipotent K) ≤ (L ⊔ TG).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [antiUnipotent_eq_radA1_sup_radA2, pull_sup]
    exact sup_le
      (key _ radA1_le_antiUnipotent (fun x hx y hy => radA1_comm hx hy)
        (fun x hx => mul_self_of_mem_radA1 hx) (hA1card.trans hq3))
      (key _ radA2_le_antiUnipotent (fun x hx y hy => radA2_comm hx hy)
        (fun x hx => mul_self_of_mem_radA2 hx) (hA2card.trans hq3))
  set w₁ : G := ((φ₁.symm (uElt 1 1 1 1) : L) : G) with hw₁
  have hw₁L : w₁ ∈ L := (φ₁.symm _).2
  have hw₁U : w₁ ∈ pull φ₁ (antiUnipotent K) := symm_mem_pull.mpr ⟨1, 1, 1, 1, rfl⟩
  have hsq1 : (uElt (1 : K) 1 1 1) ^ 2 = uElt 0 1 1 0 := SymplecticFourOuterSquare.w_sq
  have hw₁2 : w₁ ^ 2 ≠ 1 := by
    rw [hw₁, ← coe_symm_pow, Ne, coe_symm_eq_one_iff, hsq1, ← uElt_zero_eq_one]
    intro h
    exact one_ne_zero (uElt_inj h).2.1
  have hw₁4 : w₁ ^ 4 = 1 := by
    rw [hw₁, ← coe_symm_pow, coe_symm_eq_one_iff,
      show uElt (1 : K) 1 1 1 ^ 4 = (uElt 1 1 1 1 ^ 2) ^ 2 by rw [← pow_mul], hsq1, sq]
    exact mul_self_of_mem_radA1 ⟨1, 1, 0, rfl⟩
  have hgw : g⁻¹ * w₁ * g ∈ L ⊔ TG := by simpa using hU hw₁U
  have hk : g⁻¹ * w₁ ^ 2 * g ∈ L := by
    have h := mul_self_mem_L hS hT hgw
    rwa [show g⁻¹ * w₁ * g * (g⁻¹ * w₁ * g) = g⁻¹ * w₁ ^ 2 * g by rw [sq]; group] at h
  have hw₁t : w₁ ^ 2 * t = t * w₁ ^ 2 := hS.comm_L_T (pow_mem hw₁L 2) hS.t_mem
  have hw₁w₁ : w₁ ^ 2 * w₁ ^ 2 = 1 := by rw [← pow_add, hw₁4]
  obtain ⟨l, hlL, hl⟩ := exists_conj_of_outer hS.two_le hS.card_K φ (hS.cent_le hgC) huu hout hk
    (by
      calc g⁻¹ * t * g * (g⁻¹ * w₁ ^ 2 * g) = g⁻¹ * (t * w₁ ^ 2) * g := by group
        _ = g⁻¹ * (w₁ ^ 2 * t) * g := by rw [hw₁t]
        _ = g⁻¹ * w₁ ^ 2 * g * (g⁻¹ * t * g) := by group) (by
      calc g⁻¹ * w₁ ^ 2 * g * (g⁻¹ * w₁ ^ 2 * g) = g⁻¹ * (w₁ ^ 2 * w₁ ^ 2) * g := by group
        _ = 1 := by rw [hw₁w₁]; group)
  apply hax w₁ hw₁L hw₁4 hw₁2 (g * l⁻¹ * g⁻¹)
  calc t * w₁ ^ 2 = g * (g⁻¹ * t * g * (g⁻¹ * w₁ ^ 2 * g)) * g⁻¹ := by group
    _ = g * (l * (g⁻¹ * t * g) * l⁻¹) * g⁻¹ := by rw [hl]
    _ = (g * l⁻¹ * g⁻¹)⁻¹ * t * (g * l⁻¹ * g⁻¹) := by group

end Setup

end OneAxisFusion

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open scoped Pointwise

end CFSG.LocalAnalysis.SymplecticFourStandard
