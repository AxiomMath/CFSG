module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.JInK
public import CFSG.Mathlib.GroupTheory.InvolutionInvertingSylowThree
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Conj

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

private theorem eq_one_of_sq_eq_one_of_cube_eq_one {G : Type*} [Group G] {x : G}
    (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h : x ^ 3 = x := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul]
  rw [h] at h3
  exact h3

private theorem comm_eq_one_iff {G : Type} [Group G] {b x : G} :
    b * x * b⁻¹ * x⁻¹ = 1 ↔ x * b = b * x := by
  constructor
  · intro h
    have h2 : b * x * b⁻¹ = x := by rwa [mul_inv_eq_one] at h
    have h3 : b * x = x * b := by
      calc b * x = (b * x * b⁻¹) * b := by group
        _ = x * b := by rw [h2]
    exact h3.symm
  · intro h
    rw [← h]
    group

private theorem comm_mul {G : Type} [Group G] {B : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {b : G} (hbB : ∀ x ∈ B, b * x * b⁻¹ ∈ B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) :
    b * (x * y) * b⁻¹ * (x * y)⁻¹ =
      (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by
  have hφy : b * y * b⁻¹ * y⁻¹ ∈ B := B.mul_mem (hbB y hy) (B.inv_mem hy)
  have hcxφy : Commute x (b * y * b⁻¹ * y⁻¹) := hB x hx (b * y * b⁻¹ * y⁻¹) hφy
  calc b * (x * y) * b⁻¹ * (x * y)⁻¹
      = b * x * (y * b⁻¹ * y⁻¹) * x⁻¹ := by group
    _ = b * x * (b⁻¹ * (b * y * b⁻¹ * y⁻¹)) * x⁻¹ := by
          rw [show y * b⁻¹ * y⁻¹ = b⁻¹ * (b * y * b⁻¹ * y⁻¹) by group]
    _ = b * x * b⁻¹ * (b * y * b⁻¹ * y⁻¹) * x⁻¹ := by group
    _ = b * x * b⁻¹ * ((b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = b * x * b⁻¹ * (x⁻¹ * (b * y * b⁻¹ * y⁻¹)) := by
          rw [hcxφy.inv_left.eq.symm]
    _ = (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by group

theorem exists_rank_four {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    ∃ E : Subgroup G, E ≤ ktil R ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  classical
  have hS : GGFF.SettingCore b L z := h.settingCore
  obtain ⟨hYpg, hYcard, hYmax⟩ := sylow_B₁_inf_J h hJ
  have hm : n - 1 = 4 ∨ n - 1 = 5 := by
    rcases h.hypA.n_cases with rfl | rfl <;> norm_num
  obtain ⟨t, htJ, ht2, htinv⟩ :=
    CFSG.InvolutionInvertingSylowThree.exists_inverting_involution (Y := bOne z ⊓ J)
      hm hJ.model inf_le_right hYpg hYmax
  have htL : t ∈ L := hJ.le htJ
  have htb : t * b = b * t :=
    (Subgroup.mem_centralizer_iff.mp (h.hypA.le htL) b (by simp)).symm
  have htb₁ : t * GGFF.zs z 0 = GGFF.zs z 0 * t := hJ.comm t htJ
  have htK : t ∈ ktil R := le_oppE h hJ hR htJ
  have hB₂comm : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp hR.b2.abel.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hB₁abel : CFSG.Open.IsElemAbelian 3 (bOne z) :=
    GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm
  have hZle : Subgroup.zpowers (GGFF.zs z 0) ≤ bOne z := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  have hYle : bOne z ⊓ J ≤ bOne z := inf_le_left
  have hZmap : (Subgroup.zpowers (GGFF.zs z 0)).map (MulAut.conj t) =
      Subgroup.zpowers (GGFF.zs z 0) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change t * GGFF.zs z 0 * t⁻¹ = GGFF.zs z 0
    rw [htb₁]
    group
  have hYmap : (bOne z ⊓ J).map (MulAut.conj t) = bOne z ⊓ J := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · change t * y * t⁻¹ ∈ bOne z
        rw [htinv y hy]
        exact (bOne z).inv_mem (Subgroup.mem_inf.mp hy).1
      · change t * y * t⁻¹ ∈ J
        rw [htinv y hy]
        exact J.inv_mem (Subgroup.mem_inf.mp hy).2
    · intro x hx
      have hx' : x⁻¹ ∈ bOne z ⊓ J :=
        ⟨(bOne z).inv_mem (Subgroup.mem_inf.mp hx).1, J.inv_mem (Subgroup.mem_inf.mp hx).2⟩
      refine Subgroup.mem_map.mpr ⟨x⁻¹, hx', ?_⟩
      simpa using htinv x⁻¹ hx'
  have hB₁eq : bOne z = Subgroup.zpowers (GGFF.zs z 0) ⊔ (bOne z ⊓ J) := by
    apply le_antisymm
    · rw [show bOne z = Subgroup.closure {GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} from
        GGFF.SettingCore.tor_eq_closure z]
      apply (Subgroup.closure_le _).mpr
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right
          (And.intro (Subgroup.subset_closure (by simp)) hJ.z₁)
      · exact Subgroup.mem_sup_right
          (And.intro (Subgroup.subset_closure (by simp)) hJ.z₂)
    · exact sup_le hZle hYle
  have htNorB₁ : t ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hB₁eq, Subgroup.map_sup, hZmap, hYmap]
  have htB₂ : ∀ x ∈ B₂, t * x * t⁻¹ ∈ B₂ := hR.b2.D_nor t ⟨htL, htNorB₁⟩
  let CG : Subgroup G :=
    { carrier := {x | x ∈ B₂ ∧ t * x * t⁻¹ = x}
      one_mem' := ⟨B₂.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨B₂.mul_mem hx.1 hy.1, by
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x * y := by rw [hx.2, hy.2]⟩
      inv_mem' := fun {x} hx => ⟨B₂.inv_mem hx.1, by
        have h : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
        rw [h, hx.2]⟩ }
  let EG : Subgroup G :=
    { carrier := {x | x ∈ B₂ ∧ t * x * t⁻¹ = x⁻¹}
      one_mem' := ⟨B₂.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨B₂.mul_mem hx.1 hy.1, by
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx.2, hy.2]
          _ = (x * y)⁻¹ := by
              rw [mul_inv_rev]
              exact (hB₂comm y⁻¹ (B₂.inv_mem hy.1) x⁻¹ (B₂.inv_mem hx.1)).symm⟩
      inv_mem' := fun {x} hx => ⟨B₂.inv_mem hx.1, by
        have h : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
        rw [h, hx.2]⟩ }
  have hCG_le_B₂ : CG ≤ B₂ := fun x hx => hx.1
  have hEG_le_B₂ : EG ≤ B₂ := fun x hx => hx.1
  have hCGEG : CG ⊓ EG = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxCG, hxEG⟩ := Subgroup.mem_inf.mp hx
    have hx1 : x = x⁻¹ := hxCG.2.symm.trans hxEG.2
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [hx1]; exact inv_mul_cancel x
    exact eq_one_of_sq_eq_one_of_cube_eq_one hx2 (hR.b2.abel.2 x hxCG.1)
  let f : ↥CG × ↥EG → ↥B₂ := fun p => ⟨(p.1 : G) * (p.2 : G), B₂.mul_mem p.1.2.1 p.2.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨c1, e1⟩ ⟨c2, e2⟩ heq
      have h : (c1 : G) * (e1 : G) = (c2 : G) * (e2 : G) := congrArg Subtype.val heq
      have h2 : (c2 : G)⁻¹ * (c1 : G) = (e2 : G) * (e1 : G)⁻¹ := by
        calc (c2 : G)⁻¹ * (c1 : G)
            = (c2 : G)⁻¹ * ((c1 : G) * (e1 : G)) * (e1 : G)⁻¹ := by group
          _ = (c2 : G)⁻¹ * ((c2 : G) * (e2 : G)) * (e1 : G)⁻¹ := by rw [h]
          _ = (e2 : G) * (e1 : G)⁻¹ := by group
      have hmemCG : (c2 : G)⁻¹ * (c1 : G) ∈ CG := CG.mul_mem (CG.inv_mem c2.2) c1.2
      have hmemEG : (e2 : G) * (e1 : G)⁻¹ ∈ EG := EG.mul_mem e2.2 (EG.inv_mem e1.2)
      have hmem : (c2 : G)⁻¹ * (c1 : G) ∈ CG ⊓ EG :=
        Subgroup.mem_inf.mpr ⟨hmemCG, h2 ▸ hmemEG⟩
      rw [hCGEG] at hmem
      have hc : (c2 : G)⁻¹ * (c1 : G) = 1 := Subgroup.mem_bot.mp hmem
      have hc_eq : (c1 : G) = (c2 : G) := by
        calc (c1 : G) = (c2 : G) * ((c2 : G)⁻¹ * (c1 : G)) := by group
          _ = (c2 : G) * 1 := by rw [hc]
          _ = (c2 : G) := by rw [mul_one]
      have he_eq : (e1 : G) = (e2 : G) := by
        rw [hc_eq] at h
        exact mul_left_cancel h
      exact Prod.ext (Subtype.ext hc_eq) (Subtype.ext he_eq)
    · intro x
      let a : G := (x : G) * (t * (x : G) * t⁻¹)
      let c0 : G := (x : G) * (t * (x : G) * t⁻¹)⁻¹
      have haB₂ : a ∈ B₂ := B₂.mul_mem x.2 (htB₂ (x : G) x.2)
      have hcB₂ : c0 ∈ B₂ := B₂.mul_mem x.2 (B₂.inv_mem (htB₂ (x : G) x.2))
      have htx : t * (x : G) * t⁻¹ ∈ B₂ := htB₂ (x : G) x.2
      have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
      have hcancel : t * (t * (x : G) * t⁻¹) * t⁻¹ = (x : G) := by
        calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * (x : G) * (t * t)⁻¹ := by group
          _ = (x : G) := by rw [ht2', inv_one, one_mul, mul_one]
      have hcancel2 : t * (t * (x : G) * t⁻¹)⁻¹ * t⁻¹ = (x : G)⁻¹ := by
        set A : G := t * (x : G) * t⁻¹ with hA
        have h1 : t * A⁻¹ * t⁻¹ = (t * A * t⁻¹)⁻¹ := by group
        have h : t * (t * (x : G) * t⁻¹)⁻¹ * t⁻¹ =
            (t * (t * (x : G) * t⁻¹) * t⁻¹)⁻¹ := by
          rw [← hA]; exact h1
        rw [h, hcancel]
      have haCG : a ∈ CG := by
        refine ⟨haB₂, ?_⟩
        have hcomm := hB₂comm (x : G) x.2 (t * (x : G) * t⁻¹) htx
        show t * a * t⁻¹ = a
        simp only [a]
        calc t * ((x : G) * (t * (x : G) * t⁻¹)) * t⁻¹
            = (t * (x : G) * t⁻¹) * (t * (t * (x : G) * t⁻¹) * t⁻¹) := by group
          _ = (t * (x : G) * t⁻¹) * (x : G) := by rw [hcancel]
          _ = (x : G) * (t * (x : G) * t⁻¹) := hcomm.symm
      have hcEG : c0 ∈ EG := by
        refine ⟨hcB₂, ?_⟩
        show t * c0 * t⁻¹ = c0⁻¹
        simp only [c0]
        calc t * ((x : G) * (t * (x : G) * t⁻¹)⁻¹) * t⁻¹
            = (t * (x : G) * t⁻¹) * (t * (t * (x : G) * t⁻¹)⁻¹ * t⁻¹) := by group
          _ = (t * (x : G) * t⁻¹) * (x : G)⁻¹ := by rw [hcancel2]
          _ = ((x : G) * (t * (x : G) * t⁻¹)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      have hac : a * c0 = (x : G) ^ 2 := by
        have hcommx := hB₂comm (x : G) x.2 (t * (x : G) * t⁻¹) htx
        simp only [a, c0]
        rw [pow_two]
        calc (x : G) * (t * (x : G) * t⁻¹) * ((x : G) * (t * (x : G) * t⁻¹)⁻¹)
            = (x : G) * ((t * (x : G) * t⁻¹) * (x : G)) * (t * (x : G) * t⁻¹)⁻¹ := by group
          _ = (x : G) * ((x : G) * (t * (x : G) * t⁻¹)) * (t * (x : G) * t⁻¹)⁻¹ := by
              rw [hcommx]
          _ = (x : G) * (x : G) := by group
      have hx4 : (x : G) ^ 4 = (x : G) := by
        have hx3 : (x : G) ^ 3 = 1 := hR.b2.abel.2 (x : G) x.2
        calc (x : G) ^ 4 = (x : G) ^ 3 * (x : G) := by group
          _ = 1 * (x : G) := by rw [hx3]
          _ = (x : G) := by rw [one_mul]
      have hxa : (x : G) = a ^ 2 * c0 ^ 2 := by
        have hacomm : a * c0 = c0 * a := hB₂comm a haB₂ c0 hcB₂
        calc (x : G) = (x : G) ^ 4 := hx4.symm
          _ = (x : G) ^ 2 * (x : G) ^ 2 := by
              rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
          _ = (a * c0) * (a * c0) := by rw [← hac]
          _ = a ^ 2 * c0 ^ 2 := by
              rw [pow_two, pow_two]
              calc (a * c0) * (a * c0) = a * (c0 * a) * c0 := by group
                _ = a * (a * c0) * c0 := by rw [hacomm]
                _ = a * a * (c0 * c0) := by group
      refine ⟨(⟨a ^ 2, CG.pow_mem haCG 2⟩, ⟨c0 ^ 2, EG.pow_mem hcEG 2⟩), ?_⟩
      apply Subtype.ext
      show (a ^ 2 : G) * (c0 ^ 2 : G) = (x : G)
      exact hxa.symm
  have hcard_prod : Nat.card ↥B₂ = Nat.card ↥CG * Nat.card ↥EG := by
    calc Nat.card ↥B₂ = Nat.card (↥CG × ↥EG) := (Nat.card_congr (Equiv.ofBijective f hf)).symm
      _ = Nat.card ↥CG * Nat.card ↥EG := Nat.card_prod _ _
  have hsup : (Subgroup.zpowers (GGFF.zs z 0)).subgroupOf (bOne z) ⊔
      (bOne z ⊓ J).subgroupOf (bOne z) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hZle hYle, ← hB₁eq, Subgroup.subgroupOf_self]
  have decompB₁ : ∀ x ∈ bOne z,
      ∃ a ∈ Subgroup.zpowers (GGFF.zs z 0), ∃ b ∈ bOne z ⊓ J, x = a * b := by
    let : CommGroup ↥(bOne z) :=
      { (inferInstance : Group ↥(bOne z)) with
        mul_comm := fun a b => isMulCommutative_iff.mp hB₁abel.1 a b }
    intro x hx
    let x' : ↥(bOne z) := ⟨x, hx⟩
    have hx'sup : x' ∈ (Subgroup.zpowers (GGFF.zs z 0)).subgroupOf (bOne z) ⊔
        (bOne z ⊓ J).subgroupOf (bOne z) := hsup ▸ Subgroup.mem_top x'
    rw [Subgroup.mem_sup] at hx'sup
    obtain ⟨a, ha, b, hb, hab⟩ := hx'sup
    refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
    have h1 := congrArg (fun w : ↥(bOne z) => (w : G)) hab
    exact h1.symm
  have htZ : ∀ a ∈ Subgroup.zpowers (GGFF.zs z 0), t * a * t⁻¹ = a :=
    fun a ha => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← hk, ← conj_zpow]
      rw [show t * GGFF.zs z 0 * t⁻¹ = GGFF.zs z 0 by
        rw [htb₁]
        group]
  have htY : ∀ y ∈ bOne z ⊓ J, t * y * t⁻¹ = y⁻¹ := fun y hy => htinv y hy
  have hCGcapB₁ : CG ⊓ bOne z = Subgroup.zpowers (GGFF.zs z 0) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxCG, hxB₁⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, b, hb, hab⟩ := decompB₁ x hxB₁
      have hx' : x = a * b⁻¹ := by
        calc x = t * x * t⁻¹ := hxCG.2.symm
          _ = t * (a * b) * t⁻¹ := by rw [hab]
          _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a * b⁻¹ := by rw [htZ a ha, htY b hb]
      have hbb : b = b⁻¹ := mul_left_cancel (hab.symm.trans hx')
      have hb2 : b ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [hbb]; exact inv_mul_cancel b
      have hb1 : b = 1 :=
        eq_one_of_sq_eq_one_of_cube_eq_one hb2 (hB₁abel.2 b (hYle hb))
      rw [hab, hb1, mul_one]
      exact ha
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨⟨hR.b2.B₁_le (hZle hx), htZ x hx⟩, hZle hx⟩
  have hEGcapB₁ : EG ⊓ bOne z = bOne z ⊓ J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxEG, hxB₁⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, b, hb, hab⟩ := decompB₁ x hxB₁
      have hB₁comm : ∀ c ∈ bOne z, ∀ d ∈ bOne z, c * d = d * c := fun c hc d hd =>
        congrArg Subtype.val (isMulCommutative_iff.mp hB₁abel.1 ⟨c, hc⟩ ⟨d, hd⟩)
      have hx' : x⁻¹ = a * b⁻¹ := by
        calc x⁻¹ = t * x * t⁻¹ := hxEG.2.symm
          _ = t * (a * b) * t⁻¹ := by rw [hab]
          _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a * b⁻¹ := by rw [htZ a ha, htY b hb]
      have h1 : x⁻¹ = a⁻¹ * b⁻¹ := by
        rw [hab, mul_inv_rev,
          hB₁comm b⁻¹ (hYle (Subgroup.inv_mem _ hb)) a⁻¹ (hZle (Subgroup.inv_mem _ ha))]
      have haa : a = a⁻¹ :=
        mul_right_cancel (hx'.symm.trans h1)
      have ha2 : a ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [haa]; exact inv_mul_cancel a
      have ha1 : a = 1 :=
        eq_one_of_sq_eq_one_of_cube_eq_one ha2 (hB₁abel.2 a (hZle ha))
      rw [hab, ha1, one_mul]
      exact hb
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨⟨hR.b2.B₁_le (hYle hx), htY x hx⟩, hYle hx⟩
  have hZcard : Nat.card (Subgroup.zpowers (GGFF.zs z 0)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hS.zs_pow 0) (fun h1 =>
      h.model.z_ne_one 0 (Subtype.ext (by simpa [GGFF.zs] using h1)))
  have hCGcapCard : Nat.card ↥(CG ⊓ bOne z) = 3 := by rw [hCGcapB₁, hZcard]
  have hEGcapCard : Nat.card ↥(EG ⊓ bOne z) = 9 := by rw [hEGcapB₁, hYcard]
  have hB₁_le_cen : bOne z ≤ Subgroup.centralizer ({b} : Set G) :=
    (GGFF.SettingCore.tor_le z).trans h.hypA.le
  let ψ : ↥B₂ →* ↥(bOne z) :=
    MonoidHom.mk' (fun x => ⟨b * (x : G) * b⁻¹ * (x : G)⁻¹, hR.b2.comm x x.2⟩)
      (fun x y => Subtype.ext (comm_mul hB₂comm hR.b2.b_nor x.2 y.2))
  have hψ_ker : ψ.ker = (bOne z).subgroupOf B₂ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      apply hR.b2.fix x x.2
      have hx1 : b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1 := by
        have h' := congrArg (fun u : ↥(bOne z) => (u : G)) hx
        simpa [ψ] using h'
      exact comm_eq_one_iff.mp hx1
    · intro hx
      apply Subtype.ext
      change b * (x : G) * b⁻¹ * (x : G)⁻¹ = 1
      exact comm_eq_one_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp (hB₁_le_cen hx) b (by simp)).symm)
  have hψ_eq_one_iff : ∀ x : ↥B₂, ψ x = 1 ↔ (x : G) ∈ bOne z := by
    intro x
    rw [← MonoidHom.mem_ker, hψ_ker, Subgroup.mem_subgroupOf]
  have hψ_t : ∀ (x : G) (hx : x ∈ B₂),
      (ψ ⟨t * x * t⁻¹, htB₂ x hx⟩ : G) = t * (ψ ⟨x, hx⟩ : G) * t⁻¹ := by
    intro x hx
    show b * (t * x * t⁻¹) * b⁻¹ * (t * x * t⁻¹)⁻¹ =
      t * (b * x * b⁻¹ * x⁻¹) * t⁻¹
    rw [show t * (b * x * b⁻¹ * x⁻¹) * t⁻¹ =
      (t * b * t⁻¹) * (t * x * t⁻¹) * (t * b * t⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ by group]
    rw [show t * b * t⁻¹ = b by rw [htb]; group]
  let ψCG : ↥CG →* ↥(bOne z) :=
    MonoidHom.mk' (fun c => ψ ⟨(c : G), c.2.1⟩) (fun c d => Subtype.ext (by
      show (ψ (⟨(c : G), c.2.1⟩ * ⟨(d : G), d.2.1⟩) : G) =
        ((ψ ⟨(c : G), c.2.1⟩ : ↥(bOne z)) : G) * ((ψ ⟨(d : G), d.2.1⟩ : ↥(bOne z)) : G)
      rw [map_mul]; rfl))
  have hψCGker : (ψCG.ker).map CG.subtype = CG ⊓ bOne z := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨c.2, (hψ_eq_one_iff ⟨(c : G), c.2.1⟩).mp hc⟩
    · intro hx
      obtain ⟨hxCG, hxB₁⟩ := Subgroup.mem_inf.mp hx
      exact ⟨⟨x, hxCG⟩,
        (hψ_eq_one_iff ⟨x, hCG_le_B₂ hxCG⟩).mpr hxB₁, rfl⟩
  have hψCGrange_le : ψCG.range ≤ (CG ⊓ bOne z).subgroupOf (bOne z) := by
    rintro y ⟨c, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨⟨hR.b2.B₁_le (ψ ⟨(c : G), c.2.1⟩).2, ?_⟩, (ψ ⟨(c : G), c.2.1⟩).2⟩)
    have h1 := hψ_t (c : G) c.2.1
    have h2 : (⟨t * (c : G) * t⁻¹, htB₂ (c : G) c.2.1⟩ : ↥B₂) = ⟨(c : G), c.2.1⟩ :=
      Subtype.ext c.2.2
    have h2' : (ψ ⟨t * (c : G) * t⁻¹, htB₂ (c : G) c.2.1⟩ : G) =
        (ψ ⟨(c : G), c.2.1⟩ : G) := congrArg (fun z : ↥B₂ => (ψ z : G)) h2
    exact (h2'.symm.trans h1).symm
  let ψEG : ↥EG →* ↥(bOne z) :=
    MonoidHom.mk' (fun c => ψ ⟨(c : G), c.2.1⟩) (fun c d => Subtype.ext (by
      show (ψ (⟨(c : G), c.2.1⟩ * ⟨(d : G), d.2.1⟩) : G) =
        ((ψ ⟨(c : G), c.2.1⟩ : ↥(bOne z)) : G) * ((ψ ⟨(d : G), d.2.1⟩ : ↥(bOne z)) : G)
      rw [map_mul]; rfl))
  have hψEGker : (ψEG.ker).map EG.subtype = EG ⊓ bOne z := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨c.2, (hψ_eq_one_iff ⟨(c : G), c.2.1⟩).mp hc⟩
    · intro hx
      obtain ⟨hxEG, hxB₁⟩ := Subgroup.mem_inf.mp hx
      exact ⟨⟨x, hxEG⟩,
        (hψ_eq_one_iff ⟨x, hEG_le_B₂ hxEG⟩).mpr hxB₁, rfl⟩
  have hψEGrange_le : ψEG.range ≤ (EG ⊓ bOne z).subgroupOf (bOne z) := by
    rintro y ⟨c, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨⟨hR.b2.B₁_le (ψ ⟨(c : G), c.2.1⟩).2, ?_⟩, (ψ ⟨(c : G), c.2.1⟩).2⟩)
    have h1 := hψ_t (c : G) c.2.1
    have h2 : (⟨t * (c : G) * t⁻¹, htB₂ (c : G) c.2.1⟩ : ↥B₂) =
        (⟨(c : G), c.2.1⟩ : ↥B₂)⁻¹ := by
      apply Subtype.ext
      show t * (c : G) * t⁻¹ = (c : G)⁻¹
      exact c.2.2
    have h2' : (ψ ⟨t * (c : G) * t⁻¹, htB₂ (c : G) c.2.1⟩ : G) =
        (ψ (⟨(c : G), c.2.1⟩ : ↥B₂)⁻¹ : G) :=
      congrArg (fun z : ↥B₂ => (ψ z : G)) h2
    have h3 : (ψ (⟨(c : G), c.2.1⟩ : ↥B₂)⁻¹ : G) = (ψ ⟨(c : G), c.2.1⟩ : G)⁻¹ := by
      rw [map_inv]; rfl
    exact ((h3.symm.trans (h2'.symm.trans h1))).symm
  have hsubgroupOfCard : ∀ {H : Subgroup G}, H ≤ bOne z →
      Nat.card ↥(H.subgroupOf (bOne z)) = Nat.card ↥H := fun {H} hH =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hCGcard_le : Nat.card ↥CG ≤ 9 := by
    have h1 := Subgroup.card_ker_mul_card_range ψCG
    have hkerCard : Nat.card ↥ψCG.ker = Nat.card ↥(CG ⊓ bOne z) := by
      rw [← hψCGker, Subgroup.card_map_of_injective CG.subtype_injective]
    have hrange_le : Nat.card ↥ψCG.range ≤ 3 := by
      calc Nat.card ↥ψCG.range ≤ Nat.card ↥((CG ⊓ bOne z).subgroupOf (bOne z)) :=
            Subgroup.card_le_of_le hψCGrange_le
        _ = Nat.card ↥(CG ⊓ bOne z) := hsubgroupOfCard inf_le_right
        _ = 3 := hCGcapCard
    have hCGeq : Nat.card ↥CG = Nat.card ↥(CG ⊓ bOne z) * Nat.card ↥ψCG.range := by
      calc Nat.card ↥CG = Nat.card ↥ψCG.ker * Nat.card ↥ψCG.range := h1.symm
        _ = Nat.card ↥(CG ⊓ bOne z) * Nat.card ↥ψCG.range := by rw [hkerCard]
    calc Nat.card ↥CG = 3 * Nat.card ↥ψCG.range := by rw [hCGeq, hCGcapCard]
      _ ≤ 3 * 3 := Nat.mul_le_mul_left 3 hrange_le
      _ = 9 := by norm_num
  have hEGcard_le : Nat.card ↥EG ≤ 81 := by
    have h1 := Subgroup.card_ker_mul_card_range ψEG
    have hkerCard : Nat.card ↥ψEG.ker = Nat.card ↥(EG ⊓ bOne z) := by
      rw [← hψEGker, Subgroup.card_map_of_injective EG.subtype_injective]
    have hrange_le : Nat.card ↥ψEG.range ≤ 9 := by
      calc Nat.card ↥ψEG.range ≤ Nat.card ↥((EG ⊓ bOne z).subgroupOf (bOne z)) :=
            Subgroup.card_le_of_le hψEGrange_le
        _ = Nat.card ↥(EG ⊓ bOne z) := hsubgroupOfCard inf_le_right
        _ = 9 := hEGcapCard
    have hEGeq : Nat.card ↥EG = Nat.card ↥(EG ⊓ bOne z) * Nat.card ↥ψEG.range := by
      calc Nat.card ↥EG = Nat.card ↥ψEG.ker * Nat.card ↥ψEG.range := h1.symm
        _ = Nat.card ↥(EG ⊓ bOne z) * Nat.card ↥ψEG.range := by rw [hkerCard]
    calc Nat.card ↥EG = 9 * Nat.card ↥ψEG.range := by rw [hEGeq, hEGcapCard]
      _ ≤ 9 * 9 := Nat.mul_le_mul_left 9 hrange_le
      _ = 81 := by norm_num
  have hprod : Nat.card ↥CG * Nat.card ↥EG = 729 := by
    rw [← hcard_prod, hR.b2.card]
    norm_num
  have hCG9 : Nat.card ↥CG = 9 := by
    have h1 : (Nat.card ↥CG : ℤ) * (Nat.card ↥EG : ℤ) = 729 := by exact_mod_cast hprod
    have h2 : (Nat.card ↥CG : ℤ) ≤ 9 := by exact_mod_cast hCGcard_le
    have h3 : (Nat.card ↥EG : ℤ) ≤ 81 := by exact_mod_cast hEGcard_le
    have h4 : (0 : ℤ) ≤ (Nat.card ↥CG : ℤ) := by positivity
    have h5 : (9 : ℤ) ≤ (Nat.card ↥CG : ℤ) := by nlinarith
    have h6 : (Nat.card ↥CG : ℤ) = 9 := le_antisymm h2 h5
    exact_mod_cast h6
  have hEG81 : Nat.card ↥EG = 81 := by
    have h : 9 * Nat.card ↥EG = 729 := by rw [← hprod, hCG9]
    omega
  have hB₂_le_cenR : B₂ ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (hB₂comm x hx r (hR.le hr)).symm
  have hktil_nor : Subgroup.centralizer (R : Set G) ≤
      Subgroup.normalizer ((ktil R : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmapH : (Subgroup.centralizer (R : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer (R : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    change (CFSG.RankThree.PartTwo.Sec21.FF79.OppE 3
        (Subgroup.centralizer (R : Set G))).map (MulAut.conj g).toMonoidHom =
      CFSG.RankThree.PartTwo.Sec21.FF79.OppE 3 (Subgroup.centralizer (R : Set G))
    rw [CFSG.RankThree.PartTwo.Sec21.FF79.map_oppE_mulEquiv, hmapH]
  have hEG_le_ktil : EG ≤ ktil R := by
    intro x hx
    have hxcen : x ∈ Subgroup.centralizer (R : Set G) := hB₂_le_cenR hx.1
    have hxnor : x ∈ Subgroup.normalizer ((ktil R : Subgroup G) : Set G) := hktil_nor hxcen
    have hxtK : x * t * x⁻¹ ∈ ktil R := (Subgroup.mem_normalizer_iff.mp hxnor t).mp htK
    have hxinvK : x * t * x⁻¹ * t⁻¹ ∈ ktil R := (ktil R).mul_mem hxtK ((ktil R).inv_mem htK)
    have heq : x * t * x⁻¹ * t⁻¹ = x⁻¹ := by
      have hx3 : x ^ 3 = 1 := hR.b2.abel.2 x hx.1
      have hx2 : x ^ 2 = x⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        rw [← pow_succ]
        exact hx3
      calc x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
        _ = x * (t * x * t⁻¹)⁻¹ := by rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group]
        _ = x * x := by rw [hx.2, inv_inv]
        _ = x ^ 2 := by rw [pow_two]
        _ = x⁻¹ := hx2
    rw [heq] at hxinvK
    simpa using (ktil R).inv_mem hxinvK
  exact ⟨EG, hEG_le_ktil, hR.b2.abel.mono hEG_le_B₂, by rw [hEG81]; norm_num⟩

end CFSG.StandardType.FF81.PropOne

end
