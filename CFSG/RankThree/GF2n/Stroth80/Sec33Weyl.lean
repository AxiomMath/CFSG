module

public import CFSG.RankThree.GF2n.Stroth80.Sec33NotInQ
public import CFSG.RankThree.GF2n.Stroth80.Sec33Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_mem_centralizer_B (hc : Ctx M Q Z B) {y t : G} (hy : y ∈ Q)
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) :
    ⁅y, t⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
  classical
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  have htM : t ∈ M := by have := ht; rw [← hc.QB_inf_M_eq] at this; exact this.2
  have htc : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp ht.2 z hz
    rw [← this]; group
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h.linear_of_centralizes htM htc
  obtain ⟨u₀, hu₀B, hu₀Q, hu₀⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  have hTb : T b = b := by
    have := hc.act_fix_B ht (T := T) hTπ u₀ hu₀B
    rwa [hu₀] at this
  have hct : t * y⁻¹ * t⁻¹ ∈ Q := hc.L0_normalizes_Q ht y⁻¹ (Q.inv_mem hy)
  have hcQ : ⁅y, t⁆ ∈ Q := by
    rw [show ⁅y, t⁆ = y * (t * y⁻¹ * t⁻¹) by rw [commutatorElement_def]; group]
    exact Q.mul_mem hy hct
  refine ⟨hcQ, (hcent _ hcQ).mpr ?_⟩
  have hπ : M₀.π ⁅y, t⁆ = M₀.π y - T (M₀.π y) := by
    rw [show ⁅y, t⁆ = y * (t * y⁻¹ * t⁻¹) by rw [commutatorElement_def]; group,
      M₀.π_mul _ hy _ hct, hTπ y⁻¹ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy, map_neg,
      sub_eq_add_neg]
  have := hTB (M₀.π y) b
  rw [hTb] at this
  rw [hπ, map_sub, LinearMap.sub_apply, this, sub_self]

theorem Ctx.comm_mem_L0_of_weyl (hc : Ctx M Q Z B) {n : G} (h1 : conjSubgroup n Q = QB B)
    (h2 : conjSubgroup n (QB B) = Q) (h3 : conjSubgroup n Z = B) (h4 : conjSubgroup n B = Z)
    {l c : G} (hl : l ∈ QB B) (hcB : c ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅l, c⁆ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
  have hy : n⁻¹ * l * n ∈ Q := mem_conjSubgroup.mp (h1 ▸ hl)
  have ht₁QB : n⁻¹ * c * n ∈ QB B := mem_conjSubgroup.mp (h2 ▸ hcB.1)
  have ht₁C : n⁻¹ * c * n ∈ Subgroup.centralizer (Z : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzB : n * z * n⁻¹ ∈ B := h3 ▸ (mem_conjSubgroup.mpr (by
      rw [show n⁻¹ * (n * z * n⁻¹) * n = z by group]; exact hz))
    have := Subgroup.mem_centralizer_iff.mp hcB.2 _ hzB
    calc z * (n⁻¹ * c * n) = n⁻¹ * ((n * z * n⁻¹) * c) * n := by group
      _ = n⁻¹ * (c * (n * z * n⁻¹)) * n := by rw [this]
      _ = (n⁻¹ * c * n) * z := by group
  have hM1 := hc.comm_mem_centralizer_B hy ⟨ht₁QB, ht₁C⟩
  have hconj := hc.conj_centralizer_B h1 h4
  have : ⁅l, c⁆ ∈ conjSubgroup n (Q ⊓ Subgroup.centralizer (B : Set G)) := by
    rw [mem_conjSubgroup]
    have e : n⁻¹ * ⁅l, c⁆ * n = ⁅n⁻¹ * l * n, n⁻¹ * c * n⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact hM1
  rwa [hconj] at this

theorem Ctx.conj_mem_inf (hc : Ctx M Q Z B) {y r : G} (hy : y ∈ Q) (hr : r ∈ Q ⊓ QB B) :
    y * r * y⁻¹ ∈ Q ⊓ QB B := by
  have hZ : ⁅y, r⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hr.1
  have hZL : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  rw [show y * r * y⁻¹ = ⁅y, r⁆ * r by rw [commutatorElement_def]; group]
  exact (Q ⊓ QB B).mul_mem (hZL hZ) hr

theorem Ctx.ZB_comm_CB (hc : Ctx M Q Z B) {y : G} (hy : y ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ∀ a ∈ Z ⊔ B, a * y = y * a := by
  have hle : Z ⊔ B ≤ Subgroup.centralizer ({y} : Set G) := sup_le
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
      (hc.hyp.toHyp79.V_central hz hy.1))
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy.2 b hb))
  exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem Ctx.ZB_comm_L0 (hc : Ctx M Q Z B) {y : G}
    (hy : y ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) : ∀ a ∈ Z ⊔ B, a * y = y * a := by
  obtain ⟨g, hg⟩ := hc.conj
  have hle : Z ⊔ B ≤ Subgroup.centralizer ({y} : Set G) := sup_le
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy.2 z hz))
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (by
      have hyQ : y ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hy.1
      have hbZ : b ∈ conjSubgroup g Z := hg ▸ hb
      exact hc.hyp.toHyp79.conj_central g hbZ hyQ))
  exact fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

theorem Ctx.ZB_le_inf (hc : Ctx M Q Z B) : Z ⊔ B ≤ Q ⊓ QB B :=
  sup_le (le_inf hc.Z_le_Q hc.Z_le_QB.1) (le_inf hc.le hc.B_le_QB)

theorem Ctx.ZB_le_CB (hc : Ctx M Q Z B) : Z ⊔ B ≤ Q ⊓ Subgroup.centralizer (B : Set G) := by
  refine sup_le (le_inf hc.Z_le_Q fun z hz => ?_) (le_inf hc.le fun b hb => ?_)
  · exact Subgroup.mem_centralizer_iff.mpr fun v hv => (hc.hyp.toHyp79.V_central hz (hc.le hv)).symm
  · exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subtype.ext_iff.mp (hc.isElemAbelian_B.1.is_comm.comm ⟨v, hv⟩ ⟨b, hb⟩)

theorem Ctx.weyl_conj_mul_comm_mem (hc : Ctx M Q Z B) {u l : G} (hu : u ∈ Q) (hl : l ∈ QB B)
    (h1 : conjSubgroup (u * l * u) Q = QB B) (h2 : conjSubgroup (u * l * u) (QB B) = Q)
    (h3 : conjSubgroup (u * l * u) Z = B) (h4 : conjSubgroup (u * l * u) B = Z) {t : G}
    (ht : t ∈ QB B ⊓ Subgroup.centralizer (Z : Set G)) :
    (u * l * u) * t * (u * l * u)⁻¹ * ⁅u, t⁆ ∈ Q ⊓ QB B := by
  classical
  obtain ⟨g, hg⟩ := hc.conj
  have hcCB : ⁅u, t⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := hc.comm_mem_centralizer_B hu ht
  have hdL : ⁅l, ⁅u, t⁆⁆ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) :=
    hc.comm_mem_L0_of_weyl h1 h2 h3 h4 hl hcCB
  have hd1 : ⁅u, ⁅l, ⁅u, t⁆⁆⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) :=
    hc.comm_mem_centralizer_B hu hdL
  have hlQB : l ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hl
  have htQB : t ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ ht.1
  have heB : ⁅l, t⁆ ∈ B := hg ▸ hc.hyp.toHyp79.comm_mem_conj g hlQB htQB
  have hxCB : (u * l * u) * t * (u * l * u)⁻¹ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
    have hconj : conjSubgroup (u * l * u) (QB B ⊓ Subgroup.centralizer (Z : Set G)) =
        Q ⊓ Subgroup.centralizer (B : Set G) := by
      rw [conjSubgroup_inf, conjSubgroup_centralizer, h2, h3]
    rw [← hconj, mem_conjSubgroup]
    rw [show (u * l * u)⁻¹ * ((u * l * u) * t * (u * l * u)⁻¹) * (u * l * u) = t by group]
    exact ht
  have hid : (u * l * u) * t * (u * l * u)⁻¹ =
      ⁅u, ⁅l, ⁅u, t⁆⁆⁆ * ⁅l, ⁅u, t⁆⁆ * ⁅u, ⁅u, t⁆⁆ * ⁅u, t⁆ * ⁅u, ⁅l, t⁆⁆ * ⁅l, t⁆ * ⁅u, t⁆ *
        t := by
    simp only [commutatorElement_def]; group
  have hL₀inv : t⁻¹ ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) :=
    (QB B ⊓ Subgroup.centralizer (Z : Set G)).inv_mem ht
  have hlam1 : ⁅⁅u, t⁆, t⁻¹⁆ ∈ Q ⊓ QB B := by
    have := hc.comm_mem_inf hL₀inv hcCB
    rw [← commutatorElement_inv]
    exact (Q ⊓ QB B).inv_mem this
  set c := ⁅u, t⁆ with hcdef
  set d := ⁅l, c⁆ with hddef
  set e := ⁅l, t⁆ with hedef
  set d₁ := ⁅u, d⁆ with hd1def
  set c₁ := ⁅u, c⁆ with hc1def
  set e₁ := ⁅u, e⁆ with he1def
  set x := (u * l * u) * t * (u * l * u)⁻¹ with hxdef
  have hcQ : c ∈ Q := hcCB.1
  have hc₁Z : c₁ ∈ Z := hc.hyp.toHyp79.comm_mem_V hu hcQ
  have he₁Z : e₁ ∈ Z := hc.hyp.toHyp79.comm_mem_V hu (hc.le heB)
  have hc2Z : c * c ∈ Z := by
    have := hc.hyp.toHyp79.sq_mem_V hcQ
    rwa [pow_two] at this
  set ζ := c₁ * e₁ * e * (c * c) with hζdef
  have hζA : ζ ∈ Z ⊔ B :=
    (Z ⊔ B).mul_mem ((Z ⊔ B).mul_mem ((Z ⊔ B).mul_mem (Subgroup.mem_sup_left hc₁Z)
      (Subgroup.mem_sup_left he₁Z)) (Subgroup.mem_sup_right heB)) (Subgroup.mem_sup_left hc2Z)
  have k1 : c * e₁ = e₁ * c := (hc.ZB_comm_CB hcCB e₁ (Subgroup.mem_sup_left he₁Z)).symm
  have k2 : c * e = e * c := (hc.ZB_comm_CB hcCB e (Subgroup.mem_sup_right heB)).symm
  have hce : c * e₁ * e = e₁ * e * c :=
    calc c * e₁ * e = e₁ * c * e := by rw [k1]
      _ = e₁ * (c * e) := by group
      _ = e₁ * (e * c) := by rw [k2]
      _ = e₁ * e * c := by group
  have hdζ : d * ζ = ζ * d := (hc.ZB_comm_L0 hdL ζ hζA).symm
  have hd1ζ : d₁ * ζ = ζ * d₁ := (hc.ZB_comm_CB hd1 ζ hζA).symm
  have hx2 : x = ζ * d₁ * (d * t) := by
    rw [hid]
    calc d₁ * d * c₁ * c * e₁ * e * c * t = d₁ * d * (c₁ * (c * e₁ * e) * c) * t := by group
      _ = d₁ * d * (c₁ * (e₁ * e * c) * c) * t := by rw [hce]
      _ = d₁ * (d * ζ) * t := by rw [hζdef]; group
      _ = d₁ * (ζ * d) * t := by rw [hdζ]
      _ = (d₁ * ζ) * d * t := by group
      _ = (ζ * d₁) * d * t := by rw [hd1ζ]
      _ = ζ * d₁ * (d * t) := by group
  have hdt : d * t ∈ Q ⊓ QB B := by
    have hmem : d * t ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
      have : d * t = (ζ * d₁)⁻¹ * x := by rw [hx2]; group
      rw [this]
      exact (Q ⊓ Subgroup.centralizer (B : Set G)).mul_mem
        ((Q ⊓ Subgroup.centralizer (B : Set G)).inv_mem
          ((Q ⊓ Subgroup.centralizer (B : Set G)).mul_mem (hc.ZB_le_CB hζA) hd1)) hxCB
    exact ⟨hmem.1, (QB B).mul_mem hdL.1 ht.1⟩
  set r' := d * t with hr'def
  have hz' : ⁅u, r'⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hu hdt.1
  have hident : d₁ * c = ⁅u, r'⁆ * r' * (c⁻¹ * (⁅c, t⁻¹⁆ * r'⁻¹) * c) := by
    have hd_rt : d = r' * t⁻¹ := by rw [hr'def]; group
    rw [hd1def, hd_rt, hcdef]
    simp only [commutatorElement_def]; group
  have hZL : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hd1c : d₁ * c ∈ Q ⊓ QB B := by
    rw [hident]
    refine (Q ⊓ QB B).mul_mem ((Q ⊓ QB B).mul_mem (hZL hz') hdt) ?_
    have := hc.conj_mem_inf (y := c⁻¹) (Q.inv_mem hcQ)
      (r := ⁅c, t⁻¹⁆ * r'⁻¹) ((Q ⊓ QB B).mul_mem hlam1 ((Q ⊓ QB B).inv_mem hdt))
    rwa [inv_inv] at this
  have hconjdt : c⁻¹ * r' * c ∈ Q ⊓ QB B := by
    have := hc.conj_mem_inf (y := c⁻¹) (Q.inv_mem hcQ) (r := r') hdt
    rwa [inv_inv] at this
  have hfin : x * c = ζ * (d₁ * c) * (c⁻¹ * r' * c) := by rw [hx2]; group
  rw [hfin]
  exact (Q ⊓ QB B).mul_mem ((Q ⊓ QB B).mul_mem (hc.ZB_le_inf hζA) hd1c) hconjdt

end CFSG.RankThree.GF2n.Stroth80
