module

public import CFSG.Sporadic.Fi24.Class
public import CFSG.Sporadic.Fi23.StarKernel
public import CFSG.Fischer.EdgeAction
public import CFSG.Sporadic.Fi22.TauGroup

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_centralizer_R
    {x y : R} : x ∈ Subgroup.centralizer ({y} : Set R) ↔ x * y = y * x :=
  Subgroup.mem_centralizer_singleton_iff (G := R)

theorem mem_centralizer_J
    {x y : J} : x ∈ Subgroup.centralizer ({y} : Set J) ↔ x * y = y * x :=
  Subgroup.mem_centralizer_singleton_iff (G := J)

theorem mem_centralizer_Fi23 {x y : Fi23.J} :
    x ∈ Subgroup.centralizer ({y} : Set Fi23.J) ↔ x * y = y * x :=
  Subgroup.mem_centralizer_singleton_iff (G := Fi23.J)

@[expose] noncomputable def xb :
    R := cls p1

theorem xb_eq : xb = cls p1 := rfl

theorem xb_mem_D24 :
    xb ∈ D24 := cls_mem p1

theorem tR_mul_xb_sq :
    tR * xb * (tR * xb) = 1 := by
  have h := pow_orderOf_eq_one (tR * cls p1)
  rw [orderOf_tR_mul_cls_p1, pow_two] at h
  exact h

theorem tR_xb_comm :
    tR * xb = xb * tR := by
  have hx : xb * xb = 1 := Pair.mul_self pair_R xb_mem_D24
  calc tR * xb = xb * xb * (tR * xb) := by rw [hx, one_mul]
    _ = xb * (tR * tR) * xb * (tR * xb) := by rw [tR_mul_tR, mul_one]
    _ = xb * tR * (tR * xb * (tR * xb)) := by simp only [mul_assoc]
    _ = xb * tR := by rw [tR_mul_xb_sq, mul_one]

theorem tR_ne_xb : tR ≠ xb := by
  intro h
  have := orderOf_tR_mul_cls_p1
  rw [← xb_eq, ← h, tR_mul_tR, orderOf_one] at this
  exact absurd this (by norm_num)

theorem xb_mem_localClass :
    xb ∈ LocalClass D24 tR :=
  ⟨xb_mem_D24, tR_ne_xb.symm, tR_xb_comm.symm⟩

@[expose] noncomputable def tJ :
    J := tAut a * a⁻¹

theorem jR_tJ :
    jR tJ = tR * xb := tR_mul_cls_p1_eq.symm

@[expose] noncomputable def sb :
    Fi23.J := fi23EquivJMR ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩

theorem sb_eq :
    sb = fi23EquivJMR ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩ := rfl

theorem sb_mem_D23 :
    sb ∈ Fi23.D23 := isConj_d_fi23EquivJMR xb_mem_localClass

structure EdgeSwap
    (e : J) : Prop where
  swap_tR : jR e * tR * (jR e)⁻¹ = xb
  swap_xb : jR e * xb * (jR e)⁻¹ = tR
  sq : e * e = 1
  fixed : Nat.card {w : ↥(LocalClass D24 tR ∩ LocalClass D24 xb) //
    jR e * (w : R) * (jR e)⁻¹ = w} = 360

noncomputable abbrev CE :
    Subgroup R := Subgroup.centralizer ({tR * xb} : Set R) ⊓ JR

noncomputable abbrev LE :
    Subgroup R := CE ⊓ Subgroup.centralizer ({tR} : Set R)

theorem mem_MR_of_mem_LE
    {ℓ : R} (h : ℓ ∈ LE) : ℓ ∈ MR := by
  rcases mem_MR_or_of_commute (Subgroup.mem_inf.1 h).2 with h' | h'
  · exact h'
  · exfalso
    apply tR_not_mem_JR
    have := JR.mul_mem (JR.inv_mem (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h).1).2) (MR_le_JR h')
    rwa [inv_mul_cancel_left] at this

theorem commute_xb_of_mem_LE
    {ℓ : R} (h : ℓ ∈ LE) : ℓ * xb = xb * ℓ := by
  have h1 : ℓ * (tR * xb) = tR * xb * ℓ :=
    mem_centralizer_R.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 h).1).1
  have h2 : ℓ * tR = tR * ℓ := mem_centralizer_R.1 (Subgroup.mem_inf.1 h).2
  have h3 : tR * (ℓ * xb) = tR * (xb * ℓ) := by
    rw [← mul_assoc, ← h2, mul_assoc, h1, mul_assoc]
  exact mul_left_cancel h3

@[expose] noncomputable def fromFi23 :
    Fi23.J →* R :=
  MR.subtype.comp (fi23EquivJMR.symm : Fi23.J →* MR)

theorem fromFi23_apply
    (g : Fi23.J) : fromFi23 g = ((fi23EquivJMR.symm g : MR) : R) := rfl

theorem fromFi23_injective :
    Function.Injective fromFi23 := fun g h e => by
  rw [fromFi23_apply, fromFi23_apply] at e
  exact fi23EquivJMR.symm.injective (Subtype.ext e)

theorem LE_eq_map :
    LE = (Subgroup.centralizer ({sb} : Set Fi23.J)).map fromFi23 := by
  ext ℓ
  constructor
  · intro h
    have hm := mem_MR_of_mem_LE h
    refine Subgroup.mem_map.2 ⟨fi23EquivJMR ⟨ℓ, hm⟩, mem_centralizer_Fi23.2 ?_, ?_⟩
    · rw [sb_eq, ← map_mul, ← map_mul]
      refine congrArg fi23EquivJMR (Subtype.ext ?_)
      show ℓ * (xb * tR) = xb * tR * ℓ
      have h2 : ℓ * tR = tR * ℓ := mem_centralizer_R.1 (Subgroup.mem_inf.1 h).2
      rw [← mul_assoc, commute_xb_of_mem_LE h, mul_assoc, h2, mul_assoc]
    · rw [fromFi23_apply, MulEquiv.symm_apply_apply]
  · intro h
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 h
    obtain ⟨m, rfl⟩ := fi23EquivJMR.surjective g
    rw [fromFi23_apply, MulEquiv.symm_apply_apply]
    have hmc : m * ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩ =
        ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩ * m := by
      apply fi23EquivJMR.injective
      rw [map_mul, map_mul, ← sb_eq]
      exact mem_centralizer_Fi23.1 hg
    have hmc'' := Subtype.ext_iff.1 hmc
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at hmc''
    have hmc' : (m : R) * (xb * tR) = xb * tR * m := hmc''
    have hmT : (m : R) * tR = tR * m := commute_tR_of_mem_MR m.2
    have hmx : (m : R) * xb = xb * m := by
      have h3 : (m : R) * xb * tR = xb * m * tR := by
        rw [mul_assoc, hmc', mul_assoc, ← hmT, mul_assoc]
      exact mul_right_cancel h3
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 ?_, MR_le_JR m.2⟩,
      mem_centralizer_R.2 hmT⟩
    rw [← mul_assoc, hmT, mul_assoc, hmx, mul_assoc]

@[expose] noncomputable def leEquiv :
    Subgroup.centralizer ({sb} : Set Fi23.J) ≃* LE :=
  ((Subgroup.centralizer ({sb} : Set Fi23.J)).equivMapOfInjective fromFi23
    fromFi23_injective).trans (MulEquiv.subgroupCongr LE_eq_map.symm)

theorem card_LE :
    Nat.card LE = 129123503308800 := by
  rw [LE_eq_map, Subgroup.card_map_of_injective fromFi23_injective]
  exact Fi23.card_centralizer_of_mem sb_mem_D23

theorem commutator_LE :
    commutator LE = ⊤ := by
  rw [LE_eq_map]
  exact commutator_map_eq_top (G := Fi23.J) (H := R) fromFi23 fromFi23_injective
    (Fi23.commutator_centralizer_of_mem sb_mem_D23)

theorem starEquiv_conj
    {m : R} (hm : m ∈ MR) (f : LocalClass D24 tR)
    (hf' : m * f * m⁻¹ ∈ LocalClass D24 tR) :
    (starEquiv ⟨m * f * m⁻¹, hf'⟩ : Fi23.J) =
      fi23EquivJMR ⟨m, hm⟩ * starEquiv f * (fi23EquivJMR ⟨m, hm⟩)⁻¹ := by
  rw [starEquiv_val, starEquiv_val, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg fi23EquivJMR (Subtype.ext ?_)
  show m * f * m⁻¹ * tR = m * (f * tR) * m⁻¹
  have hmT : m * tR = tR * m := commute_tR_of_mem_MR hm
  have hmi : m⁻¹ * tR = tR * m⁻¹ := by
    calc m⁻¹ * tR = m⁻¹ * (tR * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * tR) * m⁻¹ := by rw [hmT]
      _ = tR * m⁻¹ := by group
  rw [mul_assoc (m * f), hmi]
  group

theorem eq_of_mem_LE_centralizes
    {ℓ : R} (hℓ : ℓ ∈ LE)
    (h : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb, ℓ * w * ℓ⁻¹ = w) :
    ℓ = 1 ∨ ℓ = tR * xb := by
  have hm := mem_MR_of_mem_LE hℓ
  have hsb : starEquiv ⟨xb, xb_mem_localClass⟩ = ⟨sb, sb_mem_D23⟩ := rfl
  have hℓ' := hℓ
  rw [LE_eq_map] at hℓ'
  obtain ⟨g, hgC, hge⟩ := Subgroup.mem_map.1 hℓ'
  have hgℓ : fi23EquivJMR ⟨ℓ, hm⟩ = g := by
    have : (⟨ℓ, hm⟩ : MR) = fi23EquivJMR.symm g := Subtype.ext (hge.symm.trans (fromFi23_apply g))
    rw [this, MulEquiv.apply_symm_apply]
  have hg : g * sb = sb * g := mem_centralizer_Fi23.1 hgC
  have hcent : ∀ y ∈ LocalClass Fi23.D23 sb, g * y * g⁻¹ = y := by
    intro y hy
    obtain ⟨f, hf⟩ := starEquiv.surjective ⟨y, hy.1⟩
    have hfx : (f : R) ∈ LocalClass D24 xb := by
      have := (localPoints_tR.mem_localClass_iff Fi23.pair_J ⟨xb, xb_mem_localClass⟩ f).2
      apply this
      show ((starEquiv f : Fi23.D23) : Fi23.J) ∈ LocalClass Fi23.D23
        ((starEquiv ⟨xb, xb_mem_localClass⟩ : Fi23.D23) : Fi23.J)
      rw [hf, hsb]
      exact hy
    have hfix := h f ⟨f.2, hfx⟩
    have hf' : ℓ * (f : R) * ℓ⁻¹ ∈ LocalClass D24 tR := by rw [hfix]; exact f.2
    have e1 := starEquiv_conj hm f hf'
    have e2 : (⟨ℓ * (f : R) * ℓ⁻¹, hf'⟩ : LocalClass D24 tR) = f := Subtype.ext hfix
    rw [e2, hf, hgℓ] at e1
    exact e1.symm
  rcases Fi23.eq_of_centralizes_star sb_mem_D23 hg hcent with h1 | h1
  · left
    have : (⟨ℓ, hm⟩ : MR) = 1 := fi23EquivJMR.injective (by rw [map_one, hgℓ]; exact h1)
    have h' := Subtype.ext_iff.1 this
    rw [OneMemClass.coe_one] at h'
    exact h'
  · right
    have : (⟨ℓ, hm⟩ : MR) = ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩ :=
      fi23EquivJMR.injective (by rw [hgℓ, h1, sb_eq])
    rw [tR_xb_comm]
    have h' := Subtype.ext_iff.1 this
    exact h'

theorem tR_mul_xb_mem_CE :
    tR * xb ∈ CE := by
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 rfl, ?_⟩
  rw [← jR_tJ]
  exact jR_mem_JR tJ

theorem card_D22 : Nat.card Fi22.D = 3510 := by
  rw [← Nat.card_congr Fi22.ptD, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_fixed_ne_360
    (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
      Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ)) :
    ∀ y : Fi22.J, y ^ 2 = 1 → y ≠ 1 →
      Nat.card {x : Fi22.D // y * (x : Fi22.J) * y⁻¹ = x} ≠ 360 := fun y hy2 hy1 h => by
  have h' := hfix22 y hy2 hy1
  rw [h] at h'
  rcases h' with h' | h' | h' <;> norm_num at h'

section Swap

variable {e : J} (he : EdgeSwap e)
include he

theorem jR_mem_CE : jR e ∈ CE := by
  have key : jR e * (tR * xb) * (jR e)⁻¹ = tR * xb := by
    calc jR e * (tR * xb) * (jR e)⁻¹ = (jR e * tR * (jR e)⁻¹) * (jR e * xb * (jR e)⁻¹) := by
          group
      _ = tR * xb := by rw [he.swap_tR, he.swap_xb, tR_xb_comm]
  refine Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 ?_, jR_mem_JR e⟩
  calc jR e * (tR * xb) = jR e * (tR * xb) * (jR e)⁻¹ * jR e := by group
    _ = tR * xb * jR e := by rw [key]

theorem index_LE (hW : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
      ∃ w' ∈ LocalClass D24 tR ∩ LocalClass D24 xb, w * w' ≠ w' * w) :
    (LE.subgroupOf CE).index = 2 := by
  have h := index_centralizer_inf_eq_two pair_R tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm hW
    (jR_mem_JR e) he.swap_tR he.swap_xb
  exact h

theorem card_CE
    (hW : ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
      ∃ w' ∈ LocalClass D24 tR ∩ LocalClass D24 xb, w * w' ≠ w' * w) :
    Nat.card CE = 2 * Nat.card (tauGroup Fi22.pair_D) := by
  have h := card_eq_two_mul_of_index (inf_le_left : LE ≤ CE) (index_LE he hW)
  rw [h, card_LE, Fi22.card_tauGroup]

variable (ψ : ↥(LocalClass D24 tR ∩ LocalClass D24 xb) ≃ Fi22.D)
  (hψc : ∀ x y : ↥(LocalClass D24 tR ∩ LocalClass D24 xb),
    (x : R) * y = y * x ↔ (ψ x : Fi22.J) * ψ y = ψ y * ψ x)
  (hψt : ∀ x y : ↥(LocalClass D24 tR ∩ LocalClass D24 xb),
    ∃ h : (x : R) * y * x ∈ LocalClass D24 tR ∩ LocalClass D24 xb,
      (ψ ⟨_, h⟩ : Fi22.J) = ψ x * ψ y * ψ x)

theorem edgeHom_swap_not_mem
    (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
      Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ)) :
    edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
      Fi22.center_eq_bot ⟨jR e, (inf_le_left : CE ≤ _) (jR_mem_CE he)⟩ ∉
        (innerTau Fi22.pair_D).range := by
  have hj : jR e * jR e = 1 := by rw [← map_mul, he.sq, map_one]
  have h := edgeHom_not_mem_range pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb
    tR_xb_comm ψ hψc hψt Fi22.center_eq_bot 360
    (g := ⟨jR e, (inf_le_left : CE ≤ _) (jR_mem_CE he)⟩)
    (Subtype.ext (by rw [Subgroup.coe_mul, OneMemClass.coe_one]; exact hj)) he.fixed
    (by rw [card_D22]; norm_num) (card_fixed_ne_360 hfix22)
  exact h

end Swap

theorem outTwo_CE
    (hPF : PolarFacts)
    (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
      Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
    {e : J} (he : EdgeSwap e) : OutTwo CE := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 hPF) ⟨tR, tR_mem_D24⟩ ⟨xb, xb_mem_D24⟩ tR_ne_xb
    tR_xb_comm
  have hW := exists_not_commute_of_edgeEquiv Fi22.pair_D ψ hψc Fi22.center_eq_bot
  have hCE : CE ≤ Subgroup.centralizer ({tR * xb} : Set R) := inf_le_left
  exact outTwo_edgeC pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
    Fi22.center_eq_bot Fi22.index_innerTau_range hCE
    Fi22.tauGroup_complete_D commutator_LE (by rw [Fi22.card_tauGroup]; exact card_LE)
    (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
    (card_CE he hW) tR_mul_xb_mem_CE (jR_mem_CE he) (edgeHom_swap_not_mem he ψ hψc hψt hfix22)

theorem map_centralizer_tJ :
    (Subgroup.centralizer ({tJ} : Set J)).map jR = CE := by
  ext x
  constructor
  · intro h
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 h
    refine Subgroup.mem_inf.2 ⟨mem_centralizer_R.2 ?_, jR_mem_JR g⟩
    rw [← jR_tJ]
    show jR g * jR tJ = jR tJ * jR g
    rw [← map_mul, ← map_mul, mem_centralizer_J.1 hg]
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    rw [← range_jR] at h2
    obtain ⟨g, rfl⟩ := h2
    refine ⟨g, mem_centralizer_J.2 ?_, rfl⟩
    apply jR_injective
    rw [show jR (g * tJ) = jR g * jR tJ from map_mul jR g tJ,
      show jR (tJ * g) = jR tJ * jR g from map_mul jR tJ g, jR_tJ]
    exact mem_centralizer_R.1 h1

theorem outTwo_centralizer_tJ
    (hPF : PolarFacts)
    (hfix22 : ∀ g : Fi22.J, g ^ 2 = 1 → g ≠ 1 →
      Nat.card {x : Fi22.D // g * (x : Fi22.J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ))
    {e : J} (he : EdgeSwap e) : OutTwo (Subgroup.centralizer ({tJ} : Set J)) := by
  have h := OutTwo.of_map (G := J) (H := R) jR jR_injective map_centralizer_tJ
    (outTwo_CE hPF hfix22 he)
  exact h

end CFSG.Sporadic.Fi24
