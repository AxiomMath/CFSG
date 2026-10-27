module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoBound
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
import CFSG.RankThree.GF2n.Stroth80.Sec115Count
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]


private theorem card_le_two_of_isCyclic_of_sq_eq_one {Γ : Type} [Group Γ] [Finite Γ]
    [IsCyclic Γ] (h : ∀ x : Γ, x * x = 1) : Nat.card Γ ≤ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Γ)
  have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact h g
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hord
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact hle

private noncomputable def Ctx.outerConjNormal (hc : Ctx M Q Z B) :
    Mbar M Q →* Outer (XbarMod M Q Z B) :=
  letI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  (QuotientGroup.mk' (inner (XbarMod M Q Z B))).comp
    ((centerQuotientHom ↥(Xbar M Q Z B)).comp
      (MulAut.conjNormal (H := Xbar M Q Z B)))

private theorem Ctx.mem_sup_centralizer_of_outerConjNormal_eq_one (hc : Ctx M Q Z B)
    {l : Mbar M Q} (h : Ctx.outerConjNormal hc l = 1) :
    l ∈ Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  have hinner : centerQuotientHom ↥(Xbar M Q Z B)
      ((MulAut.conjNormal (H := Xbar M Q Z B)) l) ∈ inner (XbarMod M Q Z B) := by
    have h1 := h
    unfold Ctx.outerConjNormal at h1
    change (QuotientGroup.mk' (inner (XbarMod M Q Z B)))
      (centerQuotientHom ↥(Xbar M Q Z B)
        ((MulAut.conjNormal (H := Xbar M Q Z B)) l)) = 1 at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨q, hq⟩ := hinner
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(Xbar M Q Z B)) q
  have hkq : QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) k = q := hk
  have hconj : (MulAut.conjNormal (H := Xbar M Q Z B)) ((k : Mbar M Q)⁻¹ * l) =
      ((MulAut.conjNormal (H := Xbar M Q Z B)) (k : Mbar M Q))⁻¹ *
        (MulAut.conjNormal (H := Xbar M Q Z B)) l := by
    rw [map_mul, map_inv]
  have hc₀ : centerQuotientHom ↥(Xbar M Q Z B)
      ((MulAut.conjNormal (H := Xbar M Q Z B)) ((k : Mbar M Q)⁻¹ * l)) = 1 := by
    have hk' : (MulAut.conjNormal (H := Xbar M Q Z B)) (k : Mbar M Q) =
        MulAut.conj k := by
      ext z
      simp [MulAut.conjNormal_apply, MulAut.conj_apply]
    have hqk : centerQuotientHom ↥(Xbar M Q Z B)
        ((MulAut.conjNormal (H := Xbar M Q Z B)) (k : Mbar M Q)) = MulAut.conj q := by
      rw [hk', centerQuotient_conj, hkq]
    rw [hconj, map_mul, map_inv, hqk, hq]
    group
  have hβ : (MulAut.conjNormal (H := Xbar M Q Z B)) ((k : Mbar M Q)⁻¹ * l) = 1 := by
    refine MulEquiv.ext fun z => ?_
    let S : Set ↥(Xbar M Q Z B) :=
      ((↑) : ↥(Xbar M Q Z B) → Mbar M Q) ⁻¹' Ebar M Q Z B
    have hgen : Subgroup.closure S = ⊤ := by
      change Subgroup.closure (Subtype.val ⁻¹' Ebar M Q Z B) = ⊤
      exact Subgroup.closure_closure_coe_preimage
    have hfix : ∀ x : ↥(Xbar M Q Z B), x ∈ Subgroup.closure S →
        (MulAut.conjNormal (H := Xbar M Q Z B)) ((k : Mbar M Q)⁻¹ * l) x = x := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem τ hτ =>
        have hτ2 : τ * τ = 1 := by
          apply Subtype.ext
          have hτo := Ctx.orderOf_eq_two_of_mem_Ebar hτ
          rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two, ← hτo]
          exact pow_orderOf_eq_one (τ : Mbar M Q)
        exact apply_eq_self_of_centerQuotientHom_eq_one hc.odd_card_center_Xbar hc₀ hτ2
      | one => exact map_one _
      | mul a b ha hb iha ihb => rw [map_mul, iha, ihb]
      | inv a ha iha => rw [map_inv, iha]
    exact hfix z (by rw [hgen]; exact Subgroup.mem_top z)
  have hcent : (k : Mbar M Q)⁻¹ * l ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxfix := congrArg (fun f : MulAut ↥(Xbar M Q Z B) => (f ⟨x, hx⟩ : ↥(Xbar M Q Z B)))
      hβ
    have h1 : ((k : Mbar M Q)⁻¹ * l) * x * ((k : Mbar M Q)⁻¹ * l)⁻¹ = x := by
      have h2 := congrArg Subtype.val hxfix
      simpa only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_one] using h2
    calc x * ((k : Mbar M Q)⁻¹ * l) =
        (((k : Mbar M Q)⁻¹ * l) * x * ((k : Mbar M Q)⁻¹ * l)⁻¹) *
          ((k : Mbar M Q)⁻¹ * l) := by rw [h1]
      _ = ((k : Mbar M Q)⁻¹ * l) * x := by group
  have hl : l = (k : Mbar M Q) * ((k : Mbar M Q)⁻¹ * l) := by group
  rw [hl]
  exact Subgroup.mul_mem_sup k.2 hcent

private theorem Ctx.card_range_outerConjNormal_comp_eq_one (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    Nat.card ((Ctx.outerConjNormal hc).comp (bar M Q (LB M Q B)).subtype).range = 1 := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let ψ : ↥L →* Outer (XbarMod M Q Z B) := (Ctx.outerConjNormal hc).comp L.subtype
  have hcyc : IsCyclic (Outer (XbarMod M Q Z B)) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.isCyclic_outer_of_lieModel_PSU4 hU
  have hrangeSq : ∀ g : ↥ψ.range, g * g = 1 := by
    intro g
    refine Subtype.ext ?_
    change (g : Outer (XbarMod M Q Z B)) * (g : Outer (XbarMod M Q Z B)) = 1
    obtain ⟨l, hl⟩ := g.2
    rw [← hl]
    change ψ l * ψ l = 1
    have hl2 : l * l = 1 := by
      apply Subtype.ext
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
        hc.isElemAbelian_bar_LB.2 l l.2
    rw [← map_mul, hl2, map_one]
  have hrange2 : Nat.card ↥ψ.range ≤ 2 :=
    card_le_two_of_isCyclic_of_sq_eq_one hrangeSq
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  let ybar : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hy.mem_M⟩
  let U : Subgroup (Mbar M Q) := ψ.ker.map L.subtype
  have hUle : U ≤ L := Subgroup.map_subtype_le _
  have hUinv : ∀ u ∈ U, ybar * u * ybar⁻¹ ∈ U := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hu
    have hconj : ybar * (l : Mbar M Q) * ybar⁻¹ ∈ L :=
      hc.conj_mem_bar_LB_of_isLBTorus hy l.2
    refine Subgroup.mem_map.mpr ⟨⟨ybar * (l : Mbar M Q) * ybar⁻¹, hconj⟩, ?_, rfl⟩
    change Ctx.outerConjNormal hc (ybar * (l : Mbar M Q) * ybar⁻¹) = 1
    have h1 : Ctx.outerConjNormal hc (ybar * (l : Mbar M Q) * ybar⁻¹) =
        Ctx.outerConjNormal hc ybar * Ctx.outerConjNormal hc (l : Mbar M Q) *
          (Ctx.outerConjNormal hc ybar)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [h1, show Ctx.outerConjNormal hc (l : Mbar M Q) = 1 from MonoidHom.mem_ker.mp hl]
    group
  have hLinv : ∀ u ∈ L, ybar * u * ybar⁻¹ ∈ L := fun u hu =>
    hc.conj_mem_bar_LB_of_isLBTorus hy hu
  obtain ⟨d, hd⟩ := hy.card_invariant U hUle hUinv
  obtain ⟨e, he⟩ := hy.card_invariant L le_rfl hLinv
  have hkerCard : Nat.card ↥U = Nat.card ↥ψ.ker :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hcard : Nat.card ↥L = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hdvd : Nat.card Z ^ d ∣ Nat.card Z ^ e := by
    rw [← hd, ← he]
    exact Subgroup.card_dvd_of_le hUle
  have hde : d ≤ e :=
    (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < Nat.card Z)).mp hdvd
  have hval : Nat.card Z ^ e = Nat.card Z ^ d * Nat.card ↥ψ.range := by
    rw [← he, hcard, ← hkerCard, hd, mul_comm]
  have hrd : Nat.card ↥ψ.range = Nat.card Z ^ (e - d) := by
    have h1 : Nat.card Z ^ d * Nat.card Z ^ (e - d) =
        Nat.card Z ^ d * Nat.card ↥ψ.range := by
      rw [← pow_add, show d + (e - d) = e by omega, hval]
    exact (Nat.mul_left_cancel (pow_pos Nat.card_pos d) h1).symm
  have hk0 : e - d = 0 := by
    by_contra hk
    have hkpos : 0 < e - d := Nat.pos_of_ne_zero hk
    have hqle : Nat.card Z ≤ Nat.card Z ^ (e - d) := by
      calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
        _ ≤ Nat.card Z ^ (e - d) :=
          Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr hk)
    rw [← hrd] at hqle
    omega
  rw [hrd, hk0, pow_zero]

private theorem Ctx.outerConjNormal_eq_one_of_mem_bar_LB (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x)
    {l : Mbar M Q} (hl : l ∈ bar M Q (LB M Q B)) : Ctx.outerConjNormal hc l = 1 := by
  have hcard := Ctx.card_range_outerConjNormal_comp_eq_one hc hU
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let ψ : ↥L →* Outer (XbarMod M Q Z B) := (Ctx.outerConjNormal hc).comp L.subtype
  have hbot : ψ.range = ⊥ := (Subgroup.card_eq_one).mp hcard
  have hmem : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨⟨l, hl⟩, rfl⟩
  rw [hbot] at hmem
  simpa [ψ] using hmem

theorem Ctx.bar_LB_le_Xbar_sup_centralizer_of_psu4 (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    bar M Q (LB M Q B) ≤
      Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) := by
  intro l hl
  exact Ctx.mem_sup_centralizer_of_outerConjNormal_eq_one hc
    (Ctx.outerConjNormal_eq_one_of_mem_bar_LB hc hU hl)

private noncomputable def Ctx.xbarPreimageLB (hc : Ctx M Q Z B) : Subgroup ↥(Xbar M Q Z B) where
  carrier := {y | ∃ c ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)),
    (y : Mbar M Q) * c ∈ bar M Q (LB M Q B)}
  one_mem' := ⟨1, Subgroup.one_mem _, by simpa using (bar M Q (LB M Q B)).one_mem⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
    refine ⟨c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, ?_⟩
    have hcomm : c₁ * (y₂ : Mbar M Q) = (y₂ : Mbar M Q) * c₁ :=
      (Subgroup.mem_centralizer_iff.mp hc₁ (y₂ : Mbar M Q) y₂.2).symm
    have he : (((y₁ * y₂ : ↥(Xbar M Q Z B)) : Mbar M Q) * (c₁ * c₂)) =
        (((y₁ : Mbar M Q) * c₁) * ((y₂ : Mbar M Q) * c₂)) := by
      simp only [Subgroup.coe_mul]
      calc (y₁ : Mbar M Q) * (y₂ : Mbar M Q) * (c₁ * c₂) =
          ((y₁ : Mbar M Q) * ((y₂ : Mbar M Q) * c₁)) * c₂ := by group
        _ = ((y₁ : Mbar M Q) * (c₁ * (y₂ : Mbar M Q))) * c₂ := by rw [hcomm]
        _ = (y₁ : Mbar M Q) * c₁ * ((y₂ : Mbar M Q) * c₂) := by group
    rw [he]
    exact (bar M Q (LB M Q B)).mul_mem h₁ h₂
  inv_mem' := by
    rintro y ⟨c, hc, h⟩
    refine ⟨c⁻¹, Subgroup.inv_mem _ hc, ?_⟩
    have hcomm : c⁻¹ * (y : Mbar M Q)⁻¹ = (y : Mbar M Q)⁻¹ * c⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hc) (y : Mbar M Q)⁻¹
        ((Xbar M Q Z B).inv_mem y.2)).symm
    have he : (((y⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) * c⁻¹) =
        ((y : Mbar M Q) * c)⁻¹ := by
      simp only [Subgroup.coe_inv, mul_inv_rev]
      exact hcomm.symm
    rw [he]
    exact (bar M Q (LB M Q B)).inv_mem h

private def xbarCentralizerInXbar (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] :
    Subgroup ↥(Xbar M Q Z B) :=
  (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).comap (Xbar M Q Z B).subtype

private instance xbarCentralizerInXbar_normal (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] :
    (xbarCentralizerInXbar M Q Z B).Normal :=
  Subgroup.normal_of_le_center fun z hz => by
    change (z : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) at hz
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz (g : Mbar M Q) g.2)

private noncomputable def xbarSupQuot (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (C : Subgroup (Mbar M Q)) [hN : (C.subgroupOf (Xbar M Q Z B ⊔ C)).Normal] :
    ↥(Xbar M Q Z B ⊔ C) →*
      (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
  QuotientGroup.mk' _

private noncomputable def barLBQuotHom (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (C : Subgroup (Mbar M Q)) [hN : (C.subgroupOf (Xbar M Q Z B ⊔ C)).Normal]
    (hLle : bar M Q (LB M Q B) ≤ Xbar M Q Z B ⊔ C) :
    ↥(bar M Q (LB M Q B)) →*
      (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
  (xbarSupQuot M Q Z B C).comp (Subgroup.inclusion hLle)

private noncomputable def xbarPreimageTheta (hc : Ctx M Q Z B)
    (C : Subgroup (Mbar M Q)) [hN : (C.subgroupOf (Xbar M Q Z B ⊔ C)).Normal] :
    ↥(hc.xbarPreimageLB) →*
      (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
  (xbarSupQuot M Q Z B C).comp
    ((Subgroup.inclusion (le_sup_left : Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C)).comp
      (hc.xbarPreimageLB).subtype)

private theorem xbarPreimageTheta_ker (hc : Ctx M Q Z B)
    [hN : ((Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
      (Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))).Normal] :
    (xbarPreimageTheta hc (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))).ker =
      (xbarCentralizerInXbar M Q Z B).subgroupOf hc.xbarPreimageLB := by
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  let q : ↥(Xbar M Q Z B ⊔ C) →*
      (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarSupQuot M Q Z B C
  let θ : ↥H →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarPreimageTheta hc C
  change θ.ker = ZX.subgroupOf H
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hh
    have h2 : q (Subgroup.inclusion (le_sup_left :
        Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C) (h : ↥(Xbar M Q Z B))) = 1 := hh
    change QuotientGroup.mk' (C.subgroupOf (Xbar M Q Z B ⊔ C))
      (Subgroup.inclusion (le_sup_left :
        Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C) (h : ↥(Xbar M Q Z B))) = 1 at h2
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion (le_sup_left :
        Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C) (h : ↥(Xbar M Q Z B)))).mp h2)
  · intro hh
    have h2 : (h : ↥(Xbar M Q Z B)) ∈ ZX := hh
    change (h : Mbar M Q) ∈ C at h2
    show q (Subgroup.inclusion (le_sup_left :
        Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C) (h : ↥(Xbar M Q Z B))) = 1
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    exact h2

private theorem xbarPreimageTheta_range (hc : Ctx M Q Z B)
    [hN : ((Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
      (Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))).Normal]
    {hLle : bar M Q (LB M Q B) ≤
      Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))} :
    (xbarPreimageTheta hc (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))).range =
      (barLBQuotHom M Q Z B
        (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) hLle).range := by
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let q : ↥(Xbar M Q Z B ⊔ C) →*
      (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarSupQuot M Q Z B C
  let fL : ↥L →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    barLBQuotHom M Q Z B C hLle
  let θ : ↥H →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarPreimageTheta hc C
  change θ.range = fL.range
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    obtain ⟨c, hcC, hcL⟩ := h.2
    let cC : ↥C := ⟨c, hcC⟩
    refine ⟨⟨(h : Mbar M Q) * c, hcL⟩, ?_⟩
    simp only [fL, θ, barLBQuotHom, xbarPreimageTheta, MonoidHom.comp_apply]
    rw [show Subgroup.inclusion hLle ⟨(h : Mbar M Q) * c, hcL⟩ =
        Subgroup.inclusion (le_sup_left : Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C)
            (h : ↥(Xbar M Q Z B)) *
          Subgroup.inclusion (le_sup_right : C ≤ Xbar M Q Z B ⊔ C) cC by
      apply Subtype.ext
      rfl]
    rw [map_mul]
    have hc1 : q (Subgroup.inclusion (le_sup_right : C ≤ Xbar M Q Z B ⊔ C) cC) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr cC.2)
    rw [hc1, mul_one]
    rfl
  · rintro _ ⟨l, rfl⟩
    obtain ⟨y, hyX, c, hcC, hcL⟩ := Subgroup.mem_sup_of_normal_left.mp (hLle l.2)
    change c ∈ C at hcC
    let yX : ↥(Xbar M Q Z B) := ⟨y, hyX⟩
    let cC : ↥C := ⟨c, hcC⟩
    have hyH : yX ∈ H := by
      refine ⟨c, hcC, ?_⟩
      change (yX : Mbar M Q) * c ∈ L
      rw [show (yX : Mbar M Q) = y from rfl, hcL]
      exact l.2
    refine ⟨⟨yX, hyH⟩, ?_⟩
    simp only [fL, θ, barLBQuotHom, xbarPreimageTheta, MonoidHom.comp_apply]
    have hprod : Subgroup.inclusion hLle l =
        Subgroup.inclusion (le_sup_left : Xbar M Q Z B ≤ Xbar M Q Z B ⊔ C) yX *
          Subgroup.inclusion (le_sup_right : C ≤ Xbar M Q Z B ⊔ C) cC := by
      apply Subtype.ext
      change (l : Mbar M Q) = y * c
      exact hcL.symm
    rw [hprod, map_mul]
    have hc1 : q (Subgroup.inclusion (le_sup_right : C ≤ Xbar M Q Z B ⊔ C) cC) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr cC.2)
    rw [hc1, mul_one]
    rfl

private theorem barLBQuotHom_ker
    [hN : ((Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
      (Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))).Normal]
    {hLle : bar M Q (LB M Q B) ≤
      Xbar M Q Z B ⊔ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))} :
    (barLBQuotHom M Q Z B
      (Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) hLle).ker =
      (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B)) := by
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let fL : ↥L →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    barLBQuotHom M Q Z B C hLle
  change fL.ker = (L ⊓ C).subgroupOf L
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hl
    refine ⟨l.2, ?_⟩
    have h1 : QuotientGroup.mk' (C.subgroupOf (Xbar M Q Z B ⊔ C))
        (Subgroup.inclusion hLle l) = 1 := hl
    exact Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion hLle l)).mp h1)
  · intro hl
    have h1 : Subgroup.inclusion hLle l ∈ C.subgroupOf (Xbar M Q Z B ⊔ C) :=
      Subgroup.mem_subgroupOf.mpr hl.2
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hLle l)).mpr h1

private theorem Ctx.card_quotient_xbarPreimageLB (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    Nat.card (↥(hc.xbarPreimageLB) ⧸
      (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB)) =
    Nat.card (↥(bar M Q (LB M Q B)) ⧸
      (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B))) := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  let N : Subgroup ↥H := ZX.subgroupOf H
  have hLle : L ≤ Xbar M Q Z B ⊔ C :=
    hc.bar_LB_le_Xbar_sup_centralizer_of_psu4 hU
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  haveI : C.Normal := Subgroup.normal_centralizer
  haveI : (C.subgroupOf (Xbar M Q Z B ⊔ C)).Normal := Subgroup.normal_subgroupOf
  let fL : ↥L →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    barLBQuotHom M Q Z B C hLle
  let θ : ↥H →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarPreimageTheta hc C
  have hker : θ.ker = N := xbarPreimageTheta_ker hc
  have hrange : θ.range = fL.range := xbarPreimageTheta_range hc (hLle := hLle)
  have hkerFL : fL.ker = (L ⊓ C).subgroupOf L := barLBQuotHom_ker (hLle := hLle)
  have h1 : Nat.card (↥H ⧸ N) = Nat.card (↥H ⧸ θ.ker) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).symm.toEquiv
  have h2 : Nat.card (↥H ⧸ θ.ker) = Nat.card ↥θ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv
  have h3 : Nat.card ↥θ.range = Nat.card ↥fL.range := by rw [hrange]
  have h4 : Nat.card ↥fL.range = Nat.card (↥L ⧸ (L ⊓ C).subgroupOf L) := by
    rw [← hkerFL]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange fL).toEquiv).symm
  rw [h1, h2, h3, h4]

private theorem Ctx.commutator_xbarPreimageLB_le (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    ∀ a b : ↥(hc.xbarPreimageLB),
      ⁅a, b⁆ ∈ (xbarCentralizerInXbar M Q Z B).subgroupOf hc.xbarPreimageLB := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  have hLle : L ≤ Xbar M Q Z B ⊔ C :=
    hc.bar_LB_le_Xbar_sup_centralizer_of_psu4 hU
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  haveI : C.Normal := Subgroup.normal_centralizer
  haveI : (C.subgroupOf (Xbar M Q Z B ⊔ C)).Normal := Subgroup.normal_subgroupOf
  let fL : ↥L →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    barLBQuotHom M Q Z B C hLle
  let θ : ↥H →* (↥(Xbar M Q Z B ⊔ C) ⧸ C.subgroupOf (Xbar M Q Z B ⊔ C)) :=
    xbarPreimageTheta hc C
  haveI hLcomm : IsMulCommutative ↥L := hc.isElemAbelian_bar_LB.1
  have hRangeComm : IsMulCommutative ↥(fL.range) := Subgroup.range_isMulCommutative fL
  have hker : θ.ker = ZX.subgroupOf H := xbarPreimageTheta_ker hc
  have hrange : θ.range = fL.range := xbarPreimageTheta_range hc (hLle := hLle)
  have hRangeComm' : IsMulCommutative ↥θ.range := hrange ▸ hRangeComm
  intro a b
  have hcommθ : θ a * θ b = θ b * θ a := by
    have h := hRangeComm'.is_comm.comm ⟨θ a, ⟨a, rfl⟩⟩ ⟨θ b, ⟨b, rfl⟩⟩
    exact congrArg Subtype.val h
  have h1θ : θ ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcommθ
  have h2 : ⁅a, b⁆ ∈ θ.ker := MonoidHom.mem_ker.mpr h1θ
  rw [hker] at h2
  exact h2

private theorem Ctx.xbarPreimageLB_quotient (hc : Ctx M Q Z B) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    IsPGroup 2 (↥(hc.xbarPreimageLB) ⧸
      (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB)) ∧
    (∀ a b : ↥(hc.xbarPreimageLB),
      ⁅a, b⁆ ∈ (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB)) ∧
    Nat.card ↥(bar M Q (LB M Q B)) =
      Nat.card (↥(hc.xbarPreimageLB) ⧸
        (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB)) *
      Nat.card ↥(bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  let N : Subgroup ↥H := ZX.subgroupOf H
  haveI hLcomm : IsMulCommutative ↥L := hc.isElemAbelian_bar_LB.1
  haveI : ((L ⊓ C).subgroupOf L).Normal := Subgroup.normal_of_isMulCommutative _
  have hquot2 : IsPGroup 2 (↥H ⧸ N) := by
    have h2 : IsPGroup 2 (↥L ⧸ (L ⊓ C).subgroupOf L) :=
      hc.isPGroup_bar_LB.to_quotient ((L ⊓ C).subgroupOf L)
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    refine IsPGroup.iff_card.mpr ⟨k, ?_⟩
    rw [hc.card_quotient_xbarPreimageLB hU, hk]
  refine ⟨hquot2, hc.commutator_xbarPreimageLB_le hU, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((L ⊓ C).subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  rw [h1, ← hc.card_quotient_xbarPreimageLB hU]

private theorem Ctx.odd_card_xbarCentralizerInXbar (hc : Ctx M Q Z B) :
    Odd (Nat.card ↥(xbarCentralizerInXbar M Q Z B)) := by
  refine hc.odd_card_center_Xbar.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  intro z hz
  change (z : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) at hz
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz (g : Mbar M Q) g.2)

private theorem xbarCentralizerInXbar_le_xbarPreimageLB (hc : Ctx M Q Z B) :
    xbarCentralizerInXbar M Q Z B ≤ hc.xbarPreimageLB := by
  intro z hz
  change (z : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) at hz
  exact ⟨(z : Mbar M Q)⁻¹, Subgroup.inv_mem _ hz, by simp⟩

private theorem Ctx.exists_isPGroup_two_complement_of_xbarPreimageLB (hc : Ctx M Q Z B)
    {x : ℕ} (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    ∃ P : Subgroup ↥(hc.xbarPreimageLB), IsPGroup 2 ↥P ∧
      (∀ p q : ↥P, p * q = q * p) ∧
      (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB) ⊔ P = ⊤ ∧
      (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB) ⊓ P = ⊥ ∧
      Nat.card ↥P = Nat.card (↥(hc.xbarPreimageLB) ⧸
        (xbarCentralizerInXbar M Q Z B).subgroupOf (hc.xbarPreimageLB)) := by
  classical
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  let N : Subgroup ↥H := ZX.subgroupOf H
  have hZXleH : ZX ≤ H := xbarCentralizerInXbar_le_xbarPreimageLB hc
  obtain ⟨hquot2, hcommN, -⟩ := hc.xbarPreimageLB_quotient hU
  have hNodd : Odd (Nat.card ↥N) := by
    have hZXodd : Odd (Nat.card ↥ZX) := hc.odd_card_xbarCentralizerInXbar
    rwa [show Nat.card ↥N = Nat.card ↥ZX from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZXleH).toEquiv]
  have hcop : Nat.Coprime (Nat.card ↥N) N.index := by
    obtain ⟨k, hk⟩ := hquot2.exists_card_eq
    rw [Subgroup.index_eq_card, hk]
    exact (Nat.coprime_two_right.mpr hNodd).pow_right k
  obtain ⟨P, hP⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hcompl : IsCompl N P := hP.isCompl
  have hNcenter : N ≤ Subgroup.center ↥H := by
    intro n hn
    have hnZX : (n : ↥(Xbar M Q Z B)) ∈ ZX := Subgroup.mem_subgroupOf.mp hn
    change (n : Mbar M Q) ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) at hnZX
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    refine Subtype.ext (Subtype.ext ?_)
    simpa only [Subgroup.coe_mul] using
      Subgroup.mem_centralizer_iff.mp hnZX (g : Mbar M Q) g.1.2
  have hNnorm : N ≤ Subgroup.normalizer (P : Set ↥H) :=
    hNcenter.trans (Subgroup.center_le_normalizer (P : Set ↥H))
  have hcard_sup := card_sup_mul_card_inf_of_le_normalizer hNnorm
  have hsup : P ⊔ N = ⊤ := by rw [sup_comm]; exact hcompl.sup_eq_top
  have hinf : P ⊓ N = ⊥ := by rw [inf_comm]; exact hcompl.inf_eq_bot
  have hHcard : Nat.card ↥H = Nat.card (↥H ⧸ N) * Nat.card ↥N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hPcard : Nat.card ↥P = Nat.card (↥H ⧸ N) := by
    have h1 : Nat.card ↥H = Nat.card ↥P * Nat.card ↥N := by
      rw [← hcard_sup, hsup, hinf, Subgroup.card_bot, mul_one, Subgroup.card_top]
    have h1' : Nat.card (↥H ⧸ N) * Nat.card ↥N = Nat.card ↥P * Nat.card ↥N := by
      rw [← hHcard]
      exact h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1').symm
  have hP2 : IsPGroup 2 ↥P := by
    obtain ⟨k, hk⟩ := hquot2.exists_card_eq
    exact IsPGroup.iff_card.mpr ⟨k, hPcard.trans hk⟩
  have hPab : ∀ p q : ↥P, p * q = q * p := by
    intro p q
    have hcomm : ⁅(p : ↥H), (q : ↥H)⁆ ∈ N := hcommN (p : ↥H) (q : ↥H)
    have hmemP : ⁅(p : ↥H), (q : ↥H)⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem p.2 q.2) (P.inv_mem p.2)) (P.inv_mem q.2)
    have hbot : ⁅(p : ↥H), (q : ↥H)⁆ ∈ (⊥ : Subgroup ↥H) := by
      rw [← hcompl.inf_eq_bot]
      exact Subgroup.mem_inf.mpr ⟨hcomm, hmemP⟩
    have h1 : ⁅(p : ↥H), (q : ↥H)⁆ = 1 := Subgroup.mem_bot.mp hbot
    have h2 : (p : ↥H) * (q : ↥H) = (q : ↥H) * (p : ↥H) :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    exact Subtype.ext h2
  exact ⟨P, hP2, hPab, hcompl.sup_eq_top, hcompl.inf_eq_bot, hPcard⟩



private theorem Ctx.card_Z_pow_le_card_proj (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    {L₀ : Subgroup ↥(Xbar M Q Z B)}
    (hL0 : Nat.card ↥(bar M Q (LB M Q B)) = Nat.card L₀ *
      Nat.card ↥(bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))) :
    Nat.card Z ^ (n - 2) ≤ Nat.card L₀ := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  obtain ⟨xq, kq, hZq, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hxq : 1 ≤ xq := by
    rcases Nat.eq_zero_or_pos xq with h | h
    · rw [h, pow_zero] at hZq
      omega
    · exact h
  have hqpos : 0 < Nat.card Z := by omega
  have hCcard : Nat.card ↥(L ⊓ C) ≤ Nat.card Z :=
    card_inf_centralizer_Xbar_le hc hw hn hxq hZq ha2
  have hL0' : Nat.card ↥L = Nat.card L₀ * Nat.card ↥(L ⊓ C) := by
    simpa only [L, C] using hL0
  have hLge : Nat.card Z ^ (n - 1) ≤ Nat.card ↥L := by
    simpa only [L] using hc.card_bar_LB_ge hw (by omega)
  have hprod : Nat.card Z ^ (n - 1) ≤ Nat.card L₀ * Nat.card Z := by
    calc Nat.card Z ^ (n - 1) ≤ Nat.card ↥L := hLge
      _ = Nat.card L₀ * Nat.card ↥(L ⊓ C) := hL0'
      _ ≤ Nat.card L₀ * Nat.card Z := Nat.mul_le_mul_left _ hCcard
  have hPge : Nat.card Z ^ (n - 2) ≤ Nat.card L₀ := by
    have h1 : Nat.card Z ^ (n - 2) * Nat.card Z ≤ Nat.card L₀ * Nat.card Z := by
      rwa [← pow_succ, show n - 2 + 1 = n - 1 by omega]
    exact Nat.le_of_mul_le_mul_right h1 hqpos
  exact hPge

theorem Ctx.exists_proj_bar_LB_of_psu4 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ}
    (hU : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSU 4 2 x) :
    ∃ L₀ : Subgroup ↥(Xbar M Q Z B), IsPGroup 2 L₀ ∧
      (∀ y ∈ L₀, ∀ y' ∈ L₀, y * y' = y' * y) ∧
      (∀ l ∈ bar M Q (LB M Q B), ∃ y ∈ L₀,
        (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) ∧
      (∀ y ∈ L₀, ∃ l ∈ bar M Q (LB M Q B),
        (y : Mbar M Q)⁻¹ * l ∈ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) ∧
      Nat.card Z ^ (n - 2) ≤ Nat.card L₀ := by
  classical
  let L : Subgroup (Mbar M Q) := bar M Q (LB M Q B)
  let C : Subgroup (Mbar M Q) := Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))
  let H : Subgroup ↥(Xbar M Q Z B) := hc.xbarPreimageLB
  let ZX : Subgroup ↥(Xbar M Q Z B) := xbarCentralizerInXbar M Q Z B
  let N : Subgroup ↥H := ZX.subgroupOf H
  obtain ⟨P, hP2, hPab, hPsup, -, hPcard⟩ :=
    hc.exists_isPGroup_two_complement_of_xbarPreimageLB hU
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  obtain ⟨-, -, hcardQ⟩ := hc.xbarPreimageLB_quotient hU
  let L₀ : Subgroup ↥(Xbar M Q Z B) := P.map H.subtype
  have hL0card : Nat.card ↥L₀ = Nat.card ↥P :=
    Subgroup.card_map_of_injective H.subtype_injective
  haveI : IsMulCommutative ↥P := ⟨⟨hPab⟩⟩
  haveI hL0comm : IsMulCommutative ↥L₀ := Subgroup.map_isMulCommutative P H.subtype
  have hLle : L ≤ Xbar M Q Z B ⊔ C :=
    hc.bar_LB_le_Xbar_sup_centralizer_of_psu4 hU
  have hL0 : Nat.card (bar M Q (LB M Q B)) = Nat.card L₀ * Nat.card ↥(L ⊓ C) := by
    rw [hcardQ, ← hPcard, hL0card]
  have hL0ge : Nat.card Z ^ (n - 2) ≤ Nat.card ↥L₀ :=
    hc.card_Z_pow_le_card_proj hw hn ha2 (L₀ := L₀) (by simpa only [L, C] using hL0)
  refine ⟨L₀, ?_, ?_, ?_, ?_, hL0ge⟩
  · exact hP2.of_equiv (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective)
  · intro y hy y' hy'
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨y, hy⟩ : ↥L₀) (⟨y', hy'⟩ : ↥L₀))
  · intro l hl
    obtain ⟨y, hyX, c, hcC, hyl⟩ := Subgroup.mem_sup_of_normal_left.mp (hLle hl)
    let yX : ↥(Xbar M Q Z B) := ⟨y, hyX⟩
    have hyH : yX ∈ H := ⟨c, hcC, by simpa [yX] using hyl ▸ hl⟩
    have htop : P ⊔ N = ⊤ := by rw [sup_comm]; exact hPsup
    obtain ⟨p, hpP, z, hzN, hpz⟩ := Subgroup.mem_sup_of_normal_right.mp
      (show (⟨yX, hyH⟩ : ↥H) ∈ P ⊔ N from by rw [htop]; exact Subgroup.mem_top _)
    refine ⟨((p : ↥H) : ↥(Xbar M Q Z B)),
      Subgroup.mem_map.mpr ⟨p, hpP, rfl⟩, ?_⟩
    have hzC : ((z : ↥H) : Mbar M Q) ∈ C := by
      have hzZX : (z : ↥(Xbar M Q Z B)) ∈ ZX := Subgroup.mem_subgroupOf.mp hzN
      change (z : Mbar M Q) ∈ C at hzZX
      exact hzZX
    have hpc : ((p : ↥H) : Mbar M Q) * (z : Mbar M Q) = y := by
      have := congrArg (fun e : ↥H => ((e : ↥(Xbar M Q Z B)) : Mbar M Q)) hpz
      simpa only [Subgroup.coe_mul, yX] using this
    have hgoal : ((p : ↥H) : Mbar M Q)⁻¹ * l = (z : Mbar M Q) * c := by
      rw [← hyl, ← hpc]
      group
    rw [hgoal]
    exact C.mul_mem hzC hcC
  · intro y hy
    obtain ⟨p, hpP, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨c, hcC, hpcL⟩ := p.2
    refine ⟨((p : ↥H) : Mbar M Q) * c, hpcL, ?_⟩
    show ((p : ↥(Xbar M Q Z B)) : Mbar M Q)⁻¹ * (((p : ↥H) : Mbar M Q) * c) ∈ C
    rw [show ((p : ↥(Xbar M Q Z B)) : Mbar M Q) = ((p : ↥H) : Mbar M Q) from rfl]
    rw [inv_mul_cancel_left]
    exact hcC


private theorem map_range_sub_one_eq_of_commute {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] {T U : E ≃ₗ[K] E} (h : T * U = U * T) :
    Submodule.map (T : E →ₗ[K] E) (LinearMap.range ((U : E →ₗ[K] E) - 1)) =
      LinearMap.range ((U : E →ₗ[K] E) - 1) := by
  have hmap : Submodule.map (T : E →ₗ[K] E)
      (LinearMap.range ((U : E →ₗ[K] E) - 1)) =
      LinearMap.range (((T * U * T⁻¹ : E ≃ₗ[K] E) : E →ₗ[K] E) - 1) := by
    rw [← LinearMap.range_comp]
    have hcomp : ((T : E →ₗ[K] E).comp ((U : E →ₗ[K] E) - 1)) =
        ((((T * U * T⁻¹ : E ≃ₗ[K] E) : E →ₗ[K] E) - 1).comp (T : E →ₗ[K] E)) := by
      ext y
      simp [LinearEquiv.mul_apply]
    rw [hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr T.surjective,
      Submodule.map_top]
  rw [hmap, show T * U * T⁻¹ = U from by rw [h]; group]

private theorem Ctx.phi_comm_of_mem_centralizer {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q) (c : ↥(H0 M Z))
    (hcC : (QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)))
    (s : ↥(XbarH M Q Z B)) : φ c * φ s.1 = φ s.1 * φ c := by
  classical
  let πH0 : ↥(H0 M Z) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp
      (Subgroup.inclusion (inf_le_left : H0 M Z ≤ M))
  have hcπ : πH0 c = QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) := rfl
  have hsPre : (s.1 : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc s.1).mp s.2
  have hsX : πH0 s.1 ∈ Xbar M Q Z B := by
    change QuotientGroup.mk (⟨(s.1 : G), s.1.2.1⟩ : ↥M) ∈ Xbar M Q Z B
    exact (mem_XbarPre_iff hc s.1.2.1).mp hsPre
  have hcommMk : πH0 s.1 * πH0 c = πH0 c * πH0 s.1 :=
    Subgroup.mem_centralizer_iff.mp hcC (πH0 s.1) hsX
  let sH : ↥(H0 M Z) := s.1
  have hq : ((⁅c, sH⁆ : ↥(H0 M Z)) : G) ∈ Q := by
    have h1 : πH0 ⁅c, sH⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcommMk.symm
    have h2 : Subgroup.inclusion (inf_le_left : H0 M Z ≤ M)
        (⁅c, sH⁆ : ↥(H0 M Z)) ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hφq : φ ⁅c, sH⁆ = 1 := (φker _).mpr hq
  have h1 : ⁅φ c, φ sH⁆ = 1 := by
    rw [← map_commutatorElement φ c sH, hφq]
  exact commutatorElement_eq_one_iff_mul_comm.mp h1


private theorem cmComm_map_eq_self_of_comm {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ}
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) {T : M₀.E ≃ₗ[K] M₀.E}
    (hcomm : ∀ s : ↥(XbarH M Q Z B), T * φ s.1 = φ s.1 * T) :
    Submodule.map (T : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) =
      cmComm M Q Z B K γ M₀ φ := by
  have hle : Submodule.map (T : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) ≤
      cmComm M Q Z B K γ M₀ φ := by
    rw [cmComm, Submodule.map_iSup]
    refine iSup_le fun s => ?_
    rw [map_range_sub_one_eq_of_commute (hcomm s)]
    exact le_iSup (fun s : ↥(XbarH M Q Z B) =>
      LinearMap.range (((φ s.1 : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) s
  have hcomm_inv : ∀ s : ↥(XbarH M Q Z B), T.symm * φ s.1 = φ s.1 * T.symm := by
    intro s
    have h := hcomm s
    have hTU : T * φ s.1 * T.symm = φ s.1 := by
      rw [h]
      ext y
      simp [LinearEquiv.mul_apply]
    calc T.symm * φ s.1 = T.symm * (T * φ s.1 * T.symm) := by rw [hTU]
      _ = φ s.1 * T.symm := by
          ext y
          simp [LinearEquiv.mul_apply]
  have hle_inv : Submodule.map (T.symm : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) ≤
      cmComm M Q Z B K γ M₀ φ := by
    rw [cmComm, Submodule.map_iSup]
    refine iSup_le fun s => ?_
    rw [map_range_sub_one_eq_of_commute (hcomm_inv s)]
    exact le_iSup (fun s : ↥(XbarH M Q Z B) =>
      LinearMap.range (((φ s.1 : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1)) s
  have hge : cmComm M Q Z B K γ M₀ φ ≤
      Submodule.map (T : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) := by
    calc cmComm M Q Z B K γ M₀ φ =
        Submodule.map (T : M₀.E →ₗ[K] M₀.E)
          (Submodule.map (T.symm : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ)) := by
          rw [← Submodule.map_comp]
          have hcomp : ((T : M₀.E →ₗ[K] M₀.E).comp (T.symm : M₀.E →ₗ[K] M₀.E)) =
              (1 : M₀.E →ₗ[K] M₀.E) := by
            ext y
            simp
          rw [hcomp, show (1 : M₀.E →ₗ[K] M₀.E) = LinearMap.id from rfl, Submodule.map_id]
      _ ≤ Submodule.map (T : M₀.E →ₗ[K] M₀.E) (cmComm M Q Z B K γ M₀ φ) :=
          Submodule.map_mono hle_inv
  exact le_antisymm hle hge

theorem Ctx.exists_cmComm_restrict_of_mem_centralizer {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hc : Ctx M Q Z B) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (φker : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q) (c : ↥(H0 M Z))
    (hcC : (QuotientGroup.mk (⟨(c : G), c.2.1⟩ : ↥M) : Mbar M Q) ∈
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :
    ∃ τ : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ),
      (∀ v, (τ v : M₀.E) = φ c (v : M₀.E)) ∧
      (∀ s : ↥(XbarH M Q Z B), τ * cmCommAct hc φ s = cmCommAct hc φ s * τ) ∧
      ((c : G) * c ∈ Q → τ * τ = 1) := by
  classical
  let C : Submodule K M₀.E := cmComm M Q Z B K γ M₀ φ
  let τ : ↥C ≃ₗ[K] ↥C :=
    LinearEquiv.ofSubmodules (φ c) C C (cmComm_map_eq_self_of_comm φ
      (fun s => Ctx.phi_comm_of_mem_centralizer hc φ φker c hcC s))
  have hτapply : ∀ v : ↥C, (τ v : M₀.E) = φ c (v : M₀.E) := by
    intro v
    exact LinearEquiv.ofSubmodules_apply (φ c) (p := C) (q := C)
      (h := cmComm_map_eq_self_of_comm φ
        (fun s => Ctx.phi_comm_of_mem_centralizer hc φ φker c hcC s)) v
  refine ⟨τ, hτapply, ?_, ?_⟩
  · intro s
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    change (τ ((cmCommAct hc φ s) v) : M₀.E) =
      ((cmCommAct hc φ s) (τ v) : M₀.E)
    rw [hτapply, coe_cmCommAct, coe_cmCommAct, hτapply]
    exact congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f (v : M₀.E))
      (Ctx.phi_comm_of_mem_centralizer hc φ φker c hcC s)
  · intro hc2
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    have hcc : ((c * c : ↥(H0 M Z)) : G) ∈ Q := by simpa using hc2
    have hφ2 : φ c * φ c = 1 := by
      rw [← map_mul]
      exact (φker (c * c)).mpr hcc
    rw [LinearEquiv.mul_apply, hτapply, hτapply]
    have h2 : (φ c * φ c) (v : M₀.E) = (1 : M₀.E ≃ₗ[K] M₀.E) (v : M₀.E) :=
      congrArg (fun f : M₀.E ≃ₗ[K] M₀.E => f (v : M₀.E)) hφ2
    simpa [LinearEquiv.mul_apply] using h2


end CFSG.RankThree.GF2n.Stroth80
