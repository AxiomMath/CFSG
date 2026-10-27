module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveStruct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem UOf_ne_NOf (h : Hyp612Sym n M V g) : UOf M V g ≠ NOf M V g := by
  intro hUN
  have hUVg : UOf M V g ≤ conjSubgroup V g := by
    rw [hUN, h.NOf_eq_inf]
    exact inf_le_right
  have hcent : conjSubgroup V g ≤ centralizer ((UOf M V g : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (elemAbelian_conj h).comm (hUVg hu) hw
  have hle : conjSubgroup V g ≤ V := fun w hw => h.centralizer_le' ⟨hw, hcent hw⟩
  have heq : conjSubgroup V g = V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [E3.card_conjSubgroup])
  apply h.not_V_le_conjM
  have h1 := h.conjV_le_conjM
  rwa [heq] at h1

theorem BOf_ne_NOf (h : Hyp612Sym n M V g) : BOf M V g ≠ NOf M V g := by
  have h1 := (swap h).UOf_ne_NOf
  rwa [UOf_swap, NOf_swap] at h1

theorem UOf_ne_BOf (h : Hyp612Sym n M V g) : UOf M V g ≠ BOf M V g := by
  intro hUB
  apply h.UOf_ne_NOf
  rw [NOf, ← hUB, inf_idem]

theorem NOf_lt_UOf (h : Hyp612Sym n M V g) : NOf M V g < UOf M V g :=
  lt_of_le_of_ne inf_le_left (Ne.symm h.UOf_ne_NOf)

theorem NOf_lt_BOf (h : Hyp612Sym n M V g) : NOf M V g < BOf M V g :=
  lt_of_le_of_ne inf_le_right (Ne.symm h.BOf_ne_NOf)

theorem BOf_le_normalizer_UOf (h : Hyp612Sym n M V g) :
    BOf M V g ≤ normalizer ((UOf M V g : Subgroup G) : Set G) := by
  have hconj_mem : ∀ b ∈ BOf M V g, ∀ u ∈ UOf M V g, b * u * b⁻¹ ∈ UOf M V g := by
    intro b hb u hu
    have hN : ⁅u, b⁆ ∈ NOf M V g := commutator_mem_N h hu hb
    have hcU : ⁅b, u⁆ ∈ UOf M V g := by
      have h1 : ⁅u, b⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem hN
      have h2 : ⁅u, b⁆⁻¹ ∈ UOf M V g := by
        have := h1
        rw [NOf, Subgroup.mem_inf] at this
        exact this.1
      rwa [commutatorElement_inv u b] at h2
    have hbub : b * u * b⁻¹ = ⁅b, u⁆ * u := by rw [commutatorElement_def]; group
    rw [hbub]
    exact (UOf M V g).mul_mem hcU hu
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact hconj_mem b hb u
  · intro hbu
    have hb' : b⁻¹ ∈ BOf M V g := (BOf M V g).inv_mem hb
    have hmem : b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ ∈ UOf M V g :=
      hconj_mem b⁻¹ hb' (b * u * b⁻¹) hbu
    rwa [show b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u by group] at hmem

theorem coe_KOf_eq_BOf_mul_UOf (h : Hyp612Sym n M V g) :
    ((KOf M V g : Subgroup G) : Set G) = (BOf M V g : Set G) * (UOf M V g : Set G) := by
  rw [KOf, sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right (BOf M V g) (UOf M V g)
    h.BOf_le_normalizer_UOf

theorem KOf_le_M (h : Hyp612Sym n M V g) : KOf M V g ≤ M :=
  sup_le (inf_le_left.trans h.le_M) inf_le_right

theorem card_BOf_le_card_UOf (h : Hyp612Sym n M V g) :
    Nat.card (BOf M V g) ≤ Nat.card (UOf M V g) := by
  classical
  have hex : ∃ v : G, v ∈ V ∧ v ∉ UOf M V g := by
    by_contra hc
    have hle : V ≤ UOf M V g := by
      intro x hx
      by_contra hxU
      exact hc ⟨x, hx, hxU⟩
    exact h.not_V_le_conjM (hle.trans inf_le_right)
  obtain ⟨v, hvV, hvU⟩ := hex
  haveI hcomm : IsMulCommutative ↥(UOf M V g) :=
    (h.elemAbelian.mono (inf_le_left : UOf M V g ≤ V)).1
  let F : ↥(BOf M V g) →* (↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g) :=
    MonoidHom.mk' (fun b => ((⟨⁅v, (b : G)⁆, commutator_mem_U h b.2 hvV⟩ :
      ↥(UOf M V g)) : (↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g))) (by
      intro x y
      have hn : ⁅(x : G), ⁅v, (y : G)⁆⁆ ∈ NOf M V g := by
        have h1 : ⁅⁅v, (y : G)⁆, (x : G)⁆ ∈ NOf M V g :=
          commutator_mem_N h (u := ⁅v, (y : G)⁆) (b := (x : G))
            (commutator_mem_U h y.2 hvV) x.2
        have h2 : ⁅⁅v, (y : G)⁆, (x : G)⁆⁻¹ ∈ NOf M V g := (NOf M V g).inv_mem h1
        rwa [commutatorElement_inv] at h2
      have hAL : ⁅v, (x : G)⁆ ∈ LOf V g := by
        rw [LOf]
        exact Subgroup.mem_sup_left (commutator_mem_U h x.2 hvV).1
      have hcentral : ⁅v, (x : G)⁆ * ⁅(x : G), ⁅v, (y : G)⁆⁆ * (⁅v, (x : G)⁆)⁻¹ =
          ⁅(x : G), ⁅v, (y : G)⁆⁆ := by
        rw [← mul_comm_of_mem_NOf h hn hAL]
        group
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_div, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_mk]
      have hdiv : ⁅v, (x : G) * (y : G)⁆ / (⁅v, (x : G)⁆ * ⁅v, (y : G)⁆) =
          ⁅v, (x : G)⁆ * ⁅(x : G), ⁅v, (y : G)⁆⁆ * (⁅v, (x : G)⁆)⁻¹ := by
        rw [div_eq_mul_inv, commutatorElement_mul_right_eq_mul_conj]
        calc ⁅v, (x : G)⁆ * (x : G) * ⁅v, (y : G)⁆ * (x : G)⁻¹ *
              (⁅v, (x : G)⁆ * ⁅v, (y : G)⁆)⁻¹
            = ⁅v, (x : G)⁆ * (x : G) * ⁅v, (y : G)⁆ * (x : G)⁻¹ *
                ((⁅v, (y : G)⁆)⁻¹ * (⁅v, (x : G)⁆)⁻¹) := by rw [mul_inv_rev]
          _ = ⁅v, (x : G)⁆ * ((x : G) * ⁅v, (y : G)⁆ * (x : G)⁻¹ *
                (⁅v, (y : G)⁆)⁻¹) * (⁅v, (x : G)⁆)⁻¹ := by group
          _ = ⁅v, (x : G)⁆ * ⁅(x : G), ⁅v, (y : G)⁆⁆ * (⁅v, (x : G)⁆)⁻¹ := by
                rw [← commutatorElement_def]
      rw [hdiv, hcentral]
      exact hn)
  have hker : F.ker = (NOf M V g).subgroupOf (BOf M V g) := by
    ext b
    have hFb : F b = ((⟨⁅v, (b : G)⁆, commutator_mem_U h b.2 hvV⟩ :
        ↥(UOf M V g)) : (↥(UOf M V g)) ⧸
        (NOf M V g).subgroupOf (UOf M V g)) := rfl
    rw [MonoidHom.mem_ker, hFb, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hb
      have hbN : ⁅(b : G), v⁆ ∈ NOf M V g := by
        have h1 := (NOf M V g).inv_mem hb
        rwa [commutatorElement_inv] at h1
      have hbK : (b : G) ∈ KOf M V g := Subgroup.mem_sup_right b.2
      have hbU : (b : G) ∈ UOf M V g :=
        h.mem_UOf_of_commutator_mem_N hvV hvU hbK hbN
      rw [NOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hbU, b.2⟩
    · intro hb
      have hbV : (b : G) ∈ V := by
        have h1 : (b : G) ∈ NOf M V g := hb
        rw [h.NOf_eq_inf, Subgroup.mem_inf] at h1
        exact h1.1
      have hbv : (⟨⁅v, (b : G)⁆, commutator_mem_U h b.2 hvV⟩ : ↥(UOf M V g)) = 1 :=
        Subtype.ext (commutatorElement_eq_one_iff_mul_comm.2 (h.elemAbelian.comm hvV hbV))
      rw [hbv]
      exact (NOf M V g).one_mem
  have hcardB := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((NOf M V g).subgroupOf (BOf M V g))
  have hcardU := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((NOf M V g).subgroupOf (UOf M V g))
  have hNB : Nat.card ((NOf M V g).subgroupOf (BOf M V g)) = Nat.card (NOf M V g) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : NOf M V g ≤ BOf M V g)).toEquiv
  have hNU : Nat.card ((NOf M V g).subgroupOf (UOf M V g)) = Nat.card (NOf M V g) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : NOf M V g ≤ UOf M V g)).toEquiv
  have hquotB : Nat.card ((↥(BOf M V g)) ⧸ (NOf M V g).subgroupOf (BOf M V g)) =
      Nat.card F.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange F).toEquiv
  have hle : Nat.card ((↥(BOf M V g)) ⧸ (NOf M V g).subgroupOf (BOf M V g)) ≤
      Nat.card ((↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g)) := by
    rw [hquotB]
    have h1 : Nat.card F.range ≤ Nat.card (⊤ : Subgroup
        ((↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g))) :=
      Subgroup.card_le_of_le le_top
    rwa [Subgroup.card_top] at h1
  calc Nat.card (BOf M V g)
      = Nat.card ((↥(BOf M V g)) ⧸ (NOf M V g).subgroupOf (BOf M V g)) *
          Nat.card ((NOf M V g).subgroupOf (BOf M V g)) := hcardB
    _ = Nat.card ((↥(BOf M V g)) ⧸ (NOf M V g).subgroupOf (BOf M V g)) *
          Nat.card (NOf M V g) := by rw [hNB]
    _ ≤ Nat.card ((↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g)) *
          Nat.card (NOf M V g) := Nat.mul_le_mul_right _ hle
    _ = Nat.card ((↥(UOf M V g)) ⧸ (NOf M V g).subgroupOf (UOf M V g)) *
          Nat.card ((NOf M V g).subgroupOf (UOf M V g)) := by rw [hNU]
    _ = Nat.card (UOf M V g) := hcardU.symm

theorem card_UOf_eq_card_BOf (h : Hyp612Sym n M V g) :
    Nat.card (UOf M V g) = Nat.card (BOf M V g) := by
  have h1 := h.card_BOf_le_card_UOf
  have h2 := (swap h).card_BOf_le_card_UOf
  rw [UOf_swap, BOf_swap] at h2
  exact le_antisymm h2 h1

theorem mQuot_conjV_BOf (h : Hyp612Sym n M V g) :
    E3.mQuot (conjSubgroup V g) (BOf M V g) = E3.mQuot V (UOf M V g) := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  have hVg : IsPGroup 2 (conjSubgroup V g) := IsElemAbelian.isPGroup (elemAbelian_conj h)
  have hU : UOf M V g ≤ V := inf_le_left
  have hB : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have h1 := E3.card_eq_two_pow_mul hV hU
  have h2 := E3.card_eq_two_pow_mul hVg hB
  rw [E3.card_conjSubgroup, h1, h.card_UOf_eq_card_BOf] at h2
  have hpos : 0 < Nat.card (BOf M V g) := Nat.card_pos
  have := Nat.eq_of_mul_eq_mul_right hpos h2
  exact (Nat.pow_right_injective (le_refl 2) this).symm

theorem one_le_mQuot_UOf (h : Hyp612Sym n M V g) : 1 ≤ E3.mQuot V (UOf M V g) := by
  have hV : IsPGroup 2 V := IsElemAbelian.isPGroup h.elemAbelian
  by_contra hlt
  have h0 : E3.mQuot V (UOf M V g) = 0 := by omega
  have := (E3.mQuot_eq_zero_iff hV (inf_le_left : UOf M V g ≤ V)).1 h0
  exact h.not_V_le_conjM (by rw [← this]; exact inf_le_right)

theorem one_le (h : Hyp612Sym n M V g) : 1 ≤ n :=
  (one_le_mQuot_UOf h).trans h.mQuot_U_le

theorem normalizer_le_of_mQuot_le (h : Hyp612Sym n M V g) {x : G} {Y : Subgroup G}
    (hYX : Y ≤ conjSubgroup V x) (hm : E3.mQuot (conjSubgroup V x) Y ≤ n) :
    normalizer (Y : Set G) ≤ normalizer (conjSubgroup V x : Set G) := by
  by_contra hN
  have hnorm : normalizer (conjSubgroup V x : Set G) = conjSubgroup M x := by
    rw [← conjSubgroup_normalizer, h.normalizer_eq]
  rw [hnorm] at hN
  have h1 := rStarMV_le hYX hN
  rw [rStarMV_conjSubgroup] at h1
  have h2 : ((E3.mQuot (conjSubgroup V x) Y : ℕ) : ℕ∞) ≤ n := by exact_mod_cast hm
  exact absurd h.lt_rStar (not_lt.2 (h1.trans h2))

end Hyp612Sym

namespace Hyp612

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem two_le_mQuot_UOf (h : Hyp612 n M V g) : 2 ≤ E3.mQuot V (UOf M V g) := by
  by_contra hlt
  have h1 : E3.mQuot V (UOf M V g) ≤ 1 := by omega
  have h2 : E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ 1 := by
    rw [Hyp612Sym.mQuot_conjV_BOf h.toHyp612H3.toHyp612Sym]
    exact h1
  apply h.not_inCalO1
  refine ⟨⟨h.not_conjV_le_M, ?_, fun hh => absurd rfl hh⟩,
    ⟨h.not_V_le_conjM, ?_, fun hh => absurd rfl hh⟩⟩
  · unfold E3.mQuot at h1 ⊢
    unfold UOf at h1
    rwa [Subgroup.inf_relIndex_left] at h1
  · unfold E3.mQuot at h2 ⊢
    unfold BOf at h2
    rwa [Subgroup.inf_relIndex_left] at h2

end Hyp612

end CFSG.LocalAnalysis.WeakClosure81
