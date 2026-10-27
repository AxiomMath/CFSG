module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9
public import CFSG.Quasithin.H13.VolIAutSLFive
public import CFSG.Quasithin.Background.HL42Aut
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Vol2.Ch12Sec1Swap

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def subI {V : Subgroup G} (hV : IsElemAbelian 2 V) (X : Subgroup G) :
    Subgroup (IntMod V hV) :=
  X.comap (E3.valHom hV)

namespace Sec121H9

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_subI {V X : Subgroup G} {hV : IsElemAbelian 2 V} {w : IntMod V hV} :
    w ∈ subI hV X ↔ w.val ∈ X := Iff.rfl

omit [Finite G] in
theorem card_subI {V X : Subgroup G} (hV : IsElemAbelian 2 V) (hXV : X ≤ V) :
    Nat.card (subI hV X) = Nat.card X :=
  Nat.card_congr
    { toFun := fun w => ⟨(w : IntMod V hV).val, w.2⟩
      invFun := fun x => ⟨IntMod.mk hV ⟨x, hXV x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Finite G] in
theorem pCoreOf_subgroupOf_self (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L

theorem card_autOn_L (hyp : Hyp121 G T L V V₁ V₂ n) :
    Nat.card (autOn L V) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hLV : L ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer.trans (Sec121Q.normalizer_le_of_hyp121 hyp)
  have hCL : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L :=
    le_antisymm (fun x hx => Sec121Q.inf_centralizer_le_pCoreOf_of_hyp121 hyp hV₁V hyp.norm₁
        hnat₁ ⟨hx.1, Subgroup.centralizer_le (by exact_mod_cast hV₁V) hx.2⟩)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        (Sec121Q.pCoreOf_le_centralizer_of_hyp121 hyp))
  rw [card_autOn_eq_relIndex hLV, hCL, Subgroup.relIndex, pCoreOf_subgroupOf_self]
  rfl

theorem card_mulAut_le (hyp : Hyp121 G T L V V₁ V₂ n) :
    Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ 2 * Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := hyp.iso
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
  rcases hyp.rank with rfl | rfl
  · exact CFSG.Quasithin.H.L4.card_mulAut_SL_four
  · exact VolI.autSLFiveTwo_holds

end Sec121H9

open Sec121H9 in
theorem h9Hyp_of_hyp121 [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : IsElemAbelian 2 V) :
    H9Hyp n (autI hV (Subgroup.normalizer (L : Set G))) (autI hV L) (autI hV T)
      (subI hV V₁) (subI hV V₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcV : IsMulCommutative ↥V := hV.1
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  obtain ⟨hcard₁, hcard₂, -⟩ := Sec1212.card_eq_of_hyp121 hyp
  have hconv : ∀ {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (w : IntMod V hV),
      (convI hV ⟨g, hg⟩ w).val = g * w.val * g⁻¹ := fun hg w => convI_apply_val hV ⟨_, hg⟩ w
  have hinv : ∀ {X : Subgroup G}, L ≤ Subgroup.normalizer (X : Set G) →
      autI hV L ≤ stabV (subI hV X) := by
    intro X hLX φ hφ w
    obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := (mem_autI hV).1 hφ
    rw [mem_subI, mem_subI, hconv]
    exact Subgroup.mem_normalizer_iff.mp (hLX hgL) w.val
  obtain ⟨m₀, hm₀, hm₀1⟩ := Sec121Swap.exists_swap_of_hyp121 hyp
  have hm₀V : m₀ ∈ Subgroup.normalizer (V : Set G) := hMV hm₀
  have hm₀L : convI hV ⟨m₀, hm₀V⟩ ∉ autI hV L := by
    intro h
    apply hm₀1
    refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := hinv hyp.norm₁ h (IntMod.mk hV ⟨a, hV₁V ha⟩)
    rw [mem_subI, mem_subI, hconv] at h1
    exact h1.mp ha
  have hLM : autI hV L ≤ autI hV (Subgroup.normalizer (L : Set G)) :=
    autI_mono hV Subgroup.le_normalizer
  have hindex : (autI hV L).relIndex (autI hV (Subgroup.normalizer (L : Set G))) = 2 := by
    have h1 := ((autI hV L).subgroupOf (autI hV (Subgroup.normalizer (L : Set G)))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv] at h1
    obtain ⟨φ⟩ := hyp.aut
    have hM : Nat.card (autI hV (Subgroup.normalizer (L : Set G))) ≤
        2 * Nat.card (autI hV L) := by
      have e1 : Nat.card (autI hV (Subgroup.normalizer (L : Set G))) =
          Nat.card (autOn (Subgroup.normalizer (L : Set G)) V) := rfl
      have e2 : Nat.card (autI hV L) = Nat.card (autOn L V) := rfl
      rw [e1, e2, Nat.card_congr φ.toEquiv, card_autOn_L hyp]
      exact card_mulAut_le hyp
    have hpos : 0 < Nat.card (autI hV L) := Nat.card_pos
    set k := ((autI hV L).subgroupOf (autI hV (Subgroup.normalizer (L : Set G)))).index with hk
    have hk1 : k ≠ 1 := by
      intro h
      rw [hk, Subgroup.index_eq_one] at h
      apply hm₀L
      have : (⟨_, (mem_autI hV).2 ⟨⟨m₀, hm₀V⟩, hm₀, rfl⟩⟩ :
          ↥(autI hV (Subgroup.normalizer (L : Set G)))) ∈
          (autI hV L).subgroupOf (autI hV (Subgroup.normalizer (L : Set G))) := by
        rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hk0 : k ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have : 3 * Nat.card (autI hV L) ≤ Nat.card (autI hV L) * k := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hk3
      omega
    show k = 2
    omega
  refine
    { rank := hyp.rank
      exp := fun w => IntMod.sq_eq_one w
      aut := ?_
      le := hLM
      index := hindex
      sylow_le := autI_mono hV hTL
      sylow_two := ?_
      sylow_odd := ?_
      inf := ?_
      sup := ?_
      inv₁ := hinv hyp.norm₁
      inv₂ := hinv hyp.norm₂
      card₁ := by rw [card_subI hV hV₁V, hcard₁]
      full := ?_
      faith := ?_
      swap := ?_ }
  · obtain ⟨φ⟩ := hyp.aut
    obtain ⟨e⟩ := hyp.iso
    exact ⟨φ.trans (MulAut.congr e)⟩
  · have hT2 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hyp.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hTL.trans hMV)).symm
    exact hT2.map (convI hV)
  ·
    set M := Subgroup.normalizer (L : Set G) with hMdef
    let f : ↥M →* ↥(autI hV M) :=
      { toFun := fun m => ⟨convI hV ⟨m, hMV m.2⟩, (mem_autI hV).2 ⟨⟨m, hMV m.2⟩, m.2, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          show convI hV ⟨1, _⟩ = 1
          exact map_one _
        map_mul' := fun a b => by
          apply Subtype.ext
          show convI hV ⟨a * b, _⟩ = convI hV ⟨a, _⟩ * convI hV ⟨b, _⟩
          rw [← map_mul]
          rfl }
    have hfs : Function.Surjective f := by
      rintro ⟨φ, hφ⟩
      obtain ⟨⟨g, hgN⟩, hgM, rfl⟩ := (mem_autI hV).1 hφ
      exact ⟨⟨g, hgM⟩, rfl⟩
    have hmap : (T.subgroupOf M).map f = (autI hV T).subgroupOf (autI hV M) := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨⟨m, hm⟩, hmT, he⟩
        rw [← congrArg Subtype.val he]
        exact (mem_autI hV).2 ⟨⟨m, hMV hm⟩, Subgroup.mem_subgroupOf.mp hmT, rfl⟩
      · intro h
        obtain ⟨⟨g, hgN⟩, hgT, rfl⟩ := (mem_autI hV).1 h
        exact ⟨⟨g, hTL hgT⟩, Subgroup.mem_subgroupOf.mpr hgT, rfl⟩
    have hdvd := Subgroup.index_map_dvd (T.subgroupOf M) hfs
    rw [hmap] at hdvd
    intro h2
    exact hyp.sylow.2 (h2.trans (hdvd.trans (by
      have := Subgroup.relIndex_dvd_index_of_le hTL
      exact this)))
  · rw [eq_bot_iff]
    intro w hw
    have h1 : w.val ∈ V₁ ⊓ V₂ := ⟨hw.1, hw.2⟩
    rw [hyp.inf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact IntMod.val_injective h1
  · rw [eq_top_iff]
    intro w _
    have hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm (⟨a, hV₁V ha⟩ : ↥V) ⟨b, hV₂V hb⟩)
    obtain ⟨a, ha, c, hc, hac⟩ :=
      Sec121Thm.exists_mul_of_mem_sup hcomm (hyp.sup.symm ▸ w.val_mem : w.val ∈ V₁ ⊔ V₂)
    have e : w = IntMod.mk hV ⟨a, hV₁V ha⟩ * IntMod.mk hV ⟨c, hV₂V hc⟩ :=
      IntMod.val_injective (by rw [IntMod.val_mul]; exact hac.symm)
    rw [e]
    exact Subgroup.mul_mem_sup (show IntMod.mk hV ⟨a, hV₁V ha⟩ ∈ subI hV V₁ from ha)
      (show IntMod.mk hV ⟨c, hV₂V hc⟩ ∈ subI hV V₂ from hc)
  ·
    intro φ
    let e : ↥(subI hV V₁) ≃* ↥V₁ :=
      { toFun := fun w => ⟨(w : IntMod V hV).val, w.2⟩
        invFun := fun x => ⟨IntMod.mk hV ⟨x, hV₁V x.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hφ' : (e.symm.trans φ).trans e ∈ autOn L V₁ := by
      rw [G64.BinaryNaturalSL.eq_top hnat₁]
      exact Subgroup.mem_top _
    obtain ⟨⟨l, hl⟩, hlφ⟩ := (A4.mem_autOn_iff hyp.norm₁).mp hφ'
    have hlV : l ∈ Subgroup.normalizer (V : Set G) := hMV (Subgroup.le_normalizer hl)
    refine ⟨convI hV ⟨l, hlV⟩, (mem_autI hV).2 ⟨⟨l, hlV⟩, hl, rfl⟩, fun w => ?_⟩
    apply IntMod.val_injective
    rw [hconv]
    have h1 := congrArg (fun ψ : MulAut ↥V₁ => ((ψ (e w) : ↥V₁) : G)) hlφ
    simp only [A4.actionOn_apply_coe] at h1
    rw [show ((e.symm.trans φ).trans e) (e w) = e (φ w) by simp] at h1
    exact h1
  ·
    intro φ hφ hfix
    obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := (mem_autI hV).1 hφ
    rw [convI_eq_one_iff]
    refine Sec1212.mem_centralizer_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁
      (Subgroup.le_normalizer hgL) (Sec1212.mem_centralizer_iff_conj.mpr fun a ha => ?_)
    have h1 := hfix (IntMod.mk hV ⟨a, hV₁V ha⟩) ha
    have h2 := congrArg IntMod.val h1
    rw [hconv] at h2
    exact h2
  ·
    obtain ⟨t, htT, ht1⟩ := Sec121Swap.exists_mem_not_normalizer hyp hTL
    have htV : t ∈ Subgroup.normalizer (V : Set G) := hMV (hTL htT)
    obtain ⟨h1, h2⟩ := Sec121Swap.swap_of_hyp121 hyp (hTL htT) ht1
    refine ⟨convI hV ⟨t, htV⟩, (mem_autI hV).2 ⟨⟨t, htV⟩, htT, rfl⟩, fun h => ht1 ?_, ?_⟩
    · refine Sec121Swap.mem_normalizer_of_conj_mem fun a ha => ?_
      have h3 := hinv hyp.norm₁ h (IntMod.mk hV ⟨a, hV₁V ha⟩)
      rw [mem_subI, mem_subI, hconv] at h3
      exact h3.mp ha
    · have hle : (subI hV V₁).map (convI hV ⟨t, htV⟩).toMonoidHom ≤ subI hV V₂ := by
        rintro _ ⟨w, hw, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, mem_subI, hconv]
        exact h1 _ hw
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [Subgroup.card_map_of_injective (f := (convI hV ⟨t, htV⟩).toMonoidHom)
        (convI hV ⟨t, htV⟩).injective, card_subI hV hV₁V, card_subI hV hV₂V, hcard₁, hcard₂]

end CFSG.Quasithin.H13
