module

public import CFSG.Quasithin.MS93.S5A55SpC

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F] [CharP F 2]

theorem exists_lam_surj [Fintype F] [DecidableEq F] (W : Finset (F × F)) (hW0 : (0 : F × F) ∈ W)
    (hWadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W) (hWc : Fintype.card F ≤ W.card) :
    ∃ ν : F, ∀ s : F, ∃ w ∈ W, w.1 + ν ^ 2 * w.2 = s := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_contra hbad
  push Not at hbad
  set q := Fintype.card F with hq
  have hadd : ∀ (ν : F) (x y : F × F),
      (x + y).1 + ν ^ 2 * (x + y).2 = (x.1 + ν ^ 2 * x.2) + (y.1 + ν ^ 2 * y.2) := by
    intro ν x y
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have step1 : ∀ ν : F, 2 * W.card ≤ q * (W.filter (fun w => w.1 + ν ^ 2 * w.2 = 0)).card := by
    intro ν
    obtain ⟨s₀, hs₀⟩ := hbad ν
    set K := W.filter (fun w => w.1 + ν ^ 2 * w.2 = 0) with hK
    set I := W.image (fun w => w.1 + ν ^ 2 * w.2) with hI
    have ha : W.card ≤ K.card * I.card := by
      refine Finset.card_le_mul_card_image W K.card (fun b hb => ?_)
      obtain ⟨wb, hwb, rfl⟩ := Finset.mem_image.1 hb
      refine Finset.card_le_card_of_injOn (fun w => w + wb) (fun w hw => ?_)
        (fun x _ y _ h => add_right_cancel h)
      obtain ⟨hwW, hwe⟩ := Finset.mem_filter.1 hw
      refine Finset.mem_filter.2 ⟨hWadd _ hwW _ hwb, ?_⟩
      rw [hadd, hwe]
      linear_combination (wb.1 + ν ^ 2 * wb.2) * h2
    have hIadd : ∀ x ∈ I, ∀ y ∈ I, x + y ∈ I := by
      intro x hx y hy
      obtain ⟨wx, hwx, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨wy, hwy, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_image.2 ⟨wx + wy, hWadd _ hwx _ hwy, hadd ν wx wy⟩
    have hb : 2 * I.card ≤ q := by
      have hdisj : Disjoint I (I.image (· + s₀)) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
        have hs : s₀ ∈ I := by
          have := hIadd _ hx _ hy
          convert this using 1
          linear_combination (-y) * h2
        obtain ⟨w, hw, hws⟩ := Finset.mem_image.1 hs
        exact hs₀ w hw hws
      have hcard : (I.image (· + s₀)).card = I.card :=
        Finset.card_image_of_injective _ (add_left_injective s₀)
      have hu := Finset.card_union_of_disjoint hdisj
      have hle : (I ∪ I.image (· + s₀)).card ≤ q := Finset.card_le_univ _
      omega
    calc 2 * W.card ≤ 2 * (K.card * I.card) := Nat.mul_le_mul_left _ ha
      _ = K.card * (2 * I.card) := by ring
      _ ≤ K.card * q := Nat.mul_le_mul_left _ hb
      _ = q * K.card := mul_comm _ _
  have step2 : ∑ ν : F, (W.filter (fun w => w.1 + ν ^ 2 * w.2 = 0)).card ≤ q + (W.card - 1) := by
    have e : ∑ ν : F, (W.filter (fun w => w.1 + ν ^ 2 * w.2 = 0)).card =
        ∑ w ∈ W, (Finset.univ.filter (fun ν : F => w.1 + ν ^ 2 * w.2 = 0)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [e, ← Finset.add_sum_erase W _ hW0]
    refine Nat.add_le_add ?_ ?_
    · exact Finset.card_le_univ _
    · calc ∑ w ∈ W.erase 0, (Finset.univ.filter (fun ν : F => w.1 + ν ^ 2 * w.2 = 0)).card
          ≤ ∑ _w ∈ W.erase 0, 1 := by
            refine Finset.sum_le_sum fun w hw => Finset.card_le_one.2 fun ν hν μ hμ => ?_
            have hw0 := Finset.ne_of_mem_erase hw
            have e1 := (Finset.mem_filter.1 hν).2
            have e2 := (Finset.mem_filter.1 hμ).2
            by_cases hd : w.2 = 0
            · exfalso
              rw [hd, mul_zero, add_zero] at e1
              exact hw0 (Prod.ext e1 hd)
            · refine eq_of_sq_eq ?_
              have : (ν ^ 2 - μ ^ 2) * w.2 = 0 := by linear_combination e1 - e2
              exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
        _ = W.card - 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hW0]
  have h3 : ∑ _ν : F, 2 * W.card ≤ ∑ ν : F, q * (W.filter (fun w => w.1 + ν ^ 2 * w.2 = 0)).card :=
    Finset.sum_le_sum fun ν _ => step1 ν
  rw [Finset.sum_const, Finset.card_univ, ← Finset.mul_sum, smul_eq_mul] at h3
  have hq0 : 0 < q := Fintype.card_pos
  have h4 : 2 * W.card ≤ q + (W.card - 1) :=
    (Nat.le_of_mul_le_mul_left h3 hq0).trans step2
  have hW1 : 1 ≤ W.card := Finset.card_pos.2 ⟨0, hW0⟩
  omega

variable [Finite F]

theorem exists_gv_of_le_Q₁ (hq : ∃ t : F, t ≠ 0 ∧ t ≠ 1) {Z : Subgroup (Sp4 F)} (hZ : Z ≤ Q₁ F)
    (hZc : Nat.card F ^ 2 ≤ Nat.card Z) :
    ∃ ν : F, (∀ s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
        mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s) ∧
      ∃ z ∈ Z, z ∈ qPoint (F ∙ gv ν) ∧ z ∉ xPoint (F ∙ gv ν) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  let ψ : Z → F × F := fun z =>
    (mat (z : Sp4 F) (.inl 0) (.inr 0), mat (z : Sp4 F) (.inl 1) (.inr 1))
  by_cases ha : ∃ z ∈ Z, mat z (.inl 0) (.inr 0) = 0 ∧ mat z (.inl 1) (.inr 1) = 0 ∧ z ≠ 1
  · obtain ⟨z, hzZ, hzb, hzd, hz1⟩ := ha
    have hzQ := hZ hzZ
    have : Fintype Z := Fintype.ofFinite Z
    set W := (Finset.univ : Finset Z).image ψ with hW
    have hW0 : (0 : F × F) ∈ W := Finset.mem_image.2 ⟨⟨1, one_mem _⟩, Finset.mem_univ _, by
      simp [ψ, entry_one]⟩
    have hWadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W := by
      intro x hx y hy
      obtain ⟨zx, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨zy, -, rfl⟩ := Finset.mem_image.1 hy
      refine Finset.mem_image.2 ⟨zx * zy, Finset.mem_univ _, ?_⟩
      simp only [ψ, Subgroup.coe_mul, Prod.mk_add_mk]
      rw [entry_mul_of_mem_Q₁ (hZ zx.2) (hZ zy.2), entry_mul_of_mem_Q₁ (hZ zx.2) (hZ zy.2)]
    have hWc : Fintype.card F ≤ W.card := by
      have hinj : Function.Injective fun z : Z => ((⟨ψ z, Finset.mem_image.2
          ⟨z, Finset.mem_univ _, rfl⟩⟩ : W), mat (z : Sp4 F) (.inl 0) (.inr 1)) := by
        intro x y hxy
        simp only [Prod.mk.injEq, Subtype.mk.injEq, ψ] at hxy
        exact Subtype.ext (eq_of_mem_Q₁ (hZ x.2) (hZ y.2) hxy.1.1 hxy.2 hxy.1.2)
      have h := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := W), Fintype.card_coe] at h
      rw [← Nat.card_eq_fintype_card]
      have : Nat.card F ^ 2 ≤ W.card * Nat.card F := hZc.trans h
      rw [sq] at this
      exact Nat.le_of_mul_le_mul_right this (by omega)
    obtain ⟨ν, hν⟩ := exists_lam_surj W hW0 hWadd hWc
    refine ⟨ν, fun s => ?_, z, hzZ, mem_qPoint_gv_of hzQ hzb hzd ν, fun hx =>
      hz1 (eq_one_of_mem_xPoint_gv hzQ hzb hzd hx)⟩
    obtain ⟨w, hw, hws⟩ := hν s
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨y, y.2, hZ y.2, hws⟩
  · push Not at ha
    have hinj : Function.Injective ψ := by
      intro x y hxy
      have h1 := congrArg Prod.fst hxy
      have h2 := congrArg Prod.snd hxy
      simp only [ψ] at h1 h2
      have hkZ : (x : Sp4 F) * (y : Sp4 F)⁻¹ ∈ Z := mul_mem x.2 (inv_mem y.2)
      have hb : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 0) (.inr 0) = 0 := by
        rw [entry_mul_inv_of_mem_Q₁ (hZ x.2) (hZ y.2), h1, sub_self]
      have hd : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 1) (.inr 1) = 0 := by
        rw [entry_mul_inv_of_mem_Q₁ (hZ x.2) (hZ y.2), h2, sub_self]
      exact Subtype.ext (mul_inv_eq_one.1 (ha _ hkZ hb hd))
    have hc2 : Nat.card Z = Nat.card F ^ 2 := le_antisymm (by
      have := Nat.card_le_card_of_injective _ hinj
      rwa [Nat.card_prod, ← sq] at this) hZc
    have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hc2, sq])
    have hcov : ∀ ν s : F, ∃ y ∈ Z, y ∈ Q₁ F ∧
        mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := by
      intro ν s
      obtain ⟨⟨y, hyZ⟩, hy⟩ := hbij.2 (s, 0)
      simp only [ψ, Prod.mk.injEq] at hy
      exact ⟨y, hyZ, hZ hyZ, by rw [hy.1, hy.2, mul_zero, add_zero]⟩
    by_contra hall
    push Not at hall
    have hX : ∀ ν : F, (∀ z ∈ Z, z ∈ qPoint (F ∙ gv ν) → z ∈ xPoint (F ∙ gv ν)) →
        xPoint (F ∙ gv ν) ≤ Z := by
      intro ν hν g hg
      obtain ⟨s, rfl⟩ := (mem_xPoint_span (gv_ne_zero ν)).1 hg
      obtain ⟨⟨k, hkZ⟩, hk⟩ := hbij.2 (s * ν ^ 2, s)
      simp only [ψ, Prod.mk.injEq] at hk
      have hkQ := hZ hkZ
      have hkq : k ∈ qPoint (F ∙ gv ν) := (mem_qPoint_gv_iff hkQ ν).2 (by rw [hk.1, hk.2]; ring)
      have hkx := (mem_xPoint_gv_iff hkQ ν).1 (hν k hkZ hkq)
      obtain ⟨e0, e1, e2⟩ := entry_transv_gv ν s
      have : k = transv (gv ν) s := eq_of_mem_Q₁ hkQ (transv_gv_mem_Q₁ ν s)
        (by rw [hk.1, e0]) (by rw [hkx.2, hk.2, e1]; ring) (by rw [hk.2, e2])
      rw [← this]
      exact hkZ
    obtain ⟨t, ht0, ht1⟩ := hq
    have hall' : ∀ ν : F, ∀ z ∈ Z, z ∈ qPoint (F ∙ gv ν) → z ∈ xPoint (F ∙ gv ν) :=
      fun ν z hz hzq => hall ν (hcov ν) z hz hzq
    obtain ⟨hmq, hmx⟩ := transv_mul_transv_gv (zero_ne_one (α := F)) (Ne.symm ht0) (Ne.symm ht1)
    exact hmx (hall' t _ (mul_mem (hX 0 (hall' 0) (transv_mem_xPoint _ _))
      (hX 1 (hall' 1) (transv_mem_xPoint _ _))) hmq)

end CFSG.Quasithin.MS93.S5
