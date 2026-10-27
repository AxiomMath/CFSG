module

public import CFSG.Quasithin.H13.GoldschmidtI51Index2
public import CFSG.Quasithin.H13.GoldschmidtI51Rx

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

omit [Finite G] in
theorem cj_pCoreOf_self {X : Subgroup G} {h : G} (hh : h ∈ X) :
    cj h (pCoreOf 2 X) = pCoreOf 2 X := by
  ext x
  rw [mem_cj]
  constructor
  · intro hx
    have := normalizes_pCoreOf X hh hx
    simpa [mul_assoc] using this
  · intro hx
    have := normalizes_pCoreOf X ((X).inv_mem hh) hx
    simpa [mul_assoc] using this

noncomputable def Kq (Gs : Fin 3 → Subgroup G) (x : LinesO Gs) : Subgroup ↥(QQ Gs 0) :=
  (cj ((Quotient.out x : ↥(Gs 0)) : G) (QQ Gs 1)).subgroupOf (QQ Gs 0)

theorem Kq_index (hD : IsDSystem D Gs) (x : LinesO Gs) : (Kq Gs x).index = 2 := by
  have h := Q0_relIndex hD
  have hh : ((Quotient.out x : ↥(Gs 0)) : G) ∈ Gs 0 := (Quotient.out x).2
  have h1 := relIndex_cj ((Quotient.out x : ↥(Gs 0)) : G) (QQ Gs 0 ⊓ QQ Gs 1) (QQ Gs 0)
  rw [cj_inf, cj_pCoreOf_self hh] at h1
  rw [h] at h1
  show ((cj ((Quotient.out x : ↥(Gs 0)) : G) (QQ Gs 1)).subgroupOf (QQ Gs 0)).index = 2
  have h2 : ((cj ((Quotient.out x : ↥(Gs 0)) : G) (QQ Gs 1)).subgroupOf (QQ Gs 0)).index =
      (QQ Gs 0 ⊓ cj ((Quotient.out x : ↥(Gs 0)) : G) (QQ Gs 1)).relIndex (QQ Gs 0) := by
    rw [Subgroup.inf_relIndex_left]; rfl
  rw [h2]
  exact h1

theorem Kq_inj (hD : IsDSystem D Gs) : Function.Injective (Kq Gs) := by
  intro x x' hxx
  obtain ⟨a, hxa⟩ : ∃ a : ↥(Gs 0), (a : LinesO Gs) = x := ⟨_, QuotientGroup.out_eq' x⟩
  obtain ⟨a', hxa'⟩ : ∃ a' : ↥(Gs 0), (a' : LinesO Gs) = x' := ⟨_, QuotientGroup.out_eq' x'⟩
  have hKq : ∀ (y : LinesO Gs) (b : ↥(Gs 0)), (b : LinesO Gs) = y →
      Kq Gs y = (cj (b : G) (QQ Gs 1)).subgroupOf (QQ Gs 0) := by
    intro y b hb
    have hyb : (Quotient.out y : ↥(Gs 0)) = b * ((b⁻¹ * Quotient.out y : ↥(Gs 0))) := by group
    have hP : ((b⁻¹ * Quotient.out y : ↥(Gs 0)) : G) ∈ Gs 0 ⊓ Gs 1 := by
      have := QuotientGroup.eq.1 (show (b : LinesO Gs) = ((Quotient.out y : ↥(Gs 0)) : LinesO Gs) by
        rw [hb]; exact (QuotientGroup.out_eq' y).symm)
      exact Subgroup.mem_subgroupOf.1 this
    ext n
    simp only [Kq, Subgroup.mem_subgroupOf, mem_cj]
    have hb1 := hP.2
    have hnorm : ∀ u : G, u ∈ QQ Gs 1 ↔ ((b⁻¹ * Quotient.out y : ↥(Gs 0)) : G)⁻¹ * u *
        ((b⁻¹ * Quotient.out y : ↥(Gs 0)) : G) ∈ QQ Gs 1 := by
      intro u
      constructor
      · intro hu
        simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hb1) hu
      · intro hu
        have := normalizes_pCoreOf (Gs 1) hb1 hu
        simpa [mul_assoc] using this
    have e : ((Quotient.out y : ↥(Gs 0)) : G)⁻¹ * (n : G) * ((Quotient.out y : ↥(Gs 0)) : G) =
        ((b⁻¹ * Quotient.out y : ↥(Gs 0)) : G)⁻¹ * ((b : G)⁻¹ * (n : G) * (b : G)) *
          ((b⁻¹ * Quotient.out y : ↥(Gs 0)) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, ← hnorm]
  rw [hKq x a hxa, hKq x' a' hxa'] at hxx
  have hiff : ∀ n : ↥(QQ Gs 0), (a : G)⁻¹ * (n : G) * (a : G) ∈ QQ Gs 1 ↔
      (a' : G)⁻¹ * (n : G) * (a' : G) ∈ QQ Gs 1 := by
    intro n
    have := SetLike.ext_iff.1 hxx n
    simpa [Subgroup.mem_subgroupOf, mem_cj] using this
  have hg1 : (a' : G)⁻¹ * a ∈ Gs 1 := by
    by_contra hg1
    obtain ⟨m, hm, hmc⟩ := Q01_conj_ne hD (g := ((a' : G)⁻¹ * a)⁻¹)
      ((Gs 0).inv_mem ((Gs 0).mul_mem ((Gs 0).inv_mem a'.2) a.2))
      (fun h0 => hg1 (by simpa using (Gs 1).inv_mem h0))
    have hn0 : (a' : G) * m * (a' : G)⁻¹ ∈ QQ Gs 0 := normalizes_pCoreOf (Gs 0) a'.2 hm.1
    have e0 : (a' : G)⁻¹ * ((a' : G) * m * (a' : G)⁻¹) * a' = m := by group
    have h1 := (hiff ⟨_, hn0⟩).2 (by
      show (a' : G)⁻¹ * ((a' : G) * m * (a' : G)⁻¹) * a' ∈ QQ Gs 1
      rw [e0]; exact hm.2)
    have e : (a : G)⁻¹ * ((a' : G) * m * (a' : G)⁻¹) * a =
        ((a' : G)⁻¹ * a)⁻¹ * m * ((a' : G)⁻¹ * a) := by group
    simp only at h1
    rw [e] at h1
    rw [inv_inv] at hmc
    have hq0 : ((a' : G)⁻¹ * a)⁻¹ * m * ((a' : G)⁻¹ * a) ∈ QQ Gs 0 := by
      have := normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem ((Gs 0).mul_mem ((Gs 0).inv_mem a'.2) a.2))
        hm.1
      simpa using this
    exact hmc ⟨hq0, h1⟩
  have hP : (a' : G)⁻¹ * a ∈ Gs 0 ⊓ Gs 1 :=
    ⟨(Gs 0).mul_mem ((Gs 0).inv_mem a'.2) a.2, hg1⟩
  rw [← hxa, ← hxa', QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have := (Gs 0 ⊓ Gs 1).inv_mem hP
  simpa using this

theorem Rx_mem_Q1 (hD : IsDSystem .C3 Gs) {u : G} (hu : u ∈ Rx Gs) : u ∈ QQ Gs 1 := by
  obtain ⟨s0, hs0, hs00⟩ := exists_s0 hD
  have huQ := Rx_le_Q0 hD hu
  have hfix := hu.2 ((s0 : G) : G ⧸ Gs 0) (col_oPt.2 (G1_sub_Nbd hs0))
  have h1 : ((u * s0 : G) : G ⧸ Gs 0) = ((s0 : G) : G ⧸ Gs 0) := hfix
  rw [QuotientGroup.eq] at h1
  have h2 : s0⁻¹ * u * s0 ∈ Gs 0 := by
    have := (Gs 0).inv_mem h1
    simpa [mul_assoc] using this
  exact (fix_iff hD hs0 hs00 huQ).1 h2

theorem card_Q0_ge (hD : IsDSystem .C3 Gs) : 32 ≤ Nat.card ↥(QQ Gs 0) := by
  have : Fintype (LinesO Gs) := Fintype.ofFinite _
  have h15 : Fintype.card (LinesO Gs) = 15 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact (gqLoc hD).idx01
  have hX := card_index_two (Kq Gs) (Kq_inj hD) (Kq_index hD)
  rw [h15] at hX
  obtain ⟨r, hr, hr1⟩ := Rx_ne hD
  have hrmem : ∀ x : LinesO Gs, (⟨r, Rx_le_Q0 hD hr⟩ : ↥(QQ Gs 0)) ∈ Kq Gs x := by
    intro x
    have hh : ((Quotient.out x : ↥(Gs 0)) : G) ∈ Gs 0 := (Quotient.out x).2
    have hconj := Rx_conj ((Gs 0).inv_mem hh) hr
    rw [inv_inv] at hconj
    have := Rx_mem_Q1 hD hconj
    simp only [Kq, Subgroup.mem_subgroupOf, mem_cj]
    exact this
  have hnt : Nontrivial ↥(⨅ x, Kq Gs x) :=
    nontrivial_of_ne ⟨⟨r, Rx_le_Q0 hD hr⟩, Subgroup.mem_iInf.2 hrmem⟩ 1 (fun h => hr1 (by
      have := congrArg (fun y : ↥(⨅ x, Kq Gs x) => ((y : ↥(QQ Gs 0)) : G)) h
      simpa using this))
  have h2 : 2 ≤ Nat.card ↥(⨅ x, Kq Gs x) := Finite.one_lt_card_iff_nontrivial.2 hnt
  omega

theorem card_G_ge (hD : IsDSystem .C3 Gs) : 725760 ≤ Nat.card G := by
  obtain ⟨b, o, ⟨M⟩⟩ := model0_bo hD
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M.ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange M.ψ).toEquiv, M.range] at h1
  have hR : 360 ≤ Nat.card ↥(sgR b) := by
    have hle : A6g ≤ sgR b := by
      cases b <;> simp [sgR]
    have := Subgroup.card_le_of_le hle
    rwa [card_A6g] at this
  have hker : Nat.card M.ψ.ker = Nat.card ↥(QQ Gs 0) := by
    rw [M.ker]
    exact (Subgroup.card_map_of_injective (Gs 0).subtype_injective).symm
  have hQ := card_Q0_ge hD
  have hG := Subgroup.card_eq_card_quotient_mul_card_subgroup (Gs 0)
  rw [card_Omega hD, h1, hker] at hG
  rw [hG]
  nlinarith

end CFSG.Quasithin.H13.I51
