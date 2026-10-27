module

public import CFSG.Quasithin.Background.S1549DL3M
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Background.FFC6B

public section

namespace CFSG.Quasithin

namespace S1549D

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.B5 CFSG.Open CFSG.LieType.BorelTits

theorem sl3_card_ne_360 {q : ℕ} : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 360 := by
  intro h
  have hq : q ≤ 4 := by
    by_contra hq
    push Not at hq
    have h1 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 5 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 5 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4
  interval_cases q <;> norm_num at h

theorem sp4_card_ne_360 {q : ℕ} : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≠ 360 := by
  intro h
  have hq : q ≤ 2 := by
    by_contra hq
    push Not at hq
    have h1 : 3 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 3 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4
  interval_cases q <;> norm_num at h

section Excl

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_sl3_360 (hc : Nat.card ↥L = 360) {n : ℕ} (h : BinaryNaturalSL L U Z 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, card_statedSL_three1527d] at h1
  exact sl3_card_ne_360 h1.symm

theorem not_sp4_360 (hc : Nat.card ↥L = 360) {n : ℕ} (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp] at h1
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at h1
  exact sp4_card_ne_360 (q := Nat.card F) (by simpa using h1.symm)

theorem not_sl_two_360 (hc : Nat.card ↥L = 360) {d : ℕ} (hd : d = 4 ∨ d = 5)
    {π : ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) →* ↥L}
    (hπ : (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2))).RealizesVia L U Z π) : False := by
  have h1 := card_eq_of_nat_realizes1527d hπ
  rw [hc] at h1
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at h1
    omega
  · rw [card_statedSL_five_zmod1527d] at h1
    omega

theorem not_extSq_360 (hc : Nat.card ↥L = 360) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (h : SLExteriorTwo L U Z d) : False := by
  obtain ⟨π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL d (ZMod 2)) :=
    (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
  rw [hc] at hcard
  rcases hd with rfl | rfl
  · rw [card_statedSL_four_zmod1527d] at hcard
    omega
  · rw [card_statedSL_five_zmod1527d] at hcard
    omega

end Excl

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem a6_irrPlus (hB51 : AsB51) (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hB : B51Hyp G L) (hc : Nat.card ↥L = 360) : commV L ∈ IrrPlus L ⊤ := by
  obtain ⟨hp1, -⟩ := hB51 V hV G L hB
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · exact hi.1
  · exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -, -⟩ := hii
    have h1 := card_eq_of_nat_realizes1527d (hreal 0)
    rw [hc, card_statedSL_three1527d] at h1
    exact sl3_card_ne_360 h1.symm
  · exfalso
    obtain ⟨hn, π, U₁, U₂, -, hreal, -⟩ := hiii.2
    exact not_sl_two_360 hc hn hreal
  · exfalso
    obtain ⟨-, n, hn, k, hk, -, hdir⟩ := hiv
    obtain ⟨I, π, -, -, -, hreal⟩ := hdir
    exact not_sl_two_360 hc hn (hreal ⟨0, hk⟩)

theorem a6_section_dichotomy (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1) {X K T Ab : Subgroup (MulAut V)}
    (h : B51Hyp X K) (hU : commV K ∈ IrrPlus K ⊤) (hT : IsSylowTwoOf T X)
    (hAb : IsFFStarOffender X Ab) (hAbT : Ab ≤ T) {C : Subgroup V} (hC : C = fixV K ⊓ commV K)
    (hc : Nat.card ↥K = 360) :
    (1 : WithTop ℚ) ≤ qOf (autSec (K ⊔ T) (commV K) C) ∨
      (BinaryNaturalSp4 (autSec (K ⊔ T) (commV K) C) ⊤ ⊥ 1 ∧
        autSec (K ⊔ T) (commV K) C = ffJ (autSec (K ⊔ T) (commV K) C) ∧
        autSec K (commV K) C = ⁅autSec (K ⊔ T) (commV K) C, autSec (K ⊔ T) (commV K) C⁆ ∧
        Nonempty (↥(autSec (K ⊔ T) (commV K) C) ≃* Equiv.Perm (Fin 6))) := by
  obtain ⟨B, hBA, hB, hconcl⟩ := FFC.B59.b42_offender hB42 hV h hU hT hAb hAbT hC
  have hb4 := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  have hLG := le_G h
  have hLU : K ≤ stabSub (commV K) := hLG.trans hGU
  have hLC : K ≤ stabSub C := hLG.trans hGC
  have hcL' : Nat.card ↥(autSec K (commV K) C) = 360 := by
    rw [← hc]
    exact (Nat.card_congr (secEquiv K hLU hLC hfL).toEquiv).symm
  have hq1 : ∀ {G' : Subgroup (MulAut (Sec (commV K) C))}, qOf G' = ((1 : ℚ) : WithTop ℚ) →
      (1 : WithTop ℚ) ≤ qOf G' := fun hq => by rw [hq]; exact le_of_eq (by simp)
  rcases hconcl with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
  · exact Or.inl (hq1 c1.2.2.2)
  · exfalso
    obtain ⟨-, ⟨n, hn⟩, -⟩ := c2
    exact not_sl3_360 hcL' hn
  · obtain ⟨⟨n, hn, h1⟩, -⟩ := c3
    by_cases hn1 : n = 1
    · subst hn1
      obtain ⟨⟨e6⟩, hL, hG⟩ := FFC.ident_sp4 hb4 hn
      refine Or.inr ⟨?_, hG, ?_, ⟨(MulEquiv.subgroupCongr hG).trans e6⟩⟩
      · rw [hG]
        exact hn
      · calc autSec K (commV K) C = ⁅ffJ (autSec (K ⊔ T) (commV K) C), ffJ (autSec (K ⊔ T) (commV K) C)⁆ := hL
          _ = ⁅autSec (K ⊔ T) (commV K) C, autSec (K ⊔ T) (commV K) C⁆ := by rw [← hG]
    · exfalso
      have hJL := h1 (by have := one_le_of_binaryNaturalSp4 hn; omega)
      rw [hJL] at hn
      exact not_sp4_360 hcL' hn
  · exact Or.inl (hq1 c4.2)
  · exact Or.inl (hq1 c5.2)
  · exact Or.inl (hq1 c6.2.2.2.1)
  · exact Or.inl (hq1 c7.2.2.2.2.1)
  · exact Or.inl (hq1 c8.2.2.1)
  · exfalso
    obtain ⟨-, n, hn4, hn, -⟩ := c9
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hn
    exact not_sl_two_360 hcL' hn4 hπ
  · obtain ⟨hext, hrest⟩ := c10
    rcases hrest with hi | hii
    · exact Or.inl (hq1 hi.2.2.2)
    · exfalso
      exact not_extSq_360 hcL' (Or.inl rfl) hext
  · exact Or.inl (hq1 c11.2.2.2.1)

end Main


section Decomp

variable {V : Type} [CommGroup V] [Finite V]

theorem commV_L_sup_fixV_L_eq_top (hV : ∀ v : V, v ^ 2 = 1) {X L S : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hS : IsSylowTwoOf S X) (hXLS : X ≤ L ⊔ S) {z : V}
    (hzS : ∀ s ∈ S, s z = z) (hgen : Subgroup.closure {v : V | ∃ g ∈ X, g z = v} = ⊤) :
    commV L ⊔ fixV L = ⊤ := by
  classical
  set W : Subgroup V := commV L ⊔ fixV L with hW
  have hWinv : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul]
    exact W.mul_mem (Subgroup.mem_sup_left (commV_invariant hLn hx hu))
      (Subgroup.mem_sup_right (fixV_invariant hLn hx hc))
  let P : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ X ∧ g z * z⁻¹ ∈ W}
      one_mem' := ⟨X.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨X.mul_mem ha hb, ?_⟩
        have e : (a * b) z * z⁻¹ = a (b z * z⁻¹) * (a z * z⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e]
        exact W.mul_mem (hWinv a ha _ hb') ha'
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨X.inv_mem ha, ?_⟩
        have h1 := hWinv a⁻¹ (X.inv_mem ha) _ ha'
        have e : a⁻¹ (a z * z⁻¹) = (a⁻¹ z * z⁻¹)⁻¹ := by
          simp only [map_mul, map_inv, MulAut.inv_apply_self]
          group
        rw [e] at h1
        simpa using W.inv_mem h1 }
  have hLP : L ≤ P := fun l hl =>
    ⟨hLX hl, Subgroup.mem_sup_left (Subgroup.subset_closure ⟨l, hl, z, rfl⟩)⟩
  have hSP : S ≤ P := fun s hs => ⟨hS.1 hs, by rw [hzS s hs, mul_inv_cancel]; exact W.one_mem⟩
  have hXP : X ≤ P := hXLS.trans (sup_le hLP hSP)
  have hgz : ∀ g ∈ X, g z * z⁻¹ ∈ W := fun g hg => (hXP hg).2
  have hcommX : commV X ≤ W := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    have hv : v ∈ Subgroup.closure {v : V | ∃ g ∈ X, g z = v} := by
      rw [hgen]
      exact Subgroup.mem_top v
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, rfl⟩ := hy
      have e : x (h z) * (h z)⁻¹ = (x * h) z * z⁻¹ * (h z * z⁻¹)⁻¹ := by
        simp only [MulAut.mul_apply]
        group
      rw [e]
      exact W.mul_mem (hgz _ (X.mul_mem hx hh)) (W.inv_mem (hgz h hh))
    | one => simp
    | mul a b _ _ ha hb =>
      have e : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
        simp only [map_mul, mul_inv_rev]
        ac_rfl
      rw [e]
      exact W.mul_mem ha hb
    | inv a _ ha =>
      have e : x a⁻¹ * (a⁻¹)⁻¹ = (x a * a⁻¹)⁻¹ := by
        simp only [map_inv, inv_inv, mul_inv_rev]
        ac_rfl
      rw [e]
      exact W.inv_mem ha
  have htop := commV_sup_fixV_eq_top hV hS hzS hgen
  have hfix : fixV X ≤ fixV L := fun v hv l hl => hv l (hLX hl)
  refine eq_top_iff.mpr ?_
  rw [← htop]
  exact sup_le hcommX (hfix.trans le_sup_right)

end Decomp

end S1549D

end CFSG.Quasithin
