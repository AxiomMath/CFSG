
module

public import CFSG.Quasithin.Background.A3Structure36BHeisBase

public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Quasithin.Background.A3Structure36BStarBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem eq_top_of_isPOnePlusTwo (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K)
    (hl2 : L2MultiplierFact) {q : ℕ} (hq : q.Prime) (D : PrimeData X q) (hDK : D.K = K)
    (hH : IsPOnePlusTwo q ↥D.P) : D.P = ⊤ := by
  have hfin : Finite X := h.finite
  have hperf : Group.IsPerfect X := isPerfect_of_hyp h
  have hfq : Fact q.Prime := ⟨hq⟩
  have hDchar : D.P.Characteristic := D.characteristic
  have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
  have hRF : CFSG.pCore q X ≤ CFSG.fittingSubgroup X := CFSG.pCore_le_fitting X q
  have hRK : CFSG.pCore q X ≤ K := hKF ▸ hRF
  have hext : CFSG.IsExtraspecial q ↥D.P := hH.1
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h1 : Nat.card ↥(CFSG.pCore 2 X) = 1 := by
      rw [h.o2]
      exact Subgroup.card_bot
    have h2 : Nat.card ↥D.P ≤ Nat.card ↥(CFSG.pCore 2 X) := Subgroup.card_le_card_group _
    rw [hH.2.1, h1] at h2
    have : 1 < 2 ^ 3 := by norm_num
    omega
  have hA123 := range_conj_eq_ker_autQuotient_frattini (P := ↥D.P) (p := q)
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup X, P' = D.P.map (CFSG.pCore q X).subtype := ⟨_, rfl⟩
  have hP'le : P' ≤ CFSG.pCore q X := hP' ▸ Subgroup.map_subtype_le D.P
  have hP'normal : P'.Normal := by
    rw [hP']
    infer_instance
  have hmemP' : ∀ x : X, x ∈ P' ↔ ∃ d : ↥(CFSG.pCore q X), d ∈ D.P ∧ (d : X) = x := by
    intro x
    rw [hP']
    exact Subgroup.mem_map
  have hb : ∀ r : ↥(CFSG.pCore q X), ∃ u : ↥D.P, ∀ x : ↥D.P,
      (u : ↥(CFSG.pCore q X)) * (x : ↥(CFSG.pCore q X)) * (u : ↥(CFSG.pCore q X))⁻¹ =
        r * (x : ↥(CFSG.pCore q X)) * r⁻¹ := by
    intro r
    have hrK : (r : X) ∈ D.K := hDK ▸ hRK r.2
    have hβ : MulAut.characteristic D.P (MulAut.conjNormal (r : X)) ∈
        (autQuotient (frattini ↥D.P)).ker := by
      rw [mem_ker_autQuotient]
      intro x
      obtain ⟨y, hy, hyx⟩ := (D.mem_K (r : X)).1 hrK (x : ↥(CFSG.pCore q X)) x.2
      have hy' : y = x⁻¹ * MulAut.characteristic D.P (MulAut.conjNormal (r : X)) x := by
        apply Subtype.ext
        exact hyx
      rw [← hy']
      exact hy
    rw [← hA123] at hβ
    obtain ⟨u, hu⟩ := hβ
    refine ⟨u, fun x => ?_⟩
    have h2 := congrArg (fun φ : MulAut ↥D.P => ((φ x : ↥D.P) : ↥(CFSG.pCore q X))) hu
    exact h2
  obtain ⟨C, hC⟩ : ∃ C : Subgroup X,
      C = CFSG.pCore q X ⊓ Subgroup.centralizer (P' : Set X) := ⟨_, rfl⟩
  have hCn : C.Normal := by
    rw [hC]
    have := A1a.normal_centralizer_of_normal P'
    infer_instance
  have hCle : C ≤ CFSG.pCore q X := hC ▸ inf_le_left
  have hCp : IsPGroup q ↥C := (CFSG.pCore_isPGroup (p := q) (G := X)).to_le hCle
  have hdec : ∀ r : X, r ∈ CFSG.pCore q X → ∃ u ∈ P', ∃ c ∈ C, r = u * c := by
    intro r hr
    obtain ⟨u, hu⟩ := hb ⟨r, hr⟩
    have hcR : (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * r ∈ CFSG.pCore q X :=
      (CFSG.pCore q X).mul_mem ((CFSG.pCore q X).inv_mem (u : ↥(CFSG.pCore q X)).2) hr
    have hcent : (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * r ∈ Subgroup.centralizer (P' : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      obtain ⟨x, hxP, rfl⟩ := (hmemP' d).1 hd
      have h3 := congrArg (fun z : ↥(CFSG.pCore q X) => (z : X)) (hu ⟨x, hxP⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      calc (x : X) * ((((u : ↥(CFSG.pCore q X)) : X))⁻¹ * r)
          = (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * (((u : ↥(CFSG.pCore q X)) : X) * x *
            (((u : ↥(CFSG.pCore q X)) : X))⁻¹) * r := by group
        _ = (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * (r * x * r⁻¹) * r := by rw [h3]
        _ = (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * r * x := by group
    refine ⟨((u : ↥(CFSG.pCore q X)) : X), (hmemP' _).2 ⟨u, u.2, rfl⟩,
      (((u : ↥(CFSG.pCore q X)) : X))⁻¹ * r, ?_, by group⟩
    rw [hC]
    exact ⟨hcR, hcent⟩
  have hS : ∀ x ∈ C, x ^ q = 1 → x ∈ P' := by
    intro x hxC hxq
    by_cases hx1 : x = 1
    · rw [hx1]
      exact P'.one_mem
    · have hxC' : x ∈ CFSG.pCore q X ⊓ Subgroup.centralizer (P' : Set X) := hC ▸ hxC
      have hxR : x ∈ CFSG.pCore q X := hxC'.1
      have hcent : (⟨x, hxR⟩ : ↥(CFSG.pCore q X)) ∈
          Subgroup.centralizer (D.P : Set ↥(CFSG.pCore q X)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have := Subgroup.mem_centralizer_iff.1 hxC'.2 (y : X) ((hmemP' _).2 ⟨y, hy, rfl⟩)
        exact Subtype.ext this
      have hord : orderOf (⟨x, hxR⟩ : ↥(CFSG.pCore q X)) = q := by
        apply orderOf_eq_prime
        · exact Subtype.ext (by simpa using hxq)
        · intro h1
          apply hx1
          exact congrArg Subtype.val h1
      have := D.supercritical.mem_of_orderOf_eq _ hcent hord
      exact (hmemP' x).2 ⟨⟨x, hxR⟩, this, rfl⟩
  obtain ⟨SX, hSX⟩ : ∃ SX : Subgroup X, SX = P' ⊓ Subgroup.centralizer (P' : Set X) :=
    ⟨_, rfl⟩
  have hSXcard : Nat.card SX ≤ q := by
    let ι : ↥D.P →* X := (CFSG.pCore q X).subtype.comp D.P.subtype
    have hι : Function.Injective ι :=
      (CFSG.pCore q X).subtype_injective.comp D.P.subtype_injective
    have hle : SX ≤ ι.range := by
      intro x hx
      rw [hSX] at hx
      obtain ⟨d, hdP, rfl⟩ := (hmemP' x).1 hx.1
      exact ⟨⟨d, hdP⟩, rfl⟩
    have hcomap : SX.comap ι ≤ Subgroup.center ↥D.P := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro z
      have hy' : ι y ∈ SX := hy
      rw [hSX] at hy'
      have h3 := Subgroup.mem_centralizer_iff.1 hy'.2 (ι z)
        ((hmemP' _).2 ⟨(z : ↥(CFSG.pCore q X)), z.2, rfl⟩)
      apply hι
      rw [map_mul, map_mul]
      exact h3
    have h1 : SX = (SX.comap ι).map ι := (Subgroup.map_comap_eq_self hle).symm
    calc Nat.card SX = Nat.card (SX.comap ι) := by
          conv_lhs => rw [h1]
          exact Subgroup.card_map_of_injective hι
      _ ≤ Nat.card (Subgroup.center ↥D.P) := Subgroup.card_le_of_le hcomap
      _ = q := CFSG.IsExtraspecial.center_order_p q ↥D.P
  have hcyc : IsCyclic ↥C := by
    have hrank : CFSG.pRank q ↥C ≤ 1 := by
      refine csSup_le' ?_
      rintro r ⟨A, hA, hcard⟩
      have hAle : A.map C.subtype ≤ SX := by
        rintro _ ⟨a, ha, rfl⟩
        have hpow : (a : X) ^ q = 1 := by
          have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := q) (A := A) (a : C) ha
          exact congrArg Subtype.val this
        have hxP' := hS a a.2 hpow
        rw [hSX]
        refine ⟨hxP', ?_⟩
        have hxC' : (a : X) ∈ CFSG.pCore q X ⊓ Subgroup.centralizer (P' : Set X) := hC ▸ a.2
        exact hxC'.2
      have h1 : Nat.card A ≤ Nat.card SX := by
        calc Nat.card A = Nat.card (A.map C.subtype) :=
              (Subgroup.card_map_of_injective C.subtype_injective).symm
          _ ≤ Nat.card SX := Subgroup.card_le_of_le hAle
      rw [hcard] at h1
      have h2 : q ^ r ≤ q ^ 1 := by simpa using h1.trans hSXcard
      exact (Nat.pow_le_pow_iff_right hq.one_lt).1 h2
    rcases (LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hq hCp).1 hrank with
      hcyc | ⟨h2, -⟩
    · exact hcyc
    · exact absurd h2 hq2
  have hCcent : C ≤ Subgroup.center X := le_center_of_isCyclic_normal hcyc
  obtain ⟨H, hH'⟩ : ∃ H : Subgroup X, H = CFSG.fittingSubgroup X ⊓ CFSG.pPrimeCore q X :=
    ⟨_, rfl⟩
  have hHn : H.Normal := by
    rw [hH']
    infer_instance
  obtain ⟨N, hN⟩ : ∃ N : Subgroup X, N = P' ⊔ H := ⟨_, rfl⟩
  have hNn : N.Normal := by
    rw [hN]
    infer_instance
  have hHF : H ≤ CFSG.fittingSubgroup X := hH' ▸ inf_le_left
  have hNF : N ≤ CFSG.fittingSubgroup X := by
    rw [hN]
    exact sup_le (hP'le.trans hRF) hHF
  have hKD : IsKernelData X (CFSG.fittingSubgroup X) := hKF ▸ hK.data
  obtain ⟨r, hr, h5, hPSL⟩ := hK.psl
  have hFN : N = CFSG.fittingSubgroup X := by
    refine eq_of_commutator_le hl2 h hr h5 hPSL hKD hNF ?_ (odd_card_fitting h)
    intro k hk g
    have hk' : k ∈ CFSG.pCore q X ⊔ H := hH' ▸ fitting_le_pCore_sup_inf (X := X) q hk
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hk'
    obtain ⟨u, hu, c, hc, rfl⟩ := hdec y hy
    have hcc : c ∈ Subgroup.center X := hCcent hc
    have e1 : u * c * z = (u * z) * c := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 hcc z, ← mul_assoc]
    rw [e1, commutatorElement_mul_center_left g hcc]
    have hw : u * z ∈ N := by
      rw [hN]
      exact (P' ⊔ H).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hz)
    have h2 : ⁅u * z, g⁆ = (u * z) * (g * (u * z)⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact N.mul_mem hw (hNn.conj_mem _ (N.inv_mem hw) g)
  have hRN : CFSG.pCore q X ≤ P' := by
    intro x hx
    have hxN : x ∈ P' ⊔ H := by
      rw [← hN, hFN]
      exact hRF hx
    obtain ⟨p, hp, hh, hhH, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxN
    have hpR : p ∈ CFSG.pCore q X := hP'le hp
    have hhR : hh ∈ CFSG.pCore q X := by
      have := (CFSG.pCore q X).mul_mem ((CFSG.pCore q X).inv_mem hpR) hx
      simpa using this
    have hh1 : hh = 1 := by
      have hhH' : hh ∈ CFSG.fittingSubgroup X ⊓ CFSG.pPrimeCore q X := hH' ▸ hhH
      have : hh ∈ CFSG.pCore q X ⊓ CFSG.pPrimeCore q X := ⟨hhR, hhH'.2⟩
      rw [pCore_inf_pPrimeCore] at this
      exact Subgroup.mem_bot.1 this
    rw [hh1, mul_one]
    exact hp
  rw [eq_top_iff]
  intro d _
  obtain ⟨d', hd', hdd'⟩ := (hmemP' (d : X)).1 (hRN d.2)
  have : d' = d := Subtype.ext hdd'
  rw [← this]
  exact hd'

end CFSG.Quasithin.A36B
