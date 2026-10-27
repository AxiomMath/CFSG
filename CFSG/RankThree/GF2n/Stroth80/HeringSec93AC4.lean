module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC3
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93AltStep3
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93TorusLift
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3D

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

section Key

variable {G : Type} [Group G] [Finite G]

theorem key_surj {A A' H : Subgroup G} {y : G} (hHA : H ≤ A) (hHA' : H ≤ A')
    (hAA' : ∀ x ∈ A', ∀ u ∈ A, ⁅x, u⁆ ∈ H) (hcomm : ∀ u ∈ A, ∀ v ∈ A, ⁅u, v⁆ ∈ H)
    (hHn : ∀ u ∈ A, ∀ k ∈ H, u * k * u⁻¹ ∈ H) (hyH : ∀ k ∈ H, y * k * y⁻¹ ∈ H)
    (hxy : ∀ x ∈ A', ⁅x, y⁆ ∈ A)
    (hinj : ∀ x ∈ A', ⁅x, y⁆ ∈ H → x ∈ H) (hcard : Nat.card A' = Nat.card A) :
    ∀ f₀ ∈ A, ∃ x ∈ A', ⁅x, y⁆ * f₀ ∈ H := by
  classical
  have hNH : (H.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff hHA).mpr fun k u hk hu => hHn u hu k hk
  haveI := hNH
  let φ₀ : ↥A' → ↥A ⧸ H.subgroupOf A := fun x => QuotientGroup.mk ⟨⁅(x : G), y⁆, hxy x x.2⟩
  have hφmul : ∀ x₁ x₂ : ↥A', φ₀ (x₁ * x₂) = φ₀ x₁ * φ₀ x₂ := by
    intro x₁ x₂
    show (QuotientGroup.mk (⟨⁅((x₁ * x₂ : ↥A') : G), y⁆, hxy _ (x₁ * x₂).2⟩ : ↥A) :
        ↥A ⧸ H.subgroupOf A) = QuotientGroup.mk (⟨⁅(x₁ : G), y⁆, hxy _ x₁.2⟩ : ↥A) *
          QuotientGroup.mk (⟨⁅(x₂ : G), y⁆, hxy _ x₂.2⟩ : ↥A)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (⁅((x₁ * x₂ : ↥A') : G), y⁆)⁻¹ * (⁅(x₁ : G), y⁆ * ⁅(x₂ : G), y⁆) ∈ H
    have hu₁ : ⁅(x₁ : G), y⁆ ∈ A := hxy _ x₁.2
    have hu₂ : ⁅(x₂ : G), y⁆ ∈ A := hxy _ x₂.2
    have hk₁ : ⁅(x₁ : G), ⁅(x₂ : G), y⁆⁆ ∈ H := hAA' _ x₁.2 _ hu₂
    have hc : ⁅⁅(x₁ : G), y⁆⁻¹, ⁅(x₂ : G), y⁆⁻¹⁆ ∈ H := hcomm _ (A.inv_mem hu₁) _ (A.inv_mem hu₂)
    have hv : (⁅(x₂ : G), y⁆ * ⁅(x₁ : G), y⁆)⁻¹ ∈ A := A.inv_mem (A.mul_mem hu₂ hu₁)
    have e : (⁅((x₁ * x₂ : ↥A') : G), y⁆)⁻¹ * (⁅(x₁ : G), y⁆ * ⁅(x₂ : G), y⁆) =
        ((⁅(x₂ : G), y⁆ * ⁅(x₁ : G), y⁆)⁻¹ * ⁅(x₁ : G), ⁅(x₂ : G), y⁆⁆⁻¹ *
          ((⁅(x₂ : G), y⁆ * ⁅(x₁ : G), y⁆)⁻¹)⁻¹) * ⁅⁅(x₁ : G), y⁆⁻¹, ⁅(x₂ : G), y⁆⁻¹⁆ := by
      simp only [Subgroup.coe_mul, commutatorElement_def]
      group
    rw [e]
    exact H.mul_mem (hHn _ hv _ (H.inv_mem hk₁)) hc
  let φ : ↥A' →* ↥A ⧸ H.subgroupOf A := MonoidHom.mk' φ₀ hφmul
  have hker : φ.ker = H.subgroupOf A' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show φ₀ x = 1 ↔ _
    show (QuotientGroup.mk (⟨⁅(x : G), y⁆, hxy x x.2⟩ : ↥A) : ↥A ⧸ H.subgroupOf A) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · exact hinj x x.2
    · intro hx
      have e : ⁅(x : G), y⁆ = (x : G) * (y * (x : G)⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      show ⁅(x : G), y⁆ ∈ H
      rw [e]
      refine H.mul_mem hx ?_
      exact hyH _ (H.inv_mem hx)
  have hrange : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf A)
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA').toEquiv] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv] at h2
    have h3 : Nat.card (↥A' ⧸ H.subgroupOf A') = Nat.card φ.range := by
      rw [← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [h3, hcard] at h1
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    rw [h1] at h2
    exact (Nat.eq_of_mul_eq_mul_right hpos h2.symm).symm
  intro f₀ hf₀
  have hmem : (QuotientGroup.mk (⟨f₀⁻¹, A.inv_mem hf₀⟩ : ↥A) : ↥A ⧸ H.subgroupOf A) ∈
      φ.range := by
    rw [hrange]
    exact Subgroup.mem_top _
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, x.2, ?_⟩
  have hx' : (QuotientGroup.mk (⟨⁅(x : G), y⁆, hxy x x.2⟩ : ↥A) : ↥A ⧸ H.subgroupOf A) =
      QuotientGroup.mk (⟨f₀⁻¹, A.inv_mem hf₀⟩ : ↥A) := hx
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx'
  have : (⁅(x : G), y⁆)⁻¹ * f₀⁻¹ ∈ H := hx'
  have h2 := H.inv_mem this
  rw [mul_inv_rev, inv_inv, inv_inv] at h2
  have h3 := hHn _ (hxy x x.2) _ h2
  have e : ⁅(x : G), y⁆ * (f₀ * ⁅(x : G), y⁆) * ⁅(x : G), y⁆⁻¹ = ⁅(x : G), y⁆ * f₀ := by
    group
  rwa [e] at h3

end Key

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_comm_mem_inf_of_not_mem_Fhat (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G} (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hline : LineGeom M Q Z B h) {y : G} (hyL : y ∈ LB M Q B) (hyF : y ∉ Fhat M Q B h) :
    ∀ f₀ ∈ LB M Q B ⊓ Fhat M Q B h, ∃ x ∈ conjSubgroup h (LB M Q B) ⊓ Fhat M Q B h,
      ⁅x, y⁆ * f₀ ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
  classical
  have hs := cfg.hs.toSec5
  have hh := cfg.hh
  have hne := cfg.hne
  have hLX : LB M Q B ≤ Xhat M Q B h := le_sup_left
  have hL'X : conjSubgroup h (LB M Q B) ≤ Xhat M Q B h := le_sup_right
  have hHF : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤ Fhat M Q B h :=
    step93L2Second_H_le_pCore hc hh
  have hFX : Fhat M Q B h ≤ Xhat M Q B h := pCoreIn_le _
  have hQH : Q ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) :=
    le_inf sec39_Q_le_LB (Q_le_conj_LB hc hh)
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hFL : ∀ f ∈ Fhat M Q B h, ∀ u ∈ LB M Q B, f * u * f⁻¹ ∈ LB M Q B := fun f hf u hu => by
    have := conj_mem_conjSubgroup f hu
    rwa [(pCoreIn_conj_LB_eq h34 hs hh hf).1] at this
  have hFL' : ∀ f ∈ Fhat M Q B h, ∀ u ∈ conjSubgroup h (LB M Q B),
      f * u * f⁻¹ ∈ conjSubgroup h (LB M Q B) := fun f hf u hu => by
    have := conj_mem_conjSubgroup f hu
    rwa [(pCoreIn_conj_LB_eq h34 hs hh hf).2] at this
  have hFn : Xhat M Q B h ≤ Subgroup.normalizer (Fhat M Q B h : Set G) := le_normalizer_pCoreIn _
  obtain ⟨hN, hrel⟩ := normalizer_inf_le_Fhat_and_relIndex h34 cfg hq hline
  obtain ⟨w, hwX, hw, -⟩ := exists_cover_of_line h34 hs hh hne hline
  refine key_surj (A := LB M Q B ⊓ Fhat M Q B h) (A' := conjSubgroup h (LB M Q B) ⊓ Fhat M Q B h)
    (H := LB M Q B ⊓ conjSubgroup h (LB M Q B)) (y := y) (le_inf inf_le_left hHF)
    (le_inf inf_le_right hHF) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rintro x ⟨hxL', hxF⟩ u ⟨huL, huF⟩
    refine ⟨?_, ?_⟩
    · have e : ⁅x, u⁆ = (x * u * x⁻¹) * u⁻¹ := rfl
      rw [e]
      exact (LB M Q B).mul_mem (hFL x hxF u huL) ((LB M Q B).inv_mem huL)
    · have e : ⁅x, u⁆ = x * (u * x⁻¹ * u⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (conjSubgroup h (LB M Q B)).mul_mem hxL'
        (hFL' u huF x⁻¹ ((conjSubgroup h (LB M Q B)).inv_mem hxL'))
  ·
    rintro u ⟨huL, -⟩ v ⟨hvL, -⟩
    exact hQH (hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator huL hvL))
  · rintro u ⟨huL, -⟩ k hk
    exact conj_mem_inf_of_mem_Xhat hc hh (hLX huL) hk
  · intro k hk
    exact conj_mem_inf_of_mem_Xhat hc hh (hLX hyL) hk
  ·
    rintro x ⟨hxL', hxF⟩
    refine ⟨?_, ?_⟩
    · have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := rfl
      rw [e]
      exact (LB M Q B).mul_mem (hFL x hxF y hyL) ((LB M Q B).inv_mem hyL)
    · have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine (Fhat M Q B h).mul_mem hxF ?_
      exact (Subgroup.mem_normalizer_iff.mp (hFn (hLX hyL)) x⁻¹).mp ((Fhat M Q B h).inv_mem hxF)
  ·
    rintro x ⟨hxL', hxF⟩ hxy
    have hyx : ⁅y, x⁆ ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
      rw [← commutatorElement_inv]
      exact (LB M Q B ⊓ conjSubgroup h (LB M Q B)).inv_mem hxy
    have hyxL' : y * x * y⁻¹ ∈ conjSubgroup h (LB M Q B) := by
      have e : y * x * y⁻¹ = ⁅y, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (conjSubgroup h (LB M Q B)).mul_mem hyx.2 hxL'
    have hxc : x ∈ conjSubgroup y⁻¹ (conjSubgroup h (LB M Q B)) := by
      rw [mem_conjSubgroup, inv_inv]
      exact hyxL'
    have hne' : conjSubgroup y⁻¹ (conjSubgroup h (LB M Q B)) ≠ conjSubgroup h (LB M Q B) := by
      intro e
      apply hyF
      apply hN y hyL
      have := conjSubgroup_eq_self_iff.mp e
      have h2 := Subgroup.inv_mem _ this
      simpa using h2
    have hε : y⁻¹ ∈ Xhat M Q B h := (Xhat M Q B h).inv_mem (hLX hyL)
    have := inf_conj_inf_eq_H h34 hs hh hne hline hε hne'
    have hx' : x ∈ conjSubgroup h (LB M Q B) ⊓ conjSubgroup y⁻¹ (conjSubgroup h (LB M Q B)) :=
      ⟨hxL', hxc⟩
    rw [this] at hx'
    exact hx'
  ·
    have hwF : conjSubgroup w (Fhat M Q B h) = Fhat M Q B h :=
      conjSubgroup_eq_self_iff.mpr (hFn hwX)
    have : conjSubgroup w (LB M Q B ⊓ Fhat M Q B h) =
        conjSubgroup h (LB M Q B) ⊓ Fhat M Q B h := by
      rw [conjSubgroup_inf, hw, hwF]
    rw [← this]
    exact card_conjSubgroup w _

theorem step93L2AltXH_of_line (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hline : LineGeom M Q Z B h) :
    LB M Q B ⊓ hc.CN t ≤ Fhat M Q B h ∨
      LB M Q B ⊓ conjSubgroup h (LB M Q B) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B := by
  classical
  have hs := cfg.hs.toSec5
  have hh := cfg.hh
  have hsyl := card_LB_sup_Fhat_eq h34 cfg hq hline
  have hTor := torus_transitive_of_relIndex_eq h34 cfg hq hsyl
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hXH : Xhat M Q B h ≤ H0 M Z := sup_le hc.LB_le_H0 (hLconj ▸ hc'.LB_le_H0)
  have hFX : Fhat M Q B h ≤ Xhat M Q B h := pCoreIn_le _
  by_cases hNF : LB M Q B ⊓ hc.CN t ≤ Fhat M Q B h
  · exact Or.inl hNF
  right
  obtain ⟨y₀, hy₀, hy₀F⟩ := SetLike.not_le_iff_exists.mp hNF
  set S : Subgroup G :=
    LB M Q B ⊓ conjSubgroup h (LB M Q B) ⊔ (LB M Q B ⊓ hc.CN t) with hSdef
  have hHS : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤ S := le_sup_left
  have hNS : LB M Q B ⊓ hc.CN t ≤ S := le_sup_right
  have hSL : S ≤ LB M Q B := sup_le inf_le_left inf_le_left
  have hA : ∀ a ∈ LB M Q B, a ∉ Fhat M Q B h → a ∈ S := by
    intro a haL haF
    obtain ⟨g, hgM, hgL, hga⟩ := hTor y₀ hy₀.1 hy₀F a haL haF
    have hCN := step93L2AltXH_CN_inv_of_cfg h34 h311a h311bComm h312b cfg hgM hgL
    have hy₁N : g * y₀ * g⁻¹ ∈ LB M Q B ⊓ hc.CN t := by
      have := conj_mem_conjSubgroup g hy₀
      rwa [hCN] at this
    have hy₁F : g * y₀ * g⁻¹ ∉ Fhat M Q B h := fun hy => haF (by
      have h1 := (Fhat M Q B h).mul_mem ((Fhat M Q B h).inv_mem hy) hga
      rw [inv_mul_cancel_left] at h1
      simpa using (Fhat M Q B h).inv_mem h1)
    obtain ⟨x, hx, hxk⟩ := exists_comm_mem_inf_of_not_mem_Fhat h34 cfg hq hline hy₁N.1 hy₁F
      (g * y₀ * g⁻¹ * a⁻¹) ⟨(LB M Q B).mul_mem hy₁N.1 ((LB M Q B).inv_mem haL), hga⟩
    have hxM : x ∈ M := (hXH (hFX hx.2)).1
    have hxL : conjSubgroup x (LB M Q B) = LB M Q B := (pCoreIn_conj_LB_eq h34 hs hh hx.2).1
    have hxN : x * (g * y₀ * g⁻¹) * x⁻¹ ∈ LB M Q B ⊓ hc.CN t := by
      have := conj_mem_conjSubgroup x hy₁N
      rwa [step93L2AltXH_CN_inv_of_cfg h34 h311a h311bComm h312b cfg hxM hxL] at this
    have e : a = (⁅x, g * y₀ * g⁻¹⁆ * (g * y₀ * g⁻¹ * a⁻¹))⁻¹ * (x * (g * y₀ * g⁻¹) * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact S.mul_mem (S.inv_mem (hHS hxk)) (hNS hxN)
  have hLS : LB M Q B ≤ S := by
    intro a ha
    by_cases haF : a ∈ Fhat M Q B h
    · have hya : y₀ * a ∈ LB M Q B := (LB M Q B).mul_mem hy₀.1 ha
      have hyaF : y₀ * a ∉ Fhat M Q B h := fun hy => hy₀F (by
        have h1 := (Fhat M Q B h).mul_mem hy ((Fhat M Q B h).inv_mem haF)
        rwa [mul_inv_cancel_right] at h1)
      have h2 := S.mul_mem (S.inv_mem (hNS hy₀)) (hA _ hya hyaF)
      rwa [inv_mul_cancel_left] at h2
    · exact hA a ha haF
  exact le_antisymm hSL hLS

theorem step93L2AltXH_of_near (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {h : G}
    (cfg : Cfg93c hc n t r Z0 h)
    (hq : QuotSat (Xhat M Q B h) (Fhat M Q B h) (IsSLModel 2 (Nat.card Z)))
    (hnear : conjSubgroup h B ≤ QB B) :
    LB M Q B ⊓ hc.CN t ≤ Fhat M Q B h ∨
      LB M Q B ⊓ conjSubgroup h (LB M Q B) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B :=
  step93L2AltXH_of_line h34 h311a h311bComm h312b cfg hq (lineGeom_of_QB hc cfg.hh hnear)

end HS9

end CFSG.RankThree.GF2n.Stroth80
