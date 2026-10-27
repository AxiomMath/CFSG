module

public import CFSG.RankThree.GF2n.Tim79a34BigAlpha
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.RankThree.GF2n.Tim79a

section BigNXStmt

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def BigNormalizerXStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∀ g ∈ M, conjSubgroup g (wOf V H) = wOf V H → conjSubgroup g (xOf V H) = xOf V H

end BigNXStmt

section BigNXProof

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic CFSG.Blueprint
open Matrix
open scoped commutatorElement

section BigNX

variable {G : Type} [Group G]

theorem bigNX_conjSubgroup_ne_bot {S : Subgroup G} (g : G) (hS : S ≠ ⊥) :
    conjSubgroup g S ≠ ⊥ := fun h0 => by
  have h1 : S.map (MulAut.conj g).toMonoidHom = ⊥ := h0
  exact hS ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h1)

variable {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem bigNX_exists_conj_of_mem_wOf (hVH : V ≤ H) (hNat : BigNatCfg V H hVH Φ ψ) (ha : a ≠ 0)
    (haV : ψG a ∈ V) {u : G} (hu : u ∈ wOf V H) (hu1 : u ≠ 1) :
    ∃ x ∈ xOf V H, u ∈ conjSubgroup x V := by
  obtain ⟨c, rfl⟩ := bigB_exists_psi (ψ := ψ) hu
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hu1 bigRW_psi_zero
  obtain ⟨g₁, hg₁⟩ := exists_mat_mulVec_eq_of_ne_zero ha hc0
  obtain ⟨x, hx⟩ := xToXbar_surjective hVH (Φ g₁)
  have hgx : Φ.symm (xToXbar hVH x) = g₁ := by
    rw [hx]
    exact Φ.symm_apply_apply g₁
  refine ⟨(x : G), x.2, ?_⟩
  have key := hNat.equiv x a
  rw [hgx, hg₁] at key
  rw [mem_conjSubgroup, key]
  have e : (x : G)⁻¹ * ((x : G) * ψG a * (x : G)⁻¹) * (x : G) = ψG a := by group
  rw [e]
  exact haV

end BigNX

theorem bigNormalizerXStatement_of_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) : BigNormalizerXStatement := by
  intro G _ _ M V Q P H hH g _ hgW
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  obtain ⟨n, f, Φ, ψ, -, -, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  have haV := hpoint a T ha hTT hTV
  refine conjSubgroup_eq_of_le ?_
  have hmap : conjSubgroup g (xOf V H) = ⨆ U ∈ omegaOf V H, conjSubgroup g U := by
    unfold conjSubgroup xOf
    simp only [Subgroup.map_iSup]
  rw [hmap]
  refine iSup₂_le fun U hU => ?_
  obtain ⟨h, hh, rfl⟩ := hU
  have hne := bigNX_conjSubgroup_ne_bot g (hc.conj_inf_wOf_ne_bot hh)
  rw [conjSubgroup_inf, hgW] at hne
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
  obtain ⟨huU, huW⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨x, hx, hux⟩ := bigNX_exists_conj_of_mem_wOf hVH hNat ha haV huW hu1'
  have hUx : conjSubgroup g (conjSubgroup h V) = conjSubgroup x V := by
    rw [conjSubgroup_conjSubgroup]
    refine tiPair_conj_eq_of_inf_ne_bot hc.ti (Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨u, Subgroup.mem_inf.mpr ⟨?_, hux⟩⟩, fun h' => hu1' (congrArg Subtype.val h')⟩)
    rwa [← conjSubgroup_conjSubgroup]
  rw [hUx]
  exact le_xOf (conjSubgroup_mem_omegaOf (xOf_le_H hVH hx))

end BigNXProof

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigGe_mem_QW {M V Q H : Subgroup G} (hQM : Q = inSubgroup (pCore 2) M) {g : ↥M}
    (hg : (g : Mbar M) ∈ Subgroup.normalizer (WbarM M V H : Set (Mbar M))) {w : G}
    (hw : w ∈ wOf V H) (hwM : w ∈ M) : (g : G) * w * (g : G)⁻¹ ∈ Q ⊔ wOf V H := by
  have h1 : ((⟨w, hwM⟩ : ↥M) : Mbar M) ∈ WbarM M V H :=
    mem_WbarM_iff.mpr ⟨⟨w, hwM⟩, hw, rfl⟩
  have h2 := (Subgroup.mem_normalizer_iff.mp hg _).mp h1
  obtain ⟨w', hw'W, hw'⟩ := mem_WbarM_iff.mp h2
  have h3 : (w' : Mbar M) = ((g * ⟨w, hwM⟩ * g⁻¹ : ↥M) : Mbar M) := by
    rw [hw', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h4 : ((w'⁻¹ * (g * ⟨w, hwM⟩ * g⁻¹) : ↥M) : G) ∈ inSubgroup (pCore 2) M :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h3)
  have h5 : (g : G) * w * (g : G)⁻¹ =
      (w' : G) * ((w'⁻¹ * (g * ⟨w, hwM⟩ * g⁻¹) : ↥M) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h5]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hw'W) (Subgroup.mem_sup_left (hQM ▸ h4))

theorem bigGe_key [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hcov : ∀ p ∈ P ⊓ wOf V H, ∀ b ∈ B, b ∉ P → ∃ r ∈ P, r * b * r⁻¹ = p * b)
    (hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H)
    {g : G} (hg : g ∈ M) {x : G} (hxg : x ∈ conjSubgroup g B) (hxS : x ∈ P ⊔ B) (hxP : x ∉ P) :
    ∃ r ∈ P, conjSubgroup g B = conjSubgroup r B := by
  have hBM : B ≤ M := hBW.trans (wOf_le_M_of_minCex hc)
  have hBN : B ≤ Subgroup.normalizer (P : Set G) := fun b hb => hc.M_le_normalizer_P (hBM hb)
  have hPM : P ≤ M := bigAlpha_P_le_M hc
  obtain ⟨p, hp, b, hb, hxpb⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hBN hxS
  have hbP : b ∉ P := fun h => hxP (hxpb ▸ P.mul_mem hp h)
  have hx2 : x * x = 1 := by
    have h1 := hc.wOf_isElemAbelian.mul_self_eq_one (hBW (mem_conjSubgroup.mp hxg))
    have e : x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, h1]
    group
  have hpW : p ∈ wOf V H := hmem p hp b hb hbP (by rw [← hxpb]; exact hx2)
  obtain ⟨r, hr, hrb⟩ := hcov p ⟨hp, hpW⟩ b hb hbP
  have hxr : x ∈ conjSubgroup r B := by
    rw [mem_conjSubgroup]
    have e : r⁻¹ * x * r = b := by
      rw [hxpb, ← hrb]
      group
    rw [e]
    exact hb
  have hx1 : x ≠ 1 := fun h => hxP (h ▸ P.one_mem)
  exact ⟨r, hr, bigAlpha_conj_eq hBTI hg (hPM hr) hx1 hxg hxr⟩

theorem bigGe_exists_conj_eq [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H) (hBne : B ≠ ⊥)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hcov : ∀ p ∈ P ⊓ wOf V H, ∀ b ∈ B, b ∉ P → ∃ r ∈ P, r * b * r⁻¹ = p * b)
    (hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H)
    {g : G} (hg : g ∈ M) (hgW : ∀ w ∈ wOf V H, g * w * g⁻¹ ∈ wOf V H ⊔ P) :
    ∃ r ∈ P, conjSubgroup g B = conjSubgroup r B := by
  obtain ⟨⟨b₁, hb₁⟩, hb₁ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb₁1 : b₁ ≠ 1 := fun h => hb₁ne (Subtype.ext h)
  have hy : g * b₁ * g⁻¹ ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * b₁ * g⁻¹) * g = b₁ := by group
    rw [e]
    exact hb₁
  have hyS : g * b₁ * g⁻¹ ∈ P ⊔ B := by
    have h2 : wOf V H ⊔ P ≤ P ⊔ B := by
      refine sup_le ?_ le_sup_left
      rw [← hPB]
      exact sup_le_sup_right inf_le_left B
    exact h2 (hgW b₁ (hBW hb₁))
  have hyP : g * b₁ * g⁻¹ ∉ P := by
    intro h
    have hgP : conjSubgroup g P = P := conjSubgroup_eq_self_iff.mpr (hc.M_le_normalizer_P hg)
    have h3 : g * b₁ * g⁻¹ ∈ conjSubgroup g P := by
      rw [hgP]
      exact h
    have h4 : b₁ ∈ P := by
      have e : g⁻¹ * (g * b₁ * g⁻¹) * g = b₁ := by group
      have := mem_conjSubgroup.mp h3
      rwa [e] at this
    have h5 : b₁ ∈ B ⊓ P := ⟨hb₁, h4⟩
    rw [hBP, Subgroup.mem_bot] at h5
    exact hb₁1 h5
  exact bigGe_key hc hBW hBTI hcov hmem hg hy hyS hyP

theorem bigGe_comm_mem [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) {p b : G} (hp : p ∈ P) (hb : b ∈ B) : ⁅p, b⁆ ∈ P ⊓ wOf V H := by
  have hBM : B ≤ M := hBW.trans (wOf_le_M_of_minCex hc)
  refine ⟨?_, ?_⟩
  · have hb' : b * p⁻¹ * b⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P (hBM hb)) p⁻¹).mp (P.inv_mem hp)
    have e : ⁅p, b⁆ = p * (b * p⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact P.mul_mem hp hb'
  · have hpW : p * b * p⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hc.PleH hp)) b).mp (hBW hb)
    rw [commutatorElement_def]
    exact (wOf V H).mul_mem hpW ((wOf V H).inv_mem (hBW hb))

theorem bigGe_conj_W [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H) (hBne : B ≠ ⊥)
    (hcov : ∀ b ∈ B, b ∉ P → ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w)
    {g : G} (hg : g ∈ M) (hgB : conjSubgroup g B = B) :
    conjSubgroup g (wOf V H) = wOf V H := by
  obtain ⟨b₀, hb₀, hb₀P⟩ : ∃ b₀ ∈ B, b₀ ∉ P := by
    obtain ⟨⟨b, hb⟩, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    refine ⟨b, hb, fun hbP => hbne (Subtype.ext ?_)⟩
    have h : b ∈ B ⊓ P := ⟨hb, hbP⟩
    rw [hBP, Subgroup.mem_bot] at h
    exact h
  have hle : conjSubgroup g (P ⊓ wOf V H) ≤ P ⊓ wOf V H := by
    intro c hcc
    obtain ⟨p, hp, hpc⟩ := hcov b₀ hb₀ hb₀P _ (mem_conjSubgroup.mp hcc)
    have e : c = ⁅g * p * g⁻¹, g * b₀ * g⁻¹⁆ := by
      have e1 : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
      rw [e1, ← hpc]
      simp only [commutatorElement_def]
      group
    have hgb : g * b₀ * g⁻¹ ∈ B := by
      have h1 : g * b₀ * g⁻¹ ∈ conjSubgroup g B := by
        rw [mem_conjSubgroup]
        have e2 : g⁻¹ * (g * b₀ * g⁻¹) * g = b₀ := by group
        rw [e2]
        exact hb₀
      rwa [hgB] at h1
    rw [e]
    exact bigGe_comm_mem hc hBW
      ((Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hg) p).mp hp) hgb
  have heq : conjSubgroup g (P ⊓ wOf V H) = P ⊓ wOf V H := conjSubgroup_eq_of_le hle
  calc conjSubgroup g (wOf V H) = conjSubgroup g ((P ⊓ wOf V H) ⊔ B) := by rw [hPB]
    _ = conjSubgroup g (P ⊓ wOf V H) ⊔ conjSubgroup g B := Subgroup.map_sup _ _ _
    _ = (P ⊓ wOf V H) ⊔ B := by rw [heq, hgB]
    _ = wOf V H := hPB

theorem bigGe_conj_R [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {g : G}
    (hg : g ∈ M) (hX : conjSubgroup g (xOf V H) = xOf V H) :
    conjSubgroup g (xOf V H ⊓ Subgroup.centralizer (V : Set G)) =
      xOf V H ⊓ Subgroup.centralizer (V : Set G) := by
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
    rw [hc.normalizer_eq]
    exact hg
  have hC : conjSubgroup g (Subgroup.centralizer (V : Set G)) =
      Subgroup.centralizer (V : Set G) :=
    conjSubgroup_eq_self_iff.mpr (mem_normalizer_centralizer hgV)
  rw [conjSubgroup_inf, hX, hC]

theorem bigGe_mem_normalizer_Rbar {M V H : Subgroup G} {g : ↥M}
    (h : conjSubgroup (g : G) (xOf V H ⊓ Subgroup.centralizer (V : Set G)) =
      xOf V H ⊓ Subgroup.centralizer (V : Set G)) :
    (g : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  constructor
  · rintro ⟨ρ, hρ, hρk⟩
    refine ⟨g * ρ * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 : (g : G) * (ρ : G) * (g : G)⁻¹ ∈
          conjSubgroup (g : G) (xOf V H ⊓ Subgroup.centralizer (V : Set G)) := by
        rw [mem_conjSubgroup]
        have e : (g : G)⁻¹ * ((g : G) * (ρ : G) * (g : G)⁻¹) * (g : G) = (ρ : G) := by group
        rw [e]
        exact Subgroup.mem_subgroupOf.mp hρ
      rw [h] at h1
      simpa using h1
    · rw [← hρk]
      simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  · rintro ⟨ρ, hρ, hρk⟩
    refine ⟨g⁻¹ * ρ * g, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 : (ρ : G) ∈ conjSubgroup (g : G) (xOf V H ⊓ Subgroup.centralizer (V : Set G)) := by
        rw [h]
        exact Subgroup.mem_subgroupOf.mp hρ
      simpa using mem_conjSubgroup.mp h1
    · have e : (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M)) (g⁻¹ * ρ * g) =
          (g : Mbar M)⁻¹ * (QuotientGroup.mk' ((inSubgroup (pCore 2) M).subgroupOf M)) ρ *
            (g : Mbar M) := by
        simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [e, hρk]
      group

theorem bigGe_cov_of_comm {P W B : Subgroup G}
    (hcov : ∀ b ∈ B, b ∉ P → ∀ w ∈ P ⊓ W, ∃ p ∈ P, ⁅p, b⁆ = w) :
    ∀ p ∈ P ⊓ W, ∀ b ∈ B, b ∉ P → ∃ r ∈ P, r * b * r⁻¹ = p * b := by
  intro p hp b hb hbP
  obtain ⟨r, hr, hrb⟩ := hcov b hb hbP p hp
  refine ⟨r, hr, ?_⟩
  rw [commutatorElement_def] at hrb
  calc r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
    _ = p * b := by rw [hrb]

theorem bigGe_normalizer_le [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H) (hBne : B ≠ ⊥)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hcov : ∀ b ∈ B, b ∉ P → ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w)
    (hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H)
    (hδ : ∀ g ∈ M, ∀ w ∈ wOf V H, g * w * g⁻¹ ∈ Q ⊔ wOf V H → g * w * g⁻¹ ∈ wOf V H ⊔ P)
    (hNX : ∀ g ∈ M, conjSubgroup g (wOf V H) = wOf V H →
      conjSubgroup g (xOf V H) = xOf V H) :
    Subgroup.normalizer (WbarM M V H : Set (Mbar M)) ≤
      Subgroup.normalizer (RbarM M V H : Set (Mbar M)) := by
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hgM : (g : G) ∈ M := g.2
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hPM : P ≤ M := bigAlpha_P_le_M hc
  have hgW : ∀ w ∈ wOf V H, (g : G) * w * (g : G)⁻¹ ∈ wOf V H ⊔ P := fun w hw =>
    hδ _ hgM w hw (bigGe_mem_QW hQM hx hw (hWM hw))
  obtain ⟨r, hrP, hrB⟩ := bigGe_exists_conj_eq hc hBW hBP hPB hBne hBTI
    (bigGe_cov_of_comm hcov) hmem hgM hgW
  have hrM : r ∈ M := hPM hrP
  have hg'M : r⁻¹ * (g : G) ∈ M := M.mul_mem (M.inv_mem hrM) hgM
  have hg'B : conjSubgroup (r⁻¹ * (g : G)) B = B := by
    rw [conjSubgroup_mul, hrB, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hg'W := bigGe_conj_W hc hBW hBP hPB hBne hcov hg'M hg'B
  have hg'R := bigGe_conj_R hc hg'M (hNX _ hg'M hg'W)
  have hnorm : ((⟨r⁻¹ * (g : G), hg'M⟩ : ↥M) : Mbar M) ∈
      Subgroup.normalizer (RbarM M V H : Set (Mbar M)) :=
    bigGe_mem_normalizer_Rbar (g := ⟨r⁻¹ * (g : G), hg'M⟩) hg'R
  have hrQ : r ∈ inSubgroup (pCore 2) M := by
    rw [← hQM]
    exact hc.P_le_Q hrP
  have hr1 : ((⟨r, hrM⟩ : ↥M) : Mbar M) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hrQ
  have hclass : (g : Mbar M) = ((⟨r⁻¹ * (g : G), hg'M⟩ : ↥M) : Mbar M) := by
    have e : g = ⟨r, hrM⟩ * ⟨r⁻¹ * (g : G), hg'M⟩ := by
      apply Subtype.ext
      simp
    conv_lhs => rw [e]
    rw [QuotientGroup.mk_mul, hr1, one_mul]
  rw [hclass]
  exact hnorm

theorem bigEpsilonNormalizerGeStatement_of_delta (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hδ : BigDeltaStatement)
    (hNX : BigNormalizerXStatement) : BigEpsilonNormalizerGeStatement := by
  intro G _ _ M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨B, hBW, hBP, hPB, hBTI⟩ := bigBStatement_of_local hZ hN hIW G M V Q P H hH
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hT hTV
  obtain ⟨-, hFrat, -⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  have hCover := bigPCoverStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hT hTV
  have hBne : B ≠ ⊥ := by
    intro hB0
    obtain ⟨b₀, hb₀⟩ := exists_spForm_eq_one ha
    have hPB' := hPB
    rw [hB0, sup_bot_eq] at hPB'
    have h1 : ((Additive.toMul (ψ b₀) : ↥(wOf V H)) : G) ∈ P ⊓ wOf V H := by
      rw [hPB']
      exact (Additive.toMul (ψ b₀)).2
    have h2 := (hiff b₀).mp h1.1
    rw [hb₀] at h2
    exact one_ne_zero h2
  have hcov : ∀ b ∈ B, b ∉ P → ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w := by
    intro b hbB hbP w hw
    obtain ⟨β, hβ⟩ : ∃ β : Fin n ⊕ Fin n → GaloisField 2 f,
        ((Additive.toMul (ψ β) : ↥(wOf V H)) : G) = b :=
      ⟨ψ.symm (Additive.ofMul ⟨b, hBW hbB⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
    have hs : CaseM.spForm a β ≠ 0 := fun h => hbP (by rw [← hβ]; exact (hiff β).mpr h)
    obtain ⟨p, hp, hpb⟩ := hCover β hs w hw
    exact ⟨p, hp, by rw [← hβ]; exact hpb⟩
  have hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H :=
    fun p hp b hbB hbP hpb =>
      bigAlpha_mem_W hH hf hNat ha hT hTV hiff hRbar hxOf hFrat hp (hBW hbB) hbP hpb
  exact bigGe_normalizer_le hc hBW hBP hPB hBne hBTI hcov hmem (hδ G M V Q P H hH)
    (hNX G M V Q P H hH)

theorem bigEpsilonNormalizerGeStatement_of_delta_natural (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hδ : BigDeltaStatement) :
    BigEpsilonNormalizerGeStatement :=
  bigEpsilonNormalizerGeStatement_of_delta hZ hN hIW hδ (bigNormalizerXStatement_of_natural hZ hN)

end CFSG.RankThree.GF2n.Tim79a
