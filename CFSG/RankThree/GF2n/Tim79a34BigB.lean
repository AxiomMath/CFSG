module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34BigPLocal
public import CFSG.RankThree.GF2n.Tim79a34BigWCentral
public import CFSG.RankThree.GF2n.Tim79aCitedSp62

public section

namespace CFSG.RankThree.GF2n.Tim79a

section BigBStmt

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def BigBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    ∃ B : Subgroup G, B ≤ wOf V H ∧ B ⊓ P = ⊥ ∧ (P ⊓ wOf V H) ⊔ B = wOf V H ∧
      ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B

end BigBStmt

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section Natural

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

omit Φ in
theorem bigB_exists_psi {y : G} (hy : y ∈ wOf V H) :
    ∃ u : Fin n ⊕ Fin n → GaloisField 2 f, ψG u = y :=
  ⟨ψ.symm (Additive.ofMul ⟨y, hy⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩

theorem bigB_psi_smul_mem (hVH : V ≤ H) (hNat : BigNatCfg V H hVH Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (l : GaloisField 2 f) : ψG (l • a) ∈ V := by
  by_cases hl : l = 0
  · rw [hl, zero_smul, bigRW_psi_zero]
    exact V.one_mem
  · exact hNat.point (l • a) T (smul_ne_zero hl ha) (CaseOADeg.isTransGroup_smul hl hT) hTV

omit Φ in
theorem bigB_mem_iff {x : G} (hxH : x ∈ H) {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    (hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V)
    (hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a)
    (hact : ∀ l : GaloisField 2 f, x * ψG (l • a) * x⁻¹ = ψG (l • b₀)) (y : G) :
    y ∈ conjSubgroup x V ⊓ wOf V H ↔ ∃ l : GaloisField 2 f, y = ψG (l • b₀) := by
  constructor
  · intro hy
    obtain ⟨hyV, hyW⟩ := Subgroup.mem_inf.mp hy
    have hyV' : x⁻¹ * y * x ∈ V := mem_conjSubgroup.mp hyV
    have hyW' : x⁻¹ * y * x ∈ wOf V H := by
      have := (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (H.inv_mem hxH)) y).mp hyW
      simpa using this
    obtain ⟨u, hu⟩ := bigB_exists_psi (ψ := ψ) hyW'
    obtain ⟨l, rfl⟩ := hV u (by rw [hu]; exact hyV')
    refine ⟨l, ?_⟩
    rw [← hact l, hu]
    group
  · rintro ⟨l, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, (Additive.toMul (ψ (l • b₀))).2⟩
    rw [mem_conjSubgroup, ← hact l]
    have e : x⁻¹ * (x * ψG (l • a) * x⁻¹) * x = ψG (l • a) := by group
    rw [e]
    exact hmem l

omit Φ in
theorem bigB_inf_P_eq_bot {x : G} (hxH : x ∈ H) {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    (hb₀ : CaseM.spForm a b₀ = 1) (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0)
    (hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V)
    (hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a)
    (hact : ∀ l : GaloisField 2 f, x * ψG (l • a) * x⁻¹ = ψG (l • b₀)) :
    (conjSubgroup x V ⊓ wOf V H) ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyB, hyP⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨l, rfl⟩ := (bigB_mem_iff hxH hmem hV hact y).mp hyB
  have h0 := (hiff (l • b₀)).mp hyP
  rw [spForm_smul_right', hb₀, mul_one] at h0
  rw [h0, zero_smul, bigRW_psi_zero]
  exact Subgroup.one_mem _

omit Φ in
theorem bigB_sup_eq {x : G} (hxH : x ∈ H) {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    (hb₀ : CaseM.spForm a b₀ = 1) (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0)
    (hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V)
    (hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a)
    (hact : ∀ l : GaloisField 2 f, x * ψG (l • a) * x⁻¹ = ψG (l • b₀)) :
    (P ⊓ wOf V H) ⊔ (conjSubgroup x V ⊓ wOf V H) = wOf V H := by
  refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
  intro y hy
  obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) hy
  have h1 : ψG (u - CaseM.spForm a u • b₀) ∈ P ⊓ wOf V H := by
    refine Subgroup.mem_inf.mpr ⟨(hiff _).mpr ?_, (Additive.toMul (ψ _)).2⟩
    rw [spForm_sub_right, spForm_smul_right', hb₀, mul_one, sub_self]
  have h2 : ψG (CaseM.spForm a u • b₀) ∈ conjSubgroup x V ⊓ wOf V H :=
    (bigB_mem_iff hxH hmem hV hact _).mpr ⟨_, rfl⟩
  have h3 : ψG u = ψG (u - CaseM.spForm a u • b₀) * ψG (CaseM.spForm a u • b₀) := by
    rw [bigRW_psi_mul, sub_add_cancel]
  rw [h3]
  exact Subgroup.mul_mem_sup h1 h2

theorem bigB_inf_M_le [Finite G] (hH : BigEndHyp M V Q P H) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {h : ↥(xOf V H)} {g₁ : ↥(StatedSp n (GaloisField 2 f))}
    (hgh : Φ.symm (xToXbar hH.setup.mc.toMinCex.V_le_H h) = g₁)
    {b₀ : Fin n ⊕ Fin n → GaloisField 2 f} (hb₀ : CaseM.spForm a b₀ = 1)
    (hg₁ : SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀) :
    conjSubgroup (h : G) V ⊓ M ≤ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  intro y hy
  obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.mp hy
  have hv : (h : G)⁻¹ * y * (h : G) ∈ V := mem_conjSubgroup.mp hyU
  have e : (h : G) * ((h : G)⁻¹ * y * (h : G)) * (h : G)⁻¹ = y := by group
  by_cases hvW : (h : G)⁻¹ * y * (h : G) ∈ wOf V H
  · have h1 := (Subgroup.mem_normalizer_iff.mp
      (H_le_normalizer_wOf V H (xOf_le_H hVH h.2)) _).mp hvW
    rwa [e] at h1
  · exfalso
    obtain ⟨μ, hμ, hact⟩ := bigRW_conj_act_eq_trans hVH hNat hT hTV hv hvW
    have h1 := hact h g₁ hgh a
    rw [hg₁, e] at h1
    have haV : ψG a ∈ V := by
      simpa using bigB_psi_smul_mem hVH hNat ha hT hTV 1
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hyM
    have hyV : y * ψG a * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN _).mp haV
    rw [h1] at hyV
    obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hT hTV hyV
    have h2 := congrArg (CaseM.spForm a) hl
    rw [spForm_add_right, spForm_smul_right', spForm_smul_right', CaseM.spForm_self, hb₀,
      CaseM.spForm_comm a b₀, hb₀] at h2
    apply hμ
    linear_combination -h2

omit Φ in
theorem bigB_isTI_of_eq_inf [Finite G] {U M B : Subgroup G} (hU : IsTI U) (hB : B = U ⊓ M) :
    ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B := by
  intro g hg
  have hgM : conjSubgroup g M = M := conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
  have hBg : conjSubgroup g B = conjSubgroup g U ⊓ M := by
    rw [hB, conjSubgroup_inf, hgM]
  by_cases hbot : B ⊓ conjSubgroup g B = ⊥
  · exact Or.inl hbot
  · right
    have hne : U ⊓ conjSubgroup g U ≠ ⊥ := by
      intro h0
      apply hbot
      rw [eq_bot_iff, ← h0]
      refine inf_le_inf ?_ ?_
      · rw [hB]
        exact inf_le_left
      · rw [hBg]
        exact inf_le_left
    have hUg : conjSubgroup g U = U := conjSubgroup_eq_of_isTI hU hne
    rw [hBg, hUg, hB]

theorem bigB_exists [Finite G] (hH : BigEndHyp M V Q P H) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0) :
    ∃ B : Subgroup G, B ≤ wOf V H ∧ B ⊓ P = ⊥ ∧ (P ⊓ wOf V H) ⊔ B = wOf V H ∧
      ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨b₀, hb₀⟩ := exists_spForm_eq_one ha
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    rw [spForm_zero_right] at hb₀
    exact zero_ne_one hb₀
  obtain ⟨g₁, hg₁⟩ := exists_mat_mulVec_eq_of_ne_zero ha hb₀0
  obtain ⟨h, hh⟩ := xToXbar_surjective hVH (Φ g₁)
  have hgh : Φ.symm (xToXbar hVH h) = g₁ := by
    rw [hh]
    exact Φ.symm_apply_apply g₁
  have hmem := bigB_psi_smul_mem hVH hNat ha hT hTV
  have hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a := fun u hu =>
    bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hT hTV hu
  have hact : ∀ l : GaloisField 2 f, (h : G) * ψG (l • a) * (h : G)⁻¹ = ψG (l • b₀) := by
    intro l
    have key := hNat.equiv h (l • a)
    rw [hgh, Matrix.mulVec_smul, hg₁] at key
    exact key.symm
  have hxH : (h : G) ∈ H := xOf_le_H hVH h.2
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hle := bigB_inf_M_le hH hf hNat ha hT hTV hgh hb₀ hg₁
  have hBeq : conjSubgroup (h : G) V ⊓ wOf V H = conjSubgroup (h : G) V ⊓ M :=
    le_antisymm (inf_le_inf_left _ hWM) (le_inf inf_le_left hle)
  refine ⟨conjSubgroup (h : G) V ⊓ wOf V H, inf_le_right,
    bigB_inf_P_eq_bot hxH hb₀ hiff hmem hV hact, bigB_sup_eq hxH hb₀ hiff hmem hV hact, ?_⟩
  exact bigB_isTI_of_eq_inf (isTI_conjSubgroup hc.ti (h : G)) hBeq

end Natural

theorem bigBStatement_of_local (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) : BigBStatement := by
  intro G _ _ M V Q P H hH
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hiff := (bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV).1
  exact bigB_exists hH hf hNat ha hTT hTV hiff

end CFSG.RankThree.GF2n.Tim79a
