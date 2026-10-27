module

public import CFSG.RankThree.GF2n.Tim79a34BigEpsGe
public import CFSG.RankThree.GF2n.Tim79a34BigIWProof
public import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section CommutatorCover

variable {G : Type} [Group G] {M V Q P H : Subgroup G}

theorem BigEndHyp.exists_commutator_eq_of_not_mem_P [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {b : G} (hbW : b ∈ wOf V H) (hbP : b ∉ P) :
    ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  obtain ⟨β, hβ⟩ := bigB_exists_psi (ψ := ψ) hbW
  have hb : CaseM.spForm a β ≠ 0 := fun h0 => hbP (by
    rw [← hβ]
    exact (h.psi_mem_P_iff hf hNat ha hT hTV β).mpr h0)
  intro w hw
  obtain ⟨p, hp, hpw⟩ :=
    bigPCoverStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV β hb w hw
  exact ⟨p, hp, by rw [← hβ]; exact hpw⟩

end CommutatorCover

section Natural

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem conjSubgroup_xOf_eq_of_conjSubgroup_wOf_eq [Finite G] (hc : MinCex M V Q P H)
    (hNat : BigNatCfg V H hc.V_le_H Φ ψ) (ha : a ≠ 0) (haV : ψG a ∈ V) {g : G}
    (hgW : conjSubgroup g (wOf V H) = wOf V H) :
    conjSubgroup g (xOf V H) = xOf V H := by
  have hVH : V ≤ H := hc.V_le_H
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

private theorem mem_wOf_of_sq_mul [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hIW : cPbar V H P ≤ wOf V H) {p b : G} (hp : p ∈ P) (hbW : b ∈ wOf V H)
    (hbP : b ∉ P) (hpb : (p * b) * (p * b) = 1) : p ∈ wOf V H := by
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV
  obtain ⟨-, hFrat, -⟩ :=
    bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ hIW
  exact bigAlpha_mem_W h hf hNat ha hT hTV hiff hRbar hxOf hFrat hp hbW hbP hpb

private theorem exists_conj_fixing_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hIW : cPbar V H P ≤ wOf V H) {B : Subgroup G} (hBW : B ≤ wOf V H)
    (hBP : B ⊓ P = ⊥) (hWQ : ∀ w ∈ wOf V H, ∀ x ∈ Q, ⁅w, x⁆ ∈ P)
    {x : G} (hx : x ∈ Q) {b₁ : G} (hb₁B : b₁ ∈ B) (hb₁1 : b₁ ≠ 1) :
    ∃ r ∈ P, (r⁻¹ * x) * b₁ * (r⁻¹ * x)⁻¹ = b₁ := by
  have hb₁W : b₁ ∈ wOf V H := hBW hb₁B
  have hb₁P : b₁ ∉ P := by
    intro h1
    have hmem : b₁ ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hb₁B, h1⟩
    rw [hBP, Subgroup.mem_bot] at hmem
    exact hb₁1 hmem
  have hpP : ⁅x, b₁⁆ ∈ P := by
    rw [← commutatorElement_inv]
    exact P.inv_mem (hWQ b₁ hb₁W x hx)
  have hp2 : (⁅x, b₁⁆ * b₁) * (⁅x, b₁⁆ * b₁) = 1 := by
    have hb2 : b₁ * b₁ = 1 := h.setup.mc.toMinCex.wOf_isElemAbelian.mul_self_eq_one hb₁W
    have e : ⁅x, b₁⁆ * b₁ = x * b₁ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    have e2 : (x * b₁ * x⁻¹) * (x * b₁ * x⁻¹) = x * (b₁ * b₁) * x⁻¹ := by group
    rw [e2, hb2]
    group
  have hpW : ⁅x, b₁⁆ ∈ wOf V H :=
    mem_wOf_of_sq_mul h hZ hf hNat ha hT hTV hIW hpP hb₁W hb₁P hp2
  obtain ⟨r, hr, hrb⟩ :=
    h.exists_commutator_eq_of_not_mem_P hZ hb₁W hb₁P ⁅x, b₁⁆ ⟨hpP, hpW⟩
  refine ⟨r, hr, ?_⟩
  have h1 : x * b₁ * x⁻¹ = ⁅x, b₁⁆ * b₁ := by
    rw [commutatorElement_def]
    group
  have h2 : ⁅x, b₁⁆ * b₁ = r * b₁ * r⁻¹ := by
    rw [← hrb, commutatorElement_def]
    group
  calc (r⁻¹ * x) * b₁ * (r⁻¹ * x)⁻¹ = r⁻¹ * (x * b₁ * x⁻¹) * r := by group
    _ = r⁻¹ * (⁅x, b₁⁆ * b₁) * r := by rw [h1]
    _ = r⁻¹ * (r * b₁ * r⁻¹) * r := by rw [h2]
    _ = b₁ := by group

private theorem exists_mem_P_commute_of_mem_Q_aux [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hIW : cPbar V H P ≤ wOf V H) {B : Subgroup G} (hBW : B ≤ wOf V H)
    (hBP : B ⊓ P = ⊥)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hBne : B ≠ ⊥) (hWQ : ∀ w ∈ wOf V H, ∀ x ∈ Q, ⁅w, x⁆ ∈ P) {x : G} (hx : x ∈ Q) :
    ∃ r ∈ P, ∀ b ∈ B, (r⁻¹ * x) * b = b * (r⁻¹ * x) := by
  obtain ⟨⟨b₁, hb₁B⟩, hb₁ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb₁1 : b₁ ≠ 1 := fun h1 => hb₁ne (Subtype.ext h1)
  obtain ⟨r, hr, hrb₁⟩ :=
    exists_conj_fixing_of_mem_Q h hZ hf hNat ha hT hTV hIW hBW hBP hWQ hx hb₁B hb₁1
  refine ⟨r, hr, fun b hbB => ?_⟩
  have hQM : Q ≤ M := h.setup.mc.toMinCex.Q_le_M
  have hyQ : r⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem (h.setup.mc.toMinCex.P_le_Q hr)) hx
  have hyM : r⁻¹ * x ∈ M := hQM hyQ
  have hb₁y : b₁ ∈ conjSubgroup (r⁻¹ * x) B := by
    rw [mem_conjSubgroup]
    have e : (r⁻¹ * x)⁻¹ * b₁ * (r⁻¹ * x) = b₁ := by
      calc (r⁻¹ * x)⁻¹ * b₁ * (r⁻¹ * x)
          = (r⁻¹ * x)⁻¹ * ((r⁻¹ * x) * b₁ * (r⁻¹ * x)⁻¹) * (r⁻¹ * x) := by
              rw [hrb₁]
        _ = b₁ := by group
    rw [e]
    exact hb₁B
  have hyB : conjSubgroup (r⁻¹ * x) B = B := by
    have h := bigAlpha_conj_eq hBTI hyM (Subgroup.one_mem M) hb₁1 hb₁y
      (by rwa [conjSubgroup_one])
    rwa [conjSubgroup_one] at h
  have hyN : r⁻¹ * x ∈ Subgroup.normalizer (B : Set G) :=
    conjSubgroup_eq_self_iff.mp hyB
  have hmemB : ⁅r⁻¹ * x, b⁆ ∈ B := by
    rw [commutatorElement_def]
    exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN b).mp hbB) (B.inv_mem hbB)
  have hmemP : ⁅r⁻¹ * x, b⁆ ∈ P := by
    rw [← commutatorElement_inv]
    exact P.inv_mem (hWQ b (hBW hbB) (r⁻¹ * x) hyQ)
  have hone : ⁅r⁻¹ * x, b⁆ = 1 := by
    have hmem : ⁅r⁻¹ * x, b⁆ ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hmemB, hmemP⟩
    rwa [hBP, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hone

end Natural

section Closed

variable {G : Type} [Group G] {M V Q P H : Subgroup G}

theorem BigEndHyp.exists_mem_P_commute_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {B : Subgroup G} (hBW : B ≤ wOf V H)
    (hBP : B ⊓ P = ⊥) (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hBne : B ≠ ⊥) (hWQ : ∀ w ∈ wOf V H, ∀ x ∈ Q, ⁅w, x⁆ ∈ P) {x : G} (hx : x ∈ Q) :
    ∃ r ∈ P, ∀ b ∈ B, (r⁻¹ * x) * b = b * (r⁻¹ * x) := by
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  exact exists_mem_P_commute_of_mem_Q_aux h hZ hf ⟨hequiv, hpoint⟩ ha hT hTV
    (bigIWStatement_holds G M V Q P H h hZ) hBW hBP hBTI hBne hWQ hx

theorem BigEndHyp.conjSubgroup_wOf_eq_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hWQ : ∀ w ∈ wOf V H, ∀ x ∈ Q, ⁅w, x⁆ ∈ P) {x : G} (hx : x ∈ Q) :
    conjSubgroup x (wOf V H) = wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  obtain ⟨hiff, -, -, -⟩ :=
    bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV
  obtain ⟨B, hBW, hBP, hPB, hBTI⟩ := bigB_exists h hf hNat ha hT hTV hiff
  have hBne : B ≠ ⊥ := by
    intro hB0
    obtain ⟨b₀, hb₀⟩ := exists_spForm_eq_one ha
    rw [hB0, sup_bot_eq] at hPB
    have h1 : ((Additive.toMul (ψ b₀) : ↥(wOf V H)) : G) ∈ P ⊓ wOf V H := by
      rw [hPB]
      exact (Additive.toMul (ψ b₀)).2
    have h2 := (hiff b₀).mp h1.1
    rw [hb₀] at h2
    exact one_ne_zero h2
  have hcov : ∀ b ∈ B, b ∉ P → ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w :=
    fun b hbB hbP w hw => h.exists_commutator_eq_of_not_mem_P hZ (hBW hbB) hbP w hw
  obtain ⟨r, hr, hcomm⟩ :=
    h.exists_mem_P_commute_of_mem_Q hZ hBW hBP hBTI hBne hWQ hx
  have hQM : Q ≤ M := hc.Q_le_M
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hyM : r⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hPM hr)) (hQM hx)
  have hyB : conjSubgroup (r⁻¹ * x) B = B := by
    rw [conjSubgroup_eq_self_iff]
    exact Subgroup.centralizer_le_normalizer (B : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm b hb).symm)
  have hyW := bigGe_conj_W hc hBW hBP hPB hBne hcov hyM hyB
  have hx_eq : x = r * (r⁻¹ * x) := by group
  rw [hx_eq, conjSubgroup_mul, hyW]
  exact conjSubgroup_eq_self_iff.mpr (H_le_normalizer_wOf V H (hc.PleH hr))

theorem BigEndHyp.conjSubgroup_xOf_eq_of_mem_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hWQ : ∀ w ∈ wOf V H, ∀ x ∈ Q, ⁅w, x⁆ ∈ P) {x : G} (hx : x ∈ Q) :
    conjSubgroup x (xOf V H) = xOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  have haV : ((Additive.toMul (ψ a) : ↥(wOf V H)) : G) ∈ V := hpoint a T ha hT hTV
  exact conjSubgroup_xOf_eq_of_conjSubgroup_wOf_eq hc hNat ha haV
    (h.conjSubgroup_wOf_eq_of_mem_Q hZ hWQ hx)

end Closed

end CFSG.RankThree.GF2n.Tim79a
