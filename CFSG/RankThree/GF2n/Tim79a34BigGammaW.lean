module

public import CFSG.RankThree.GF2n.Tim79a34BigB
public import CFSG.RankThree.GF2n.Tim79a34BigPAct
public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
import CFSG.RankThree.GF2n.Tim77Prop24Core

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

theorem eq_self_of_conj_transvection {n : ℕ} {F : Type} [Field F]
    {a b₀ : Fin n ⊕ Fin n → F}
    (hab : CaseM.spForm a b₀ = 1) (σ : (Fin n ⊕ Fin n → F) →+ (Fin n ⊕ Fin n → F))
    (hσa : ∀ l : F, σ (l • a) = l • a) (hσb : ∀ l : F, σ (l • b₀) = l • b₀)
    (hσP : ∀ u, CaseM.spForm a u = 0 → ∃ l : F, σ u = u + l • a)
    {μ μ' : F} (hμ : μ ≠ 0)
    (hconj : ∀ w, σ (w + (μ * CaseM.spForm b₀ w) • b₀) =
      σ w + (μ' * CaseM.spForm b₀ (σ w)) • b₀)
    (w : Fin n ⊕ Fin n → F) : σ w = w := by
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    rw [spForm_zero_right] at hab
    exact zero_ne_one hab
  have hba : CaseM.spForm b₀ a = -1 := by
    have h := CaseM.spForm_comm b₀ a
    rw [hab] at h
    have h' : - CaseM.spForm b₀ a = 1 := h.symm
    calc CaseM.spForm b₀ a = -(- CaseM.spForm b₀ a) := (neg_neg _).symm
      _ = -1 := by rw [h']
  have hμ' : μ' = μ := by
    have hσa1 : σ a = a := by simpa using hσa 1
    have h := hconj a
    rw [map_add, hσa1, hσb, hba] at h
    have h' : (μ * (-1 : F)) • b₀ = (μ' * (-1 : F)) • b₀ := add_left_cancel h
    simp only [mul_neg, mul_one, neg_smul, neg_inj] at h'
    exact ((smul_left_inj (M := Fin n ⊕ Fin n → F) hb₀0).mp h').symm
  have hfix : ∀ u, CaseM.spForm a u = 0 → σ u = u := by
    intro u hu
    obtain ⟨φ, hφ⟩ := hσP u hu
    have h := hconj u
    rw [map_add, hσb, hφ] at h
    have h' : (μ * CaseM.spForm b₀ u) • b₀ =
        (μ' * CaseM.spForm b₀ (u + φ • a)) • b₀ := add_left_cancel h
    rw [spForm_add_right, spForm_smul_right', hba, hμ'] at h'
    have h2 : μ * CaseM.spForm b₀ u = μ * (CaseM.spForm b₀ u + φ * (-1)) :=
      (smul_left_inj (M := Fin n ⊕ Fin n → F) hb₀0).mp h'
    have h5 : μ * (CaseM.spForm b₀ u + φ * (-1)) - μ * CaseM.spForm b₀ u = 0 := by
      rw [← h2]; ring
    have h3 : μ * φ = 0 := by
      rw [mul_add, mul_neg, mul_one, add_sub_cancel_left, mul_neg, neg_eq_zero] at h5
      exact h5
    rw [hφ, (mul_eq_zero.mp h3).resolve_left hμ, zero_smul, add_zero]
  have hperp : CaseM.spForm a (w - CaseM.spForm a w • b₀) = 0 := by
    rw [spForm_sub_right, spForm_smul_right', hab, mul_one, sub_self]
  calc σ w = σ ((w - CaseM.spForm a w • b₀) + CaseM.spForm a w • b₀) := by
        conv_lhs => rw [show w = (w - CaseM.spForm a w • b₀) + CaseM.spForm a w • b₀
          from (sub_add_cancel _ _).symm]
    _ = σ (w - CaseM.spForm a w • b₀) + σ (CaseM.spForm a w • b₀) := map_add _ _ _
    _ = (w - CaseM.spForm a w • b₀) + CaseM.spForm a w • b₀ := by rw [hfix _ hperp, hσb]
    _ = w := sub_add_cancel _ _

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem BigEndHyp.exists_gammaB_data [Finite G] (h : BigEndHyp M V Q P H) (ha : a ≠ 0) :
    ∃ (h₀ : ↥(xOf V H)) (g₁ : ↥(StatedSp n (GaloisField 2 f)))
      (b₀ : Fin n ⊕ Fin n → GaloisField 2 f),
      Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H h₀) = g₁ ∧ CaseM.spForm a b₀ = 1 ∧
        SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀ := by
  obtain ⟨b₀, hb₀⟩ := exists_spForm_eq_one ha
  have hb₀0 : b₀ ≠ 0 := by
    rintro rfl
    rw [spForm_zero_right] at hb₀
    exact zero_ne_one hb₀
  obtain ⟨g₁, hg₁⟩ := exists_mat_mulVec_eq_of_ne_zero ha hb₀0
  obtain ⟨h₀, hh₀⟩ := xToXbar_surjective h.setup.mc.toMinCex.V_le_H (Φ g₁)
  exact ⟨h₀, g₁, b₀, by rw [hh₀]; exact Φ.symm_apply_apply g₁, hb₀, hg₁⟩

theorem BigEndHyp.gammaB_spec [Finite G] (h : BigEndHyp M V Q P H) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {h₀ : ↥(xOf V H)} {g₁ : ↥(StatedSp n (GaloisField 2 f))}
    (hgh : Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H h₀) = g₁)
    {b₀ : Fin n ⊕ Fin n → GaloisField 2 f} (hb₀ : CaseM.spForm a b₀ = 1)
    (hg₁ : SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀)
    {B : Subgroup G} (hB : B = conjSubgroup (h₀ : G) V ⊓ wOf V H) :
    B ≤ wOf V H ∧ B ⊓ P = ⊥ ∧ (P ⊓ wOf V H) ⊔ B = wOf V H ∧
      (∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B) ∧ B ≠ ⊥ := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hxH : (h₀ : G) ∈ H := xOf_le_H hVH h₀.2
  have hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V :=
    bigB_psi_smul_mem hVH hNat ha hT hTV
  have hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a := fun u hu =>
    bigRW_eq_smul_of_psi_mem_V h hf hNat ha hT hTV hu
  have hact : ∀ l : GaloisField 2 f, (h₀ : G) * ψG (l • a) * (h₀ : G)⁻¹ = ψG (l • b₀) := by
    intro l
    have key := hNat.equiv h₀ (l • a)
    rw [hgh, Matrix.mulVec_smul, hg₁] at key
    exact key.symm
  have hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0 :=
    h.psi_mem_P_iff hf hNat ha hT hTV
  have hleM : conjSubgroup (h₀ : G) V ⊓ M ≤ wOf V H :=
    bigB_inf_M_le h hf hNat ha hT hTV hgh hb₀ hg₁
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hBeq : conjSubgroup (h₀ : G) V ⊓ wOf V H = conjSubgroup (h₀ : G) V ⊓ M :=
    le_antisymm (inf_le_inf_left _ hWM) (le_inf inf_le_left hleM)
  have hne : B ≠ ⊥ := by
    have hb₀0 : b₀ ≠ 0 := by
      rintro rfl
      rw [spForm_zero_right] at hb₀
      exact zero_ne_one hb₀
    have hmemB : ψG b₀ ∈ B := by
      rw [hB]
      exact (bigB_mem_iff (b₀ := b₀) hxH hmem hV hact (ψG b₀)).mpr ⟨1, by rw [one_smul]⟩
    intro hbot
    have h1 : ψG b₀ = 1 := by
      have h2 : ψG b₀ ∈ (⊥ : Subgroup G) := hbot ▸ hmemB
      simpa using h2
    exact hb₀0 (bigRW_psi_injective (by rw [h1, bigRW_psi_zero]))
  refine ⟨?_, ?_, ?_, ?_, hne⟩
  · rw [hB]; exact inf_le_right
  · rw [hB]; exact bigB_inf_P_eq_bot hxH hb₀ hiff hmem hV hact
  · rw [hB]; exact bigB_sup_eq hxH hb₀ hiff hmem hV hact
  · intro g hg
    rw [hB]
    exact bigB_isTI_of_eq_inf (isTI_conjSubgroup hc.ti (h₀ : G)) hBeq g hg

private theorem gammaB_sigma {x : G} (hxW : conjSubgroup x (wOf V H) = wOf V H) :
    ∃ (σ : (Fin n ⊕ Fin n → GaloisField 2 f) →+
      (Fin n ⊕ Fin n → GaloisField 2 f)),
      ∀ u, ψG (σ u) = x * ψG u * x⁻¹ := by
  let cx : ↥(wOf V H) →* ↥(wOf V H) :=
    { toFun := fun u => ⟨x * (u : G) * x⁻¹,
        (Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hxW) (u : G)).mp u.2⟩
      map_one' := by
        apply Subtype.ext
        show x * (1 : G) * x⁻¹ = 1
        group
      map_mul' := fun u v => by
        apply Subtype.ext
        show x * ((u : G) * (v : G)) * x⁻¹ = (x * (u : G) * x⁻¹) * (x * (v : G) * x⁻¹)
        group }
  let σ : (Fin n ⊕ Fin n → GaloisField 2 f) →+ (Fin n ⊕ Fin n → GaloisField 2 f) :=
    { toFun := fun u => ψ.symm (Additive.ofMul (cx (Additive.toMul (ψ u))))
      map_zero' := by
        simp [bigRW_psi_zero]
      map_add' := fun u v => by
        show ψ.symm (Additive.ofMul (cx (Additive.toMul (ψ (u + v))))) =
          ψ.symm (Additive.ofMul (cx (Additive.toMul (ψ u)))) +
          ψ.symm (Additive.ofMul (cx (Additive.toMul (ψ v))))
        rw [map_add, toMul_add, map_mul, ofMul_mul, map_add] }
  refine ⟨σ, fun u => ?_⟩
  show ((Additive.toMul (ψ (ψ.symm (Additive.ofMul (cx (Additive.toMul (ψ u))))))
    : ↥(wOf V H)) : G) = x * ψG u * x⁻¹
  rw [AddEquiv.apply_symm_apply]
  rfl

private theorem gammaB_sigma_fixed {h₀ : ↥(xOf V H)} {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    {x : G} {σ : (Fin n ⊕ Fin n → GaloisField 2 f) →+
      (Fin n ⊕ Fin n → GaloisField 2 f)}
    (hσψ : ∀ u, ψG (σ u) = x * ψG u * x⁻¹) (hxH : (h₀ : G) ∈ H)
    (hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V)
    (hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a)
    (hact : ∀ l : GaloisField 2 f, (h₀ : G) * ψG (l • a) * (h₀ : G)⁻¹ = ψG (l • b₀))
    (hxA : ∀ u ∈ V ⊓ wOf V H, x * u = u * x)
    (hxB : ∀ b ∈ conjSubgroup (h₀ : G) V ⊓ wOf V H, x * b = b * x) :
    (∀ l : GaloisField 2 f, σ (l • a) = l • a) ∧
      (∀ l : GaloisField 2 f, σ (l • b₀) = l • b₀) := by
  have hσ_fix : ∀ u, x * ψG u = ψG u * x → σ u = u := by
    intro u hcomm
    have h1 : ψG (σ u) = ψG u := by
      rw [hσψ u, hcomm]
      group
    exact bigRW_psi_injective h1
  have hσa : ∀ l : GaloisField 2 f, σ (l • a) = l • a := by
    intro l
    apply hσ_fix
    exact hxA _ (Subgroup.mem_inf.mpr ⟨hmem l, (Additive.toMul (ψ (l • a))).2⟩)
  have hb₀B : ∀ l : GaloisField 2 f,
      ψG (l • b₀) ∈ conjSubgroup (h₀ : G) V ⊓ wOf V H := by
    intro l
    exact (bigB_mem_iff (b₀ := b₀) hxH hmem hV hact (ψG (l • b₀))).mpr ⟨l, rfl⟩
  have hσb : ∀ l : GaloisField 2 f, σ (l • b₀) = l • b₀ := by
    intro l
    apply hσ_fix
    exact hxB _ (hb₀B l)
  exact ⟨hσa, hσb⟩

private theorem gammaB_sigma_perp [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {x : G} {σ : (Fin n ⊕ Fin n → GaloisField 2 f) →+ (Fin n ⊕ Fin n → GaloisField 2 f)}
    (hσψ : ∀ u, ψG (σ u) = x * ψG u * x⁻¹)
    (hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a)
    (hxP : ∀ u ∈ P ⊓ wOf V H, ⁅u, x⁆ ∈ V ⊓ wOf V H) :
    ∀ u, CaseM.spForm a u = 0 → ∃ l : GaloisField 2 f, σ u = u + l • a := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  intro u hu
  have huP : ψG u ∈ P := (h.psi_mem_P_iff hf hNat ha hT hTV u).mpr hu
  have huPW : ψG u ∈ P ⊓ wOf V H :=
    Subgroup.mem_inf.mpr ⟨huP, (Additive.toMul (ψ u)).2⟩
  have hz : ⁅ψG u, x⁆ ∈ V ⊓ wOf V H := hxP _ huPW
  obtain ⟨z, hzψ⟩ := bigB_exists_psi (ψ := ψ) (Subgroup.mem_inf.mp hz).2
  have hzV : ψG z ∈ V := by rw [hzψ]; exact (Subgroup.mem_inf.mp hz).1
  obtain ⟨l, hl⟩ := hV z hzV
  refine ⟨l, ?_⟩
  have hcomm : x * ψG u * x⁻¹ = ψG (u + l • a) := by
    have h1 : x * ψG u * x⁻¹ * (ψG u)⁻¹ = ψG (l • a) := by
      have e : x * ψG u * x⁻¹ * (ψG u)⁻¹ = (⁅ψG u, x⁆)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e, ← hzψ, hl]
      exact inv_eq_of_mul_eq_one_right (bigRW_psi_mul_self (l • a))
    calc x * ψG u * x⁻¹ = (x * ψG u * x⁻¹ * (ψG u)⁻¹) * ψG u := by group
      _ = ψG (l • a) * ψG u := by rw [h1]
      _ = ψG u * ψG (l • a) :=
          hc.wOf_comm (Additive.toMul (ψ (l • a))).2 (Additive.toMul (ψ u)).2
      _ = ψG (u + l • a) := bigRW_psi_mul u (l • a)
  have h2 : ψG (σ u) = ψG (u + l • a) := by rw [hσψ u, hcomm]
  exact bigRW_psi_injective h2

private theorem gammaB_conj_point [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {h₀ : ↥(xOf V H)} {g₁ : ↥(StatedSp n (GaloisField 2 f))}
    (hgh : Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H h₀) = g₁)
    {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    (hg₁ : SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀) :
    ∃ (y : G) (μ : GaloisField 2 f), μ ≠ 0 ∧ y ∈ conjSubgroup (h₀ : G) V ∧
      y ∉ wOf V H ∧
      ∀ w, y * ψG w * y⁻¹ = ψG (w + (μ * CaseM.spForm b₀ w) • b₀) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨v, hvV, hvW⟩ := SetLike.not_le_iff_exists.mp hc.not_V_le_wOf
  obtain ⟨μ, hμ, hact₀⟩ := bigRW_conj_act_eq_trans hVH hNat hT hTV hvV hvW
  set y : G := (h₀ : G) * v * (h₀ : G)⁻¹ with hy
  have hactv : ∀ w, y * ψG w * y⁻¹ =
      ψG (w + (μ * CaseM.spForm b₀ w) • b₀) := by
    intro w
    have h1 := hact₀ h₀ g₁ hgh w
    rw [hg₁, ← hy] at h1
    exact h1
  have hyU : y ∈ conjSubgroup (h₀ : G) V := by
    rw [mem_conjSubgroup, hy]
    have e : (h₀ : G)⁻¹ * ((h₀ : G) * v * (h₀ : G)⁻¹) * (h₀ : G) = v := by group
    rwa [e]
  have hyW : y ∉ wOf V H := by
    intro hyw
    apply hvW
    have hN : (h₀ : G)⁻¹ ∈ Subgroup.normalizer (wOf V H : Set G) :=
      (Subgroup.normalizer (wOf V H : Set G)).inv_mem
        (H_le_normalizer_wOf V H (xOf_le_H hVH h₀.2))
    have h1 : (h₀ : G)⁻¹ * y * (h₀ : G) ∈ wOf V H := by
      simpa using (Subgroup.mem_normalizer_iff.mp hN y).mp hyw
    rw [hy] at h1
    have e : (h₀ : G)⁻¹ * ((h₀ : G) * v * (h₀ : G)⁻¹) * (h₀ : G) = v := by group
    rwa [e] at h1
  exact ⟨y, μ, hμ, hyU, hyW, hactv⟩

private theorem gammaB_conj_second [Finite G] (h : BigEndHyp M V Q P H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {h₀ : ↥(xOf V H)} {g₁ : ↥(StatedSp n (GaloisField 2 f))}
    (hgh : Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H h₀) = g₁)
    {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    (hg₁ : SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀) {x y : G}
    (hBne : conjSubgroup (h₀ : G) V ⊓ wOf V H ≠ ⊥)
    (hxW : conjSubgroup x (wOf V H) = wOf V H)
    (hxB : ∀ b ∈ conjSubgroup (h₀ : G) V ⊓ wOf V H, x * b = b * x)
    (hyU : y ∈ conjSubgroup (h₀ : G) V) (hyW : y ∉ wOf V H) :
    ∃ (v' : G) (μ' : GaloisField 2 f), μ' ≠ 0 ∧ v' ∈ V ∧ v' ∉ wOf V H ∧
      (h₀ : G) * v' * (h₀ : G)⁻¹ = x * y * x⁻¹ ∧
      ∀ w, (x * y * x⁻¹) * ψG w * (x * y * x⁻¹)⁻¹ =
        ψG (w + (μ' * CaseM.spForm b₀ w) • b₀) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbU : (b : G) ∈ conjSubgroup (h₀ : G) V := (Subgroup.mem_inf.mp b.2).1
  have hb1G : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hxN : x ∈ Subgroup.normalizer (conjSubgroup (h₀ : G) V : Set G) :=
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hc.ti (h₀ : G)) hbU hb1G
      (hxB (b : G) b.2)
  have hzU : x * y * x⁻¹ ∈ conjSubgroup (h₀ : G) V :=
    (Subgroup.mem_normalizer_iff.mp hxN y).mp hyU
  let v' : G := (h₀ : G)⁻¹ * (x * y * x⁻¹) * (h₀ : G)
  have hv'V : v' ∈ V := mem_conjSubgroup.mp hzU
  have hzv' : (h₀ : G) * v' * (h₀ : G)⁻¹ = x * y * x⁻¹ := by
    show (h₀ : G) * ((h₀ : G)⁻¹ * (x * y * x⁻¹) * (h₀ : G)) * (h₀ : G)⁻¹ = x * y * x⁻¹
    group
  have hv'W : v' ∉ wOf V H := by
    intro hv'w
    apply hyW
    have hN : (h₀ : G) ∈ Subgroup.normalizer (wOf V H : Set G) :=
      H_le_normalizer_wOf V H (xOf_le_H hVH h₀.2)
    have h1 : (h₀ : G) * v' * (h₀ : G)⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp hN v').mp hv'w
    rw [hzv'] at h1
    have hNx : x⁻¹ ∈ Subgroup.normalizer (wOf V H : Set G) :=
      (Subgroup.normalizer (wOf V H : Set G)).inv_mem (conjSubgroup_eq_self_iff.mp hxW)
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ wOf V H := by
      simpa using (Subgroup.mem_normalizer_iff.mp hNx (x * y * x⁻¹)).mp h1
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [e] at h2
    exact h2
  obtain ⟨μ', hμ', hact'₀⟩ := bigRW_conj_act_eq_trans hVH hNat hT hTV hv'V hv'W
  have hact' : ∀ w, (x * y * x⁻¹) * ψG w * (x * y * x⁻¹)⁻¹ =
      ψG (w + (μ' * CaseM.spForm b₀ w) • b₀) := by
    intro w
    have h1 := hact'₀ h₀ g₁ hgh w
    rw [hg₁, hzv'] at h1
    exact h1
  exact ⟨v', μ', hμ', hv'V, hv'W, hzv', hact'⟩

private theorem gammaB_conj_eq {x y : G} {b₀ : Fin n ⊕ Fin n → GaloisField 2 f}
    {σ : (Fin n ⊕ Fin n → GaloisField 2 f) →+ (Fin n ⊕ Fin n → GaloisField 2 f)}
    {μ μ' : GaloisField 2 f}
    (hσψ : ∀ u, ψG (σ u) = x * ψG u * x⁻¹)
    (hactv : ∀ w, y * ψG w * y⁻¹ =
      ψG (w + (μ * CaseM.spForm b₀ w) • b₀))
    (hact' : ∀ w, (x * y * x⁻¹) * ψG w * (x * y * x⁻¹)⁻¹ =
      ψG (w + (μ' * CaseM.spForm b₀ w) • b₀)) :
    ∀ w, σ (w + (μ * CaseM.spForm b₀ w) • b₀) =
      σ w + (μ' * CaseM.spForm b₀ (σ w)) • b₀ := by
  intro w
  apply ψ.injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [hσψ (w + (μ * CaseM.spForm b₀ w) • b₀)]
  rw [← hactv w, ← hact' (σ w), hσψ w]
  group

theorem BigEndHyp.commute_wOf_of_commute_gammaB [Finite G] (h : BigEndHyp M V Q P H)
    (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    {h₀ : ↥(xOf V H)} {g₁ : ↥(StatedSp n (GaloisField 2 f))}
    (hgh : Φ.symm (xToXbar h.setup.mc.toMinCex.V_le_H h₀) = g₁)
    {b₀ : Fin n ⊕ Fin n → GaloisField 2 f} (hb₀ : CaseM.spForm a b₀ = 1)
    (hg₁ : SpExtras.mat n (GaloisField 2 f) g₁ *ᵥ a = b₀) {x : G}
    (hxW : conjSubgroup x (wOf V H) = wOf V H) (hxA : ∀ u ∈ V ⊓ wOf V H, x * u = u * x)
    (hxB : ∀ b ∈ conjSubgroup (h₀ : G) V ⊓ wOf V H, x * b = b * x)
    (hxP : ∀ u ∈ P ⊓ wOf V H, ⁅u, x⁆ ∈ V ⊓ wOf V H) :
    ∀ w ∈ wOf V H, x * w = w * x := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hxH : (h₀ : G) ∈ H := xOf_le_H hVH h₀.2
  have hmem : ∀ l : GaloisField 2 f, ψG (l • a) ∈ V :=
    bigB_psi_smul_mem hVH hNat ha hT hTV
  have hV : ∀ u, ψG u ∈ V → ∃ l : GaloisField 2 f, u = l • a := fun u hu =>
    bigRW_eq_smul_of_psi_mem_V h hf hNat ha hT hTV hu
  have hact : ∀ l : GaloisField 2 f, (h₀ : G) * ψG (l • a) * (h₀ : G)⁻¹ = ψG (l • b₀) := by
    intro l
    have key := hNat.equiv h₀ (l • a)
    rw [hgh, Matrix.mulVec_smul, hg₁] at key
    exact key.symm
  obtain ⟨σ, hσψ⟩ := gammaB_sigma hxW
  obtain ⟨hσa, hσb⟩ := gammaB_sigma_fixed hσψ hxH hmem hV hact hxA hxB
  have hσP := gammaB_sigma_perp h hf hNat ha hT hTV hσψ hV hxP
  have hBne : conjSubgroup (h₀ : G) V ⊓ wOf V H ≠ ⊥ :=
    (BigEndHyp.gammaB_spec (B := conjSubgroup (h₀ : G) V ⊓ wOf V H)
      h hf hNat ha hT hTV hgh hb₀ hg₁ rfl).2.2.2.2
  obtain ⟨y, μ, hμ, hyU, hyW, hactv⟩ := gammaB_conj_point h hNat hT hTV hgh hg₁
  obtain ⟨v', μ', hμ', hv'V, hv'W, hzv', hact'⟩ :=
    gammaB_conj_second h hNat hT hTV hgh hg₁ hBne hxW hxB hyU hyW
  have hconj := gammaB_conj_eq hσψ hactv hact'
  have hσid : ∀ u, σ u = u := fun u =>
    eq_self_of_conj_transvection hb₀ σ hσa hσb hσP hμ hconj u
  intro w hw
  obtain ⟨u, rfl⟩ := bigB_exists_psi (ψ := ψ) hw
  have h1 : x * ψG u * x⁻¹ = ψG u := by rw [← hσψ u, hσid u]
  calc x * ψG u = (x * ψG u * x⁻¹) * x := by group
    _ = ψG u * x := by rw [h1]

end CFSG.RankThree.GF2n.Tim79a

end
