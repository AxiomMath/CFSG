module

public import CFSG.RankThree.GF2n.Tim79a34BigB
public import CFSG.RankThree.GF2n.Tim79a34BigAlpha
public import CFSG.RankThree.GF2n.Tim79a34BigAssembly

public section

namespace CFSG.RankThree.GF2n.Tim79a

section BigIdentStmt

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def BigIdentStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), BigEndHyp M V Q P H →
    Subgroup.center (Xbar V H) = ⊥ →
    ∀ B : Subgroup G, B ≤ wOf V H → B ⊓ P = ⊥ → (P ⊓ wOf V H) ⊔ B = wOf V H →
      (∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B) →
      ∀ g ∈ M, (∀ b ∈ B, ∀ w ∈ wOf V H, ⁅g * b * g⁻¹, w⁆ = 1) →
        conjSubgroup g B ≤ wOf V H ⊔ P

end BigIdentStmt

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section Natural

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem bigDelta_noncomm [Finite G] (hc : MinCex M V Q P H)
    (hNat : BigNatCfg V H hc.V_le_H Φ ψ) (ha : a ≠ 0) (hT : CaseM.IsTransGroup a T)
    (hTV : T.map Φ.toMonoidHom = Vy V H) {v : G} (hvV : v ∈ V) (hvW : v ∉ wOf V H)
    {β : Fin n ⊕ Fin n → GaloisField 2 f} (hs : CaseM.spForm a β ≠ 0) :
    v * ψG β ≠ ψG β * v := by
  intro hcomm
  obtain ⟨μ, hμ, hact⟩ := bigRW_conj_act_eq_trans hc.V_le_H hNat hT hTV hvV hvW
  have h1 := hact 1 1 (by rw [map_one, map_one]) β
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, map_one, Matrix.one_mulVec] at h1
  have h2 : v * ψG β * v⁻¹ = ψG β := by rw [hcomm]; group
  rw [h2] at h1
  have h3 := bigRW_psi_injective h1
  have h4 : (μ * CaseM.spForm a β) • a = 0 := by
    have := congrArg (fun y => y - β) h3
    simpa using this.symm
  rcases smul_eq_zero.mp h4 with h | h
  · exact (mul_eq_zero.mp h).elim hμ hs
  · exact ha h

theorem bigDelta_mem_VW [Finite G] (hH : BigEndHyp M V Q P H) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0)
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom) (hxOf : xOf V H = H)
    {p b : G} (hp : p ∈ P) (hbW : b ∈ wOf V H) (hbP : b ∉ P)
    (hpb : ⁅p, b⁆ ∈ V ⊓ wOf V H) : ∃ v ∈ V, v⁻¹ * p ∈ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hb2 : b * b = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hbW
  obtain ⟨β, hβ⟩ : ∃ β : Fin n ⊕ Fin n → GaloisField 2 f, ψG β = b :=
    ⟨ψ.symm (Additive.ofMul ⟨b, hbW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
  have hs : CaseM.spForm a β ≠ 0 := fun h => hbP (by rw [← hβ]; exact (hiff β).mpr h)
  obtain ⟨τ, hτ, hpX, hτp, hact⟩ := bigAlpha_act hc hNat hxOf hRbar hp
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcomm : ⁅p, b⁆ = ψG (SpExtras.mat n (GaloisField 2 f) τ *ᵥ β + β) := by
    rw [← bigRW_psi_mul, hact β, hβ, commutatorElement_def, hbinv]
  obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hT hTV
    (u := SpExtras.mat n (GaloisField 2 f) τ *ᵥ β + β)
    (by rw [← hcomm]; exact (Subgroup.mem_inf.mp hpb).1)
  obtain ⟨u₀, -, c, hparam⟩ := exists_spRad_param ha hτ
  have hu₀a : ∃ m : GaloisField 2 f, u₀ = m • a := by
    refine ⟨(CaseM.spForm a β)⁻¹ * (l - (CaseM.spForm u₀ β + c * CaseM.spForm a β)), ?_⟩
    rw [hparam β] at hl
    have h2 : (CaseM.spForm a β) • u₀ =
        (l - (CaseM.spForm u₀ β + c * CaseM.spForm a β)) • a := by
      linear_combination (norm := module) hl - bigRW_vec_add_self β
    calc u₀ = (CaseM.spForm a β)⁻¹ • ((CaseM.spForm a β) • u₀) := by
          rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = ((CaseM.spForm a β)⁻¹ * (l - (CaseM.spForm u₀ β + c * CaseM.spForm a β))) • a := by
          rw [h2, smul_smul]
  obtain ⟨m, hm⟩ := hu₀a
  have hmat : SpExtras.mat n (GaloisField 2 f) τ = CaseM.spTrans a c := by
    refine Matrix.ext_iff_mulVec.2 fun x => ?_
    rw [hparam x, hm, spTrans_mulVec, spForm_smul_left', smul_smul]
    have h2 := two_smul_vec_eq_zero ((m * CaseM.spForm a x) • a)
    linear_combination (norm := module) h2
  have hτT : τ ∈ T := (hT.1 τ).2 ⟨c, hmat⟩
  have hVy : xToXbar hVH ⟨p, hpX⟩ ∈ Vy V H := by
    rw [hτp, ← hTV]
    exact Subgroup.mem_map.mpr ⟨τ, hτT, rfl⟩
  exact bigAlpha_exists_of_mem_Vy hVH hpX hVy

end Natural

section Core

variable {G : Type} [Group G]

theorem bigDelta_conj_inf_Q {M Q P W B : Subgroup G}
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hBW : B ≤ W) (hBP : B ⊓ P = ⊥)
    (hQW : Q ⊓ W = P ⊓ W) {g z : G} (hg : g ∈ M) (hzB : z ∈ conjSubgroup g B) (hzQ : z ∈ Q) :
    z = 1 := by
  have hb : g⁻¹ * z * g ∈ B := mem_conjSubgroup.mp hzB
  have hq : g⁻¹ * z * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hMQ (M.inv_mem hg)) z).mp hzQ
    simpa using this
  have hqW : g⁻¹ * z * g ∈ Q ⊓ W := Subgroup.mem_inf.mpr ⟨hq, hBW hb⟩
  rw [hQW] at hqW
  have hbp : g⁻¹ * z * g ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hb, (Subgroup.mem_inf.mp hqW).1⟩
  rw [hBP, Subgroup.mem_bot] at hbp
  calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    _ = 1 := by rw [hbp]; group

theorem bigDelta_eq_one_of_centralizes {M V W B : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hVW : ¬ V ≤ W)
    (hnc : ∀ v ∈ V, v ∉ W → ∀ b ∈ B, b ≠ 1 → v * b ≠ b * v)
    {g z : G} (hg : g ∈ M) (hzB : z ∈ conjSubgroup g B)
    (hz : ∀ v ∈ V, z * v = v * z) : z = 1 := by
  obtain ⟨v₀, hv₀V, hv₀W⟩ := SetLike.not_le_iff_exists.mp hVW
  have hbB : g⁻¹ * z * g ∈ B := mem_conjSubgroup.mp hzB
  by_contra hz1
  have hb1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hv₁ : g * v₀ * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV hg) v₀).mp hv₀V
  apply hnc v₀ hv₀V hv₀W _ hbB hb1
  have h1 := hz _ hv₁
  calc v₀ * (g⁻¹ * z * g) = g⁻¹ * ((g * v₀ * g⁻¹) * z) * g := by group
    _ = g⁻¹ * (z * (g * v₀ * g⁻¹)) * g := by rw [h1]
    _ = (g⁻¹ * z * g) * v₀ := by group

theorem bigDelta_comm_centralizes {M V A : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hfix₁ : ∀ a ∈ A, m₁ * a * m₁⁻¹ = a) (hfix₂ : ∀ a ∈ A, m₂ * a * m₂⁻¹ = a)
    (hcomm₁ : ∀ v ∈ V, ⁅m₁, v⁆ ∈ A) (hcomm₂ : ∀ v ∈ V, ⁅m₂, v⁆ ∈ A) :
    ∀ z ∈ V, ⁅m₁, m₂⁆ * z = z * ⁅m₁, m₂⁆ := by
  intro z hz
  have hm : m₂ * m₁ ∈ M := M.mul_mem hm₂ hm₁
  obtain ⟨v, hvdef⟩ : ∃ v, v = (m₂ * m₁)⁻¹ * z * (m₂ * m₁) := ⟨_, rfl⟩
  have hv : v ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hm)) z).mp hz
    rw [hvdef]
    simpa using this
  have hzv : z = m₂ * (m₁ * v * m₁⁻¹) * m₂⁻¹ := by rw [hvdef]; group
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = ⁅m₁, v⁆ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, a₂ = ⁅m₂, v⁆ := ⟨_, rfl⟩
  have ha₁A : a₁ ∈ A := by rw [ha₁]; exact hcomm₁ v hv
  have ha₂A : a₂ ∈ A := by rw [ha₂]; exact hcomm₂ v hv
  have h1 : m₁ * v * m₁⁻¹ = a₁ * v := by rw [ha₁, commutatorElement_def]; group
  have h2 : m₂ * v * m₂⁻¹ = a₂ * v := by rw [ha₂, commutatorElement_def]; group
  have key : m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ = m₂ * (m₁ * v * m₁⁻¹) * m₂⁻¹ := by
    calc m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ = (m₁ * a₂ * m₁⁻¹) * (m₁ * v * m₁⁻¹) := by
          rw [h2]; group
      _ = a₂ * (a₁ * v) := by rw [hfix₁ _ ha₂A, h1]
      _ = (a₂ * a₁) * v := by rw [mul_assoc]
      _ = (a₁ * a₂) * v := by rw [hAcomm _ ha₂A _ ha₁A]
      _ = a₁ * (a₂ * v) := by rw [mul_assoc]
      _ = (m₂ * a₁ * m₂⁻¹) * (m₂ * v * m₂⁻¹) := by rw [hfix₂ _ ha₁A, h2]
      _ = m₂ * (m₁ * v * m₁⁻¹) * m₂⁻¹ := by rw [h1]; group
  have hconj : ⁅m₁, m₂⁆ * z * ⁅m₁, m₂⁆⁻¹ = z := by
    calc ⁅m₁, m₂⁆ * z * ⁅m₁, m₂⁆⁻¹
        = ⁅m₁, m₂⁆ * (m₂ * (m₁ * v * m₁⁻¹) * m₂⁻¹) * ⁅m₁, m₂⁆⁻¹ := by rw [← hzv]
      _ = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ := by simp only [commutatorElement_def]; group
      _ = m₂ * (m₁ * v * m₁⁻¹) * m₂⁻¹ := key
      _ = z := hzv.symm
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem bigDelta_good_W [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {b : G}
    (hb : b ∈ wOf V H) :
    (∀ a ∈ V ⊓ wOf V H, b * a * b⁻¹ = a) ∧ ∀ v ∈ V, ⁅b, v⁆ ∈ V ⊓ wOf V H := by
  refine ⟨fun a ha => ?_, fun v hv => ?_⟩
  · have := hc.wOf_comm hb (Subgroup.mem_inf.mp ha).2
    rw [this]
    group
  · have hbM : b ∈ M := wOf_le_M_of_minCex hc hb
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hbM
    have h1 : b * v * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hbN v).mp hv
    have h2 : v * b⁻¹ * v⁻¹ ∈ wOf V H :=
      (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H (hc.V_le_H hv)) _).mp
        ((wOf V H).inv_mem hb)
    have e : ⁅b, v⁆ = b * (v * b⁻¹ * v⁻¹) := by rw [commutatorElement_def]; group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact V.mul_mem h1 (V.inv_mem hv)
    · rw [e]
      exact (wOf V H).mul_mem hb h2

theorem bigDelta_good_conj [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {g b : G}
    (hg : g ∈ M) (hgA : ∀ a ∈ V ⊓ wOf V H, g * a * g⁻¹ ∈ V ⊓ wOf V H)
    (hgA' : ∀ a ∈ V ⊓ wOf V H, g⁻¹ * a * g ∈ V ⊓ wOf V H) (hb : b ∈ wOf V H) :
    g * b * g⁻¹ ∈ M ∧ (∀ a ∈ V ⊓ wOf V H, (g * b * g⁻¹) * a * (g * b * g⁻¹)⁻¹ = a) ∧
      ∀ v ∈ V, ⁅g * b * g⁻¹, v⁆ ∈ V ⊓ wOf V H := by
  obtain ⟨hfix, hcomm⟩ := bigDelta_good_W hc hb
  have hbM : b ∈ M := wOf_le_M_of_minCex hc hb
  refine ⟨M.mul_mem (M.mul_mem hg hbM) (M.inv_mem hg), fun a ha => ?_, fun v hv => ?_⟩
  · have h1 := hfix _ (hgA' a ha)
    calc (g * b * g⁻¹) * a * (g * b * g⁻¹)⁻¹ = g * (b * (g⁻¹ * a * g) * b⁻¹) * g⁻¹ := by group
      _ = a := by rw [h1]; group
  · have hgN : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact M.inv_mem hg
    have hvN : g⁻¹ * v * g ∈ V := by
      simpa using (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
    have e : ⁅g * b * g⁻¹, v⁆ = g * ⁅b, g⁻¹ * v * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hgA _ (hcomm _ hvN)

theorem bigDelta_comm_V [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {g b₁ b'' : G}
    (hg : g ∈ M) (hgA : ∀ a ∈ V ⊓ wOf V H, g * a * g⁻¹ ∈ V ⊓ wOf V H)
    (hgA' : ∀ a ∈ V ⊓ wOf V H, g⁻¹ * a * g ∈ V ⊓ wOf V H) (hb₁ : b₁ ∈ wOf V H)
    (hb'' : b'' ∈ wOf V H) :
    ∀ z ∈ V, ⁅b₁, g * b'' * g⁻¹⁆ * z = z * ⁅b₁, g * b'' * g⁻¹⁆ := by
  obtain ⟨hfix₁, hcomm₁⟩ := bigDelta_good_W hc hb₁
  obtain ⟨hm₂, hfix₂, hcomm₂⟩ := bigDelta_good_conj hc hg hgA hgA' hb''
  exact bigDelta_comm_centralizes (M := M) (V := V) (A := V ⊓ wOf V H) hc.normalizer_eq.ge
    (fun a ha a' ha' => hc.wOf_comm (Subgroup.mem_inf.mp ha).2 (Subgroup.mem_inf.mp ha').2)
    (wOf_le_M_of_minCex hc hb₁) hm₂ hfix₁ hfix₂ hcomm₁ hcomm₂

theorem bigDelta_comm_conj [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hQW : Q ⊓ wOf V H = P ⊓ wOf V H)
    (hBsup : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hnc : ∀ v ∈ V, v ∉ wOf V H → ∀ b ∈ B, b ≠ 1 → v * b ≠ b * v)
    {g : G} (hg : g ∈ M) (hgA : ∀ a ∈ V ⊓ wOf V H, g * a * g⁻¹ ∈ V ⊓ wOf V H)
    (hgA' : ∀ a ∈ V ⊓ wOf V H, g⁻¹ * a * g ∈ V ⊓ wOf V H)
    (hnorm : ∀ y ∈ wOf V H, ∀ z ∈ conjSubgroup g B, y * z * y⁻¹ ∈ conjSubgroup g B) :
    ∀ w ∈ wOf V H, ∀ z ∈ conjSubgroup g B, z * w = w * z := by
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.2
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hc.normalizer_eq.ge
  have hF : ∀ f ∈ P ⊓ wOf V H, ∀ z ∈ conjSubgroup g B, f * z = z * f := by
    intro f hf z hz
    have hfP : f ∈ P := (Subgroup.mem_inf.mp hf).1
    have hfW : f ∈ wOf V H := (Subgroup.mem_inf.mp hf).2
    have hzM : z ∈ M := by
      have hb : g⁻¹ * z * g ∈ B := mem_conjSubgroup.mp hz
      have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [e]
      exact M.mul_mem (M.mul_mem hg (hWM (hBW hb))) (M.inv_mem hg)
    have h1 : f * z * f⁻¹ * z⁻¹ ∈ conjSubgroup g B :=
      (conjSubgroup g B).mul_mem (hnorm f hfW z hz) ((conjSubgroup g B).inv_mem hz)
    have h2 : f * z * f⁻¹ * z⁻¹ ∈ Q := by
      have h3 : z * f⁻¹ * z⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hMQ hzM) _).mp (Q.inv_mem (hc.P_le_Q hfP))
      have e : f * z * f⁻¹ * z⁻¹ = f * (z * f⁻¹ * z⁻¹) := by group
      rw [e]
      exact Q.mul_mem (hc.P_le_Q hfP) h3
    have h4 := bigDelta_conj_inf_Q hMQ hBW hBP hQW hg h1 h2
    calc f * z = (f * z * f⁻¹ * z⁻¹) * z * f := by group
      _ = z * f := by rw [h4]; group
  have hB : ∀ b₁ ∈ B, ∀ z ∈ conjSubgroup g B, b₁ * z = z * b₁ := by
    intro b₁ hb₁ z hz
    have hb₁W : b₁ ∈ wOf V H := hBW hb₁
    have hb'' : g⁻¹ * z * g ∈ B := mem_conjSubgroup.mp hz
    have h1 : ⁅b₁, z⁆ ∈ conjSubgroup g B :=
      (conjSubgroup g B).mul_mem (hnorm b₁ hb₁W z hz) ((conjSubgroup g B).inv_mem hz)
    have h2 := bigDelta_comm_V hc hg hgA hgA' hb₁W (hBW hb'')
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h2
    have h3 : ⁅b₁, z⁆ = 1 :=
      bigDelta_eq_one_of_centralizes hMV hc.not_V_le_wOf hnc hg h1 (fun u hu => h2 u hu)
    exact commutatorElement_eq_one_iff_mul_comm.mp h3
  intro w hw z hz
  have hw' : w ∈ (P ⊓ wOf V H) ⊔ B := by
    rw [hBsup]
    exact hw
  obtain ⟨f, hf, b₁, hb₁, rfl⟩ := CFSG.RankThree.GF2n.Tim79a.exists_mul_of_mem_sup
    (fun s hs t ht => hc.wOf_comm (Subgroup.mem_inf.mp hs).2 (hBW ht)) hw'
  calc z * (f * b₁) = (z * f) * b₁ := by group
    _ = (f * z) * b₁ := by rw [hF f hf z hz]
    _ = f * (z * b₁) := by group
    _ = f * (b₁ * z) := by rw [hB b₁ hb₁ z hz]
    _ = (f * b₁) * z := by group

theorem bigDelta_normalizes {M B W : Subgroup G} (hWM : W ≤ M)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    {g b x : G} (hg : g ∈ M) (hb : b ∈ B) (hxdef : x = g * b * g⁻¹) (hx1 : x ≠ 1)
    (hyx : ∀ y ∈ W, y * x = x * y) :
    ∀ y ∈ W, ∀ z ∈ conjSubgroup g B, y * z * y⁻¹ ∈ conjSubgroup g B := by
  intro y hy z hz
  have hxg : x ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup, hxdef]
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    rw [e]
    exact hb
  have hxr : x ∈ conjSubgroup (y * g) B := by
    rw [mem_conjSubgroup]
    have h1 : y⁻¹ * x * y = x := by
      calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
        _ = y⁻¹ * (y * x) := by rw [hyx y hy]
        _ = x := by group
    have e : (y * g)⁻¹ * x * (y * g) = b := by
      calc (y * g)⁻¹ * x * (y * g) = g⁻¹ * (y⁻¹ * x * y) * g := by group
        _ = g⁻¹ * x * g := by rw [h1]
        _ = b := by rw [hxdef]; group
    rw [e]
    exact hb
  have hconj := bigAlpha_conj_eq hBTI hg (M.mul_mem (hWM hy) hg) hx1 hxg hxr
  have hmem : y * z * y⁻¹ ∈ conjSubgroup (y * g) B := by
    rw [conjSubgroup_mul, mem_conjSubgroup]
    have e : y⁻¹ * (y * z * y⁻¹) * y = z := by group
    rw [e]
    exact hz
  rw [← hconj] at hmem
  exact hmem

theorem bigDelta_comm_mem {A : Subgroup G} {p c b : G}
    (hcc : c * c = 1) (hbb : b * b = 1) (hcb : c * b = b * c)
    (hpc : ⁅p, c⁆ ∈ A) (hpp : p * p ∈ A)
    (hAb : ∀ a ∈ A, b * a = a * b) (hAc : ∀ a ∈ A, c * a = a * c)
    (hAp : ∀ a ∈ A, a * p = p * a)
    (hx : (p * c * b) * (p * c * b) = 1) : ⁅p, b⁆ ∈ A := by
  obtain ⟨a, ha⟩ : ∃ a, a = ⁅p, c⁆ := ⟨_, rfl⟩
  rw [← ha] at hpc
  have hpc' : p * c = a * c * p := by rw [ha, commutatorElement_def]; group
  have hbc : b * c = c * b := hcb.symm
  have hba : b * a = a * b := hAb a hpc
  have hca : c * a = a * c := hAc a hpc
  have hcbac : c * b * a * c = a * b := by
    calc c * b * a * c = c * (b * a) * c := by group
      _ = c * (a * b) * c := by rw [hba]
      _ = (c * a) * (b * c) := by group
      _ = (a * c) * (c * b) := by rw [hca, hbc]
      _ = a * (c * c) * b := by group
      _ = a * b := by rw [hcc]; group
  have h1 : p * a * b * p * b = 1 := by
    calc p * a * b * p * b = p * ((c * b * a * c) * p * b) := by rw [hcbac]; group
      _ = p * (c * b * (a * c * p) * b) := by group
      _ = p * (c * b * (p * c) * b) := by rw [hpc']
      _ = (p * c * b) * (p * c * b) := by group
      _ = 1 := hx
  have h2 : a * (p * b * p * b) = 1 := by
    calc a * (p * b * p * b) = (a * p) * b * p * b := by group
      _ = (p * a) * b * p * b := by rw [hAp a hpc]
      _ = 1 := h1
  have hpbpb : p * b * p * b = a⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hs' : (p * p)⁻¹ ∈ A := A.inv_mem hpp
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbs : b * (p * p)⁻¹ = (p * p)⁻¹ * b := hAb _ hs'
  have e : ⁅p, b⁆ = (p * b * p * b) * (b⁻¹ * (p * p)⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  have e2 : b⁻¹ * (p * p)⁻¹ * b⁻¹ = (p * p)⁻¹ := by
    rw [hbinv]
    calc b * (p * p)⁻¹ * b = (p * p)⁻¹ * b * b := by rw [hbs]
      _ = (p * p)⁻¹ := by rw [mul_assoc, hbb, mul_one]
  rw [e, hpbpb, e2]
  exact A.mul_mem (A.inv_mem hpc) hs'

theorem bigDelta_decompose [Finite G] {M V Q P H B C : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hBsup : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hQW : Q ⊓ wOf V H = P ⊓ wOf V H) (hCQ : C ≤ Q) (hPCQ : P ⊔ C = Q)
    {g x : G} (hg : g ∈ M) (hxg : x ∈ conjSubgroup g B) (hx : x ∈ Q ⊔ wOf V H) (hx1 : x ≠ 1) :
    ∃ p ∈ P, ∃ c ∈ C, ∃ b₀ ∈ B, b₀ ≠ 1 ∧ x = p * c * b₀ := by
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.2
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := hc.M_le_normalizer_P
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  obtain ⟨q₁, hq₁, w₀, hw₀, hxqw⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup
    (V := Q) (U := wOf V H) (fun w hw => hMQ (hWM hw)) hx
  have hw₀' : w₀ ∈ (P ⊓ wOf V H) ⊔ B := by
    rw [hBsup]
    exact hw₀
  obtain ⟨f₀, hf₀, b₀, hb₀, hwfb⟩ := CFSG.RankThree.GF2n.Tim79a.exists_mul_of_mem_sup
    (fun s hs t ht => hc.wOf_comm (Subgroup.mem_inf.mp hs).2 (hBW ht)) hw₀'
  have hf₀P : f₀ ∈ P := (Subgroup.mem_inf.mp hf₀).1
  obtain ⟨q', hq'Q, hxq⟩ : ∃ q' ∈ Q, x = q' * b₀ :=
    ⟨q₁ * f₀, Q.mul_mem hq₁ (hc.P_le_Q hf₀P), by rw [hxqw, hwfb]; group⟩
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    rw [h, mul_one] at hxq
    exact hx1 (bigDelta_conj_inf_Q hMQ hBW hBP hQW hg hxg (by rw [hxq]; exact hq'Q))
  have hCN : C ≤ Subgroup.normalizer (P : Set G) := fun c hc' => hMP (hQM (hCQ hc'))
  have hq'PC : q' ∈ P ⊔ C := by
    rw [hPCQ]
    exact hq'Q
  obtain ⟨p, hp, c, hcC, hq'pc⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hCN hq'PC
  exact ⟨p, hp, c, hcC, b₀, hb₀, hb₀1, by rw [hxq, hq'pc]⟩

theorem bigDelta_split [Finite G] {M V Q P H B C : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hFrat : inSubgroup frattini P = V ⊓ wOf V H)
    (hPC : ∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ V ⊓ wOf V H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c) (hCel : Assembly.IsElemAbelian 2 C)
    (hVW : ∀ p ∈ P, ∀ b ∈ B, b ≠ 1 → ⁅p, b⁆ ∈ V ⊓ wOf V H → ∃ v ∈ V, v⁻¹ * p ∈ wOf V H)
    {x p c b₀ : G} (hp : p ∈ P) (hcC : c ∈ C) (hb₀ : b₀ ∈ B) (hb₀1 : b₀ ≠ 1)
    (hxpcb : x = p * c * b₀) (hx2 : x * x = 1) :
    ∃ v ∈ V, ∃ u ∈ wOf V H, x = v * (u * c) ∧ x * v = v * x := by
  have hb₀W : b₀ ∈ wOf V H := hBW hb₀
  have hc2 : c * c = 1 := hCel.mul_self_eq_one hcC
  have hb₀2 : b₀ * b₀ = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hb₀W
  have hcb₀ : c * b₀ = b₀ * c := hCW c hcC b₀ hb₀W
  have hpp : p * p ∈ V ⊓ wOf V H := by
    have h1 : p ^ 2 ∈ inSubgroup frattini P := Tim78.sq_mem_inSubgroup_frattini hc.isPGroup_P hp
    rw [hFrat, sq] at h1
    exact h1
  have hAb : ∀ a ∈ V ⊓ wOf V H, b₀ * a = a * b₀ := fun a ha =>
    hc.wOf_comm hb₀W (Subgroup.mem_inf.mp ha).2
  have hAc : ∀ a ∈ V ⊓ wOf V H, c * a = a * c := fun a ha =>
    hCW c hcC a (Subgroup.mem_inf.mp ha).2
  have hAp : ∀ a ∈ V ⊓ wOf V H, a * p = p * a := fun a ha =>
    hc.commute_of_mem_P hp (Subgroup.mem_inf.mp ha).1
  have hcomm_mem : ⁅p, b₀⁆ ∈ V ⊓ wOf V H :=
    bigDelta_comm_mem hc2 hb₀2 hcb₀ (hPC p hp c hcC) hpp hAb hAc hAp (by rw [← hxpcb]; exact hx2)
  obtain ⟨v, hvV, hvW⟩ := hVW p hp b₀ hb₀ hb₀1 hcomm_mem
  obtain ⟨f, hfdef⟩ : ∃ f, f = v⁻¹ * p := ⟨_, rfl⟩
  have hfW : f ∈ wOf V H := by rw [hfdef]; exact hvW
  have hpvf : p = v * f := by rw [hfdef]; group
  have hu : f * b₀ ∈ wOf V H := (wOf V H).mul_mem hfW hb₀W
  have hu2 : (f * b₀) * (f * b₀) = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hu
  have hcu : c * (f * b₀) = (f * b₀) * c := hCW c hcC _ hu
  have hw₁2 : ((f * b₀) * c) * ((f * b₀) * c) = 1 := by
    calc (f * b₀) * c * ((f * b₀) * c) = (f * b₀) * (c * (f * b₀)) * c := by group
      _ = (f * b₀) * ((f * b₀) * c) * c := by rw [hcu]
      _ = ((f * b₀) * (f * b₀)) * (c * c) := by group
      _ = 1 := by rw [hu2, hc2, one_mul]
  have hxvw : x = v * ((f * b₀) * c) := by
    rw [hxpcb, hpvf]
    calc v * f * c * b₀ = v * f * (c * b₀) := by group
      _ = v * f * (b₀ * c) := by rw [hcb₀]
      _ = v * ((f * b₀) * c) := by group
  have hvv : v * v = 1 := hc.elemAb.mul_self_eq_one hvV
  have hvw : v * ((f * b₀) * c) = ((f * b₀) * c) * v := by
    have h1 : (v * ((f * b₀) * c))⁻¹ = v * ((f * b₀) * c) :=
      inv_eq_of_mul_eq_one_right (by rw [← hxvw]; exact hx2)
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hw₁2,
      inv_eq_of_mul_eq_one_right hvv] at h1
    exact h1.symm
  refine ⟨v, hvV, f * b₀, hu, hxvw, ?_⟩
  calc x * v = v * (((f * b₀) * c) * v) := by rw [hxvw]; group
    _ = v * (v * ((f * b₀) * c)) := by rw [← hvw]
    _ = v * x := by rw [← hxvw]

theorem bigDelta_mem_wOf_of_comm [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hnc : ∀ v ∈ V, v ∉ wOf V H → ∀ b ∈ B, b ≠ 1 → v * b ≠ b * v)
    {g b x v : G} (hg : g ∈ M) (hgA : ∀ a ∈ V ⊓ wOf V H, g * a * g⁻¹ ∈ V ⊓ wOf V H)
    (hb : b ∈ B) (hb1 : b ≠ 1) (hxdef : x = g * b * g⁻¹) (hvV : v ∈ V)
    (hxv : x * v = v * x) : v ∈ wOf V H := by
  by_contra hvn
  have hv'V : g⁻¹ * v * g ∈ V := by
    have hgN : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact M.inv_mem hg
    simpa using (Subgroup.mem_normalizer_iff.mp hgN v).mp hvV
  have hv'W : g⁻¹ * v * g ∉ wOf V H := by
    intro h
    apply hvn
    have h1 := hgA _ (Subgroup.mem_inf.mpr ⟨hv'V, h⟩)
    have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
    rw [e] at h1
    exact (Subgroup.mem_inf.mp h1).2
  apply hnc _ hv'V hv'W b hb hb1
  calc g⁻¹ * v * g * b = g⁻¹ * (v * (g * b * g⁻¹)) * g := by group
    _ = g⁻¹ * (v * x) * g := by rw [hxdef]
    _ = g⁻¹ * (x * v) * g := by rw [hxv]
    _ = b * (g⁻¹ * v * g) := by rw [hxdef]; group

theorem bigDelta_reduced [Finite G] {M V Q P H B C : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBP : B ⊓ P = ⊥) (hBsup : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hFrat : inSubgroup frattini P = V ⊓ wOf V H) (hQW : Q ⊓ wOf V H = P ⊓ wOf V H)
    (hCQ : C ≤ Q) (hPCQ : P ⊔ C = Q) (hPC : ∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ V ⊓ wOf V H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c) (hCel : Assembly.IsElemAbelian 2 C)
    (hnc : ∀ v ∈ V, v ∉ wOf V H → ∀ b ∈ B, b ≠ 1 → v * b ≠ b * v)
    (hVW : ∀ p ∈ P, ∀ b ∈ B, b ≠ 1 → ⁅p, b⁆ ∈ V ⊓ wOf V H → ∃ v ∈ V, v⁻¹ * p ∈ wOf V H)
    (hId : ∀ g ∈ M, (∀ b ∈ B, ∀ w ∈ wOf V H, ⁅g * b * g⁻¹, w⁆ = 1) →
      conjSubgroup g B ≤ wOf V H ⊔ P)
    {g b : G} (hg : g ∈ M) (hb : b ∈ B) (hx : g * b * g⁻¹ ∈ Q ⊔ wOf V H) :
    g * b * g⁻¹ ∈ wOf V H ⊔ P := by
  by_contra hxn
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := hc.M_le_normalizer_P
  have hAnorm : ∀ {m : G}, m ∈ M → ∀ a ∈ V ⊓ wOf V H, m * a * m⁻¹ ∈ V ⊓ wOf V H := by
    intro m hm a ha
    have h1 := mem_normalizer_inSubgroup_frattini (hMP hm)
    rw [hFrat] at h1
    exact (Subgroup.mem_normalizer_iff.mp h1 a).mp ha
  have hgA : ∀ a ∈ V ⊓ wOf V H, g * a * g⁻¹ ∈ V ⊓ wOf V H := hAnorm hg
  have hgA' : ∀ a ∈ V ⊓ wOf V H, g⁻¹ * a * g ∈ V ⊓ wOf V H := by
    intro a ha
    simpa using hAnorm (M.inv_mem hg) a ha
  obtain ⟨x, hxdef⟩ : ∃ x, x = g * b * g⁻¹ := ⟨_, rfl⟩
  rw [← hxdef] at hx hxn
  have hx1 : x ≠ 1 := by
    intro h
    apply hxn
    rw [h]
    exact (wOf V H ⊔ P).one_mem
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hx1
    rw [hxdef]
    group
  have hxg : x ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup, hxdef]
    have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    rw [e]
    exact hb
  have hx2 : x * x = 1 := by
    have h1 := hc.wOf_isElemAbelian.mul_self_eq_one (hBW hb)
    rw [hxdef]
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨p, hp, c, hcC, b₀, hb₀, hb₀1, hxpcb⟩ :=
    bigDelta_decompose hc hBW hBP hBsup hQW hCQ hPCQ hg hxg hx hx1
  obtain ⟨v, hvV, u, hu, hxvu, hxv⟩ :=
    bigDelta_split hc hBW hFrat hPC hCW hCel hVW hp hcC hb₀ hb₀1 hxpcb hx2
  have hvW := bigDelta_mem_wOf_of_comm hc hnc hg hgA hb hb1 hxdef hvV hxv
  have hw₂ : v * u ∈ wOf V H := (wOf V H).mul_mem hvW hu
  have hxw₂c : x = (v * u) * c := by rw [hxvu]; group
  have hyx : ∀ y ∈ wOf V H, y * x = x * y := by
    intro y hy
    rw [hxw₂c]
    calc y * (v * u * c) = (y * (v * u)) * c := by group
      _ = ((v * u) * y) * c := by rw [hc.wOf_comm hy hw₂]
      _ = (v * u) * (y * c) := by group
      _ = (v * u) * (c * y) := by rw [← hCW c hcC y hy]
      _ = (v * u * c) * y := by group
  have hnorm := bigDelta_normalizes hWM hBTI hg hb hxdef hx1 hyx
  have hcomm_all := bigDelta_comm_conj hc hBW hBP hQW hBsup hnc hg hgA hgA' hnorm
  have hconj_le : conjSubgroup g B ≤ wOf V H ⊔ P := by
    refine hId g hg (fun b' hb' w hw => ?_)
    have hz : g * b' * g⁻¹ ∈ conjSubgroup g B := by
      rw [mem_conjSubgroup]
      have e : g⁻¹ * (g * b' * g⁻¹) * g = b' := by group
      rw [e]
      exact hb'
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm_all w hw _ hz)
  exact hxn (hconj_le hxg)

theorem bigDelta_assemble [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hBsup : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hred : ∀ g ∈ M, ∀ b ∈ B, g * b * g⁻¹ ∈ Q ⊔ wOf V H → g * b * g⁻¹ ∈ wOf V H ⊔ P)
    {g : G} (hg : g ∈ M) {w : G} (hw : w ∈ wOf V H) (hx : g * w * g⁻¹ ∈ Q ⊔ wOf V H) :
    g * w * g⁻¹ ∈ wOf V H ⊔ P := by
  have hw' : w ∈ (P ⊓ wOf V H) ⊔ B := by
    rw [hBsup]
    exact hw
  obtain ⟨f, hf, b, hb, rfl⟩ := CFSG.RankThree.GF2n.Tim79a.exists_mul_of_mem_sup
    (fun s hs t ht => hc.wOf_comm (Subgroup.mem_inf.mp hs).2 (hBW ht)) hw'
  have hfP : f ∈ P := (Subgroup.mem_inf.mp hf).1
  have hgf : g * f * g⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hg) f).mp hfP
  have hsplit : g * (f * b) * g⁻¹ = (g * f * g⁻¹) * (g * b * g⁻¹) := by group
  have hx' : g * b * g⁻¹ ∈ Q ⊔ wOf V H := by
    have e : g * b * g⁻¹ = (g * f * g⁻¹)⁻¹ * (g * (f * b) * g⁻¹) := by group
    rw [e]
    exact (Q ⊔ wOf V H).mul_mem
      ((Q ⊔ wOf V H).inv_mem (Subgroup.mem_sup_left (hc.P_le_Q hgf))) hx
  have h1 := hred g hg b hb hx'
  rw [hsplit]
  exact (wOf V H ⊔ P).mul_mem (Subgroup.mem_sup_right hgf) h1

theorem bigDeltaStatement_of_ident (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (hId : BigIdentStatement) :
    BigDeltaStatement := by
  intro G _ _ M V Q P H hH g hgM w hw hwQ
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  obtain ⟨-, hFrat, -⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  obtain ⟨B, hBW, hBP, hBsup, hBTI⟩ := bigBStatement_of_local hZ hN hIW G M V Q P H hH
  obtain ⟨C, hCQ, hPCQ, hPC, hCW, -, -, hCel⟩ := hγ G M V Q P H hH hcentre
  have hQW : Q ⊓ wOf V H = P ⊓ wOf V H := bigQWStatement_of_natural hZ hN hIW hγ G M V Q P H hH
  have hbP : ∀ b ∈ B, b ≠ 1 → b ∉ P := by
    intro b hb hb1 hbP
    have h1 : b ∈ B ⊓ P := Subgroup.mem_inf.mpr ⟨hb, hbP⟩
    rw [hBP, Subgroup.mem_bot] at h1
    exact hb1 h1
  have hnc : ∀ v ∈ V, v ∉ wOf V H → ∀ b ∈ B, b ≠ 1 → v * b ≠ b * v := by
    intro v hv hvW b hb hb1
    obtain ⟨β, hβ⟩ := bigB_exists_psi (ψ := ψ) (hBW hb)
    have hs : CaseM.spForm a β ≠ 0 := fun h =>
      hbP b hb hb1 (by rw [← hβ]; exact (hiff β).mpr h)
    rw [← hβ]
    exact bigDelta_noncomm hc hNat ha hTT hTV hv hvW hs
  have hVW : ∀ p ∈ P, ∀ b ∈ B, b ≠ 1 → ⁅p, b⁆ ∈ V ⊓ wOf V H → ∃ v ∈ V, v⁻¹ * p ∈ wOf V H :=
    fun p hp b hb hb1 hpb =>
      bigDelta_mem_VW hH hf hNat ha hTT hTV hiff hRbar hxOf hp (hBW hb) (hbP b hb hb1) hpb
  have hId' := hId G M V Q P H hH hcentre B hBW hBP hBsup hBTI
  exact bigDelta_assemble hc hBW hBsup (fun g hg b hb hx =>
    bigDelta_reduced hc hBW hBP hBsup hBTI hFrat hQW hCQ hPCQ hPC hCW hCel hnc hVW hId' hg hb hx)
    hgM hw hwQ

end Core

end CFSG.RankThree.GF2n.Tim79a
