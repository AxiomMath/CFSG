module

public import CFSG.RankThree.GF2n.Tim79a34BigB
public import CFSG.RankThree.GF2n.Tim79a34BigAssembly
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigAlpha_conj_sup_of_mem {P B : Subgroup G} {r : G} (hr : r ∈ P) :
    conjSubgroup r B ⊔ P = B ⊔ P := by
  have h1 : conjSubgroup r P = P := conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr)
  have h2 : conjSubgroup r (B ⊔ P) = B ⊔ P :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (Subgroup.mem_sup_right hr))
  calc conjSubgroup r B ⊔ P = conjSubgroup r B ⊔ conjSubgroup r P := by rw [h1]
    _ = conjSubgroup r (B ⊔ P) := (Subgroup.map_sup _ _ _).symm
    _ = B ⊔ P := h2

theorem bigAlpha_conj_eq {M B : Subgroup G}
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    {g r : G} (hg : g ∈ M) (hrM : r ∈ M) {x : G} (hx1 : x ≠ 1) (hxg : x ∈ conjSubgroup g B)
    (hxr : x ∈ conjSubgroup r B) : conjSubgroup g B = conjSubgroup r B := by
  have hk : r⁻¹ * g ∈ M := M.mul_mem (M.inv_mem hrM) hg
  have hb : r⁻¹ * x * r ∈ B := mem_conjSubgroup.mp hxr
  have hb2 : r⁻¹ * x * r ∈ conjSubgroup (r⁻¹ * g) B := by
    rw [mem_conjSubgroup]
    have h := mem_conjSubgroup.mp hxg
    have e : (r⁻¹ * g)⁻¹ * (r⁻¹ * x * r) * (r⁻¹ * g) = g⁻¹ * x * g := by group
    rw [e]
    exact h
  have hne : r⁻¹ * x * r ≠ 1 := by
    intro h
    apply hx1
    have e : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
    rw [e, h]
    group
  rcases hBTI _ hk with h | h
  · exfalso
    have hmem : r⁻¹ * x * r ∈ B ⊓ conjSubgroup (r⁻¹ * g) B := Subgroup.mem_inf.mpr ⟨hb, hb2⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  · calc conjSubgroup g B = conjSubgroup (r * (r⁻¹ * g)) B := by rw [mul_inv_cancel_left]
      _ = conjSubgroup r (conjSubgroup (r⁻¹ * g) B) := conjSubgroup_mul _ _ _
      _ = conjSubgroup r B := by rw [h]

theorem bigAlpha_P_le_M [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) : P ≤ M := by
  intro p hp
  have h : p ∈ inSubgroup (pCore 2) M := by
    rw [← hc.hQ]
    exact hc.P_le_Q hp
  exact (inSubgroup_pCore_two M).2.1 h

theorem bigAlpha_key [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hcov : ∀ p ∈ P ⊓ wOf V H, ∀ b ∈ B, b ∉ P → ∃ r ∈ P, r * b * r⁻¹ = p * b)
    (hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H)
    {g : G} (hg : g ∈ M) {x : G} (hxg : x ∈ conjSubgroup g B) (hxS : x ∈ P ⊔ B) (hxP : x ∉ P) :
    conjSubgroup g B ⊔ P = B ⊔ P := by
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
  have hconj := bigAlpha_conj_eq hBTI hg (hPM hr) hx1 hxg hxr
  rw [hconj]
  exact bigAlpha_conj_sup_of_mem hr

theorem bigAlpha_assemble [Finite G] {M V Q P H B : Subgroup G} (hc : MinCex M V Q P H)
    (hBW : B ≤ wOf V H) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hBTI : ∀ g ∈ M, B ⊓ conjSubgroup g B = ⊥ ∨ conjSubgroup g B = B)
    (hcov : ∀ p ∈ P ⊓ wOf V H, ∀ b ∈ B, b ∉ P → ∃ r ∈ P, r * b * r⁻¹ = p * b)
    (hmem : ∀ p ∈ P, ∀ b ∈ B, b ∉ P → (p * b) * (p * b) = 1 → p ∈ wOf V H)
    {g : G} (hg : g ∈ M) (hnot : ¬ ((wOf V H ⊔ P) ⊓ conjSubgroup g (wOf V H ⊔ P) ≤ P)) :
    conjSubgroup g (wOf V H ⊔ P) = wOf V H ⊔ P := by
  have hBM : B ≤ M := hBW.trans (wOf_le_M_of_minCex hc)
  have hWle : wOf V H ≤ B ⊔ P :=
    calc wOf V H = (P ⊓ wOf V H) ⊔ B := hPB.symm
      _ ≤ P ⊔ B := sup_le_sup_right inf_le_left B
      _ = B ⊔ P := sup_comm _ _
  have hSB : wOf V H ⊔ P = B ⊔ P :=
    le_antisymm (sup_le hWle le_sup_right)
      (sup_le (hBW.trans le_sup_left) le_sup_right)
  have hgP : conjSubgroup g P = P := conjSubgroup_eq_self_iff.mpr (hc.M_le_normalizer_P hg)
  have hSg : conjSubgroup g (B ⊔ P) = conjSubgroup g B ⊔ P :=
    calc conjSubgroup g (B ⊔ P) = conjSubgroup g B ⊔ conjSubgroup g P := Subgroup.map_sup _ _ _
      _ = conjSubgroup g B ⊔ P := by rw [hgP]
  have hBgN : conjSubgroup g B ≤ Subgroup.normalizer (P : Set G) := by
    intro z hz
    have h1 : g⁻¹ * z * g ∈ M := hBM (mem_conjSubgroup.mp hz)
    have e : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [e]
    exact hc.M_le_normalizer_P (M.mul_mem (M.mul_mem hg h1) (M.inv_mem hg))
  obtain ⟨y, hy, hyP⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨hyS, hyS'⟩ := Subgroup.mem_inf.mp hy
  rw [hSB] at hyS hyS'
  rw [hSg, sup_comm] at hyS'
  obtain ⟨p'', hp'', x, hx, hyx⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup hBgN hyS'
  have hxy : x = p''⁻¹ * y := by rw [hyx]; group
  have hxS : x ∈ P ⊔ B := by
    rw [hxy]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hp''))
      (by rw [sup_comm]; exact hyS)
  have hxP : x ∉ P := fun h => hyP (hyx ▸ P.mul_mem hp'' h)
  rw [hSB, hSg]
  exact bigAlpha_key hc hBW hBTI hcov hmem hg hx hxS hxP

theorem bigAlpha_sq_mul [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H) {v w : G}
    (hv : v ∈ V) (hwP : w ∈ P) (hwW : w ∈ wOf V H) : (v * w) * (v * w) = 1 := by
  have hv2 : v * v = 1 := hc.elemAb.mul_self_eq_one hv
  have hw2 : w * w = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hwW
  have hvw : v * w = w * v := hc.commute_of_mem_P hwP hv
  calc v * w * (v * w) = v * (w * v) * w := by group
    _ = v * (v * w) * w := by rw [← hvw]
    _ = (v * v) * (w * w) := by group
    _ = 1 := by rw [hv2, hw2, one_mul]

section Natural

variable {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem bigAlpha_exists_of_mem_Vy (hVH : V ≤ H) {p : G} (hpX : p ∈ xOf V H)
    (h : xToXbar hVH ⟨p, hpX⟩ ∈ Vy V H) : ∃ v ∈ V, v⁻¹ * p ∈ wOf V H := by
  obtain ⟨x, hxV, hx⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp h)
  refine ⟨(x : G), hxV, ?_⟩
  rw [coe_xToXbar] at hx
  have h1 : piBar V H (x⁻¹ * Subgroup.inclusion (xOf_le_H hVH) ⟨p, hpX⟩) = 1 := by
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  have h2 := (piBar_eq_one_iff _).mp h1
  simpa using h2

theorem bigAlpha_act [Finite G] (hc : MinCex M V Q P H)
    (hNat : BigNatCfg V H hc.V_le_H Φ ψ) (hxOf : xOf V H = H)
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom) {p : G} (hp : p ∈ P) :
    ∃ τ ∈ spRad a, ∃ hpX : p ∈ xOf V H, xToXbar hc.V_le_H ⟨p, hpX⟩ = Φ τ ∧
      ∀ v, ψG (SpExtras.mat n (GaloisField 2 f) τ *ᵥ v) = p * ψG v * p⁻¹ := by
  have hVH : V ≤ H := hc.V_le_H
  have hPH : P ≤ H := hc.PleH
  have hpX : p ∈ xOf V H := by
    rw [hxOf]
    exact hPH hp
  have hmemR : xToXbar hVH ⟨p, hpX⟩ ∈ Rbar V H P := by
    rw [mem_Rbar, coe_xToXbar]
    exact mem_barOf_iff.mpr ⟨⟨p, hPH hp⟩, hp, rfl⟩
  rw [hRbar] at hmemR
  obtain ⟨τ, hτ, hτp⟩ := Subgroup.mem_map.mp hmemR
  refine ⟨τ, hτ, hpX, hτp.symm, fun v => ?_⟩
  have hkey := hNat.equiv ⟨p, hpX⟩ v
  have hsymm : Φ.symm (xToXbar hVH ⟨p, hpX⟩) = τ := by
    rw [← hτp]
    exact Φ.symm_apply_apply τ
  rw [hsymm] at hkey
  exact hkey

theorem bigAlpha_mem_W [Finite G] (hH : BigEndHyp M V Q P H) (hf : 2 ^ f = qBar V H)
    (hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hTV : T.map Φ.toMonoidHom = Vy V H)
    (hiff : ∀ w, ψG w ∈ P ↔ CaseM.spForm a w = 0)
    (hRbar : Rbar V H P = (spRad a).map Φ.toMonoidHom) (hxOf : xOf V H = H)
    (hFrat : inSubgroup frattini P = V ⊓ wOf V H)
    {p b : G} (hp : p ∈ P) (hbW : b ∈ wOf V H) (hbP : b ∉ P) (hpb : (p * b) * (p * b) = 1) :
    p ∈ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hb2 : b * b = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hbW
  obtain ⟨β, hβ⟩ : ∃ β : Fin n ⊕ Fin n → GaloisField 2 f, ψG β = b :=
    ⟨ψ.symm (Additive.ofMul ⟨b, hbW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
  have hs : CaseM.spForm a β ≠ 0 := fun h => hbP (by rw [← hβ]; exact (hiff β).mpr h)
  obtain ⟨τ, hτ, hpX, hτp, hact⟩ := bigAlpha_act hc hNat hxOf hRbar hp
  have hpinv : p⁻¹ = b * p * b := inv_eq_of_mul_eq_one_right (by simpa [mul_assoc] using hpb)
  have hpp : p * p = ψG (SpExtras.mat n (GaloisField 2 f) τ *ᵥ β + β) := by
    rw [← bigRW_psi_mul, hact β, hβ, hpinv]
    have e : p * b * (b * p * b) * b = (p * (b * b)) * (p * (b * b)) := by group
    rw [e, hb2]
    group
  have hp2V : p * p ∈ V := by
    have h1 : p ^ 2 ∈ inSubgroup frattini P := Tim78.sq_mem_inSubgroup_frattini hc.isPGroup_P hp
    rw [hFrat] at h1
    rw [← sq]
    exact (Subgroup.mem_inf.mp h1).1
  obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hT hTV
    (u := SpExtras.mat n (GaloisField 2 f) τ *ᵥ β + β) (by rw [← hpp]; exact hp2V)
  obtain ⟨u₀, hu₀, c, hparam⟩ := exists_spRad_param ha hτ
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
  obtain ⟨v, hvV, hvW⟩ := bigAlpha_exists_of_mem_Vy hVH hpX hVy
  have hwP : v⁻¹ * p ∈ P := P.mul_mem (P.inv_mem (hc.V_le_P hvV)) hp
  have hp1 : p * p = 1 := by
    have h := bigAlpha_sq_mul hc hvV hwP hvW
    have e : v * (v⁻¹ * p) = p := by group
    rwa [e] at h
  have hz : SpExtras.mat n (GaloisField 2 f) τ *ᵥ β + β = 0 := by
    apply bigRW_psi_injective (ψ := ψ)
    rw [← hpp, hp1, bigRW_psi_zero]
  have hc0 : c = 0 := by
    rw [hmat, spTrans_mulVec] at hz
    have h1 : (c * CaseM.spForm a β) • a = 0 := by
      linear_combination (norm := module) hz - bigRW_vec_add_self β
    rcases smul_eq_zero.mp h1 with h | h
    · exact (mul_eq_zero.mp h).resolve_right hs
    · exact absurd h ha
  have hτ1 : τ = 1 := by
    apply SpExtras.mat_injective
    rw [hmat, hc0, spTrans_zero, map_one]
  have hx1 : xToXbar hVH ⟨p, hpX⟩ = 1 := by rw [hτp, hτ1, map_one]
  have hx1' : piBar V H (Subgroup.inclusion (xOf_le_H hVH) ⟨p, hpX⟩) = 1 := by
    rw [← coe_xToXbar hVH ⟨p, hpX⟩, hx1]
    rfl
  exact (piBar_eq_one_iff _).mp hx1'

end Natural

theorem bigAlphaStatement_of_local (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hB : BigBStatement) : BigAlphaStatement := by
  intro G _ _ M V Q P H hH g hg hnot
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨B, hBW, -, hPB, hBTI⟩ := hB G M V Q P H hH
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hT hTV
  obtain ⟨-, hFrat, -⟩ := bigPCommutatorStatement_holds hN G M V Q P H hH hcentre hcP
  have hCover := bigPCoverStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hT hTV
  refine bigAlpha_assemble hc hBW hPB hBTI ?_ ?_ hg hnot
  · intro p hpPW b hbB hbP
    have hbW : b ∈ wOf V H := hBW hbB
    obtain ⟨β, hβ⟩ : ∃ β : Fin n ⊕ Fin n → GaloisField 2 f,
        ((Additive.toMul (ψ β) : ↥(wOf V H)) : G) = b :=
      ⟨ψ.symm (Additive.ofMul ⟨b, hbW⟩), by rw [AddEquiv.apply_symm_apply]; rfl⟩
    have hs : CaseM.spForm a β ≠ 0 := fun h => hbP (by rw [← hβ]; exact (hiff β).mpr h)
    obtain ⟨r, hr, hrb⟩ := hCover β hs p hpPW
    refine ⟨r, hr, ?_⟩
    rw [hβ, commutatorElement_def] at hrb
    calc r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
      _ = p * b := by rw [hrb]
  · intro p hp b hbB hbP hpb
    exact bigAlpha_mem_W hH hf hNat ha hT hTV hiff hRbar hxOf hFrat hp (hBW hbB) hbP hpb

end CFSG.RankThree.GF2n.Tim79a
