module

public import CFSG.RankThree.PartOne.NF7H.DatumStmt
public import CFSG.RankThree.PartOne.NF7H.Main
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N1322
open scoped Matrix

theorem kf1322NF7U_of_hGA
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF1322NF7U := by
  intro G _ _ p _ A c L E h12 hF12 hF13 hT hEA hL hrow f v hv hv0
  classical
  have hp : p.Prime := h12.prime
  have hrow' := hrow
  obtain ⟨f₀, hf1, -, hmodel⟩ := hrow'
  have hZL : Subgroup.center ↥L = ⊥ :=
    KF132.psp_two_center_trivial hGA hf1 hF12.isQuasisimple_L hmodel
  have hG : Sec12TwoGeneric p c L E := KF132.sec12TwoGeneric_of_center_bot hF12 hZL
  have hcL : c ∉ L := h12.c_not_mem_of_generic hG
  have hcE : c ∈ E := h12.A_le_E h12.c_mem
  have hzc : Subgroup.zpowers c ⊓ L = ⊥ :=
    Sec12Three.zpowers_inf_eq_bot hp (Sec12Three.orderOf_c h12) hcL
  have hU := kf1322NF7Uinv_of_hGA hGA G p A c L E h12 hF12 hF13 hT hEA hL hrow
  have hspan : LinAlg.bsub f (Subgroup.zpowers c) = Submodule.span (ZMod p) {v} :=
    Sec127.bsub_zpowers_eq_span f hv
  set ι : (Fin 3 → ZMod p) → G := fun w => ((f (Multiplicative.ofAdd w) : E) : G) with hι
  have hι_add : ∀ w w', ι (w + w') = ι w * ι w' := by
    intro w w'
    simp [hι, ofAdd_add]
  have hι_sub : ∀ w w', ι (w - w') = ι w * (ι w')⁻¹ := by
    intro w w'
    simp [hι, ofAdd_sub, div_eq_mul_inv]
  have hι_nsmul : ∀ (n : ℕ) w, ι (n • w) = ι w ^ n := by
    intro n w
    show ((f (Multiplicative.ofAdd (n • w)) : E) : G) = ((f (Multiplicative.ofAdd w) : E) : G) ^ n
    rw [ofAdd_nsmul, map_pow, Subgroup.coe_pow]
  have hι_E : ∀ w, ι w ∈ E := fun w => (f (Multiplicative.ofAdd w)).2
  have hι_surj : ∀ g ∈ E, ∃ w, ι w = g := fun g hg =>
    ⟨Multiplicative.toAdd (f.symm ⟨g, hg⟩), by simp [hι]⟩
  have hι_inj : ∀ w w', ι w = ι w' → w = w' := by
    intro w w' h
    have : f (Multiplicative.ofAdd w) = f (Multiplicative.ofAdd w') := Subtype.ext h
    exact Multiplicative.ofAdd.injective (f.injective this)
  have hact : ∀ (x : G) (hx : x ∈ torusNormalizer E) (w : Fin 3 → ZMod p),
      ι (LinAlg.coordHom f (conjAut E x hx) w) = x * ι w * x⁻¹ := by
    intro x hx w
    exact LinAlg.wAction_apply f ⟨x, hx⟩ w
  have hmat : ∀ (σ : MulAut E) (w : Fin 3 → ZMod p),
      ((LinAlg.coordGL f σ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w =
        LinAlg.coordHom f σ w := fun σ w => LinAlg.coordGL_mulVec f σ w
  have hmem_span : ∀ z : Fin 3 → ZMod p, z ∈ Submodule.span (ZMod p) {v} ↔
      ι z ∈ Subgroup.zpowers c := by
    intro z
    rw [← hspan, LinAlg.mem_bsub]
  intro y hy u hu hsq hmod hstab l hl lam hlam
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨ν, hν, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hl
  obtain ⟨yy, hyy, hyyφ⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hφ)
  obtain ⟨uu, huuL, huu, huuν⟩ := Sec12Three.mem_torusImage_iff.1 hν
  obtain ⟨hh, hhL, hhW, hhψ⟩ := Sec12Three.mem_torusImage_iff.1 hψ
  have huuν' : conjAut E uu huu = ν := huuν
  have hhhψ' : conjAut E hh hhW = ψ := hhψ
  have huinv : ∀ f₁ ∈ E ⊓ L, uu * f₁ * uu⁻¹ = f₁⁻¹ := by
    intro f₁ hf₁
    obtain ⟨hf₁E, hf₁L⟩ := Subgroup.mem_inf.1 hf₁
    obtain ⟨w₁, hw₁⟩ := hι_surj f₁ hf₁E
    have h1 := hmod w₁
    rw [hmat, hmem_span, hι_add, ← huuν', hact uu huu w₁, hw₁] at h1
    have h2 : uu * f₁ * uu⁻¹ * f₁ ∈ Subgroup.zpowers c ⊓ L :=
      Subgroup.mem_inf.2 ⟨h1, L.mul_mem (L.mul_mem (L.mul_mem huuL hf₁L) (L.inv_mem huuL)) hf₁L⟩
    rw [hzc, Subgroup.mem_bot] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hvvW : yy * uu * yy⁻¹ ∈ torusNormalizer E :=
    (torusNormalizer E).mul_mem ((torusNormalizer E).mul_mem hyy huu)
      ((torusNormalizer E).inv_mem hyy)
  have hconj_v : conjAut E (yy * uu * yy⁻¹) hvvW = φ * ν * φ⁻¹ := by
    have h1 : (⟨yy * uu * yy⁻¹, hvvW⟩ : ↥(Subgroup.normalizer (E : Set G))) =
        ⟨yy, hyy⟩ * ⟨uu, huu⟩ * ⟨yy, hyy⟩⁻¹ := rfl
    have h2 : E.normalizerMonoidHom ⟨yy, hyy⟩ = φ := hyyφ
    have h3 : E.normalizerMonoidHom ⟨uu, huu⟩ = ν := huuν
    show E.normalizerMonoidHom ⟨yy * uu * yy⁻¹, hvvW⟩ = φ * ν * φ⁻¹
    rw [h1, map_mul, map_mul, map_inv, h2, h3]
  have hvvc : yy * uu * yy⁻¹ ∈ cNormalizer c := by
    refine Sec127.mem_cNormalizer_of_stabilizes f hv ⟨yy * uu * yy⁻¹, hvvW⟩ ?_
    obtain ⟨μ, hμ⟩ := hstab
    have h1 : LinAlg.wAction f ⟨yy * uu * yy⁻¹, hvvW⟩ v =
        LinAlg.coordHom f (φ * ν * φ⁻¹) v := by
      rw [← hconj_v]; rfl
    rw [h1, ← hmat, map_mul, map_mul, map_inv, hμ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have hvvL : yy * uu * yy⁻¹ ∈ Subgroup.normalizer (L : Set G) := hF12.twoB ⟨hvvc, hvvW⟩
  have hcancel : ∀ (A B : GL (Fin 3) (ZMod p)) (w : Fin 3 → ZMod p),
      ((A * B⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        ((B : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) =
        (A : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w := by
    intro A B w
    have h1 : ((B⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        ((B : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
  set k : ℤ := ((lam.val : ℕ) : ℤ) with hk
  have hkact : ∀ f₁ ∈ E ⊓ L, (yy * uu * yy⁻¹) * f₁ * (yy * uu * yy⁻¹)⁻¹ = hh * f₁ ^ k * hh⁻¹ := by
    intro f₁ hf₁
    obtain ⟨hf₁E, hf₁L⟩ := Subgroup.mem_inf.1 hf₁
    obtain ⟨w₁, hw₁⟩ := hι_surj f₁ hf₁E
    have h1 := hlam (((LinAlg.coordGL f ψ : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w₁)
    have hgm : LinAlg.coordGL f φ * LinAlg.coordGL f ν * (LinAlg.coordGL f φ)⁻¹ =
        LinAlg.coordGL f (φ * ν * φ⁻¹) := by simp [map_mul, map_inv]
    rw [hgm, hcancel, hmat, hmat, hmem_span, hι_sub] at h1
    have hlb : lam • LinAlg.coordHom f ψ w₁ = (lam.val) • LinAlg.coordHom f ψ w₁ := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [hlb, hι_nsmul, ← hhhψ', hact hh hhW w₁, ← hconj_v, hact _ hvvW w₁, hw₁] at h1
    have hvL : (yy * uu * yy⁻¹) * f₁ * (yy * uu * yy⁻¹)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hvvL f₁).1 hf₁L
    have hhL' : hh * f₁ * hh⁻¹ ∈ L := L.mul_mem (L.mul_mem hhL hf₁L) (L.inv_mem hhL)
    have h2 : (yy * uu * yy⁻¹) * f₁ * (yy * uu * yy⁻¹)⁻¹ * ((hh * f₁ * hh⁻¹) ^ lam.val)⁻¹ ∈
        Subgroup.zpowers c ⊓ L :=
      Subgroup.mem_inf.2 ⟨h1, L.mul_mem hvL (L.inv_mem (L.pow_mem hhL' _))⟩
    rw [hzc, Subgroup.mem_bot] at h2
    have h3 := mul_inv_eq_one.1 h2
    rw [h3, conj_pow, hk, zpow_natCast]
  have hfin := hU yy uu hyy huuL huu huinv (yy * uu * yy⁻¹) hvvc hvvW (fun e _ => rfl) hh hhL hhW k
    hkact
  have hcard : Nat.card ↥(E ⊓ L) = p ^ 2 := by
    rw [hEA]
    exact Sec12Three.card_A_inf_L h12 hG hcL
  obtain ⟨f₁, hf₁, hf₁ne⟩ : ∃ f₁ ∈ E ⊓ L, f₁ ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : E ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hno x hx)
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hf₁A : f₁ ∈ A := by
    rw [← hEA]
    exact (Subgroup.mem_inf.1 hf₁).1
  have hf₁p : f₁ ^ p = 1 := Sec12Three.pow_eq_one_of_mem_A h12 hf₁A
  have hord : orderOf f₁ = p := orderOf_eq_prime hf₁p hf₁ne
  have hz := hfin f₁ hf₁
  have h2 : f₁ ^ (k * k - 1) = 1 := by rw [zpow_sub_one, hz, mul_inv_cancel]
  have h3 : (orderOf f₁ : ℤ) ∣ k * k - 1 := orderOf_dvd_iff_zpow_eq_one.2 h2
  rw [hord] at h3
  have h4 : ((k * k - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
  have hkl : ((k : ℤ) : ZMod p) = lam := by simp [hk]
  push_cast at h4
  rw [hkl] at h4
  linear_combination h4

end CFSG.RankThree.PartOne.NF7H
