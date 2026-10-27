module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

structure Cfg619 (T L V H : Subgroup G) (n : ℕ) (y : G) : Prop where
  elemAbelian : IsElemAbelian 2 (conjClosure V H)
  relIndex_B : (conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)).relIndex
    (conjClosure V H) = 2
  relIndex_F : (conjSub y V ⊓ Subgroup.normalizer (V : Set G)).relIndex (conjSub y V) = 2
  commutator_EB : ⁅conjSub y V, conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G)⁆ =
    conjSub y (ch6ZS T L V)
  commutator_VF : ⁅V, conjSub y V ⊓ Subgroup.normalizer (V : Set G)⁆ = ch6ZS T L V
  ne : conjSub y (ch6ZS T L V) ≠ ch6ZS T L V
  le_centralizer : conjSub y V ≤ Subgroup.centralizer (ch6ZS T L V : Set G)
  le_H : conjSub y V ≤ H
  not_le_pCoreOf : ¬ conjSub y V ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))
  conjClosure_le : conjClosure V H ≤ Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G)
  n_eq : n = 2

namespace Hyp6116

theorem exists_cfg619 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h615 : Stmt6_1_5)
    (h6110 : Stmt6_1_10) (h6112 : Stmt6_1_12) (h : Hyp6116 G T M L V n)
    (hH : IsInHS T M L V H) (hHs : IsHStar T M H)
    (hodd : Odd (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V)) : ∃ y : G, Cfg619 T L V H n y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := h.amalgamHypV h432 hH
  have hV1 : V ≠ ⊥ := h.toHyp611.ne_bot
  have hVel := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVel
  have hN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  have h₂ : H ≤ L ⊔ T ⊔ H := le_sup_right
  have hb1 : 1 < critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := stmt6_1_18 h432 G T M L V n h H hH
  have hb3 : 3 ≤ critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by obtain ⟨k, hk⟩ := hodd; omega
  have hTH := h.isSylowTwoOf hH
  have hHZ := h.le_normalizer_ZS hH
  have hAγ₁ : Vv V (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = conjClosure V H := Vv_γ₁ h₂ hN
  have hVA : V ≤ conjClosure V H := le_conjClosure V H
  have hAel : IsElemAbelian 2 (conjClosure V H) := by
    rw [← hAγ₁]
    exact isElemAbelian_Vv_γ₁ hyp hV1 (by omega)
  have hA2 : IsPGroup 2 (conjClosure V H) := B2F.isPGroup_of_isElemAbelian hAel
  obtain ⟨hUM, hnotN⟩ := h.isUniqueMaxOver_normalizer h331 h432 h615 hHs
  have hc : E1.nParam H = 1 := h.nParam_eq_one H hHs
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex hyp hV1
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
  have hstabγ : stab γ = conjSub (g : G) H := by rw [hg, stab_smul, stab_γ₁ h₂]
  have hVvγ : Vv V γ = conjSub (g : G) (conjClosure V H) := by rw [hg, Vv_smul hN, hAγ₁]
  obtain ⟨⟨γ', hγ'n, hdγ'⟩, ⟨γ₂, hγ₂n, hdγ₂⟩⟩ :=
    exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega)
  have hAstab : conjClosure V H ≤ conjSub (g : G) H := by
    have := (Vv_γ₁_le_pCoreOf_stab_inf hyp hV1 hγ'n hdγ').trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    rw [hAγ₁] at this
    exact this.trans (inf_le_right.trans hstabγ.le)
  have hUγH : conjSub (g : G) (conjClosure V H) ≤ H := by
    have := (Vv_le_pCoreOf_stab_inf hyp hV1 hγ₂n hdγ₂).trans
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    rw [hVvγ, stab_γ₁ h₂] at this
    exact this.trans inf_le_left
  have hAZγ := h.conjClosure_le_centralizer_conjSub h6112 hH (g : G) hAstab
  have hUγZ : conjSub (g : G) (conjClosure V H) ≤
      Subgroup.centralizer (ch6ZS T L V : Set G) := by
    have h1 : conjClosure V H ≤ conjSub (g : G)⁻¹ H := (conjSub_le_iff (g : G)).mp hUγH
    have h2 := h.conjClosure_le_centralizer_conjSub h6112 hH (g : G)⁻¹ h1
    have h3 := conjSub_mono (g : G) h2
    rwa [conjSub_centralizer', conjSub_inv_conjSub] at h3
  have hA₂ : ¬ conjClosure V H ≤ ballStab 1 γ := fun hle => hγ.not_le (hVA.trans hle)
  obtain ⟨α, hαn, hα2⟩ := exists_nbr_relIndex_two hyp hV1 hγ hb3 hodd hUM hc hAγ₁.ge hA₂
  have hgα : (g⁻¹ • α) ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj (g⁻¹)).mpr hαn
    rwa [hg, inv_smul_smul] at this
  obtain ⟨k, hk, hkα⟩ :=
    stab_transitive_on_nbrs (γ := γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
      (show γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁.symm) hgα
  have hkH : ((k : ↥(L ⊔ T ⊔ H)) : G) ∈ H := by rwa [stab_γ₁ h₂] at hk
  have hαy : α = (g * k) • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by
    rw [mul_smul, hkα, smul_inv_smul]
  set y : G := ((g * k : ↥(L ⊔ T ⊔ H)) : G) with hy
  have hE : Vv V α = conjSub y V := by rw [hαy, Vv_smul_γ₀ hN]
  have hZy : conjSub y (ch6ZS T L V) = conjSub (g : G) (ch6ZS T L V) := by
    rw [hy, Subgroup.coe_mul, conjSub_mul, conjSub_eq_of_mem_normalizer' (hHZ hkH)]
  have hEUγ : conjSub y V ≤ conjSub (g : G) (conjClosure V H) := by
    rw [hy, Subgroup.coe_mul, conjSub_mul]
    exact conjSub_mono _ (conjSub_le_conjClosure hkH)
  have hEH : conjSub y V ≤ H := hEUγ.trans hUγH
  have hEZ : conjSub y V ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := hEUγ.trans hUγZ
  have hE2 : IsPGroup 2 (conjSub y V) := hV2.map _
  rw [hE] at hα2
  set B := conjClosure V H ⊓ Subgroup.normalizer (conjSub y V : Set G) with hB
  have hEB : ⁅conjSub y V, B⁆ ≠ ⊥ := by
    intro h0
    have hEC : conjSub y V ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hkey : ∀ x ∈ H, conjSub y V ≤ Subgroup.centralizer (conjSub x V : Set G) := by
      intro x hx
      refine h.toHyp611Nat.le_centralizer_conjSub_of_le h6110 (B := B ⊓ conjSub x V)
        inf_le_right (inf_le_left.trans inf_le_right) ?_
        (hEC.trans (Subgroup.centralizer_le
          (show ((B ⊓ conjSub x V : Subgroup G) : Set G) ⊆ (B : Set G) from inf_le_left)))
      refine mQuot_le_one_of_relIndex_le_two (hV2.map _) ?_
      rw [Subgroup.inf_relIndex_right, ← hα2]
      exact Subgroup.relIndex_le_of_le_right (conjSub_le_conjClosure hx) (by rw [hα2]; norm_num)
    have hAN : conjClosure V H ≤ Subgroup.normalizer (conjSub y V : Set G) := by
      have : conjClosure V H ≤ Subgroup.centralizer (conjSub y V : Set G) :=
        conjClosure_le fun x hx v hv =>
          (Subgroup.le_centralizer_iff.mp (hkey x hx)) (mul_mem_conjSub hv)
      exact this.trans (Subgroup.centralizer_le_normalizer _)
    have hBA : B = conjClosure V H := inf_eq_left.mpr hAN
    rw [hBA, Subgroup.relIndex_self] at hα2
    norm_num at hα2
  have hBN : B ≤ Subgroup.normalizer (conjSub y V : Set G) ⊓
      Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G) := by
    refine le_inf inf_le_right (inf_le_left.trans ?_)
    rw [hZy]
    exact hAZγ
  have hB2 : IsPGroup 2 B := hA2.to_le inf_le_left
  have hEBZ := h.toHyp611Nat.commutator_eq_conjSub y hBN hB2 hEB
  have hVγ : V ≤ stab γ := V_le_stab_of_dist_le hyp hV1 (le_of_eq hγ.dist_eq)
  have hZne : conjSub y (ch6ZS T L V) ≠ ch6ZS T L V := by
    intro heq
    apply hγ.not_le
    have hstabN : stab γ ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
      rw [hstabγ]
      have h1 : conjSub (g : G) H ≤ conjSub (g : G) (Subgroup.normalizer (ch6ZS T L V : Set G)) :=
        conjSub_mono _ hHZ
      rwa [← conjSub_normalizer, ← hZy, heq] at h1
    have hON : Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer
        (pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) : Set G) :=
      (F7.normalizer_le_normalizer_centralizer _).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    have hle : pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓ stab γ ≤
        pCoreOf 2 (stab γ) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hON (hstabN hx), Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact (le_inf h.toHyp611Nat.V_le_pCoreOf_centralizer hVγ).trans
      (hle.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp γ))
  have hEQ : ¬ conjSub y V ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
    intro hle
    apply hZne
    have h1 : ⁅conjSub y V, B⁆ ≤ ch6ZS T L V := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono inf_le_left hle).trans
        (h.commutator_conjClosure_pCoreOf_le hH)
    rw [hEBZ] at h1
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [card_conjSub'])
  have hEγ₁ : ¬ conjSub y V ≤ ballStab 1 (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    intro hle
    apply hEQ
    have hker : ballStab 1 (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) ≤
        kerIn (H ⊓ Subgroup.normalizer (V : Set G)) H := by
      rw [(ballStab_one_γ₁ hyp.gen).1]
      intro x hx b hb
      have := (mem_coreIn.mp hx).2 b⁻¹ (H.inv_mem hb)
      rw [inv_inv] at this
      exact ⟨this.2, hN this.1⟩
    have hMP : MinParabolic H T (H ⊓ Subgroup.normalizer (V : Set G)) := ⟨hTH, hnotN, hUM⟩
    have hO := hMP.isSylowTwoOf_pCoreOf_kerIn
    have hEO : conjSub y V ≤ pCoreOf 2 H :=
      F7.le_of_normal_sylow hO
        (Subgroup.normal_subgroupOf_of_le_normalizer
          (hMP.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)))
        (hle.trans hker) hE2
    have hle' : pCoreOf 2 H ⊓ (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
        pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx.1, Subgroup.le_normalizer hx⟩)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    exact (le_inf hEO (le_inf hEH hEZ)).trans hle'
  have hdαγ : dist α γ = 1 := by
    rw [CosetGeom.dist_comm]
    exact dist_eq_one_iff_adj.mpr hαn
  have hdαγ₁ : dist α (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) = critDist (L ⊔ T ⊔ H) (L ⊔ T) H V := by
    have h1 := CosetGeom.dist_triangle hyp.gen α γ (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
    have h2 := hγ.geodesic
    rw [CosetGeom.dist_comm γ] at h1
    by_contra hne
    apply hEγ₁
    obtain ⟨-, hVb, -⟩ := critDist_spec hyp hV1
    have hEb : conjSub y V ≤ ballStab (critDist (L ⊔ T ⊔ H) (L ⊔ T) H V) α := by
      rw [hαy, ballStab_smul]
      exact conjSub_mono _ hVb
    refine hEb.trans fun x hx => mem_ballStab.mpr fun δ hδ => mem_ballStab.mp hx δ ?_
    have h3 := CosetGeom.dist_triangle hyp.gen α (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) δ
    omega
  have hyα : ((g * k)⁻¹ • α) = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hαy, inv_smul_smul]
  have hyγ : ((g * k)⁻¹ • γ) ∈ nbrs (γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj ((g * k)⁻¹)).mpr hαn.symm
    rwa [hyα] at this
  obtain ⟨z, hz, hzγ⟩ := stab_transitive_on_nbrs (γ := γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) hyγ
    (show γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁)
  have hzγ₀ : z • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := smul_eq_of_mem_stab hz
  set w : ↥(L ⊔ T ⊔ H) := z * (g * k)⁻¹ with hw
  have hwα : w • α = γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hw, mul_smul, hyα, hzγ₀]
  have hwγ : w • γ = γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H := by rw [hw, mul_smul, hzγ]
  have hwE : conjSub (w : G) (conjSub y V) = V := by
    have := Vv_smul hN w α
    rw [hwα, Vv_γ₀ hN, hE] at this
    exact this.symm
  have hcrit : IsCriticalVertex (L ⊔ T ⊔ H) (L ⊔ T) H V (w • γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) :=
    { dist_eq := by rw [← hwα, CosetGeom.dist_smul]; exact hdαγ₁
      not_le := by
        intro hle
        apply hEγ₁
        rw [ballStab_smul, ← hwE] at hle
        have := conjSub_mono (w : G)⁻¹ hle
        rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
      geodesic := by
        have := CosetGeom.dist_smul w γ (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
        rw [hwγ] at this
        rw [this, CosetGeom.dist_comm]
        exact hγ.geodesic }
  obtain ⟨δ'', hδ''n, hδ''2⟩ :=
    exists_nbr_relIndex_two hyp hV1 hcrit hb3 hodd hUM hc (hVA.trans hAγ₁.ge) hcrit.not_le
  have hδn : (w⁻¹ • δ'') ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) := by
    have := (smul_adj (w⁻¹)).mpr hδ''n
    rwa [inv_smul_smul] at this
  obtain ⟨k', hk', hk'δ⟩ :=
    stab_transitive_on_nbrs (γ := γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H)
      (show γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H ∈ nbrs (γ₁ (L ⊔ T ⊔ H) (L ⊔ T) H) from adj_γ₀_γ₁.symm) hδn
  have hk'H : ((k' : ↥(L ⊔ T ⊔ H)) : G) ∈ H := by rwa [stab_γ₁ h₂] at hk'
  set d : G := ((k' : ↥(L ⊔ T ⊔ H)) : G) with hd
  have hδ'' : δ'' = (w * k') • γ₀ (L ⊔ T ⊔ H) (L ⊔ T) H := by
    rw [mul_smul, hk'δ, smul_inv_smul]
  have hVvδ'' : Vv V δ'' = conjSub (w : G) (conjSub d V) := by
    rw [hδ'', Vv_smul_γ₀ hN, Subgroup.coe_mul, conjSub_mul]
  rw [hVvδ''] at hδ''2
  set F := conjSub y V ⊓ Subgroup.normalizer (conjSub d V : Set G) with hF
  have hF2 : F.relIndex (conjSub y V) = 2 := by
    have h2 : conjSub (w : G)⁻¹ V = conjSub y V := by
      have := congrArg (conjSub (w : G)⁻¹) hwE
      rw [conjSub_conjSub_inv] at this
      exact this.symm
    have h1 : conjSub (w : G)⁻¹ (V ⊓ Subgroup.normalizer
        (conjSub (w : G) (conjSub d V) : Set G)) = F := by
      rw [conjSub_inf, conjSub_normalizer, conjSub_conjSub_inv, h2, hF]
    rw [← hδ''2, ← h1, ← h2]
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective
  have hdZ : conjSub d (ch6ZS T L V) = ch6ZS T L V := conjSub_eq_of_mem_normalizer' (hHZ hk'H)
  have hFE : F ≤ conjSub y V := inf_le_left
  have hF2' : IsPGroup 2 F := hE2.to_le hFE
  have hDF : ⁅conjSub d V, F⁆ ≠ ⊥ := by
    intro h0
    have hDC : conjSub d V ≤ Subgroup.centralizer (F : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have h1 := h.toHyp611Nat.le_centralizer_conjSub_of_le h6110 (x := y) (y := d) (B := F) hFE
      inf_le_right (mQuot_le_one_of_relIndex_le_two hE2 (by rw [hF2])) hDC
    have hEN : conjSub y V ≤ Subgroup.normalizer (conjSub d V : Set G) :=
      (Subgroup.le_centralizer_iff.mp h1).trans (Subgroup.centralizer_le_normalizer _)
    have hFeq : F = conjSub y V := inf_eq_left.mpr hEN
    rw [hFeq, Subgroup.relIndex_self] at hF2
    norm_num at hF2
  have hFN : F ≤ Subgroup.normalizer (conjSub d V : Set G) ⊓
      Subgroup.centralizer (conjSub d (ch6ZS T L V) : Set G) := by
    rw [hdZ]
    exact le_inf inf_le_right (hFE.trans hEZ)
  have hDFZ : ⁅conjSub d V, F⁆ = ch6ZS T L V := by
    rw [h.toHyp611Nat.commutator_eq_conjSub d hFN hF2' hDF, hdZ]
  have hdinv : d⁻¹ ∈ H := H.inv_mem hk'H
  have hdU : conjSub d⁻¹ (conjClosure V H) = conjClosure V H :=
    conjSub_eq_of_mem_normalizer' (le_normalizer_conjClosure V H hdinv)
  have hdZ' : conjSub d⁻¹ (ch6ZS T L V) = ch6ZS T L V := conjSub_eq_of_mem_normalizer' (hHZ hdinv)
  have hy' : ∀ X : Subgroup G, conjSub (d⁻¹ * y) X = conjSub d⁻¹ (conjSub y X) :=
    fun X => conjSub_mul _ _ _
  have hdd : conjSub d⁻¹ (conjSub d V) = V := conjSub_conjSub_inv _ _
  have hrel : ∀ A B' : Subgroup G, (conjSub d⁻¹ A).relIndex (conjSub d⁻¹ B') = A.relIndex B' :=
    fun A B' => Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj _).injective
  have e1 : conjSub d⁻¹ B =
      conjClosure V H ⊓ Subgroup.normalizer (conjSub (d⁻¹ * y) V : Set G) := by
    rw [hB, conjSub_inf, hdU, ← conjSub_normalizer, ← hy']
  have e2 : conjSub d⁻¹ F = conjSub (d⁻¹ * y) V ⊓ Subgroup.normalizer (V : Set G) := by
    rw [hF, conjSub_inf, ← hy', ← conjSub_normalizer, hdd]
  have hB' : (conjClosure V H ⊓ Subgroup.normalizer (conjSub (d⁻¹ * y) V : Set G)).relIndex
      (conjClosure V H) = 2 := by
    rw [← e1, ← hdU, hrel]
    exact hα2
  have hF' : (conjSub (d⁻¹ * y) V ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (conjSub (d⁻¹ * y) V) = 2 := by
    rw [← e2, hy', hrel]
    exact hF2
  have hEB' : ⁅conjSub (d⁻¹ * y) V,
      conjClosure V H ⊓ Subgroup.normalizer (conjSub (d⁻¹ * y) V : Set G)⁆ =
      conjSub (d⁻¹ * y) (ch6ZS T L V) := by
    have := congrArg (conjSub d⁻¹) hEBZ
    rw [conjSub_commutator', e1, ← hy', ← hy'] at this
    exact this
  have hVF' : ⁅V, conjSub (d⁻¹ * y) V ⊓ Subgroup.normalizer (V : Set G)⁆ = ch6ZS T L V := by
    have := congrArg (conjSub d⁻¹) hDFZ
    rw [conjSub_commutator', hdd, e2, hdZ'] at this
    exact this
  have hZ' : conjSub (d⁻¹ * y) (ch6ZS T L V) ≠ ch6ZS T L V := by
    intro heq
    apply hZne
    rw [hy'] at heq
    have := congrArg (conjSub d) heq
    rwa [conjSub_inv_conjSub, hdZ] at this
  have hEZ' : conjSub (d⁻¹ * y) V ≤ Subgroup.centralizer (ch6ZS T L V : Set G) := by
    rw [hy']
    have := conjSub_mono d⁻¹ hEZ
    rwa [conjSub_centralizer', hdZ'] at this
  have hn2 := h.toHyp611Nat.n_le_two_of_config h6110 hVA hB' hF' hEB' hVF' hZ' hEZ'
  have hn : n = 2 := by
    have := h.two_le
    omega
  have hdH : conjSub d⁻¹ H = H := conjSub_eq_of_mem_normalizer' (Subgroup.le_normalizer hdinv)
  have hEH' : conjSub (d⁻¹ * y) V ≤ H := by
    rw [hy', ← hdH]
    exact conjSub_mono _ hEH
  have hdN : d ∈ Subgroup.normalizer
      ((H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk'H, F7.normalizer_le_normalizer_centralizer _ (hHZ hk'H)⟩
  have hdQ : conjSub d (pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G))) =
      pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) :=
    conjSub_eq_of_mem_normalizer'
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hdN)
  have hEQ' : ¬ conjSub (d⁻¹ * y) V ≤
      pCoreOf 2 (H ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
    intro hle
    apply hEQ
    have h1 := conjSub_mono d hle
    rwa [hy', conjSub_inv_conjSub, hdQ] at h1
  have hAZ' : conjClosure V H ≤
      Subgroup.centralizer (conjSub (d⁻¹ * y) (ch6ZS T L V) : Set G) := by
    have h1 : conjClosure V H ≤ Subgroup.centralizer (conjSub y (ch6ZS T L V) : Set G) := by
      rw [hZy]
      exact hAZγ
    have h2 := conjSub_mono d⁻¹ h1
    rwa [hdU, conjSub_centralizer', ← hy'] at h2
  exact ⟨d⁻¹ * y, hAel, hB', hF', hEB', hVF', hZ', hEZ', hEH', hEQ', hAZ', hn⟩

end Hyp6116

end CFSG.Quasithin.H13
