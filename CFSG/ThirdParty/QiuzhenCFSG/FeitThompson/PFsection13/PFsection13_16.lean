module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_15
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_16
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.16) -/


private theorem section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 := by
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have h2T := theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  rcases h2T with
    ⟨_hMF, _hType, _hTypeIf, _hVcomm, _hFrob, hQelem, _hQcard, _hvBound,
      _hcoh, _hTI, _hTau⟩
  rcases hsource with
    ⟨hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcase with
    ⟨hprod, _hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSFP, _hTFQ,
      _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII, _hSType, _hTType,
      _hcover⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  letI : IsElementaryAbelian q Q := hQelem
  letI : IsMulCommutative Q := IsElementaryAbelian.toIsMulCommutative q
  have hW1leQ : W1 ≤ Q := hW1leQinf.trans inf_le_left
  have hQcentQ : Q ≤ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := Q)).2 inferInstance
  have hQle : Q ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 := by
    intro x hxQ
    refine ⟨Subgroup.mem_top x, ?_⟩
    have hxcentQ : x ∈ Subgroup.centralizer (Q : Set G) := hQcentQ hxQ
    rw [Subgroup.mem_centralizer_iff] at hxcentQ
    change x ∈ Subgroup.centralizer (W1 : Set G)
    rw [Subgroup.mem_centralizer_iff]
    exact fun y hyW1 => hxcentQ y (hW1leQ hyW1)
  have hprodSwap := section13_section12InternalDirectProduct_swap hprod
  rcases hprodSwap with ⟨_hW2leW, _hW1leW, _hWswap, _hdisj, hW2centW1⟩
  have hW2le : W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 := by
    intro x hxW2
    exact ⟨Subgroup.mem_top x, hW2centW1 hxW2⟩
  exact sup_le hQle hW2le

private theorem section13_theorem_13_16_normalizer_W1_le_Tmax_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Subgroup.normalizer (W1 : Set G) ≤ Tmax := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcase with
    ⟨_hprod, _hWcyc, hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSFP, _hTFQ,
      _hSdecomp, _hTdecomp, _hSdisj, _hTdisj, _hST, _hII, _hSType, _hTType,
      _hcover⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hd_one : d = 1 := theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  have hD_card : Nat.card D = 1 := by
    rw [← hd_card, hd_one]
  have hD_bot : D = ⊥ := (Subgroup.card_eq_one (H := D)).1 hD_card
  have hW1sharp : Section7.puncturedSubgroupSet W1 ⊆ Section7.puncturedSubgroupSet Q := by
    intro x hx
    exact ⟨hW1leQinf.trans inf_le_left hx.1, hx.2⟩
  exact section13_normalizer_le_of_punctured_subset_ti
    (H := W1) (N := Tmax) (X := Section7.puncturedSubgroupSet Q)
    (section13_theorem_13_10_Qsharp_ti_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hD_bot)
    (section13_theorem_13_10_Qsharp_normalizer_le_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hD_bot)
    hW1ne hW1sharp


private theorem section13_theorem_13_16_normalizer_W1_le_Q_sup_VinfN_sup_W2_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    Subgroup.normalizer (W1 : Set G) ≤
      (Q ⊔ (V ⊓ Subgroup.normalizer (W1 : Set G))) ⊔ W2 := by
  classical
  have hsourceOrig := hsource
  let N : Subgroup G := Subgroup.normalizer (W1 : Set G)
  let D0 : Subgroup G := ambientDerivedSubgroup Tmax
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hptypeTOrig := hptypeT
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVleDer, _hVnil, _hW2norm,
      hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hQnormD : section10NormalIn Q D0 :=
    section13_mf_normalIn_ambientDerived_of_typeP (M := Tmax) (MF := Q)
      (U := V) (W1 := W2) (W2 := W1) hptypeTOrig
  have hDnormT : section10NormalIn D0 Tmax :=
    section12_normalIn_ambientDerivedSubgroup (E := Tmax)
  have hQVcomp :
      (V.subgroupOf D0).IsComplement' (Q.subgroupOf D0) :=
    section13_complementIn_of_normal_isComplement'
      (H := D0) (K := Q) (L := V) hDercomp hQnormD
  have hTW2comp :
      (W2.subgroupOf Tmax).IsComplement' (D0.subgroupOf Tmax) :=
    section13_complementIn_of_normal_isComplement'
      (H := Tmax) (K := D0) (L := W2) hTcomp hDnormT
  have hQW2cent :
      Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 :=
    section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hCent_le_N :
      subgroupCentralizerIn (⊤ : Subgroup G) W1 ≤ N := by
    intro x hx
    exact centralizer_le_normalizer W1 hx.2
  have hQW2leN : Q ⊔ W2 ≤ N := hQW2cent.trans hCent_le_N
  have hQleN : Q ≤ N := le_sup_left.trans hQW2leN
  have hW2leN : W2 ≤ N := le_sup_right.trans hQW2leN
  intro n hnN
  have hnT : n ∈ Tmax := hNleT hnN
  let nT : Tmax := ⟨n, hnT⟩
  rcases hTW2comp.existsUnique nT with ⟨⟨wT, dT⟩, hnTmul, _hnTuniq⟩
  have hwW2 : (wT : G) ∈ W2 := by
    exact wT.property
  have hdD : (dT : G) ∈ D0 := by
    exact dT.property
  let dD : D0 := ⟨(dT : G), hdD⟩
  rcases hQVcomp.existsUnique dD with ⟨⟨vD, qD⟩, hdDmul, _hdDuniq⟩
  have hvV : (vD : G) ∈ V := by
    exact vD.property
  have hqQ : (qD : G) ∈ Q := by
    exact qD.property
  have hnTmulG : (wT : G) * (dT : G) = n := by
    exact congrArg (fun x : Tmax => (x : G)) hnTmul
  have hdDmulG : (vD : G) * (qD : G) = (dT : G) := by
    exact congrArg (fun x : D0 => (x : G)) hdDmul
  have hwN : (wT : G) ∈ N := hW2leN hwW2
  have hqN : (qD : G) ∈ N := hQleN hqQ
  have hvN : (vD : G) ∈ N := by
    have hv_eq : (vD : G) = (wT : G)⁻¹ * n * (qD : G)⁻¹ := by
      rw [← hnTmulG, ← hdDmulG]
      group
    rw [hv_eq]
    exact N.mul_mem (N.mul_mem (N.inv_mem hwN) hnN) (N.inv_mem hqN)
  have hvK : (vD : G) ∈ V ⊓ N := ⟨hvV, hvN⟩
  have hn_decomp : n = (wT : G) * ((vD : G) * (qD : G)) := by
    rw [← hnTmulG, ← hdDmulG]
  let R : Subgroup G := (Q ⊔ (V ⊓ N)) ⊔ W2
  have hwR : (wT : G) ∈ R :=
    (show W2 ≤ R from le_sup_right) hwW2
  have hvR : (vD : G) ∈ R :=
    (show V ⊓ N ≤ R from le_sup_right.trans le_sup_left) hvK
  have hqR : (qD : G) ∈ R :=
    (show Q ≤ R from le_sup_left.trans le_sup_left) hqQ
  rw [hn_decomp]
  exact R.mul_mem hwR (R.mul_mem hvR hqR)

private theorem section13_theorem_13_16_W2_le_normalizer_VinfN_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    W2 ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.normalizer (W1 : Set G) : Subgroup G) : Set G) := by
  let N : Subgroup G := Subgroup.normalizer (W1 : Set G)
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, hW2normV,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hQW2cent :
      Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 :=
    section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hCent_le_N :
      subgroupCentralizerIn (⊤ : Subgroup G) W1 ≤ N := by
    intro x hx
    exact centralizer_le_normalizer W1 hx.2
  have hW2leN : W2 ≤ N := le_sup_right.trans (hQW2cent.trans hCent_le_N)
  intro w hwW2
  have hwNormV : w ∈ Subgroup.normalizer (V : Set G) :=
    (mem_subgroupNormalizerIn.mp (hW2normV hwW2)).1
  have hwNormN : w ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.le_normalizer (hW2leN hwW2)
  rw [Subgroup.mem_normalizer_iff] at hwNormV hwNormN ⊢
  intro x
  constructor
  · intro hx
    exact ⟨(hwNormV x).1 hx.1, (hwNormN x).1 hx.2⟩
  · intro hx
    exact ⟨(hwNormV x).2 hx.1, (hwNormN x).2 hx.2⟩

private theorem section13_theorem_13_16_K_W2_complementIn_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section12ComplementIn
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2)
      (V ⊓ Subgroup.normalizer (W1 : Set G)) W2 := by
  let N : Subgroup G := Subgroup.normalizer (W1 : Set G)
  let D0 : Subgroup G := ambientDerivedSubgroup Tmax
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVleDer, _hVnil, _hW2norm,
      hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hKleD0 : V ⊓ N ≤ D0 := inf_le_left.trans hDercomp.2.1
  have hdisj : Disjoint (V ⊓ N) W2 :=
    hTcomp.2.2.2.mono_left hKleD0
  exact ⟨le_sup_left, le_sup_right, rfl, hdisj⟩

private theorem section13_theorem_13_16_K_sup_W2_le_normalizer_K_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    (V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2 ≤
      Subgroup.normalizer
        ((V ⊓ Subgroup.normalizer (W1 : Set G) : Subgroup G) : Set G) := by
  exact sup_le Subgroup.le_normalizer
    (section13_theorem_13_16_W2_le_normalizer_VinfN_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)

private theorem section13_theorem_13_16_K_normalIn_K_sup_W2_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    section10NormalIn
      (V ⊓ Subgroup.normalizer (W1 : Set G))
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) := by
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  refine ⟨le_sup_left, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (H := K) (K := K ⊔ W2) le_sup_left).2
    (section13_theorem_13_16_K_sup_W2_le_normalizer_K_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)

private theorem section13_subgroupCentralizerIn_normalIn_of_le_normalizer
    {G : Type u} [Group G]
    {E A : Subgroup G}
    (hEnormA : E ≤ Subgroup.normalizer (A : Set G)) :
    section10NormalIn (subgroupCentralizerIn E A) E := by
  let C : Subgroup G := subgroupCentralizerIn E A
  have hCE : C ≤ E := inf_le_left
  refine ⟨hCE, ?_⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (H := C) (K := E) hCE).2 ?_
  have hconj_mem :
      ∀ {g c : G}, g ∈ E → c ∈ C → g * c * g⁻¹ ∈ C := by
    intro g c hg hc
    refine ⟨E.mul_mem (E.mul_mem hg hc.1) (E.inv_mem hg), ?_⟩
    change g * c * g⁻¹ ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hgNorm : g ∈ Subgroup.normalizer (A : Set G) := hEnormA hg
    rw [Subgroup.mem_normalizer_iff] at hgNorm
    have hga : g⁻¹ * a * g ∈ A := by
      exact (hgNorm (g⁻¹ * a * g)).2 (by simpa [mul_assoc] using ha)
    have hcCent : c ∈ Subgroup.centralizer (A : Set G) := hc.2
    rw [Subgroup.mem_centralizer_iff] at hcCent
    have hcomm := hcCent (g⁻¹ * a * g) hga
    calc
      a * (g * c * g⁻¹) = g * (g⁻¹ * a * g) * c * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [hcomm]
      _ = g * c * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = g * c * g⁻¹ * a := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact hconj_mem hg hc
  · intro hgc
    have hback := hconj_mem (E.inv_mem hg) hgc
    simpa [mul_assoc] using hback

private theorem section13_theorem_13_16_K_subgroupOf_KW2_solvable_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Group.IsSolvable
      ((V ⊓ Subgroup.normalizer (W1 : Set G)).subgroupOf
        ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2)) := by
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer, hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hKsubV_nil : Group.IsNilpotent (K.subgroupOf V) := by
    letI : Group.IsNilpotent V := hVnil
    infer_instance
  have hKnil : Group.IsNilpotent K := by
    let e : K.subgroupOf V ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := V) inf_le_left
    exact Group.nilpotent_of_mulEquiv (G := K.subgroupOf V) (G' := K)
      (_h := hKsubV_nil) e
  have hKsubKW2_nil : Group.IsNilpotent (K.subgroupOf KW2) := by
    let e : K.subgroupOf KW2 ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := KW2) le_sup_left
    exact Group.nilpotent_of_mulEquiv (G := K) (G' := K.subgroupOf KW2)
      (_h := hKnil) e.symm
  haveI : Group.IsNilpotent (K.subgroupOf KW2) := hKsubKW2_nil
  simpa [K, KW2] using (inferInstance : Group.IsSolvable (K.subgroupOf KW2))

private theorem section13_theorem_13_16_Q1_solvable_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D Q1 : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hQprod : section12InternalDirectProduct W1 Q1 Q) :
    Group.IsSolvable Q1 := by
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  rcases hQprod with ⟨_hW1Q, hQ1Q, _hQ_eq, _hdisj, _hcent⟩
  rcases hQMF with ⟨⟨_hQT, _hQnormT, hQnil, _hQhallT⟩, _hmax⟩
  have hQ1subQ_nil : Group.IsNilpotent (Q1.subgroupOf Q) := by
    letI : Group.IsNilpotent Q := hQnil
    infer_instance
  have hQ1nil : Group.IsNilpotent Q1 := by
    let e : Q1.subgroupOf Q ≃* Q1 :=
      Subgroup.subgroupOfEquivOfLe (H := Q1) (K := Q) hQ1Q
    exact Group.nilpotent_of_mulEquiv (G := Q1.subgroupOf Q) (G' := Q1)
      (_h := hQ1subQ_nil) e
  haveI : Group.IsNilpotent Q1 := hQ1nil
  infer_instance

private theorem section13_theorem_13_16_K_le_centralizer_W1_of_frobenius
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hfrob : section12FrobeniusJoinWithKernel
      (V ⊓ Subgroup.normalizer (W1 : Set G)) W2) :
    V ⊓ Subgroup.normalizer (W1 : Set G) ≤
      subgroupCentralizerIn ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) W1 := by
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let E : Subgroup G := K ⊔ W2
  let C0 : Subgroup G := subgroupCentralizerIn E W1
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hQW2cent :
      Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 :=
    section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hW2leNormW1 : W2 ≤ Subgroup.normalizer (W1 : Set G) := by
    intro w hw
    exact centralizer_le_normalizer W1
      (hQW2cent ((show W2 ≤ Q ⊔ W2 from le_sup_right) hw)).2
  have hEleNormW1 : E ≤ Subgroup.normalizer (W1 : Set G) := by
    exact sup_le inf_le_right hW2leNormW1
  have hC0normIn : section10NormalIn C0 E :=
    section13_subgroupCentralizerIn_normalIn_of_le_normalizer hEleNormW1
  have hKW2comp : section12ComplementIn E K W2 := by
    simpa [K, E] using
      section13_theorem_13_16_K_W2_complementIn_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
  have hKsolv : Group.IsSolvable (K.subgroupOf E) := by
    simpa [K, E] using
      section13_theorem_13_16_K_subgroupOf_KW2_solvable_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
  by_contra hK_not_le_C0
  have hKsub_not_le_C0sub :
      ¬ K.subgroupOf E ≤ C0.subgroupOf E := by
    intro hle
    apply hK_not_le_C0
    intro k hkK
    have hkE : k ∈ E := (show K ≤ E from le_sup_left) hkK
    have hkSub : (⟨k, hkE⟩ : E) ∈ K.subgroupOf E :=
      Subgroup.mem_subgroupOf.mpr hkK
    have hkCsub := hle hkSub
    simpa [C0, Subgroup.mem_subgroupOf] using hkCsub
  haveI : (C0.subgroupOf E).Normal := hC0normIn.2
  have hC0sub_le_Ksub :
      C0.subgroupOf E ≤ K.subgroupOf E := by
    simpa [K, E, C0] using
      (lemma_3_2_a (K := K.subgroupOf E) (R := W2.subgroupOf E)
        (N := C0.subgroupOf E) hfrob hKsolv hKsub_not_le_C0sub)
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨w, hwne⟩
  let wG : G := (w : G)
  have hwW2 : wG ∈ W2 := w.property
  have hwE : wG ∈ E := (show W2 ≤ E from le_sup_right) hwW2
  have hwC0 : wG ∈ C0 := by
    exact ⟨hwE, (hQW2cent ((show W2 ≤ Q ⊔ W2 from le_sup_right) hwW2)).2⟩
  have hwC0sub : (⟨wG, hwE⟩ : E) ∈ C0.subgroupOf E := by
    simpa [C0, Subgroup.mem_subgroupOf] using hwC0
  have hwKsub := hC0sub_le_Ksub hwC0sub
  have hwK : wG ∈ K := by
    simpa [Subgroup.mem_subgroupOf] using hwKsub
  have hdisj : Disjoint K W2 := hKW2comp.2.2.2
  have hwbot : wG ∈ (⊥ : Subgroup G) :=
    (Subgroup.disjoint_def.mp hdisj) hwK hwW2
  have hw_one : wG = 1 := by
    simpa using hwbot
  exact hwne (by ext; exact hw_one)

private theorem section13_isInvariant_subgroupOf_of_le_normalizer
    {G : Type u} [Group G]
    {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant A H (K.subgroupOf H) := by
  haveI : Subgroup.Normalizes A H := ⟨hAH⟩
  refine ⟨?_⟩
  intro a x
  change ((x : H) : G) ∈ K ↔ ((a : G) * ((x : H) : G) * (a : G)⁻¹) ∈ K
  exact Subgroup.mem_normalizer_iff.mp (hAK a.property) ((x : H) : G)

private theorem section13_internalDirectProduct_of_subgroup_isCompl
    {G : Type u} [Group G]
    (W1 Q : Subgroup G) (C : Subgroup Q)
    (hW1Q : W1 ≤ Q)
    (hcompl : IsCompl (W1.subgroupOf Q) C)
    (hQcomm : Q ≤ Subgroup.centralizer (Q : Set G)) :
    section12InternalDirectProduct W1 (C.map Q.subtype) Q := by
  let B : Subgroup Q := W1.subgroupOf Q
  let Q1 : Subgroup G := C.map Q.subtype
  have hBmap : B.map Q.subtype = W1 := by
    simpa [B] using
      Subgroup.map_subgroupOf_eq_of_le (G := G) (H := W1) (K := Q) hW1Q
  have hCmap : C.map Q.subtype = Q1 := rfl
  have htopmap : (⊤ : Subgroup Q).map Q.subtype = Q := by
    ext x
    constructor
    · rintro ⟨q, _hq, rfl⟩
      exact q.property
    · intro hxQ
      exact ⟨⟨x, hxQ⟩, Subgroup.mem_top _, rfl⟩
  have hsupQ : W1 ⊔ Q1 = Q := by
    calc
      W1 ⊔ Q1 = B.map Q.subtype ⊔ C.map Q.subtype := by rw [hBmap, hCmap]
      _ = (B ⊔ C).map Q.subtype := by rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup Q).map Q.subtype := by rw [hcompl.sup_eq_top]
      _ = Q := htopmap
  have hdisj : Disjoint W1 Q1 := by
    rw [← hBmap, ← hCmap]
    exact Subgroup.disjoint_map Q.subtype_injective hcompl.disjoint
  have hQ1Q : Q1 ≤ Q := by
    intro x hx
    rcases hx with ⟨c, _hc, rfl⟩
    exact c.property
  refine ⟨hW1Q, hQ1Q, ?_, hdisj, ?_⟩
  · exact hsupQ.symm
  · intro x hxW1
    have hxQcent : x ∈ Subgroup.centralizer (Q : Set G) := hQcomm (hW1Q hxW1)
    rw [Subgroup.mem_centralizer_iff] at hxQcent ⊢
    intro y hyQ1
    exact hxQcent y (hQ1Q hyQ1)

private theorem section13_le_normalizer_map_of_isInvariant
    {G : Type u} [Group G]
    (A Q : Subgroup G) (C : Subgroup Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    [hCinv : letI : Subgroup.Normalizes A Q := ⟨hAQ⟩; IsInvariant A Q C] :
    A ≤ Subgroup.normalizer ((C.map Q.subtype : Subgroup G) : Set G) := by
  letI : Subgroup.Normalizes A Q := ⟨hAQ⟩
  intro a haA
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨q, hqC, rfl⟩
    refine ⟨(⟨a, haA⟩ : A) • q, ?_, ?_⟩
    · exact (IsInvariant.invariant (A := A) (G := Q) (H := C)
        (⟨a, haA⟩ : A) q).1 hqC
    · simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  · intro hx
    rcases hx with ⟨q, hqC, hx_eq⟩
    refine ⟨(⟨a, haA⟩ : A)⁻¹ • q, ?_, ?_⟩
    · exact (IsInvariant.invariant (A := A) (G := Q) (H := C)
        ((⟨a, haA⟩ : A)⁻¹) q).1 hqC
    · have hx_eq' : (q : G) = a * x * a⁻¹ := by simpa using hx_eq
      calc
        (((⟨a, haA⟩ : A)⁻¹ • q : Q) : G) = a⁻¹ * (q : G) * a := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        _ = x := by
          rw [hx_eq']
          group

private theorem section13_coprime_card_of_le_elementary
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] (Q Q1 A : Subgroup G)
    [IsElementaryAbelian q Q]
    (hQ1Q : Q1 ≤ Q)
    (hcop : Nat.Coprime q (Nat.card A)) :
    Nat.Coprime (Nat.card Q1) (Nat.card A) := by
  have hQp : IsPGroup q Q := IsElementaryAbelian.isPGroup q Q
  have hQ1p : IsPGroup q Q1 := IsPGroup.to_le (H := Q1) (K := Q) hQp hQ1Q
  rcases hQ1p.exists_card_eq with ⟨n, hn⟩
  rw [hn]
  exact hcop.pow_left n

private def theorem_13_16_MaschkeFrobeniusSourceData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q V : Subgroup G) : Prop :=
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  ∃ Q1 : Subgroup G,
    section12InternalDirectProduct W1 Q1 Q ∧
      (K ≠ ⊥ →
        section12FrobeniusJoinWithKernel K W2 ∧
          KW2 ≤ Subgroup.normalizer (Q1 : Set G) ∧
          Nat.Coprime (Nat.card Q1) (Nat.card KW2))

private theorem section13_theorem_13_16_MaschkeFrobeniusSourceData_of_inputs
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q V : Subgroup G) (q : ℕ)
    [Fact q.Prime] [IsElementaryAbelian q Q]
    (hW1Q : W1 ≤ Q)
    (hKW2normQ :
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) ≤
        Subgroup.normalizer (Q : Set G))
    (hKW2normW1 :
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) ≤
        Subgroup.normalizer (W1 : Set G))
    (hcop : Nat.Coprime q
      (Nat.card (((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) : Subgroup G)))
    (hfrob : (V ⊓ Subgroup.normalizer (W1 : Set G)) ≠ ⊥ →
      section12FrobeniusJoinWithKernel (V ⊓ Subgroup.normalizer (W1 : Set G)) W2) :
    theorem_13_16_MaschkeFrobeniusSourceData W1 W2 Q V := by
  classical
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  letI : Subgroup.Normalizes KW2 Q := ⟨by simpa [K, KW2] using hKW2normQ⟩
  have hW1inv : IsInvariant KW2 Q (W1.subgroupOf Q) := by
    exact section13_isInvariant_subgroupOf_of_le_normalizer
      (A := KW2) (H := Q) (K := W1)
      (by simpa [K, KW2] using hKW2normQ)
      (by simpa [K, KW2] using hKW2normW1)
  letI : IsInvariant KW2 Q (W1.subgroupOf Q) := hW1inv
  rcases section12_exists_isCompl_isInvariant_of_elementaryAbelian_coprime
      (V := Q) (A := KW2) (p := q) (by simpa [K, KW2] using hcop)
      (W1.subgroupOf Q) with ⟨C, hcompl, hCinv⟩
  let Q1 : Subgroup G := C.map Q.subtype
  have hQcomm : Q ≤ Subgroup.centralizer (Q : Set G) := by
    letI : IsMulCommutative Q := IsElementaryAbelian.toIsMulCommutative q
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := Q)).2 inferInstance
  have hQprod : section12InternalDirectProduct W1 Q1 Q := by
    simpa [Q1] using
      section13_internalDirectProduct_of_subgroup_isCompl W1 Q C hW1Q hcompl hQcomm
  have hQ1Q : Q1 ≤ Q := hQprod.2.1
  haveI : IsInvariant KW2 Q C := hCinv
  refine ⟨Q1, hQprod, ?_⟩
  intro hKne
  refine ⟨by simpa [K] using hfrob hKne, ?_, ?_⟩
  · change KW2 ≤ Subgroup.normalizer (Q1 : Set G)
    exact section13_le_normalizer_map_of_isInvariant KW2 Q C
      (by simpa [K, KW2] using hKW2normQ)
  · change Nat.Coprime (Nat.card Q1) (Nat.card KW2)
    exact section13_coprime_card_of_le_elementary Q Q1 KW2 hQ1Q
      (by simpa [K, KW2] using hcop)

private def theorem_13_16_MaschkeFrobeniusInputSourceData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 _Q V : Subgroup G) (q : ℕ) : Prop :=
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  Nat.Prime q ∧
    Nat.Coprime q (Nat.card KW2) ∧
      (K ≠ ⊥ → section12FrobeniusJoinWithKernel K W2)

private def theorem_13_16_KW2FrobeniusCoprimeSourceData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 _Q V : Subgroup G) (q : ℕ) : Prop :=
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  Nat.Coprime q (Nat.card KW2) ∧
    (K ≠ ⊥ → section12FrobeniusJoinWithKernel K W2)

private def theorem_13_16_KCentralizesQSourceData
    {G : Type u} [Group G] [Finite G]
    (W1 W2 Q V : Subgroup G) : Prop :=
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  ∃ Q1 : Subgroup G,
    section12InternalDirectProduct W1 Q1 Q ∧
      (K ≠ ⊥ →
        Section9.frobeniusActionData KW2 K W2 Q1 ∧
          subgroupCentralizerIn Q1 W2 = ⊥ ∧
            K ≤ subgroupCentralizerIn KW2 W1)

private theorem section13_theorem_13_16_Q1_centralizer_W2_eq_bot_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D Q1 : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hQprod : section12InternalDirectProduct W1 Q1 Q) :
    subgroupCentralizerIn Q1 W2 = ⊥ := by
  let D0 : Subgroup G := ambientDerivedSubgroup Tmax
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, hcentralizer, _hnormType⟩
  rcases hQprod with ⟨_hW1Q, hQ1Q, _hQ_eq, hW1disjQ1, _hW1centQ1⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨x, hxne⟩
  let xG : G := (x : G)
  have hxW2 : xG ∈ W2 := x.property
  have hxG_ne : xG ≠ 1 := by
    intro hxG
    apply hxne
    ext
    exact hxG
  have hxcent : elementCentralizerIn D0 xG = W1 :=
    hcentralizer xG hxW2 hxG_ne
  apply le_antisymm
  · intro y hy
    have hyParts :
        y ∈ Q1 ∧ y ∈ Subgroup.centralizer (W2 : Set G) := by
      simpa [subgroupCentralizerIn] using hy
    have hyD0 : y ∈ D0 := hDercomp.1 (hQ1Q hyParts.1)
    have hyCentX : y ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hyParts ⊢
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hyParts.2 xG hxW2
    have hyElem : y ∈ elementCentralizerIn D0 xG := by
      simpa [elementCentralizerIn] using And.intro hyD0 hyCentX
    have hyW1 : y ∈ W1 := by
      simpa [hxcent] using hyElem
    exact (Subgroup.disjoint_def.mp hW1disjQ1) hyW1 hyParts.1
  · exact bot_le

private theorem section13_theorem_13_16_Vinf_normalizer_W1_le_D_from_sourceData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (W1 W2 Q V D : Subgroup G)
    (hD : D = subgroupCentralizerIn V Q)
    (hdata : theorem_13_16_KCentralizesQSourceData W1 W2 Q V) :
    V ⊓ Subgroup.normalizer (W1 : Set G) ≤ D := by
  classical
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  by_cases hKbot : K = ⊥
  · intro x hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [K, hKbot] using hx
    have hx_one : x = 1 := by
      simpa using hxbot
    rw [hx_one]
    exact D.one_mem
  · rcases hdata with ⟨Q1, hQprod, hstep⟩
    rcases hstep hKbot with ⟨haction, hCW2, hKCW1_in⟩
    have h91 := Section9.theorem_9_1 (K ⊔ W2) K W2 Q1 haction
    have hQ1_centralizes_K : subgroupCentralizerIn Q1 K = Q1 :=
      h91.2.1 hCW2
    have hQ1_le_centK : Q1 ≤ Subgroup.centralizer (K : Set G) := by
      intro q hq
      have hqC : q ∈ subgroupCentralizerIn Q1 K := by
        simpa [hQ1_centralizes_K] using hq
      exact hqC.2
    have hK_le_centQ1 : K ≤ Subgroup.centralizer (Q1 : Set G) :=
      Subgroup.le_centralizer_iff.mp hQ1_le_centK
    have hK_le_centW1 : K ≤ Subgroup.centralizer (W1 : Set G) := by
      intro k hk
      exact (hKCW1_in hk).2
    rcases hQprod with ⟨_hW1Q, _hQ1Q, hQ_eq, _hdisj, _hW1centQ1⟩
    have hK_le_centQ : K ≤ Subgroup.centralizer (Q : Set G) := by
      rw [hQ_eq]
      exact section13_le_centralizer_sup_of_le_centralizers hK_le_centW1 hK_le_centQ1
    rw [hD]
    intro x hxK
    exact ⟨hxK.1, hK_le_centQ hxK⟩

private theorem section13_theorem_13_16_KCentralizesQSourceData_from_maschkeData
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hdata : theorem_13_16_MaschkeFrobeniusSourceData W1 W2 Q V) :
    theorem_13_16_KCentralizesQSourceData W1 W2 Q V := by
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  rcases hdata with ⟨Q1, hQprod, hstep⟩
  refine ⟨Q1, hQprod, ?_⟩
  intro hKne
  rcases hstep hKne with ⟨hfrob, hKW2normQ1, hcop⟩
  have hKW2comp : section12ComplementIn KW2 K W2 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_W2_complementIn_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource
  have haction : Section9.frobeniusActionData KW2 K W2 Q1 :=
    ⟨hKW2comp, hfrob, hKW2normQ1,
      section13_theorem_13_16_Q1_solvable_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Q1 Sfam Tfam τS τT
        p q u v c d hsource hQprod,
      hcop⟩
  have hKCW1 : K ≤ subgroupCentralizerIn KW2 W1 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_le_centralizer_W1_of_frobenius
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource hfrob
  exact ⟨haction,
    section13_theorem_13_16_Q1_centralizer_W2_eq_bot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Q1 Sfam Tfam τS τT
      p q u v c d hsource hQprod,
    hKCW1⟩

public theorem section13_prime_q_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime q := by
  by_cases h10 : theorem_13_10_hypothesis Smax P C Sfam p q u
  · rcases (theorem_13_4 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource h10).2 with ⟨hcase, _hv⟩
    rcases hcase with
      ⟨_h92, _hH0le, _hcent, hq, _hp, _hred, _hcard, _hcentby,
        _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
    exact hq
  · rcases ((theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource).2 h10) with
      ⟨_hCbot, hcase, _hu⟩
    rcases hcase with
      ⟨_h92, _hH0le, _hcent, _hp, hq, _hred, _hcard, _hcentby,
        _hcyclic, _hirr, _hfield, _hcop, _hdiv⟩
    exact hq

private theorem section13_theorem_13_16_q_coprime_KW2_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Coprime q
      (Nat.card (((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) : Subgroup G)) := by
  classical
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  let D0 : Subgroup G := ambientDerivedSubgroup Tmax
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hptypeTOrig := hptypeT
  rcases hptypeT with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, _hVleDer, _hVnil, _hW2norm,
      hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hQleT : Q ≤ Tmax := Section12.section16MFSubgroup_le hQMF
  have hD0leT : D0 ≤ Tmax := by
    simpa [D0] using section12_ambientDerivedSubgroup_le (G := G) (E := Tmax)
  have hQleD0 : Q ≤ D0 := by
    simpa [D0] using hDercomp.1
  have hVleD0 : V ≤ D0 := by
    simpa [D0] using hDercomp.2.1
  have hW2leT : W2 ≤ Tmax := hTcomp.2.1
  have hQHallT : IsHallSubgroup (subgroupPrimeSet Q) (Q.subgroupOf Tmax) :=
    Section12.section16MFSubgroup_subgroupOf_isHall hQMF
  have hcopQindex : Nat.Coprime (Nat.card Q) (Q.subgroupOf Tmax).index := by
    rw [← section12_card_subgroupOf_eq hQleT]
    exact hQHallT.card_coprime_index
  have hQnormD0 : section10NormalIn Q D0 := by
    simpa [D0] using section13_mf_normalIn_ambientDerived_of_typeP hptypeTOrig
  have hQVD0comp : (Q.subgroupOf D0).IsComplement' (V.subgroupOf D0) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (M := D0) (K := Q) (L := V)
      (by simpa [D0] using hDercomp) hQnormD0.2
  have hindexQ_D0 : (Q.subgroupOf D0).index = Nat.card V := by
    have hidx := hQVD0comp.symm.index_eq_card
    exact hidx.trans (section12_card_subgroupOf_eq hVleD0)
  have hQsubT_le_DsubT : Q.subgroupOf Tmax ≤ D0.subgroupOf Tmax := by
    intro x hx
    change ((x : Tmax) : G) ∈ D0
    exact hQleD0 (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hrelQ_D0 :
      (Q.subgroupOf Tmax).relIndex (D0.subgroupOf Tmax) =
        (Q.subgroupOf D0).index := by
    rw [Subgroup.relIndex_subgroupOf (H := Q) (K := D0) (L := Tmax) hD0leT]
    rw [← Subgroup.relIndex_subgroupOf (H := Q) (K := D0) (L := D0) le_rfl]
    have hD0top : D0.subgroupOf D0 = ⊤ := Subgroup.subgroupOf_eq_top.2 le_rfl
    rw [hD0top]
    exact Subgroup.relIndex_top_right (Q.subgroupOf D0)
  have hcardV_dvd_indexQ : Nat.card V ∣ (Q.subgroupOf Tmax).index := by
    refine ⟨(D0.subgroupOf Tmax).index, ?_⟩
    rw [← hindexQ_D0, ← hrelQ_D0]
    exact (Subgroup.relIndex_mul_index hQsubT_le_DsubT).symm
  have hD0normT : section10NormalIn D0 Tmax := by
    simpa [D0] using section12_normalIn_ambientDerivedSubgroup (G := G) (E := Tmax)
  have hD0W2Tcomp : (D0.subgroupOf Tmax).IsComplement' (W2.subgroupOf Tmax) :=
    Section12.section12ComplementIn_left_normal_isComplement'
      (M := Tmax) (K := D0) (L := W2)
      (by simpa [D0] using hTcomp) hD0normT.2
  have hindexD0_T : (D0.subgroupOf Tmax).index = Nat.card W2 := by
    have hidx := hD0W2Tcomp.symm.index_eq_card
    exact hidx.trans (section12_card_subgroupOf_eq hW2leT)
  have hcardW2_dvd_indexQ : Nat.card W2 ∣ (Q.subgroupOf Tmax).index := by
    refine ⟨(Q.subgroupOf Tmax).relIndex (D0.subgroupOf Tmax), ?_⟩
    rw [← hindexD0_T, Nat.mul_comm]
    exact (Subgroup.relIndex_mul_index hQsubT_le_DsubT).symm
  have hcardK_dvd_indexQ : Nat.card K ∣ (Q.subgroupOf Tmax).index := by
    exact (Subgroup.card_dvd_of_le (show K ≤ V from inf_le_left)).trans
      hcardV_dvd_indexQ
  have hcopQK : Nat.Coprime (Nat.card Q) (Nat.card K) :=
    Nat.Coprime.coprime_dvd_right hcardK_dvd_indexQ hcopQindex
  have hcopQW2 : Nat.Coprime (Nat.card Q) (Nat.card W2) :=
    Nat.Coprime.coprime_dvd_right hcardW2_dvd_indexQ hcopQindex
  have hKW2comp : section12ComplementIn KW2 K W2 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_W2_complementIn_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
  have hKnormKW2 : section10NormalIn K KW2 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_normalIn_K_sup_W2_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsourceOrig
  have hKW2card : Nat.card KW2 = Nat.card K * Nat.card W2 :=
    section13_card_eq_mul_of_complementIn_normal hKW2comp hKnormKW2
  have hcopQKW2 : Nat.Coprime (Nat.card Q) (Nat.card KW2) := by
    rw [hKW2card]
    exact hcopQK.mul_right hcopQW2
  have hW1Q : W1 ≤ Q := hW1leQinf.trans inf_le_left
  have hq_dvd_Q : q ∣ Nat.card Q := by
    rw [hq_card]
    exact Subgroup.card_dvd_of_le hW1Q
  exact Nat.Coprime.coprime_dvd_left hq_dvd_Q hcopQKW2

private theorem section13_theorem_13_16_KW2FrobeniusCoprimeSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_16_KW2FrobeniusCoprimeSourceData W1 W2 Q V q := by
  refine ⟨section13_theorem_13_16_q_coprime_KW2_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource, ?_⟩
  intro hKne
  -- Source substep in `(13.16)`: if `K = N_V(W₁)` is nontrivial, then
  -- the restricted semidirect product `KW₂` is Frobenius with kernel `K`.
  classical
  let K : Subgroup G := V ⊓ Subgroup.normalizer (W1 : Set G)
  let KW2 : Subgroup G := K ⊔ W2
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsource
  have h2T := theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  rcases h2T with
    ⟨_hQMF2, _hType, _hTypeIf, _hVcomm, hfrobVW2, _hQelem, _hQcard,
      _hvBound, _hcoh, _hTI, _hTau⟩
  have hKW2comp : section12ComplementIn KW2 K W2 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_W2_complementIn_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource
  have hKnormKW2 : section10NormalIn K KW2 := by
    simpa [K, KW2] using
      section13_theorem_13_16_K_normalIn_K_sup_W2_of_sourceContext
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource
  have hcompLocal :
      (K.subgroupOf KW2).IsComplement' (W2.subgroupOf KW2) :=
    Section12.section12ComplementIn_left_normal_isComplement' hKW2comp hKnormKW2.2
  have hKsub_ne : K.subgroupOf KW2 ≠ ⊥ := by
    intro hbot
    exact hKne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_left)
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨_hQMF, _hW2cyc, hW2ne, _hW2Hall, _hTcomp, _hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, _hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hW2sub_ne : W2.subgroupOf KW2 ≠ ⊥ := by
    intro hbot
    exact hW2ne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le le_sup_right)
  refine (lemma_3_1 (G := KW2) (K := K.subgroupOf KW2) (R := W2.subgroupOf KW2)
    hKsub_ne hW2sub_ne hKnormKW2.2 hcompLocal).2 ?_
  intro x hxne
  -- Restrict the fixed-point-free action from the Frobenius group `VW₂` to
  -- the nontrivial normalized subgroup `K ≤ V`.
  let VW2 : Subgroup G := V ⊔ W2
  have hfrobLocal :
      IsFrobeniusGroupWithKernelComplement (V.subgroupOf VW2) (W2.subgroupOf VW2) := by
    simpa [section12FrobeniusJoinWithKernel, VW2] using hfrobVW2
  have hcentVW2 :
      ∀ x : W2.subgroupOf VW2, x ≠ 1 →
        elementCentralizerIn (V.subgroupOf VW2) (x : VW2) = ⊥ :=
    (lemma_3_1 (G := VW2) (K := V.subgroupOf VW2) (R := W2.subgroupOf VW2)
      hfrobLocal.kernel_ne_bot hfrobLocal.complement_ne_bot
      hfrobLocal.normal hfrobLocal.isComplement').1 hfrobLocal
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases hy with ⟨hyK, hyCent⟩
  have hxW2 : ((x : KW2) : G) ∈ W2 := by
    exact x.property
  have hxVW2 : ((x : KW2) : G) ∈ VW2 := by
    exact (show W2 ≤ V ⊔ W2 from le_sup_right) hxW2
  let xVW2 : W2.subgroupOf VW2 := ⟨⟨((x : KW2) : G), hxVW2⟩, hxW2⟩
  have hxVW2_ne : xVW2 ≠ 1 := by
    intro hxbot
    apply hxne
    ext
    exact congrArg (fun z : W2.subgroupOf VW2 => (z : G)) hxbot
  have hyK_ambient : ((y : KW2) : G) ∈ K := by
    simpa [Subgroup.mem_subgroupOf] using hyK
  have hyV : ((y : KW2) : G) ∈ V :=
    (show K ≤ V from inf_le_left) hyK_ambient
  have hyVW2 : ((y : KW2) : G) ∈ VW2 :=
    (show V ≤ V ⊔ W2 from le_sup_left) hyV
  let yVW2 : VW2 := ⟨((y : KW2) : G), hyVW2⟩
  have hyCommKW2 : (y : KW2) * (x : KW2) = (x : KW2) * (y : KW2) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyCent
  have hyCentVW2 :
      yVW2 ∈ elementCentralizerIn (V.subgroupOf VW2) (xVW2 : VW2) := by
    refine ⟨?_, ?_⟩
    · change ((yVW2 : VW2) : G) ∈ V
      exact hyV
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      ext
      exact congrArg (fun z : KW2 => (z : G)) hyCommKW2
  have hybotVW2 : yVW2 ∈ (⊥ : Subgroup VW2) := by
    rw [← hcentVW2 xVW2 hxVW2_ne]
    exact hyCentVW2
  have hyVW2_one : yVW2 = 1 := by
    simpa using hybotVW2
  ext
  exact congrArg (fun z : VW2 => (z : G)) hyVW2_one

private theorem section13_theorem_13_16_MaschkeFrobeniusInputSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    theorem_13_16_MaschkeFrobeniusInputSourceData W1 W2 Q V q := by
  exact ⟨section13_prime_q_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource,
    section13_theorem_13_16_KW2FrobeniusCoprimeSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d _hsource⟩

private theorem section13_theorem_13_16_MaschkeFrobeniusSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    theorem_13_16_MaschkeFrobeniusSourceData W1 W2 Q V := by
  have hsourceOrig := hsource
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have h2T := theorem_13_2 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  rcases h2T with
    ⟨_hQMF2, _hType, _hTypeIf, _hVcomm, _hFrobV, hQelem, _hQcard,
      _hvBound, _hcoh, _hTI, _hTau⟩
  rcases hsource with
    ⟨_hcase, _hptypeS, hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeT with
    ⟨hQMF, _hW2cyc, _hW2ne, _hW2Hall, hTcomp, hVleDer, _hVnil, _hW2norm,
      _hDercomp, _hQnotcyc, _hsecond, _hfit, _hfitDer, hW1leQinf,
      _hW1cyc, _hW1ne, _hcent, _hnormType⟩
  have hW1Q : W1 ≤ Q := hW1leQinf.trans inf_le_left
  have hQW2cent :
      Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 :=
    section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig
  have hKW2normW1 :
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) ≤
        Subgroup.normalizer (W1 : Set G) := by
    refine sup_le inf_le_right ?_
    intro w hwW2
    exact centralizer_le_normalizer W1
      (hQW2cent ((show W2 ≤ Q ⊔ W2 from le_sup_right) hwW2)).2
  have hTleNormQ : Tmax ≤ Subgroup.normalizer (Q : Set G) := by
    rcases hQMF with ⟨⟨hQT, hQnormT, _hQnil, _hQhallT⟩, _hmax⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).1 hQnormT
  have hKW2normQ :
      ((V ⊓ Subgroup.normalizer (W1 : Set G)) ⊔ W2) ≤
        Subgroup.normalizer (Q : Set G) := by
    refine sup_le ?_ ?_
    · exact (inf_le_left.trans (hVleDer.trans hTcomp.1)).trans hTleNormQ
    · exact hTcomp.2.1.trans hTleNormQ
  rcases section13_theorem_13_16_MaschkeFrobeniusInputSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig with ⟨hqprime, hcop, hfrob⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  letI : IsElementaryAbelian q Q := hQelem
  exact section13_theorem_13_16_MaschkeFrobeniusSourceData_of_inputs
    W1 W2 Q V q hW1Q hKW2normQ hKW2normW1 hcop hfrob

private theorem section13_theorem_13_16_KCentralizesQSourceData_of_sourceContext
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    theorem_13_16_KCentralizesQSourceData W1 W2 Q V := by
  exact section13_theorem_13_16_KCentralizesQSourceData_from_maschkeData
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource
    (section13_theorem_13_16_MaschkeFrobeniusSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hNleT)

private theorem section13_theorem_13_16_Vinf_normalizer_W1_le_D_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    V ⊓ Subgroup.normalizer (W1 : Set G) ≤ D := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  exact section13_theorem_13_16_Vinf_normalizer_W1_le_D_from_sourceData
    W1 W2 Q V D hD
    (section13_theorem_13_16_KCentralizesQSourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hNleT)

private theorem section13_theorem_13_16_Vinf_normalizer_W1_eq_bot_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    V ⊓ Subgroup.normalizer (W1 : Set G) = ⊥ := by
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, _hp_card, _hq_card, _hC, _hD, _hc_card,
      hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hsourceT := section13_hypothesis_13_1_sourceData_swap hsourceOrig
  have hd_one : d = 1 := theorem_13_12 Tmax Smax W W2 W1 Q P V U D C
    Tfam Sfam τT τS q p v u d c hsourceT
  have hD_card : Nat.card D = 1 := by
    rw [← hd_card, hd_one]
  have hD_bot : D = ⊥ := (Subgroup.card_eq_one (H := D)).1 hD_card
  have hKleD :
      V ⊓ Subgroup.normalizer (W1 : Set G) ≤ D :=
    section13_theorem_13_16_Vinf_normalizer_W1_le_D_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsourceOrig hNleT
  exact le_antisymm (hKleD.trans (le_of_eq hD_bot)) bot_le

/-- Source blocker for the Maschke/Frobenius step that removes the `V`-part in `(13.16)`. -/
private theorem section13_theorem_13_16_remove_V_part_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    Subgroup.normalizer (W1 : Set G) ≤ Q ⊔ W2 := by
  have hNleQKW2 :
      Subgroup.normalizer (W1 : Set G) ≤
        (Q ⊔ (V ⊓ Subgroup.normalizer (W1 : Set G))) ⊔ W2 :=
    section13_theorem_13_16_normalizer_W1_le_Q_sup_VinfN_sup_W2_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hNleT
  have hKbot :
      V ⊓ Subgroup.normalizer (W1 : Set G) = ⊥ :=
    section13_theorem_13_16_Vinf_normalizer_W1_eq_bot_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hNleT
  simpa [hKbot, sup_assoc] using hNleQKW2

/-- Peterfalvi `(13.16)` T-side decomposition, reduced to removing the `V`-part. -/
private theorem section13_theorem_13_16_Tnormalizer_le_Q_sup_W2_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hNleT : Subgroup.normalizer (W1 : Set G) ≤ Tmax) :
    Subgroup.normalizer (W1 : Set G) ≤ Q ⊔ W2 := by
  exact section13_theorem_13_16_remove_V_part_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
    p q u v c d hsource _hNleT

/-- Peterfalvi `(13.16)` normalizer containment, reduced to the T-side source blocker. -/
private theorem section13_theorem_13_16_normalizer_le_Q_sup_W2_of_sourceContext
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Subgroup.normalizer (W1 : Set G) ≤ Q ⊔ W2 := by
  have hNleT :
      Subgroup.normalizer (W1 : Set G) ≤ Tmax :=
    section13_theorem_13_16_normalizer_W1_le_Tmax_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  exact section13_theorem_13_16_Tnormalizer_le_Q_sup_W2_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource hNleT

/-- Peterfalvi `(13.16)`, reduced to the remaining normalizer containment source blocker. -/
public theorem theorem_13_16
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Subgroup.normalizer (W1 : Set G) = subgroupCentralizerIn (⊤ : Subgroup G) W1 ∧
        subgroupCentralizerIn (⊤ : Subgroup G) W1 = Q ⊔ W2 := by
  intro hsource
  have hQW2leC :
      Q ⊔ W2 ≤ subgroupCentralizerIn (⊤ : Subgroup G) W1 :=
    section13_theorem_13_16_Q_sup_W2_le_centralizer_W1_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  have hNleQW2 : Subgroup.normalizer (W1 : Set G) ≤ Q ⊔ W2 :=
    section13_theorem_13_16_normalizer_le_Q_sup_W2_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hsource
  have hCleN :
      subgroupCentralizerIn (⊤ : Subgroup G) W1 ≤ Subgroup.normalizer (W1 : Set G) := by
    intro x hx
    exact centralizer_le_normalizer W1 hx.2
  have hCeq : subgroupCentralizerIn (⊤ : Subgroup G) W1 = Q ⊔ W2 :=
    le_antisymm (hCleN.trans hNleQW2) hQW2leC
  exact ⟨le_antisymm (by simpa [hCeq] using hNleQW2) hCleN, hCeq⟩
end CFSG.Section13
