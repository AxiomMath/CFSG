module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qi
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 SigmaTwo4)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qj_map_map_symm (m : G) (K : Subgroup G) :
    (K.map (MulAut.conj m).toMonoidHom).map (MulAut.conj m).symm.toMonoidHom = K := by
  have h : (MulAut.conj m).symm.toMonoidHom.comp (MulAut.conj m).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [Subgroup.map_map, h, Subgroup.map_id]

theorem uc22p22qj_layer_map (m : G) (K : Subgroup G) :
    rankThreeLayer (K.map (MulAut.conj m).toMonoidHom) =
      (rankThreeLayer K).map (MulAut.conj m).toMonoidHom := by
  unfold rankThreeLayer
  refine (CFSG.LargeExtraspecial.Bridge.map_sSup_setOf (MulAut.conj m)
    (P := fun L => IsComponentOf L K)
    (P' := fun L => IsComponentOf L (K.map (MulAut.conj m).toMonoidHom)) ?_).symm
  intro N
  constructor
  · intro h
    have h1 := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv (MulAut.conj m).symm h
    rwa [uc22p22qj_map_map_symm, uc22p22qj_map_map_symm] at h1
  · intro h
    exact CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv (MulAut.conj m) h

theorem uc22p22qj_relPPrimeCore_map (p : ℕ) (m : G) (K : Subgroup G) :
    relPPrimeCore p (K.map (MulAut.conj m).toMonoidHom) =
      (relPPrimeCore p K).map (MulAut.conj m).toMonoidHom := by
  unfold relPPrimeCore
  refine (CFSG.LargeExtraspecial.Bridge.map_sSup_setOf (MulAut.conj m)
    (P := fun N => N ≤ K ∧ (N.subgroupOf K).Normal ∧ Nat.Coprime p (Nat.card N))
    (P' := fun N => N ≤ K.map (MulAut.conj m).toMonoidHom ∧
      (N.subgroupOf (K.map (MulAut.conj m).toMonoidHom)).Normal ∧ Nat.Coprime p (Nat.card N)) ?_).symm
  intro N
  have hc : Nat.card (N.map (MulAut.conj m).toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h1' : N ≤ K := (Subgroup.map_le_map_iff_of_injective (MulAut.conj m).injective).1 h1
    refine ⟨h1', ?_, by rwa [hc] at h3⟩
    have h4 := CFSG.LargeExtraspecial.Bridge.normal_subgroupOf_map (MulAut.conj m).symm h1 h2
    rwa [uc22p22qj_map_map_symm, uc22p22qj_map_map_symm] at h4
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Subgroup.map_mono h1, CFSG.LargeExtraspecial.Bridge.normal_subgroupOf_map (MulAut.conj m) h1 h2,
      by rwa [hc]⟩

theorem uc22p22qj_normalizer_map (m : G) {Y N : Subgroup G}
    (h : normalizer ((Y.map (MulAut.conj m⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ N) :
    normalizer (Y : Set G) ≤ N.map (MulAut.conj m).toMonoidHom := by
  intro g hg
  rw [uc22p22qi_mem_map]
  apply h
  refine uc22p22qk_mem_normalizer fun w hw => ?_
  obtain ⟨y, hy, rfl⟩ := hw
  refine ⟨g * y * g⁻¹, (mem_normalizer_iff.1 hg y).1 hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

theorem uc22p22qj_map_map_inv (m : G) (K : Subgroup G) :
    (K.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom = K := by
  ext x
  rw [uc22p22qi_mem_map, uc22p22qi_mem_map]
  simp only [inv_inv]
  rw [show m * (m⁻¹ * x * m) * m⁻¹ = x by group]

theorem uc22p22qj_clauseTwo_map {N P P₀ : Subgroup G} {p : ℕ} (m : G)
    (h : CFSG.Open.uniqueFourClauseTwo N P P₀ p) :
    CFSG.Open.uniqueFourClauseTwo (N.map (MulAut.conj m).toMonoidHom) (P.map (MulAut.conj m).toMonoidHom)
      (P₀.map (MulAut.conj m).toMonoidHom) p := by
  obtain ⟨h1, h2, h3, ⟨hf, n, hn, ⟨e⟩⟩, h5, h6, h7, h8⟩ := h
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hC : centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (P₀ : Set G)).map (MulAut.conj m).toMonoidHom := uc22p22qi_centralizer_map m P₀
  have hLay : uniqueFourLayer (centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) =
      (uniqueFourLayer (centralizer (P₀ : Set G))).map (MulAut.conj m).toMonoidHom := by
    rw [hC]
    exact uc22p22qj_layer_map m _
  refine ⟨Subgroup.map_mono h1, by rw [Subgroup.card_map_of_injective hinj]; exact h2,
    uc22p22qi_weak_map h3, ⟨hf, n, hn, ⟨?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · rw [hLay]
    exact (Subgroup.equivMapOfInjective _ _ hinj).symm.trans e
  · rw [hLay]
    intro hle
    exact h5 ((Subgroup.map_le_map_iff_of_injective hinj).1 hle)
  · intro S hS hSp
    have hS' : S ≤ (centralizer (P₀ : Set G) ⊓
        centralizer (uniqueFourLayer (centralizer (P₀ : Set G)) : Set G)).map (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ hinj, ← uc22p22qi_centralizer_map m, ← uc22p22qi_centralizer_map m, ← hLay]
      exact hS
    have hS₀ : S.map (MulAut.conj m).symm.toMonoidHom ≤ centralizer (P₀ : Set G) ⊓
        centralizer (uniqueFourLayer (centralizer (P₀ : Set G)) : Set G) := by
      have h2 := Subgroup.map_mono (f := (MulAut.conj m).symm.toMonoidHom) hS'
      rwa [uc22p22qj_map_map_symm] at h2
    have hcyc := h6 _ hS₀ (hSp.map _)
    haveI := hcyc
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective S (MulAut.conj m).symm.toMonoidHom
      (MulAut.conj m).symm.injective).symm (Subgroup.equivMapOfInjective S _ _).symm.surjective
  · have hfr := uc22p22qi_frobenius_map m h7
    rw [Subgroup.map_sup, Subgroup.map_sup] at hfr
    have e1 : uniqueFourPrimeCore p (N.map (MulAut.conj m).toMonoidHom) =
        (uniqueFourPrimeCore p N).map (MulAut.conj m).toMonoidHom := uc22p22qj_relPPrimeCore_map p m N
    have e2 : pCoreOf 2 (N.map (MulAut.conj m).toMonoidHom) = (pCoreOf 2 N).map (MulAut.conj m).toMonoidHom :=
      CFSG.LargeExtraspecial.Bridge.pCoreOf_map 2 (MulAut.conj m) N
    have e3 : uniqueFourPrimeCore p (centralizer ((P₀.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G)) =
        (uniqueFourPrimeCore p (centralizer (P₀ : Set G))).map (MulAut.conj m).toMonoidHom := by
      rw [hC]
      exact uc22p22qj_relPPrimeCore_map p m _
    rw [e1, e2, e3]
    exact hfr
  · intro P₁ hP₁ hcard hne
    refine uc22p22qj_normalizer_map m ?_
    have hY₀P : P₁.map (MulAut.conj m⁻¹).toMonoidHom ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      have := uc22p22qi_mem_map.1 (hP₁ hy)
      simpa [MulAut.conj_apply, mul_assoc] using this
    refine h8 _ hY₀P (by rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]; exact hcard) ?_
    intro heq
    apply hne
    rw [← uc22p22qj_map_map_inv m P₁, heq]

theorem uc22p22qj_exists_conj (hU : CFSG.Open.uniqueFourUnique G) {M N : Subgroup G}
    (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M) (hN : CFSG.Open.uniqueFourIsMaxTwoLocal N) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma M) (hpN : p ∈ CFSG.Open.uniqueFourSigma N) :
    ∃ g : G, CFSG.Open.uniqueFourConj g N = M := by
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  obtain ⟨PM, hPM, -⟩ := UC6.exists_sylow_le_of_sigma hU hM hp
  obtain ⟨PN, hPN, -⟩ := UC6.exists_sylow_le_of_sigma hU hN hpN
  obtain ⟨g, hg⟩ := UC6.exists_le_uniqueFourConj_sylow (PM.isPGroup') PN
  have hPMN : (PM : Subgroup G) ≤ CFSG.Open.uniqueFourConj g N := hg.trans (UC6.uniqueFourConj_mono hPN g)
  have hN' : CFSG.Open.uniqueFourIsMaxTwoLocal (CFSG.Open.uniqueFourConj g N) :=
    UC6.isMaxTwoLocal_conj hN g
  have hpN' : p ∈ CFSG.Open.uniqueFourSigma (CFSG.Open.uniqueFourConj g N) :=
    UC6.mem_uniqueFourSigma_conj hpN g
  have h4 : 2 ≤ Open.pRank p (PM : Subgroup G) :=
    le_trans (by norm_num) (UC6.four_le_pRank_sylow hp.1 PM)
  have hle : M ≤ CFSG.Open.uniqueFourConj g N := UC6.sec61 hU hN' hpN' hPMN h4 hM.1 hPM
  exact ⟨g, hM.2 _ hN'.1 hle⟩

theorem uc22p22qj_exists_pair (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig2) :
    ∃ P P₀ : Subgroup G, UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀ ∧ 5 ≤ p ∧ IsMulCommutative P ∧
      CFSG.Open.uniqueFourClauseTwo S.M P P₀ p := by
  have hp' := hp
  obtain ⟨hpσ, hβ, N, hN, hpN, P', hP'N, -, h5, -, hab, P₀', hcl⟩ := hp'
  obtain ⟨g, hg⟩ := uc22p22qj_exists_conj hU S.maxLocal hN hpσ hpN
  haveI : Fact p.Prime := ⟨hpσ.1.1⟩
  have hM : N.map (MulAut.conj g⁻¹).toMonoidHom = S.M := hg
  have hcl' := uc22p22qj_clauseTwo_map g⁻¹ hcl
  rw [hM] at hcl'
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hPsyl : IsSylowOf p ((P' : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom) S.M := by
    have h1 : IsSylowOf p (P' : Subgroup G) N := uc22p22q_isSylowOf_of_sylow P' hP'N
    rw [isSylowOf_iff] at h1 ⊢
    obtain ⟨hle, hpg, hrel⟩ := h1
    refine ⟨?_, hpg.of_equiv (Subgroup.equivMapOfInjective _ _ hinj), ?_⟩
    · rw [← hM]
      exact Subgroup.map_mono hle
    · rw [← hM, Subgroup.relIndex_map_map_of_injective _ _ hinj]
      exact hrel
  refine ⟨(P' : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom, P₀'.map (MulAut.conj g⁻¹).toMonoidHom,
    ⟨hp, hPsyl, hcl'.1, hcl'.2.1, ?_⟩, h5, ?_, hcl'⟩
  · intro hle
    exact hcl'.2.2.2.2.1 ((uc22p22q_layer_le _).trans hle)
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

@[expose] def Frob4 (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), UC6.Hyp612 D p P P₀ → 5 ≤ p → IsMulCommutative P →
    CFSG.Open.uniqueFourClauseTwo D.M P P₀ p →
    CFSG.Open.uniqueFourIsFrobenius
      (CFSG.Open.uniqueFourPrimeCore p D.M ⊔ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G))
      (CFSG.Open.pCoreOf 2 D.M) (centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G))

theorem sigma2Print_ofSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hF : Frob4 (UC6.dataOfSetup4 hS hU S)) : Sigma2Print (UC6.dataOfSetup4 hS hU S) := by
  intro p hp
  obtain ⟨P, P₀, hH, h5, hab, hcl⟩ := uc22p22qj_exists_pair hS hU S hp
  have hsolv : Group.IsSolvable ↥S.M := UC6S846.solvable_of_sigmaTwo4 hU S.maxLocal hp.1 hp.2
  have hcl' := hcl
  obtain ⟨-, -, hwc, hlay, hnot, -, -, hN⟩ := hcl'
  exact ⟨P, P₀, hH, h5, hsolv, hwc, hlay, hnot, hF p P P₀ hH h5 hab hcl, hN⟩

theorem r613cent_ofSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) :
    UC6.R613Cent (UC6.dataOfSetup4 hS hU S) := by
  intro p P' P₀' hH'
  obtain ⟨P, P₀, hH, -, hab, -⟩ := uc22p22qj_exists_pair hS hU S hH'.mem_sig2
  haveI : Fact p.Prime := ⟨(UC6.dataOfSetup4 hS hU S).sig_prime p (by
    rw [(UC6.dataOfSetup4 hS hU S).sig_sub]
    exact Or.inl (Or.inr hH'.mem_sig2)) |>.1⟩
  obtain ⟨k, -, hk⟩ := hH.sylow.exists_mem_conj hH'.sylow
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hy' := (hk y).1 hy
  have ha' := (hk a).1 (Subgroup.mem_inf.1 ha).1
  have h1 := congrArg Subtype.val (hab.is_comm.comm ⟨k⁻¹ * a * k, ha'⟩ ⟨k⁻¹ * y * k, hy'⟩)
  have h2 : k⁻¹ * a * k * (k⁻¹ * y * k) = k⁻¹ * y * k * (k⁻¹ * a * k) := h1
  calc a * y = k * (k⁻¹ * a * k * (k⁻¹ * y * k)) * k⁻¹ := by group
    _ = k * (k⁻¹ * y * k * (k⁻¹ * a * k)) * k⁻¹ := by rw [h2]
    _ = y * a := by group

end CFSG.LocalAnalysis.UniquenessCase.UC22
