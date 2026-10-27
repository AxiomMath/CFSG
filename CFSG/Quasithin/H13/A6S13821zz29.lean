module

public import CFSG.Quasithin.H13.A6S13821zz27
public import CFSG.Quasithin.H13.A6S13821zz28
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.F918C5
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.A6S13816b
public import CFSG.Quasithin.H13.A6S13821y
public import CFSG.Quasithin.H13.A6S13821zz24

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.S153L

attribute [local instance] commGroupOfFact

namespace A6S20

theorem ksCover_of_quot_center {Y : Type} [Group Y] (hU : IsPSU 3 2 3 (Y ⧸ Subgroup.center Y)) :
    KsCover Y :=
  ⟨Y ⧸ Subgroup.center Y, inferInstance, ⊤, 3,
    (Subgroup.topEquiv (G := Y ⧸ Subgroup.center Y)).symm.toMonoidHom.comp
      (QuotientGroup.mk' _), le_rfl, ⟨1, rfl⟩,
    Or.inr (Or.inr (Or.inl
      (IsPSU.of_mulEquiv (Subgroup.topEquiv (G := Y ⧸ Subgroup.center Y)).symm hU))),
    (Subgroup.topEquiv (G := Y ⧸ Subgroup.center Y)).symm.surjective.comp
      (QuotientGroup.mk'_surjective _), fun x hx => by
      have h1 : (QuotientGroup.mk' (Subgroup.center Y)) x = 1 :=
        (Subgroup.topEquiv (G := Y ⧸ Subgroup.center Y)).symm.injective (by simpa using hx)
      exact (QuotientGroup.eq_one_iff x).mp h1⟩

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_natural_su38_13820b
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection) (h42 : AsB42)
    (h45 : AsB45) {H K : Subgroup G} {n : ℕ} (hC : S.Ctx13820 H K n) (hL1K : S.L1 ≤ K)
    (hU : IsPSU 3 2 3 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) :
    ∃ hF : HypF918 T V L (fsuV1 T V) S.V3 H K, ∃ I : Subgroup G, fsuV1 T V ≤ I ∧
      ∃ hIU : I ≤ conjClosure S.V3 H, H ≤ Subgroup.normalizer (I : Set G) ∧
        (haveI := factElem hF hIU
         BinaryNaturalSU3 (autIH (fsuV1 T V) I H K) ⊤ ⊥ 3) ∧
        ∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) →
          k ∈ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hH, hK, hKn, hHK, -, -⟩ := hC
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36c h37 h38 h139 h1334 h13 hS hH hK
  have e : (K ⊔ T) ⊔ S.L1 = H := by
    rw [hHK, sup_assoc, sup_comm T S.L1]
  rw [e] at hF
  have hSQ := S.sqtkGroup_of_mem_Hz hH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHKT : H = K ⊔ T := by
    rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have h1 : IsPSU 3 2 3 ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    IsPSU.of_mulEquiv (QuotientGroup.congr _ _ e₁.symm (Subgroup.map_center_eq e₁.symm)) hU
  have hq := S.isQuasisimple_modO2 h36c h139 h1334 h13 hS hH hK
  have hcQZ := A6S20.card_of_isPSU38 h1
  have hcQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 16547328 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)), hcQZ, hZ]
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFe := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hne : autIH (fsuV1 T V) I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have hker : CFSG.pCore 2 ↥K ≤ (toAutI hF I).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    apply hF.actH_eq_one_of_mem_pCoreOf hIU
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp) hx1
  let φ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autIH (fsuV1 T V) I H K) :=
    QuotientGroup.lift _ (toAutI hF I) hker
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := toAutI_surjective hF I y
    exact ⟨QuotientGroup.mk x, hx⟩
  have : Nontrivial ↥(autIH (fsuV1 T V) I H K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨⟨eZ⟩, hdZ⟩ := A6S20.quotCenter_of_surjective hq hφs
  have hcL : Nat.card ↥(autIH (fsuV1 T V) I H K) = 5515776 ∨
      Nat.card ↥(autIH (fsuV1 T V) I H K) = 16547328 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autIH (fsuV1 T V) I H K)), ← Nat.card_congr eZ.toEquiv, hcQZ]
    rw [hZ] at hdZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hdZ with h | h
    · left
      rw [h]
    · right
      rw [h]
  have hKs : KsCover ↥(autIH (fsuV1 T V) I H K) :=
    A6S20.ksCover_of_quot_center (IsPSU.of_mulEquiv eZ h1)
  have hDD := d31_of_hyp hF hSQ hIU hV₁I hirr'
  obtain ⟨B, hA⟩ := qOff_of_hyp hF hIU hV₁I hKI hnt
  have hMp : autIH (fsuV1 T V) I H (conjClosure K T) = autIH (fsuV1 T V) I H K := by
    rw [hK₀]
  have hD3 : D3Std (autIH (fsuV1 T V) I H H) (autIH (fsuV1 T V) I H (conjClosure K T))
      (autIH (fsuV1 T V) I H T) (autIH (fsuV1 T V) I H K)
      (subM (fsuV1 T V) (conjClosure I H) I) :=
    ⟨hDD, hA.qhat_VT hDD.exp, hirr'⟩
  have hqM := hA.qhat_M hDD.sylow.1
  have hq2 := hA.qOf_VT hDD.exp
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases (F918_4' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4).2 with hHI | (⟨hVT, -⟩ | h3)
    · exact hHI
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t' ht'
        have hst := stab_of_orbSup_eq hVT.symm _ (actH_mem_autIH_of_mem (I := I) hF hTH ht')
        exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
          (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨t', hTH ht'⟩).mp hst
      rw [hHKT]
      exact sup_le hKI' hTI
    · exact (A6S20.false_of_d310Two_card_su3 hcL h3.1).elim
  have hMst : autIH (fsuV1 T V) I H H ≤ stabSub (subM (fsuV1 T V) (conjClosure I H) I) := by
    rw [autIH_eq_map hF (le_refl H)]
    exact (map_actH_le_stabSub_iff hF.H_le_normalizer_V₁
      (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I).mpr hHI
  have hVtop : subM (fsuV1 T V) (conjClosure I H) I = ⊤ := by
    have hgen := hDD.gen
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun m hm => ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (hMst hm v).2 hv
  have hfaith : autIH (fsuV1 T V) I H K ⊓ centSub (subM (fsuV1 T V) (conjClosure I H) I) = ⊥ := by
    rw [hVtop]
    refine eq_bot_iff.2 fun g hg => ?_
    have : g = 1 := MulEquiv.ext fun u => hg.2 u trivial
    exact this ▸ Subgroup.one_mem _
  obtain ⟨-, hnat, hcard⟩ := A6S20.natural_su3_of_d3Std hA21 h42 h45 hD310 hD3 hMp hqM hq2
    hfaith hKs hcL
  rw [hVtop, top_inf_eq] at hnat
  have hW2 : ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure I H)), w ^ 2 = 1 := fun w =>
    Subtype.ext (by
      simpa using (Fact.out : IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure I H))).2 w w.2)
  have hcomm : commV (autIH (fsuV1 T V) I H K) = ⊤ := by
    have h1 := hirr'.1.2.2.1
    rw [hVtop] at h1
    rw [eq_top_iff, ← h1, XMod.commOf, Subgroup.closure_le]
    rintro _ ⟨a, l, -, rfl⟩
    exact Subgroup.subset_closure ⟨(a : MulAut _), hMp ▸ a.2, l, rfl⟩
  obtain ⟨z, hzL, hz3, hzc, hfp⟩ := A6S20.exists_scalar_su38 hnat
  have hC0 := A6S20.fixV_eq_bot_of_scalar hW2 hcomm hzL hz3 hzc fun w hw => hfp w trivial hw
  rw [hC0] at hnat
  refine ⟨hF, I, hV₁I, hIU, hHI, hnat, fun k hk hku => ?_⟩
  have hFU := factElem hF (le_conjClosure S.V3 H)
  have hsU : Function.Surjective (toAutI hF S.V3) := toAutI_surjective hF S.V3
  have hsI : Function.Surjective (toAutI hF I) := toAutI_surjective hF I
  have hcU : Nat.card ↥(autIH (fsuV1 T V) S.V3 H K) = 16547328 := by
    rw [← hcQ]
    exact (Nat.card_congr e₁.toEquiv).symm
  have hkerU : ∀ x : ↥K, toAutI hF S.V3 x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [toAutI_eq_one_iff]
    exact ⟨fun hx => mem_pCoreOf_of_actH_eq_one hF hx,
      fun hx => hF.actH_eq_one_of_mem_pCoreOf (le_conjClosure S.V3 H) hx⟩
  have hle : (toAutI hF S.V3).ker ≤ (toAutI hF I).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [toAutI_eq_one_iff]
    exact hF.actH_eq_one_of_mem_pCoreOf hIU ((hkerU x).mp hx)
  have hidx : (toAutI hF S.V3).ker.index = (toAutI hF I).ker.index := by
    rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsU,
      MonoidHom.range_eq_top.mpr hsI, Subgroup.card_top, Subgroup.card_top, hcU, hcard]
  have heq : (toAutI hF S.V3).ker = (toAutI hF I).ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h2 := (toAutI hF S.V3).ker.card_mul_index
    have h3 := (toAutI hF I).ker.card_mul_index
    rw [hidx] at h2
    have hpos : 0 < (toAutI hF I).ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.eq_of_mul_eq_mul_right hpos (h2.trans h3.symm)).symm.le
  have hkI : toAutI hF I ⟨k, hk⟩ = 1 := by
    rw [toAutI_eq_one_iff, A6Tv.actH_eq_one_iff hF.H_le_normalizer_V₁
      (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H)]
    exact hku
  have hkU : (⟨k, hk⟩ : ↥K) ∈ (toAutI hF S.V3).ker := by
    rw [heq]
    exact hkI
  exact (hkerU _).mp hkU

end Setting4

end CFSG.Quasithin.H13.A6
