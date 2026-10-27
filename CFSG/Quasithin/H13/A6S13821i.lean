module

public import CFSG.Quasithin.Background.OrbSupStab
public import CFSG.Quasithin.H13.A6S13821e
public import CFSG.Quasithin.H13.A6S13821g
public import CFSG.Quasithin.H13.A6S13821h
public import CFSG.Quasithin.H13.L32AC36c
public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.EmptyFaithful.F918C5

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace A6Hat7

theorem false_of_d310Two_card {W : Type} [CommGroup W] [Finite W] {T L : Subgroup (MulAut W)}
    {U : Subgroup W} (h : D310Two T L U) (hc : Nat.card L = 7560) : False := by
  have hv : padicValNat 2 (Nat.card L) = 3 := by
    rw [hc]
    exact L32A.C.padicValNat_two_pow_mul_odd (a := 3) (u := 945) (by decide)
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hn := L32A.C.one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    rw [hX, L32A.C.padicValNat_two_pow_mul_odd ((L32A.C.odd_two_pow_sub_one_of_pos
      (by omega)).mul (L32A.C.odd_two_pow_sub_one_of_pos (by omega)))] at hv
    have hn1 : n = 1 := by omega
    subst hn1
    rw [hc] at hX
    norm_num at hX
  ·
    have hn := L32A.C.one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [hX0, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    rw [hX, L32A.C.padicValNat_two_pow_mul_odd ((L32A.C.odd_two_pow_sub_one_of_pos
      (by omega)).mul (L32A.C.odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have h1 : Nat.card ↥L ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 K) :=
      Subgroup.card_dvd_of_surjective (f := π) hπ.1
    rw [card_statedSL1527d (d := 4) (by norm_num), hK, hc] at h1
    norm_num [Finset.prod_Icc_succ_top] at h1
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 7))) π hπ.1
    have h2 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    omega

theorem mem_stabSub_of_eq_orbSup {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) :
    t ∈ CFSG.Quasithin.stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_eq_orbSup h ht

end A6Hat7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

attribute [local instance] commGroupOfFact in
theorem false_of_hat7_core (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hF : HypF918 T V L (fsuV1 T V) S.V3 H K) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hHeq : H = K ⊔ T) (hL1K : S.L1 ≤ K)
    (hHat : IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : K ∈ cComp H := hF.K_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hF.T_le_H
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := hTH.trans hHK
  have hK₀ : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hTN ht) k).mp hk) (le_conjClosure K T)
  obtain ⟨hq, hZ, ⟨eA7⟩⟩ := hHat
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_le_normalizer_V₁
  obtain ⟨c, hcX, hc3, hρ, hcV3, hconj⟩ :=
    S.exists_c_hat h139 h1334 h13 hS hH (A6Hat7.oTwoRes_solvRad_ne_bot hKc hZ)
  have hcK : (c : G) ∈ K := hL1K (S.oTwoRes_solvRad_le_L1 h139 h1334 h13 hS hH hcX)
  have hcH : (c : G) ∈ H := hKH hcK
  have hN := S.norm_mem_V1 hS hH hcH hc3 hρ hcV3 hconj
  have hfpf : ∀ u ∈ conjClosure S.V3 H, (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ fsuV1 T V →
      u ∈ fsuV1 T V := fun u hu hfix => S.mem_V1_of_fix hS hH hcH hN hu hfix
  have hcZ : ((⟨c, hcK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
    A6Hat7.mem_center_of_mem_solvRad hKH hq (oTwoRes_le _ hcX)
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hfact := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hIHU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure I H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ hIU
  have hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hcI : ¬ ∀ u ∈ conjClosure I H, (c : G) * u * (c : G)⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro hall
    apply hnt
    intro k hk i hi
    have hiV : i ∈ fsuV1 T V :=
      hfpf i (hIHU (le_conjClosure I H hi)) (hall i (le_conjClosure I H hi))
    have h1 : k * i * k⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp (hV₁ (hF.K₀_le_H hk)) i).mp hiV
    exact (fsuV1 T V).mul_mem h1 ((fsuV1 T V).inv_mem hiV)
  obtain ⟨ψ⟩ := A6Hat7.nonempty_mulEquiv_autIH_of hF hIU hZ hcZ hcI
  have hcard : Nat.card ↥(autIH (fsuV1 T V) I H K) = 7560 := by
    rw [← Nat.card_congr ψ.toEquiv]
    exact A6Hat7.card_of_isHat_alt7 ⟨hq, hZ, ⟨eA7⟩⟩
  have h4 := (F918_4' hF (S.sqtkGroup_of_mem_Hz hH) hK₀ hV₁I hIU W hW hirrU hD310 hD391
    hI4).2
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with h4 | (⟨hVT, -⟩ | h3)
    · exact h4
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t ht
        have hst := A6Hat7.mem_stabSub_of_eq_orbSup hVT
          (actH_mem_autIH_of_mem (I := I) hF hTH ht)
        exact (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV₁I (le_conjClosure I H)
          ⟨t, hTH ht⟩).mp hst
      rw [hHeq]
      exact sup_le (hK₀ ▸ hKI) hTI
    · exact (A6Hat7.false_of_d310Two_card h3 hcard).elim
  have hcI' : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  set W' := ↥(tildeOf (fsuV1 T V) (conjClosure I H)) with hW'
  set φ := actH hV₁ hIH with hφ
  set Lg := autIH (fsuV1 T V) I H K with hLg
  have hAL : autIH (fsuV1 T V) I H (conjClosure K T) = Lg := by rw [hK₀]
  have hW2 : ∀ w : W', w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hfact.out.2 _ w.2)
  have htop : subM (fsuV1 T V) (conjClosure I H) I = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨a, haIH, haw⟩ := exists_mk_of_mem_tilde w
    rw [mem_subM_iff, ← haw]
    rw [hcI'] at haIH
    exact (secMk_mem_tildeOf_iff hV₁I).mpr haIH
  have hcmem : φ ⟨c, hcH⟩ ∈ autIH (fsuV1 T V) I H (conjClosure K T) :=
    actH_mem_autIH_of_mem (I := I) hF hF.K₀_le_H (le_conjClosure K T hcK)
  have hfix : XMod.fixed ↥(autIH (fsuV1 T V) I H (conjClosure K T)) (⊤ : Subgroup W') = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨-, hw⟩
    obtain ⟨a, haIH, haw⟩ := exists_mk_of_mem_tilde w
    have hw' : w = modMk hIHN (a : G) haIH := Subtype.ext haw.symm
    have h1 := hw ⟨φ ⟨c, hcH⟩, hcmem⟩
    have h2 : φ ⟨c, hcH⟩ w = w := h1
    rw [hw', hφ, actH_modMk hV₁ hIHN hIH ⟨c, hcH⟩ haIH] at h2
    have h3 := (A6Tv.modMk_conj_eq_iff' hIHN haIH _).1 h2
    have haV : (a : G) ∈ fsuV1 T V := hfpf _ (hIHU haIH) h3
    rw [Subgroup.mem_bot, hw']
    exact Subtype.ext ((secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G))
      (B := fsuV1 T V) (x := ⟨(a : G), hIHN haIH⟩)).mpr haV)
  obtain ⟨hlt, hirrsec⟩ := hirr'.1.2.2.2
  rw [htop, hfix] at hlt
  rw [htop, hfix] at hirrsec
  have hqL : CFSG.IsQuasisimple ↥Lg := CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ hq
  have hcen : Nat.card (Subgroup.center ↥Lg) = 3 := by
    rw [← hZ, ← Subgroup.map_center_eq ψ, Subgroup.card_map_of_injective ψ.injective]
  have heL : Nonempty ((↥Lg ⧸ Subgroup.center ↥Lg) ≃* ↥(alternatingGroup (Fin 7))) :=
    ⟨(QuotientGroup.congr _ _ ψ (Subgroup.map_center_eq ψ)).symm.trans eA7⟩
  have hZL : Subgroup.center ↥Lg ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcen
    omega
  have hirrL : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lg := by
    refine ⟨?_, fun U hU => ?_⟩
    · obtain ⟨w, -, hw⟩ := IsConcreteLE.exists_of_lt hlt
      exact nontrivial_of_ne w 1 fun h => hw (h ▸ Subgroup.one_mem _)
    · refine hirrsec U (fun a l hl => ?_) bot_le le_top
      have ha : (a : MulAut W') ∈ Lg := hAL ▸ a.2
      exact hU _ ha l hl
  obtain ⟨B, hB, -⟩ := hF.F918_2
  have hBH : B ≤ H := (hB.1.trans hF.pCoreOf_L₁T_le_T).trans hTH
  obtain ⟨-, -, hQ⟩ := hF.F918_3_weak (X := H) hIU hKI hnt hB (Or.inr rfl)
  obtain ⟨⟨hA2, hr⟩, -⟩ := hQ
  set E := autIH (fsuV1 T V) I H B with hE
  have hEN : E ≤ Subgroup.normalizer (Lg : Set (MulAut W')) := by
    rw [hE, hLg, autIH_eq_map hF hBH, autIH_eq_map hF hKH]
    refine le_trans (Subgroup.map_mono ?_) (map_le_normalizer_map_of_le_normalizer φ hKH hHK)
    rw [Subgroup.subgroupOf_self]
    exact le_top
  have hle : Nat.card W' ≤ Nat.card ↥E ^ 2 * Nat.card ↥(fixV E) := (rAV_le_two_iff hW2 hA2).1 hr
  have hlt' := B45Exc.threeA7Exclusion2F_holds W' (fun w => by rw [← pow_two]; exact hW2 w) Lg
    E hqL hirrL heL hZL hEN hA2.2.1 hA2.2.2
  have hlt'' : Nat.card ↥E ^ 2 * Nat.card ↥(fixV E) < Nat.card W' := hlt'
  omega

theorem not_isHat7 (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hS : S.Hyp138)
    {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ IsHat (↥K ⧸ CFSG.pCore 2 ↥K) ↥(alternatingGroup (Fin 7)) := by
  intro hHat
  obtain ⟨-, hH₀, -, hKc, hKN₀, hF⟩ := S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  have hL1K := S.L1_le_of_hat7 hF318 h36 h38 hH₀ hKc hKN₀ hHat
  have hHeq : K ⊔ (S.L1 ⊔ T) = K ⊔ T := by
    rw [← sup_assoc, sup_eq_left.mpr hL1K]
  exact S.false_of_hat7_core h139 h1334 h13 hD310 hD391 hI4 hS hH₀ hF hKN₀ hHeq hL1K hHat

end Setting4

theorem case13821Hat7_holds (h16 : Lem13816)
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hF318 : A318Facts) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) : Case13821Hat7 :=
  fun _ _ _ _ _ _ S hS _ hH _ hK =>
    S.not_isHat7 h16 h36c h36 h37 h38 hF318 h139 h1334 h13 hD310 hD391 hI4 hS hH hK

end CFSG.Quasithin.H13.A6
