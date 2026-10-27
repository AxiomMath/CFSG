module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2G1
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2D1
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Odd
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2G23
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2G4
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9L2
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Core
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9a
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9K
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KN
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KRC
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E5a
public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.ThreeC
open scoped IsMulCommutative commutatorElement

structure A2Leaves : Prop where
  c1 : Leaf_C1
  e5c : Leaf_E5c
  e6ii : Leaf_E6ii
  e7 : Leaf_E7
  ks1 : Leaf_KS1
  ks2 : Leaf_KS2

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem caseB_false (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (hL : A2Leaves)
    (c : A2Cfg G T M L D H K q) (hV : ¬ a2V L T ≤ a2TC K T) : False := by
  obtain ⟨t, ht, htK⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.nf.TK hcon
  obtain ⟨v, hvV, hv1, hv2⟩ := leaf_C3s_of h37 h38 G T M L D H K q c hV t ht htK
  have hvR : v ∈ a2R H := c.V_le_R hvV
  have h5 := hL.c1 nfa2_G1 nfa2_G3 G T M L D H K q c t ht htK v hvR hv1 hv2
  have hQC : a2N0 K T ⊓ a2Q L T ≤ a2N0 K T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine inf_le_inf_left _ ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    have hVC := (Hyp331.vPlus_reduced c.nf.hyp.toSetup331).1 hvV
    exact (Subgroup.mem_centralizer_iff.mp hVC.2 x hx).symm
  have hR2 : IsPGroup 2 (a2R H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have h1 : mIdx (a2N0 K T) (a2N0 K T ⊓ Subgroup.centralizer ({v} : Set G)) ≤
      mIdx (a2N0 K T) (a2N0 K T ⊓ a2Q L T) := mIdx_anti_of_le hQC
  have h2 : mIdx (a2N0 K T) (a2Q L T ⊓ a2N0 K T) ≤ mIdx (a2R H) (a2Q L T) :=
    mIdx_inf_le_mIdx hR2 (c.N0_le_TC.trans c.TC_le_R)
  rw [inf_comm] at h2
  have h3 := leaf_LSRQ_of h9 hGA G T M L D H K q c
  omega

theorem centralizerMod_sup_eq {Z U S S' : Subgroup G}
    (hN : S ⊔ S' ≤ Subgroup.normalizer (Z : Set G))
    (hS' : ∀ u ∈ U, ∀ s ∈ S', u * s * u⁻¹ * s⁻¹ ∈ Z) :
    centralizerMod Z U (S ⊔ S') = centralizerMod Z U S := by
  refine le_antisymm (centralizerMod_anti_right U le_sup_left) ?_
  rintro u ⟨huU, huN, hu⟩
  refine ⟨huU, huN, fun x hx => ?_⟩
  rw [Subgroup.sup_eq_closure] at hx
  have key : x ∈ Subgroup.normalizer (Z : Set G) ∧ u * x * u⁻¹ * x⁻¹ ∈ Z := by
    refine Subgroup.closure_induction (p := fun x _ =>
      x ∈ Subgroup.normalizer (Z : Set G) ∧ u * x * u⁻¹ * x⁻¹ ∈ Z) ?_ ?_ ?_ ?_ hx
    · rintro x (hxS | hxS')
      · exact ⟨hN (Subgroup.mem_sup_left hxS), hu x hxS⟩
      · exact ⟨hN (Subgroup.mem_sup_right hxS'), hS' u huU x hxS'⟩
    · exact ⟨Subgroup.one_mem _, by simpa using Z.one_mem⟩
    · rintro x y _ _ ⟨hxN, hx⟩ ⟨hyN, hy⟩
      refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
      have h1 : x * (u * y * u⁻¹ * y⁻¹) * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxN _).mp hy
      have e : u * (x * y) * u⁻¹ * (x * y)⁻¹ =
          (u * x * u⁻¹ * x⁻¹) * (x * (u * y * u⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact Z.mul_mem hx h1
    · rintro x _ ⟨hxN, hx⟩
      refine ⟨Subgroup.inv_mem _ hxN, ?_⟩
      have h1 : x⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp (Z.inv_mem hx)
      have e : u * x⁻¹ * u⁻¹ * x⁻¹⁻¹ = x⁻¹ * (u * x * u⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact h1
  exact key.2

theorem e8_false (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hL : A2Leaves)
    (c : A2Cfg G T M L D H K q) (e5a : E5aConcl L K T H) (e7 : E7Concl L K T H) : False := by
  unfold E7Concl at e7
  obtain ⟨B, hBR, hBTC, hB⟩ := e7
  obtain ⟨b, hbB, hbTC⟩ : ∃ b ∈ B, b ∉ a2TC K T := by
    by_contra hcon
    push Not at hcon
    exact hBTC fun x hx => hcon x hx
  have hks1 := hL.ks1 nfa2_G1 nfa2_G2 nfa2_G3 G T M L D H K q c e5a
  have hle := hB
  have hR2 : IsPGroup 2 (a2R H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have h3 : 3 ≤ a2Off (a2Z T) (a2UH L T H K) B := by
    refine (hks1 b (hBR hbB) hbTC).trans ?_
    have hzB : Subgroup.zpowers b ≤ B := (Subgroup.zpowers_le).2 hbB
    exact mIdx_anti_of_le (centralizerMod_anti_right (a2UH L T H K) hzB)
  have hTCR : a2TC K T ≤ a2R H := c.TC_le_R
  have hBTCR : B ⊔ a2TC K T ≤ a2R H := sup_le hBR hTCR
  have hm2 : 2 ≤ mIdx (B ⊔ a2TC K T) (a2TC K T) := by omega
  have hs := leaf_SLRTC_of h5 h7 h9 h128 h37 h38 h39 G T M L D H K q c
  have hadd := mIdx_add hR2 hBTCR (le_sup_right : a2TC K T ≤ B ⊔ a2TC K T)
  have h0 : mIdx (a2R H) (B ⊔ a2TC K T) = 0 := by omega
  have hrel : (B ⊔ a2TC K T).relIndex (a2R H) = 1 := by
    have := HypF98.relIndex_eq_two_pow_mIdx (Y := B ⊔ a2TC K T) hR2
    rw [h0] at this
    simpa using this
  have hRle : a2R H ≤ B ⊔ a2TC K T := Subgroup.relIndex_eq_one.mp hrel
  have hRe : B ⊔ a2TC K T = a2R H := le_antisymm hBTCR hRle
  have hKC : conjClosure K T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    nf_conjClosure_le_centralizer_Z h36 c.nf.hyp c.nf.inH_H₀ c.nf.K_comp c.nf.nonfaithful
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hRZ : a2R H ≤ Subgroup.normalizer (a2Z T : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    have hxG2 : x ∈ conjClosure K T ⊔ T :=
      c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H hx)
    refine (sup_le hKC hTC) hxG2
  have hNZ : B ⊔ a2TC K T ≤ Subgroup.normalizer (a2Z T : Set G) := hRe ▸ hRZ
  have hcomm : ∀ u ∈ a2UH L T H K, ∀ s ∈ a2TC K T, u * s * u⁻¹ * s⁻¹ ∈ a2Z T := by
    intro u hu s hs'
    have := Subgroup.commutator_mem_commutator hu hs'
    exact e5a (by simpa [commutatorElement_def] using this)
  have hCeq : centralizerMod (a2Z T) (a2UH L T H K) B =
      centralizerMod (a2Z T) (a2UH L T H K) (a2R H) := by
    rw [← hRe]
    exact (centralizerMod_sup_eq hNZ hcomm).symm
  have hks2 := hL.ks2 nfa2_G1 nfa2_G2 nfa2_G3 G T M L D H K q c e5a
  have : a2Off (a2Z T) (a2UH L T H K) B = a2Off (a2Z T) (a2UH L T H K) (a2R H) := by
    unfold a2Off; rw [hCeq]
  rw [hRe] at hle
  have hm : mIdx (a2R H) (a2TC K T) ≤ 2 := hs
  omega

theorem caseA_false (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (hL : A2Leaves) (c : A2Cfg G T M L D H K q)
    (hV : a2V L T ≤ a2TC K T) : False := by
  have hF := c.amalgamHypV h5 h7 h128 h37 h38 h39
  have hV0 := c.V_ne_bot
  have hb2 : 2 ≤ critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) :=
    two_le_critDist_of_le_pCoreOf hF hV0 hV
  have hodd : Odd (critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T)) :=
    leaf_E3 G (a2G0 L K T) (a2G1 L T) (a2G2 K T) T (a2V L T) hF hV0
      (leaf_D1_of_LS1 (leaf_LS1_of h5 h9 hGA h128 h37 h38 h39) h9 G T M L D H K q c)
  have hb3 : 3 ≤ critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hTCH : a2TC K T ≤ a2G1 L T ⊓ a2G2 K T :=
    c.TC_le_R.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans (le_inf c.nf.HLT c.H_le_G2))
  have e1 : E1Concl L K T :=
    ⟨leaf_E1a_of (leaf_LS1_of h5 h9 hGA h128 h37 h38 h39) h9 hGA G T M L D H K q c, le_antisymm (leaf_E1b_of (leaf_LS1_of h5 h9 hGA h128 h37 h38 h39) h5 h7 h9 h128 h37 h38 h39 G T M L D H K q c)
      (le_coreIn (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hTCH)⟩
  have e5a := leaf_E5a_of h36 h5 h9 hGA h128 h37 h38 h39 G T M L D H K q c
  have e5b : E5bConcl L K T H := by
    refine le_antisymm (leaf_E5b_of h36 (leaf_LSCV_of h7 h9 hGA) h37 h38 G T M L D H K q c e5a) fun t ht => ?_
    have htG : t ∈ a2G2 K T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ht
    refine ⟨htG, Subgroup.centralizer_le_normalizer _ (c.G2_le_centralizer_Z h36 htG), fun u hu => ?_⟩
    have h1 : ⁅u, t⁆ ∈ a2Z T := e5a (Subgroup.commutator_mem_commutator hu ht)
    have e : t * u * t⁻¹ * u⁻¹ = ⁅u, t⁆⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (a2Z T).inv_mem h1
  have e5c := hL.e5c nfa2_G1 nfa2_G4 G T M L D H K q c
  have facts : CaseAFacts G T M L D H K q := ⟨c, hV, hF, hV0, hodd, hb3, e1, e5a, e5b, e5c⟩
  have e6i := leaf_E6i h36 G T M L D H K q facts
  have e6ii := hL.e6ii G T M L D H K q facts
  have e7 := hL.e7 G T M L D H K q facts e6i e6ii
  exact e8_false h36 h5 h7 h9 h128 h37 h38 h39 hL c e5a e7

theorem nine_false (h36 : A36ForSQTK) (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hP9K : Leaf_P9K)
    (c : A2Cfg G T M L D H K q)
    (hq : (9 : ℤ) ∣ (q : ℤ) - sgn4 q) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, x, hwK, hw9, hwN, hxY, hxK, hx3, hwx⟩ := leaf_P9a_of_P9K hP9K nfa2_P9L2 G T M L D H K q c hq
  have hwM : w ∈ M := c.normalizer_le_M h5 h7 h9 hwN
  have hKC : conjClosure K T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    nf_conjClosure_le_centralizer_Z h36 c.nf.hyp c.nf.inH_H₀ c.nf.K_comp c.nf.nonfaithful
  have hwZ : w ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    hKC (le_conjClosure K T hwK)
  have hw3 : w ^ 3 ∈ Subgroup.centralizer (a2V L T : Set G) :=
    leaf_P9b_of h36 h5 h128 h37 h38 h39 G T M L D H K q c w hwM hwZ hw9
  have hYH : oTwoUpper H ≤ H := le_sup_left.trans (C1Pack12.oTwoUpper_sup_eq_of_sylow c.sylow_H).le
  have hxH : x ∈ H := hYH hxY
  have hrH : w ^ 3 * x⁻¹ ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hwx
  have hyH : w ^ 3 ∈ H := by
    have e : w ^ 3 = (w ^ 3 * x⁻¹) * x := by group
    rw [e]
    exact H.mul_mem hrH hxH
  have hyQ : w ^ 3 ∈ pCoreOf 2 (L ⊔ T) := leaf_LSCV_of h7 h9 hGA G T M L D H K q c ⟨c.nf.HLT hyH, hw3⟩
  have hyR : w ^ 3 ∈ a2R H := c.Q_le_R hyQ
  have hxR : x ∈ a2R H := by
    have e : x = (w ^ 3 * x⁻¹)⁻¹ * w ^ 3 := by group
    rw [e]
    exact (a2R H).mul_mem ((a2R H).inv_mem hwx) hyR
  have hR2 : IsPGroup 2 (a2R H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) ⟨x, hxR⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  rcases k with _ | k
  · simp at hk
  · have : 2 ∣ 3 := by rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    omega

theorem cfg_false (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hL : A2Leaves) (c : A2Cfg G T M L D H K q) :
    False := by
  by_cases hV : a2V L T ≤ a2TC K T
  · exact caseA_false h36 h5 h7 h9 hGA h128 h37 h38 h39 hL c hV
  · exact caseB_false h9 hGA h37 h38 hL c hV

theorem obl3_3_13D12NF_a2_of_leaves
    (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hL : A2Leaves) : Obl3_3_13D12NF_a2 := by
  intro G _ _ T M L D H K hyp hTL e hc hmod hout hHeq hH hHLT hwr hO hK hKq hYK hTK hKf hin
    ⟨q, hq, h24, _, hmodel⟩
  exact cfg_false h36 h5 h7 h9 hGA h128 h37 h38 h39 hL
    ⟨⟨hyp, hH, hHLT, hwr, hO, hK, hKq, hYK, hTK, hKf, ⟨q, hq, h24, hmodel⟩⟩,
      ⟨hTL, e, hc, hmod, hout, hHeq⟩, hin, hq, h24, hmodel⟩

theorem obl3_3_13D12NF_a2_nine_of_P9K (h36 : A36ForSQTK)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement)
    (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hP9K : Leaf_P9K) :
    Obl3_3_13D12NF_a2_nine := by
  intro G _ _ T M L D H K hyp hTL e hc hmod hout hHeq hH hHLT hwr hO hK hKq hYK hTK hKf hin
    ⟨q, hq, h24, h9q, hmodel⟩
  have cfg : A2Cfg G T M L D H K q :=
    ⟨⟨hyp, hH, hHLT, hwr, hO, hK, hKq, hYK, hTK, hKf, ⟨q, hq, h24, hmodel⟩⟩,
      ⟨hTL, e, hc, hmod, hout, hHeq⟩, hin, hq, h24, hmodel⟩
  exact nine_false h36 h5 h7 h9 hGA h128 h37 h38 h39 hP9K cfg h9q

theorem obl3_3_13D12NF_a2_nine_holds
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Obl3_3_13D12NF_a2_nine :=
  obl3_3_13D12NF_a2_nine_of_P9K h36 h5 h7 h9 hGA h128 h37 h38 h39
    (leaf_P9K_of h5 h7 h9 h128 h37 h38 h39)

end CFSG.Quasithin.H13.NFa2
