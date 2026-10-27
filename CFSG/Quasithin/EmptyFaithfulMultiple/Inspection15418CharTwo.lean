module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Background.A4Local
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace Insp15418

variable {Γ : Type*} [Group Γ]

theorem odd_card_iSup {s : ℕ} {D : Fin s → Subgroup Γ}
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, a * b = b * a)
    (hodd : ∀ i, Odd (Nat.card ↥(D i))) [∀ i, Finite ↥(D i)] :
    Odd (Nat.card ↥(⨆ i, D i)) := by
  classical
  have hc : Pairwise fun i j : Fin s => ∀ x y : Γ, x ∈ D i → y ∈ D j → Commute x y :=
    fun i j hij x y hx hy => hcomm i j hij x hx y hy
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hc)]
  have hdvd : Nat.card ↥(Subgroup.noncommPiCoprod hc).range ∣ Nat.card (∀ i, ↥(D i)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.noncommPiCoprod hc).ker,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    exact dvd_mul_right _ _
  refine Odd.of_dvd_nat ?_ hdvd
  rw [Nat.card_pi]
  exact Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i _ => hodd i

theorem commutator_mem_of_relIndex_eq_two {H K : Subgroup Γ} (h : H.relIndex K = 2) {a b : Γ}
    (ha : a ∈ K) (hb : b ∈ K) : a * b * a⁻¹ * b⁻¹ ∈ H := by
  have h2 : (H.subgroupOf K).index = 2 := h
  have key : (⟨a, ha⟩ : ↥K) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥K)⁻¹ * (⟨b, hb⟩ : ↥K)⁻¹ ∈
      H.subgroupOf K := by
    rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
      Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    tauto
  simpa [Subgroup.mem_subgroupOf] using key

end Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}

section Basic

variable (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem le_omegaOneCenter : Z ≤ quasithinOmegaOneCenter S := by
  intro z hz
  apply Subgroup.subset_closure
  refine ⟨⟨d.le hz, Subgroup.mem_centralizer_iff.mpr ?_⟩, d.sq_eq_one z hz⟩
  intro s hs
  have hs' : s ∈ I ⊓ Subgroup.centralizer (Z : Set G) := d.centralizer_eq ▸ hs
  exact (Subgroup.mem_centralizer_iff.mp hs'.2 z hz).symm

theorem inf_centralizer_omegaOneCenter_le :
    I ⊓ Subgroup.centralizer (quasithinOmegaOneCenter S : Set G) ≤ S :=
  (inf_le_inf_left _ (Subgroup.centralizer_le d.le_omegaOneCenter)).trans d.centralizer_eq.le

theorem exists_orderOf_eq_three : ∃ x ∈ oTwoUpper G₁, orderOf x = 3 := by
  obtain ⟨x, hx, h3⟩ := F6.exists_orderOf_eq_three_left d.triple.subgroupOf
  refine ⟨(x : G), mem_oTwoUpper_of_odd hx ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, h3]
    decide
  · rw [Subgroup.orderOf_coe, h3]

theorem not_isPGroup_oTwoUpper {P : Subgroup G} (hP : IsPGroup 2 P) : ¬ oTwoUpper G₁ ≤ P := by
  intro hle
  obtain ⟨x, hx, h3⟩ := d.exists_orderOf_eq_three
  obtain ⟨k, hk⟩ := hP ⟨x, hle hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [h3] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  omega

theorem S_sup_oTwoUpper_left : S ⊔ oTwoUpper G₁ = G₁ := by
  have h := F6.inf_sup_twoResidual_left d.triple.subgroupOf
  rw [d.inf_subgroupOf, F6.twoResidual_eq_oTwoUpper] at h
  have h2 := congrArg (Subgroup.map I.subtype) h
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le d.S_le, ← oTwoUpper_map,
    Subgroup.map_subgroupOf_eq_of_le d.G₁_le] at h2

theorem S_sup_oTwoUpper_right : S ⊔ oTwoUpper G₂ = G₂ := by
  have h := F6.inf_sup_twoResidual_right d.triple.subgroupOf
  rw [d.inf_subgroupOf, F6.twoResidual_eq_oTwoUpper] at h
  have h2 := congrArg (Subgroup.map I.subtype) h
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le d.S_le, ← oTwoUpper_map,
    Subgroup.map_subgroupOf_eq_of_le d.G₂_le] at h2

theorem commutator_le_pCoreOf_left : ⁅S, S⁆ ≤ pCoreOf 2 G₁ := by
  have h := F6.relIndex_pCoreOf_left d.triple.subgroupOf
  rw [d.inf_subgroupOf] at h
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab := Insp15418.commutator_mem_of_relIndex_eq_two h
    (show (⟨a, d.S_le ha⟩ : ↥I) ∈ S.subgroupOf I from ha)
    (show (⟨b, d.S_le hb⟩ : ↥I) ∈ S.subgroupOf I from hb)
  rw [← F6.map_pCoreOf_subgroupOf d.G₁_le]
  exact ⟨_, hab, by simp [commutatorElement_def]⟩

theorem commutator_le_pCoreOf_right : ⁅S, S⁆ ≤ pCoreOf 2 G₂ := by
  have h := F6.relIndex_pCoreOf_right d.triple.subgroupOf
  rw [d.inf_subgroupOf] at h
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab := Insp15418.commutator_mem_of_relIndex_eq_two h
    (show (⟨a, d.S_le ha⟩ : ↥I) ∈ S.subgroupOf I from ha)
    (show (⟨b, d.S_le hb⟩ : ↥I) ∈ S.subgroupOf I from hb)
  rw [← F6.map_pCoreOf_subgroupOf d.G₂_le]
  exact ⟨_, hab, by simp [commutatorElement_def]⟩

end Basic

section CharTwo

variable (d : InspectionData15418 I G₁ G₂ S T Z) (hc : CharTwo I)
include d hc

theorem isElemAbelian_V : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter S) I) :=
  (conjClosure_isTwoReducedIn_of_charTwo d.isSylowTwoOf hc le_rfl).2.1

theorem inf_centralizer_V :
    I ⊓ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter S) I : Set G) =
      pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := (conjClosure_isTwoReducedIn_of_charTwo d.isSylowTwoOf hc le_rfl).2.2
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
    (pCoreOf_le_centralizer_of_isTwoReducedIn hred))
  have hCT : I ⊓ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter S) I : Set G) ≤ S :=
    (inf_le_inf_left _ (Subgroup.centralizer_le (le_conjClosure _ _))).trans
      d.inf_centralizer_omegaOneCenter_le
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (d.isPGroup_S.to_le hCT)
  exact B2F.le_normalizer_inf Subgroup.le_normalizer
    ((le_normalizer_conjClosure _ _).trans (B2F.normalizer_le_normalizer_centralizer _))

theorem not_thompsonJ_le :
    ¬ thompsonJ I ≤
      Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter S) I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJ
  have hJS : thompsonJ S ≤ pCoreOf 2 I := by
    rw [← d.inf_centralizer_V hc]
    exact le_inf ((thompsonJ_le_self S).trans d.S_le)
      ((thompsonJ_le_thompsonJ_of_isSylowTwoOf d.isSylowTwoOf).trans hJ)
  have hL : oTwoUpper G₁ ≤ pCoreOf 2 I := by
    rw [← d.thompson₁]
    exact (Subgroup.commutator_mono ((oTwoUpper_le G₁).trans d.G₁_le) hJS).trans
      (L15421.commutator_le_right_of_le_normalizer
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  exact d.not_isPGroup_oTwoUpper (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I) hL

theorem commutator_le_of_noComponent
    (hnc : ∀ K : Subgroup ↥(autI (d.isElemAbelian_V hc) I), ¬ CFSG.IsComponent K) :
    ⁅S, S⁆ ≤ pCoreOf 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := conjClosure (quasithinOmegaOneCenter S) I with hVdef
  have hV : IsElemAbelian 2 V := d.isElemAbelian_V hc
  have hIN : I ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo d.isSylowTwoOf hc le_rfl
  obtain ⟨hFF, -, hJeq, hJle⟩ := B2_7_of_not_le hV hred.1 hIN (d.not_thompsonJ_le hc)
  have hJ : autI hV (thompsonJ I) ≤ ffJ (autI hV I) := hJeq ▸ hJle
  have hO : CFSG.Open.pCore 2 ↥(autI hV I) = ⊥ := pCore_autOn_eq_bot hred
  obtain ⟨n, H, hcomm, hDH, -, hsq, hJH⟩ :=
    L15421.ffJ_eq_iSup_of_noComponent inputB19_holds (fun v => IntMod.sq_eq_one v) hO hFF hnc
  have hJS : thompsonJ S ≤ thompsonJ I := thompsonJ_le_thompsonJ_of_isSylowTwoOf d.isSylowTwoOf
  set D := ⨆ i, oddCoreOfSub (H i) with hDdef
  have hDL : ∀ L : Subgroup G, L ≤ I → L = oTwoUpper L → ⁅L, thompsonJ S⁆ = L →
      autI hV L ≤ D := by
    intro L hLI hL hLJ
    refine L15421.autI_le_of_odd hV hL (hLI.trans hIN) fun x hx ho => ?_
    refine L15421.mem_iSup_of_odd hcomm hDH hsq ?_ ?_
    · rw [← hJH]
      exact L15421.autI_le_ffJ_of hV hIN hJ hLI hJS hLJ (convI_mem_autI hV hx _)
    · refine Odd.of_dvd_nat ho ?_
      have h := orderOf_map_dvd (convI hV) ⟨x, hIN (hLI hx)⟩
      rwa [Subgroup.orderOf_mk] at h
  have hDodd : Odd (Nat.card ↥D) := by
    refine Insp15418.odd_card_iSup
      (fun i j hij a ha b hb => hcomm i j hij a (hDH i ha) b (hDH j hb)) fun i => ?_
    rw [oddCoreOfSub, Subgroup.card_map_of_injective (H i).subtype_injective]
    exact EscapingLocal.odd_card_oddCore _
  have hD2 : ∀ y ∈ D, ∀ k : ℕ, y ^ 2 ^ k = 1 → y = 1 := by
    intro y hy k hk
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf y ∣ Nat.card ↥D := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥D) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hDodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hkey : ∀ {Gi : Subgroup G}, Gi ≤ I → S ≤ Gi →
      ⁅oTwoUpper Gi, thompsonJ S⁆ = oTwoUpper Gi → ⁅S, S⁆ ≤ pCoreOf 2 Gi →
      ∀ l ∈ oTwoUpper Gi, ∀ c ∈ ⁅S, S⁆, l * c * l⁻¹ * c⁻¹ ∈ pCoreOf 2 I := by
    intro Gi hGiI hSGi hJ' hSQ l hl c hc'
    have hcGi : c ∈ Gi := hSGi (Subgroup.commutator_le_self S hc')
    have hLI : oTwoUpper Gi ≤ I := (oTwoUpper_le Gi).trans hGiI
    have hm : l * c * l⁻¹ * c⁻¹ ∈ oTwoUpper Gi := by
      have h1 := conj_mem_oTwoUpper (Subgroup.le_normalizer hcGi) ((oTwoUpper Gi).inv_mem hl)
      have e : l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) := by group
      rw [e]
      exact (oTwoUpper Gi).mul_mem hl h1
    have hq : l * c * l⁻¹ * c⁻¹ ∈ pCoreOf 2 Gi := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gi (oTwoUpper_le Gi hl)) c).mp (hSQ hc')
      exact (pCoreOf 2 Gi).mul_mem h1 ((pCoreOf 2 Gi).inv_mem (hSQ hc'))
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Gi ⟨_, hq⟩
    have hk' : (l * c * l⁻¹ * c⁻¹) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have himg := hDL (oTwoUpper Gi) hLI (A4.oTwoUpper_oTwoUpper Gi).symm hJ'
      (convI_mem_autI hV hm (hIN (hLI hm)))
    have h1 := hD2 _ himg k (by
      rw [← map_pow]
      have e : (⟨l * c * l⁻¹ * c⁻¹, hIN (hLI hm)⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k =
          1 := Subtype.ext hk'
      rw [e, map_one])
    rw [← d.inf_centralizer_V hc]
    exact ⟨hLI hm, (convI_eq_one_iff hV _).mp h1⟩
  set W := ⁅S, S⁆ ⊔ pCoreOf 2 I with hWdef
  have hSS : ⁅S, S⁆ ≤ S := Subgroup.commutator_le_self S
  have hWI : W ≤ I := sup_le (hSS.trans d.S_le) (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  have hW2 : IsPGroup 2 ↥W :=
    d.isPGroup_S.to_le (sup_le hSS (pCoreOf_le_of_isSylowTwoOf d.isSylowTwoOf))
  have hON : I ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    F6.mem_normalizer_sup (Subgroup.normalizer_commutator_ge_left S S hs) (hON (d.S_le hs))
  have hLW : ∀ {Gi : Subgroup G}, Gi ≤ I → S ≤ Gi →
      ⁅oTwoUpper Gi, thompsonJ S⁆ = oTwoUpper Gi → ⁅S, S⁆ ≤ pCoreOf 2 Gi →
      oTwoUpper Gi ≤ Subgroup.normalizer (W : Set G) := by
    intro Gi hGiI hSGi hJ' hSQ l hl
    have hlI : l ∈ I := hGiI (oTwoUpper_le Gi hl)
    refine L15421.mem_normalizer_of_conj_mem fun x hx => ?_
    have hx' : x ∈ ((⁅S, S⁆ ⊔ pCoreOf 2 I : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hSS.trans d.S_le).trans hON)] at hx'
    obtain ⟨c, hc', q, hq, rfl⟩ := Set.mem_mul.mp hx'
    have e : l * (c * q) * l⁻¹ = (l * c * l⁻¹ * c⁻¹) * c * (l * q * l⁻¹) := by group
    rw [e]
    refine W.mul_mem (W.mul_mem ?_ (le_sup_left (a := ⁅S, S⁆) hc')) ?_
    · exact le_sup_right (b := pCoreOf 2 I) (hkey hGiI hSGi hJ' hSQ l hl c hc')
    · exact le_sup_right (b := pCoreOf 2 I) ((Subgroup.mem_normalizer_iff.mp (hON hlI) q).mp hq)
  have hIW : I ≤ Subgroup.normalizer (W : Set G) := by
    rw [← d.triple.1]
    refine sup_le ?_ ?_
    · rw [← d.S_sup_oTwoUpper_left]
      exact sup_le hSW (hLW d.G₁_le d.S_le_G₁ d.thompson₁ d.commutator_le_pCoreOf_left)
    · rw [← d.S_sup_oTwoUpper_right]
      exact sup_le hSW (hLW d.G₂_le d.S_le_G₂ d.thompson₂ d.commutator_le_pCoreOf_right)
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWI hIW hW2)

theorem commutator_le_of_charTwo (hCC : ComponentComparison15421) : ⁅S, S⁆ ≤ pCoreOf 2 I := by
  by_cases hK : ∃ K : Subgroup ↥(autI (d.isElemAbelian_V hc) I), CFSG.IsComponent K
  · exfalso
    have hred := (conjClosure_isTwoReducedIn_of_charTwo d.isSylowTwoOf hc le_rfl).2.2
    have hFF := (B2_7_of_not_le (d.isElemAbelian_V hc) hred.1 (le_normalizer_conjClosure _ _)
      (d.not_thompsonJ_le hc)).1
    exact hCC G I G₁ G₂ S d.sqtk d.triple d.inf_eq d.isGoldschmidtAmalgam.2 hc
      (d.isElemAbelian_V hc) (d.inf_centralizer_V hc) hFF hK
      (d.isPGroup_S.to_le d.inf_centralizer_omegaOneCenter_le)
  · push Not at hK
    exact d.commutator_le_of_noComponent hc hK

end CharTwo

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple
