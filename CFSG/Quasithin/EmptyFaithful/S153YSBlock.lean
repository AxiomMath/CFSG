module

public import CFSG.Quasithin.EmptyFaithful.S153YSBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.Quasithin.Background.C118NoOuter
public import CFSG.Quasithin.Background.C1PackC126Solv
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C2Eleven

public section

namespace CFSG.Quasithin.YS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_eq_of_normalizes' {S L : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G)) :
    conjClosure L S = L :=
  le_antisymm (conjClosure_le fun _ hg _ hl => (Subgroup.mem_normalizer_iff.mp (hS hg) _).mp hl)
    (le_conjClosure _ _)

namespace S3Hyp

variable {I T T₀ : Subgroup G} (h : S3Hyp I T T₀)
include h

theorem T₀_lt : T₀ < I := by
  refine lt_of_le_of_ne h.sylow.le fun heq => ?_
  have h2 : IsPGroup 2 I := heq ▸ h.sylow.isPGroup
  have hV : pCoreOf 2 I = I :=
    le_antisymm (pCoreOf_le 2 I)
      (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer h2)
  have := h.relV
  rw [hV, ← heq, Subgroup.relIndex_self] at this
  omega

theorem eq_V_or_eq {W : Subgroup G} (hVW : pCoreOf 2 I ≤ W) (hWT : W ≤ T₀) :
    W = pCoreOf 2 I ∨ W = T₀ := by
  by_cases hW : W ≤ pCoreOf 2 I
  · exact Or.inl (le_antisymm hW hVW)
  · right
    obtain ⟨w, hwW, hwV⟩ := Set.not_subset.1 hW
    refine le_antisymm hWT fun x hx => ?_
    rcases mem_or_inv_mul_mem_of_relIndex_two h.relV (h.sylow.le |> fun _ => hWT hwW) hwV hx with hxV | hxV
    · exact hVW hxV
    · have := W.mul_mem hwW (hVW hxV)
      simpa using this


theorem exists_reduction :
    ∃ U L : Subgroup G, U ≤ I ∧ T₀ < U ∧ IsMinimalParabolic T₀ U ∧ CharTwo U ∧ IsChi0Block U L ∧
      IsAltType L 3 ∧ ⁅L, thompsonJ T₀⁆ = L ∧ U = L ⊔ T₀ ∧
      T₀ ≤ Subgroup.normalizer (L : Set G) ∧ pCoreOf 2 U = pCoreOf 2 I ∧
      C5.NoCommonNormal T₀ U T := by
  classical
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := pCoreOf 2 I with hVdef
  have hVI : V ≤ I := pCoreOf_le 2 I
  have hV2 : IsPGroup 2 V := pCoreOf_isPGroup 2 I
  have hVn : I ≤ Subgroup.normalizer (V : Set G) := le_normalizer_pCoreOf 2 I
  have hT₀I : T₀ ≤ I := h.sylow.le
  obtain ⟨U, ⟨hT₀U, hUI⟩, hmin⟩ : ∃ U : Subgroup G, (T₀ < U ∧ U ≤ I) ∧
      ∀ X : Subgroup G, T₀ < X → X ≤ I → ¬ X < U := by
    obtain ⟨U, hU, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup G))
      {U : Subgroup G | T₀ < U ∧ U ≤ I} ⟨I, h.T₀_lt, le_rfl⟩
    exact ⟨U, hU, fun X hX1 hX2 => hmin X ⟨hX1, hX2⟩⟩
  have hT₀max : IsMaxSubgroupIn U T₀ := ⟨hT₀U, fun K hTK hKU => by
    by_contra hne
    exact hmin K hTK (hKU.trans hUI) (lt_of_le_of_ne hKU hne)⟩
  have hmaxOver : maxOver U T₀ = {T₀} := by
    ext N
    constructor
    · rintro ⟨⟨hNU, -⟩, hTN⟩
      by_contra hne
      exact hmin N (lt_of_le_of_ne hTN (fun e => hne (by rw [e]; rfl))) (hNU.le.trans hUI) hNU
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨hT₀max, le_rfl⟩
  have hncard : (maxOver U T₀).ncard = 1 := by rw [hmaxOver]; exact Set.ncard_singleton _
  have hnotN : ¬ U ≤ Subgroup.normalizer (T₀ : Set G) := fun hUN =>
    absurd (fun u hu => h.normalizer_T₀_le ⟨hUI hu, hUN hu⟩ : U ≤ T₀) (not_le_of_gt hT₀U)
  have hUfam : U ∈ uFamHat I T₀ := ⟨⟨hUI, hT₀U, hncard⟩, hnotN⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) theoremC118
  obtain ⟨hC1ne, h1Z, h1char, hC2ne, h2B, h2char, -⟩ := hC.pair T₀ h.sylow.2.1 h.T₀_ne_bot
  have hZle : omegaOneCenterOf T₀ ≤ T₀ := (Subgroup.closure_le _).mpr fun x hx => hx.1.1
  have hC1le : C₁ T₀ ≤ T₀ := h1Z.trans hZle
  have hTN₁ : T ≤ Subgroup.normalizer (C₁ T₀ : Set G) :=
    h.T_le_normalizer.trans (normalizer_le_normalizer_of_characteristic_subgroupOf hC1le h1char)
  have hTN₂ : T ≤ Subgroup.normalizer (C₂ T₀ : Set G) :=
    h.T_le_normalizer.trans ((normalizer_le_normalizer_baum T₀).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char))
  have hM' : (I ⊓ Subgroup.centralizer (C₁ T₀ : Set G)) ⊔ (I ⊓ Subgroup.normalizer (C₂ T₀ : Set G)) ≤ T₀ := by
    refine sup_le ?_ ?_
    · exact (inf_le_inf_left I (Subgroup.centralizer_le_normalizer _)).trans (h.star _ hC1le hC1ne hTN₁)
    · exact h.star _ (h2B.trans (C1GN.baum_le T₀)) hC2ne hTN₂
  have hsolv : perfectCore I ≤ Subgroup.centralizer (VZ T₀ I : Set G) := by
    rw [(isSolvable_iff_perfectCore_eq_bot I).1 h.isSolvable]
    exact bot_le
  obtain ⟨K, hKblk, hK3, hth, hUeq, hKnot⟩ := C1Pack.exists_a3Block_of_not_le hC h.charTwo h.sqtk
    h.sylow hsolv hUfam hM' le_rfl (not_le_of_gt hT₀U)
  have hsylU : IsSylowTwoOf T₀ U := C1GN.isSylowTwoOf_of_le h.sylow hT₀U.le hUI
  have hVU : V ≤ U := h.V_le.trans hT₀U.le
  have hVO : V ≤ pCoreOf 2 U :=
    le_pCoreOf_of_le_normalizer 2 hVU (hUI.trans hVn) hV2
  have hOT : pCoreOf 2 U ≤ T₀ := B6.pCoreOf_two_le_of_isSylowTwoOf hsylU
  have hOV : pCoreOf 2 U = V := by
    rcases h.eq_V_or_eq hVO hOT with e | e
    · exact e
    · exact absurd (e ▸ le_normalizer_pCoreOf 2 U) hnotN
  have hcharU : CharTwo U := by
    intro x hx
    obtain ⟨hxU, hxC⟩ := hx
    rw [hOV] at hxC ⊢
    exact h.charTwo ⟨hUI hxU, hxC⟩
  have hBlk : IsBlock2 U K := hKblk.1
  have hKshort : IsShort2 K := hBlk.1
  have hKU : K ≤ U := hBlk.2.1
  have hKchar : CharTwo K := hKshort.2.1
  obtain ⟨b, hbK, hb3⟩ : ∃ b ∈ K, orderOf b = 3 := by
    have hcard := C2Six.natCard_pCore_quotient_of_isAltType_three hK3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hdvd : 3 ∣ Nat.card ↥K := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hcard]
      exact Dvd.intro _ rfl
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 hdvd
    exact ⟨(b : G), b.2, by rw [Subgroup.orderOf_coe]; exact hb⟩
  have hbO : b ∉ pCoreOf 2 K := by
    intro hb
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨b, hb⟩
    have hk' : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hb3] at h1
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hKV : K ⊓ V ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ (hV2.to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, (hUI.trans hVn) (hKU hx)⟩
  have hJN : thompsonJ T₀ ≤ Subgroup.normalizer (K : Set G) := C56.le_normalizer_of_commutator_eq hth
  obtain ⟨j₀, hj₀J, hj₀V⟩ : ∃ j ∈ thompsonJ T₀, j ∉ V := by
    by_contra hcon
    push Not at hcon
    apply hbO
    have hbcomm : ⁅K, thompsonJ T₀⁆ ≤ K ⊓ V := by
      refine Subgroup.commutator_le.2 fun k hk j hj => ?_
      refine ⟨?_, ?_⟩
      · have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by rw [commutatorElement_def]; group
        rw [e]
        exact K.mul_mem hk ((Subgroup.mem_normalizer_iff.1 (hJN hj) k⁻¹).1 (K.inv_mem hk))
      · have hjV : j ∈ V := hcon j hj
        have hkn : k ∈ Subgroup.normalizer (V : Set G) := (hUI.trans hVn) (hKU hk)
        have h1 : k * j * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hkn j).1 hjV
        rw [commutatorElement_def]
        exact V.mul_mem h1 (V.inv_mem hjV)
    have hbJ : b ∈ ⁅K, thompsonJ T₀⁆ := by rw [hth]; exact hbK
    exact hKV (hbcomm hbJ)
  have hj₀T : j₀ ∈ T₀ := B6.thompsonJ_le T₀ hj₀J
  have hVnK : V ≤ Subgroup.normalizer (K : Set G) := by
    intro v hv
    rw [C2Eleven.mem_normalizer_iff_conjByElt]
    by_contra hne
    have hvU : v ∈ U := hVU hv
    have hB' : IsBlock2 U (conjByElt v K) := IsBlock2.conjByElt_of_mem hBlk hvU
    have hcomm := distinctBlocksCommuteStatement U K (conjByElt v K) hcharU hBlk hB'
      (fun e => hne e.symm)
    have hle : K ≤ Subgroup.centralizer (conjByElt v K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hb' : v * b * v⁻¹ ∈ conjByElt v K := by
      have e : v⁻¹ * (v * b * v⁻¹) * v = b := by group
      rw [mem_conjByElt, e]
      exact hbK
    have hcb : (v * b * v⁻¹) * b = b * (v * b * v⁻¹) :=
      Subgroup.mem_centralizer_iff.1 (hle hbK) _ hb'
    have hcV : v * b * v⁻¹ * b⁻¹ ∈ V := by
      have hbn : b ∈ Subgroup.normalizer (V : Set G) := (hUI.trans hVn) (hKU hbK)
      have h1 : b * v⁻¹ * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hbn v⁻¹).1 (V.inv_mem hv)
      have e : v * b * v⁻¹ * b⁻¹ = v * (b * v⁻¹ * b⁻¹) := by group
      rw [e]
      exact V.mul_mem hv h1
    have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
    have hc3 : (v * b * v⁻¹ * b⁻¹) ^ 3 = 1 := by
      have hcomm' : Commute (v * b * v⁻¹) b⁻¹ := (show Commute (v * b * v⁻¹) b from hcb).inv_right
      rw [hcomm'.mul_pow 3, inv_pow, hb3']
      rw [conj_pow, hb3']
      simp
    obtain ⟨k, hk⟩ := hV2 ⟨_, hcV⟩
    have hk' : (v * b * v⁻¹ * b⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf (v * b * v⁻¹ * b⁻¹) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hc3
      have h2 := orderOf_dvd_of_pow_eq_one hk'
      have h3 := Nat.dvd_gcd h1 h2
      rw [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at h3
      exact Nat.dvd_one.1 h3
    have hc1 : v * b * v⁻¹ * b⁻¹ = 1 := orderOf_eq_one_iff.1 hord
    have hbeq : v * b * v⁻¹ = b := by
      have : v * b * v⁻¹ = (v * b * v⁻¹ * b⁻¹) * b := by group
      rw [this, hc1, one_mul]
    have hbK' : b ∈ conjByElt v K := by rw [← hbeq]; exact hb'
    apply hbO
    refine hKchar ⟨hbK, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro x hx
    have hxK : x ∈ K := pCoreOf_le 2 K hx
    exact (Subgroup.mem_centralizer_iff.1 (hle hxK) b hbK').symm
  have hT₀N : T₀ ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    rcases mem_or_inv_mul_mem_of_relIndex_two h.relV hj₀T hj₀V ht with htV | htV
    · exact hVnK htV
    · have e : t = j₀ * (j₀⁻¹ * t) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hJN hj₀J) (hVnK htV)
  have hUeq' : U = K ⊔ T₀ := by
    rw [hUeq, sup_comm]
    congr 1
    exact conjClosure_eq_of_normalizes' hT₀N
  refine ⟨U, K, hUI, hT₀U, ⟨hsylU, hnotN, T₀, le_rfl, hT₀U, fun X hTX hXU => ?_⟩, hcharU, hKblk, hK3, hth,
    hUeq', hT₀N, hOV, ?_⟩
  · by_contra hXT
    exact hmin X (lt_of_le_of_ne hTX fun e => hXT (e ▸ le_rfl)) (hXU.le.trans hUI) hXU
  · intro X hXT hX1 hUX hTX
    have := h.star X hXT hX1 hTX
    exact absurd (fun u hu => this ⟨hUI hu, hUX hu⟩ : U ≤ T₀) (not_le_of_gt hT₀U)

end S3Hyp

end CFSG.Quasithin.YS
