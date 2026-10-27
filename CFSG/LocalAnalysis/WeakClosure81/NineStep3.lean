module

public import CFSG.LocalAnalysis.WeakClosure81.NineLemmaD
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}

theorem isE_self {i : ℕ} {S A H K : Subgroup G} (h : E1.IsE i K S A H) :
    E1.IsE i H (S ⊓ H) A H := by
  obtain ⟨-, -, hSyl, hrest⟩ := h
  refine ⟨le_refl H, ?_, ?_, ?_⟩
  · rw [inf_assoc, inf_idem]
    exact E1.tauOf_le H (S ⊓ H) A
  · rwa [inf_assoc, inf_idem]
  · rwa [inf_assoc, inf_idem]

theorem not_le_pCoreOf_of_eOne {H A : Subgroup G} (h : E1.EOne ↥H (A.subgroupOf H)) :
    ¬ A ≤ pCoreOf 2 H := by
  intro hA
  obtain ⟨p, -, -, -, -, -, hcard⟩ := h
  have hsub : A.subgroupOf H ≤ CFSG.pCore 2 ↥H := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 H]
    exact Subgroup.subgroupOf_mono H hA
  have hker : A.subgroupOf H ≤ (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hsub
  have hbot : E1.barO2 ↥H (A.subgroupOf H) = ⊥ := by
    rw [E1.barO2]
    exact (Subgroup.map_eq_bot_iff (H := A.subgroupOf H)).mpr hker
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (by norm_num)

theorem le_of_isE_of_isElemAbelian {i : ℕ} {S A H K : Subgroup G} (hS : IsSylowIn 2 S K)
    (hAS : A ≤ S) (hA : IsElemAbelian 2 A) (h : E1.IsE i K S A H) : A ≤ H :=
  (E3.card_le_of_isE hS hAS hA h).1

theorem exists_isE_not_le_frattiniR (h : TwoPTwoIrred K S X p) {A : Subgroup G} (hAS : A ≤ S)
    (hAab : IsElemAbelian 2 A) (hAR : ¬ A ≤ pCoreOf 2 K) :
    ∃ H : Subgroup G, E1.IsE 1 K S A H ∧ E1.EOne ↥H (A.subgroupOf H) ∧
      ¬ twoResidual H ≤ nineFrattiniR K X := by
  have hSK : S ≤ K := h.sylowTwo.le
  have hXK : X ≤ K := h.sylowP.le
  have hΦXK : nineFrattini X ≤ K := (TwoPTwoIrred.nineFrattini_le X).trans hXK
  have hΦR_le_K : nineFrattiniR K X ≤ K :=
    sup_le hΦXK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  let Q := ↥K
  let π : Q →* Q ⧸ CFSG.pCore 2 Q := QuotientGroup.mk' (CFSG.pCore 2 Q)
  let Sq : Subgroup Q := S.subgroupOf K
  let Aq : Subgroup Q := A.subgroupOf K
  let Xq : Subgroup Q := X.subgroupOf K
  let Φb : Subgroup (Q ⧸ CFSG.pCore 2 Q) := ((nineFrattini X).subgroupOf K).map π
  let Xb : Subgroup (Q ⧸ CFSG.pCore 2 Q) := Xq.map π
  let Tb : Subgroup (Q ⧸ CFSG.pCore 2 Q) := Sq.map π
  let Ab : Subgroup (Q ⧸ CFSG.pCore 2 Q) := Aq.map π
  have hSylQ : IsSylowIn 2 Sq ⊤ := by
    have h1 := (E1.isSylowIn_subgroupOf_iff (P := S) (K := K) (H := K) h.sylowTwo.le
      le_rfl).mpr h.sylowTwo
    simpa [Sq] using h1
  have hAqSq : Aq ≤ Sq := Subgroup.subgroupOf_mono K hAS
  have hAqab : IsElemAbelian 2 Aq := CFSG.Open.IsElemAbelian.subgroupOf hAab K
  have hXqP : IsPGroup p Xq := h.sylowP.isPGroup.comap_subtype
  have hsup_eq : (CFSG.pCore 2 Q ⊔ Xq) =
      (pCoreOf 2 K ⊔ X).subgroupOf K := by
    rw [Subgroup.subgroupOf_sup (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hXK,
      CFSG.openPCoreOf_subgroupOf]
  have hN : (CFSG.pCore 2 Q ⊔ Xq).Normal :=
    hsup_eq.symm ▸ h.toTwoPTwo.normal_pCoreOf_sup
  have hXqMap : (CFSG.pCore 2 Q ⊔ Xq).map π = Xb := by
    rw [Subgroup.map_sup]
    have hbot : (CFSG.pCore 2 Q).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hbot, bot_sup_eq]
  have hXbNorm : Xb.Normal := by
    rw [← hXqMap]
    exact hN.map π (QuotientGroup.mk'_surjective (CFSG.pCore 2 Q))
  have hXbP : IsPGroup p Xb := hXqP.map π
  have hAbTb : Ab ≤ Tb := Subgroup.map_mono hAqSq
  have hAbab : IsElemAbelian 2 Ab := E1.isElemAbelian_map' π hAqab
  have hTbSyl : IsSylowIn 2 Tb ⊤ :=
    E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective (CFSG.pCore 2 Q)) hSylQ
  have hΦR : nineFrattiniR K X =
      ((nineFrattini X).subgroupOf K ⊔ CFSG.pCore 2 Q).map K.subtype := by
    rw [nineFrattiniR, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hΦXK]
    rfl
  have hpre : ∀ q : Q, π q ∈ Φb → (q : G) ∈ nineFrattiniR K X := by
    intro q hq
    have hq' : q ∈ (((nineFrattini X).subgroupOf K).map π).comap π := hq
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hq'
    rw [hΦR]
    exact Subgroup.mem_map_of_mem K.subtype hq'
  have hnot : ¬ ⁅Xb, Ab⁆ ≤ Φb := by
    intro hle
    apply hAR
    intro a ha
    have haK : a ∈ K := hSK (hAS ha)
    have ha2 : a ^ 2 ^ 1 = 1 := by
      rw [pow_one]
      exact hAab.2 a ha
    refine h.toTwoPTwo.mem_pCoreOf_of_commutator_mem_frattiniR haK ha2 ?_
    intro x hx
    have hxK : x ∈ K := hXK hx
    let qa : Q := ⟨a, haK⟩
    let qx : Q := ⟨x, hxK⟩
    have hqxXq : qx ∈ Xq := Subgroup.mem_subgroupOf.mpr hx
    have hqaAq : qa ∈ Aq := Subgroup.mem_subgroupOf.mpr ha
    have hqxXb : π qx ∈ Xb := Subgroup.mem_map_of_mem π hqxXq
    have hqaAb : π qa ∈ Ab := Subgroup.mem_map_of_mem π hqaAq
    have hmem : ⁅π qa, π qx⁆ ∈ ⁅Xb, Ab⁆ := by
      have h1 : ⁅π qx, π qa⁆ ∈ ⁅Xb, Ab⁆ :=
        Subgroup.commutator_mem_commutator hqxXb hqaAb
      have hinv : ⁅π qa, π qx⁆ = (⁅π qx, π qa⁆)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hinv]
      exact Subgroup.inv_mem _ h1
    have hΦ : π ⁅qa, qx⁆ ∈ Φb := by
      rw [map_commutatorElement]
      exact hle hmem
    have hR : ((⁅qa, qx⁆ : Q) : G) ∈ nineFrattiniR K X := hpre ⁅qa, qx⁆ hΦ
    have hR' : K.subtype ⁅qa, qx⁆ ∈ nineFrattiniR K X := hR
    rw [map_commutatorElement] at hR'
    simpa [qa, qx] using hR'
  haveI : Xb.Normal := hXbNorm
  have hcomm_le : ⁅Xb, Ab⁆ ≤ ⨆ I ∈ {I : Subgroup (Q ⧸ CFSG.pCore 2 Q) |
      E1.IsE 1 ⊤ Tb Ab I ∧ E1.EOne ↥I (Ab.subgroupOf I) ∧
        Nat.card (E1.barO2 ↥I (Ab.subgroupOf I)) ≤ 2 ^ 1}, twoResidual I :=
    E1.comm_le_iSup_twoResidual (T := Tb) (A := Ab) (X := Xb) h.prime h.odd hTbSyl hAbTb hAbab
      hXbP
  have hex : ∃ I : Subgroup (Q ⧸ CFSG.pCore 2 Q), E1.IsE 1 ⊤ Tb Ab I ∧
      E1.EOne ↥I (Ab.subgroupOf I) ∧
      Nat.card (E1.barO2 ↥I (Ab.subgroupOf I)) ≤ 2 ^ 1 ∧ ¬ twoResidual I ≤ Φb := by
    by_contra hcon
    push Not at hcon
    apply hnot
    refine hcomm_le.trans ?_
    refine iSup₂_le fun I hI => ?_
    exact hcon I hI.1 hI.2.1 hI.2.2
  obtain ⟨I, hI, hIEOne, hIcard, hInot⟩ := hex
  obtain ⟨J, hJ, hJres⟩ :=
    E1.ten_seven_eOne (T := Sq) (A := Aq) (Y := CFSG.pCore 2 Q) hSylQ hAqSq hAqab hI
      ⟨hIEOne, hIcard⟩
  have hHK' : J.map K.subtype ≤ K := Subgroup.map_subtype_le J
  have hHIsE : E1.IsE 1 K S A (J.map K.subtype) := by
    have h1 := (E1.isE_map_subtype K).mpr hJ
    rwa [Subgroup.map_subgroupOf_eq_of_le hSK,
      Subgroup.map_subgroupOf_eq_of_le (hAS.trans hSK)] at h1
  haveI : Group.IsSolvable ↥K := h.toTwoPTwo.isSolvable
  haveI : Group.IsSolvable ↥(J.map K.subtype) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHK')
  have hEOneH := E1.isE_eOne_of_isSolvable hHIsE
    (inferInstance : Group.IsSolvable ↥(J.map K.subtype))
  have hResH : twoResidual (J.map K.subtype) = (twoResidual J).map K.subtype :=
    (E1.map_twoResidual K.subtype J).symm
  have hnotH : ¬ twoResidual (J.map K.subtype) ≤ nineFrattiniR K X := by
    intro hle
    apply hInot
    rw [hJres]
    have hJle : twoResidual J ≤ (nineFrattiniR K X).subgroupOf K := by
      rw [← Subgroup.map_le_map_iff_of_injective (f := K.subtype) K.subtype_injective]
      rw [Subgroup.map_subgroupOf_eq_of_le hΦR_le_K, ← hResH]
      exact hle
    have hΦRmap : ((nineFrattiniR K X).subgroupOf K).map π = Φb := by
      rw [nineFrattiniR, Subgroup.subgroupOf_sup hΦXK (CFSG.LieType.BorelTits.pCoreOf_le 2 K),
        Subgroup.map_sup, CFSG.openPCoreOf_subgroupOf]
      have hbot : (CFSG.pCore 2 Q).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [hbot, sup_bot_eq]
    exact (Subgroup.map_mono hJle).trans (le_of_eq hΦRmap)
  exact ⟨J.map K.subtype, hHIsE, hEOneH.1, hnotH⟩

theorem sup_twoResidual_eq_of_not_le_frattiniR (h : TwoPTwoIrred K S X p) {H : Subgroup G}
    (hHK : H ≤ K) (hH : ¬ twoResidual H ≤ nineFrattiniR K X) : S ⊔ twoResidual H = K := by
  have hSK : S ≤ K := h.sylowTwo.le
  have hXK : X ≤ K := h.sylowP.le
  have hΦX : nineFrattini X ≤ X := TwoPTwoIrred.nineFrattini_le X
  have hΦXK : nineFrattini X ≤ K := hΦX.trans hXK
  set K₀ : Subgroup G := S ⊔ twoResidual H with hK0
  set Y₀ : Subgroup G := X ⊓ K₀ with hY0
  have hK0_le_K : K₀ ≤ K := sup_le hSK (twoResidual_le H |>.trans hHK)
  have hS_le_K0 : S ≤ K₀ := le_sup_left
  have hRes_le_K0 : twoResidual H ≤ K₀ := le_sup_right
  have hK0_mul : (K₀ : Set G) = (S : Set G) * (Y₀ : Set G) := by
    apply Set.Subset.antisymm
    · intro k hk
      have hkK : k ∈ K := hK0_le_K hk
      have hkSX : k ∈ (S : Set G) * (X : Set G) := by
        change k ∈ (K : Set G) at hkK
        rwa [TwoPTwo.mul_eq h.toTwoPTwo] at hkK
      rw [Set.mem_mul] at hkSX ⊢
      obtain ⟨s, hs, x, hx, rfl⟩ := hkSX
      refine ⟨s, hs, x, ⟨hx, ?_⟩, rfl⟩
      have hmem : s⁻¹ * (s * x) ∈ K₀ := K₀.mul_mem (K₀.inv_mem (hS_le_K0 hs)) hk
      simpa using hmem
    · rintro _ ⟨s, hs, y, hy, rfl⟩
      exact K₀.mul_mem (hS_le_K0 hs) hy.2
  have hnormY : ∀ s ∈ S ⊓ Subgroup.normalizer (X : Set G),
      ∀ y ∈ Y₀ ⊔ nineFrattini X, s * y * s⁻¹ ∈ Y₀ ⊔ nineFrattini X := by
    intro s hs y hy
    have hsS : s ∈ S := hs.1
    have hsX : s ∈ Subgroup.normalizer (X : Set G) := hs.2
    have hsK0 : s ∈ K₀ := hS_le_K0 hsS
    have hsK0n : s ∈ Subgroup.normalizer (K₀ : Set G) := Subgroup.le_normalizer hsK0
    have hY0norm : s ∈ Subgroup.normalizer (Y₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hzX, hzK0⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsX z).mp hzX,
          (Subgroup.mem_normalizer_iff.mp hsK0n z).mp hzK0⟩
      · rintro ⟨hzX, hzK0⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hsX z).mpr hzX,
          (Subgroup.mem_normalizer_iff.mp hsK0n z).mpr hzK0⟩
    have hΦnorm : s ∈ Subgroup.normalizer (nineFrattini X : Set G) :=
      TwoPTwoIrred.normalizer_le_normalizer_nineFrattini X hsX
    exact RonanD33.conj_mem_sup
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hY0norm a).mp ha)
      (fun a ha => (Subgroup.mem_normalizer_iff.mp hΦnorm a).mp ha) hy
  have hcases := h.irred.2 (Y₀ ⊔ nineFrattini X) le_sup_right (sup_le inf_le_left hΦX) hnormY
  have hXK0 : X ≤ K₀ := by
    rcases hcases with hY | hY
    ·
      exfalso
      apply hH
      have hY_le_Φ : Y₀ ≤ nineFrattini X := hY ▸ le_sup_left
      intro o ho
      have hoK0 : o ∈ K₀ := hRes_le_K0 ho
      have ho_mul : o ∈ (S : Set G) * (Y₀ : Set G) := by
        rw [← hK0_mul]
        exact hoK0
      rw [Set.mem_mul] at ho_mul
      obtain ⟨s, hsS, y, hyY0, hsy⟩ := ho_mul
      have hyΦ : y ∈ nineFrattini X := hY_le_Φ hyY0
      have hyX : y ∈ X := hΦX hyΦ
      have hresK : o ∈ twoResidual K := E1.twoResidual_mono hHK ho
      have htwoK : twoResidual K ≤ pCoreOf 2 K ⊔ X := by
        rw [← TwoPTwo.twoResidual_sup_pCoreOf h.toTwoPTwo]
        exact le_sup_left
      have ho_sup : o ∈ pCoreOf 2 K ⊔ X := htwoK hresK
      have hy_sup : y ∈ pCoreOf 2 K ⊔ X := Subgroup.mem_sup_right hyX
      have hs_sup : s ∈ pCoreOf 2 K ⊔ X := by
        have hs_eq : s = o * y⁻¹ := by rw [← hsy]; group
        rw [hs_eq]
        exact (pCoreOf 2 K ⊔ X).mul_mem ho_sup ((pCoreOf 2 K ⊔ X).inv_mem hy_sup)
      obtain ⟨n, hn⟩ := h.sylowTwo.isPGroup.exists_orderOf_eq_pow ⟨s, hsS⟩
      have hord : orderOf s = 2 ^ n := by rw [← Subgroup.orderOf_mk s hsS, hn]
      have hs2 : s ^ 2 ^ n = 1 := by rw [← hord, pow_orderOf_eq_one]
      have hsR : s ∈ pCoreOf 2 K := TwoPTwo.mem_pCoreOf_of_mem_sup h.toTwoPTwo hs_sup hs2
      rw [nineFrattiniR, sup_comm]
      rw [← hsy]
      exact (pCoreOf 2 K ⊔ nineFrattini X).mul_mem (Subgroup.mem_sup_left hsR)
        (Subgroup.mem_sup_right hyΦ)
    ·
      have hYX : Y₀ = X := TwoPTwoIrred.eq_of_sup_nineFrattini_eq inf_le_left hY
      rw [← hYX]
      exact inf_le_right
  have hK_le_K0 : K ≤ K₀ := by
    intro k hk
    have hkSX : k ∈ (S : Set G) * (X : Set G) := by
      change k ∈ (K : Set G) at hk
      rwa [TwoPTwo.mul_eq h.toTwoPTwo] at hk
    rw [Set.mem_mul] at hkSX
    obtain ⟨s, hs, x, hx, rfl⟩ := hkSX
    exact K₀.mul_mem (hS_le_K0 hs) (hXK0 hx)
  exact le_antisymm hK0_le_K hK_le_K0

theorem cClos_le_cClos_inf_of_isE (hV : IsElemAbelian 2 V) (hm : 2 < rk ↥V) {A H : Subgroup G}
    (hSK : S ≤ K) (hA : IsGConj V A) (hAS : A ≤ S) (hH : E1.IsE 1 K S A H) :
    E3.cClos V 1 S ≤ E3.cClos V 1 (S ⊓ H) := by
  obtain ⟨g, rfl⟩ := hA
  have hA_le_W : conjSubgroup V g ≤ E3.wClos V 1 S := by
    refine E3.le_wClos_of_mQuot_le hV g hAS le_rfl ?_ ?_
    · rw [E3.mQuot_self]
      norm_num
    · omega
  have hcS : E3.cClos V 1 S ≤ S ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) := by
    rw [E3.cClos]
    exact inf_le_inf_left S (Subgroup.centralizer_le (fun x hx => hA_le_W hx))
  have hCtau : S ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ≤
      E1.tauOf K S (conjSubgroup V g) := by
    intro t ht
    obtain ⟨htS, htC⟩ := ht
    refine (E1.mem_tauOf_of_le hSK).mpr ⟨htS, fun a ha => ?_⟩
    have hcomm : a * t = t * a := Subgroup.mem_centralizer_iff.mp htC a ha
    rw [commutatorElement_def, ← hcomm]
    simp
  have hle1 : E3.cClos V 1 S ≤ S ⊓ H := (hcS.trans hCtau).trans hH.2.1
  have hWmono : E3.wClos V 1 (S ⊓ H) ≤ E3.wClos V 1 S := E3.wClos_mono inf_le_left
  have hle2 : E3.cClos V 1 S ≤ Subgroup.centralizer (E3.wClos V 1 (S ⊓ H) : Set G) := by
    rw [E3.cClos]
    exact (inf_le_right).trans (Subgroup.centralizer_le (fun x hx => hWmono hx))
  rw [E3.cClos]
  exact le_inf hle1 hle2

private theorem nineStep3_conjSubgroup_iSup {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g :=
  Subgroup.map_iSup _ _

theorem commutator_cClos_ne_bot_of_isE (hV : IsElemAbelian 2 V) (hm : 2 < rk ↥V)
    (h : TwoPTwoIrred K S X p) {A H : Subgroup G} (hA : IsGConj V A) (hAS : A ≤ S)
    (hH : E1.IsE 1 K S A H) (hHres : ¬ twoResidual H ≤ nineFrattiniR K X)
    (hC : ⁅twoResidual K, E3.cClos V 1 S⁆ ≠ ⊥) :
    ⁅twoResidual H, E3.cClos V 1 (S ⊓ H)⁆ ≠ ⊥ := by
  intro hbot
  have hSK : S ≤ K := h.sylowTwo.le
  have hleC : E3.cClos V 1 S ≤ E3.cClos V 1 (S ⊓ H) :=
    cClos_le_cClos_inf_of_isE hV hm hSK hA hAS hH
  have hcommHS : ⁅twoResidual H, E3.cClos V 1 S⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅twoResidual H, E3.cClos V 1 S⁆
        ≤ ⁅twoResidual H, E3.cClos V 1 (S ⊓ H)⁆ := Subgroup.commutator_mono le_rfl hleC
      _ = ⊥ := hbot
  have hcent : twoResidual H ≤ Subgroup.centralizer (E3.cClos V 1 S : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommHS
  have hconj_cent : ∀ s ∈ S, conjSubgroup (twoResidual H) s ≤
      Subgroup.centralizer (E3.cClos V 1 S : Set G) := by
    intro s hs
    have hsN : s ∈ Subgroup.normalizer (E3.cClos V 1 S : Set G) :=
      (E3.normalizer_le_normalizer_cClos (V := V) (i := 1) S) (Subgroup.le_normalizer hs)
    have hconjC : conjSubgroup (E3.cClos V 1 S) s = E3.cClos V 1 S :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hsN
    calc conjSubgroup (twoResidual H) s
        ≤ conjSubgroup (Subgroup.centralizer (E3.cClos V 1 S : Set G)) s :=
          E3.conjSubgroup_mono_left s hcent
      _ = Subgroup.centralizer (conjSubgroup (E3.cClos V 1 S) s : Set G) :=
          E3.conjSubgroup_centralizer (E3.cClos V 1 S) s
      _ = Subgroup.centralizer (E3.cClos V 1 S : Set G) := by rw [hconjC]
  let N : Subgroup G := ⨆ s : S, conjSubgroup (twoResidual H) (s : G)
  have hNleK : N ≤ K := by
    refine iSup_le fun s : S => ?_
    have hsK : (s : G) ∈ K := hSK s.2
    calc conjSubgroup (twoResidual H) (s : G)
        ≤ conjSubgroup K (s : G) := E3.conjSubgroup_mono_left _
          ((twoResidual_le H).trans hH.1)
      _ = K := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hsK)
  have hRes_le_N : twoResidual H ≤ N := by
    have h1 := le_iSup (fun s : S => conjSubgroup (twoResidual H) (s : G)) ⟨1, S.one_mem⟩
    simpa [conjSubgroup_one] using h1
  have hNcent : N ≤ Subgroup.centralizer (E3.cClos V 1 S : Set G) :=
    iSup_le fun s : S => hconj_cent (s : G) s.2
  have hle : ∀ s ∈ S, conjSubgroup N s ≤ N := by
    intro s hs
    have hmap : conjSubgroup N s = ⨆ t : S, conjSubgroup (twoResidual H) ((t : G) * s) := by
      have hN_eq : N = ⨆ t : S, conjSubgroup (twoResidual H) (t : G) := rfl
      rw [hN_eq, nineStep3_conjSubgroup_iSup]
      simp_rw [conjSubgroup_conjSubgroup]
    rw [hmap]
    refine iSup_le fun t : S => ?_
    exact le_iSup (fun u : S => conjSubgroup (twoResidual H) (u : G))
      ⟨(t : G) * s, S.mul_mem t.2 hs⟩
  have heq : ∀ s ∈ S, conjSubgroup N s = N := by
    intro s hs
    refine le_antisymm (hle s hs) ?_
    have h1 := hle s⁻¹ (S.inv_mem hs)
    have h2 := E3.conjSubgroup_mono_left s h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
  have hS_N : S ≤ Subgroup.normalizer (N : Set G) := fun s hs =>
    conjSubgroup_eq_iff_mem_normalizer.mp (heq s hs)
  have hRes_N : twoResidual H ≤ Subgroup.normalizer (N : Set G) :=
    hRes_le_N.trans (Subgroup.le_normalizer (H := N))
  have hK_N : K ≤ Subgroup.normalizer (N : Set G) := by
    rw [← sup_twoResidual_eq_of_not_le_frattiniR h hH.1 hHres]
    exact sup_le hS_N hRes_N
  have hNnormal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNleK).mpr hK_N
  have hnotN : ¬ N ≤ nineFrattiniR K X := fun hleN => hHres (hRes_le_N.trans hleN)
  have hresK_N : twoResidual K ≤ N :=
    TwoPTwoIrred.twoResidual_le_of_not_le_frattiniR h hNleK hNnormal hnotN
  have hcommK : ⁅twoResidual K, E3.cClos V 1 S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hresK_N.trans hNcent)
  exact hC hcommK

end CFSG.LocalAnalysis.WeakClosure81
