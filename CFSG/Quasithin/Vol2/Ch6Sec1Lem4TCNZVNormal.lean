module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFinal
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCNZVOrder
public import CFSG.Quasithin.EmptyFaithful.T1521SCutComp
public import CFSG.Quasithin.Vol2.Ch1EightFourInit

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open NZVOrder
open CFSG.Quasithin.Ch1Four (init_of_a312Case init_of_a312Nonquasi)

theorem nZVNormalFact_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (hO2 : L216ModuleFact) :
    NZVNormalFact := by
  intro G _ _ T M L V M₁ K₁ X h horth hM₁ hCM₁ hK₁ htits hTK hKZ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := ZV614 T L V with hZdef
  set H : Subgroup G := Subgroup.normalizer (Z : Set G) with hHdef
  have hsim := h.simple
  have hnab := h.nonabelian
  have hqtke := h.qtke
  have hTM : T ≤ M := h.T_le
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTM.trans h.normal
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := Hyp611.T_le_normalizer h
  have hTC : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.le_centralizer_iff.mpr ((quasithinOmegaOneCenter_le_inf T).trans inf_le_right)
  have hTM₁ : T ≤ M₁ := hTC.trans hCM₁
  have hTH : T ≤ H := by
    intro t ht
    refine normalizer_ZV614 (hTV ht) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hLx := Subgroup.mem_normalizer_iff.mp (hTN ht) x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), hLx.mp hxL⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, hLx.mpr hxL⟩
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
  have hSylH : IsSylowTwoOf T H := by
    refine ⟨hTH, h.sylow.1, ?_⟩
    have hrel := Subgroup.relIndex_mul_index hTH
    intro h2
    apply h.sylow.2
    have h2' : 2 ∣ T.relIndex H := h2
    rw [← hrel]
    exact Dvd.dvd.mul_right h2' _
  have hZ4 : Nat.card Z = 4 := (hO2 G T M L V h horth).2
  have hZne : Z ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ4
    norm_num at hZ4
  have hZH : Z ≤ H := Subgroup.le_normalizer
  have hZn : (Z.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr le_rfl
  have hZp : IsPGroup 2 Z := (IsPGroup.iff_card).2 ⟨2, hZ4⟩
  have hZpc : Z ≤ pCoreOf 2 H := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hZH hz⟩, ?_, rfl⟩
    have hmem : Z.subgroupOf H ≤ CFSG.pCore 2 ↥H :=
      le_sSup (show Z.subgroupOf H ∈ {K : Subgroup ↥H | K.Normal ∧ IsPGroup 2 K} from
        ⟨hZn, hZp.of_equiv (Subgroup.subgroupOfEquivOfLe hZH).symm⟩)
    exact hmem (Subgroup.mem_subgroupOf.mpr hz)
  have hHne : pCoreOf 2 H ≠ ⊥ := fun h0 => hZne (le_bot_iff.mp (h0 ▸ hZpc))
  have hK₁H : K₁ ≤ H := hKZ.trans (centralizer_le_normalizer614 Z)
  have hB : K₁ ∈ lFamily T :=
    cComp_mem_of_le hK₁ le_sup_left (sup_le (le_of_mem_cComp hK₁) hTM₁)
  obtain ⟨L', hL', hK₁L'⟩ := lemma_1_2_4_exists hqtke hsim hnab h37 h39 hHne hSylH hK₁H hB
  have hL'n := lemma_1_2_4_normal hqtke hsim hnab h37 h38 hHne hSylH hB hK₁L' hL' hTK
  obtain ⟨ψ, hψ, hψN⟩ := exists_modO2_surj_of_le (G := G) hK₁H
  obtain ⟨i, hi⟩ := card_modO2_of_surj ψ hψ hψN
  have hK₁card : Nat.card (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = 17971200 :=
    CFSG.Quasithin.T1521SCut.card_isTits htits
  have hBcard : Nat.card (↥(modO2Image H K₁) ⧸ CFSG.pCore 2 ↥(modO2Image H K₁)) =
      17971200 * 2 ^ i := by
    rw [hi, hK₁card]
  rcases lemma_1_2_4_list hqtke hsim hnab h312 hHne hSylH hK₁H hB hL' hK₁L' with heq | hcase | hnq
  ·
    have hpT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hSylH
    have hL'N : L' ≤ Subgroup.normalizer (K₁ : Set G) := by
      intro x hx
      have hxH : x ∈ H := le_of_mem_cComp hL' hx
      have hmemL : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨x, hxH⟩ : ↥H) ∈ modO2Image H L' :=
        Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      have hmemK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨x, hxH⟩ : ↥H) ∈ modO2Image H K₁ := by
        rw [heq]
        exact hmemL
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmemK
      have hyK : (y : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hy
      have hq : (y : G)⁻¹ * x ∈ pCoreOf 2 H := by
        have hk : (y : ↥H)⁻¹ * ⟨x, hxH⟩ ∈ CFSG.pCore 2 ↥H :=
          (QuotientGroup.eq).mp hyeq
        exact Subgroup.mem_map.mpr ⟨(y : ↥H)⁻¹ * ⟨x, hxH⟩, hk, by simp⟩
      have hqT : (y : G)⁻¹ * x ∈ T := hpT hq
      have hxeq : x = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [hxeq]
      exact Subgroup.mul_mem _ (Subgroup.le_normalizer hyK) (hTK hqT)
    have hK₁L'n : (K₁.subgroupOf L').Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁L').mpr hL'N
    have hsub : IsSubnormal K₁ H :=
      CFSG.Quasithin.A3.subnormal_trans (CFSG.Quasithin.A3.subnormal_of_normal hK₁L' hK₁L'n)
        (subnormal_of_mem_cComp hL')
    have hK₁eq : K₁ = L' := by
      by_contra hne
      have hlt : K₁ < L' := lt_of_le_of_ne hK₁L' hne
      exact hL'.2.2.2 K₁ hlt hK₁.1 hK₁.2.1 hsub
    rw [hK₁eq]
    exact hL'n
  ·
    exfalso
    have hI := init_of_a312Case hcase
    rw [hBcard] at hI
    exact not_initNum_tits i _ hI
  ·
    exfalso
    have hBL : modO2Image H K₁ ≤ modO2Image H L' := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr
        (hK₁L' (Subgroup.mem_subgroupOf.mp hy)), rfl⟩
    have hK₁perf : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr hK₁.2.1
    haveI := hK₁perf
    have hperf : Group.IsPerfect ↥(modO2Image H K₁) := Group.IsPerfect.ofSurjective (f := ψ) hψ
    have hI := init_of_a312Nonquasi hBL hperf hnq
    rw [hBcard] at hI
    exact not_initNum_tits i _ hI

end CFSG.Quasithin.H13.T614
