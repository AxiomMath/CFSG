module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
public import CFSG.Quasithin.Recognition.St84.AppTreeSAP2
public import CFSG.Quasithin.Recognition.St84.AppTreeSAS3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
  CFSG.Quasithin.St84 CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112sa_odd_relIndex_of_two_elements_mem {G : Type*} [Group G]
    {A E : Subgroup G} [Finite E] (hAE : A ≤ E) [hN : (A.subgroupOf E).Normal]
    (h : ∀ x : ↥E, IsPGroup 2 (Subgroup.zpowers x) → (x : G) ∈ A) :
    Odd (A.relIndex E) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2' : 2 ∣ A.relIndex E := even_iff_two_dvd.mp heven
  have h2 : 2 ∣ Nat.card (↥E ⧸ A.subgroupOf E) := by
    simpa [Subgroup.relIndex, Subgroup.index_eq_card] using h2'
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf E) q
  let π : ↥E →* ↥E ⧸ A.subgroupOf E := QuotientGroup.mk' (A.subgroupOf E)
  have hq2 : π x ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  have hx2A : (x : G) ^ 2 ∈ A := by
    have hmem : (x ^ 2 : ↥E) ∈ A.subgroupOf E :=
      (QuotientGroup.eq_one_iff (x ^ 2)).mp (by
        change π (x ^ 2) = 1
        rw [map_pow, hq2])
    exact Subgroup.mem_subgroupOf.mp hmem
  have hxnotA : (x : G) ∉ A := by
    intro hxA
    have h1 : π x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxA)
    rw [h1] at hq
    simp at hq
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      exfalso
      have h2dvd : 2 ∣ orderOf x := by
        rw [← hq]
        exact orderOf_map_dvd π x
      rw [hkm, pow_zero, one_mul] at h2dvd
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2dvd)
    · exact hk
  have hzp : (x ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm m (2 ^ k), ← hkm, pow_orderOf_eq_one]
  have hz : IsPGroup 2 (Subgroup.zpowers (x ^ m)) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hzp)
  have hmemA : (x ^ m : ↥E) ∈ A.subgroupOf E :=
    Subgroup.mem_subgroupOf.mpr (h (x ^ m) hz)
  have hqpow : π x ^ m = π x := by
    obtain ⟨t, ht⟩ := hm
    rw [ht, pow_succ, pow_mul, hq2, one_pow, one_mul]
  have h1 : π (x ^ m) = 1 := (QuotientGroup.eq_one_iff _).mpr hmemA
  rw [map_pow, hqpow] at h1
  rw [h1] at hq
  simp at hq

theorem f112saP2_V_le_X2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    f112saP2_V L2 S ≤ f112saX2 L1 L2 S :=
  le_inf (f112saP2_V_le_M L2 S)
    (fun _ hx => (le_sup_right : S ≤ bigB L1 L2 S) hx.1.1)

theorem f112saP2_V_isPGroup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : IsPGroup 2 (f112saP2_V L2 S) :=
  hF.1.h2.pgroup.to_le (fun _ hx => hx.1.1)

theorem f112saX2_le_normalizer_V_of_hyp111R {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (hR : Hyp111R L1 L2 S) :
    f112saX2 L1 L2 S ≤
      Subgroup.normalizer (f112saP2_V L2 S : Set H) := by
  have hB1 : bigB L1 L2 S ≤
      Subgroup.normalizer ((S ⊓ L2 : Subgroup H) : Set H) :=
    (F1.bigB_le_normalizer_sylow hR).2
  have hB2 : bigB L1 L2 S ≤
      Subgroup.normalizer (oTwoRes L2 : Set H) :=
    f112sa_bigB_le_normalizer_oTwoRes_right hF.toW
  have hBV : bigB L1 L2 S ≤
      Subgroup.normalizer ((S ⊓ L2 ⊓ oTwoRes L2 : Subgroup H) : Set H) :=
    (le_inf hB1 hB2).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := S ⊓ L2) (K := oTwoRes L2))
  exact (f112sa_X2_le_bigB L1 L2 S).trans (by simpa [f112saP2_V] using hBV)

noncomputable abbrev f112saBigT (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  pCoreOf 2 (f112saHalpha L1 L2 S)

theorem f112saBigT_isPGroup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : IsPGroup 2 (f112saBigT L1 L2 S) := by
  rw [f112saBigT, CFSG.Open.pCoreOf]
  exact (CFSG.pCore_isPGroup (G := ↥(f112saHalpha L1 L2 S)) (p := 2)).map
    (f112saHalpha L1 L2 S).subtype

theorem f112saBigT_le_normalizer_Halpha {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saHalpha L1 L2 S ≤
      Subgroup.normalizer (f112saBigT L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (Subgroup.le_normalizer).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saHalpha L1 L2 S))

theorem f112saBigT_le_normalizer_Nalpha {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saNalpha L1 L2 S ≤
      Subgroup.normalizer (f112saBigT L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (f112saNalpha_le_normalizer_Halpha hF).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (f112saHalpha L1 L2 S))

noncomputable abbrev f112saMB (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  ((oTwoRes L2).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB

noncomputable abbrev f112saBigW (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112saMB L1 L2 S ⊔ f112saBigT L1 L2 S

theorem f112saMB_le_range (L1 L2 S : Subgroup H) :
    f112saMB L1 L2 S ≤ (f112Gold L1 L2 S).ofB.range :=
  Subgroup.map_le_range _ _

theorem f112saUbeta_le_normalizer_MB {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    (f112Gold L1 L2 S).ofB.range ≤
      Subgroup.normalizer (f112saMB L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  intro g hg
  obtain ⟨p, rfl⟩ := hg
  have hconj : ∀ q : ↥(f112P2 L1 L2 S), ∀ x ∈ f112saMB L1 L2 S,
      (f112Gold L1 L2 S).ofB q * x * ((f112Gold L1 L2 S).ofB q)⁻¹ ∈
        f112saMB L1 L2 S := by
    intro q x hx
    obtain ⟨m, hm, rfl⟩ := hx
    have hm' : (m : H) ∈ oTwoRes L2 := Subgroup.mem_subgroupOf.mp hm
    have hqm : (q : H) * (m : H) * (q : H)⁻¹ ∈ oTwoRes L2 :=
      (Subgroup.mem_normalizer_iff.mp (f112saP2_oTwoRes_normal hF h1 q.2) (m : H)).mp hm'
    have hqmP : (q : H) * (m : H) * (q : H)⁻¹ ∈ f112P2 L1 L2 S :=
      (f112P2 L1 L2 S).mul_mem ((f112P2 L1 L2 S).mul_mem q.2 m.2)
        ((f112P2 L1 L2 S).inv_mem q.2)
    refine Subgroup.mem_map.mpr
      ⟨⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩,
        Subgroup.mem_subgroupOf.mpr hqm, ?_⟩
    change (f112Gold L1 L2 S).ofB (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ :
        ↥(f112P2 L1 L2 S)) =
      (f112Gold L1 L2 S).ofB q * (f112Gold L1 L2 S).ofB m *
        ((f112Gold L1 L2 S).ofB q)⁻¹
    rw [show (⟨(q : H) * (m : H) * (q : H)⁻¹, hqmP⟩ : ↥(f112P2 L1 L2 S)) =
      q * m * q⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj p x
  · intro hx
    have h := hconj p⁻¹ ((f112Gold L1 L2 S).ofB p * x * ((f112Gold L1 L2 S).ofB p)⁻¹) hx
    have heq : (f112Gold L1 L2 S).ofB p⁻¹ *
        ((f112Gold L1 L2 S).ofB p * x * ((f112Gold L1 L2 S).ofB p)⁻¹) *
        ((f112Gold L1 L2 S).ofB p⁻¹)⁻¹ = x := by
      rw [map_inv, inv_inv]
      group
    rwa [heq] at h

noncomputable abbrev f112saBigK (L1 L2 S : Subgroup H) : Subgroup H :=
  oTwoRes L2 ⊔ pCoreOf 2 (f112P2 L1 L2 S)

noncomputable abbrev f112saQ2B (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  ((pCoreOf 2 (f112P2 L1 L2 S)).subgroupOf (f112P2 L1 L2 S)).map
    (f112Gold L1 L2 S).ofB

noncomputable abbrev f112saBigL (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  ((f112saBigK L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB

theorem f112saQ2_isPGroup {L1 L2 S : Subgroup H} :
    IsPGroup 2 (pCoreOf 2 (f112P2 L1 L2 S)) := by
  rw [CFSG.Open.pCoreOf]
  exact (CFSG.pCore_isPGroup (G := ↥(f112P2 L1 L2 S)) (p := 2)).map
    (f112P2 L1 L2 S).subtype

theorem f112saQ2B_isPGroup {L1 L2 S : Subgroup H} :
    IsPGroup 2 (f112saQ2B L1 L2 S) := by
  have h : IsPGroup 2 ((pCoreOf 2 (f112P2 L1 L2 S)).subgroupOf (f112P2 L1 L2 S)) :=
    (f112saQ2_isPGroup (L1 := L1) (L2 := L2) (S := S)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (f112P2 L1 L2 S))).symm
  exact h.map (f112Gold L1 L2 S).ofB

theorem f112saBigL_eq_sup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saBigL L1 L2 S = f112saMB L1 L2 S ⊔ f112saQ2B L1 L2 S := by
  let M : Subgroup H := oTwoRes L2
  let P : Subgroup H := f112P2 L1 L2 S
  let Q : Subgroup H := pCoreOf 2 P
  have hMK : M ≤ P := (oTwoRes_le L2).trans le_sup_left
  have hQK : Q ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hsub : (M ⊔ Q).subgroupOf P = M.subgroupOf P ⊔ Q.subgroupOf P :=
    @Subgroup.subgroupOf_sup H _ (oTwoRes L2) (pCoreOf 2 (f112P2 L1 L2 S))
      (f112P2 L1 L2 S) hMK hQK
  have hmap : f112saBigL L1 L2 S = ((M ⊔ Q).subgroupOf P).map
      (f112Gold L1 L2 S).ofB := rfl
  have hR : f112saMB L1 L2 S ⊔ f112saQ2B L1 L2 S =
      (M.subgroupOf P ⊔ Q.subgroupOf P).map (f112Gold L1 L2 S).ofB := by
    change Subgroup.map (f112Gold L1 L2 S).ofB (M.subgroupOf P) ⊔
      Subgroup.map (f112Gold L1 L2 S).ofB (Q.subgroupOf P) = _
    rw [Subgroup.map_sup]
  rw [hmap, hR, hsub]

theorem f112sa_pCoreOf_L {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) :
    pCoreOf 2 (f112saBigL L1 L2 S) = f112saQ2B L1 L2 S := by
  let M : Subgroup H := oTwoRes L2
  let P : Subgroup H := f112P2 L1 L2 S
  let Q : Subgroup H := pCoreOf 2 P
  let K : Subgroup H := M ⊔ Q
  have hKle : K ≤ P :=
    sup_le ((oTwoRes_le L2).trans le_sup_left) (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hpc : pCoreOf 2 (K.subgroupOf P) = (pCoreOf 2 K).subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [pCoreOf_subgroupOf_map (K := K) (E := P) hKle,
      Subgroup.map_subgroupOf_eq_of_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKle)]
  have hpcL : pCoreOf 2 (f112saBigL L1 L2 S) =
      (pCoreOf 2 (K.subgroupOf P)).map (f112Gold L1 L2 S).ofB := by
    change pCoreOf 2 (Subgroup.map (f112Gold L1 L2 S).ofB (K.subgroupOf P)) = _
    exact pCoreOf_map_injective (f := (f112Gold L1 L2 S).ofB)
      (f112Gold L1 L2 S).ofB_injective (K.subgroupOf P)
  have hpcK : pCoreOf 2 K = Q := by
    change pCoreOf 2 (M ⊔ Q) = Q
    exact @pCoreOf_sup_pCoreOf H _ (oTwoRes L2) (f112P2 L1 L2 S)
      ((oTwoRes_le L2).trans le_sup_left)
      (by change f112P2 L1 L2 S ≤ Subgroup.normalizer (oTwoRes L2 : Set H)
          exact f112saP2_oTwoRes_normal hF h1)
  rw [hpcL, hpc, hpcK]

noncomputable abbrev f112saBigR (L1 L2 S : Subgroup H) : Subgroup H :=
  ((f112saBigT L1 L2 S).comap (f112Gold L1 L2 S).ofB).map
    (f112P2 L1 L2 S).subtype

theorem f112saBigR_isPGroup {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) : IsPGroup 2 (f112saBigR L1 L2 S) :=
  ((f112saBigT_isPGroup hF).comap_of_injective (f112Gold L1 L2 S).ofB
    (f112Gold L1 L2 S).ofB_injective).map (f112P2 L1 L2 S).subtype

theorem f112saBigR_conj_mem {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S)
    {x y : H} (hx : x ∈ f112saX2 L1 L2 S) (hy : y ∈ f112saBigR L1 L2 S) :
    x * y * x⁻¹ ∈ f112saBigR L1 L2 S := by
  let X := f112Gold L1 L2 S
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
  have hpT : X.ofB p ∈ f112saBigT L1 L2 S := Subgroup.mem_comap.mp hp
  have hxB : x ∈ bigB L1 L2 S := f112sa_X2_le_bigB L1 L2 S hx
  have hxP1 : x ∈ f112P1 L1 L2 S := Subgroup.mem_sup_right hxB
  have hxP2 : x ∈ f112P2 L1 L2 S := Subgroup.mem_sup_right hxB
  have hxA : X.ofA ⟨x, hxP1⟩ ∈ f112saNalpha L1 L2 S := by
    refine Subgroup.mem_inf.mpr ⟨?_, ⟨⟨x, hxP1⟩, rfl⟩⟩
    exact f112sa_X2_map_le_EOdd (Subgroup.mem_map.mpr
      ⟨⟨x, hxP1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hxT : X.ofA ⟨x, hxP1⟩ ∈
      Subgroup.normalizer (f112saBigT L1 L2 S : Set X.Universal) :=
    f112saBigT_le_normalizer_Nalpha hF hxA
  have hconj : X.ofA ⟨x, hxP1⟩ * X.ofB p * (X.ofA ⟨x, hxP1⟩)⁻¹ ∈
      f112saBigT L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp hxT (X.ofB p)).mp hpT
  let px : ↥(f112P2 L1 L2 S) := ⟨x, hxP2⟩
  refine Subgroup.mem_map.mpr ⟨px * p * px⁻¹, Subgroup.mem_comap.mpr ?_, ?_⟩
  · have hB : X.ofB px = X.ofA ⟨x, hxP1⟩ :=
      (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hxP1, hxP2⟩).symm
    rw [map_mul, map_mul, map_inv, hB]
    exact hconj
  · rfl

theorem f112saBigR_normalized_X2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saX2 L1 L2 S ≤
      Subgroup.normalizer (f112saBigR L1 L2 S : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact f112saBigR_conj_mem hF hx hy
  · intro hy
    have hx' : x⁻¹ ∈ f112saX2 L1 L2 S := (f112saX2 L1 L2 S).inv_mem hx
    have hz := f112saBigR_conj_mem hF hx' hy
    simpa [mul_assoc] using hz

theorem f112saMB_le_BigL {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) :
    f112saMB L1 L2 S ≤ f112saBigL L1 L2 S := by
  rw [f112saBigL_eq_sup hF]
  exact le_sup_left

theorem f112saBigK_le_P2 (L1 L2 S : Subgroup H) :
    f112saBigK L1 L2 S ≤ f112P2 L1 L2 S :=
  sup_le ((oTwoRes_le L2).trans le_sup_left)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (f112P2 L1 L2 S))

theorem f112saBigL_quot_BigK {L1 L2 S : Subgroup H} :
    Nonempty (oTwoQuot ↥(f112saBigL L1 L2 S) ≃* oTwoQuot ↥(f112saBigK L1 L2 S)) := by
  let P : Subgroup H := f112P2 L1 L2 S
  let K : Subgroup H := f112saBigK L1 L2 S
  have hKle : K ≤ P := f112saBigK_le_P2 L1 L2 S
  let e : ↥(f112saBigL L1 L2 S) ≃* ↥K :=
    (Subgroup.equivMapOfInjective (K.subgroupOf P) (f112Gold L1 L2 S).ofB
      (f112Gold L1 L2 S).ofB_injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKle)
  exact ⟨pCoreQuotientMulEquiv 2 e⟩

theorem f112sa_exists_adj {L1 L2 S : Subgroup H} (v : Vtx (f112Gold L1 L2 S)) :
    ∃ w, (f112Gold L1 L2 S).treeGraph.Adj v w := by
  let X := f112Gold L1 L2 S
  obtain ⟨g, rfl⟩ | ⟨g, rfl⟩ := exists_smul_base X v
  · exact ⟨g • baseB X, (adj_smul X g (baseA X) (baseB X)).2 (adj_baseA_baseB X)⟩
  · exact ⟨g • baseA X,
      (adj_smul X g (baseB X) (baseA X)).2 (adj_baseA_baseB X).symm⟩
