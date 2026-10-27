module

public import CFSG.Timmesfeld.Bridge.RootSetsConn5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20y
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen
public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3P
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_normalizer_quot_of_isSU3
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSU3 X n) {S : Subgroup X}
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) :
    IsCyclic (↥(Subgroup.normalizer (S : Set X)) ⧸
        S.subgroupOf (Subgroup.normalizer (S : Set X))) := by
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hX.2
  have hperf : Group.IsPerfect (↥(⊤ : Subgroup X)) := by
    rw [Group.IsPerfect.top_iff]
    exact Group.isPerfect_def.mpr hX.1.1
  let eTop : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  let eQ : (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ≃*
      (X ⧸ Subgroup.center X) :=
    QuotientGroup.congr _ _ eTop (Subgroup.map_center_eq eTop)
  have hXPSU : CFSG.Quasithin.IsPSU 3 2 n (X ⧸ Subgroup.center X) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hX.2
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv eQ.symm hXPSU
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S (⊤ : Subgroup X) :=
    CFSG.Quasithin.E1.isSylowIn_two_iff.mp hS
  have hU3 := CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n hn2 X (⊤ : Subgroup X) S
    hperf hPSU hSyl
  obtain ⟨-, -, -, hgen, -⟩ := hU3
  have hgen' : ∃ g ∈ Subgroup.normalizer (S : Set X),
      ∀ b ∈ Subgroup.normalizer (S : Set X), ∃ k, (g ^ k)⁻¹ * b ∈ S := by
    simpa using hgen
  haveI : (S.subgroupOf (Subgroup.normalizer (S : Set X))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  exact CFSG.Quasithin.H13.P31X.isCyclic_quotient_of_cyc hgen'

theorem uc2_17_36b_dvd_index
    {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSU3 X n)
    {S : Subgroup X} (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤)
    {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqdvd : q ∣ 2 ^ n + 1) :
    q ∣ (S.subgroupOf (Subgroup.normalizer (S : Set X))).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hX.2
  have hq3' : ¬ q ∣ 2 * 1 + 1 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hW := uc22pwliu_borelWit_of_lieModel (r := 1) (ε := 1) hX.1 le_rfl le_rfl
    (by norm_num) hn2 hX.2 hq hqdvd hq3'
  have hidx : ¬ 2 ∣ S.index := by
    have h := hS.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at h
  let P : Sylow 2 X := hS.isPGroup.toSylow hidx
  obtain ⟨F, hFN, -, hFcard⟩ := hW P
  have hqN : q ∣ Nat.card (Subgroup.normalizer (S : Set X)) := by
    have h := Subgroup.card_dvd_of_le hFN
    rw [hFcard, pow_one] at h
    exact h
  have hcard := Subgroup.card_mul_index (S.subgroupOf (Subgroup.normalizer (S : Set X)))
  have hSS : Nat.card (S.subgroupOf (Subgroup.normalizer (S : Set X))) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  rw [hSS] at hcard
  obtain ⟨k, hk⟩ := hS.isPGroup.exists_card_eq
  have hcop : Nat.Coprime q (Nat.card S) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((hq.odd_of_ne_two (by omega)).coprime_two_right)
  rw [← hcard] at hqN
  exact hcop.dvd_of_dvd_mul_left hqN

private theorem exists_permuting_of_odd_prime_card {W U T : Subgroup G} {q : ℕ}
    (hUW : U ≤ W) (hUT : U ≤ T) (hU2 : IsPGroup 2 U)
    (hWT : T ≤ Subgroup.normalizer (W : Set G))
    (hq : q.Prime) (hqodd : Odd q)
    (hcard : Nat.card W = q * Nat.card U) :
    ∃ A : Subgroup G, A ≤ W ∧ Nat.card A = q ∧ Permutes A T := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hqW : q ∣ Nat.card W := by
    rw [hcard]
    exact dvd_mul_right q _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' q (by simpa using hqW)
  let A : Subgroup G := Subgroup.zpowers (a : G)
  have hAcard : Nat.card A = q := by
    rw [show A = Subgroup.zpowers (a : G) from rfl, Nat.card_zpowers,
      Subgroup.orderOf_coe, ha]
  have hAW : A ≤ W := by
    rw [show A = Subgroup.zpowers (a : G) from rfl, Subgroup.zpowers_le]
    exact a.2
  have hdisj : Disjoint U A :=
    UC22.uc22pw_disjoint_of_odd (N := U) (A := A) hU2 (by rw [hAcard]; exact hqodd)
  have hUA : (U : Set G) * (A : Set G) = (W : Set G) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowAltSix.set_mul_eq_of_card U A W
      hUW hAW (disjoint_iff.mp hdisj)
      (by rw [hAcard, hcard, Nat.mul_comm])
  exact ⟨A, hAW, hAcard, UC22.uc22pw_permutes_of_split hUT hWT hUA⟩

private theorem transfer_preimage
    {L T : Subgroup G} {n q : ℕ}
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hSyl : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L) L)
    (hshape : IsSU3 (Bar2 L) n)
    (hq : q.Prime) (hq3 : 3 < q) (hqdiv : q ∣ 2 ^ n + 1) :
    ∃ W : Subgroup G, W ≤ L ∧ (T ⊓ L : Subgroup G) ≤ W ∧
      Nat.card W = q * Nat.card (T ⊓ L : Subgroup G) ∧
      T ≤ Subgroup.normalizer (W : Set G) ∧
      W ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  let Lg := ↥L
  let U₁ : Subgroup Lg := (T ⊓ L).subgroupOf L
  let X := Lg ⧸ CFSG.pCore 2 Lg
  let π : Lg →* X := QuotientGroup.mk' (CFSG.pCore 2 Lg)
  let S : Subgroup X := U₁.map π
  have hmapU : U₁.map L.subtype = (T ⊓ L) :=
    Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have htopL : (⊤ : Subgroup Lg).map L.subtype = L := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hU₁ : CFSG.Quasithin.IsSylowIn 2 U₁ ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_of_injective
      (p := 2) (f := L.subtype) (P := U₁) (H := ⊤) L.subtype_injective)
    exact h.mp (by simpa [hmapU, htopL] using hSyl)
  have hSX : CFSG.Quasithin.IsSylowIn 2 S ⊤ :=
    CFSG.Quasithin.E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective _) hU₁
  have hXshape : IsSU3 X n := hshape
  have hcyc := isCyclic_normalizer_quot_of_isSU3 (n := n) hXshape hSX
  have hdivq : q ∣ (S.subgroupOf (Subgroup.normalizer (S : Set X))).index :=
    uc2_17_36b_dvd_index hshape hSX hq hq3 hqdiv
  let NX : Subgroup X := Subgroup.normalizer (S : Set X)
  let SN : Subgroup ↥NX := S.subgroupOf NX
  haveI : SN.Normal := inferInstance
  let QX := ↥NX ⧸ SN
  have hQXcyc : IsCyclic QX := hcyc
  have hqQX : q ∣ Nat.card QX := by
    rw [← Subgroup.index_eq_card]
    exact hdivq
  letI : CommGroup QX := IsCyclic.commGroup
  let C : Subgroup QX := (powMonoidHom q).ker
  have hCcard : Nat.card C = q := by
    rw [show C = (powMonoidHom q).ker from rfl,
      IsCyclic.card_powMonoidHom_ker QX q, Nat.gcd_eq_right hqQX]
  let WX : Subgroup X := (C.comap (QuotientGroup.mk' SN)).map NX.subtype
  have hWXcard : Nat.card WX = q * Nat.card S := by
    rw [show WX = (C.comap (QuotientGroup.mk' SN)).map NX.subtype from rfl,
      Subgroup.card_map_of_injective NX.subtype_injective,
      CFSG.Timmesfeld.Bridge.card_comap_mk'_eq (H := ↥NX) (J := SN) C, hCcard,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := S))).toEquiv,
      Nat.mul_comm]
  let WL : Subgroup Lg := WX.comap π
  have hcompS : S.comap π = U₁ := by
    have hker : π.ker ≤ U₁ := by
      rw [QuotientGroup.ker_mk']
      haveI : (CFSG.pCore 2 Lg).Normal := CFSG.pCore_normal
      exact CFSG.Quasithin.IsSylowIn.le_of_normal (p := 2) (P := U₁) (H := ⊤)
        (N := CFSG.pCore 2 Lg) hU₁ le_top (by infer_instance) CFSG.pCore_isPGroup
    exact Subgroup.comap_map_eq_self (f := π) (H := U₁) hker
  have hWLcard : Nat.card WL = q * Nat.card U₁ := by
    have h1 : Nat.card WL = Nat.card (CFSG.pCore 2 Lg) * Nat.card WX := by
      rw [show WL = WX.comap π from rfl,
        CFSG.Timmesfeld.Bridge.card_comap_mk'_eq (J := CFSG.pCore 2 Lg) WX]
    have h2 : Nat.card U₁ = Nat.card (CFSG.pCore 2 Lg) * Nat.card S := by
      calc Nat.card U₁ = Nat.card (S.comap π) := by rw [hcompS]
        _ = Nat.card (CFSG.pCore 2 Lg) * Nat.card S := by
          rw [CFSG.Timmesfeld.Bridge.card_comap_mk'_eq (J := CFSG.pCore 2 Lg) S]
    rw [h1, hWXcard, h2]; ring
  have hWLmem : ∀ y : Lg, y ∈ WL ↔ π y ∈ NX ∧ y ^ q ∈ U₁ := by
    intro y
    constructor
    · intro hy
      have hyW : π y ∈ WX := hy
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.1 hyW
      have hn1 : ((QuotientGroup.mk' SN) n) ^ q = 1 := MonoidHom.mem_ker.mp hn
      refine ⟨?_, ?_⟩
      · rw [← hny]; exact n.2
      · have h2 : ((n : ↥NX) ^ q) ∈ SN := by
          rw [← QuotientGroup.eq_one_iff]
          simpa [map_pow] using hn1
        have h3 : ((n : X) ^ q) ∈ S := by
          rw [Subgroup.mem_subgroupOf] at h2
          exact h2
        have h3' : π (y ^ q) ∈ S := by
          simpa [map_pow, ← hny] using h3
        have h3'' : y ^ q ∈ Subgroup.comap π S := h3'
        rwa [hcompS] at h3''
    · rintro ⟨hyN, hyq⟩
      let n : ↥NX := ⟨π y, hyN⟩
      have hnq : (n : ↥NX) ^ q ∈ SN := by
        rw [Subgroup.mem_subgroupOf]
        show ((n : X) ^ q) ∈ S
        rw [show (n : X) = π y from rfl, ← map_pow]
        exact Subgroup.mem_map.2 ⟨y ^ q, hyq, rfl⟩
      have hnC : (QuotientGroup.mk' SN) n ∈ C := by
        refine MonoidHom.mem_ker.mpr ?_
        have hq1 : (QuotientGroup.mk' SN) (n ^ q) = 1 :=
          (QuotientGroup.eq_one_iff (n ^ q)).mpr hnq
        simpa [map_pow] using hq1
      exact Subgroup.mem_map.2 ⟨n, hnC, rfl⟩
  have hcomapNX_le : Subgroup.comap π NX ≤ Subgroup.normalizer (U₁ : Set Lg) := by
    have h := Subgroup.le_normalizer_comap (f := π) (H := S)
    rwa [hcompS] at h
  let WG : Subgroup G := WL.map L.subtype
  have hcardU : Nat.card U₁ = Nat.card (T ⊓ L : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := (T ⊓ L : Subgroup G)) (K := L) (inf_le_right : (T ⊓ L : Subgroup G) ≤ L)).toEquiv
  have hWGcard : Nat.card WG = q * Nat.card (T ⊓ L : Subgroup G) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hWLcard, hcardU]
  have hT_N : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (H := T) ht, hTL ht⟩
  have hWG_mem : ∀ x : G, x ∈ WG ↔
      x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧ x ∈ L ∧
        x ^ q ∈ (T ⊓ L : Subgroup G) := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hyW := hy
      rw [hWLmem] at hyW
      have hyN : y ∈ Subgroup.normalizer (U₁ : Set Lg) := hcomapNX_le hyW.1
      have hxN : ((y : Lg) : G) ∈
          Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
        CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_of_mem_normalizer_subgroupOf
          (K := (T ⊓ L : Subgroup G)) (H := L) inf_le_right hyN
      have hq : ((y ^ q : Lg) : G) ∈ (T ⊓ L : Subgroup G) :=
        (Subgroup.mem_subgroupOf (H := (T ⊓ L : Subgroup G)) (K := L)).1 hyW.2
      exact ⟨hxN, y.2, by simpa using hq⟩
    · rintro ⟨hxN, hxL, hxq⟩
      let y : Lg := ⟨x, hxL⟩
      have hyN : y ∈ Subgroup.normalizer (U₁ : Set Lg) :=
        CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer hxN
      have hyS : π y ∈ NX := by
        have h := Subgroup.le_normalizer_map π (H := U₁)
          (Subgroup.mem_map.2 ⟨y, hyN, rfl⟩)
        simpa [S, NX] using h
      have hyq : y ^ q ∈ U₁ := by
        rw [Subgroup.mem_subgroupOf]
        change (x : G) ^ q ∈ (T ⊓ L : Subgroup G)
        exact hxq
      exact Subgroup.mem_map.2 ⟨y, (hWLmem y).mpr ⟨hyS, hyq⟩, rfl⟩
  have hWG_le_N : WG ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun x hx => ((hWG_mem x).mp hx).1
  have hWG_inv : ∀ t ∈ T, ∀ x ∈ WG, t * x * t⁻¹ ∈ WG := by
    intro t ht x hx
    rw [hWG_mem] at hx ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hT_N ht) hx.1) (Subgroup.inv_mem _ (hT_N ht)),
      (Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp hx.2.1, ?_⟩
    have hq := hx.2.2
    have h := (Subgroup.mem_normalizer_iff.mp (hT_N ht) _).mp hq
    change (t * x * t⁻¹) ^ q ∈ (T ⊓ L : Subgroup G)
    rw [show t * x * t⁻¹ = (MulAut.conj t) x by rfl,
      ← map_pow (MulAut.conj t) x q]
    exact h
  have hT_normWG : T ≤ Subgroup.normalizer (WG : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hWG_inv t ht x hx
    · intro hx
      have h := hWG_inv t⁻¹ (T.inv_mem ht) (t * x * t⁻¹) hx
      have heq : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
      rwa [heq] at h
  have hU_le_WG : (T ⊓ L : Subgroup G) ≤ WG := by
    intro u hu
    have huL : u ∈ L := (Subgroup.mem_inf.mp hu).2
    let y : Lg := ⟨u, huL⟩
    have hyS : π y ∈ S := by
      refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      simpa [y] using hu
    have hyN : π y ∈ NX := Subgroup.le_normalizer hyS
    have hyq : y ^ q ∈ U₁ := by
      rw [Subgroup.mem_subgroupOf]
      have h : ((y : Lg) : G) ^ q ∈ (T ⊓ L : Subgroup G) := by
        simpa [y] using (T ⊓ L).pow_mem hu q
      exact h
    have hyWL : y ∈ WL := (hWLmem y).mpr ⟨hyN, hyq⟩
    change L.subtype y ∈ WG
    exact Subgroup.mem_map.2 ⟨y, hyWL, rfl⟩
  exact ⟨WG, Subgroup.map_subtype_le _, hU_le_WG, hWGcard, hT_normWG, hWG_le_N⟩

theorem exists_permutes_of_isSU3_bar2
    {L T : Subgroup G} {n q : ℕ}
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hSyl : CFSG.Quasithin.IsSylowIn 2 (T ⊓ L) L)
    (hshape : IsSU3 (Bar2 L) n)
    (hq : q.Prime) (hq3 : 3 < q) (hqdiv : q ∣ 2 ^ n + 1) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = q ∧
      A ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧ Permutes A T := by
  obtain ⟨W, hWL, hUW, hWcard, hWT, hWN⟩ :=
    transfer_preimage hTL hSyl hshape hq hq3 hqdiv
  obtain ⟨A, hAW, hAcard, hperm⟩ :=
    exists_permuting_of_odd_prime_card hUW
      (inf_le_left : (T ⊓ L : Subgroup G) ≤ T) hSyl.isPGroup hWT hq
      (hq.odd_of_ne_two (by omega)) hWcard
  exact ⟨A, hAW.trans hWL, hAcard, hAW.trans hWN, hperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
