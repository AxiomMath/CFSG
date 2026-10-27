module

public import CFSG.Quasithin.Background.E3Closed
public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Generation

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem exists_mem_le_mQuot_eq {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : ℕ}
    (hc : c < rk ↥B) {b : G} (hb : b ∈ B) :
    ∃ D : Subgroup G, D ≤ B ∧ b ∈ D ∧ mQuot B D = c := by
  have hB2 : IsPGroup 2 B := B2F.isPGroup_of_isElemAbelian hB
  have hcard : Nat.card B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup hB2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x : ↥B := ⟨b, hb⟩ with hx
  have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hB.2 b hb)
  have hord : Nat.card (Subgroup.zpowers x) ∣ 2 ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx2
  obtain ⟨n, hn1, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  obtain ⟨K, hK, hxK⟩ := Sylow.exists_subgroup_card_pow_prime_le (G := ↥B) 2 (n := n)
    (m := rk ↥B - c) (by rw [hcard]; exact pow_dvd_pow 2 (Nat.sub_le _ _)) (Subgroup.zpowers x)
    hn (by omega)
  refine ⟨K.map B.subtype, Subgroup.map_subtype_le K, ⟨x, hxK (Subgroup.mem_zpowers x), rfl⟩, ?_⟩
  have hDB : K.map B.subtype ≤ B := Subgroup.map_subtype_le K
  have hDcard : Nat.card (K.map B.subtype) = 2 ^ (rk ↥B - c) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hK]
  have h := card_eq_two_pow_mul hB2 hDB
  rw [hcard, hDcard, ← pow_add] at h
  have h' := Nat.pow_right_injective (le_refl 2) h
  omega

omit [Finite G] in
theorem rk_conjSubgroup (V : Subgroup G) (g : G) : rk ↥(conjSubgroup V g) = rk ↥V := by
  unfold rk
  rw [card_conjSubgroup]

theorem le_wClos_of_mQuot_le (hV : IsElemAbelian 2 V) {X B : Subgroup G} (g : G) (hBX : B ≤ X)
    (hBg : B ≤ conjSubgroup V g) {k : ℕ} (hk : mQuot (conjSubgroup V g) B ≤ k)
    (hkV : k < rk ↥V) : B ≤ wClos V k X := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hVg2 : IsPGroup 2 (conjSubgroup V g) := B2F.isPGroup_of_isElemAbelian hVg
  have hB2 : IsPGroup 2 B := hVg2.to_le hBg
  have hBab : IsElemAbelian 2 B := B2F.isElemAbelian_mono hBg hVg
  set m := mQuot (conjSubgroup V g) B with hm
  have hrk : rk ↥(conjSubgroup V g) = m + rk ↥B := by
    have h := card_eq_two_pow_mul hVg2 hBg
    rw [card_eq_two_pow_of_isPGroup hVg2, card_eq_two_pow_of_isPGroup hB2, ← pow_add] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hrkV : rk ↥(conjSubgroup V g) = rk ↥V := rk_conjSubgroup V g
  intro b hb
  have hc : k - m < rk ↥B := by omega
  obtain ⟨D, hDB, hbD, hmD⟩ := exists_mem_le_mQuot_eq hBab hc hb
  have hmem : D ∈ gammaSet V k X := by
    refine ⟨hDB.trans hBX, g, hDB.trans hBg, ?_⟩
    have := mQuot_add (V := conjSubgroup V g) hDB hBg
    omega
  exact le_wClos hmem hbD

theorem le_wClos_of_mQuot_le_self (hV : IsElemAbelian 2 V) {X B : Subgroup G} (hBX : B ≤ X)
    (hBV : B ≤ V) {k : ℕ} (hk : mQuot V B ≤ k) (hkV : k < rk ↥V) : B ≤ wClos V k X :=
  le_wClos_of_mQuot_le hV 1 hBX (by rwa [conjSubgroup_one]) (by rwa [conjSubgroup_one]) hkV

theorem mQuot_eq_of_card_eq {V V' A : Subgroup G} (hV : IsPGroup 2 V) (hV' : IsPGroup 2 V')
    (hAV : A ≤ V) (hAV' : A ≤ V') (hc : Nat.card V = Nat.card V') : mQuot V A = mQuot V' A := by
  have h1 := card_eq_two_pow_mul hV hAV
  have h2 := card_eq_two_pow_mul hV' hAV'
  rw [hc, h2] at h1
  have h3 := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  exact (Nat.pow_right_injective (le_refl 2) h3).symm

theorem mQuot_conj_eq {A : Subgroup G} (hV : IsElemAbelian 2 V) {g : G} (hAV : A ≤ V)
    (hAg : A ≤ conjSubgroup V g) : mQuot V A = mQuot (conjSubgroup V g) A :=
  mQuot_eq_of_card_eq (B2F.isPGroup_of_isElemAbelian hV)
    (B2F.isPGroup_of_isElemAbelian (isElemAbelian_conjSubgroup hV g)) hAV hAg
    (card_conjSubgroup V g).symm

omit [Finite G] in
theorem lt_sParam_of_lt (hV : IsElemAbelian 2 V) {k : ℕ} (hr : (k : ℕ∞) < rParam V)
    (hm : k < mParam (autI hV ⊤)) : k < sParam hV := by
  have hne : min (rParam V) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (min_le_right _ _)
  have h : (k : ℕ∞) < (sParam hV : ℕ∞) := by
    unfold sParam
    rw [ENat.natCast_toNat hne]
    exact lt_min hr (by exact_mod_cast hm)
  exact_mod_cast h

omit [Finite G] in
theorem mParam_le_rk {W : Type*} [CommGroup W] [Finite W] (X : Subgroup (MulAut W)) :
    mParam X ≤ rk W := by
  unfold mParam
  split_ifs with hev
  · by_cases hne : {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty
    · obtain ⟨t, -, -, ht⟩ := Nat.sInf_mem hne
      rw [ht]
      have := rk_add_rkIdx (fixV (Subgroup.zpowers t))
      omega
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
  · exact le_rfl

theorem sParam_le_rk (hV : IsElemAbelian 2 V) : sParam hV ≤ rk ↥V := by
  have h1 : mParam (autI hV ⊤) ≤ rk (IntMod V hV) := mParam_le_rk _
  have h2 : rk (IntMod V hV) = rk ↥V := by
    unfold rk
    rfl
  exact (sParam_le_mParam hV).trans (h1.trans h2.le)

end Generation

section Core

variable {G : Type u} [Group G] [Finite G] {V H S : Subgroup G}

theorem pCoreOf_le_of_isE {j : ℕ} {A K : Subgroup G} (hK : E1.IsE j H S A K) :
    pCoreOf 2 K ≤ S :=
  (B6.pCoreOf_two_le_of_isSylowTwoOf hK.2.2.1).trans inf_le_left

theorem e3_17_mQuot (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j : ℕ} {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K) :
    mQuot V (A ⊓ pCoreOf 2 K) ≤ i + j := by
  have hAab : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAV hV
  obtain ⟨-, hcard⟩ := card_le_of_isE hS hAS hAab hK
  have hA2 : IsPGroup 2 A := B2F.isPGroup_of_isElemAbelian hAab
  have hmB : mQuot A (A ⊓ pCoreOf 2 K) ≤ j := by
    have e := card_eq_two_pow_mul hA2 (inf_le_left : A ⊓ pCoreOf 2 K ≤ A)
    rw [e] at hcard
    have := Nat.le_of_mul_le_mul_right hcard Nat.card_pos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
  have hadd := mQuot_add (V := V) (inf_le_left : A ⊓ pCoreOf 2 K ≤ A) hAV
  omega

theorem e3_17_B_le (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkV : k < rk ↥V) {A K : Subgroup G} (hAS : A ≤ S) (hAV : A ≤ V)
    (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K) :
    A ⊓ pCoreOf 2 K ≤ wClos V k (pCoreOf 2 K) :=
  le_wClos_of_mQuot_le_self hV inf_le_right (inf_le_left.trans hAV)
    ((e3_17_mQuot hV hS hAS hAV hAi hK).trans hijk) hkV

theorem e3_17_cent_le (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K) :
    Subgroup.centralizer (wClos V k (pCoreOf 2 K) : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hBW := e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  refine (Subgroup.centralizer_le hBW).trans ?_
  by_contra hnot
  have h1 := rParam_le_mQuot (inf_le_left.trans hAV) hnot
  have hmk : mQuot V (A ⊓ pCoreOf 2 K) ≤ k := (e3_17_mQuot hV hS hAS hAV hAi hK).trans hijk
  exact absurd (lt_of_lt_of_le hkr (h1.trans (Nat.cast_le.2 hmk))) (lt_irrefl _)

omit [Finite G] in
theorem le_normalizer_inf_centralizer {K W : Subgroup G} (hKW : K ≤ Subgroup.normalizer (W : Set G)) :
    K ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) := by
  intro h hh
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have h1 : conjSubgroup K h = K := conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hh)
  have h2 : conjSubgroup W h = W := conjSubgroup_eq_iff_mem_normalizer.2 (hKW hh)
  rw [conjSubgroup_inf, conjSubgroup_centralizer, h1, h2]

theorem e3_17_le (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K) :
    cClos V k S ≤ cClos V k (pCoreOf 2 K) := by
  set Q := pCoreOf 2 K with hQ
  set W := wClos V k Q with hW
  have hNV := e3_17_cent_le hV hS hijk hkr hkV hAS hAV hAi hK
  have hQS : Q ≤ S := pCoreOf_le_of_isE hK
  have hAW : A ≤ wClos V k S :=
    le_wClos_of_mQuot_le_self hV hAS hAV (hAi.trans (by omega)) hkV
  have hCA : cClos V k S ≤ S ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hAW))
  have hτ : S ⊓ Subgroup.centralizer (A : Set G) ≤ E1.tauOf H S A := by
    intro t ht
    refine ⟨ht.1, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hS.le ht.1), fun a ha => ?_⟩
    have h1 : a * t = t * a := Subgroup.mem_centralizer_iff.1 ht.2 a ha
    rw [commutatorElement_eq_one_iff_mul_comm.2 h1.symm]
    exact Subgroup.one_mem _
  have hCK : cClos V k S ≤ K := fun x hx => (hK.2.1 (hτ (hCA hx))).2
  have hSW : wClos V k Q ≤ wClos V k S := wClos_mono hQS
  have hCW : cClos V k S ≤ Subgroup.centralizer (W : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hSW)
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans (normalizer_le_normalizer_wClos Q)
  have hY : K ⊓ Subgroup.centralizer (W : Set G) ≤
      kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K :=
    le_kerIn_of_le_normalizer (inf_le_inf_left K hNV) (le_normalizer_inf_centralizer hKW)
  have hCY : cClos V k S ≤ kerIn (K ⊓ Subgroup.normalizer (V : Set G)) K :=
    fun x hx => hY ⟨hCK hx, hCW hx⟩
  have h2 : IsPGroup 2 (cClos V k S) := hS.isPGroup.to_le inf_le_left
  have hCQ : cClos V k S ≤ Q := e3_12_le_pCoreOf hV hS hAV hAS ⟨j, hK⟩ h2 hCY
  exact le_inf hCQ hCW

theorem e3_17_comm_ne (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) :
    ⁅twoResidual K, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ ∧ ⁅A, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ := by
  have hle := e3_17_le hV hS hijk hkr hkV hAS hAV hAi hK
  have h1 : ⁅twoResidual K, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ := fun h =>
    hne (le_bot_iff.1 (h ▸ Subgroup.commutator_mono le_rfl hle))
  refine ⟨h1, fun hA => h1 ?_⟩
  have hAK : A ≤ K := (card_le_of_isE hS hAS (B2F.isElemAbelian_mono hAV hV) hK).1
  have hKC : K ≤ Subgroup.normalizer (cClos V k (pCoreOf 2 K) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans (normalizer_le_normalizer_cClos _)
  have hAC : A ≤ Subgroup.centralizer (cClos V k (pCoreOf 2 K) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hA
  have hcc : conjClosure A K ≤ Subgroup.centralizer (cClos V k (pCoreOf 2 K) : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
    have hc' : h⁻¹ * c * h ∈ cClos V k (pCoreOf 2 K) := by
      have := (Subgroup.mem_normalizer_iff.1 (hKC (K.inv_mem hh)) c).1 hc
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.1 (hAC hz) _ hc'
    calc c * (h * z * h⁻¹) = h * ((h⁻¹ * c * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * c * h)) * h⁻¹ := by rw [hcomm]
      _ = h * z * h⁻¹ * c := by group
  have hres : twoResidual K ≤ conjClosure A K := E1.twoResidual_le_conjClosure hK.isEAny
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hres.trans hcc)

theorem e3_17_two_core (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) :
    V ⊓ centerOf (wClos V k (pCoreOf 2 K)) ≠ ⊥ := by
  obtain ⟨-, hAC⟩ := e3_17_comm_ne hV hS hijk hkr hkV hAS hAV hAi hK hne
  intro h
  apply hAC
  set Q := pCoreOf 2 K with hQ
  set W := wClos V k Q with hW
  have hNV := e3_17_cent_le hV hS hijk hkr hkV hAS hAV hAi hK
  have hAK : A ≤ K := (card_le_of_isE hS hAS (B2F.isElemAbelian_mono hAV hV) hK).1
  have hKC : K ≤ Subgroup.normalizer (cClos V k Q : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K).trans (normalizer_le_normalizer_cClos _)
  have hmk : mQuot V (A ⊓ Q) ≤ k := (e3_17_mQuot hV hS hAS hAV hAi hK).trans hijk
  have hVQ : V ⊓ Q ≤ W :=
    le_wClos_of_mQuot_le_self hV inf_le_right inf_le_left
      ((mQuot_mono (inf_le_inf_right _ hAV)).trans hmk) hkV
  rw [eq_bot_iff]
  refine le_trans ?_ h.le
  refine Subgroup.commutator_le.2 fun a ha c hc => ?_
  have hcW : c ∈ Subgroup.centralizer (W : Set G) := (Subgroup.mem_inf.1 hc).2
  have hcQ : c ∈ Q := (Subgroup.mem_inf.1 hc).1
  have haV : a ∈ V := hAV ha
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := hNV hcW
  have hV' : ⁅a, c⁆ ∈ V := by
    have e : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem haV ((Subgroup.mem_normalizer_iff.1 hcN _).1 (V.inv_mem haV))
  have hC' : ⁅a, c⁆ ∈ cClos V k Q := by
    have e : ⁅a, c⁆ = (a * c * a⁻¹) * c⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    have h1 : a * c * a⁻¹ ∈ cClos V k Q := by
      have := (Subgroup.mem_normalizer_iff.1 (hKC (hAK ha)) c).1 hc
      exact this
    exact (cClos V k Q).mul_mem h1 ((cClos V k Q).inv_mem hc)
  have hQ' : ⁅a, c⁆ ∈ Q := (Subgroup.mem_inf.1 hC').1
  have hW' : ⁅a, c⁆ ∈ W := hVQ ⟨hV', hQ'⟩
  exact Subgroup.mem_inf.2 ⟨hV', hW', (Subgroup.mem_inf.1 hC').2⟩

theorem e3_17_comm_eq_bot (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K)
    (hs : k < sParam hV) : ⁅A, cClos V k (pCoreOf 2 K)⁆ = ⊥ := by
  have hBW := e3_17_B_le hV hS hijk hkV hAS hAV hAi hK
  have hmk : mQuot V (A ⊓ pCoreOf 2 K) ≤ k := (e3_17_mQuot hV hS hAS hAV hAi hK).trans hijk
  have hCB : cClos V k (pCoreOf 2 K) ≤ Subgroup.centralizer ((A ⊓ pCoreOf 2 K : Subgroup G) : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hBW)
  have hE : IsPGroup 2 (cClos V k (pCoreOf 2 K)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left
  have h6 := (e3_6 hV (A := A) (B := A ⊓ pCoreOf 2 K) (E := cClos V k (pCoreOf 2 K)) inf_le_left
    hAV (lt_of_le_of_lt hmk hs) hE).1
  have hCA : cClos V k (pCoreOf 2 K) ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    have hx' : x ∈ cClos V k (pCoreOf 2 K) ⊓
        Subgroup.centralizer ((A ⊓ pCoreOf 2 K : Subgroup G) : Set G) := ⟨hx, hCB hx⟩
    rw [← h6] at hx'
    exact hx'.2
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hCA

theorem e3_17_three_core (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hAS : A ≤ S) (hAV : A ≤ V) (hAi : mQuot V A ≤ i) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) : mParam (autI hV ⊤) ≤ k := by
  by_contra hm
  push Not at hm
  have hs : k < sParam hV := lt_sParam_of_lt hV hkr hm
  exact (e3_17_comm_ne hV hS hijk hkr hkV hAS hAV hAi hK hne).2
    (e3_17_comm_eq_bot hV hS hijk hkV hAS hAV hAi hK hs)

end Core

section E317

variable {G : Type u} [Group G] [Finite G] {V H S : Subgroup G}

theorem e3_17_one (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hA : A ∈ gammaSet V i S) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) :
    cClos V k S ≤ cClos V k (pCoreOf 2 K) ∧
      ⁅twoResidual K, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ ∧ ⁅A, cClos V k (pCoreOf 2 K)⁆ ≠ ⊥ := by
  obtain ⟨hAS, g, hAg, hmg⟩ := hA
  have hVg := isElemAbelian_conjSubgroup hV g
  have hkr' : (k : ℕ∞) < rParam (conjSubgroup V g) := by rwa [rParam_conj]
  have hkV' : k < rk ↥(conjSubgroup V g) := by rwa [rk_conjSubgroup]
  have hne' : ⁅twoResidual K, cClos (conjSubgroup V g) k S⁆ ≠ ⊥ := by rwa [cClos_conjV]
  have hle := e3_17_le hVg hS hijk hkr' hkV' hAS hAg hmg.le hK
  have hcomm := e3_17_comm_ne hVg hS hijk hkr' hkV' hAS hAg hmg.le hK hne'
  simp only [cClos_conjV] at hle hcomm
  exact ⟨hle, hcomm⟩

theorem e3_17_two (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hA : A ∈ gammaSet V i S) (hAV : A ≤ V) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) :
    V ⊓ centerOf (wClos V k (pCoreOf 2 K)) ≠ ⊥ := by
  obtain ⟨hAS, g, hAg, hmg⟩ := hA
  have hmV : mQuot V A ≤ i := (mQuot_conj_eq hV hAV hAg).trans_le hmg.le
  exact e3_17_two_core hV hS hijk hkr hkV hAS hAV hmV hK hne

theorem e3_17_three (hV : IsElemAbelian 2 V) (hS : IsSylowIn 2 S H) {i j k : ℕ}
    (hijk : i + j ≤ k) (hkr : (k : ℕ∞) < rParam V) (hkV : k < rk ↥V) {A K : Subgroup G}
    (hA : A ∈ gammaSet V i S) (hK : E1.IsE j H S A K)
    (hne : ⁅twoResidual K, cClos V k S⁆ ≠ ⊥) : mParam (autI hV ⊤) ≤ k := by
  obtain ⟨hAS, g, hAg, hmg⟩ := hA
  have hVg := isElemAbelian_conjSubgroup hV g
  have hkr' : (k : ℕ∞) < rParam (conjSubgroup V g) := by rwa [rParam_conj]
  have hkV' : k < rk ↥(conjSubgroup V g) := by rwa [rk_conjSubgroup]
  have hne' : ⁅twoResidual K, cClos (conjSubgroup V g) k S⁆ ≠ ⊥ := by rwa [cClos_conjV]
  have h := e3_17_three_core hVg hS hijk hkr' hkV' hAS hAg hmg.le hK hne'
  rwa [mParam_conj hV g hVg] at h

end E317

end E3

end CFSG.Quasithin
