module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzCount
public import CFSG.Quasithin.Vol2.Ch3Sec1L319S3Wr
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.L319 (S3Wr S3Wr_card)

variable {G : Type} [Group G]

theorem eq_of_sylow_le_kz2 [Finite G] {Gz T R : Subgroup G} (hT : IsSylowTwoOf T Gz)
    (hR : IsPGroup 2 R) (hTR : T ≤ R) (hRG : R ≤ Gz) : R = T := by
  have hdvd : T.relIndex R ∣ T.relIndex Gz := by
    rw [← Subgroup.relIndex_mul_relIndex T R Gz hTR hRG]
    exact dvd_mul_right _ _
  have hodd : ¬ 2 ∣ T.relIndex Gz := hT.2.2
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hidx : (T.subgroupOf R).index ∣ Nat.card R := Subgroup.index_dvd_card _
  rw [hn] at hidx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  have hrel : T.relIndex R = 2 ^ j := hj
  have hj0 : j = 0 := by
    by_contra hj0
    apply hodd
    refine dvd_trans ?_ hdvd
    rw [hrel]
    exact dvd_pow_self 2 hj0
  have h1 : T.relIndex R = 1 := by rw [hrel, hj0, pow_zero]
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hTR

theorem pCoreOf_le_of_sylow_kz2 [Finite G] {Gz T K : Subgroup G} (hT : IsSylowTwoOf T Gz)
    (hKG : K ≤ Gz) (hTK : T ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ T := by
  have hsub : T ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hTK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hOp : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hR : IsPGroup 2 ↥(pCoreOf 2 K ⊔ T) := IsPGroup.to_sup_of_normal_left' hOp hT.2.1 hsub
  have hRG : pCoreOf 2 K ⊔ T ≤ Gz := sup_le ((pCoreOf_le 2 K).trans hKG) hT.1
  have hEq := eq_of_sylow_le_kz2 hT hR le_sup_right hRG
  rw [← hEq]
  exact le_sup_left

theorem not_two_dvd_relIndex_kz2 [Finite G] {Gz T K : Subgroup G} (hT : IsSylowTwoOf T Gz)
    (hKG : K ≤ Gz) (hTK : T ≤ Subgroup.normalizer (K : Set G)) : ¬ 2 ∣ T.relIndex K := by
  have hTW : T ≤ T ⊔ K := le_sup_left
  have hKW : K ≤ T ⊔ K := le_sup_right
  have hWG : T ⊔ K ≤ Gz := sup_le hT.1 hKG
  have hdvd : T.relIndex (T ⊔ K) ∣ T.relIndex Gz := by
    rw [← Subgroup.relIndex_mul_relIndex T (T ⊔ K) Gz hTW hWG]
    exact dvd_mul_right _ _
  have hodd : ¬ 2 ∣ T.relIndex Gz := hT.2.2
  have hiso : K.relIndex T = K.relIndex (T ⊔ K) := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hTK
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTK
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T K hTK).toEquiv
  have hA := Subgroup.relIndex_mul_card (H := T) (K := K)
  have hB := Subgroup.relIndex_mul_card (H := K) (K := T)
  have hC := Subgroup.relIndex_mul_card (H := T) (K := T ⊔ K)
  have hD := Subgroup.relIndex_mul_card (H := K) (K := T ⊔ K)
  rw [inf_eq_left.mpr hTW] at hC
  rw [inf_eq_left.mpr hKW] at hD
  rw [inf_comm K T] at hB
  have hpos : 0 < Nat.card (T ⊓ K : Subgroup G) := Nat.card_pos
  have hbc : T.relIndex (T ⊔ K) = T.relIndex K := by
    have hdpos : 0 < K.relIndex T := by
      rcases Nat.eq_zero_or_pos (K.relIndex T) with h | h
      · exfalso
        rw [h, zero_mul] at hB
        have : 0 < Nat.card T := Nat.card_pos
        omega
      · exact h
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hdpos hpos)
    have e1 : T.relIndex (T ⊔ K) * Nat.card T = Nat.card (T ⊔ K : Subgroup G) := hC
    have e2 : K.relIndex (T ⊔ K) * Nat.card K = Nat.card (T ⊔ K : Subgroup G) := hD
    have e3 : T.relIndex K * Nat.card (T ⊓ K : Subgroup G) = Nat.card K := hA
    have e4 : K.relIndex T * Nat.card (T ⊓ K : Subgroup G) = Nat.card T := hB
    rw [← hiso] at e2
    calc T.relIndex (T ⊔ K) * (K.relIndex T * Nat.card (T ⊓ K : Subgroup G))
        = T.relIndex (T ⊔ K) * Nat.card T := by rw [e4]
      _ = Nat.card (T ⊔ K : Subgroup G) := e1
      _ = K.relIndex T * Nat.card K := e2.symm
      _ = K.relIndex T * (T.relIndex K * Nat.card (T ⊓ K : Subgroup G)) := by rw [e3]
      _ = T.relIndex K * (K.relIndex T * Nat.card (T ⊓ K : Subgroup G)) := by ring
  rw [← hbc]
  intro h2
  exact hodd (dvd_trans h2 hdvd)

theorem sixteen_dvd_kz2 (c r a b : ℕ) (hc : ¬ 2 ∣ c) (h1 : c * 2 ^ a = 7920 * 2 ^ b)
    (h2 : r * 2 ^ b = 2 ^ a) : 16 ∣ r := by
  have hd1 : 2 ^ (b + 4) ∣ c * 2 ^ a := ⟨495, by rw [h1]; ring⟩
  have hcop : Nat.Coprime (2 ^ (b + 4)) c :=
    Nat.Coprime.pow_left (b + 4) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hc)
  have hd2 : 2 ^ (b + 4) ∣ 2 ^ a := Nat.Coprime.dvd_of_dvd_mul_left hcop hd1
  have hba : b + 4 ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd2
  obtain ⟨k, rfl⟩ : ∃ k, a = b + 4 + k := ⟨a - (b + 4), by omega⟩
  have hr : r * 2 ^ b = 2 ^ b * (16 * 2 ^ k) := h2.trans (by ring)
  have hpos : 0 < 2 ^ b := by positivity
  have : r = 16 * 2 ^ k := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact hr)
  exact ⟨2 ^ k, this⟩

theorem eq_one_of_two_three_kz2 {Q : Type} [Group Q] {A B : Subgroup Q} (hA : IsPGroup 2 A)
    (hB : IsPGroup 3 B) {x : Q} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨n, hn⟩ := hA ⟨x, hxA⟩
  obtain ⟨m, hm⟩ := hB ⟨x, hxB⟩
  have h2 : orderOf x ∣ 2 ^ n := by
    have hn' : x ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    exact orderOf_dvd_of_pow_eq_one hn'
  have h3 : orderOf x ∣ 3 ^ m := by
    have hm' : x ^ 3 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact orderOf_dvd_of_pow_eq_one hm'
  have hcop : Nat.Coprime (2 ^ n) (3 ^ m) := Nat.Coprime.pow n m (by norm_num)
  have h1 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd h2 h3
    rwa [Nat.Coprime.gcd_eq_one hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)


theorem mem_pCore_iff_kz2 {K : Subgroup G} (x : ↥K) :
    x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := by
  unfold pCoreOf
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

theorem false_of_m11_K_kz2 [Finite G] (hM : M11Sub144O2_kz)
    {Gz T H K X P : Subgroup G} (φ : ↥H →* S3Wr) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (pCoreOf 2 H).subgroupOf H)
    (hT : IsSylowTwoOf T Gz) (hTH : T ≤ H) (hKG : K ≤ Gz) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hXH : X ≤ H) (hXK : X ≤ K) (hPX : P ≤ X) (hP3 : IsPGroup 3 P) (hPc : Nat.card P = 9)
    (hKM : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH72 : (pCoreOf 2 H).relIndex H = 72 := by
    rw [Subgroup.relIndex, ← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top,
      S3Wr_card]
  have hcardM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
    CFSG.Sporadic.Mathieu.card_M11
  have hQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 7920 := by
    rw [Nat.card_congr hKM.some.toEquiv, hcardM]
  have hM' : ∀ U : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), Nat.card U = 144 → CFSG.pCore 2 ↥U = ⊥ :=
    fun U hU => hM _ hKM U hU
  set N : Subgroup ↥K := CFSG.pCore 2 ↥K with hNdef
  set S : Subgroup ↥K := (T ⊓ K).subgroupOf K with hSdef
  have hN_T : ∀ x ∈ N, (x : G) ∈ T := fun x hx =>
    pCoreOf_le_of_sylow_kz2 hT hKG hTK ((mem_pCore_iff_kz2 x).mp hx)
  have hNS : N ≤ S := by
    intro x hx
    rw [hSdef, Subgroup.mem_subgroupOf]
    exact ⟨hN_T x hx, x.2⟩
  let g : S →* (↥K ⧸ N) := (QuotientGroup.mk' N).comp S.subtype
  have hker : g.ker = N.subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hcardker : Nat.card g.ker = Nat.card N := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  have hcardS : Nat.card S = Nat.card (T ⊓ K : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
  have hr1 : Nat.card N * Nat.card g.range = Nat.card (T ⊓ K : Subgroup G) := by
    rw [← hcardS, ← hcardker]
    exact Subgroup.card_ker_mul_card_range g
  have hNp : IsPGroup 2 ↥N := CFSG.pCore_isPGroup
  obtain ⟨b, hb⟩ := hNp.exists_card_eq
  have hTKp : IsPGroup 2 ↥(T ⊓ K : Subgroup G) := hT.2.1.to_le inf_le_left
  obtain ⟨a, ha⟩ := hTKp.exists_card_eq
  have hidx : N.index = 7920 := hQ
  have hKc : 7920 * Nat.card N = Nat.card K := by
    rw [← hidx]
    exact Subgroup.index_mul_card N
  have hcK : T.relIndex K * Nat.card (T ⊓ K : Subgroup G) = Nat.card K :=
    Subgroup.relIndex_mul_card T K
  have harith1 : T.relIndex K * 2 ^ a = 7920 * 2 ^ b := by
    rw [← ha, ← hb, hcK, hKc]
  have harith2 : Nat.card g.range * 2 ^ b = 2 ^ a := by
    rw [← ha, ← hb, ← hr1, mul_comm]
  have h16g : 16 ∣ Nat.card g.range :=
    sixteen_dvd_kz2 _ _ _ _ (not_two_dvd_relIndex_kz2 hT hKG hTK) harith1 harith2
  have hrange_le : g.range ≤ kzImage_kz H K := by
    rintro _ ⟨s, rfl⟩
    have hs : ((s : ↥K) : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp s.2
    exact MonoidHom.mem_range.mpr ⟨⟨((s : ↥K) : G), ⟨hTH hs.1, hs.2⟩⟩, rfl⟩
  have h16 : 16 ∣ Nat.card (kzImage_kz H K) := h16g.trans (Subgroup.card_dvd_of_le hrange_le)
  have hPK : P ≤ K := hPX.trans hXK
  set SP : Subgroup ↥K := P.subgroupOf K with hSPdef
  let gP : SP →* (↥K ⧸ N) := (QuotientGroup.mk' N).comp SP.subtype
  have hkerP : gP.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxN : (SP.subtype x : ↥K) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hxS : (SP.subtype x : ↥K) ∈ SP := x.2
    have hNP : IsPGroup 2 N := CFSG.pCore_isPGroup
    have hSP : IsPGroup 3 SP := hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
    have h1 := eq_one_of_two_three_kz2 hNP hSP hxN hxS
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  have hcardP : Nat.card gP.range = 9 := by
    have h := Subgroup.card_ker_mul_card_range gP
    rw [hkerP, Subgroup.card_bot, one_mul] at h
    have hSPc : Nat.card SP = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    rw [h, hSPc, hPc]
  have hrangeP_le : gP.range ≤ kzImage_kz H K := by
    rintro _ ⟨s, rfl⟩
    have hsP : ((s : ↥K) : G) ∈ P := Subgroup.mem_subgroupOf.mp s.2
    exact MonoidHom.mem_range.mpr ⟨⟨((s : ↥K) : G), ⟨hXH (hPX hsP), ((s : ↥K)).2⟩⟩, rfl⟩
  have h9 : 9 ∣ Nat.card (kzImage_kz H K) := by
    rw [← hcardP]
    exact Subgroup.card_dvd_of_le hrangeP_le
  exact false_of_kzImage_card_kz hH72 hQ hM' h16 h9

end CFSG.Quasithin.H13
