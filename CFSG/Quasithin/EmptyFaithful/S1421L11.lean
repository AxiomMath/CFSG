module

public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

@[expose] def IsHallOdd (B X : Subgroup G) : Prop :=
  B ≤ X ∧ Odd (Nat.card B) ∧ ∃ k : ℕ, B.relIndex X = 2 ^ k

@[expose] def BorelNormalizesK1 (M H K1 : Subgroup G) : Prop :=
  M ⊓ oTwoUpper H ≤ Subgroup.normalizer (K1 : Set G)

theorem relIndex_oTwoUpper_two_pow (H : Subgroup G) :
    ∃ k : ℕ, (oTwoUpper H).relIndex H = 2 ^ k := by
  have hN : ((oTwoUpper H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
      (le_normalizer_oTwoUpper H)
  have hp : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H h.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  exact ⟨k, hk⟩

omit [Finite G] in
theorem sup_eq_of_relIndex_two_pow_of_odd {A D X : Subgroup G} (hAX : A ≤ X) (hDX : D ≤ X)
    (hA : ∃ k : ℕ, A.relIndex X = 2 ^ k) (hD : Odd (D.relIndex X)) : A ⊔ D = X := by
  have hsup : A ⊔ D ≤ X := sup_le hAX hDX
  have h1 : (A ⊔ D).relIndex X ∣ A.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_left
  have h2 : (A ⊔ D).relIndex X ∣ D.relIndex X := Subgroup.relIndex_dvd_of_le_left X le_sup_right
  obtain ⟨k, hk⟩ := hA
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd : Odd ((A ⊔ D).relIndex X) := hD.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hsup hj

theorem isSylowTwoOf_inf_oTwoUpper (st : Setting1427 T M H K1) :
    IsSylowTwoOf (T ⊓ oTwoUpper H) (M ⊓ oTwoUpper H) := by
  have hTH : T ≤ H := st.hStar.1.1
  have hT : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo st.hyp.sylow hTH
  have hK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hT (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  exact A4.isSylowTwoOf_mono hK (inf_le_inf_right _ st.hyp.m_max.1.2) inf_le_right

theorem sup_oTwoUpper_eq (st : Setting1427 T M H K1) : oTwoUpper H ⊔ T = H := by
  have hTH : T ≤ H := st.hStar.1.1
  have hT : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo st.hyp.sylow hTH
  refine sup_eq_of_relIndex_two_pow_of_odd (oTwoUpper_le H) hTH
    (relIndex_oTwoUpper_two_pow H) ?_
  exact Nat.not_even_iff_odd.mp fun he => hT.2.2 (even_iff_two_dvd.mp he)

theorem exists_isHallOdd_of_normal_sylow {C P : Subgroup G} (hP : IsSylowTwoOf P C)
    (hN : C ≤ Subgroup.normalizer (P : Set G)) : ∃ B : Subgroup G, IsHallOdd B C := by
  have : (P.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP.1).mpr hN
  have hcardP : Nat.card (P.subgroupOf C) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
  obtain ⟨e, he⟩ := hP.2.1.exists_card_eq
  have hidx : ¬ 2 ∣ (P.subgroupOf C).index := hP.2.2
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf C)) (P.subgroupOf C).index := by
    rw [hcardP, he]
    exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  obtain ⟨D, hD⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hmul : Nat.card (P.subgroupOf C) * Nat.card D = Nat.card C := hD.card_mul_card
  have hmul' : (P.subgroupOf C).index * Nat.card (P.subgroupOf C) = Nat.card C :=
    Subgroup.index_mul_card _
  have hDcard : Nat.card D = (P.subgroupOf C).index := by
    have hpos : 0 < Nat.card (P.subgroupOf C) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hmul, ← hmul', mul_comm]
  have hDindex : D.index = 2 ^ e := by
    have h1 : D.index * Nat.card D = Nat.card C := Subgroup.index_mul_card _
    have hpos : 0 < Nat.card D := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← hmul, hcardP, he]
  refine ⟨D.map C.subtype, Subgroup.map_subtype_le D, ?_, ⟨e, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hDcard]
    exact Nat.odd_iff.mpr (by omega)
  · change ((D.map C.subtype).comap C.subtype).index = 2 ^ e
    rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective, hDindex]

theorem exists_isHallOdd_borel (st : Setting1427 T M H K1) :
    ∃ B : Subgroup G, IsHallOdd B (M ⊓ oTwoUpper H) :=
  exists_isHallOdd_of_normal_sylow (isSylowTwoOf_inf_oTwoUpper st) st.notation_.borel_inf

omit [Finite G] in
theorem le_normalizer_inf_centralizer {M V : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ d ∈ M ⊓ Subgroup.centralizer (V : Set G),
      m * d * m⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
    intro m hm d hd
    refine ⟨M.mul_mem (M.mul_mem hm hd.1) (M.inv_mem hm), ?_⟩
    show m * d * m⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hm)) v).mp hv
      simpa using this
    have hc := (Subgroup.mem_centralizer_iff.mp hd.2) _ hv'
    calc v * (m * d * m⁻¹) = m * ((m⁻¹ * v * m) * d) * m⁻¹ := by group
      _ = m * (d * (m⁻¹ * v * m)) * m⁻¹ := by rw [hc]
      _ = m * d * m⁻¹ * v := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro d
  refine ⟨key m hm d, fun hd => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hd
  simpa [mul_assoc] using this

theorem exists_mul_of_mem_inf (st : Setting1427 T M H K1) {B : Subgroup G}
    (hB : IsHallOdd B (M ⊓ oTwoUpper H)) {x : G} (hx : x ∈ M ⊓ H) :
    ∃ b ∈ B, ∃ t ∈ T, x = b * t := by
  have hTM : T ≤ M := st.hyp.m_max.1.2
  have hTH : T ≤ H := st.hStar.1.1
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hxKT : x ∈ oTwoUpper H ⊔ T := by
    rw [sup_oTwoUpper_eq st]
    exact hx.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at hxKT
  obtain ⟨k, hk, t, ht, hxe0⟩ := hxKT
  have hxe : k * t = x := hxe0
  have hkx : k = x * t⁻¹ := by rw [← hxe]; group
  have hkM : k ∈ M := hkx ▸ M.mul_mem hx.1 (M.inv_mem (hTM ht))
  have hCBP : B ⊔ (T ⊓ oTwoUpper H) = M ⊓ oTwoUpper H := by
    refine sup_eq_of_relIndex_two_pow_of_odd hB.1 (inf_le_inf_right _ hTM) hB.2.2 ?_
    exact Nat.not_even_iff_odd.mp fun he =>
      (isSylowTwoOf_inf_oTwoUpper st).2.2 (even_iff_two_dvd.mp he)
  have hBN : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    hB.1.trans st.notation_.borel_inf
  have hkC : k ∈ B ⊔ (T ⊓ oTwoUpper H) := by
    rw [hCBP]
    exact ⟨hkM, hk⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hkC
  obtain ⟨b, hb, p, hp, hkb0⟩ := hkC
  have hkb : b * p = k := hkb0
  refine ⟨b, hb, p * t, T.mul_mem hp.1 ht, ?_⟩
  rw [← hxe, ← hkb, mul_assoc]

omit [Finite G] in
theorem lemma_14_2_11_normalizes (hBor : BorelNormalizesK1 M H K1) {B : Subgroup G}
    (hB : IsHallOdd B (M ⊓ oTwoUpper H)) : B ≤ Subgroup.normalizer (K1 : Set G) :=
  hB.1.trans hBor

theorem lemma_14_2_11_comm (st : Setting1427 T M H K1) {B : Subgroup G}
    (hB : IsHallOdd B (M ⊓ oTwoUpper H)) : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) := by
  have hTM : T ≤ M := st.hyp.m_max.1.2
  have hTH : T ≤ H := st.hStar.1.1
  have hBX : B ≤ M ⊓ H := hB.1.trans (inf_le_inf_left _ (oTwoUpper_le H))
  have hTX : T ≤ M ⊓ H := le_inf hTM hTH
  have h1 : ∀ x ∈ T, ∀ y ∈ B, ∃ b ∈ B, ∃ t ∈ T, x * y = b * t := fun x hx y hy =>
    exists_mul_of_mem_inf st hB ((M ⊓ H).mul_mem (hTX hx) (hBX hy))
  ext z
  constructor
  · rintro ⟨b, hb, t, ht, rfl⟩
    obtain ⟨b', hb', t', ht', hy⟩ := exists_mul_of_mem_inf st hB
      ((M ⊓ H).inv_mem ((M ⊓ H).mul_mem (hBX hb) (hTX ht)))
    refine ⟨t'⁻¹, T.inv_mem ht', b'⁻¹, B.inv_mem hb', ?_⟩
    have := congrArg (fun w => w⁻¹) hy
    simpa [mul_inv_rev] using this.symm
  · rintro ⟨t, ht, b, hb, rfl⟩
    obtain ⟨b', hb', t', ht', hy⟩ := h1 t ht b hb
    exact ⟨b', hb', t', ht', hy.symm⟩

theorem lemma_14_2_11_comm_s (st : Setting1427 T M H K1) (hBor : BorelNormalizesK1 M H K1)
    {B : Subgroup G} (hB : IsHallOdd B (M ⊓ oTwoUpper H)) :
    (B : Set G) * (sOf T K1 : Set G) = (sOf T K1 : Set G) * (B : Set G) := by
  have hBN := lemma_14_2_11_normalizes hBor hB
  have hcomm := lemma_14_2_11_comm st hB
  have hSB : ∀ s ∈ sOf T K1, ∀ b ∈ B, ∃ b' ∈ B, ∃ s' ∈ sOf T K1, s * b = b' * s' := by
    intro s hs b hb
    have hmem : s * b ∈ (B : Set G) * (T : Set G) := by
      rw [hcomm]
      exact ⟨s, hs.1, b, hb, rfl⟩
    obtain ⟨b', hb', t', ht', hst0⟩ := hmem
    have hst : b' * t' = s * b := hst0
    refine ⟨b', hb', t', ⟨ht', ?_⟩, hst.symm⟩
    have hN : t' = b'⁻¹ * s * b :=
      calc t' = b'⁻¹ * (b' * t') := by group
        _ = b'⁻¹ * (s * b) := by rw [hst]
        _ = b'⁻¹ * s * b := by group
    rw [hN]
    exact (Subgroup.normalizer (K1 : Set G)).mul_mem
      ((Subgroup.normalizer (K1 : Set G)).mul_mem ((Subgroup.normalizer (K1 : Set G)).inv_mem
        (hBN hb')) hs.2) (hBN hb)
  ext z
  constructor
  · rintro ⟨b, hb, s, hs, rfl⟩
    obtain ⟨b', hb', s', hs', hy⟩ := hSB s⁻¹ ((sOf T K1).inv_mem hs) b⁻¹ (B.inv_mem hb)
    refine ⟨s'⁻¹, (sOf T K1).inv_mem hs', b'⁻¹, B.inv_mem hb', ?_⟩
    have := congrArg (fun w => w⁻¹) hy
    simpa [mul_inv_rev] using this.symm
  · rintro ⟨s, hs, b, hb, rfl⟩
    obtain ⟨b', hb', s', hs', hy⟩ := hSB s hs b hb
    exact ⟨b', hb', s', hs', hy.symm⟩

theorem lemma_14_2_11_le_centralizer (st : Setting1427 T M H K1) {B : Subgroup G}
    (hB : IsHallOdd B (M ⊓ oTwoUpper H)) : B ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro b hb
  have hHMc : H ≤ mcOf T := (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2
  have hbX : b ∈ M ⊓ oTwoUpper H := hB.1 hb
  have hbW : b ∈ M ⊓ mcOf T := ⟨hbX.1, hHMc (oTwoUpper_le H hbX.2)⟩
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    ((lemma_14_2_4 st.hyp st.facts).isTwoReducedIn).1.2.1
  have hDM : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :
      Set G) := le_normalizer_inf_centralizer hMV
  have hmmc := st.facts.mmc_eq
  have hbDR : b ∈ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (M ⊓ mcOf T) := by
    rw [← hmmc]
    exact hbW
  have hDW : (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      Subgroup.normalizer (pCoreOf 2 (M ⊓ mcOf T) : Set G) := by
    refine le_trans ?_ (le_normalizer_pCoreOf 2 (M ⊓ mcOf T))
    rw [hmmc]
    exact le_sup_left
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDW] at hbDR
  obtain ⟨c, hc, r, hr, hbcr⟩ := hbDR
  have hr2 : IsPGroup 2 (pCoreOf 2 (M ⊓ mcOf T)) := pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hr2 ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hrM : r ∈ M := ((pCoreOf_le 2 _) hr).1
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hc (hDM hrM) (2 ^ k)
  have hbk : b ^ 2 ^ k ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [← hbcr, hpow, hrk, mul_one]
    exact hx'
  have hodd : Odd (orderOf b) :=
    hB.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard B hb)
  have hcop : Nat.Coprime (2 ^ k) (orderOf b) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hz := A4.mem_zpowers_pow_of_coprime hcop
  exact ((Subgroup.zpowers_le.mpr hbk) hz).2

end S1421

end CFSG.Quasithin
