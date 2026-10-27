module

public import CFSG.RankThree.PartTwo.Sec11.Final1128
public import CFSG.RankThree.PartTwo.Sec11.Final1128ProofSylow
public import CFSG.RankThree.PartTwo.Sec11.Final1128ProofData
import CFSG.RankThree.PartTwo.Sec11.Final1128Item1129

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Final1128Proof

namespace Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g e : G}

theorem isSylowOf_top (h117 : Item117) (h : Data G A c L a R Y d x s r g e)
    (hC : IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer {e}) (Subgroup.centralizer {e})) :
    IsSylowOf 3 (sec11P R g) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₁, hc⟩ := h.exists_core h117
  set P := sec11P R g with hPdef
  set N := Subgroup.normalizer (P : Set G) with hNdef
  have hP3 : IsPGroup 3 P := h.toSec11Data.isPGroup_sec11P
  have hPN : P ≤ N := Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := N)).exists_le_sylow
  set S := (Q : Subgroup N).map N.subtype with hS
  have hPS : P ≤ S := fun y hy => ⟨⟨y, hPN hy⟩, hQ (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
  have hSN : S ≤ N := Subgroup.map_subtype_le _
  have hS3 : IsPGroup 3 S := Q.isPGroup'.map N.subtype
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := by
    intro y hy
    obtain ⟨k, hk⟩ := hS3 ⟨y, hy⟩
    have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hyN := hSN hy
    have hcen : ∀ z ∈ P, z * (y * d * y⁻¹) = (y * d * y⁻¹) * z := by
      intro z hz
      have hz' : y⁻¹ * z * y⁻¹⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) z).mp hz
      have h1 := hc.d_comm _ hz'
      calc z * (y * d * y⁻¹) = y * ((y⁻¹ * z * y⁻¹⁻¹) * d) * y⁻¹ := by group
        _ = y * (d * (y⁻¹ * z * y⁻¹⁻¹)) * y⁻¹ := by rw [h1]
        _ = (y * d * y⁻¹) * z := by group
    have hdyP : y * d * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hyN d).mp hc.d_mem
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec12.commute_of_conj_mem_zpowers hc.orderOf_d (hc.mem_zpowers_of_central hdyP hcen) hyk)
  have hSed : S ≤ Subgroup.normalizer ((Subgroup.closure {d, e} : Subgroup G) : Set G) := by
    intro y hy
    have h1 := Item1129Proof.mem_normalizer_commutator (hSN hy)
    rwa [h.commutator_eq', Set.pair_comm] at h1
  have hxP := h.x_mem_P
  have hxe : x * e ≠ e * x := fun hxe => h.x_e_ne (commutatorElement_eq_one_iff_mul_comm.mpr hxe)
  have hfr := exists_pow_inv_mul_mem_centralizer hS3 (hPS hxP)
    (h.mul_comm_A e h.e_mem d h.d_mem_A) (h.pow_three_A e h.e_mem) (h.pow_three_A d h.d_mem_A)
    h.e_not_mem_zpowers hSed hSd hxe
  have hCS : S ⊓ Subgroup.centralizer ({e} : Set G) = P ⊓ Subgroup.centralizer {e} :=
    hC.eq_of_le (inf_le_inf_right _ hPS) inf_le_right (hS3.to_le inf_le_left)
  have hSP : S ≤ P := by
    intro y hy
    obtain ⟨n, hn⟩ := hfr y hy
    have hz : (x ^ n)⁻¹ * y ∈ S ⊓ Subgroup.centralizer ({e} : Set G) :=
      ⟨S.mul_mem (S.inv_mem (S.pow_mem (hPS hxP) n)) hy, hn⟩
    rw [hCS] at hz
    have e1 : y = x ^ n * ((x ^ n)⁻¹ * y) := by group
    rw [e1]
    exact P.mul_mem (P.pow_mem hxP n) hz.1
  have hPS' : P = S := le_antisymm hPS hSP
  have hPsyl : IsSylowOf 3 P N := by
    rw [hPS']
    exact ⟨Q, rfl⟩
  exact Sec12.isSylowOf_of_normalizer_le hPsyl le_top inf_le_right

theorem eq_zpowers_d (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∀ K : Subgroup G, K ≤ sec11P R g → sec11P R g ≤ Subgroup.normalizer (K : Set G) →
      Nat.card K = 3 → K = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₁, hc⟩ := h.exists_core h117
  intro K hKP hPK hK3
  obtain ⟨k, hkK, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : K = ⊥ := (Subgroup.eq_bot_iff_forall K).mpr hall
    rw [hbot, Subgroup.card_bot] at hK3
    norm_num at hK3
  have hk3 : orderOf k = 3 := by
    have hdvd : orderOf k ∣ 3 := hK3 ▸ Subgroup.orderOf_dvd_natCard K hkK
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hk1
    · exact h3
  have hKk : K = Subgroup.zpowers k :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkK)
      (by rw [hK3, Nat.card_zpowers, hk3])).symm
  have hcent : ∀ y ∈ sec11P R g, y * k = k * y := by
    intro y hy
    obtain ⟨n, hn⟩ := h.toSec11Data.isPGroup_sec11P ⟨y, hy⟩
    have hyn : y ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hyk : y * k * y⁻¹ ∈ Subgroup.zpowers k := by
      rw [← hKk]
      exact (Subgroup.mem_normalizer_iff.mp (hPK hy) k).mp hkK
    exact Sec12.commute_of_conj_mem_zpowers hk3 hyk hyn
  have hkd := hc.mem_zpowers_of_central (hKP hkK) fun z hz => hcent z hz
  rw [hKk]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkd)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hc.orderOf_d, hk3])

theorem isEmpty_wreath (h117 : Item117) (h : Data G A c L a R Y d x s r g e) :
    ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33) := by
  set P := sec11P R g with hPdef
  have haP := h.A_le_P h.a_mem
  have hcP := h.A_le_P h.mem_A
  have hdP := h.A_le_P h.d_mem_A
  have hd := h.eq_zpowers_d h117
  set a' : P := ⟨a, haP⟩
  set c' : P := ⟨c, hcP⟩
  set d' : P := ⟨d, hdP⟩
  have hsub : ∀ y z : P, (y : G) * z = z * y → y * z = z * y := fun y z hyz => Subtype.ext hyz
  have hpow : ∀ y : P, (y : G) ^ 3 = 1 → y ^ 3 = 1 := fun y hy => Subtype.ext (by simpa using hy)
  refine isEmpty_quotient_wreath (a := a') (c := c') (d := d') (h.card_P h117) ?_ ?_ ?_
    (hsub a' c' (h.mul_comm_A a h.a_mem c h.mem_A))
    (hsub a' d' (h.mul_comm_A a h.a_mem d h.d_mem_A))
    (hsub c' d' (h.mul_comm_A c h.mem_A d h.d_mem_A)) (hpow a' (h.pow_three_A a h.a_mem))
    (hpow c' (h.pow_three_A c h.mem_A)) (hpow d' (h.pow_three_A d h.d_mem_A)) ?_
  · intro K hK hK3
    have hKP : K.map P.subtype ≤ P := Subgroup.map_subtype_le K
    have hPN : P ≤ Subgroup.normalizer ((K.map P.subtype : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨z', hz', rfl⟩
        exact ⟨⟨y, hy⟩ * z' * ⟨y, hy⟩⁻¹, hK.conj_mem z' hz' ⟨y, hy⟩, rfl⟩
      · rintro ⟨w, hw, hwz⟩
        have hw' : (w : G) = y * z * y⁻¹ := hwz
        have hzP : z ∈ P := by
          have e1 : z = y⁻¹ * (w : G) * y := by rw [hw']; group
          rw [e1]
          exact P.mul_mem (P.mul_mem (P.inv_mem hy) w.2) hy
        refine ⟨⟨z, hzP⟩, ?_, rfl⟩
        have e2 : (⟨z, hzP⟩ : P) = ⟨y, hy⟩⁻¹ * w * ⟨y, hy⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hw']
          group
        rw [e2]
        have := hK.conj_mem w hw ⟨y, hy⟩⁻¹
        simpa using this
    have hcard : Nat.card (K.map P.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective P.subtype_injective, hK3]
    have hKd := hd _ hKP hPN hcard
    apply Subgroup.map_injective P.subtype_injective
    rw [hKd, MonoidHom.map_zpowers]
    rfl
  · intro y
    rw [Sec12.mem_zpowers_subtype_iff]
    have := h.commutator_mem h117 y y.2 a h.a_mem
    rw [commutatorElement_def] at this
    simpa using this
  · intro y
    rw [Sec12.mem_zpowers_subtype_iff]
    have := h.commutator_mem h117 y y.2 c h.mem_A
    rw [commutatorElement_def] at this
    simpa using this
  ·
    rw [← Subgroup.card_map_of_injective P.subtype_injective, MonoidHom.map_closure]
    have hset : (P.subtype : P → G) '' {a', c', d'} = {c, a, d} := by
      ext z
      simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype,
        Set.mem_insert_iff, Set.mem_singleton_iff, a', c', d']
      tauto
    rw [hset, ← h.closure_eq, h.card_eq]

end Data

end Final1128Proof

theorem final1128_of (h117 : Item117) (hsyl : Sylow1129) : Final1128 := by
  intro G _ _ A c L a R Y d x s r g a' hdata hsc hrs hx9 ha'A ha'cd hPP hnf
  have h : Final1128Proof.Data G A c L a R Y d x s r g a' :=
    { hdata with
      zpowers_s_eq := hsc
      closure_eq_closure := hrs
      orderOf_x := hx9
      e_mem := ha'A
      e_not_mem := ha'cd
      commutator_eq' := hPP }
  obtain ⟨g₁, hc⟩ := h.exists_core h117
  have hS := h.isSylowOf_top h117
    (hsyl G A c L a R Y d x s r g a' hdata hsc hrs hx9 ha'A ha'cd hPP hnf)
  have hY := rank3II_11_31 hdata hS (h.isEmpty_wreath h117)
  have hind : ¬ 3 ∣ (sec11P R g).relIndex
      (Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G)) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
    intro h3
    apply h1
    rw [← Subgroup.relIndex_mul_relIndex (sec11P R g) _ ⊤ Subgroup.le_normalizer le_top]
    exact h3.mul_right _
  have hmem := Final1128Proof.mem_commutator_of_forall_conj hdata.isPGroup_sec11P hind hY
    (h.A_le_P hdata.mem_A) (h.pow_three_A c hdata.mem_A) fun n hn => by
      rw [hPP]
      exact hc.conj_mem hn
  rw [hPP] at hmem
  exact h.c_not_mem hmem

end CFSG.RankThree.PartTwo.Sec11
