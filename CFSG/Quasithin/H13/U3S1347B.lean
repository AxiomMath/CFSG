module

public import CFSG.Quasithin.H13.U3S1347A
public import CFSG.Quasithin.H13.NQS13410C

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem pow_three_of_relIndex_three {H : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (h3 : T.relIndex H = 3) {x : G} (hx : x ∈ H) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) :
    x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hcard : Nat.card H = 3 * 2 ^ n := by
    have h1 := relIndex_mul_card T H
    rw [inf_eq_left.2 hTH, h3, hn] at h1
    exact h1.symm
  have hdvd : orderOf x ∣ 3 * 2 ^ n := by
    rw [← hcard, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hodd : Odd (orderOf x) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hxm)
  have hco : Nat.Coprime (orderOf x) (2 ^ n) := Nat.Coprime.pow_right n
    (Nat.coprime_two_right.2 hodd)
  exact orderOf_dvd_iff_pow_eq_one.1 (hco.dvd_of_dvd_mul_right hdvd)

theorem oTwoRes_le_oThreePrimeResidual {H X : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (h3 : T.relIndex H = 3) (hX : oTwoRes H ≤ X) : oTwoRes H ≤ oThreePrimeResidual X := by
  refine (closure_le _).2 fun x hx => subset_closure ⟨hX (subset_closure hx), 1, ?_⟩
  obtain ⟨hxH, m, hm, hxm⟩ := hx
  rw [pow_one]
  exact pow_three_of_relIndex_three hT hTH h3 hxH hm hxm

theorem cZ_eq_cZ_oTwoRes {H : Subgroup G} (hTsyl : IsSylowTwoOf T H) :
    cZ T H = cZ T (oTwoRes H) := by
  refine le_antisymm (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2
    (oTwoRes_le H)))) fun x hx => ?_
  obtain ⟨hxZ, hxK⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨hxZ, ?_⟩
  have hle : oTwoRes H ⊔ T ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun k hk => mem_centralizer_singleton_iff.2 ?_)
      (fun t ht => mem_centralizer_singleton_iff.2 ?_)
    · exact mem_centralizer_iff.1 hxK k hk
    · exact mem_centralizer_iff.1 (s134_Z_le_center T hxZ).2 t ht
  exact mem_centralizer_iff.2 fun h hh =>
    mem_centralizer_singleton_iff.1 (hle (le_oTwoRes_sup_of_isSylowTwoOf hTsyl hh))

theorem s1347_le_of_cZ_eq (S : A6.Setting134 G T L V) {Hi Hj X : Subgroup G} (hi : T ≤ Hi)
    (hj : T ≤ Hj) (h3i : T.relIndex Hi = 3) (hiX : Hi ≤ X)
    (hK : oTwoRes Hj = oThreePrimeResidual (X ⊓ centralizer (cZ T (oTwoRes Hj) : Set G)))
    (he : cZ T (oTwoRes Hi) = cZ T (oTwoRes Hj)) : Hi ≤ Hj := by
  have hKi : oTwoRes Hi ≤ oTwoRes Hj := by
    rw [hK]
    refine oTwoRes_le_oThreePrimeResidual S.h13.sylow.1 hi h3i
      (le_inf ((oTwoRes_le _).trans hiX) ?_)
    rw [← he]
    exact fun k hk => mem_centralizer_iff.2 fun z hz =>
      (mem_centralizer_iff.1 (mem_inf.1 hz).2 k hk).symm
  exact (le_oTwoRes_sup_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hi)).trans
    (sup_le (hKi.trans (oTwoRes_le _)) hj)

theorem s1347_false_of_cZ_eq (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (he : cZ T (oTwoRes H₁) = cZ T (oTwoRes H₂)) : False := by
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hne : ∀ {Hi Hj : Subgroup G}, T ≤ Hi → T.relIndex Hi = 3 → T.relIndex Hj = 3 →
      Hi ≤ Hj → Hi = Hj := fun hTi h3i h3j hle => by
    rcases eq_or_eq_of_relIndex_three h3j hTi hle with e | e
    · rw [e, relIndex_self] at h3i
      omega
    · exact e
  rcases (h.cent hH₀).2 with hK | hK
  · exact h.ne (hne h.inH₂.1 h3₂ h3₁
      (s1347_le_of_cZ_eq S h.inH₂.1 h.inH₁.1 h3₂ le_sup_right hK he.symm)).symm
  · exact h.ne (hne h.inH₁.1 h3₁ h3₂
      (s1347_le_of_cZ_eq S h.inH₁.1 h.inH₂.1 h3₁ le_sup_left hK he))

theorem s134_exists_HM (h135 : A6.Stmt13_3_5) (S : A6.Setting134 G T L V) :
    ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzL, hCz⟩ := (h135 G T L V S.h13 S.irr).2.2 (s134_isA6On S)
  obtain ⟨-, hzT, hz2⟩ := mem_quasithinOmegaOneCenter_iff.1 (mem_inf.1 hz).2
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  refine ⟨_, ⟨fun t ht => mem_centralizer_singleton_iff.2 ?_, fun hO => hz1 ?_⟩, hCz⟩
  · exact mem_centralizer_iff.1 hzT t ht
  · have hle : zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
      refine le_pCoreOf_of_le_normalizer (zpowers_le.2 hzC) (fun y hy => ?_) ?_
      · refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
        exact (Commute.zpow_left (mem_centralizer_singleton_iff.1 hy).symm k).eq
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hz2 hz1)
    rw [hO, le_bot_iff, zpowers_eq_bot] at hle
    exact hle

theorem s1347_not_le_M (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) := by
  intro hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := s1347_inH hedge S h
  have hZ := s134_card_Z h1332 hC58 h317 h56 S (s134_exists_HM h135 S)
  have key : ∀ {H : Subgroup G}, H ≤ H₁ ⊔ H₂ → T ≤ H → T.relIndex H = 3 →
      Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H) →
      cZ T (oTwoRes H) = quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) := by
    intro H hH hTH h3 hidx
    have hKL : oTwoRes H ≤ L := (closure_le _).2 fun x hx => by
      obtain ⟨hxH, m, hm, hxm⟩ := hx
      have hx3 := pow_three_of_relIndex_three S.h13.sylow.1 hTH h3 hxH hm hxm
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · exact NQS134.mem_L_of_orderOf_three h1332 h1228 S (hM (hH hxH))
          (orderOf_eq_prime hx3 hx1)
    have hle : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ≤ cZ T (oTwoRes H) :=
      inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hKL))
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow hTH)]
    omega
  exact s1347_false_of_cZ_eq S h hH₀
    ((key le_sup_left h.inH₁.1 (s1347_relIndex_three S h.inH₁.1 h.s3₁) h.index₁).trans
      (key le_sup_right h.inH₂.1 (s1347_relIndex_three S h.inH₂.1 h.s3₂) h.index₂).symm)

theorem sup_eq_and_inf_eq_bot_of_card {A B Z : Subgroup G} (hA : A ≤ Z) (hB : B ≤ Z)
    (hZ : Nat.card Z = 4) (hA2 : Nat.card A = 2) (hB2 : Nat.card B = 2) (hne : A ≠ B) :
    A ⊔ B = Z ∧ A ⊓ B = ⊥ := by
  constructor
  · have hdvd := card_dvd_of_le (sup_le hA hB)
    have h2 : 2 ∣ Nat.card ↥(A ⊔ B) := hA2 ▸ card_dvd_of_le le_sup_left
    rw [hZ] at hdvd
    have hc : Nat.card ↥(A ⊔ B) = 2 ∨ Nat.card ↥(A ⊔ B) = 4 := by
      have h4 : Nat.card ↥(A ⊔ B) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have h0 : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
      interval_cases h : Nat.card ↥(A ⊔ B) <;> simp_all
    rcases hc with hc | hc
    · exfalso
      have e1 : A = A ⊔ B := eq_of_le_of_card_ge le_sup_left (by omega)
      have e2 : B = A ⊔ B := eq_of_le_of_card_ge le_sup_right (by omega)
      exact hne (e1.trans e2.symm)
    · exact eq_of_le_of_card_ge (sup_le hA hB) (by omega)
  · have hdvd := card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
    rw [hA2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact card_eq_one.1 h1
    · exfalso
      have e1 : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by omega)
      have e2 : A ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by omega)
      exact hne (e1.symm.trans e2)

theorem s134_inf_cZ_eq_bot (S : A6.Setting134 G T L V) {H : Subgroup G}
    (hHM : ¬ H ≤ normalizer (L : Set G)) :
    quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ cZ T H = ⊥ := by
  by_contra hne
  apply hHM
  have hle : quasithinOmegaOneCenter T ⊓ centralizer (L : Set G) ⊓ cZ T H ≤
      quasithinOmegaOneCenter T := inf_le_left.trans inf_le_left
  refine le_trans ?_ (normalizer_le_of_isUniqueM S.uniqueM
    (S.h13.sylow.1.to_le fun x hx => (s134_Z_le_center T (hle hx)).1) hne
    (sup_le ?_ fun t ht => ?_))
  · exact (le_centralizer_iff.mp (inf_le_right.trans inf_le_right)).trans
      (centralizer_le_normalizer _)
  · exact (le_centralizer_iff.mp (inf_le_left.trans inf_le_right)).trans
      (centralizer_le_normalizer _)
  · refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
    exact (mem_centralizer_iff.1 (s134_Z_le_center T (hle hx)).2 t ht).symm

theorem s134_card_cZ_le (S : A6.Setting134 G T L V) {H : Subgroup G}
    (hHM : ¬ H ≤ normalizer (L : Set G))
    (hZ : Nat.card ↥(quasithinOmegaOneCenter T) =
      2 * Nat.card ↥(quasithinOmegaOneCenter T ⊓ centralizer (L : Set G))) :
    Nat.card ↥(cZ T H) ≤ 2 := by
  have h2 : (quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)).relIndex
      (quasithinOmegaOneCenter T) = 2 := by
    have h1 := relIndex_mul_card (quasithinOmegaOneCenter T ⊓ centralizer (L : Set G))
      (quasithinOmegaOneCenter T)
    rw [inf_eq_left.2 inf_le_left, hZ] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have h1 : (quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)).relIndex (cZ T H) ≤
      (quasithinOmegaOneCenter T ⊓ centralizer (L : Set G)).relIndex
        (quasithinOmegaOneCenter T) :=
    relIndex_le_of_le_right inf_le_left (by omega)
  rwa [← inf_relIndex_right, s134_inf_cZ_eq_bot S hHM, relIndex_bot_left, h2] at h1

theorem s1347_one_first (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) :
    InH T (H₁ ⊔ H₂) ∧ ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G) ∧
      quasithinOmegaOneCenter T = fsuV1 T V ∧
      cZ T H₁ ⊔ cZ T H₂ = quasithinOmegaOneCenter T ∧ cZ T H₁ ⊓ cZ T H₂ = ⊥ ∧
      Nat.card ↥(cZ T H₁) = 2 ∧ Nat.card ↥(cZ T H₂) = 2 := by
  have hH₀ := s1347_inH hedge S h
  have hH₀M := s1347_not_le_M hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hZ := s134_card_Z h1332 hC58 h317 h56 S ⟨_, hH₀, hH₀M⟩
  obtain ⟨H, hH, hHM⟩ : ∃ H, (H = H₁ ∨ H = H₂) ∧ ¬ H ≤ normalizer (L : Set G) := by
    by_contra hc
    push Not at hc
    exact hH₀M (sup_le (hc H₁ (Or.inl rfl)) (hc H₂ (Or.inr rfl)))
  have hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H) := by
    rcases hH with rfl | rfl
    exacts [h.index₁, h.index₂]
  have hle2 := s134_card_cZ_le S hHM hZ
  have hZV := card_le_of_le (A6.Setting134.ZV_le_ZL S)
  rw [S.card_ZV] at hZV
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by omega
  have hc₁ : Nat.card ↥(cZ T H₁) = 2 := by
    have := h.index₁
    omega
  have hc₂ : Nat.card ↥(cZ T H₂) = 2 := by
    have := h.index₂
    omega
  have hne : cZ T H₁ ≠ cZ T H₂ := fun e => s1347_false_of_cZ_eq S h hH₀ (by
    rw [← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1),
      ← cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1), e])
  obtain ⟨hsup, hinf⟩ :=
    sup_eq_and_inf_eq_bot_of_card inf_le_left inf_le_left hZ4 hc₁ hc₂ hne
  have hV1 : fsuV1 T V = quasithinOmegaOneCenter T :=
    eq_of_le_of_card_ge inf_le_right (by rw [S.card_V1]; omega)
  exact ⟨hH₀, hH₀M, hV1.symm, hsup, hinf, hc₁, hc₂⟩

end CFSG.Quasithin.H13.U3
