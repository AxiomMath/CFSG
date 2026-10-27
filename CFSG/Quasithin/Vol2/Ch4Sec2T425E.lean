module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425U
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212B

public section

namespace CFSG.Quasithin.H13.Ch4.T425

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_iSup₂ {K : Subgroup G} (S : Finset (Subgroup G))
    (h : ∀ A ∈ S, K ≤ Subgroup.normalizer (A : Set G)) :
    K ≤ Subgroup.normalizer ((⨆ A ∈ S, A : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun A => iSup_congr fun hA =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h A hA hg)

omit [Finite G] in
theorem card_sup_eq {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) = B.relIndex A * Nat.card B := by
  have hrel : B.relIndex (A ⊔ B) = B.relIndex A := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer h
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_right, hrel] at h1
  exact h1.symm

omit [Finite G] in
theorem not_dvd_card_iSup₂ {p : ℕ} (hp : p.Prime) (S : Finset (Subgroup G))
    (hS : ∀ A ∈ S, ¬ p ∣ Nat.card A)
    (hN : ∀ A ∈ S, ∀ B ∈ S, A ≤ Subgroup.normalizer (B : Set G)) :
    ¬ p ∣ Nat.card ↥(⨆ A ∈ S, A) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iSup_of_empty, iSup_bot, Subgroup.card_bot]
    exact hp.not_dvd_one
  | insert a S ha ih =>
    rw [Finset.iSup_insert]
    have hX := ih (fun A hA => hS A (Finset.mem_insert_of_mem hA))
      (fun A hA B hB => hN A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB))
    have haN : a ≤ Subgroup.normalizer ((⨆ A ∈ S, A : Subgroup G) : Set G) :=
      le_normalizer_iSup₂ S fun B hB =>
        hN a (Finset.mem_insert_self a S) B (Finset.mem_insert_of_mem hB)
    rw [card_sup_eq haN]
    have hidx : (⨆ A ∈ S, A).relIndex a ∣ Nat.card a := by
      have h1 := Subgroup.relIndex_mul_card (⨆ A ∈ S, A) a
      exact ⟨_, h1.symm⟩
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hS a (Finset.mem_insert_self a S) (h.trans hidx)
    · exact hX h

omit [Finite G] in
theorem mem_of_pow_eq_one {p : ℕ} (hp : p.Prime) {Y W : Subgroup G}
    (hWY : W ≤ Subgroup.normalizer (Y : Set G)) (hW : ¬ p ∣ Nat.card W) {y : G}
    (hy : y ∈ W ⊔ Y) {k : ℕ} (hyk : y ^ p ^ k = 1) : y ∈ Y := by
  set Z := W ⊔ Y with hZ
  have hYZ : Y ≤ Z := le_sup_right
  have hZN : Z ≤ Subgroup.normalizer (Y : Set G) := sup_le hWY Subgroup.le_normalizer
  have hYn : (Y.subgroupOf Z).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYZ).mpr hZN
  have hidx : (Y.subgroupOf Z).index = Y.relIndex W := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hWY
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hWY
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient W Y hWY).toEquiv.symm
  have hdvd : Y.relIndex W ∣ Nat.card W := ⟨_, (Subgroup.relIndex_mul_card Y W).symm⟩
  set n := (Y.subgroupOf Z).index with hn
  have hcop : Nat.Coprime n (p ^ k) := by
    refine Nat.Coprime.pow_right k ((Nat.coprime_comm.mp ?_))
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hW ?_
    rw [hidx] at h
    exact h.trans hdvd
  set y' : ↥Z := ⟨y, hy⟩ with hy'
  have h1 : y' ^ n ∈ Y.subgroupOf Z := Subgroup.pow_index_mem _ y'
  have hy'k : y' ^ p ^ k = 1 := Subtype.ext (by simpa using hyk)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : y = 1 := by simpa using hyk
    rw [this]
    exact Y.one_mem
  have hpk : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hpk
  have h2 : (y' ^ n) ^ m = y' := by
    rw [← pow_mul, pow_eq_pow_mod (n * m) hy'k, hm, pow_one]
  have h3 : y' ∈ Y.subgroupOf Z := h2 ▸ Subgroup.pow_mem _ h1 m
  exact h3

theorem eq_of_dvd_of_pRank_le_one (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {C K₁ K₂ : Subgroup G}
    (hC : pCoreOf 2 C ≠ ⊥) {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p C ≤ 1) (h₁ : K₁ ∈ cComp C) (h₂ : K₂ ∈ cComp C)
    (hp₁ : p ∣ Nat.card K₁) (hp₂ : p ∣ Nat.card K₂) : K₁ = K₂ := by
  by_contra hne
  have h12 : ⁅K₁, K₂⁆ ≤ pCoreOf 2 K₂ :=
    (lemma_1_2_1_two hK hs hnab h37 hC h₁ h₂ hne).1.trans inf_le_right
  obtain ⟨x, hxK, hxo, -, -⟩ := exists_noncentral hp2 (perfect_of_mem_cComp h₁) hp₁
    (X := ⊥) IsPGroup.of_bot bot_le fun y hy l _ => by
      rw [Subgroup.mem_bot.mp hy]
      simp
  have hx1 : x ∉ (⊥ : Subgroup G) := fun h => by
    rw [Subgroup.mem_bot] at h
    rw [h, orderOf_one] at hxo
    exact hpf.out.one_lt.ne hxo
  obtain ⟨hE, hEc⟩ := exists_elemAbelian_sup_zpowers (CFSG.SectionRank.isElemAbelian_bot p) hxo
    (fun e he => by rw [Subgroup.mem_bot.mp he]; exact Commute.one_left x) hx1
  have hEK₁ : (⊥ : Subgroup G) ⊔ Subgroup.zpowers x ≤ K₁ :=
    sup_le bot_le (Subgroup.zpowers_le.mpr hxK)
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (h12.trans (pCoreOf_le 2 K₂))
  have h2 := succ_le_pRank hp2 (perfect_of_mem_cComp h₂) hp₂ hE (k := 1)
    (by rw [hEc, Subgroup.card_bot, one_mul, pow_one]) (hEK₁.trans hK₁N)
    (fun y hy k hk => by
      have := Subgroup.commutator_mem_commutator (hEK₁ hy) hk
      rw [commutatorElement_def] at this
      exact h12 this)
    (hEK₁.trans (le_of_mem_cComp h₁)) (le_of_mem_cComp h₂)
  omega

theorem le_of_noncentral_mem {J Y : Subgroup G} (hJp : ⁅J, J⁆ = J)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hJY : J ≤ Subgroup.normalizer (Y : Set G))
    {z : G} (hzJ : z ∈ J) (hzY : z ∈ Y) {l : G} (hl : l ∈ J)
    (hzl : z * l * z⁻¹ * l⁻¹ ∉ pCoreOf 2 J) : J ≤ Y := by
  set N := J ⊓ Y with hNdef
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hJY hx⟩
  have hNn : (N.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hJN
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hπ
  have hN'n : ((N.subgroupOf J).map π).Normal :=
    Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  rcases A3.eq_top_or_le_center_of_subnormal hJq hN'n.isSubnormal with htop | hcen
  · have hcov : J ≤ pCoreOf 2 J ⊔ N := by
      intro j hj
      obtain ⟨n, hn, hnj⟩ : π ⟨j, hj⟩ ∈ (N.subgroupOf J).map π := htop ▸ Subgroup.mem_top _
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnj
      have hq : (((n⁻¹ * ⟨j, hj⟩ : ↥J)) : G) ∈ pCoreOf 2 J := C2Six.mem_pCore_two_iff.mp hnj
      have e : j = (n : G) * (((n⁻¹ * ⟨j, hj⟩ : ↥J)) : G) := by simp
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn) hq
    have hsolv : Group.IsSolvable ↥(pCoreOf 2 J) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(pCoreOf 2 J) := (pCoreOf_isPGroup 2 J).isNilpotent
      infer_instance
    have hcore : perfectCore (pCoreOf 2 J) ≤ N := by
      rw [(isSolvable_iff_perfectCore_eq_bot _).mp hsolv]
      exact bot_le
    exact (L4212.le_of_perfect_of_le_sup hJp inf_le_left hJN (pCoreOf_le 2 J) hcov hcore).trans
      inf_le_right
  · exfalso
    have hzc : π ⟨z, hzJ⟩ ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) :=
      hcen ⟨⟨z, hzJ⟩, Subgroup.mem_subgroupOf.mpr ⟨hzJ, hzY⟩, rfl⟩
    apply hzl
    have h1 := Subgroup.mem_center_iff.mp hzc (π ⟨l, hl⟩)
    have h2 : π (⟨z, hzJ⟩ * ⟨l, hl⟩ * ⟨z, hzJ⟩⁻¹ * ⟨l, hl⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact C2Six.mem_pCore_two_iff.mp h2

end CFSG.Quasithin.H13.Ch4.T425
