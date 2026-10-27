module

public import CFSG.Milestones.ASVolI.C61.HypMax

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.Quasithin.S152N

section General

variable {G : Type} [Group G]

theorem burnsideC56_blockU_le (A : Subgroup G) : blockU A ≤ A := by
  rw [blockU, Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ A := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 A ha
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha' hb) (A.inv_mem ha')) (A.inv_mem hb)

theorem burnsideC56_mem_pCore_iff {X : Subgroup G} (a : ↥X) :
    a ∈ CFSG.pCore 2 ↥X ↔ (a : G) ∈ pCoreOf 2 X := by
  constructor
  · intro h
    exact ⟨a, h, rfl⟩
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    rwa [← this]

theorem burnsideC56_alt3_moves :
    ∀ σ : alternatingGroup (Fin 3), σ ≠ 1 →
      ∃ i : Fin 3, (![1, 1, 0] : Fin 3 → ZMod 2) i ≠
        (![1, 1, 0] : Fin 3 → ZMod 2) (((σ : Equiv.Perm (Fin 3)))⁻¹ i) := by
  decide

@[expose] def burnsideC56_w110 : ↥(evenWeight 3) :=
  ⟨![1, 1, 0], by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    decide +kernel⟩

theorem burnsideC56_alt3_no_central {A : Subgroup G} (hA : IsAltType A 3) {z : G} (hzA : z ∈ A)
    (hzc : ∀ a ∈ A, a * z = z * a) (hz : orderOf z = 3) : False := by
  obtain ⟨α, -, hker, β, hβ, -, hβeq⟩ := hA
  have hσ : α ⟨z, hzA⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzA⟩ : ↥A) ∈ CFSG.pCore 2 ↥A := by
      rw [← hker]
      exact h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥A)) ⟨_, hmem⟩
    have hk' : (⟨z, hzA⟩ : ↥A) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf (⟨z, hzA⟩ : ↥A) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [Subgroup.orderOf_mk, hz] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd burnsideC56_w110)
  have huA : (u : G) ∈ A := burnsideC56_blockU_le A u.2
  have hconj : ((u : ↥(blockU A)) : G) =
      ((⟨z, hzA⟩ : ↥A) : G) * (u : G) * ((⟨z, hzA⟩ : ↥A) : G)⁻¹ := by
    have h1 := hzc (u : G) huA
    calc (u : G) = (u : G) * z * z⁻¹ := by group
      _ = z * (u : G) * z⁻¹ := by rw [h1]
  have h := hβeq ⟨z, hzA⟩ u u hconj
  rw [hu] at h
  obtain ⟨i, hi⟩ := burnsideC56_alt3_moves (α ⟨z, hzA⟩) hσ
  exact hi (h i)

theorem burnsideC56_comm_of_quot {K : Subgroup G} {X : Type} [Group X] (α : ↥K →* X)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hcomm : ∀ a b : ↥K, a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥K) : ∀ x y : X, x * y = y * x := by
  intro x y
  obtain ⟨a, rfl⟩ := hα x
  obtain ⟨b, rfl⟩ := hα y
  have h1 : α (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hcomm a b
  have e : a * b * a⁻¹ * b⁻¹ * (b * a) = a * b := by group
  calc α a * α b = α (a * b) := (map_mul α a b).symm
    _ = α (a * b * a⁻¹ * b⁻¹ * (b * a)) := by rw [e]
    _ = α (b * a) := by rw [map_mul, h1, one_mul]
    _ = α b * α a := map_mul α b a

theorem burnsideC56_alt5_nonabelian : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x := by
  decide

theorem burnsideC56_not_short_of_comm {L : Subgroup G}
    (hcomm : ∀ a b : ↥L, a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥L)
    (h3 : (CFSG.pCore 2 ↥L).index ≠ 3) : ¬ IsShort2 L := by
  intro hL
  have hQ : ∀ x y : ↥L ⧸ CFSG.pCore 2 ↥L, x * y = y * x :=
    burnsideC56_comm_of_quot (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) hcomm
  rcases hL.2.2.2.1 with hq | hc
  · obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hQ a' b']
  · exact h3 hc

theorem burnsideC56_simple_key {L P A B : Subgroup G} {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hYab : ∃ a b : Y, a * b ≠ b * a) (φ : ↥L →* Y) (hφ : Function.Surjective φ)
    (hker : φ.ker = P.subgroupOf L) (hAL : A ≤ L) (hBL : B ≤ L)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hA : ¬ A ≤ P) (hB : ¬ B ≤ P) : False := by
  set Ab : Subgroup Y := (A.subgroupOf L).map φ with hAb
  have hAn : Ab.Normal := by
    refine ⟨fun y hy g => ?_⟩
    obtain ⟨l, rfl⟩ := hφ g
    obtain ⟨a, ha, rfl⟩ := hy
    refine ⟨l * a * l⁻¹, ?_, by simp [map_mul, map_inv]⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hLA l.2) (a : G)).mp ha
    simpa using this
  have hAtop : Ab = ⊤ := by
    rcases hAn.eq_bot_or_eq_top with h | h
    · exfalso
      apply hA
      intro a haA
      have hmem : φ ⟨a, hAL haA⟩ ∈ Ab := ⟨⟨a, hAL haA⟩, haA, rfl⟩
      rw [h, Subgroup.mem_bot, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    · exact h
  apply hB
  intro b hbB
  have hcen : φ ⟨b, hBL hbB⟩ ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ Ab := hAtop ▸ Subgroup.mem_top y
    obtain ⟨a, ha, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have ha' : (a : G) ∈ A := ha
    exact (Subgroup.mem_centralizer_iff.mp (hAB ha') b hbB).symm
  have h1 := CFSG.GH74.GLS.IVK.Lifted.center_eq_one_of_simple_nonabelian hYab _ hcen
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at h1
  exact h1

end General

section Finite

variable {G : Type} [Group G] [Finite G]

theorem burnsideC56_three_key {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H)
    (h9 : ¬ 9 ∣ Nat.card H) (hAB : A ≤ Subgroup.centralizer (B : Set G)) (hA : IsAltType A 3)
    (hB3 : 3 ∣ Nat.card B) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (burnsideC56_three_dvd_of_alt3 hA)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 hB3
  have hao : orderOf (a : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  have hbo : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
  have hcomm : Commute (a : G) (b : G) := (Subgroup.mem_centralizer_iff.mp (hAB a.2) b b.2).symm
  set P₁ : Subgroup G := Subgroup.zpowers (a : G) with hP₁
  set P₂ : Subgroup G := Subgroup.zpowers (b : G) with hP₂
  have hP₁c : Nat.card P₁ = 3 := by rw [hP₁, Nat.card_zpowers, hao]
  have hP₂c : Nat.card P₂ = 3 := by rw [hP₂, Nat.card_zpowers, hbo]
  have hP₁3 : IsPGroup 3 P₁ := IsPGroup.of_card (n := 1) (by rw [hP₁c, pow_one])
  have hP₂3 : IsPGroup 3 P₂ := IsPGroup.of_card (n := 1) (by rw [hP₂c, pow_one])
  have hbN : (b : G) ∈ Subgroup.normalizer (P₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact (hcomm.zpow_left k).eq
  have hnorm : P₂ ≤ Subgroup.normalizer (P₁ : Set G) := Subgroup.zpowers_le.mpr hbN
  have hE : IsPGroup 3 (P₁ ⊔ P₂ : Subgroup G) := hP₁3.to_sup_of_normal_left' hP₂3 hnorm
  have hEH : P₁ ⊔ P₂ ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr (hAH a.2)) (Subgroup.zpowers_le.mpr (hBH b.2))
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hEH
  have hk1 : k ≤ 1 := by
    by_contra h
    exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hdvd)
  have h3E : 3 ∣ Nat.card ↥(P₁ ⊔ P₂) := hP₁c ▸ Subgroup.card_dvd_of_le le_sup_left
  have hcardE : Nat.card ↥(P₁ ⊔ P₂) = 3 := by
    rw [hk] at h3E ⊢
    interval_cases k
    · simp at h3E
    · rfl
  have hE2 : P₂ = P₁ ⊔ P₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardE, hP₂c])
  have haP₂ : (a : G) ∈ P₂ := hE2 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers (a : G))
  have haB : (a : G) ∈ B := Subgroup.zpowers_le.mpr b.2 haP₂
  exact burnsideC56_alt3_no_central hA a.2
    (fun a' ha' => (Subgroup.mem_centralizer_iff.mp (hAB ha') a haB).symm) hao

theorem burnsideC56_oTwoUpper_eq_of_s1 {H TH R K₁ : Subgroup G} (hcfg : BlockConfig H TH R K₁)
    (hs : ∀ t ∈ TH, conjByElt t K₁ = K₁) : oTwoUpper H = K₁ := by
  rw [hcfg.prod]
  apply le_antisymm
  · exact iSup₂_le fun t ht => (hs t ht).le
  · exact le_iSup₂_of_le (1 : G) TH.one_mem (by rw [C2Eleven.conjByElt_one])

theorem burnsideC56_not_nine_dvd {H : Subgroup G} {Y : Type} [Group Y] (ψ : ↥H →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H)
    (hY : Nat.card Y = 6) : ¬ 9 ∣ Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 ↥ψ.ker := by
    rw [hker]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_of_injective H.subtype
      H.subtype_injective
  obtain ⟨k, hk⟩ := hO.exists_card_eq
  have hcard : Nat.card ψ.ker * Nat.card Y = Nat.card ↥H :=
    Subgroup.card_ker_mul_card_of_surjective (f := ψ) hψ
  rw [← hcard, hk, hY]
  intro h9
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h9
  omega

theorem burnsideC56_W3_case {H : Subgroup G} {Y : Type} [Group Y] (ψ : ↥H →* Y)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (pCoreOf 2 H).subgroupOf H) (e : Y ≃* S3wrZ2) :
    (∀ x ∈ oTwoUpper H, ∀ y ∈ oTwoUpper H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
      (CFSG.pCore 2 ↥(oTwoUpper H)).index = 9 := by
  have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
  have hLH : oTwoUpper H ≤ H := oTwoUpper_le H
  have himg : ((oTwoUpper H).subgroupOf H).map ψ = oTwoUpper (⊤ : Subgroup Y) :=
    burnsideC56_map_oTwoUpper ψ hψ
  have hYW : (oTwoUpper (⊤ : Subgroup Y)).map e.toMonoidHom = W3.N0 := by
    rw [← oTwoUpper_map e.toMonoidHom ⊤, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
    exact burnsideC56_W3_oTwoUpper
  have hmem : ∀ x (hx : x ∈ oTwoUpper H), e (ψ ⟨x, hLH hx⟩) ∈ W3.N0 := by
    intro x hx
    rw [← hYW, ← himg]
    exact ⟨ψ ⟨x, hLH hx⟩, ⟨⟨x, hLH hx⟩, hx, rfl⟩, rfl⟩
  refine ⟨fun x hx y hy => ?_, ?_⟩
  · have hc := burnsideC56_W3_N0_comm _ _ (hmem x hx) (hmem y hy)
    have h1 : ψ (⟨x, hLH hx⟩ * ⟨y, hLH hy⟩ * ⟨x, hLH hx⟩⁻¹ * ⟨y, hLH hy⟩⁻¹) = 1 := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
        map_inv, hc, map_one]
      group
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · have hker' : (ψ.comp (Subgroup.inclusion hLH)).ker = CFSG.pCore 2 ↥(oTwoUpper H) := by
      rw [burnsideC56_ker_comp_inclusion hLH ψ hker,
        burnsideC56_subgroupOf_eq_pCore (burnsideC56_pCoreOf_oTwoUpper H)]
    rw [← hker', Subgroup.index_ker, ← MonoidHom.map_range, Subgroup.inclusion_range, himg,
      ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hYW, W3.card_N0]

theorem burnsideC56_hypI_blocks {H TH R K₁ : Subgroup G} (hc : CharTwo H)
    (hi : burnsideC56_HypI H) (hT : IsSylowTwoOf TH H) (hcfg : BlockConfig H TH R K₁) :
    ((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧ oTwoUpper H = K₁ ∧
        ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 5) ∧
        ¬ IsA3Product H (oTwoUpper H) 1 ∧ ¬ IsA3Product H (oTwoUpper H) 2) ∨
    ((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧ oTwoUpper H = K₁ ∧ IsAltType K₁ 3 ∧
        ¬ IsA3Product H (oTwoUpper H) 2) ∨
    ((∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧ IsAltType K₁ 3 ∧ ¬ IsBlock2 H (oTwoUpper H)) := by
  have hblk : IsBlock2 H K₁ := hcfg.chi0.1
  have hK₁H : K₁ ≤ H := hblk.2.1
  have hLH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁L : K₁ ≤ oTwoUpper H := by
    have := burnsideC5h_p1_conj_le hcfg TH.one_mem
    rwa [C2Eleven.conjByElt_one] at this
  have hLK₁ : oTwoUpper H ≤ Subgroup.normalizer (K₁ : Set G) := by
    have := burnsideC5h_p1_K_le_normalizer hcfg TH.one_mem
    rwa [C2Eleven.conjByElt_one] at this
  have hconjL : ∀ t ∈ TH, conjByElt t K₁ ≤ oTwoUpper H := fun t ht =>
    burnsideC5h_p1_conj_le hcfg ht
  have hcomm1 : ∀ t ∈ TH, conjByElt t K₁ ≠ K₁ →
      K₁ ≤ Subgroup.centralizer (conjByElt t K₁ : Set G) := by
    intro t ht hne
    have := hcfg.commute 1 TH.one_mem t ht (by rw [C2Eleven.conjByElt_one]; exact hne.symm)
    rwa [C2Eleven.conjByElt_one] at this
  have h3K₁ : 3 ∣ Nat.card K₁ := burnsideC5h_p1_three_dvd hcfg.chi0
  have h3t : ∀ t : G, 3 ∣ Nat.card (conjByElt t K₁) := fun t => by
    rw [burnsideC5h_p1_card_conjByElt]
    exact h3K₁
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  rcases hi with ⟨n, -, Y, _, φ, hφ, hker, hY⟩ | ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩ |
      ⟨Y, _, ψ, hψ, hker, ⟨e⟩⟩
  ·
    left
    have : IsSimpleGroup Y := burnsideC56_isPSL_simple hY
    have hYab := burnsideC56_isPSL_nonabelian hY
    have hs : ∀ t ∈ TH, conjByElt t K₁ = K₁ := by
      intro t ht
      by_contra hne
      exact burnsideC56_simple_key hYab φ hφ hker hK₁L (hconjL t ht) (hcomm1 t ht hne) hLK₁
        (burnsideC56_not_le_of_three_dvd hQ2 h3K₁)
        (burnsideC56_not_le_of_three_dvd hQ2 (h3t t))
    have hL := burnsideC56_oTwoUpper_eq_of_s1 hcfg hs
    have hidx : 60 ≤ (CFSG.pCore 2 ↥(oTwoUpper H)).index := by
      rw [burnsideC56_index_pCore_eq_card φ hφ (burnsideC56_ker_oTwoUpper φ hker)]
      exact (burnsideC56_isPSL_card hY).1
    have hnot3 : ¬ IsAltType (oTwoUpper H) 3 := fun h3 => by
      have := burnsideC56_index_of_alt h3
      rw [burnsideC56_card_alt_three] at this
      omega
    refine ⟨hs, hL, ?_, ?_, ?_⟩
    · rcases hcfg.chi0.2 with h | h | h
      · exact Or.inl h
      · exact absurd (by rw [hL]; exact h) hnot3
      · exact Or.inr h
    · rintro ⟨K', -, hK'3, ⟨-, hLK'⟩ | ⟨h12, -⟩⟩
      · exact hnot3 (hLK' ▸ hK'3)
      · omega
    · rintro ⟨K', -, hK'3, ⟨h21, -⟩ | ⟨-, K₂', -, -, hK₂'3, hcomm', hLeq⟩⟩
      · omega
      · have hK'L : K' ≤ oTwoUpper H := hLeq ▸ le_sup_left
        have hK₂'L : K₂' ≤ oTwoUpper H := hLeq ▸ le_sup_right
        have hLK' : oTwoUpper H ≤ Subgroup.normalizer (K' : Set G) := by
          rw [hLeq]
          exact sup_le Subgroup.le_normalizer
            ((Subgroup.le_centralizer_iff.mp hcomm').trans
              (Subgroup.centralizer_le_normalizer _))
        exact burnsideC56_simple_key hYab φ hφ hker hK'L hK₂'L hcomm' hLK'
          (burnsideC56_not_le_of_three_dvd hQ2 (burnsideC56_three_dvd_of_alt3 hK'3))
          (burnsideC56_not_le_of_three_dvd hQ2 (burnsideC56_three_dvd_of_alt3 hK₂'3))
  ·
    right
    left
    have : Finite Y := Finite.of_equiv _ e.toEquiv.symm
    have hY6 : Nat.card Y = 6 := by
      rw [Nat.card_congr e.toEquiv, burnsideC56_card_perm_three]
    have h9 : ¬ 9 ∣ Nat.card H := burnsideC56_not_nine_dvd ψ hψ hker hY6
    have hidx : (CFSG.pCore 2 ↥K₁).index ∣ 6 :=
      hY6 ▸ burnsideC56_index_pCore_dvd hK₁H ψ hker (burnsideC56_pCoreOf_block hblk)
    have hidx6 : (CFSG.pCore 2 ↥K₁).index ≤ 6 := Nat.le_of_dvd (by norm_num) hidx
    have h3 : IsAltType K₁ 3 := by
      rcases hcfg.chi0.2 with ⟨m, hm, h⟩ | h | h
      · have := burnsideC56_index_of_lin2 hm h
        omega
      · exact h
      · have := burnsideC56_index_of_alt h
        rw [burnsideC56_card_alt_five] at this
        omega
    have hs : ∀ t ∈ TH, conjByElt t K₁ = K₁ := by
      intro t ht
      by_contra hne
      exact burnsideC56_three_key hK₁H ((hconjL t ht).trans hLH) h9 (hcomm1 t ht hne) h3 (h3t t)
    refine ⟨hs, burnsideC56_oTwoUpper_eq_of_s1 hcfg hs, h3, ?_⟩
    rintro ⟨K', hK'blk, hK'3, ⟨h21, -⟩ | ⟨-, K₂', -, hK₂'blk, hK₂'3, hcomm', -⟩⟩
    · omega
    · exact burnsideC56_three_key hK'blk.2.1 hK₂'blk.2.1 h9 hcomm' hK'3
        (burnsideC56_three_dvd_of_alt3 hK₂'3)
  ·
    right
    right
    obtain ⟨hC, hidx9⟩ := burnsideC56_W3_case ψ hψ hker e
    have hLcomm : ∀ a b : ↥(oTwoUpper H), a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥(oTwoUpper H) := by
      intro a b
      rw [burnsideC56_mem_pCore_iff, burnsideC56_pCoreOf_oTwoUpper H]
      refine ⟨(a * b * a⁻¹ * b⁻¹).2, ?_⟩
      simpa using hC a a.2 b b.2
    have hnotblk : ¬ IsBlock2 H (oTwoUpper H) := fun hb =>
      burnsideC56_not_short_of_comm hLcomm (by rw [hidx9]; norm_num) hb.1
    have hK₁comm : ∀ a b : ↥K₁, a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥K₁ := by
      intro a b
      rw [burnsideC56_mem_pCore_iff, burnsideC56_pCoreOf_block hblk]
      refine ⟨(a * b * a⁻¹ * b⁻¹).2, ?_⟩
      simpa using hC a (hK₁L a.2) b (hK₁L b.2)
    have h3 : IsAltType K₁ 3 := by
      rcases hcfg.chi0.2 with ⟨m, -, F, _, _, -, α, hα, hker', -⟩ | h | ⟨α, hα, hker', -⟩
      · exfalso
        obtain ⟨x, y, hxy⟩ := burnsideC56_sl2_nonabelian F
        exact hxy (burnsideC56_comm_of_quot α hα hker' hK₁comm x y)
      · exact h
      · exfalso
        obtain ⟨x, y, hxy⟩ := burnsideC56_alt5_nonabelian
        exact hxy (burnsideC56_comm_of_quot α hα hker' hK₁comm x y)
    refine ⟨?_, h3, hnotblk⟩
    by_contra hne
    push Not at hne
    exact hnotblk (burnsideC56_oTwoUpper_eq_of_s1 hcfg hne ▸ hblk)

end Finite

end CFSG.ASVolI
