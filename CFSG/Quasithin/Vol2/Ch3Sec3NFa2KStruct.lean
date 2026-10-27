module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2L2Gen

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)
open scoped MatrixGroups commutatorElement

theorem kstruct_lift {G : Type} [Group G] {K N : Subgroup G} (hN : IsPGroup 2 N)
    (hNK : ∀ u ∈ N, u ∈ Subgroup.normalizer (K : Set G)) {k p : G} (hk : k ∈ K)
    (hu : k⁻¹ * p ∈ N) (hp : p ^ 3 = 1) : p ∈ K := by
  obtain ⟨m, hm⟩ := hN ⟨k⁻¹ * p, hu⟩
  have hu' : (k⁻¹ * p) ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hpk : p = k * (k⁻¹ * p) := (mul_inv_cancel_left k p).symm
  set u := k⁻¹ * p with hudef
  have hconj : ∀ n : ℕ, u ^ n * k * (u ^ n)⁻¹ ∈ K := fun n =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hNK u hu) n) k).mp hk
  have key : ∀ n : ℕ, ∃ k' ∈ K, (k * u) ^ n = k' * u ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', he⟩ := ih
      refine ⟨k' * (u ^ n * k * (u ^ n)⁻¹), K.mul_mem hk' (hconj n), ?_⟩
      rw [pow_succ (k * u) n, he, pow_succ u n]
      group
  obtain ⟨k', hk'K, hke⟩ := key (2 ^ m)
  have hpK : p ^ 2 ^ m ∈ K := by
    rw [hpk, hke, hu', mul_one]
    exact hk'K
  have hcop : Nat.Coprime (2 ^ m) (orderOf p) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hp)
      (Nat.Coprime.pow_left m (by norm_num))
  exact (Subgroup.zpowers_le.mpr hpK) (A4.mem_zpowers_pow_of_coprime hcop)

open CFSG.Quasithin.EmptyFaithfulMultiple in
theorem mem_normalizer_of_conj_mem' {G : Type} [Group G] [Finite G] {H L : Subgroup G}
    (hL : L ∈ cComp H) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) {y : G} (hyL : y ∈ L)
    (hy3 : orderOf y = 3) {r : G} (hr : r ∈ H) {N : Subgroup G} (hN : IsPGroup 2 N)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hd : r * y * r⁻¹ * (y ^ ε)⁻¹ ∈ N) : r ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hrL
  set L' := L.map (MulAut.conj r).toMonoidHom with hL'def
  have hL' : L' ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj r) hL
    rwa [map_conj_eq_self_of_mem hr] at h1
  have hne : L ≠ L' := by
    intro h
    apply hrL
    rw [CFSG.Quasithin.EmptyFaithfulMultiple.mem_normalizer_iff_map_conj]
    exact h.symm
  have hcomm := L15420.commutator_le_pCoreOf_of_ne hL hL' hne hq hZ
  have hy'L' : r * y * r⁻¹ ∈ L' := ⟨y, hyL, rfl⟩
  have hy'N : r * y * r⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_cComp hL hL' hy'L'
  have h1 : L15420.quotConj L (r * y * r⁻¹) hy'N = 1 := by
    rw [L15420.quotConj_eq_one_iff]
    intro l hl
    have := Subgroup.commutator_mem_commutator hl hy'L'
    have h2 : ⁅l, r * y * r⁻¹⁆⁻¹ ∈ pCoreOf 2 L := Subgroup.inv_mem _ (hcomm this)
    simpa [commutatorElement_def, mul_assoc] using h2
  have hyε : (y ^ ε)⁻¹ ∈ L := L.inv_mem (L.zpow_mem hyL ε)
  set d := r * y * r⁻¹ * (y ^ ε)⁻¹ with hddef
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ hy'N (Subgroup.le_normalizer hyε)
  have h2 : L15420.quotConj L d hdN =
      MulAut.conj ((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [L15420.quotConj_congr hddef hdN (Subgroup.mul_mem _ hy'N (Subgroup.le_normalizer hyε)),
      L15420.quotConj_mul hy'N (Subgroup.le_normalizer hyε), h1, one_mul,
      L15420.quotConj_of_mem hyε]
  obtain ⟨k, hk⟩ := hN ⟨d, hd⟩
  have hdk : d ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : MulAut.conj (((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k) = 1 := by
    rw [map_pow, ← h2, ← L15420.quotConj_pow hdN]
    rw [L15420.quotConj_congr hdk (Subgroup.pow_mem _ hdN _) (Subgroup.one_mem _)]
    exact L15420.quotConj_one
  have h4 : (((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    set w := ((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k with hw
    have := congrArg (fun α => α x) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * w = (w * x * w⁻¹) * w := by rw [this]
      _ = w * x := by group
  rw [hZ, Subgroup.mem_bot, ← QuotientGroup.mk_pow, L15420.mk_eq_one_iff] at h4
  have h5 : y ^ 2 ^ k ∈ pCoreOf 2 L := by
    simp only [Subgroup.coe_pow] at h4
    rcases hε with rfl | rfl
    · simpa [inv_pow] using h4
    · simpa using h4
  have h6 : y ∈ pCoreOf 2 L :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mem_of_pow_mem_of_pow_mem
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h5
      (by rw [← hy3, pow_orderOf_eq_one]; exact Subgroup.one_mem _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨y, h6⟩
  have hym : y ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hdvd : 3 ∣ 2 ^ m := hy3 ▸ orderOf_dvd_of_pow_eq_one hym
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  omega

section Main

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

namespace A2Cfg

theorem kstruct_pre (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q) :
    ∃ t₀ ∈ T, t₀ ∉ Subgroup.normalizer (K : Set G) ∧
      K.map (MulAut.conj t₀).toMonoidHom ∈ cComp (H ⊔ D) ∧
      conjClosure K T = K ⊔ K.map (MulAut.conj t₀).toMonoidHom ∧
      (∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
        K.map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom) ∧
      (∀ u ∈ pCoreOf 2 (H ⊔ D), u ∈ Subgroup.normalizer (K : Set G)) ∧
      ∃ P3 : Subgroup G, P3 ≤ oTwoUpper H ∧ (∀ p ∈ P3, p ^ 3 = 1) ∧
        modO2Image (H ⊔ D) K ⊓ modO2Image (H ⊔ D) (K.map (MulAut.conj t₀).toMonoidHom) = ⊥ ∧
        (∀ a ∈ modO2Image (H ⊔ D) K,
          ∀ b ∈ modO2Image (H ⊔ D) (K.map (MulAut.conj t₀).toMonoidHom), a * b = b * a) ∧
        modO2Image (H ⊔ D) P3 ≤
          modO2Image (H ⊔ D) K ⊔ modO2Image (H ⊔ D) (K.map (MulAut.conj t₀).toMonoidHom) ∧
        Nat.card (modO2Image (H ⊔ D) P3) = 9 ∧
        (∀ z ∈ modO2Image (H ⊔ D) P3, z ^ 3 = 1) ∧
        Nonempty (↥(modO2Image (H ⊔ D) (K.map (MulAut.conj t₀).toMonoidHom)) ≃*
          PSL(2, ZMod q)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : Hyp331 G T M L D := c.nf.hyp
  obtain ⟨e⟩ := c.nf.wreath
  have hH : InH T H := c.nf.inH
  have hO : pCoreOf 2 (H ⊔ D) ≠ ⊥ := c.nf.O
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  have hYK : oTwoUpper H ≤ conjClosure K T := c.nf.YK
  have hTK : ¬ T ≤ Subgroup.normalizer (K : Set G) := c.nf.TK
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hOHT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ T := fun x hx =>
    hOHT (C1Pack12.pow_three_mem_pCoreOf φ hx)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set H₀ := H ⊔ D with hH₀
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKc hO
  have h38Q := h38 _ hQ
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥H₀, π x = 1 → (x : G) ∈ T := by
    intro x hx
    have h1 : x ∈ CFSG.Open.pCore 2 ↥H₀ := by
      exact (QuotientGroup.eq_one_iff x).mp hx
    exact pCoreOf_le_of_isSylowTwoOf hT₀ ⟨x, h1, rfl⟩
  set Ab := modO2Image H₀ K with hAb
  set Tb := modO2Image H₀ T with hTbdef
  have hAbc : Ab ∈ cComp (⊤ : Subgroup _) := modO2Image_mem_cComp hK
  have hTb : IsSylowTwoOf Tb ⊤ :=
    A312.isSylowTwoOf_top_map π hπs (isSylowTwoOf_top_subgroupOf hT₀)
  obtain ⟨-, hT38⟩ := h38Q Ab hAbc
  rcases hT38 Tb hTb with ⟨hnorm, -, -⟩ |
      ⟨tb, htb, htbn, hconjT, -, hcomm, hinf, -, -⟩
  ·
    exfalso
    apply hTK
    intro t ht
    have htH : t ∈ H₀ := hTH₀ ht
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩).trans ?_
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  set Ab' := Ab.map (MulAut.conj tb).toMonoidHom with hAb'
  have hcomm' : ∀ a ∈ Ab, ∀ b ∈ Ab', a * b = b * a := by
    intro a ha b hb
    have h1 : Ab ≤ Subgroup.centralizer (Ab' : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) b hb).symm
  obtain ⟨⟨t₀, ht₀H⟩, ht₀T, rfl⟩ := htb
  have ht₀T' : t₀ ∈ T := ht₀T
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H₀ := map_conj_mem_cComp hK ht₀H
  have hK'b : modO2Image H₀ K' = Ab' := modO2Image_conj ⟨t₀, ht₀H⟩
  have ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G) := by
    intro hN
    apply htbn
    have h1 : K' = K := by
      rw [hK']
      exact A38.map_conj_eq_iff.mpr hN
    have h3' : Ab.map (MulAut.conj (π ⟨t₀, ht₀H⟩)).toMonoidHom = Ab :=
      hK'b.symm.trans (congrArg (modO2Image H₀) h1)
    exact A38.map_conj_eq_iff.mp h3'
  have hs : ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
      K.map (MulAut.conj s).toMonoidHom = K' := by
    intro s hs
    have htH : s ∈ H₀ := hTH₀ hs
    have h1 : K.map (MulAut.conj s).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj s).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
      rw [modO2Image_conj (H := H₀) (L := K) ⟨s, htH⟩]
      exact ⟨π ⟨s, htH⟩, Lem3313B.mk_mem_img _ hs, rfl⟩
    rw [hconjT] at h2
    rcases h2 with h2 | h2
    · exact Or.inl (modO2Image_injOn H₀ h1 hK h2)
    · refine Or.inr (modO2Image_injOn H₀ h1 hK'c ?_)
      rw [Set.mem_singleton_iff, ← hK'b] at h2
      exact h2
  have hKK : conjClosure K T = K ⊔ K' := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (sup_le (le_conjClosure K T) ?_)
    · have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
      rcases hs t ht with h' | h'
      · rw [h'] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [h'] at hmem
        exact Subgroup.mem_sup_right hmem
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_conjClosure ht₀T' hk
  have hKKb : modO2Image H₀ (K ⊔ K') = Ab ⊔ Ab' := by
    rw [Lem3313B.img_sup (le_of_mem_cComp hK) (le_of_mem_cComp hK'c), hK'b]
  have hYbA : modO2Image H₀ (oTwoUpper H) ≤ Ab ⊔ Ab' := by
    rw [← hKKb]
    exact Lem3313B.img_mono (hYK.trans hKK.le)
  set Pb := modO2Image H₀ P3 with hPb
  have hPbY : Pb ≤ modO2Image H₀ (oTwoUpper H) := Lem3313B.img_mono hP3.1
  have hPb9 : Nat.card Pb = 9 := by
    rw [← hP3card]
    have hinj : Function.Injective (π.comp (P3.subgroupOf H₀).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ((x : ↥H₀) : G) ∈ T := hker _ hx
      have h2 : ((x : ↥H₀) : G) ∈ P3 := x.2
      have h3' : ((x : ↥H₀) : G) ∈ P3 ⊓ T := ⟨h2, h1⟩
      rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
        Subgroup.mem_bot] at h3'
      exact Subtype.ext (Subtype.ext h3')
    have h1 : Pb = (π.comp (P3.subgroupOf H₀).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      try rfl
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP3.1.trans (hYH.trans hHH₀))).toEquiv
  have hP3exp : ∀ p ∈ P3, p ^ 3 = 1 := by
    intro p hp
    have h1 : p ^ 3 ∈ P3 := P3.pow_mem hp 3
    have h2 : p ^ 3 ∈ T := hpow3 p (hP3.1 hp)
    have h3' : p ^ 3 ∈ P3 ⊓ T := ⟨h1, h2⟩
    rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
      Subgroup.mem_bot] at h3'
    exact h3'
  have hPexp : ∀ z ∈ Pb, z ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 :=
      Subtype.ext (by simpa using hP3exp _ (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  have hNK : ∀ u ∈ pCoreOf 2 H₀, u ∈ Subgroup.normalizer (K : Set G) := by
    intro u hu
    have huH : u ∈ H₀ := (CFSG.LieType.BorelTits.pCoreOf_le 2 H₀) hu
    have h1 : K.map (MulAut.conj u).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK huH
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) (⟨u, huH⟩ : ↥H₀) = 1 :=
      CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mk_eq_one_iff.mpr hu
    have h2 : modO2Image H₀ (K.map (MulAut.conj u).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨u, huH⟩).trans ?_
      rw [hmk]
      exact A38.map_conj_eq_iff.mpr (Subgroup.one_mem _)
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  have hPSL : Nonempty (↥(modO2Image H₀ K') ≃* PSL(2, ZMod q)) := by
    obtain ⟨e₁⟩ := modO2_mulEquiv hK
    obtain ⟨e₂⟩ := nonempty_mulEquiv_psl_zmod c.q_prime c.model
    rw [hK'b]
    exact ⟨(Subgroup.equivMapOfInjective Ab (MulAut.conj (π ⟨t₀, ht₀H⟩)).toMonoidHom
      (MulAut.conj (π ⟨t₀, ht₀H⟩)).injective).symm.trans (e₁.symm.trans e₂)⟩
  have hi : modO2Image H₀ K ⊓ modO2Image H₀ K' = ⊥ := by
    rw [hK'b]
    exact hinf
  have hc : ∀ a ∈ modO2Image H₀ K, ∀ b ∈ modO2Image H₀ K', a * b = b * a := by
    intro a ha b hb
    rw [hK'b] at hb
    exact hcomm' a ha b hb
  have hPY : modO2Image H₀ P3 ≤ modO2Image H₀ K ⊔ modO2Image H₀ K' := by
    rw [hK'b]
    exact hPbY.trans hYbA
  exact ⟨t₀, ht₀T', ht₀N, hK'c, hKK, hs, hNK, P3, hP3.1, hP3exp, hi, hc, hPY, hPb9, hPexp,
    hPSL⟩

theorem kstruct (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q) :
    ∃ t₀ ∈ T, t₀ ∉ Subgroup.normalizer (K : Set G) ∧
      K.map (MulAut.conj t₀).toMonoidHom ∈ cComp (H ⊔ D) ∧
      conjClosure K T = K ⊔ K.map (MulAut.conj t₀).toMonoidHom ∧
      ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
        K.map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom := by
  obtain ⟨t₀, ht₀T, ht₀N, hK', hKK, hs, -⟩ := c.kstruct_pre h37 h38
  exact ⟨t₀, ht₀T, ht₀N, hK', hKK, hs⟩

theorem exists_x (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) : ∃ x : G, x ∈ oTwoUpper H ∧ x ∈ K ∧ orderOf x = 3 := by
  obtain ⟨t₀, -, -, -, -, -, hNK, P3, hP3Y, hP3exp, hi, hc, hPY, hPc, hPexp, ⟨e⟩⟩ :=
    c.kstruct_pre h37 h38
  have hq : q.Prime := c.q_prime
  have hq5 : 5 ≤ q := by
    have := c.q_mod
    have := hq.two_le
    omega
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hF : Nat.card (ZMod q) = q := Nat.card_zmod q
  have hcyc : ∀ X : Subgroup ↥(modO2Image (H ⊔ D) (K.map (MulAut.conj t₀).toMonoidHom)),
      IsPGroup 3 X → IsCyclic X :=
    fun X hX => L2q.isCyclic_three e hF hq hq5 X hX
  obtain ⟨⟨z, hzmem⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (L2qC.inf_ne_bot hc hi hPY hPc hPexp hcyc)
  obtain ⟨hzP, hzA⟩ := Subgroup.mem_inf.mp hzmem
  obtain ⟨y, hyP, hyz⟩ := hzP
  obtain ⟨k, hkK, hkz⟩ := hzA
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hyP' : (y : G) ∈ P3 := Subgroup.mem_subgroupOf.mp hyP
  have hkK' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hπ1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) (k⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hyz, hkz, inv_mul_cancel]
  have hu : (k : G)⁻¹ * (y : G) ∈ pCoreOf 2 (H ⊔ D) := by
    have h1 : ((k⁻¹ * y : ↥(H ⊔ D)) : G) ∈ pCoreOf 2 (H ⊔ D) :=
      CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mk_eq_one_iff.mp hπ1
    simpa using h1
  have hyK : (y : G) ∈ K :=
    kstruct_lift (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊔ D)) hNK hkK' hu
      (hP3exp _ hyP')
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have hy1' : y = 1 := Subtype.ext h
    apply hz1'
    rw [← hyz, hy1', map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨(y : G), hP3Y hyP', hyK, orderOf_eq_prime (hP3exp _ hyP') hy1⟩

theorem pCoreOf_K_le_R (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q) :
    pCoreOf 2 K ≤ pCoreOf 2 H := by
  obtain ⟨t₀, -, -, hK', hKK, -⟩ := c.kstruct h37 h38
  have hK'N : K.map (MulAut.conj t₀).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_cComp c.nf.K_comp hK'
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (conjClosure K T) := by
    rw [hKK]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hK'N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  exact h1.trans ((c.N0_le_TC).trans c.TC_le_R)

theorem R_le_normalizer_K (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q) :
    pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    have hq5 : 5 ≤ q := by
      have := c.q_mod
      have := c.q_prime.two_le
      omega
    haveI : Fact q.Prime := ⟨c.q_prime⟩
    haveI : NeZero q := ⟨c.q_prime.ne_zero⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod c.q_prime c.model
    have hcen : Subgroup.center (PSL(2, ZMod q)) = ⊥ :=
      L2q.center_eq_bot (Nat.card_zmod q) c.q_prime hq5
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hc : e x ∈ Subgroup.center (PSL(2, ZMod q)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hx y]
    rw [hcen, Subgroup.mem_bot] at hc
    exact e.injective (by rw [hc, map_one])
  intro r hr
  have hrH : r ∈ H ⊔ D := Subgroup.mem_sup_left ((CFSG.LieType.BorelTits.pCoreOf_le 2 H) hr)
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (oTwoUpper_le H hxY)
  have hd : r * x * r⁻¹ * (x ^ (1 : ℤ))⁻¹ ∈ pCoreOf 2 H := by
    rw [zpow_one]
    have h1 : x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp hxR r⁻¹).mp (Subgroup.inv_mem _ hr)
    have e : r * x * r⁻¹ * x⁻¹ = r * (x * r⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hr h1
  exact mem_normalizer_of_conj_mem' c.nf.K_comp c.nf.Kq hZ hxK hx3 hrH
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) (ε := 1) (Or.inl rfl) hd

end A2Cfg

end Main

end CFSG.Quasithin.H13.NFa2
