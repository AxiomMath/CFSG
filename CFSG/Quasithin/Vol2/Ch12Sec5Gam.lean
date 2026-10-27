module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.S1421QA15N1
public import CFSG.Quasithin.Vol2.Ch12Sec5K1List
public import CFSG.Quasithin.Vol2.Ch12Sec5KG

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Gam

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem not_sup_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G} (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)))
    (hLK : li L F.V1 < K₁) : ¬ K₁ ⊔ T ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  have hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G) := le_of_mem_cComp hK
  have hKN : K₁ ≤ Subgroup.normalizer (li L F.V1 : Set G) :=
    S125K6.le_normalizer_li (le_sup_left.trans hle) hKG
  have hsub : IsSubnormal (li L F.V1) (Subgroup.normalizer (F.V1 : Set G)) :=
    A3.subnormal_trans (A3.subnormal_of_normal hLK.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLK.le).2 hKN)) hK.2.2.1
  exact hK.2.2.2 _ hLK (S125K1.l1_mem_lFamily h1222 F hH).1 (S125K6.commutator_li L _) hsub

theorem not_dvd_card (h1228 : Stmt12_2_8) (hH : Hyp125 G T L V) {J : Subgroup G}
    (hJ : J ≤ Subgroup.normalizer (L : Set G)) : ¬ 27 ∣ Nat.card J := by
  intro h27
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := ↥J)
    (by simpa using h27)
  have hPL : P.map J.subtype ≤ L := by
    rintro _ ⟨p, hpP, rfl⟩
    have hp : (⟨p, hpP⟩ : ↥P) ^ 3 ^ 3 = 1 := by
      rw [← hP]
      exact pow_card_eq_one'
    refine S125Fin.mem_of_three_pow h1228 hH (hJ p.2) (k := 3) ?_
    have h1 := congrArg (fun z : ↥P => ((z : ↥J) : G)) hp
    simpa using h1
  have h1 : 27 ∣ Nat.card L := by
    have := Subgroup.card_dvd_of_le hPL
    rwa [Subgroup.card_map_of_injective J.subtype_injective, hP] at this
  obtain ⟨e⟩ := hH.quot
  have hc : Nat.card L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * Nat.card (CFSG.pCore 2 ↥L) :=
    (CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, card_sl_five_zmod_two] at hc
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [hc, hk] at h1
  have h2 : 27 ∣ 9999360 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right k (by norm_num)) h1
  norm_num at h2

theorem false_of_solvable (h6 : Lemma12_5_6) (h7 : Lemma12_5_7) (h10 : Lemma12_5_10)
    (hH : Hyp125 G T L V) (F : Frame125 T L V) {H : Subgroup G} (hTH : T ≤ H)
    (hHG : H ≤ Subgroup.normalizer (F.V1 : Set G)) (hs : Group.IsSolvable ↥H)
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₁T : F.V1 ≤ T := (S125.V1_le F).trans (S125.le_of_hyp1223 hH.hyp)
  have hV₁2 : IsPGroup 2 ↥F.V1 := hH.hyp.sylow.1.to_le hV₁T
  have hV₁O : F.V1 ≤ pCoreOf 2 H :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hV₁T.trans hTH) hHG hV₁2
  have hInH : InH T H := ⟨hTH, fun hb => S125.V1_ne_bot F (le_bot_iff.1 (hb ▸ hV₁O))⟩
  obtain ⟨H₁, hH₁, hle⟩ := L1295.exists_isHStar_le hInH hHM
  have h1 := S125.one_lt_nParam_of h6 h7 h10 hH F hH₁
  have hs₁ : Group.IsSolvable ↥H₁ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have h2 := E1.solvable_nParam_le_one hs₁
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

section Gamma

variable {K₁ Y : Subgroup G}

@[expose] def cMod (K₁ Y : Subgroup G) (hY : Y ≤ Subgroup.normalizer (K₁ : Set G)) :
    Subgroup ↥Y where
  carrier := {y | ∀ k ∈ K₁, (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K₁}
  mul_mem' := by
    intro a b ha hb k hk
    have hbk : (b : G) * k * (b : G)⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp (hY b.2) k).mp hk
    have h1 := ha k hk
    have h2 := hb k hk
    have hO : (a : G) ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
      S125Fin.normalizer_le_normalizer_pCoreOf K₁ (hY a.2)
    have h3 := (Subgroup.mem_normalizer_iff.mp hO _).mp h2
    have e : ((a * b : ↥Y) : G) * k * ((a * b : ↥Y) : G)⁻¹ * k⁻¹ =
        ((a : G) * ((b : G) * k * (b : G)⁻¹ * k⁻¹) * (a : G)⁻¹) *
          ((a : G) * k * (a : G)⁻¹ * k⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact Subgroup.mul_mem _ h3 h1
  one_mem' := by
    intro k _
    simp
  inv_mem' := by
    intro a ha k hk
    have haN : (a : G)⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.inv_mem _ (hY a.2)
    have hak : (a : G)⁻¹ * k * (a : G) ∈ K₁ := by
      have := (Subgroup.mem_normalizer_iff.mp haN k).mp hk
      simpa using this
    have h1 := ha _ hak
    have e : ((a⁻¹ : ↥Y) : G) * k * ((a⁻¹ : ↥Y) : G)⁻¹ * k⁻¹ =
        ((a : G) * ((a : G)⁻¹ * k * (a : G)) * (a : G)⁻¹ * ((a : G)⁻¹ * k * (a : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.inv_mem _ h1

omit [Finite G] in
theorem mem_pCore_iff (x : ↥K₁) : x ∈ CFSG.pCore 2 ↥K₁ ↔ (x : G) ∈ pCoreOf 2 K₁ :=
  (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite G] in
theorem cMod_normal (hY : Y ≤ Subgroup.normalizer (K₁ : Set G)) : (cMod K₁ Y hY).Normal := by
  refine ⟨fun y hy g k hk => ?_⟩
  have hgN : (g : G)⁻¹ ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.inv_mem _ (hY g.2)
  have hgk : (g : G)⁻¹ * k * (g : G) ∈ K₁ := by
    have := (Subgroup.mem_normalizer_iff.mp hgN k).mp hk
    simpa using this
  have h1 := hy _ hgk
  have hO : (g : G) ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
    S125Fin.normalizer_le_normalizer_pCoreOf K₁ (hY g.2)
  have h2 := (Subgroup.mem_normalizer_iff.mp hO _).mp h1
  have e : ((g * y * g⁻¹ : ↥Y) : G) * k * ((g * y * g⁻¹ : ↥Y) : G)⁻¹ * k⁻¹ =
      (g : G) * ((y : G) * ((g : G)⁻¹ * k * (g : G)) * (y : G)⁻¹ *
        ((g : G)⁻¹ * k * (g : G))⁻¹) * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact h2

omit [Finite G] in
theorem mem_pCoreOf_of_mem_cMod (hY : Y ≤ Subgroup.normalizer (K₁ : Set G))
    (hZ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥) {y : ↥Y} (hy : y ∈ cMod K₁ Y hY)
    (hyK : (y : G) ∈ K₁) : (y : G) ∈ pCoreOf 2 K₁ := by
  have hc : (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (⟨y, hyK⟩ : ↥K₁)) ∈
      Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₁) z
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_pCore_iff]
    have h1 := hy k k.2
    have e : (((k * ⟨(y : G), hyK⟩)⁻¹ * (⟨(y : G), hyK⟩ * k) : ↥K₁) : G) =
        (k : G)⁻¹ * ((y : G)⁻¹ * ((y : G) * (k : G) * (y : G)⁻¹ * (k : G)⁻¹) * (y : G)) *
          (k : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    have hyN : (y : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
      Subgroup.inv_mem _ (S125Fin.normalizer_le_normalizer_pCoreOf K₁ (hY y.2))
    have h2 := (Subgroup.mem_normalizer_iff.mp hyN _).mp h1
    have hkN : (k : G)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
      Subgroup.inv_mem _ (LieType.BorelTits.le_normalizer_pCoreOf 2 K₁ k.2)
    have h3 := (Subgroup.mem_normalizer_iff.mp hkN _).mp h2
    simpa using h3
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at hc
  exact hc

omit [Finite G] in
theorem mem_cMod_of_mem_pCoreOf (hY : Y ≤ Subgroup.normalizer (K₁ : Set G)) {y : ↥Y}
    (hy : (y : G) ∈ pCoreOf 2 K₁) : y ∈ cMod K₁ Y hY := by
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (pCoreOf 2 K₁ : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 K₁ hk
  have h1 := (Subgroup.mem_normalizer_iff.mp hkN _).mp (Subgroup.inv_mem _ hy)
  have e : (y : G) * k * (y : G)⁻¹ * k⁻¹ = (y : G) * (k * (y : G)⁻¹ * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ hy h1

omit [Finite G] in
theorem exists_pow_mem (hT2 : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K₁ : Set G))
    (y : ↥(K₁ ⊔ T)) : ∃ n : ℕ, ((y ^ 2 ^ n : ↥(K₁ ⊔ T)) : G) ∈ K₁ := by
  have : (K₁.subgroupOf (K₁ ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK)
  have hp : IsPGroup 2 (↥(K₁ ⊔ T) ⧸ K₁.subgroupOf (K₁ ⊔ T)) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hx' : x ∈ ((K₁ ⊔ T : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K₁ T hTK] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := hx'
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hlt : (⟨l * t, hx⟩ : ↥(K₁ ⊔ T)) =
        ⟨l, (le_sup_left : K₁ ≤ K₁ ⊔ T) hl⟩ * ⟨t, (le_sup_right : T ≤ K₁ ⊔ T) ht⟩ := rfl
    have hl1 : (QuotientGroup.mk (⟨l, (le_sup_left : K₁ ≤ K₁ ⊔ T) hl⟩ : ↥(K₁ ⊔ T)) :
        ↥(K₁ ⊔ T) ⧸ K₁.subgroupOf (K₁ ⊔ T)) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hl
    refine ⟨k, ?_⟩
    rw [hlt, QuotientGroup.mk_mul, hl1, one_mul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : (((⟨t, (le_sup_right : T ≤ K₁ ⊔ T) ht⟩ : ↥(K₁ ⊔ T)) ^ 2 ^ k : ↥(K₁ ⊔ T)) : G) = 1 := by
      rw [SubgroupClass.coe_pow]
      exact hk'
    rw [this]
    exact K₁.one_mem
  obtain ⟨n, hn⟩ := hp (QuotientGroup.mk y)
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hn
  exact hn

theorem isPGroup_cMod (hT2 : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K₁ : Set G))
    (hZ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥) :
    IsPGroup 2 (cMod K₁ (K₁ ⊔ T) (sup_le Subgroup.le_normalizer hTK)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro c
  obtain ⟨n, hn⟩ := exists_pow_mem hT2 hTK (c : ↥(K₁ ⊔ T))
  have hcn : (c : ↥(K₁ ⊔ T)) ^ 2 ^ n ∈ cMod K₁ (K₁ ⊔ T) (sup_le Subgroup.le_normalizer hTK) :=
    Subgroup.pow_mem _ c.2 _
  have hO := mem_pCoreOf_of_mem_cMod _ hZ hcn hn
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁) ⟨_, hO⟩
  refine ⟨n + m, Subtype.ext (Subtype.ext ?_)⟩
  have hm' : ((((c : ↥(K₁ ⊔ T)) ^ 2 ^ n : ↥(K₁ ⊔ T)) : G)) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hm' ⊢
  rw [pow_add, pow_mul]
  exact hm'

theorem exists_solvable_of_gamma {Q : Type} [Group Q]
    (hγ : ∀ (X : Type) [Group X] [Finite X] (K₀ : Subgroup X) [K₀.Normal],
      Nonempty (↥K₀ ≃* Q) → Subgroup.centralizer (K₀ : Set X) ≤ K₀ → IsPGroup 2 (X ⧸ K₀) →
      ∀ S : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ →
        27 ∣ Nat.card ↥(sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H}))
    (h1228 : Stmt12_2_8) (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Q) (hZ : Subgroup.center (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) = ⊥) :
    ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧ Group.IsSolvable ↥H ∧
      ¬ H ≤ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hT2 : IsPGroup 2 T := hH.hyp.sylow.1
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := (S125L2G.T_le_V F hf.T_le).1.trans hK₁n
  have hYN : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  set C := cMod K₁ (K₁ ⊔ T) hYN with hC
  have : C.Normal := cMod_normal hYN
  set π := QuotientGroup.mk' C with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hK'n : (K₁.subgroupOf (K₁ ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hYN
  set K₀ := (K₁.subgroupOf (K₁ ⊔ T)).map π with hK₀
  have : K₀.Normal := hK'n.map π hπs
  set φ : ↥K₁ →* ↥(K₁ ⊔ T) ⧸ C := π.comp (Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ T))
    with hφ
  have hrange : φ.range = K₀ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥K₁ := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pCore_iff]
    exact ⟨fun hx => mem_pCoreOf_of_mem_cMod hYN hZ hx x.2,
      fun hx => mem_cMod_of_mem_pCoreOf hYN hx⟩
  let eK₀ : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* ↥K₀ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  have hcent : Subgroup.centralizer (K₀ : Set (↥(K₁ ⊔ T) ⧸ C)) ≤ K₀ := by
    intro x hx
    obtain ⟨y, rfl⟩ := hπs x
    have hyC : y ∈ C := by
      intro k hk
      set k' : ↥(K₁ ⊔ T) := ⟨k, (le_sup_left : K₁ ≤ K₁ ⊔ T) hk⟩ with hk'
      have h1 := Subgroup.mem_centralizer_iff.mp hx (π k') ⟨k', hk, rfl⟩
      have h2 : y * k' * y⁻¹ * k'⁻¹ ∈ C := by
        rw [← QuotientGroup.eq_one_iff (N := C), QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
        have h1' : (QuotientGroup.mk k' : ↥(K₁ ⊔ T) ⧸ C) * QuotientGroup.mk y =
            QuotientGroup.mk y * QuotientGroup.mk k' := h1
        rw [← h1']
        group
      have h3 : ((y * k' * y⁻¹ * k'⁻¹ : ↥(K₁ ⊔ T)) : G) ∈ K₁ := by
        have hyN := hYN y.2
        have h4 : (y : G) * k * (y : G)⁻¹ ∈ K₁ := (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
        simpa [hk'] using K₁.mul_mem h4 (K₁.inv_mem hk)
      have h5 := mem_pCoreOf_of_mem_cMod hYN hZ h2 h3
      simpa [hk'] using h5
    have : π y = 1 := (QuotientGroup.eq_one_iff y).2 hyC
    rw [this]
    exact K₀.one_mem
  have hX2 : IsPGroup 2 ((↥(K₁ ⊔ T) ⧸ C) ⧸ K₀) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := hπs x
    obtain ⟨n, hn⟩ := exists_pow_mem hT2 hTK y
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← map_pow]
    exact ⟨y ^ 2 ^ n, hn, rfl⟩
  have hSY : QuasithinUnique.IsSylowTwoOf T (K₁ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
  have hS := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSY) π hπs
  have h27 := hγ (↥(K₁ ⊔ T) ⧸ C) K₀ ⟨eK₀.symm.trans e⟩ hcent hX2 _ hS
  by_contra hno
  push Not at hno
  set M'' := (Subgroup.normalizer (L : Set G)).subgroupOf (K₁ ⊔ T) with hM''
  have hC2 : IsPGroup 2 ↥C := isPGroup_cMod hT2 hTK hZ
  have hCs : Group.IsSolvable ↥C := by
    have := hC2.isNilpotent
    infer_instance
  have hle : sSup {H : Subgroup (↥(K₁ ⊔ T) ⧸ C) |
      (T.subgroupOf (K₁ ⊔ T)).map π ≤ H ∧ Group.IsSolvable ↥H} ≤ M''.map π := by
    refine sSup_le fun Hb ⟨hSH, hHs⟩ => ?_
    set Hh := Hb.comap π with hHh
    have hCH : C ≤ Hh := fun c hc => by
      have h1 : π c = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      show π c ∈ Hb
      rw [h1]
      exact Hb.one_mem
    have hHhs : Group.IsSolvable ↥Hh := by
      let g : ↥Hh →* ↥Hb := (π.comp Hh.subtype).codRestrict Hb fun x => x.2
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hCH) g ?_
      intro x hx
      have hx1 : π (x : ↥(K₁ ⊔ T)) = 1 := congrArg Subtype.val hx
      exact ⟨⟨x, (QuotientGroup.eq_one_iff _).1 hx1⟩, rfl⟩
    have hTH : T ≤ Hh.map (K₁ ⊔ T).subtype := fun t ht =>
      ⟨⟨t, (le_sup_right : T ≤ K₁ ⊔ T) ht⟩, hSH ⟨_, ht, rfl⟩, rfl⟩
    have hHs' : Group.IsSolvable ↥(Hh.map (K₁ ⊔ T).subtype) := by
      have := hHhs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective Hh _ (K₁ ⊔ T).subtype_injective).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective Hh _ (K₁ ⊔ T).subtype_injective).symm.injective
    have hHM := hno _ hTH (Subgroup.map_subtype_le _) hHs'
    have hHhM : Hh ≤ M'' := fun y hy => hHM ⟨y, hy, rfl⟩
    calc Hb = Hh.map π := (Subgroup.map_comap_eq_self_of_surjective hπs Hb).symm
      _ ≤ M''.map π := Subgroup.map_mono hHhM
  have h1 : 27 ∣ Nat.card ↥M'' :=
    (h27.trans (Subgroup.card_dvd_of_le hle)).trans (M''.card_map_dvd π)
  have h2 : Nat.card ↥M'' = Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓ (K₁ ⊔ T)) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective
      (K₁ ⊔ T).subtype_injective]
  exact not_dvd_card h1228 hH inf_le_left (h2 ▸ h1)

theorem isSolvable_of_perm3 {H : Subgroup G}
    (h : Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) : Group.IsSolvable ↥H := by
  obtain ⟨e⟩ := h
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 ↥H)

theorem exists_solvable_of_l52 (hS3 : S3OvergroupFact) (h1222 : Stmt12_2_2)
    (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G))) (hLK : li L F.V1 < K₁)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (e : (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧ Group.IsSolvable ↥H ∧
      ¬ H ≤ Subgroup.normalizer (L : Set G) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) := (S125L2G.T_le_V F hf.T_le).1.trans hK₁n
  have hYN : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  have hSY : QuasithinUnique.IsSylowTwoOf T (K₁ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
  have hTL₁ := S125K1.T_le_normalizer_l1 h1222 F hH
  obtain ⟨eL⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  have hL₁M : li L F.V1 ≤ Subgroup.normalizer (L : Set G) :=
    (S125K6.li_le L F.V1).trans Subgroup.le_normalizer
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hne : Subgroup.normalizer (L : Set G) ⊓ (K₁ ⊔ T) ≠ K₁ ⊔ T := fun heq =>
    not_sup_le h1222 F hH hK hLK (by rw [← heq]; exact inf_le_left)
  obtain ⟨H, hTH, hHX, hHY, hH3⟩ := hS3 G (K₁ ⊔ T) K₁ T (li L F.V1)
    (Subgroup.normalizer (L : Set G) ⊓ (K₁ ⊔ T)) le_sup_left hYN hSY rfl
    (Or.inr (Or.inr ⟨e⟩)) hLK.le hTL₁ (Or.inl ⟨eL⟩)
    (fun t ht => S125K1.l1_inner h1222 F hH ht)
    (sup_le (le_inf hL₁M (hLK.le.trans le_sup_left)) (le_inf hTM le_sup_right)) inf_le_right hne
  exact ⟨H, hTH, hHX, isSolvable_of_perm3 hH3, fun hHM => hHY (le_inf hHM hHX)⟩

theorem exists_solvable_of_list2
    (hγ24 : KG125GammaM24) (hγJ4 : KG125GammaJ4) (hS3 : S3OvergroupFact)
    (h1228 : Stmt12_2_8) (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK : quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G))) (hLK : li L F.V1 < K₁)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hl : IsList1293Two (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) :
    ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧ Group.IsSolvable ↥H ∧
      ¬ H ≤ Subgroup.normalizer (L : Set G) := by
  rcases hl with h | h | h <;> obtain ⟨e⟩ := h
  · exact exists_solvable_of_l52 hS3 h1222 F hH hK hLK hK₁n e
  · exact exists_solvable_of_gamma (fun X _ _ K₀ _ => hγ24 X K₀) h1228 h1222 F hH hK₁n e
      (a318Exclusion_m24 ⟨e⟩).center_eq_bot
  · have hγ : ∀ (X : Type) [Group X] [Finite X] (K₀ : Subgroup X) [K₀.Normal],
        Nonempty (↥K₀ ≃* (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) → Subgroup.centralizer (K₀ : Set X) ≤ K₀ →
        IsPGroup 2 (X ⧸ K₀) → ∀ S : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ →
          27 ∣ Nat.card ↥(sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H}) :=
      fun X _ _ K₀ _ hK₀ => hγJ4 X K₀ (hK₀.map fun f => f.trans e)
    exact exists_solvable_of_gamma hγ h1228 h1222 F hH hK₁n (MulEquiv.refl _)
      (a318Exclusion_j4 ⟨e⟩).center_eq_bot

end Gamma

end S125Gam

end CFSG.Quasithin.H13
