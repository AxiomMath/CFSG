module

public import CFSG.Quasithin.Vol2.Ch12Sec5FinC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Fin

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_centralizerMod {N X U : Subgroup G} {g : G} (hgX : g ∈ X)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) (hgN : g ∈ Subgroup.normalizer (N : Set G)) :
    g ∈ Subgroup.normalizer (centralizerMod N X U : Set G) := by
  apply S125St.mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨hxX, hxN, hxc⟩ := hx
  refine ⟨X.mul_mem (X.mul_mem hgX hxX) (X.inv_mem hgX), Subgroup.mul_mem _
    (Subgroup.mul_mem _ hgN hxN) (Subgroup.inv_mem _ hgN), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) u).mp hu
    simpa using this
  have h1 := (Subgroup.mem_normalizer_iff.mp hgN _).mp (hxc _ hu')
  have e : g * (x * (g⁻¹ * u * g) * x⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
      g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ * u⁻¹ := by group
  rw [← e]
  exact h1

theorem mem_pCoreOf_of_comm {H₁ K L₁ T : Subgroup G} (hH₁ : H₁ ≤ K ⊔ L₁ ⊔ T) (hKH₁ : K ≤ H₁)
    (hL₁H₁ : L₁ ≤ H₁) (hTH₁ : T ≤ H₁) (hT2 : IsPGroup 2 ↥T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTL₁ : T ≤ Subgroup.normalizer (L₁ : Set G))
    (hQT : pCoreOf 2 H₁ ≤ T) {x : G} (hxT : x ∈ T)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H₁)
    (hxL : ∀ l ∈ L₁, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 H₁) : x ∈ pCoreOf 2 H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H₁ with hQ
  have hQN : H₁ ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁
  set D := T ⊓ (centralizerMod Q H₁ K ⊓ centralizerMod Q H₁ L₁) with hD
  have hcommQ : ∀ q ∈ Q, ∀ y ∈ H₁, q * y * q⁻¹ * y⁻¹ ∈ Q := by
    intro q hq y hy
    have h1 := (Subgroup.mem_normalizer_iff.mp (hQN hy) q⁻¹).mp (Q.inv_mem hq)
    have h2 := Q.mul_mem hq h1
    have e : q * (y * q⁻¹ * y⁻¹) = q * y * q⁻¹ * y⁻¹ := by group
    rwa [e] at h2
  have hQD : Q ≤ D := by
    intro q hq
    have hqH : q ∈ H₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 H₁ hq
    exact ⟨hQT hq, ⟨hqH, hQN hqH, fun k hk => hcommQ q hq k (hKH₁ hk)⟩,
      ⟨hqH, hQN hqH, fun l hl => hcommQ q hq l (hL₁H₁ hl)⟩⟩
  have hcomm_norm : ∀ g ∈ H₁, (∀ d ∈ D, g * d * g⁻¹ * d⁻¹ ∈ Q) →
      g ∈ Subgroup.normalizer (D : Set G) := by
    intro g hg hgd
    apply S125St.mem_normalizer_of_conj_le
    intro d hd
    have e : g * d * g⁻¹ = (g * d * g⁻¹ * d⁻¹) * d := by group
    rw [e]
    exact D.mul_mem (hQD (hgd d hd)) hd
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := by
    intro k hk
    refine hcomm_norm k (hKH₁ hk) fun d hd => ?_
    have h1 := Q.inv_mem (hd.2.1.2.2 k hk)
    have e : (d * k * d⁻¹ * k⁻¹)⁻¹ = k * d * k⁻¹ * d⁻¹ := by group
    rwa [e] at h1
  have hLD : L₁ ≤ Subgroup.normalizer (D : Set G) := by
    intro l hl
    refine hcomm_norm l (hL₁H₁ hl) fun d hd => ?_
    have h1 := Q.inv_mem (hd.2.2.2.2 l hl)
    have e : (d * l * d⁻¹ * l⁻¹)⁻¹ = l * d * l⁻¹ * d⁻¹ := by group
    rwa [e] at h1
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := by
    intro t ht
    have h1 := mem_normalizer_centralizerMod (hTH₁ ht) (hTK ht) (hQN (hTH₁ ht))
    have h2 := mem_normalizer_centralizerMod (hTH₁ ht) (hTL₁ ht) (hQN (hTH₁ ht))
    apply S125St.mem_normalizer_of_conj_le
    rintro d ⟨hdT, hdK, hdL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hdT) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp h1 d).mp hdK, (Subgroup.mem_normalizer_iff.mp h2 d).mp hdL⟩
  have hDQ : D ≤ Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH₁)
      (hH₁.trans (sup_le (sup_le hKD hLD) hTD)) (hT2.to_le inf_le_left)
  have hxH : x ∈ H₁ := hTH₁ hxT
  exact hDQ ⟨hxT, ⟨hxH, hQN hxH, hxK⟩, ⟨hxH, hQN hxH, hxL⟩⟩

theorem comm_mem_of_almostSpecial {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H)
    {q u : G} (hq : q ∈ pCoreOf 2 H) (hu : u ∈ conjClosure V H) : q * u * q⁻¹ * u⁻¹ ∈ V₁ := by
  have hcc := h.conjClosure_le_N
  have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) :=
    h.H_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H hq)
  have hmem : tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    (secImg_le_iff.1 h.G22_one.2) ⟨u, hcc hu⟩ hu
  have hqQ : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := secMk_mem_secImg hq
  have hc := mem_centralizer_of_mem_omegaOneCenterOf hmem hqQ
  exact commutator_mem_of_secMk_commute hc

omit [Finite G] in
theorem mem_centralizer_of_comm_mod {U V₁ : Subgroup G} {k : G} (hko : Odd (orderOf k))
    (hkV₁ : ∀ v ∈ V₁, k * v * k⁻¹ = v) (hV₁2 : ∀ v ∈ V₁, v * v = 1)
    (hkU : ∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ V₁) : k ∈ Subgroup.centralizer (U : Set G) := by
  have hk2 : k ^ 2 ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hc := hkU u hu
    have hkc := hkV₁ _ hc
    have hcc := hV₁2 _ hc
    have key : k * (k * u * k⁻¹) * k⁻¹ = u := by
      have e1 : k * (k * u * k⁻¹) * k⁻¹ =
          k * (k * u * k⁻¹ * u⁻¹) * k⁻¹ * (k * u * k⁻¹ * u⁻¹) * u := by group
      rw [e1, hkc, hcc, one_mul]
    calc u * k ^ 2 = k * (k * u * k⁻¹) * k⁻¹ * k ^ 2 := by rw [key]
      _ = k ^ 2 * u := by rw [sq]; group
  exact mem_of_pow_mem_of_coprime (Nat.coprime_two_left.mpr hko) (pow_orderOf_eq_one k) hk2

omit [Finite G] in
theorem le_pCoreOf_or_le {H N : Subgroup G} (hNK : N ≤ oTwoUpper H)
    (hNn : oTwoUpper H ≤ Subgroup.normalizer (N : Set G))
    (e : ↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* ↥(alternatingGroup (Fin 5))) :
    N ≤ pCoreOf 2 (oTwoUpper H) ∨ oTwoUpper H ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hK
  set N' : Subgroup ↥K := N.subgroupOf K with hN'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hNn
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
    exact e.isSimpleGroup
  have hNb : (N'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hN'n.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with h | h
  · left
    intro n hn
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨n, hNK hn⟩ : ↥K) ∈
        N'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := ⟨⟨n, hNK hn⟩, hn, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨n, hNK hn⟩, by assumption, rfl⟩
  · right
    rw [hK, oTwoUpper]
    refine (Subgroup.closure_le N).mpr ?_
    rintro x ⟨hxH, hxo⟩
    have hxK : x ∈ K := Subgroup.subset_closure ⟨hxH, hxo⟩
    obtain ⟨n, hn, hnx⟩ : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hxK⟩ : ↥K) ∈
        N'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := h ▸ Subgroup.mem_top _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hnx⟩
    have hj' : (n⁻¹ * ⟨x, hxK⟩) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h2 : QuotientGroup.mk' N' (⟨x, hxK⟩ : ↥K) ^ 2 ^ j = 1 := by
      have hn1 : QuotientGroup.mk' N' n = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hn
      have h3 : QuotientGroup.mk' N' (⟨x, hxK⟩ : ↥K) =
          QuotientGroup.mk' N' (n⁻¹ * ⟨x, hxK⟩) := by
        rw [map_mul, map_inv, hn1, inv_one, one_mul]
      rw [h3, ← map_pow, hj', map_one]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h4 : x ^ 2 ^ j ∈ N := by simpa [hN', Subgroup.mem_subgroupOf] using h2
    exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hxo))
      (pow_orderOf_eq_one x) h4

theorem comm_mem_pCoreOf {L₁ V : Subgroup G} (hL₁V : L₁ ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(L₁ ⊓ Subgroup.centralizer (V : Set G))) {a : G}
    (haN : a ∈ Subgroup.normalizer (L₁ : Set G)) (haC : a ∈ Subgroup.centralizer (V : Set G))
    {l : G} (hl : l ∈ L₁) : a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : L₁ ≤ Subgroup.normalizer ((L₁ ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
    intro g hg
    apply S125St.mem_normalizer_of_conj_le
    rintro x ⟨hxL, hxC⟩
    have hxC' : x ∈ Subgroup.centralizer (V : Set G) := hxC
    refine ⟨L₁.mul_mem (L₁.mul_mem hg hxL) (L₁.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hL₁V hg)) v).mp hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hxC' _ hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * v := by group
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hN hC ⟨?_, ?_⟩
  · have h1 : a * l * a⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp haN l).mp hl
    exact L₁.mul_mem h1 (L₁.inv_mem hl)
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hv' : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hL₁V hl)) v).mp hv
      simpa using this
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ V, v = l * u * l⁻¹ := ⟨_, hv', by group⟩
    have h1 : u * a = a * u := Subgroup.mem_centralizer_iff.mp haC u hu
    have h2 : l * u * l⁻¹ * a = a * (l * u * l⁻¹) := Subgroup.mem_centralizer_iff.mp haC _ hv
    have h1' : a⁻¹ * u = u * a⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_assoc, mul_inv_cancel, mul_one]
    calc l * u * l⁻¹ * (a * l * a⁻¹ * l⁻¹) = (l * u * l⁻¹ * a) * l * a⁻¹ * l⁻¹ := by group
      _ = a * l * (u * a⁻¹) * l⁻¹ := by rw [h2]; group
      _ = a * l * (a⁻¹ * u) * l⁻¹ := by rw [h1']
      _ = a * l * a⁻¹ * l⁻¹ * (l * u * l⁻¹) := by group

theorem index_subgroupOf_le_four {K A Q : Subgroup G}
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(alternatingGroup (Fin 5)))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hA : IsElemAbelian 2 A)
    (hker : ∀ a ∈ A, (∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) → a ∈ Q) :
    (Q.subgroupOf A).index ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Finite.of_equiv _ (CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e).symm.toEquiv
  set φ : ↥A →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (E1.LiftS5.quotConj K).comp (Subgroup.inclusion hAK) with hφ
  have hkerQ : φ.ker ≤ Q.subgroupOf A := by
    intro a ha
    rw [Subgroup.mem_subgroupOf]
    refine hker a a.2 fun k hk => ?_
    have h1 : φ a (QuotientGroup.mk ⟨k, hk⟩) = QuotientGroup.mk ⟨k, hk⟩ := by
      rw [MonoidHom.mem_ker.mp ha]
      rfl
    have h2 : φ a (QuotientGroup.mk ⟨k, hk⟩) = QuotientGroup.mk
        (K.normalizerMonoidHom (Subgroup.inclusion hAK a) ⟨k, hk⟩) := rfl
    rw [h2, QuotientGroup.eq] at h1
    have hnorm : (CFSG.pCore 2 ↥K).Normal := inferInstance
    have h3 := hnorm.conj_mem _ (inv_mem h1) ⟨k, hk⟩
    have h4 : (⟨k, hk⟩ : ↥K) * ((K.normalizerMonoidHom (Subgroup.inclusion hAK a) ⟨k, hk⟩)⁻¹ *
        ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ : ↥K)⁻¹ = ⟨(a : G) * k * (a : G)⁻¹ * k⁻¹, by
          have h5 : (a : G) * k * (a : G)⁻¹ ∈ K :=
            (Subgroup.mem_normalizer_iff.mp (hAK a.2) k).mp hk
          exact K.mul_mem h5 (K.inv_mem hk)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      group
    rw [h4] at h3
    exact ⟨_, by assumption, rfl⟩
  have hAtop : IsElemAbelian 2 (⊤ : Subgroup ↥A) := by
    have := hA.1
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext ?_⟩
    · exact congrArg Subtype.val (mul_comm' (⟨(x : ↥A), (x : ↥A).2⟩ : A) ⟨(y : ↥A), (y : ↥A).2⟩)
    · simpa using hA.2 _ x.2
  have hrange : IsElemAbelian 2 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hAtop φ
  have hrange2 : IsPGroup 2 ↥φ.range := fun x => ⟨1, Subtype.ext (by simpa using hrange.2 x x.2)⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hrange2
  have hle := CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (le_top : φ.range ≤ ⊤) hrange hr
  have hnq := (CFSG.LieType.nq_Alt5_and_binary_GL3_full_automorphism_two_rank
    (↥K ⧸ CFSG.pCore 2 ↥K) (Or.inl ⟨e⟩)).1 ⊤ le_top
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at hnq
  rw [hnq] at hle
  have hcard : Nat.card φ.range ≤ 4 := by
    rw [hr]
    calc 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
      _ = 4 := by norm_num
  calc (Q.subgroupOf A).index ≤ φ.ker.index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hkerQ)
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ ≤ 4 := hcard

end S125Fin

end CFSG.Quasithin.H13
